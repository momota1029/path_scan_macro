use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{
    Expr, Ident, LitStr, Token,
    parse::{Parse, ParseStream},
    parse_macro_input,
};

use regex::escape;

/// 1 つの腕（arm）
/// - `patterns`: 1 つ以上の LitStr（`|` で連結）。デフォルト腕の場合は空。
/// - `expr`: 変換式（ブロック・単一式どちらも可）
/// - `cond`: オプションの if 条件
struct Arm {
    patterns: Vec<LitStr>,
    cond: Option<Expr>,
    expr: Expr,
}

impl Parse for Arm {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut patterns = Vec::new();
        // 最初のトークン：LitStr か "_" か
        if input.peek(LitStr) {
            patterns.push(input.parse()?);
        } else if input.peek(Token![_]) {
            // default 腕
            input.parse::<Token![_]>()?;
        } else {
            return Err(input.error("Expected string literal or '_' for default arm"));
        }
        // 続いて、もし '|' があれば追加のパターンを読み込む
        while input.peek(Token![|]) {
            input.parse::<Token![|]>()?;
            // 必ず LitStr として
            patterns.push(input.parse()?);
        }
        // オプション：if 条件
        let cond = if input.peek(Token![if]) {
            input.parse::<Token![if]>()?;
            Some(input.parse()?)
        } else {
            None
        };
        // 区切りとして "=>" または ":" を期待
        if input.peek(Token![=>]) {
            input.parse::<Token![=>]>()?;
        } else if input.peek(Token![:]) {
            input.parse::<Token![:]>()?;
        } else {
            return Err(input.error("Expected '=>' or ':' after patterns"));
        }
        // 変換式部分をパース（ブロックでも単一式でも受け付ける）
        let expr: Expr = input.parse()?;

        Ok(Arm { patterns, expr, cond })
    }
}

/// 複数の腕（arm）を読み込む。各腕はカンマまたは改行で区切られてもよい。
struct Arms {
    arms: Vec<Arm>,
    completeness: bool,
}

impl Parse for Arms {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let (mut arms, mut completeness) = (Vec::new(), false);
        while !input.is_empty() {
            let arm = input.parse::<Arm>()?;
            if arm.patterns.is_empty() && arm.cond.is_none() {
                completeness = true;
            }
            arms.push(arm);
            // カンマはオプション
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
        }
        Ok(Arms { arms, completeness })
    }
}

/// パターン文字列を正規表現に変換し、キャプチャする識別子のリストを返す。
/// - リテラル部分は `escape` でエスケープ
/// - プレースホルダーは、`:identifier` または `{identifier}` の形式に対応し、
///   いずれも `(?P<identifier>[^/]+)` として変換する。
fn compile_pattern(pattern: &str) -> (String, Vec<String>) {
    let mut regex_pattern = String::new();
    let mut identifiers = Vec::new();
    regex_pattern.push('^');

    let mut chars = pattern.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '\\' => {
                if let Some(next_ch) = chars.next() {
                    regex_pattern.push_str(&escape(&next_ch.to_string()));
                }
            }
            '{' => {
                let mut ident = String::new();
                while let Some(ch2) = chars.next() {
                    if ch2 == '}' {
                        break;
                    } else {
                        ident.push(ch2);
                    }
                }
                if !ident.is_empty() {
                    identifiers.push(ident.clone());
                    regex_pattern.push_str(&format!("(?P<{}>[^/]+)", ident));
                }
            }
            ':' => {
                let mut ident = String::new();
                while let Some(&ch2) = chars.peek() {
                    if ch2.is_alphanumeric() || ch2 == '_' {
                        ident.push(ch2);
                        chars.next();
                    } else {
                        break;
                    }
                }
                if !ident.is_empty() {
                    identifiers.push(ident.clone());
                    regex_pattern.push_str(&format!("(?P<{}>[^/]+)", ident));
                } else {
                    regex_pattern.push_str(&escape(&":".to_string()));
                }
            }
            _ => {
                regex_pattern.push_str(&escape(&ch.to_string()));
            }
        }
    }
    regex_pattern.push('$');
    (regex_pattern, identifiers)
}

/// `path_scan!` macro parses an input string using the provided patterns
/// and returns a closure that yields the result of the first matching arm.
///
/// Patterns are specified as follows:
///
/// - `"pattern string" => expression`
///   In the pattern string, placeholders like `:identifier` and `{identifier}` are
///   captured and become available as variables.
///
/// - Multiple patterns can be combined using `"pattern1" | "pattern2" => expression`.
///
/// - An optional `if` condition may follow the pattern(s) (e.g., `"pattern" if condition => expression`).
///   The arm is considered a match only if the condition evaluates to true.
///
/// - The default arm is specified as `_ => expression`.
///
/// **Note:**
/// If an if-less default arm is not provided—that is, if a default arm without an `if` condition is missing—
/// the closure returns `None` on failure, making the overall expression type `Option<T>`.
///
/// # Examples
///
/// ```rust
/// use path_scan::path_scan;
///
/// // With a default arm, the return type is a concrete type (e.g., String)
/// let scanner = path_scan! {
///     "blog/:slug/index" => format!("blog: {}", slug),
///     "other/:slug" if slug.len() == 5 => format!("short blog: {}", slug),
///     _ => format!("default")
/// };
///
/// assert_eq!(scanner("blog/hello/index"), "blog: hello");
/// assert_eq!(scanner("other/short"), "short blog: short");
/// assert_eq!(scanner("unknown/path"), "default");
///
/// // Without a default arm, the return type is `Option<String>`
/// let scanner_opt = path_scan! {
///     "blog/:slug/index" => format!("blog: {}", slug)
/// };
///
/// assert_eq!(scanner_opt("blog/world/index"), Some("blog: world".to_string()));
/// assert_eq!(scanner_opt("unknown/path"), None);
/// ```
#[proc_macro]
pub fn path_scan(input: TokenStream) -> TokenStream {
    let Arms { arms, completeness } = parse_macro_input!(input as Arms);

    let mut arm_match_tokens = Vec::new();
    // 各腕について処理（Arm を直接分解）
    for Arm { patterns, expr, cond } in arms.into_iter() {
        let value = if completeness {
            quote! { #expr }
        } else {
            quote! { Some({ #expr }) }
        };
        if !patterns.is_empty() {
            for pat_lit in patterns.into_iter() {
                let pattern_str = pat_lit.value();
                let (regex_str, idents) = compile_pattern(&pattern_str);
                let regex_lit = LitStr::new(&regex_str, pat_lit.span());
                let mut bindings = Vec::new();
                for ident in idents {
                    let ident_token = Ident::new(&ident, pat_lit.span());
                    bindings.push(quote! {
                        let #ident_token = __caps.name(#ident).map(|m| m.as_str()).unwrap();
                    });
                }
                let cond_check = if let Some(cond_expr) = &cond {
                    quote! { if #cond_expr }
                } else {
                    quote! { if true }
                };
                arm_match_tokens.push(quote! {
                    if let Some(__caps) = ::regex::Regex::new(#regex_lit).unwrap().captures(input) {
                        #(#bindings)*
                        #cond_check {
                            return #value;
                        }
                    }
                });
            }
        } else {
            // デフォルト腕の場合
            let cond_check = if let Some(cond_expr) = &cond {
                quote! { if #cond_expr }
            } else {
                quote! { if true }
            };
            arm_match_tokens.push(quote! {
                #cond_check {
                    return #value;
                }
            });
        }
    }

    let last = if completeness {
        quote! {unreachable!()}
    } else {
        quote! {None}
    };
    let expanded = quote! {
        {
            move |input: &str| {
                #(#arm_match_tokens)*
                #last
            }
        }
    };
    TokenStream::from(expanded)
}

/// path_scan_val! マクロの入力をパースするための構文要素
struct PathScanValInput {
    input_expr: Expr,
    arms: Arms,
}

impl Parse for PathScanValInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let input_expr: Expr = input.parse()?;
        // カンマはオプション
        if input.peek(Token![,]) {
            input.parse::<Token![,]>()?;
        }
        if input.peek(syn::token::Brace) {
            let content;
            let _brace_token = syn::braced!(content in input);
            let arms: Arms = content.parse()?;
            Ok(PathScanValInput { input_expr, arms })
        } else {
            let arms: Arms = input.parse()?;
            Ok(PathScanValInput { input_expr, arms })
        }
    }
}

/// `path_scan_val!` macro parses an input string using the provided patterns
/// and returns the result of the first matching arm directly.
///
/// This macro supports two forms:
///
/// 1. **Comma Form**
///    ```ignore
///    path_scan_val!("input string", "pattern string" => expression, ... )
///    ```
///
/// 2. **Brace Form**
///    ```ignore
///    path_scan_val!("input string" { "pattern string" => expression, ... })
///    ```
///
/// Patterns are specified as follows:
///
/// - `"pattern string" => expression`
///   In the pattern string, placeholders like `:identifier` and `{identifier}` are
///   captured and become available as variables.
///
/// - Multiple patterns can be combined using `"pattern1" | "pattern2" => expression`.
///
/// - An optional `if` condition may follow the pattern(s) (e.g., `"pattern" if condition => expression`).
///   The arm is considered a match only if the condition evaluates to true.
///
/// - The default arm is specified as `_ => expression`.
///
/// **Note:**
/// If an if-less default arm is not provided—that is, if a default arm without an `if` condition is missing—
/// the macro returns `None` on failure, making the overall expression type `Option<T>`.
/// Commas between arms are optional.
///
/// # Examples
///
/// **Comma Form**
/// ```rust
/// # use path_scan::path_scan_val;
/// let result = path_scan_val!("blog/hello/index",
///     "blog/{slug}/index" => format!("blog: {}", slug),
///     _ => format!("default")
/// );
/// assert_eq!(result, format!("blog: hello"));
/// ```
///
/// **Brace Form**
/// ```rust
/// # use path_scan::path_scan_val;
/// let result = path_scan_val!("blog/world/index" {
///     "blog/{slug}/index" => format!("blog: {}", slug),
///     _ => format!("default")
/// });
/// assert_eq!(result, format!("blog: world"));
/// ```
///
/// **Without a Default Arm (returns `Option<T>`)**
/// ```rust
/// # use path_scan::path_scan_val;
/// let result = path_scan_val!("blog/foo/index",
///     "blog/{slug}/index" => format!("blog: {}", slug)
/// );
/// assert_eq!(result, Some(format!("blog: foo")));
///
/// let result2 = path_scan_val!("unknown/path",
///     "blog/{slug}/index" => format!("blog: {}", slug)
/// );
/// assert_eq!(result2, None);
/// ```
#[proc_macro]
pub fn path_scan_val(input: TokenStream) -> TokenStream {
    let PathScanValInput { input_expr, arms } = parse_macro_input!(input as PathScanValInput);
    let Arms { arms, completeness } = arms;

    let mut arm_match_tokens = Vec::new();
    for Arm { patterns, expr, cond } in arms.into_iter() {
        let value = if completeness {
            quote! { #expr }
        } else {
            quote! { Some({ #expr }) }
        };
        if !patterns.is_empty() {
            for pat_lit in patterns.into_iter() {
                let pattern_str = pat_lit.value();
                let (regex_str, idents) = compile_pattern(&pattern_str);
                let regex_lit = LitStr::new(&regex_str, pat_lit.span());
                let mut bindings = Vec::new();
                let regex_var = format_ident!("__regex");
                for ident in idents {
                    let ident_token = Ident::new(&ident, pat_lit.span());
                    bindings.push(quote! {
                        let #ident_token = __caps.name(#ident).map(|m| m.as_str()).unwrap();
                    });
                }
                let cond_check = if let Some(ref cond_expr) = cond {
                    quote! { if #cond_expr }
                } else {
                    quote! { if true }
                };
                arm_match_tokens.push(quote! {
                    static #regex_var: ::path_scan::once_cell::sync::Lazy<::path_scan::regex::Regex> = ::path_scan::once_cell::sync::Lazy::new(|| ::path_scan::regex::Regex::new(#regex_lit).unwrap());
                    if let Some(__caps) = #regex_var.captures(__input) {
                        #(#bindings)*
                        #cond_check {
                            break 'x #value;
                        }
                    }
                });
            }
        } else {
            let cond_check = if let Some(ref cond_expr) = cond {
                quote! { if #cond_expr }
            } else {
                quote! { if true }
            };
            arm_match_tokens.push(quote! {
                #cond_check {
                    break 'x #value;
                }
            });
        }
    }

    let last = if completeness {
        quote! { unreachable!() }
    } else {
        quote! { None }
    };

    let expanded = quote! {
        {
            let __input = #input_expr;
            #[allow(unreachable_code)]
            let __result = 'x: {
                #(#arm_match_tokens)*
                break 'x #last;
            };
            __result
        }
    };

    TokenStream::from(expanded)
}
