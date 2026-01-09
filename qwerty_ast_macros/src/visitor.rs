use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote_spanned;
use syn::{Arm, Error, Expr, Ident, LitStr, spanned::Spanned};

mod parse;

/// Converts a format string and arguments to a `write!(...)?;` statement.
fn to_write_stmt(span: Span, dest: &Expr, fmt_str: &str, args: Vec<Expr>) -> TokenStream2 {
    let fmt_str_lit = LitStr::new(fmt_str, span);
    quote_spanned! {span=>
        write!(#dest, #fmt_str_lit, #(#args),*)?;
    }
}

/// Implements `visitor_write! { ... }`. See [`crate::visitor_write`].
pub fn impl_visitor_write(args: TokenStream) -> Result<TokenStream, Error> {
    let parse::VisitorMacroCall { ty, match_on, arms } = syn::parse(args)?;
    let span = ty.span();

    let ent_arms = arms
        .into_iter()
        .map(|arm| {
            let Arm {
                attrs: _,
                pat,
                guard,
                fat_arrow_token: _,
                body,
                comma: _,
            } = arm;

            let parse::WriteCallArgs { dest, mut segs } =
                parse::parse_visitor_write_arm_expr(*body)?;
            // So we can use it as a stack
            segs.reverse();
            let (maybe_first_seg, initial_write) = if let Some(first_seg) = segs.pop() {
                if let parse::WriteCallSegment::FormatString(fmt_str, args) = first_seg {
                    (None, to_write_stmt(span, &dest, &fmt_str, args))
                } else {
                    (Some(first_seg), TokenStream2::new())
                }
            } else {
                (None, TokenStream2::new())
            };

            let mut hook_counter = 0usize;
            let (pushes, hook_arms): (Vec<_>, Vec<_>) = segs
                .into_iter()
                .chain(maybe_first_seg.into_iter())
                .map(|seg| {
                    match seg {
                        parse::WriteCallSegment::FormatString(fmt_str, args) => {
                            let write_stmt = to_write_stmt(span, &dest, &fmt_str, args);
                            let hook_id = hook_counter;
                            hook_counter += 1;
                            (
                                quote_spanned! {span=>
                                    in_stack.push(StackEntry::PlainWrite(node, #hook_id));
                                },
                                quote_spanned! {span=>
                                    #[allow(unused_variables)]
                                    StackEntry::PlainWrite(#pat, #hook_id) => {
                                        #write_stmt
                                    }
                                },
                            )
                        }

                        parse::WriteCallSegment::Visit(parse::VisitKind::SingleVisit { node }) => {
                            (
                                quote_spanned! {span=>
                                    in_stack.push(StackEntry::Visit(&#node));
                                },
                                quote_spanned! {span=>
                                    // No hook arm needed
                                },
                            )
                        }

                        parse::WriteCallSegment::Visit(parse::VisitKind::MultiVisit { nodes, sep }) => {
                            let sep_hook_id = hook_counter;
                            hook_counter += 1;
                            let write_stmt = to_write_stmt(span, &dest, "{}", vec![sep]);
                            (
                                quote_spanned! {span=>
                                    for (i, subnode) in #nodes.into_iter().enumerate().rev() {
                                        in_stack.push(StackEntry::Visit(subnode));
                                        if i > 0 {
                                            in_stack.push(StackEntry::PlainWrite(node, #sep_hook_id));
                                        }
                                    }
                                },
                                quote_spanned! {span=>
                                    #[allow(unused_variables)]
                                    StackEntry::PlainWrite(#pat, #sep_hook_id) => {
                                        #write_stmt
                                    }
                                },
                            )
                        }
                    }
                })
                .unzip();

            let maybe_guard = if let Some((if_tok, guard_expr)) = guard {
                quote_spanned! {span=>
                    #if_tok #guard_expr
                }
            } else {
                quote_spanned! {span=>
                    // No guard needed
                }
            };

            Ok(quote_spanned! {span=>
                #[allow(unused_parens, unused_variables)]
                StackEntry::Visit(node @ (#pat)) #maybe_guard => {
                    #initial_write
                    #(#pushes)*
                }
                #(#hook_arms)*
            })
        })
        .collect::<Result<Vec<_>, Error>>()?;

    Ok(quote_spanned! {span=>
        {
            let match_on = #match_on;

            enum StackEntry<'a> {
                Visit(&'a #ty),
                PlainWrite(&'a #ty, usize),
            }

            let mut in_stack = vec![StackEntry::Visit(match_on)];

            while let Some(ent) = in_stack.pop() {
                let () = match ent {
                    #(#ent_arms)*
                    StackEntry::PlainWrite(_, _) => unreachable!("broken in_stack state"),
                };
            }

            Ok(())
        }
    }
    .into())
}

/// Generate a temporary variable name when rewriting `visitor_expr`
/// expressions to replace `visit!(...)` calls with variable names.
fn generate_visit_var_name(visit_id: usize, span: Span) -> Ident {
    Ident::new(&format!("visited_node{}", visit_id), span)
}

/// Implements `visitor_expr! { ... }`. See [`crate::visitor_expr`].
pub fn impl_visitor_expr(args: TokenStream) -> Result<TokenStream, Error> {
    let parse::VisitorMacroCall { ty, match_on, arms } = syn::parse(args)?;
    let span = ty.span();

    let ent_arms = arms
        .into_iter()
        .map(|arm| {
            let Arm {
                attrs: _,
                pat,
                guard,
                fat_arrow_token: _,
                body,
                comma: _,
            } = arm;

            let (visit_exprs, compute_expr) =
                parse::parse_visitor_expr_arm_expr(*body, generate_visit_var_name)?;

            let pushes: Vec<_> = visit_exprs
                .iter()
                .rev()
                .map(|visit_expr| {
                    quote_spanned! {span=>
                        in_stack.push(StackEntry::Visit(&#visit_expr));
                    }
                })
                .collect();
            let pops: Vec<_> = (0..visit_exprs.len())
                .map(|visit_id| {
                    let visit_var_name = generate_visit_var_name(visit_id, span);
                    quote_spanned! {span=>
                        let #visit_var_name = out_stack.pop().expect("Corrupted out_stack");
                    }
                })
                .collect();

            let maybe_guard = if let Some((if_tok, guard_expr)) = guard {
                quote_spanned! {span=>
                    #if_tok #guard_expr
                }
            } else {
                quote_spanned! {span=>
                    // No guard needed
                }
            };

            Ok(quote_spanned! {span=>
                #[allow(unused_parens, unused_variables)]
                StackEntry::Visit(node @ (#pat)) #maybe_guard => {
                    in_stack.push(StackEntry::ComputeExpr(node));
                    #(#pushes)*
                }
                #[allow(unused_variables)]
                StackEntry::ComputeExpr(#pat) #maybe_guard => {
                    #(#pops)*
                    out_stack.push(#compute_expr);
                }
            })
        })
        .collect::<Result<Vec<_>, Error>>()?;

    Ok(quote_spanned! {span=>
        {
            let match_on = #match_on;

            enum StackEntry<'a> {
                Visit(&'a #ty),
                ComputeExpr(&'a #ty),
            }

            let mut in_stack = vec![StackEntry::Visit(match_on)];
            let mut out_stack = vec![];

            while let Some(ent) = in_stack.pop() {
                let () = match ent {
                    #(#ent_arms)*
                };
            }

            assert_eq!(out_stack.len(), 1, "Corrupted out_stack");
            out_stack.pop().expect("out_stack should have length 1")
        }
    }
    .into())
}
