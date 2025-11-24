//! Code generation for `#[gen_rebuild { ... }]`.

use crate::rebuild::{attrs, parse, tys};
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote_spanned;
use syn::{
    Error, Field, Fields, FieldsNamed, Ident, ItemEnum, Path, PathArguments, PathSegment, Type,
    TypePath, Variant, punctuated::Pair,
};

impl parse::RebuildConfig {
    /// Returns `Some(ty')` if the `rewrite_to` option specifies that `ty`
    /// should be rewritten to `ty'`.
    fn rewrite_ty(&self, ty: &Type) -> Option<Type> {
        if let Some(inner_ty) = tys::ty_as_option(ty) {
            Some(tys::ty_into_option(self.rewrite_ty(inner_ty)?))
        } else if let Some(inner_ty) = tys::ty_as_vec(ty) {
            Some(tys::ty_into_vec(self.rewrite_ty(inner_ty)?))
        } else if let Some(elem_tys) = tys::ty_as_tuple(ty) {
            let rewritten_elem_tys: Vec<_> = elem_tys
                .iter()
                .map(|elem_ty| self.rewrite_ty(elem_ty))
                .collect();
            if rewritten_elem_tys.iter().all(|elem| elem.is_none()) {
                None
            } else {
                let rewritten_inner_tys: Vec<_> = rewritten_elem_tys
                    .into_iter()
                    .zip(elem_tys)
                    .map(|(rewritten_ty, old_ty)| rewritten_ty.unwrap_or_else(|| old_ty.clone()))
                    .collect();
                Some(tys::tys_into_tuple(rewritten_inner_tys))
            }
        } else {
            self.rewrite_to.iter().find_map(
                |parse::TypeMapping(lhs, rhs)| {
                    if lhs == ty { Some(rhs.clone()) } else { None }
                },
            )
        }
    }

    /// Rewrites `ty` according to the `rewrite_to` option or returns it
    /// unchanged.
    fn rewrite_ty_if_needed(&self, ty: Type) -> Type {
        self.rewrite_ty(&ty).unwrap_or(ty)
    }
}

/// Removes any attributes starting with `gen_rebuild::*` from this field and
/// rewrites its type with `config` to respect `rewrite_to`. Also initially
/// unboxes types if requested (i.e., replaces any `Box<T>` with `T`).
fn strip_our_attrs_and_rewrite_field_ty(
    config: &parse::RebuildConfig,
    unbox: bool,
    field: Field,
) -> Field {
    let Field {
        attrs,
        vis,
        mutability,
        ident,
        colon_token,
        ty,
    } = attrs::strip_our_attrs_from_field(field);
    let unboxed_ty = if unbox {
        tys::ty_as_box(&ty).cloned().unwrap_or(ty)
    } else {
        ty
    };
    let ty = config.rewrite_ty_if_needed(unboxed_ty);
    Field {
        attrs,
        vis,
        mutability,
        ident,
        colon_token,
        ty,
    }
}

/// Makes the recursive call on an attr (non-child field), even if it is inside
/// a tuple, box, or vector. Should be called only when `recurse_attrs` is set.
fn recurse_and_rebuild_attr(
    config: &parse::RebuildConfig,
    span: Span,
    attr_ident: &Ident,
    attr_ty: &Type,
    rewrite_args: &Vec<TokenStream2>,
    unpacked_idents: &Vec<Ident>,
    move_assignments: &Vec<TokenStream2>,
) -> TokenStream2 {
    if let Some(inner_ty) = tys::ty_as_box(attr_ty) {
        let recurse_boxed_elem = recurse_and_rebuild_attr(
            config,
            span,
            attr_ident,
            inner_ty,
            rewrite_args,
            unpacked_idents,
            move_assignments,
        );
        if config.progress.is_some() {
            quote_spanned! {span=>
                {
                    let (attr, progress) = #recurse_boxed_elem;
                    (Box::new(attr), progress)
                }
            }
        } else {
            quote_spanned! {span=>
                Box::new(#recurse_boxed_elem)
            }
        }
    } else if let Some(inner_ty) = tys::ty_as_option(attr_ty) {
        let some_val_ident = Ident::new("some_val", span);
        let recurse_some_val = recurse_and_rebuild_attr(
            config,
            span,
            &some_val_ident,
            inner_ty,
            rewrite_args,
            unpacked_idents,
            move_assignments,
        );
        let (some_ret, none_ret) = if let Some(progress_ty) = &config.progress {
            (
                quote_spanned! {span=>
                    let (attr, progress) = #recurse_some_val;
                    (Some(attr), progress)
                },
                quote_spanned! {span=>
                    (None, #progress_ty::identity())
                },
            )
        } else {
            (
                quote_spanned! {span=>
                    Some(#recurse_some_val)
                },
                quote_spanned! {span=>
                    None
                },
            )
        };
        quote_spanned! {span=>
            if let Some(#some_val_ident) = #attr_ident {
                #some_ret
            } else {
                #none_ret
            }
        }
    } else if let Some(inner_ty) = tys::ty_as_vec(attr_ty) {
        let elem_ident = Ident::new("elem", span);
        let recurse_elem = recurse_and_rebuild_attr(
            config,
            span,
            &elem_ident,
            inner_ty,
            rewrite_args,
            unpacked_idents,
            move_assignments,
        );
        let (lhs_pat, collect_method_call, return_expr) =
            if let Some(progress_ty) = &config.progress {
                let joined_progress = quote_spanned! {span=>
                    progresses
                        .into_iter()
                        .fold(#progress_ty::identity(), |acc, progress| {
                            acc.join(progress)
                        })
                };

                (
                    quote_spanned! {span=>
                        (attrs, progresses): (Vec<_>, Vec<_>)
                    },
                    if let Some(err_ty) = &config.result_err {
                        quote_spanned! {span=>
                            .collect::<Result<Vec<_>, #err_ty>>()?
                            .into_iter()
                            .unzip()
                        }
                    } else {
                        quote_spanned! {span=>
                            .unzip()
                        }
                    },
                    quote_spanned! {span=>
                        (attrs, #joined_progress)
                    },
                )
            } else {
                (
                    quote_spanned! {span=>
                        attrs
                    },
                    if let Some(err_ty) = &config.result_err {
                        quote_spanned! {span=>
                            .collect::<Result<Vec<_>, #err_ty>>()?
                        }
                    } else {
                        quote_spanned! {span=>
                            .collect::<Vec<_>>()
                        }
                    },
                    quote_spanned! {span=>
                        attrs
                    },
                )
            };
        let map_closure = if config.result_err.is_some() {
            quote_spanned! {span=>
                Ok(#recurse_elem)
            }
        } else {
            quote_spanned! {span=>
                #recurse_elem
            }
        };

        quote_spanned! {span=>
            {
                let #lhs_pat = #attr_ident
                    .into_iter()
                    .map(|elem| #map_closure)
                    #collect_method_call;
                #return_expr
            }
        }
    } else if let Some(inner_tys) = tys::ty_as_tuple(attr_ty) {
        let elem_idents: Vec<_> = (0..inner_tys.len())
            .map(|idx| Ident::new(&format!("elem{}", idx), span))
            .collect();
        let elem_reassigns: Vec<_> = elem_idents
            .iter()
            .zip(inner_tys.iter())
            .map(|(elem_ident, elem_ty)| {
                let recurse_elem = recurse_and_rebuild_attr(
                    config,
                    span,
                    elem_ident,
                    elem_ty,
                    rewrite_args,
                    unpacked_idents,
                    move_assignments,
                );
                let (lhs_pat, do_progress_join) = if config.progress.is_some() {
                    (
                        quote_spanned! {span=>
                            (#elem_ident, elem_progress)
                        },
                        quote_spanned! {span=>
                            let progress = progress.join(elem_progress);
                        },
                    )
                } else {
                    (
                        quote_spanned! {span=>
                            #elem_ident
                        },
                        quote_spanned! {span=>
                            // No join needed
                        },
                    )
                };
                quote_spanned! {span=>
                    let #lhs_pat = #recurse_elem;
                    #do_progress_join
                }
            })
            .collect();
        let (init_progress, return_expr) = if let Some(progress_ty) = &config.progress {
            (
                quote_spanned! {span=>
                    let progress = #progress_ty::identity();
                },
                quote_spanned! {span=>
                    // Return nested tuple with progress
                    ((#(#elem_idents),*), progress)
                },
            )
        } else {
            (
                quote_spanned! {span=>
                    // Nothing
                },
                quote_spanned! {span=>
                    // Just return the tuple
                    (#(#elem_idents),*)
                },
            )
        };
        quote_spanned! {span=>
            {
                let (#(#elem_idents),*) = #attr_ident;
                #init_progress
                #(#elem_reassigns)*
                #return_expr
            }
        }
    } else {
        // We don't recognize this. Fall back to base case
        let config_ident = &config.name;
        let lhs_pat = if unpacked_idents.is_empty() {
            quote_spanned! {span=>
                attr
            }
        } else {
            quote_spanned! {span=>
                (attr, #(#unpacked_idents),*)
            }
        };
        let maybe_question_mark = if config.result_err.is_some() {
            quote_spanned! {span=>
                ?
            }
        } else {
            quote_spanned! {span=>
                // Nothing (no `?' symbol)
            }
        };
        let return_expr = if config.progress.is_some() {
            quote_spanned! {span=>
                (attr, progress)
            }
        } else {
            quote_spanned! {span=>
                attr
            }
        };

        quote_spanned! {span=>
            {
                let #lhs_pat = #attr_ident.#config_ident(#(#rewrite_args),*) #maybe_question_mark;
                #(#move_assignments)*
                #return_expr
            }
        }
    }
}

/// Generates the following for a given config and enum variant:
/// 1. The corresponding variant of the `Reconstruct` enum
/// 2. If `rewrite_to` is set, the corresponding variant of the `Rewritten`
///    enum (else `None`)
/// 3. The corresponding arm in the `match` inside `rebuild()` for
///    `RebuildStackEntry::Reconstruct(_)`
/// 4. The corresponding arm in the match inside `rebuild()` for
///    `RebuildStackEntry::Deconstruct(_)`
fn gen_variants_and_arms(
    config: &parse::RebuildConfig,
    span: Span,
    enum_ident: &Ident,
    variant: &Variant,
) -> Result<
    (
        (TokenStream2, Option<TokenStream2>),
        (TokenStream2, TokenStream2),
    ),
    Error,
> {
    let Variant {
        ident: variant_ident,
        fields: variant_fields,
        ..
    } = variant;
    let variant_fields: Vec<_> = match variant_fields {
        Fields::Named(fields_named @ FieldsNamed { named, .. }) => {
            if named.is_empty() {
                Err(Error::new_spanned(
                    fields_named,
                    concat!(
                        "List of named fields cannot be empty. ",
                        "Use a unit variant instead"
                    ),
                ))
            } else {
                Ok(named.iter().cloned().collect())
            }
        }
        Fields::Unit => Ok(vec![]),
        other_fields => Err(Error::new_spanned(
            other_fields,
            "Expected named fields in enum variant",
        )),
    }?;
    let variant_field_info = variant_fields
        .into_iter()
        .map(|field| {
            let field_name = field.ident.clone().expect("Fields should be named");
            let has_skip_attr = parse::has_skip_recurse_attr(&config.name, span, &field.attrs)?;
            Ok((field, field_name, has_skip_attr))
        })
        .collect::<Result<Vec<_>, Error>>()?;
    // "children" fields have type Box<#enum_ident>. "attr" fields are things like Strings
    let (children_field_info, attr_field_info): (Vec<_>, Vec<_>) = variant_field_info
        .iter()
        .cloned()
        .partition(|(Field { ty: field_ty, .. }, _, has_skip_attr)| {
            // If #[skip_recurse] is set on a child, treat it as an attribute
            tys::ty_is_boxed_ty(field_ty, enum_ident) && !has_skip_attr
        });

    let recurse_attr_field_name_tys = if config.recurse_attrs {
        attr_field_info
            .iter()
            .filter_map(
                |(
                    Field {
                        ty: field_ty,
                        ident: field_ident,
                        ..
                    },
                    _,
                    has_skip_attr,
                )| {
                    if *has_skip_attr || tys::should_skip_attr_ty(field_ty) {
                        None
                    } else {
                        let field_ident = field_ident.clone().expect("All fields should be named");
                        Some((field_ident, field_ty.clone()))
                    }
                },
            )
            .collect()
    } else {
        vec![]
    };

    // First, generate the variant for the enum definition for reconstruction
    let reconstruct_variant_fields = if attr_field_info.is_empty() {
        quote_spanned! {span=>
            // No fields (unit variant)
        }
    } else {
        let stripped_attr_fields: Vec<_> = attr_field_info
            .iter()
            .map(|(field, _, skip_recurse)| {
                let field = field.clone();
                if *skip_recurse {
                    attrs::strip_our_attrs_from_field(field)
                } else {
                    strip_our_attrs_and_rewrite_field_ty(config, false, field)
                }
            })
            .collect();
        // We need to remove any attributes from these fields first
        quote_spanned! {span=>
            { #(#stripped_attr_fields),* }
        }
    };
    let reconstruct_variant = quote_spanned! {span=>
        #variant_ident #reconstruct_variant_fields
    };

    // And, if appropriate, the variant for the Rewritten enum
    let maybe_rewritten_variant = if config.rewrite_to.is_empty() {
        None
    } else {
        let rewritten_variant_fields = if variant_field_info.is_empty() {
            quote_spanned! {span=>
                // No fields (unit variant)
            }
        } else {
            let rewritten_fields: Vec<_> = variant_field_info
                .iter()
                .map(|(field, _, skip_recurse)| {
                    let field = field.clone();
                    if *skip_recurse {
                        attrs::strip_our_attrs_from_field(field)
                    } else {
                        strip_our_attrs_and_rewrite_field_ty(config, true, field)
                    }
                })
                .collect();
            quote_spanned! {span=>
                { #(#rewritten_fields),* }
            }
        };

        Some(quote_spanned! {span=>
            #variant_ident #rewritten_variant_fields
        })
    };

    // These will be helpful for the next one
    let attr_field_names_in_braces = if attr_field_info.is_empty() {
        quote_spanned! {span=>
            // Unit variant
        }
    } else {
        let attr_field_names: Vec<_> = attr_field_info.iter().map(|(_, name, _)| name).collect();
        quote_spanned! {span=>
            { #(#attr_field_names),* }
        }
    };
    let all_field_names_in_braces = if variant_field_info.is_empty() {
        quote_spanned! {span=>
            // Unit variant
        }
    } else {
        let all_field_names: Vec<_> = variant_field_info.iter().map(|(_, name, _)| name).collect();
        quote_spanned! {span=>
            { #(#all_field_names),* }
        }
    };

    // Next, generate the arm of the match that reconstructs this variant
    let children_field_names: Vec<_> = children_field_info
        .iter()
        .map(|(_, name, _)| name)
        .collect();
    let pop_stmts: Vec<_> = children_field_names
        .iter()
        .map(|field_name| {
            let lhs_pat = if config.progress.is_none() {
                quote_spanned! {span=>
                    #field_name
                }
            } else {
                let prog_ident_name = field_name.to_string() + "_progress";
                let prog_ident = Ident::new(&prog_ident_name, span);
                quote_spanned! {span=>
                    (#field_name, #prog_ident)
                }
            };
            let maybe_box_it_up = if config.rewrite_to.is_empty() {
                quote_spanned! {span=>
                    let #field_name = Box::new(#field_name);
                }
            } else {
                quote_spanned! {span=>
                    // Don't create an annoying box
                }
            };
            quote_spanned! {span=>
                let #lhs_pat = out_stack
                    .pop()
                    .expect("Invalid rebuild stack state");
                #maybe_box_it_up
            }
        })
        .collect();
    let recurse_attr_args: Vec<_> = config
        .more_moved_args
        .iter()
        .chain(config.more_copied_args.iter())
        .map(|(arg_name, _)| {
            quote_spanned! {span=>
                #arg_name
            }
        })
        .collect();
    let maybe_init_progress_stmt = if let Some(progress_ty) = &config.progress {
        let identity_expr = if config.recurse_attrs {
            quote_spanned! {span=>
                attr_progress
            }
        } else {
            quote_spanned! {span=>
                #progress_ty::identity()
            }
        };
        let join_expr = children_field_names
            .iter()
            .map(|field_name| {
                let prog_ident_name = field_name.to_string() + "_progress";
                let prog_ident = Ident::new(&prog_ident_name, span);
                prog_ident
            })
            .fold(identity_expr, |acc, progress_ident| {
                quote_spanned! {span=>
                    #acc.join(#progress_ident)
                }
            });
        quote_spanned! {span=>
            let progress = #join_expr;
        }
    } else {
        quote_spanned! {span=>
            // No assignment needed
        }
    };
    let extra_rewrite_args = {
        let mut res = recurse_attr_args.clone();
        if config.progress.is_some() {
            res.push(quote_spanned! {span=>
                progress
            });
        }
        res
    };
    let (unpacked_idents, move_assignments) = {
        let (mut unpacked_idents, move_assignments): (Vec<_>, Vec<_>) = config
            .more_moved_args
            .iter()
            .map(|(arg_ident, _)| {
                let moved_arg_name = arg_ident.to_string() + "_moved";
                let moved_arg_ident = Ident::new(&moved_arg_name, span);
                let move_assignment = quote_spanned! {span=>
                    #arg_ident = #moved_arg_ident;
                };
                (moved_arg_ident, move_assignment)
            })
            .unzip();

        if config.progress.is_some() {
            unpacked_idents.push(Ident::new("progress", span));
        }
        (unpacked_idents, move_assignments)
    };
    let (post_rewrite_pat, maybe_reassign_moved_extra_args) = if config.rewrite.is_some()
        && (config.progress.is_some() || !config.more_moved_args.is_empty())
    {
        (
            quote_spanned! {span=>
                (rewritten, #(#unpacked_idents),*)
            },
            quote_spanned! {span=>
                #(#move_assignments)*
            },
        )
    } else {
        (
            quote_spanned! {span=>
                rewritten
            },
            quote_spanned! {span=>
                // Don't move the extra arg out, no need
            },
        )
    };
    let maybe_progress_pat = if !config.recurse_attrs || config.progress.is_none() {
        quote_spanned! {span=>
            // Nothing
        }
    } else {
        quote_spanned! {span=>
            , attr_progress
        }
    };
    let maybe_question_mark = if let Some(_) = &config.result_err {
        quote_spanned! {span=>
            ?
        }
    } else {
        quote_spanned! {span=>
            // Nothing (no `?' symbol)
        }
    };
    let reconstruct_and_rewrite = if config.rewrite_to.is_empty() {
        let maybe_call_rewrite_method = if let Some(rewrite_func_ident) = &config.rewrite {
            quote_spanned! {span=>
                .#rewrite_func_ident(#(#extra_rewrite_args),*) #maybe_question_mark
            }
        } else {
            quote_spanned! {span=>
                // No method call
            }
        };
        quote_spanned! {span=>
            #enum_ident::#variant_ident #all_field_names_in_braces #maybe_call_rewrite_method
        }
    } else {
        let rewrite_func_ident = config
            .rewrite
            .as_ref()
            .expect("rewrite_to requires rewrite");
        quote_spanned! {span=>
            #enum_ident::#rewrite_func_ident(Rewritten::#variant_ident #all_field_names_in_braces) #maybe_question_mark
        }
    };
    let push_operand = if config.progress.is_none() {
        quote_spanned! {span=>
            rewritten
        }
    } else {
        quote_spanned! {span=>
            (rewritten, progress)
        }
    };
    let reconstruct_arm = quote_spanned! {span=>
        RebuildStackEntry::Reconstruct(Reconstruct::#variant_ident #attr_field_names_in_braces #maybe_progress_pat) => {
                #(#pop_stmts)*
                #maybe_init_progress_stmt
                let #post_rewrite_pat = #reconstruct_and_rewrite;
                #maybe_reassign_moved_extra_args
                out_stack.push(#push_operand);
            }
    };

    // Finally, generate the arm of the match that deconstructs this variant
    let maybe_init_attr_progress = if let Some(progress_ty) = &config.progress
        && config.recurse_attrs
    {
        quote_spanned! {span=>
            let attr_progress = #progress_ty::identity();
        }
    } else {
        quote_spanned! {span=>
            // Nothing
        }
    };
    let reassign_recursed_attrs: Vec<_> = recurse_attr_field_name_tys
        .iter()
        .map(|(attr_ident, attr_ty)| {
            let rebuilt_attr = recurse_and_rebuild_attr(
                config,
                span,
                attr_ident,
                attr_ty,
                &recurse_attr_args,
                &unpacked_idents,
                &move_assignments,
            );
            let (lhs_pat, maybe_join_progress) = if config.progress.is_some() {
                (
                    quote_spanned! {span=>
                        (#attr_ident, this_attr_progress)
                    },
                    quote_spanned! {span=>
                        let attr_progress = attr_progress.join(this_attr_progress);
                    },
                )
            } else {
                (
                    quote_spanned! {span=>
                        #attr_ident
                    },
                    quote_spanned! {span=>
                        // Nothing
                    },
                )
            };
            quote_spanned! {span=>
                let #lhs_pat = #rebuilt_attr;
                #maybe_join_progress
            }
        })
        .collect();
    let maybe_comma_progress = if !config.recurse_attrs || config.progress.is_none() {
        quote_spanned! {span=>
            // Nothing
        }
    } else {
        quote_spanned! {span=>
            , attr_progress
        }
    };
    let push_stmts: Vec<_> = children_field_info
        .iter()
        .map(|(_, field_name, has_skip_attr)| {
            let variant_name = if *has_skip_attr {
                quote_spanned! {span=>
                    Passthrough
                }
            } else {
                quote_spanned! {span=>
                    Deconstruct
                }
            };
            quote_spanned! {span=>
                in_stack.push(RebuildStackEntry::#variant_name(*#field_name));
            }
        })
        .collect();
    let deconstruct_arm = quote_spanned! {span=>
        RebuildStackEntry::Deconstruct(#enum_ident::#variant_ident #all_field_names_in_braces) => {
            #maybe_init_attr_progress
            #(#reassign_recursed_attrs)*
            in_stack.push(RebuildStackEntry::Reconstruct(
                Reconstruct::#variant_ident #attr_field_names_in_braces #maybe_comma_progress));
            #(#push_stmts)*
        }
    };

    Ok((
        (reconstruct_variant, maybe_rewritten_variant),
        (reconstruct_arm, deconstruct_arm),
    ))
}

/// Generates the following for a given config:
/// 1. All variants of the `Reconstruct` enum
/// 2. All variants of the `Rewritten` enum (empty if there should be no such
///    `Rewritten` enum generated)
/// 3. The first half of the arms in the `match` inside `rebuild()` (for
///    `RebuildStackEntry::Reconstruct(_)`)
/// 4. The second half of the arms in the match inside `rebuild()` (for
///    `RebuildStackEntry::Deconstruct(_)`)
fn gen_all_variants_and_arms(
    config: &parse::RebuildConfig,
    span: Span,
    enum_ident: &Ident,
    enum_item: &ItemEnum,
) -> Result<
    (
        Vec<TokenStream2>,
        Vec<TokenStream2>,
        Vec<TokenStream2>,
        Vec<TokenStream2>,
    ),
    Error,
> {
    let results = enum_item
        .variants
        .iter()
        .map(|variant| gen_variants_and_arms(config, span, enum_ident, variant))
        .collect::<Result<Vec<_>, Error>>()?;

    let (generated_variants, generated_arms): (Vec<_>, Vec<_>) = results.into_iter().unzip();
    let (reconstruct_variants, maybe_rewritten_variants): (Vec<_>, Vec<_>) =
        generated_variants.into_iter().unzip();
    let (generated_reconstruct_arms, generated_deconstruct_arms): (Vec<_>, Vec<_>) =
        generated_arms.into_iter().unzip();

    let rewritten_variants = maybe_rewritten_variants
        .into_iter()
        .filter_map(|v| v)
        .collect();

    Ok((
        reconstruct_variants,
        rewritten_variants,
        generated_reconstruct_arms,
        generated_deconstruct_arms,
    ))
}

/// Generates the inner module for this config. This includes any generated
/// enum definitions and the `rebuild()` function itself.
pub fn gen_rebuild_for_config(
    config: parse::RebuildConfig,
    span: Span,
    enum_item: &ItemEnum,
) -> Result<TokenStream2, Error> {
    let namespace_name = &config.name;
    let enum_ident = &enum_item.ident;
    let enum_ty = Type::Path(TypePath {
        qself: None,
        path: Path {
            leading_colon: None,
            segments: std::iter::once(Pair::End(PathSegment {
                ident: enum_ident.clone(),
                arguments: PathArguments::None,
            }))
            .collect(),
        },
    });

    let (
        reconstruct_variants,
        rewritten_variants,
        generated_reconstruct_arms,
        generated_deconstruct_arms,
    ) = gen_all_variants_and_arms(&config, span, enum_ident, enum_item)?;

    let reconstruct_enum = quote_spanned! {span=>
        enum Reconstruct {
            #(#reconstruct_variants),*
        }
    };

    let maybe_rewritten_enum = if rewritten_variants.is_empty() {
        quote_spanned! {span=>
            // No Rewritten enum
        }
    } else {
        quote_spanned! {span=>
            pub enum Rewritten {
                #(#rewritten_variants),*
            }
        }
    };

    let maybe_comma_progress_ty =
        if let (true, Some(progress_ty)) = (config.recurse_attrs, &config.progress) {
            quote_spanned! {span=>
                , #progress_ty
            }
        } else {
            quote_spanned! {span=>
                // Nothing
            }
        };
    let stack_entry_enum = quote_spanned! {span=>
        enum RebuildStackEntry {
            Deconstruct(#enum_ident),
            Reconstruct(Reconstruct #maybe_comma_progress_ty),
        }
    };

    let maybe_generic_params = if config.more_generic_params.is_empty() {
        quote_spanned! {span=>
            // No generic params (e.g., no `<T>`)
        }
    } else {
        let generic_params = &config.more_generic_params;
        quote_spanned! {span=>
            <#(#generic_params),*>
        }
    };
    let maybe_more_args = if config.more_moved_args.is_empty() && config.more_copied_args.is_empty()
    {
        quote_spanned! {span=>
            // No additional args (e.g. `, f: F`)
        }
    } else {
        // Mark this as mut because we will reassign it after each call to the rewriter
        let more_args: Vec<_> = config
            .more_moved_args
            .iter()
            .map(|(arg_name, arg_ty)| {
                quote_spanned! {span=>
                    mut #arg_name: #arg_ty
                }
            })
            .chain(config.more_copied_args.iter().map(|(arg_name, arg_ty)| {
                // No mut because we never reassign this
                quote_spanned! {span=>
                    #arg_name: #arg_ty
                }
            }))
            .collect();
        quote_spanned! {span=>
            , #(#more_args),*
        }
    };
    let maybe_where = if config.more_where.is_empty() {
        quote_spanned! {span=>
            // No where clause (e.g. `where F: FnMut(String) -> String`)
        }
    } else {
        let where_preds = &config.more_where;
        quote_spanned! {span=>
            where #(#where_preds),*
        }
    };
    let root_deconstruct_expr = quote_spanned! {span=>
        RebuildStackEntry::Deconstruct(root)
    };
    let rewrite_to_ty = config.rewrite_ty_if_needed(enum_ty);
    let (maybe_result_reassign, result_ty) =
        if config.more_moved_args.is_empty() && config.progress.is_none() {
            (
                quote_spanned! {span=>
                    // No need to change result.
                },
                // Result is this enum
                quote_spanned! {span=>
                    #rewrite_to_ty
                },
            )
        } else {
            let (mut res_names, mut res_tys): (Vec<_>, Vec<_>) = config
                .more_moved_args
                .iter()
                .map(|(name, ty)| (name, ty))
                .unzip();

            let progress_var_ident = Ident::new("progress", span);
            let maybe_progress_unpack_stmt = if let Some(progress_ty) = &config.progress {
                res_names.push(&progress_var_ident);
                res_tys.push(progress_ty);

                quote_spanned! {span=>
                    let (result, #progress_var_ident) = result;
                }
            } else {
                quote_spanned! {span=>
                    // No unpacking of result needed
                }
            };

            (
                quote_spanned! {span=>
                    #maybe_progress_unpack_stmt
                    let result = (result, #(#res_names),*);
                },
                quote_spanned! {span=>
                    (#rewrite_to_ty, #(#res_tys),*)
                },
            )
        };
    let (rebuild_func_ret_ty, return_expr) = if let Some(err_ident) = &config.result_err {
        (
            quote_spanned! {span=>
                Result<#result_ty, #err_ident>
            },
            quote_spanned! {span=>
                Ok(result)
            },
        )
    } else {
        (
            quote_spanned! {span=>
                #result_ty
            },
            quote_spanned! {span=>
                result
            },
        )
    };
    let rebuild_func = quote_spanned! {span=>
        pub fn rebuild #maybe_generic_params (root: #enum_ident #maybe_more_args) -> #rebuild_func_ret_ty #maybe_where {
            let mut in_stack = vec![#root_deconstruct_expr];
            let mut out_stack = vec![];

            while let Some(ent) = in_stack.pop() {
                match ent {
                    #(#generated_deconstruct_arms)*
                    #(#generated_reconstruct_arms)*
                }
            }

            assert!(in_stack.is_empty(), "in_stack is not empty");
            assert_eq!(out_stack.len(), 1, "out_stack should have 1 entry");
            let result = out_stack
                .pop()
                .expect("out_stack is empty even though I just confirmed it had 1 entry");
            #maybe_result_reassign
            #return_expr
        }
    };

    let module = quote_spanned! {span=>
        pub mod #namespace_name {
            use super::super::*;

            #reconstruct_enum

            #maybe_rewritten_enum

            #stack_entry_enum

            #rebuild_func
        }
    };
    Ok(module)
}
