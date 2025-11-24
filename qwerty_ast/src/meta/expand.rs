use crate::{
    error::{LowerError, LowerErrorKind, TypeErrorKind},
    meta::{
        DimExpr, DimVar, MetaFunc, MetaFunctionDef, MetaProgram, MetaType, Progress,
        infer::DimVarAssignments,
        qpu,
        type_dim::{dim_expr, meta_type},
    },
};
use dashu::integer::IBig;
use qwerty_ast_macros::rebuild;
use std::collections::{HashMap, HashSet, hash_map::Entry};

mod expand_classical;
mod expand_qpu;

#[derive(Debug, Clone)]
pub enum AliasBinding {
    BasisAlias {
        rhs: qpu::MetaBasis,
    },
    BasisAliasRec {
        base_cases: HashMap<IBig, qpu::MetaBasis>,
        recursive_step: Option<(String, qpu::MetaBasis)>,
    },
}

#[derive(Debug, Clone)]
pub enum MacroBinding {
    ExprMacro {
        lhs_pat: qpu::ExprMacroPattern,
        rhs: qpu::MetaExpr,
    },
    BasisMacro {
        lhs_pat: qpu::BasisMacroPattern,
        rhs: qpu::MetaExpr,
    },
    BasisGeneratorMacro {
        lhs_pat: qpu::BasisMacroPattern,
        rhs: qpu::MetaBasisGenerator,
    },
}

#[derive(Debug, Clone)]
pub enum DimVarValue {
    Unknown,
    Known(IBig),
}

/// The scope to which a new (currently internal) dimvar would belong
#[derive(Debug, Clone)]
pub enum DimVarScope {
    /// A global dimension variable. Used only in the REPL currently.
    Global,
    /// A dimension variable for a function with the provided name.
    Func(String),
}

#[derive(Debug, Clone)]
pub struct MacroEnv {
    /// Used for allocating new dimension variables
    new_dim_var_scope: DimVarScope,
    next_internal_dim_var_id: usize,
    pub aliases: HashMap<String, AliasBinding>,
    pub macros: HashMap<String, MacroBinding>,
    pub dim_vars: HashMap<DimVar, DimVarValue>,
    pub vec_symbols: HashMap<char, qpu::MetaVector>,
}

impl MacroEnv {
    pub fn new(new_dim_var_scope: DimVarScope) -> MacroEnv {
        MacroEnv {
            new_dim_var_scope,
            next_internal_dim_var_id: 0,
            aliases: HashMap::new(),
            macros: HashMap::new(),
            dim_vars: HashMap::new(),
            vec_symbols: HashMap::new(),
        }
    }

    pub fn to_dv_assign(&self) -> DimVarAssignments {
        DimVarAssignments::new(
            self.dim_vars
                .iter()
                .filter_map(|(k, v)| match v {
                    DimVarValue::Unknown => None,
                    DimVarValue::Known(val) => Some((k.clone(), val.clone())),
                })
                .collect(),
        )
    }

    pub fn update_from_dv_assign(
        &mut self,
        dv_assign: &DimVarAssignments,
    ) -> Result<(), LowerError> {
        for (dv, val) in dv_assign.iter() {
            if let Some(DimVarValue::Known(old_val)) = self
                .dim_vars
                .insert(dv.clone(), DimVarValue::Known(val.clone()))
                && old_val != *val
            {
                return Err(LowerError {
                    kind: LowerErrorKind::DimVarConflict {
                        dim_var_name: dv.to_string(),
                        first_val: val.clone(),
                        second_val: old_val,
                    },
                    // TODO: pass a helpful debug location
                    dbg: None,
                });
            }
        }

        Ok(())
    }

    /// Add a temporary dimension variable that we feel reasonably confident
    /// that inference can take care of.
    pub fn allocate_internal_dim_var(&mut self) -> DimVar {
        loop {
            let var_name = format!("__{}", self.next_internal_dim_var_id);
            self.next_internal_dim_var_id += 1;
            let var = match &self.new_dim_var_scope {
                DimVarScope::Global => DimVar::GlobalVar { var_name },
                DimVarScope::Func(func_name) => DimVar::FuncVar {
                    var_name,
                    func_name: func_name.clone(),
                },
            };
            if let Entry::Vacant(vacant) = self.dim_vars.entry(var.clone()) {
                vacant.insert(DimVarValue::Unknown);
                break var;
            }
        }
    }
}

impl DimExpr {
    pub fn substitute_dim_var(self, dim_var: &DimVar, new_dim_expr: &DimExpr) -> Self {
        rebuild!(DimExpr, self, substitute_dim_var, dim_var, new_dim_expr)
    }

    /// Called by the `gen_rebuild` attribute macro invoked in `meta/type_dim.rs`.
    pub(crate) fn substitute_dim_var_rewriter(
        self,
        dim_var: &DimVar,
        new_dim_expr: &DimExpr,
    ) -> Self {
        match self {
            DimExpr::DimVar { var, dbg } => {
                if &var == dim_var {
                    new_dim_expr.clone()
                } else {
                    DimExpr::DimVar { var, dbg }
                }
            }

            other @ (DimExpr::DimSum { .. }
            | DimExpr::DimProd { .. }
            | DimExpr::DimPow { .. }
            | DimExpr::DimNeg { .. }
            | DimExpr::DimConst { .. }) => other,
        }
    }

    pub fn expand(self, env: &MacroEnv) -> Result<(DimExpr, Progress), LowerError> {
        rebuild!(DimExpr, self, expand, env)
    }

    pub(crate) fn expand_rewriter(
        self,
        env: &MacroEnv,
        children_progress: Progress,
    ) -> Result<(DimExpr, Progress), LowerError> {
        match (self, children_progress) {
            (DimExpr::DimVar { var, dbg }, _) => {
                if let Some(dim_var_value) = env.dim_vars.get(&var) {
                    if let DimVarValue::Known(val) = dim_var_value {
                        Ok((
                            DimExpr::DimConst {
                                val: val.clone(),
                                dbg,
                            },
                            Progress::Full,
                        ))
                    } else {
                        Ok((DimExpr::DimVar { var, dbg }, Progress::Partial))
                    }
                } else {
                    Err(LowerError {
                        kind: LowerErrorKind::TypeError {
                            kind: TypeErrorKind::UndefinedVariable(var.to_string()),
                        },
                        dbg: dbg.clone(),
                    })
                }
            }

            (DimExpr::DimSum { left, right, dbg }, Progress::Full) => {
                let left_val = left.extract_bigint()?;
                let right_val = right.extract_bigint()?;
                let val = left_val + right_val;
                Ok((DimExpr::DimConst { val, dbg }, Progress::Full))
            }

            (DimExpr::DimProd { left, right, dbg }, Progress::Full) => {
                let left_val = left.extract_bigint()?;
                let right_val = right.extract_bigint()?;
                let val = left_val * right_val;
                Ok((DimExpr::DimConst { val, dbg }, Progress::Full))
            }

            (DimExpr::DimPow { base, pow, dbg }, Progress::Full) => {
                let base_val = base.extract_bigint()?;
                let pow_val = pow.extract()?;
                let val = base_val.pow(pow_val);
                Ok((DimExpr::DimConst { val, dbg }, Progress::Full))
            }

            (DimExpr::DimNeg { val, dbg }, Progress::Full) => {
                let val = val.extract_bigint()?;
                let val = -val;
                Ok((DimExpr::DimConst { val, dbg }, Progress::Full))
            }

            (
                unfinished @ (DimExpr::DimSum { .. }
                | DimExpr::DimProd { .. }
                | DimExpr::DimPow { .. }
                | DimExpr::DimNeg { .. }),
                Progress::Partial,
            ) => Ok((unfinished, Progress::Partial)),

            (done @ DimExpr::DimConst { .. }, _) => Ok((done, Progress::Full)),
        }
    }
}

impl MetaType {
    pub fn expand(self, env: &MacroEnv) -> Result<(MetaType, Progress), LowerError> {
        rebuild!(MetaType, self, expand, env)
    }
}

pub trait Expandable {
    fn expand(self, env: &mut MacroEnv) -> Result<(Self, Progress), LowerError>
    where
        Self: Sized;
}

impl<S: Expandable> MetaFunctionDef<S> {
    fn expand(self, dvs: &DimVarAssignments) -> Result<(MetaFunctionDef<S>, Progress), LowerError> {
        let MetaFunctionDef {
            name,
            args,
            ret_type,
            body,
            is_rev,
            dim_vars,
            dbg,
        } = self;

        let mut env = MacroEnv::new(DimVarScope::Func(name.to_string()));

        for dim_var_name in &dim_vars {
            let dv = DimVar::FuncVar {
                var_name: dim_var_name.to_string(),
                func_name: name.to_string(),
            };
            let dv_val = if let Some(val) = dvs.get(&dv) {
                DimVarValue::Known(val.clone())
            } else {
                DimVarValue::Unknown
            };

            if env.dim_vars.insert(dv, dv_val).is_some() {
                // Duplicate dimvar
                return Err(LowerError {
                    kind: LowerErrorKind::Malformed,
                    dbg: dbg.clone(),
                });
            }
        }
        let expanded_pairs = body
            .into_iter()
            .map(|stmt| stmt.expand(&mut env))
            .collect::<Result<Vec<_>, LowerError>>()?;
        let (expanded_stmts, stmt_progs): (Vec<_>, Vec<_>) = expanded_pairs.into_iter().unzip();
        let stmt_prog = stmt_progs
            .into_iter()
            .fold(Progress::identity(), |acc, stmt| acc.join(stmt));

        // Why do this? Because we may have inserted some internal dim vars
        // into the context while expanding statements.
        let env_dim_vars: HashSet<_> = env
            .dim_vars
            .keys()
            .map(|var| {
                if let DimVar::FuncVar {
                    var_name,
                    func_name,
                } = var
                    && func_name == &name
                {
                    var_name.clone()
                } else {
                    // In principle, we could ignore this, but it is better to be
                    // noisy to catch bugs
                    panic!(concat!(
                        "Dimvar in final macro environment is either not a ",
                        "function variable or from a different function"
                    ))
                }
            })
            .collect();
        let old_dim_vars: HashSet<_> = dim_vars.iter().cloned().collect();
        let new_dim_vars: Vec<_> = dim_vars
            .into_iter()
            .chain(env_dim_vars.difference(&old_dim_vars).cloned())
            .collect();

        let (expanded_ret_ty, ret_ty_prog) = if let Some(ret_ty) = ret_type {
            let (ty, prog) = ret_ty.expand(&env)?;
            (Some(ty), prog)
        } else {
            // Trivially fully expanded (but inference will flag it as not
            // fully inferred)
            (None, Progress::Full)
        };
        let arg_pairs = args
            .into_iter()
            .map(|(arg_type, arg_name)| {
                if let Some(arg_ty) = arg_type {
                    arg_ty.expand(&env).map(|(expanded_arg_ty, arg_ty_prog)| {
                        ((Some(expanded_arg_ty), arg_name.to_string()), arg_ty_prog)
                    })
                } else {
                    // Inference will flag this
                    Ok(((None, arg_name.to_string()), Progress::Full))
                }
            })
            .collect::<Result<Vec<_>, LowerError>>()?;
        let (expanded_args, arg_progs): (Vec<_>, Vec<_>) = arg_pairs.into_iter().unzip();
        let args_prog = arg_progs
            .into_iter()
            .fold(Progress::identity(), Progress::join);

        let expanded_func_def = MetaFunctionDef {
            name,
            args: expanded_args,
            ret_type: expanded_ret_ty,
            body: expanded_stmts,
            is_rev,
            dim_vars: new_dim_vars,
            dbg,
        };
        let progress = stmt_prog.join(ret_ty_prog).join(args_prog);
        Ok((expanded_func_def, progress))
    }
}

impl MetaFunc {
    fn expand(self, dvs: &DimVarAssignments) -> Result<(MetaFunc, Progress), LowerError> {
        match self {
            MetaFunc::Qpu(qpu_func_def) => qpu_func_def
                .expand(dvs)
                .map(|(expanded_func_def, prog)| (MetaFunc::Qpu(expanded_func_def), prog)),

            MetaFunc::Classical(classical_func_def) => classical_func_def
                .expand(dvs)
                .map(|(expanded_func_def, prog)| (MetaFunc::Classical(expanded_func_def), prog)),
        }
    }
}

impl MetaProgram {
    /// Try to expand as many metaQwerty constructs in this program, returning
    /// a new one.
    pub fn expand(
        self,
        dv_assign: &DimVarAssignments,
    ) -> Result<(MetaProgram, Progress), LowerError> {
        let MetaProgram { funcs, dbg } = self;
        let funcs_pairs = funcs
            .into_iter()
            .map(|func| func.expand(dv_assign))
            .collect::<Result<Vec<(MetaFunc, Progress)>, LowerError>>()?;
        let (expanded_funcs, progresses): (Vec<_>, Vec<_>) = funcs_pairs.into_iter().unzip();
        let progress = progresses
            .into_iter()
            .fold(Progress::identity(), |acc, prog| acc.join(prog));

        Ok((
            MetaProgram {
                funcs: expanded_funcs,
                dbg,
            },
            progress,
        ))
    }
}
