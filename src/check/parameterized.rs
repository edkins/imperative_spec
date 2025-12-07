use std::collections::HashMap;

use crate::{
    check::ztype_inference::TypeError,
    syntax::ast::{Bound, Type, TypeArg},
};

#[derive(Clone)]
pub enum ParameterizedType {
    Param(String),
    Named(String, Vec<ParameterizedTypeArg>),
}

#[derive(Clone)]
pub enum ParameterizedTypeArg {
    Type(ParameterizedType),
    Bound(Bound),
}

impl std::fmt::Display for ParameterizedType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParameterizedType::Param(name) => write!(f, "{}", name),
            ParameterizedType::Named(name, params) => {
                if params.is_empty() {
                    write!(f, "{}", name)
                } else {
                    let params_str = params
                        .iter()
                        .map(|p| format!("{}", p))
                        .collect::<Vec<String>>()
                        .join(", ");
                    write!(f, "{}<{}>", name, params_str)
                }
            }
        }
    }
}

impl std::fmt::Display for ParameterizedTypeArg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParameterizedTypeArg::Type(t) => write!(f, "{}", t),
            ParameterizedTypeArg::Bound(b) => write!(f, "{}", b),
        }
    }
}

impl ParameterizedTypeArg {
    pub fn to_type(&self) -> Result<TypeArg, TypeError> {
        match self {
            ParameterizedTypeArg::Bound(b) => Ok(TypeArg::Bound(b.clone())),
            ParameterizedTypeArg::Type(t) => Ok(TypeArg::Type(t.to_type()?)),
        }
    }

    pub fn from_type(type_arg: &TypeArg) -> Self {
        match type_arg {
            TypeArg::Bound(b) => ParameterizedTypeArg::Bound(b.clone()),
            TypeArg::Type(t) => ParameterizedTypeArg::Type(ParameterizedType::from_type(t)),
        }
    }

    pub fn has_params(&self) -> bool {
        match self {
            ParameterizedTypeArg::Bound(_) => false,
            ParameterizedTypeArg::Type(t) => t.has_params(),
        }
    }

    pub fn unify(
        &self,
        concrete: &TypeArg,
        mapping: &mut HashMap<String, Type>,
    ) -> Result<(), TypeError> {
        match (self, concrete) {
            (ParameterizedTypeArg::Bound(b1), TypeArg::Bound(b2)) => {
                if b1 != b2 {
                    return Err(TypeError {
                        message: format!("Bound mismatch: {} vs {}", b1, b2),
                    });
                }
                Ok(())
            }
            (ParameterizedTypeArg::Type(t_param), TypeArg::Type(t_concrete)) => {
                t_param.unify(t_concrete, mapping)
            }
            _ => Err(TypeError {
                message: "Cannot unify bound with type".to_owned(),
            }),
        }
    }

    pub fn instantiate(&self, mapping: &HashMap<String, Type>) -> Result<TypeArg, TypeError> {
        match self {
            ParameterizedTypeArg::Bound(b) => Ok(TypeArg::Bound(b.clone())),
            ParameterizedTypeArg::Type(t) => {
                let concrete_type = t.instantiate(mapping)?;
                Ok(TypeArg::Type(concrete_type))
            }
        }
    }

    pub fn most_general(&self) -> Result<Self, TypeError> {
        match self {
            ParameterizedTypeArg::Bound(b) => Ok(ParameterizedTypeArg::Bound(b.clone())),
            ParameterizedTypeArg::Type(t) => {
                let general_type = t.most_general()?;
                Ok(ParameterizedTypeArg::Type(general_type))
            }
        }
    }
}

impl ParameterizedType {
    pub fn basic(name: &str) -> Self {
        ParameterizedType::Named(name.to_owned(), vec![])
    }

    pub fn lambda_type(arg_types: &[ParameterizedType], return_type: &ParameterizedType) -> Self {
        let mut args = arg_types
            .iter()
            .map(|t| ParameterizedTypeArg::Type(t.clone()))
            .collect::<Vec<ParameterizedTypeArg>>();
        let ret = ParameterizedTypeArg::Type(return_type.clone());
        args.push(ret);
        ParameterizedType::Named("Lambda".to_owned(), args)
    }

    pub fn to_type(&self) -> Result<Type, TypeError> {
        match self {
            ParameterizedType::Param(name) => Err(TypeError {
                message: format!("Unresolved type parameter: {}", name),
            }),
            ParameterizedType::Named(name, params) => {
                let type_args = params
                    .iter()
                    .map(|p| p.to_type())
                    .collect::<Result<Vec<TypeArg>, TypeError>>()?;
                Ok(Type {
                    name: name.clone(),
                    type_args,
                })
            }
        }
    }

    pub fn from_type(typ: &Type) -> Self {
        let params = typ
            .type_args
            .iter()
            .map(|ta| ParameterizedTypeArg::from_type(ta))
            .collect::<Vec<ParameterizedTypeArg>>();
        ParameterizedType::Named(typ.name.clone(), params)
    }

    pub fn has_params(&self) -> bool {
        match self {
            ParameterizedType::Param(_) => true,
            ParameterizedType::Named(_, params) => params.iter().any(|p| p.has_params()),
        }
    }

    pub fn most_general(&self) -> Result<Self, TypeError> {
        if !self.has_params() {
            return Ok(Self::from_type(&self.to_type()?.most_general_type()));
        }
        match self {
            ParameterizedType::Param(name) => Ok(ParameterizedType::Param(name.clone())),
            ParameterizedType::Named(name, params) => {
                if name == "Array" {
                    // Special case: Array<T,n> becomes Seq<T>
                    if params.len() != 2 {
                        return Err(TypeError {
                            message: format!(
                                "Array type must have 2 parameters, found {}",
                                params.len()
                            ),
                        });
                    }
                    let general_params = vec![params[0].most_general()?];
                    Ok(ParameterizedType::Named("Seq".to_owned(), general_params))
                } else if name == "Vec" {
                    // Special case: Vec<T> becomes Seq<T>
                    if params.len() != 1 {
                        return Err(TypeError {
                            message: format!(
                                "Vec type must have 1 parameter, found {}",
                                params.len()
                            ),
                        });
                    }
                    let general_params = vec![params[0].most_general()?];
                    Ok(ParameterizedType::Named("Seq".to_owned(), general_params))
                } else {
                    let general_params = params.iter().map(|p| p.most_general()).collect::<Result<
                        Vec<ParameterizedTypeArg>,
                        TypeError,
                    >>(
                    )?;
                    Ok(ParameterizedType::Named(name.clone(), general_params))
                }
            }
        }
    }

    pub fn unify(
        &self,
        concrete: &Type,
        mapping: &mut HashMap<String, Type>,
    ) -> Result<(), TypeError> {
        self.most_general()?
            .unify_inner(&concrete.most_general_type(), mapping)
    }

    fn unify_inner(
        &self,
        concrete: &Type,
        mapping: &mut HashMap<String, Type>,
    ) -> Result<(), TypeError> {
        match self {
            ParameterizedType::Param(name) => {
                if let Some(mapped_type) = mapping.get(name) {
                    if !mapped_type.compatible_with(concrete) {
                        // TODO: if they're compatible but not equal, we might want to merge them instead
                        // e.g. u64 and int
                        return Err(TypeError {
                            message: format!(
                                "Type parameter {} already mapped to {}, cannot map to {}",
                                name, mapped_type, concrete
                            ),
                        });
                    }
                } else {
                    mapping.insert(name.clone(), concrete.clone());
                }
                Ok(())
            }
            ParameterizedType::Named(name, params) => {
                if &concrete.name != name {
                    return Err(TypeError {
                        message: format!(
                            "Type name mismatch: expected {}, found {}",
                            name, concrete.name
                        ),
                    });
                }
                if params.len() != concrete.type_args.len() {
                    return Err(TypeError {
                        message: format!(
                            "Type argument length mismatch for {}: expected {}, found {}",
                            name,
                            params.len(),
                            concrete.type_args.len()
                        ),
                    });
                }
                for (param, concrete_arg) in params.iter().zip(&concrete.type_args) {
                    param.unify(concrete_arg, mapping)?;
                }
                Ok(())
            }
        }
    }

    pub fn instantiate(&self, mapping: &HashMap<String, Type>) -> Result<Type, TypeError> {
        match self {
            ParameterizedType::Param(name) => {
                if let Some(concrete_type) = mapping.get(name) {
                    Ok(concrete_type.clone())
                } else {
                    Err(TypeError {
                        message: format!("Unmapped type parameter: {}", name),
                    })
                }
            }
            ParameterizedType::Named(name, params) => {
                let type_args = params
                    .iter()
                    .map(|p| p.instantiate(mapping))
                    .collect::<Result<Vec<TypeArg>, TypeError>>()?;
                Ok(Type {
                    name: name.clone(),
                    type_args,
                })
            }
        }
    }
}
