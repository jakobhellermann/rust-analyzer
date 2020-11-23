use crate::{
    assist_context::AssistBuilder,
    assist_context::{AssistContext, Assists},
    AssistId, AssistKind,
};
use hir::{db::HirDatabase, Semantics};
use ide_db::{traits::resolve_target_trait, RootDatabase};
use syntax::ast::{self, make, AstNode, GenericParamsOwner, NameOwner};

// Assist: add_missing_generics
//
// Adds missing generic parameters to an impl.
//
// ```
// struct MyStruct<T>(T);
//
// impl MyStruct<T<|>> {}
// ```
// ->
// ```
// struct MyStruct<T>(T);
//
// impl<T> MyStruct<T> {}
// ```
pub(crate) fn add_missing_generics(acc: &mut Assists, ctx: &AssistContext) -> Option<()> {
    add_missing_generics_inner(
        acc,
        ctx,
        "add_missing_generics",
        "Add missing generics to impl block",
    )
}

type Vec<T> = smallvec::SmallVec<[T; 4]>;

pub(crate) fn add_missing_generics_inner(
    acc: &mut Assists,
    ctx: &AssistContext,
    assist_id: &'static str,
    label: &'static str,
) -> Option<()> {
    let impl_def = ctx.find_node_at_offset::<ast::Impl>()?;

    let struct_params: Vec<hir::TypeParam> = resolve_self_ty(&ctx.sema, &impl_def)
        .into_iter()
        .flat_map(|target_trait| hir::GenericDef::Adt(target_trait).params(ctx.db()))
        .filter(|type_param| !is_default_type_param(type_param, ctx.db()))
        .collect();
    let trait_params: Vec<hir::TypeParam> = resolve_target_trait(&ctx.sema, &impl_def)
        .into_iter()
        .flat_map(|target_trait| hir::GenericDef::Trait(target_trait).params(ctx.db()))
        .filter(|type_param| !is_default_type_param(type_param, ctx.db()))
        .skip(1) // trait type parameters always include 'Self'
        .collect();

    if struct_params.is_empty() && trait_params.is_empty() {
        return None;
    }

    // the params which are already specified in the impl
    let existing_impl_generics: Vec<ast::GenericParam> =
        impl_def.generic_param_list().iter().flat_map(|list| list.generic_params()).collect();
    let existing_trait_generics: Vec<ast::GenericArg> = impl_def
        .trait_()
        .and_then(path_generics)
        .into_iter()
        .flat_map(|generics| generics.generic_args())
        .collect();
    let existing_struct_generics: Vec<ast::GenericArg> = impl_def
        .self_ty()
        .and_then(path_generics)
        .into_iter()
        .flat_map(|generics| generics.generic_args())
        .collect();

    if existing_impl_generics.len() >= struct_params.len() + trait_params.len() {
        return None;
    }

    let (impl_new, trait_new, struct_new) = determine_missing_generics(
        struct_params.into_iter().map(|p| type_param_to_name(&p, ctx.db())),
        trait_params.into_iter().map(|p| type_param_to_name(&p, ctx.db())),
        existing_impl_generics.into_iter().map(generic_param_to_name),
        existing_trait_generics.into_iter().map(generic_arg_to_name),
        existing_struct_generics.into_iter().map(generic_arg_to_name),
    );

    let impl_generics_new: ast::GenericParamList =
        make::generic_param_list(impl_new.into_iter().map(|name| make::generic_param(name, None)));

    let new_trait_generics: Option<ast::GenericArgList> =
        if !trait_new.is_empty() { Some(make::generic_arg_list(trait_new)) } else { None };
    let new_struct_generics: Option<ast::GenericArgList> =
        if !struct_new.is_empty() { Some(make::generic_arg_list(struct_new)) } else { None };

    // assist
    let impl_offset = impl_def.impl_token()?.text_range().end();
    let target = impl_def.syntax().text_range();
    acc.add(AssistId(assist_id, AssistKind::QuickFix), label, target, |builder| {
        let old_impl_generics = impl_def.generic_param_list();
        let old_trait_generics = impl_def.trait_().map(path_generics).flatten();
        let old_struct_generics = impl_def.self_ty().map(path_generics).flatten();

        let trait_offset = impl_def.trait_().map(|t| t.syntax().text_range().end());
        let struct_offset = impl_def.self_ty().map(|t| t.syntax().text_range().end());

        replace_or_insert_at(builder, old_impl_generics, impl_generics_new, Some(impl_offset));
        if let Some(new_trait_generics) = new_trait_generics {
            replace_or_insert_at(builder, old_trait_generics, new_trait_generics, trait_offset);
        }
        if let Some(new_struct_generics) = new_struct_generics {
            replace_or_insert_at(builder, old_struct_generics, new_struct_generics, struct_offset);
        }
    })
}

fn replace_or_insert_at<N: ast::AstNode + std::fmt::Display>(
    builder: &mut AssistBuilder,
    old: Option<N>,
    new: N,
    offset: Option<syntax::TextSize>,
) {
    match old {
        Some(old) => builder.replace_ast(old, new),
        None => {
            if let Some(offset) = offset {
                builder.insert(offset, new.to_string())
            }
        }
    }
}

fn is_default_type_param(type_param: &hir::TypeParam, db: &dyn HirDatabase) -> bool {
    let default_param = type_param.default(db);
    default_param.map_or(false, |param| !param.is_unknown())
}

/// Given the `impl` block, attempts to find the Self-Type
fn resolve_self_ty(sema: &Semantics<RootDatabase>, impl_def: &ast::Impl) -> Option<hir::Adt> {
    let ast_path =
        impl_def.self_ty().map(|it| it.syntax().clone()).and_then(ast::PathType::cast)?.path()?;

    match sema.resolve_path(&ast_path) {
        Some(hir::PathResolution::Def(hir::ModuleDef::Adt(def))) => Some(def),
        _ => None,
    }
}
fn type_param_to_name(type_param: &hir::TypeParam, db: &dyn HirDatabase) -> String {
    type_param.name(db).to_string()
}
fn generic_param_to_name(generic_param: ast::GenericParam) -> String {
    match generic_param {
        ast::GenericParam::TypeParam(ty) => ty.name().expect("todo").to_string(),
        _ => todo!(),
    }
}
fn generic_arg_to_name(generic_param: ast::GenericArg) -> String {
    match generic_param {
        ast::GenericArg::TypeArg(ty) => match ty.ty().expect("todo") {
            ast::Type::PathType(path) => path
                .path()
                .expect("todo")
                .segment()
                .expect("todo")
                .name_ref()
                .expect("todo")
                .to_string(),
            _ => todo!(),
        },
        _ => todo!(),
    }
}

fn path_generics(typ: ast::Type) -> Option<ast::GenericArgList> {
    ast::PathType::cast(typ.syntax().clone())?.path()?.segment()?.generic_arg_list()
}

/// Given two iterators &[1,2,3], &[a,b,c,d,e]
/// this function will return a new one yielding
/// 1,2,3,d,e
fn first_then_remaining_second<'a, I1, I2, T>(
    mut i1: I1,
    mut i2: I2,
) -> impl Iterator<Item = T> + 'a
where
    I1: Iterator<Item = T> + 'a,
    I2: Iterator<Item = T> + 'a,
{
    std::iter::from_fn(move || i1.next().or(i2.next()))
}

/// struct X<T, U>; // struct_params
/// trait Foo<T, U>; // trait_params
/// impl Foo<A> for X<T> {} // existing_{impl,trait,struct}
/// -->
/// impl<A, U, T, B> Foo<A, U> for X<T, B> {} // return (new_impl, new_trait, new_struct)
fn determine_missing_generics(
    struct_params: impl Iterator<Item = String>,
    trait_params: impl Iterator<Item = String>,
    existing_impl: impl Iterator<Item = String>,
    existing_trait: impl Iterator<Item = String>,
    existing_struct: impl Iterator<Item = String>,
) -> (Vec<String>, Vec<String>, Vec<String>) {
    let mut new_impl_generics: Vec<(String, bool)> =
        existing_impl.into_iter().map(|s| (s.to_string(), false)).collect();
    let mut new_trait_generics = Vec::new();
    let mut new_struct_generics = Vec::new();

    // attempts to find an unused uppercase character in `new_impl_generics`,
    // defauls to '_'
    let generate_fresh = |vec: &[(String, bool)]| {
        ('A'..='Z')
            .map(|c| c.to_string())
            .skip_while(|char| vec.iter().any(|(i, _)| i == char))
            .next()
            .unwrap_or("_".to_string())
    };

    let mut add_to_new_impl = |item: String| {
        let already_in = new_impl_generics.iter().find(|(i, _)| i == &item);
        match already_in {
            // already in and used, generate a unique one
            Some((_, true)) => {
                let unique: String = generate_fresh(&new_impl_generics);
                new_impl_generics.push((unique.clone(), true));
                unique
            }
            // already in and unused
            Some((_, false)) => item,
            // not in there, therefore we add it
            None => {
                new_impl_generics.push((item.clone(), true));
                item
            }
        }
    };

    for parameter in first_then_remaining_second(existing_trait, trait_params) {
        let name = add_to_new_impl(parameter);
        new_trait_generics.push(name);
    }
    for parameter in first_then_remaining_second(existing_struct, struct_params) {
        let name = add_to_new_impl(parameter);
        new_struct_generics.push(name);
    }

    let new_impl_generics = new_impl_generics.into_iter().map(|(item, _)| item).collect();
    (new_impl_generics, new_trait_generics, new_struct_generics)
}

#[cfg(test)]
mod tests {
    use crate::tests::{check_assist, check_assist_not_applicable};

    use super::*;

    #[test]
    fn test_empty_impl() {
        check_assist(
            add_missing_generics,
            r#"
            struct X<T>(T);
            impl X<T> <|>{}
            "#,
            r#"
            struct X<T>(T);
            impl<T> X<T> {}
            "#,
        );
    }

    #[test]
    fn test_with_one_param() {
        check_assist(
            add_missing_generics,
            r#"
            struct X<T, U>(T, U);
            impl<T> X<T, U> <|>{}
            "#,
            r#"
            struct X<T, U>(T, U);
            impl<T, U> X<T, U> {}
            "#,
        );
    }

    #[test]
    fn test_inapplicable() {
        check_assist_not_applicable(
            add_missing_generics,
            r#"
            struct X(u32);
            impl X <|>{}
            "#,
        );
    }

    #[test]
    fn test_already_specified() {
        check_assist_not_applicable(
            add_missing_generics,
            r#"
            struct X<T>(T);
            impl<T> X<T> <|>{}
            "#,
        );
    }

    #[test]
    fn test_no_default_params() {
        check_assist_not_applicable(
            add_missing_generics,
            r#"
            struct X<T = ()>(T);
            impl X <|>{}
            "#,
        );
    }

    #[test]
    fn test_one_default_params() {
        check_assist(
            add_missing_generics,
            r#"
            struct X<T = (), U>;
            impl X <|>{}
            "#,
            r#"
            struct X<T = (), U>;
            impl<U> X<U> {}
            "#,
        );
    }

    #[test]
    fn test_with_enum() {
        check_assist(
            add_missing_generics,
            r#"
            enum Result<T, E> { Ok(T), Err(E) }
            impl Result {}<|>
            "#,
            r#"
            enum Result<T, E> { Ok(T), Err(E) }
            impl<T, E> Result<T, E> {}
            "#,
        );
    }

    #[test]
    fn test_with_trait() {
        check_assist(
            add_missing_generics,
            r#"
            trait Foo<T> {}

            impl Foo<T> f<|>or () {}
            "#,
            r#"
            trait Foo<T> {}

            impl<T> Foo<T> for () {}
            "#,
        );
    }

    #[test]
    fn both_trait_and_struct_generics() {
        check_assist(
            add_missing_generics,
            r#"
            trait Foo<T> {}
            struct X<U>(U);

            impl Foo<T> f<|>or X<U> {}
            "#,
            r#"
            trait Foo<T> {}
            struct X<U>(U);

            impl<T, U> Foo<T> for X<U> {}
            "#,
        );
    }

    #[test]
    fn test_without_struct_param() {
        check_assist(
            add_missing_generics,
            r#"
            struct X<T>(T);
            impl X <|>{}
            "#,
            r#"
            struct X<T>(T);
            impl<T> X<T> {}
            "#,
        );
    }

    #[test]
    fn all_combined() {
        check_assist(
            add_missing_generics,
            r#"
            struct X<T, U>;
            trait Foo<T, U>;
            impl Foo<A> for X<T> {<|>}
            "#,
            r#"
            struct X<T, U>;
            trait Foo<T, U>;
            impl<A, U, T, B> Foo<A, U> for X<T, B> {}
            "#,
        );
    }

    #[test]
    fn test_complicated() {
        check_assist(
            add_missing_generics,
            r#"
            struct X<T, U>;
            trait Foo<T, U> {}
            impl<T> Foo<U> for X {}<|>
            "#,
            r#"
            struct X<T, U>;
            trait Foo<T, U> {}
            impl<T, U, A, B> Foo<U, A> for X<T, B> {}
            "#,
        );
    }
}
