use crate::{
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
pub(crate) fn add_missing_generics_inner(
    acc: &mut Assists,
    ctx: &AssistContext,
    assist_id: &'static str,
    label: &'static str,
) -> Option<()> {
    let impl_def = ctx.find_node_at_offset::<ast::Impl>()?;

    let impl_generics = impl_def.generic_param_list();

    let target_trait = resolve_target_trait(&ctx.sema, &impl_def);
    let self_ty_adt = resolve_self_ty(&ctx.sema, &impl_def);

    let self_type_params = self_ty_adt
        .into_iter()
        .flat_map(|target_trait| hir::GenericDef::Adt(target_trait).params(ctx.db()).into_iter());

    let trait_params = target_trait
        .into_iter()
        .flat_map(|target_trait| hir::GenericDef::Trait(target_trait).params(ctx.db()).into_iter())
        .skip(1); // trait always have a 'Self' parameter

    let mut type_params = trait_params
        .chain(self_type_params)
        .filter(|param| is_default_type_param(param, ctx.db()))
        .peekable();

    if type_params.peek().is_none() {
        return None;
    }

    // the params which are already specified in the impl
    let impl_type_params: Vec<ast::TypeParam> = impl_generics
        .iter()
        .flat_map(|list| list.generic_params())
        .filter_map(|param| match param {
            ast::GenericParam::TypeParam(param) => Some(param),
            _ => None,
        })
        .collect();

    let mut missing_type_params = type_params
        .into_iter()
        .filter(|type_param| {
            use hir::AsName;
            let already_in_impl_params = impl_type_params.iter().any(|impl_param| {
                impl_param.name().map_or(false, |name| name.as_name() == type_param.name(ctx.db()))
            });

            !already_in_impl_params
        })
        .map(|param| {
            let name = param.name(ctx.db()).to_string();
            make::generic_param(name, None)
        })
        .peekable();

    if missing_type_params.peek().is_none() {
        return None;
    }

    let impl_generics_new = match &impl_generics {
        Some(generics) => generics.append_params(missing_type_params),
        None => make::generic_param_list(missing_type_params),
    };

    let impl_token = impl_def.impl_token()?;
    let target = impl_def.syntax().text_range();
    acc.add(AssistId(assist_id, AssistKind::QuickFix), label, target, |builder| match impl_generics
    {
        Some(impl_generics) => {
            builder.replace_ast(impl_generics, impl_generics_new);
        }
        None => {
            builder.insert(impl_token.text_range().end(), impl_generics_new.to_string());
        }
    })
}

fn is_default_type_param(type_param: &hir::TypeParam, db: &dyn HirDatabase) -> bool {
    let default_param = type_param.default(db);
    let has_default = default_param.map_or(false, |param| !param.is_unknown());
    !has_default
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
            impl<T> X <|>{}
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
    fn test_with_enum() {
        check_assist(
            add_missing_generics,
            r#"
            enum Result<T, E> { Ok(T), Err(E) }
            impl Result {}<|>
            "#,
            r#"
            enum Result<T, E> { Ok(T), Err(E) }
            impl<T, E> Result {}
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
}
