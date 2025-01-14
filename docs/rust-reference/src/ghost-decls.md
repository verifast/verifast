# Ghost declarations

A ghost declarations annotation may appear anywhere a Rust item may appear, except that only a few kinds of ghost declarations are supported inside function bodies (see [Block annotations](func-body-annots.md#block-annotations)).

> **<sup>Syntax</sup>**\
> _GhostDeclarationsAnnotation_ : `/*@` _GhostDeclaration_ <sup>\*</sup> `@*/`
>
> _GhostDeclaration_ :\
> &nbsp;&nbsp; &nbsp;&nbsp; `pub` _GhostDeclaration_\
> &nbsp;&nbsp; | `inductive` IDENTIFIER _GenericParams_ <sup>?</sup> `=` `|`<sup>?</sup> _InductiveConstructor_ ( `|` _InductiveConstructor_ )<sup>\*</sup> `;`\
> &nbsp;&nbsp; | `fix` IDENTIFIER _GenericParams_ <sup>?</sup> `(` _Params_ `)` ( `->` _Type_ )<sup>?</sup> ( `{` _Expression_ `}` | `;` )\
> &nbsp;&nbsp; | `pred` IDENTIFIER _GenericParams_ <sup>?</sup> `(` ( _Params_ `;` )<sup>?</sup> _Params_ `)` ( `=` _Assertion_ )<sup>?</sup> `;`\
> &nbsp;&nbsp; | `pred_ctor` IDENTIFIER _GenericParams_ <sup>?</sup> `(` _Params_ `)` `(` ( _Params_ `;` )<sup>?</sup> _Params_ `)` `=` _Assertion_ `;`\
> &nbsp;&nbsp; | `pred` _GenericParams_ <sup>?</sup> `<` _Type_ `>` `.` IDENTIFIER `(` ( _ParamNames_ `;` )<sup>?</sup> _ParamNames_ `)` `=` _Assertion_ `;`\
> &nbsp;&nbsp; | `lem` IDENTIFIER _GenericParams_ <sup>?</sup> `(` _Params_ `)` ( `->` _Type_ )<sup>?</sup> _LemmaRest_\
> &nbsp;&nbsp; | `fn_type` IDENTIFIER _GenericParams_ <sup>?</sup> `(` _Params_ `)` `=` `unsafe` `fn` `(` _Params_ `)` ( `->` _Type_ )<sup>?</sup> `;` `req` _Assertion_ `;` `ens` _Assertion_ `;`\
> &nbsp;&nbsp; | `lem_type` IDENTIFIER _GenericParams_ <sup>?</sup> `(` _Params_ `)` `=` `lem` `(` _Params_ `)` ( `->` _Type_ )<sup>?</sup> `;` `req` _Assertion_ `;` `ens` _Assertion_ `;`\
> &nbsp;&nbsp; | `let_lft` _Lifetime_ `=` _Expression_ `;`\
> &nbsp;&nbsp; | `abstract_type` IDENTIFIER `;`
>
> _InductiveConstructor_ : IDENTIFIER ( `(` ( _ParamType_ `,` )<sup>*</sup> _ParamType_ `)` )<sup>?</sup>
> 
> _LemmaRest_ :\
> &nbsp;&nbsp; &nbsp;&nbsp; _LemmaSpecification_ `{` _GhostCommand_ <sup>\*</sup> `}`\
> &nbsp;&nbsp; | `;` _LemmaSpecification_
>
> _LemmaSpecification_ : `nonghost_callers_only`<sup>?</sup> `req` _Assertion_ `;` `ens` _Assertion_ `;`
>
> _Params_ : (( _Param_ `,` )<sup>\*</sup> _Param_ )<sup>?</sup>
>
> _Param_ : IDENTIFIER `:` _Type_
>
> _ParamNames_ : (( IDENTIFIER `,` )<sup>\*</sup> IDENTIFIER )<sup>?</sup>