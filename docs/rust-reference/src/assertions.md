# Assertions

> **<sup>Syntax</sup>**\
> _Assertion_ :\
> &nbsp;&nbsp; &nbsp;&nbsp; _PointsToAssertion_\
> &nbsp;&nbsp; | _PredicateAssertion_\
> &nbsp;&nbsp; | _TypePredicateAssertion_\
> &nbsp;&nbsp; | _BooleanAssertion_\
> &nbsp;&nbsp; | _PatternMatchingEqualityAssertion_\
> &nbsp;&nbsp; | _ConditionalAssertion_\
> &nbsp;&nbsp; | _MatchAssertion_\
> &nbsp;&nbsp; | _Assertion_ `&*&` _Assertion_
>
> _PointsToAssertion_ : ( `[` _VFPattern_ `]` )<sup>?</sup> _Expression_ ( `|->` | `|-?->` ) _VFPattern_
>
> _VFPattern_ : `_` | `?` ( IDENTIFIER | `_` ) | Expression
>
> _PredicateAssertion_ : ( `[` _VFPattern_ `]` )<sup>?</sup> _Expression_ _VFPatternList_ <sup>?</sup> _VFPatternList_
>
> _VFPatternList_ : `(` (( _VFPattern_ `,` )<sup>\*</sup> _VFPattern_ )<sup>?</sup> `)`
>
> _TypePredicateAssertion_ : `<` _Type_ `>` `.` IDENTIFIER _VFPatternList_
>
> _BooleanAssertion_ : _Expression_
>
> _PatternMatchingEqualityAssertion_ : _Expression_ `==` _VFPattern_
>
> _ConditionalAssertion_ : `if` _Expression_ `{` _Assertion_ `}` `else` `{` _Assertion_ `}`
>
> _MatchAssertion_ : `match` _Scrutinee_ `{` ( _MatchAssertionArm_ `,`<sup>?</sup> )<sup>\*</sup> `}`
>
> _MatchAssertionArm_ : _Pattern_ `=>` _Assertion_
