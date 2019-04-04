% Binary relations
% Marc Coiffier

> 'utils require import

Given two types {{Type 'A -> A}} and {{Type 'B -> B}}, a binary
relation between {{A}} and {{B}} can be described as a function that,
when given two witnesses {{A 'a -> a}} and {{B 'b -> b}} produces a
{{Type}} which is inhabited iff {{a}} and {{b}} are related.

> 'Relation Type ? ? def ! !

> Type 'A -> Relation ( A A ) 'r ->
>   'reflexive A 'a -> r ( a a ) ? def
>   'symmetric A 'x -> A 'y -> r ( x y ) 'rxy -> r ( y x ) ? ? ? def
>   'transitive A 'x -> A 'y -> A 'z -> r ( x y ) 'rxy -> r ( y z ) 'ryz -> r ( x z ) ? ? ? ? ? def
> ! !
