% Encoding Structural Equality in CaPriCon
% Marc Coiffier

> 'utils require import

> Type 'A -> A 'x -> 
> 
> 'Eq_context { A 'a -> Type ? '.Eq -> .Eq ( x ) '.refl -> } def
> 
> 'Eq A 'y -> Eq_context .Eq ( y ) ? ? "x = y" defconstr !
> 'refl Eq_context .refl ! ! "refl x" defconstr

The type of {{A 'y -> Eq ( y ) 'e recursor dup ! tex}} is {{type tex}}.

> 2 lambdas [ 'Eq 'refl ] { export } each
