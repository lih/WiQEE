% Reflections on Prismatic Constructions
% Marc Coiffier

The Calculus of Prismatic Constructions, upon which this platform is
based, is an extension of the standard
[CoC](https://en.wikipedia.org/wiki/Calculus_of_constructions) with a
mechanism for discriminating inductive constructors.

The Problem
-----------

Inductive types can be described as enumerations of constructors. In
Coq (and similarly in other proof assistants), an inductive type must
be declared along with its constructors, using a syntax like :

~~~~~~~{.coq}
Inductive T : forall A..., Type :=
| t0 : forall x0..., T (f0... x0...) 
...
| tn : forall xn..., T (fn... xn...)
.
~~~~~~~~~

Here, we declare the inductive type $T : \forall A..., Type$, and its
constructors called $t_{i}$ ($i \in \{0..n\}$).

As a more concrete example, here is how the type of Booleans can be
defined inductively :

~~~~~~~{.coq}
Inductive Boolean : Type := true : Boolean | false : Boolean.
~~~~~~~~
