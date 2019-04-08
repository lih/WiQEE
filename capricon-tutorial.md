% First steps with CaPriCon
% Marc Coiffier

This page is intended as a tutorial on the use of a stack-based proof
environment like the one provided on this site. Since we're going to
need to print things out, and we don't yet have the knowledge to write
such features ourselves, let's first import a few useful functions
from a preexisting module.

> 'utils require import

Among other things, this module defines one function that will be of
interest to us : `vis`. When called, this function simply prints out
every hypothesis in context and every value currently on the
stack. It's very useful as the final word in a sentence, to show the
resulting context. It doesn't change anything, so feel free to
sprinkle it at any point of your scripts for debugging purposes.

Now, in order to understand what a stack-based language is, we first
have to understand the basic concept of a *stack*.

The stack
---------

