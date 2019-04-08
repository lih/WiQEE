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
have to understand the basic concept of a *stack*, and the role it
plays during the execution of a script.

Stacks, and The Stack
---------------------

A stack, in general, is a list of values, to which we arbitrarily
assign two extremes, a *top* and a *bottom*. We can operate on either
side, but as a general simplifying convention, all stack operations
will take place at the top unless specified otherwise.

The most fundamental operations that can be carried out on a stack are
*pushing* and *popping* values to and from it (at the top).

What does that have to do with CaPriCon ? Well, stack-based languages,
as their name implies, implicitly operate on a stack, that serves as
temporary storage for all the intermediate results of a
computation. When we talk about *the stack*, without any more context,
you can assume we're talking about this one.

In most stack-based languages, including CaPriCon, words designate
*instructions* that modify the stack according to predefined rules,
and complex scripts can be written by stringing words together in the
right order.

### First words

Let's start talking. The simplest kinds of words are *symbols*, more
commonly known as strings, and written as a single quote (`'`),
followed by some non-space characters.

> 'greetings
>? vis



