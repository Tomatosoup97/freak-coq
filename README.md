Freak-coq
=========


Experimental functional programming language with algebraic effects.
Type safety theorem is formalized in Coq.

Based on ["An Introduction to Algebraic Effects and Handlers"](https://www.sciencedirect.com/science/article/pii/S1571066115000705)


* File structure

- Language.v - definition of language data types and parser
- Maps.v - lemmas and definition of partial maps
- Opt.v - optimalization for state-monad imitating handlers (correctness not formalized yet)
- Semantics.v - small-step operational semantics of the language
- Sets.v - lemmas and definition of sets
- Subst.v - substitution function
- SubstLemmas.v - substitution preserves types theorem
- Tests.v - exemplary programs with expected outputs
- Types.v - definition of typing and weakening lemma
- TypeSafety.v - progress and preservation theorems



