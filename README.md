# Freak-coq


Experimental functional programming language with algebraic effects.
Type safety theorem is formalized in Coq.

Based on ["An Introduction to Algebraic Effects and Handlers"](https://www.sciencedirect.com/science/article/pii/S1571066115000705)


## File structure

- *Language.v* - definition of language data types and parser
- *Maps.v* - lemmas and definition of partial maps
- *Opt.v* - optimalization for state-monad imitating handlers (correctness not formalized yet)
- *Semantics.v* - small-step operational semantics of the language
- *Sets.v* - lemmas and definition of sets
- *Subst.v* - substitution function
- *SubstLemmas.v* - substitution preserves types theorem
- *Tests.v* - exemplary programs with expected outputs
- *Types.v* - definition of typing and weakening lemma
- *TypeSafety.v* - progress and preservation theorems

## Known issues

- *Types.v*
    1. `weakening` - by some reason I can't close the proof, even though it has all goals finished
- *SubstLemmas.v*
    1. `substitution lemma` - missing variables in Gamma blocks from further steps
- *TypeSafety.v*
    1. `progress lemma` - in do-op case there appears another var with set of
       available effects, which semantically does not make sense. I presume
       `remember` is required or other coq-trick to make it work.
    2. `preservation` - similarly as above

