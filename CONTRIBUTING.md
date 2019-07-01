Contributing to Idris 2
=======================

Contributions are welcome! The most important things needed at this stage,
beyond work on the language core, are (in no particular order):

* CI integration.
* Documentation string support (at the REPL and IDE mode).
* A better REPL, including:
  - `it` and `:let`
  - readline and tab completion
  - `:search` and `:apropos`
  - help commands
* Some parts of the Idris 1 Prelude are not yet implemented and should be
  added to base/
* Partial evaluation, especially for specialisation of interface 
  implementations.
* The lexer and parser are quite slow, new and faster versions with better
  errors would be good.
* An alternative, high performance, back end. OCaml seems worth a try.
* JS and Node back ends would be nice.

Some language extensions from Idris 1 have not yet been implemented. Most
notably:

* Type providers
  - Perhaps consider safety - do we allow arbitrary IO operations, or is
    there a way to restrict them so that they can't, for example, delete
    files or run executables.
* Elaborator reflection
  - This will necessarily be slightly different from Idris 1 since the
    elaborator works differently. It would also be nice to extend it with
    libraries and perhaps syntax for deriving implementations of interfaces.

Other contributions are also welcome, but I (@edwinb) will need to be
confident that I'll be able to maintain them!

If you're editing the core system, or adding any features, please keep an
eye on performance. In particular, check that the libraries build and tests
run in approximately the same amount of time before and after the change.
(Although running faster is fine as long as everything still works :))

Libraries
---------

Further library support would be very welcome, but unless it's adding something
that was in `prelude/` or `base/` in Idris 1, please add it initially into
`contrib/`. (We'll reorganise things at some point, but it will need some
thought and discussion).

Think about whether definitions should be `export` or `public export`. As
a general rule so far, type synonyms and anything where the evaluation
behaviour might be useful in a proof (so very small definitions) are
`public export` and everything else which is exported is `export`.

Syntax
------

Some syntax that hasn't yet been implemented but will be:

* Range syntax (e.g. [1..10], [1,3..10], [1..] etc) [needs some thought about
  what should go in the Prelude and exactly how to implement]
* Idiom brackets
* !-notation [needs some thought about the exact rules]

Some things from Idris 1 definitely won't be implemented:

* Uniqueness types (instead, Idris 2 is based on QTT and supports linearity)
* Some esoteric syntax experiments, such as match applications
* Syntax extensions (at least in the unrestricted form from Idris 1)
* DSL blocks (probably) unless someone has a compelling use case that can't
  be done another way