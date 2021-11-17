This directory contains background material, i.e. various pieces of code
that contain a variety of ideas that could be integrated into a future
version.

**Tagless.hs** illustrates
1. modularity of language features
2. some meta-structure (Liftable, Apply)
3. how many 'interpreters' are then straight lifts from the host language
4. that the meta-structure is itself highly structured (and could be generated)
5. some items are different (see the Printer instance, and compiler one too)
6. how partial evaluation wants different signatures (see Lambda2 and below)
  (buried in there are a couple of ideas that are not as clear as in other
   codes)

**incope.ml** illustrates
1. how laws for structures (monoid, ring, etc) can be used to create
   parts of a simplifying partial evaluator.  See "module P" for details.
2. CPS -- see RCN interpreter. This relies on the signature to be of the
   'Lambda2' kind (see above code) rather than the simpler 1-parameter version.
3. CPS transformer. See CPST. This is a **language to language** transformer.
4. Addition of imperative features (SymSI and EXSI_INT and EXSI_INT_INT)

**Exper.hs** illustrates
1. the use of type families to be able to gain some separate between the
  host types and the embedded types

**Family.hs** illustrates
1. the use of associated types instead (mostly for PE)

**PHvsCH.hs** illustrates
1. how various encodings of binders end up being equivalent (this arose
  from questions that Phil Wadler asked us)

**StackMachine.hs and stack-symantics.hs** illustrate
1. how we can do very 'different' kinds of meta-languages, here Forth or
   postscript-like. The typing discipline is quite different in both, so
   both teach different things.

**Thincope2.hs** illustrates that:
1. if you have a compiler, you can write a compile-time functor to generate
   an interpreter

**incopety.ml** illustrates that:
1. (the opposite of the above!) that given an interpreter, a compiler can
  be generated functorially
2. given an interpreter and a functorial compiler, we can write a functorial
  partial evaluator (that furthermore has all the simplifications too)
