# The Calculus of Continuations

My take on Thielecke's CPS calculus, and variants hereof.

I'm currently running against time to finish everything, and I'm pretty tired,
but I'll get back in here to improve this documentation.

# Summary of files

A summary of the proof files, in order, and what they cover.

- [Prelude.v](theories/Prelude.v): random stuff needed throughout the
  formalization, such as tactics and some proofs about lists.
- [Syntax.v](theories/Syntax.v): the syntax of the CPS calculus, along with
  declarations necessary for handling de Bruijn indexes and free variables.
- [Metatheory.v](theories/Metatheory.v): most metatheory about de Bruijn
  variable handling.
- [AbstractRewriting.v](theories/AbstractRewriting.v): general definitions and
  proofs about abstract rewriting systems needed by other proofs.
- [Context.v](theories/Context.v): definition of static and full contexts in the
  CPS calculus, along with congruences.
- [Axiomatic.v](theories/Axiomatic.v): definition of the axiomatic semantics and
  the axiomatic congruence relation as originally studied, including admissible
  rules.
- [Reduction.v](theories/Reduction.v): definition of the reduction semantics,
  including one-step and multi-step reduction, and convertibility congruence,
  showing they're sound with respect to the axiomatic semantics.
- [Residuals.v](theories/Residuals.v): development of a theory of residuals and
  "terms with a mark", necessary for confluence, including the cube lemma.
- [Confluency.v](theories/Confluency.v): definition of a notion of parallel
  reduction, including proofs of confluence and of the Church-Rosser property.
- [Factorization.v](theories/Factorization.v): full reduction may be factorized,
  showing that we're always allowed to perform leftmost jumps first.
- [Observational.v](theories/Observational.v): observational theory of the
  calculus, including observational congruence and barbed congruence.
- [Machine.v](theories/Machine.v): big-step machine semantics, as given for
  compiler IRs, and it's equivalence to head reduction.
- [Transition.v](theories/Transition.v): labelled transition semantics, and
  development on their soundness with regards to the other semantics.
- [TypeSystem.v](theories/TypeSystem.v): definition of a simply-typed type
  system for the CPS calculus, and admissibility of the structural rules for it.
- [Conservation.v](theories/Conservation.v): proof of conservation (uniform
  normalization) for jump reduction, and some of its corollaries.
- [Normalization.v](theories/Normalization.v): proof of strong normalization for
  the reduction relation and related stuff.
- [Structural.v](theories/Structural.v): confluence and strong normalization are
  preserved by strong bisimilarity, which includes continuation floating, which
  acts as an structural rule.

# TODO

Some desirable results that are still pending are standardization of full
reduction as well as simultion of CPS translations and their full abstraction in
the simply typed context. Some preliminary work is present with regard to those,
which I still have to properly document.
