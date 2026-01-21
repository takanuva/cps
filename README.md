# The Calculus of Continuations

My take on Thielecke's CPS-calculus, and variants hereof.

I'm currently running against time to finish everything, and I'm pretty tired,
but I'll get back in here to improve this documentation.

![Coq 8.16](https://github.com/takanuva/cps/actions/workflows/coq-8.16.yml/badge.svg)
![Coq 8.17](https://github.com/takanuva/cps/actions/workflows/coq-8.17.yml/badge.svg)
![Coq 8.18](https://github.com/takanuva/cps/actions/workflows/coq-8.18.yml/badge.svg)
![Coq 8.19.2](https://github.com/takanuva/cps/actions/workflows/coq-8.19.2.yml/badge.svg)
![Coq 8.20.1](https://github.com/takanuva/cps/actions/workflows/coq-8.20.1.yml/badge.svg)
![Coq 9.0](https://github.com/takanuva/cps/actions/workflows/coq-9.0.yml/badge.svg)

# Summary of files

A summary of the proof files, in order, and what they cover. I should surely
come back here and improve this documentation at some point. This is but a
sketch for the curious ones.

The following files are somewhat self-contained and unrelated to the main goal:

- [Prelude.v](theories/Prelude.v): random stuff needed throughout the
  formalization, such as tactics and some proofs about lists.
- [AbstractRewriting.v](theories/AbstractRewriting.v): general definitions and
  proofs about abstract rewriting systems (including bisimulation) needed by
  other proofs.
- [Substitution.v](theories/Substitution.v): an implementation of the
  sigma-calculus, as of now just an experiment to automate reasoning about
  substitutions in a de Bruijn setting.
- [Lambda/Calculus.v](theories/Lambda/Calculus.v): some basic definitions about the lambda-calculus.

Content about the CPS-calculus itself:

- [Syntax.v](theories/Syntax.v): the syntax of the CPS calculus, along with
  declarations necessary for handling de Bruijn indexes and free variables.
- [Metatheory.v](theories/Metatheory.v): most metatheory about de Bruijn
  variable handling.
- [Context.v](theories/Context.v): definition of static and full contexts in the
  CPS calculus, along with the notion of a congruence.
- [Equational.v](theories/Equational.v): definition of the equational theory
  (also called the axiomatic semantics) as originally studied, including
  admissible rules.
- [Reduction.v](theories/Reduction.v): definition of the reduction semantics,
  including one-step and multi-step reduction, and convertibility congruence,
  showing they're sound with respect to the equational theory.
- [Shrinking.v](theories/Shrinking.v): introduces the notion of a shrinking
  reduction along with tidying requirements for preserving confluence,
  factorization and normalization.
- [Residuals.v](theories/Residuals.v): development of a theory of residuals and
  "terms with a mark", necessary for confluence, including the cube lemma.
- [Confluence.v](theories/Confluence.v): definition of a notion of parallel
  reduction, including proofs of confluence and of the Church-Rosser property.
- [Factorization.v](theories/Factorization.v): full reduction may be factorized,
  showing that we're always allowed to perform leftmost jumps first.
- [Conservation.v](theories/Conservation.v): proof of conservation (uniform
  normalization) for jump reduction, and some of its corollaries.
- [Structural.v](theories/Structural.v): proof of preservation of strong
  normalization for some notions of structural rules on jump development.
- [Observational.v](theories/Observational.v): observational theory of the
  calculus, including observational congruence and barbed congruence.
- [Machine.v](theories/Machine.v): big-step machine semantics, as given for
  compiler IRs, and it's equivalence to head reduction.
- [Transition.v](theories/Transition.v): labelled transition semantics, and
  development on their soundness with regards to the other semantics.
- [TypeSystem.v](theories/TypeSystem.v): definition of a simply typed type
  system for the CPS calculus, and admissibility of the structural rules for it.
- [Normalization.v](theories/Normalization.v): proof of strong normalization for
  jumps and the full reduction relation, along with it logical consistency.
- [Lambda/PlotkinCBN.v](theories/Lambda/PlotkinCBN.v): definitions for the
  call-by-name lambda-calculus, as defined by Plotkin, along with its CPS
  translation and proofs of simulation, adequacy and denotational soundness.
- [Lambda/PlotkinCBV.v](theories/Lambda/PlotkinCBV.v): same as above, but for
  the call-by-value lambda-calculus.

# TODO

There's some work on other stuff, such as proving contification is sound and
that Appel's interpreter is correct. I also gotta review the transition system,
and actually make use of the sigma-calculus. We eventually want to prove
standardization as well, following factorization. Also, there are some sketches
about ANF and correctness of control operators in the translations. We should
prove some other CPS translations (such as the one Kennedy uses). I want to
mechanize Merro's results on the observational theory as well. May the gods help
me.
