(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Local.Constructions.Calculus.
Require Local.Constructions.Conversion.
Require Local.Constructions.Confluence.
Require Local.Constructions.TypeSystem.
Require Local.Constructions.Normalization.
Require Local.Constructions.Inversion.
Require Local.Constructions.Stratification.
Require Local.Constructions.Reduction.

Module TT :=
  Calculus <+
  Conversion <+
  Confluence <+
  TypeSystem <+
  Normalization <+
  Inversion <+
  Stratification <+
  Reduction.
