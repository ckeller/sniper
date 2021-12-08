(**************************************************************************)
(*                                                                        *)
(*     Sniper                                                             *)
(*     Copyright (C) 2021                                                 *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)



Require Export SMTCoq.SMTCoq.

From MetaCoq Require Export All.
Require Export MetaCoq.Template.All.
Require Export MetaCoq.Template.Universes.
Require Export MetaCoq.PCUIC.PCUICSubstitution.
Require Export MetaCoq.Template.All.
Require Export String.
Require Export List.
Require Export ZArith.
Require Export utilities.
Require Export definitions.
Require Export elimination_fixpoints.
Require Export expand.
Require Export elimination_pattern_matching. 
Require Export elimination_polymorphism.
Require Export eliminators.
Require Export interpretation_algebraic_types.



Ltac def_and_pattern_matching := 
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_dependent_pattern_matching H')).


Ltac def_fix_and_pattern_matching :=
get_definitions_theories ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_fix_ho H' ltac:(fun H'' =>
try (eliminate_dependent_pattern_matching H'')))).


Ltac def_and_pattern_matching_mono :=
def_and_pattern_matching ; inst.

Ltac def_and_pattern_matching_mono_param t :=
def_and_pattern_matching ; inst t.
Ltac def_fix_and_pattern_matching_mono_param t :=
def_fix_and_pattern_matching ; inst t.



Ltac scope_param_nat t :=
try interp_alg_types_context_goal; try (def_fix_and_pattern_matching_mono_param t ; try nat_convert) ;
get_eliminators_in_goal.

Ltac scope_no_param_nat :=
try interp_alg_types_context_goal; try (def_fix_and_pattern_matching ; inst ; try nat_convert) ;
get_eliminators_in_goal.

Ltac scope_param_no_nat t :=
try interp_alg_types_context_goal; try (def_fix_and_pattern_matching_mono_param t) ;
get_eliminators_in_goal.

Ltac scope_no_param_no_nat :=
try interp_alg_types_context_goal; try (def_fix_and_pattern_matching ; inst) ;
get_eliminators_in_goal.

Ltac scope_param_no_nat_var t :=
intros ; try interp_alg_types_context_goal; try (def_fix_and_pattern_matching_mono_param t) ;
get_eliminators_in_variables.

Ltac scope_no_param_no_nat_var :=
intros ; try interp_alg_types_context_goal; try (def_fix_and_pattern_matching ; inst) ;
get_eliminators_in_variables.

Ltac snipe_param_nat t := 
scope_param_nat t ; verit.

Ltac snipe_no_param_nat := 
scope_no_param_nat ; verit.

Ltac snipe_param_no_nat t :=
scope_param_no_nat t ; verit.

Ltac snipe_no_param_no_nat :=
scope_no_param_no_nat ; verit.

Ltac snipe_param_no_nat_var t :=
scope_param_no_nat_var t ; verit.

Ltac snipe_no_param_no_nat_var :=
scope_no_param_no_nat_var ; verit.

Tactic Notation "snipe" constr(t) := snipe_param_no_nat t.
Tactic Notation "snipe" := snipe_no_param_no_nat.

Tactic Notation "scope" constr(t) := scope_param_no_nat t.
Tactic Notation "scope" := scope_no_param_no_nat.

Tactic Notation "snipe2" constr(t) := snipe_param_no_nat_var t.
Tactic Notation "snipe2" := snipe_no_param_no_nat_var.

Tactic Notation "scope2" constr(t) := scope_param_no_nat_var t.
Tactic Notation "scope2" := scope_no_param_no_nat_var.

Tactic Notation "scope_nat" constr(t) := scope_param_nat t.
Tactic Notation "scope_nat" := scope_no_param_nat.

Tactic Notation "snipe_nat" constr(t) := snipe_param_nat t.
Tactic Notation "snipe_nat" := snipe_no_param_nat.
