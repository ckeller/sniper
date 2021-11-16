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


Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import BinInt.
Require Import Coq.Arith.PeanoNat.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.All.
Require Import List.
Require Import utilities.
Import ListNotations.


(* Instantiate a hypothesis with the parameter x *)
Ltac instantiate_par H x :=
  let T := type of H in
 lazymatch T  with
  | forall (y : ?A), _ => tryif (let H':= fresh H "_" x in assert (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x)) then idtac else (let H':= fresh H in assert (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x))
  | _ => fail
      end.


(* Instantiate a hypothesis with the parameter x and return its identifier *)
Ltac instantiate_par_ident H x :=
  let T := type of H in
 lazymatch T  with
  | forall (y : ?A), _ => let H':= fresh H in 
let _ := match goal with _ => assert (H':= H) ; 
let U := type of (H' x) in notHyp U ; specialize (H' x) end in H'
  | _ => fail
      end.


Goal (forall (A : Type) (B : Type), A = A /\ B = B) ->  forall (x : nat) (y : bool), x=x /\ y= y.
intro H.
let H' := instantiate_par_ident H bool in instantiate_par H' bool.
Abort.


Ltac instantiate_tuple_terms H t := match t with
| (?x, ?t') => try (let H' := instantiate_par_ident H x in let u := type of H' in
instantiate_tuple_terms H' t) ; try (instantiate_tuple_terms H t')
| unit =>  let T := type of H in
           match T with
            | forall (y : ?A), _ => constr_eq A Type ; clear H
            | _ => idtac
            end
end.

Ltac instantiate_tuple_terms_goal H := let t0 := return_tuple_subterms_of_type_type in 
let t := eval cbv in t0 in instantiate_tuple_terms H t.

Goal (forall (A B C : Type), B = B -> C = C -> A = A) -> nat = nat -> bool = bool.
intros H.
let p := return_tuple_subterms_of_type_type in pose p.
instantiate_tuple_terms_goal H.
Abort.


Ltac instantiate_tuple_terms_tuple_hyp t terms := match t with 
| (?H, ?t') => instantiate_tuple_terms H terms ; instantiate_tuple_terms_tuple_hyp t' terms
| unit => idtac
end.


Ltac instantiate_tuple_terms_tuple_hyp_no_unit t terms := lazymatch t with 
| (?t1, ?t2 ) => instantiate_tuple_terms_tuple_hyp_no_unit t1 terms ; 
instantiate_tuple_terms_tuple_hyp_no_unit t2 terms
| ?H => let T := type of H in 
     match T with 
  | forall (y : ?A), _ => constr_eq A Type ; try (instantiate_tuple_terms H terms)
  | _ => try (let U := type of T in constr_eq U Prop ; notHyp H ; let H0 := fresh H in assert (H0 : T) by exact H)
  end
end.

Ltac elimination_polymorphism t0 := 
let t := eval cbv in t0 in 
let terms0 := return_tuple_subterms_of_type_type in 
let terms := eval cbv in terms0 in 
let h0 := hyps in 
let h := eval cbv in h0 in
instantiate_tuple_terms_tuple_hyp_no_unit t terms ; 
instantiate_tuple_terms_tuple_hyp h terms.

Ltac test t0 := 
let t := eval cbv in t0 in 
let h0 := hyps in 
let h := eval cbv in h0 in
let x := constr:((nat, (bool, unit))) in 
instantiate_tuple_terms_tuple_hyp_no_unit t x ; 
instantiate_tuple_terms_tuple_hyp h x.

Ltac test2 t0 :=
let h0 := hyps in
let t := eval cbv in t0 in 
let x := constr:((nat, (bool, unit))) in
instantiate_tuple_terms_tuple_hyp_no_unit t0 x.


Goal (forall (A B C : Type), B = B -> C = C -> A = A) -> nat = nat -> bool = bool.
intro.
elimination_polymorphism (rev_involutive, unit).

Abort.


Tactic Notation "inst" := elimination_polymorphism unit.
Tactic Notation "inst" constr(t) := elimination_polymorphism (t, unit).


Goal (forall (A : Type) (a : A), a = a) -> (forall (x : nat), x = x).
Proof. intros H. inst app_length.

Abort.

Section test.

Variable A : Type. 
 Theorem nil_cons : forall (x:A) (l:list A), [] <> x :: l.
  Proof.
    intros. unfold "<>". intro H. inversion H.
  Qed.

Goal False -> forall (x : nat) (y : bool), x=x /\ y= y.
inst (pair_equal_spec, app_length, nil_cons, app_comm_cons).
Abort.


Goal True -> forall (x:A) (l:list A), [] <> x :: l.
intros.
test2 nil_cons. apply nil_cons0. Qed.

End test.
