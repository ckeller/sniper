Require Import utilities.
From elpi Require Import elpi.

Ltac mypose t := let Na := fresh "f" in pose t as Na; fold Na. (*TODO fold in all hyps except
the self refering one *)

Elpi Tactic anonymous_funs.

Elpi Accumulate File "elpi/higher_order.elpi".
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate lp:{{

  pred mypose_list i: list term, i: goal, o: list sealed-goal.
  mypose_list [X|XS] G GL :- coq.ltac.call "mypose" [trm X] G [G'],
    coq.ltac.open (mypose_list XS) G' GL.
  mypose_list [] _ _.

  solve (goal Ctx _ TyG _ _ as G) GL :- ctx_to_trms Ctx Trms, 
    get_anonymous_funs_list [TyG|Trms] Lfun, mypose_list Lfun G GL.

}}.
Elpi Typecheck.

Require Import List.

Lemma bar : forall (A B C : Type) (l : list A) (f : A -> B) (g : B -> C), 
map g (map f l) = map (fun x => g (f x)) l.
intros.
pose (h := (fun x => x + 1) 42 = 43). 
elpi anonymous_funs. Abort.

Elpi Tactic prenex_higher_order.
Elpi Accumulate File "elpi/higher_order.elpi".
Elpi Accumulate File "elpi/utilities.elpi".
Elpi Accumulate lp:{{

  solve (goal Ctx _ TyG _ [trm T] as G) GL :- coq.say T, is_ho1 T.

}}.
Elpi Typecheck.

Goal False.
elpi prenex_higher_order (forall (A : Type), nat -> nat).




