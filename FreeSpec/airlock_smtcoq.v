Add Rec LoadPath "/home/louise/github.com/louiseddp/sniper" as Sniper.
Require Import Sniper.
From Coq Require Import Arith.
Add Rec LoadPath "/home/louise/github.com/lthms/FreeSpec/master/_build/default/theories/Core" as FreeSpec.Core.
From FreeSpec.Core Require Import Core CoreFacts.


Section airlock1.

Definition interface := Type -> Type.
Variable ix : interface.
Variable A B : Type.
Variable MayProvide
     : interface -> interface -> Type.
Variable Provide : forall ix i : interface, MayProvide ix i -> Type.
Definition Ω := (bool * bool)%type.
Inductive door : Set :=  left : door | right : door.

(* We establish some properties on user-defined types, containing in
   particular the fact that it has a decidable order. We plan to have
   these properties proved automatically. *)

Section CompDec_door.
  Let eqb : door -> door -> bool :=
    fun a b =>
      match a, b with
      | left, left | right, right => true
      | _, _ => false
      end.

  Let lt : door -> door -> Prop :=
    fun a b =>
      match a, b with
      | left, right => True
      | _, _ => False
      end.

  Global Instance door_ord : OrdType door.
  Proof.
    exists lt.
    - now intros [ | ] [ | ] [ | ].
    - now intros [ | ] [ | ].
  Defined.

  Global Instance door_eqbtype : EqbType door.
  Proof.
    exists eqb.
    now intros [ | ] [ | ].
  Defined.

  Global Instance door_comp : @Comparable door door_ord.
  Proof.
    split.
    intros [ | ] [ | ]; try now apply OrderedType.EQ.
    - now apply OrderedType.LT.
    - now apply OrderedType.GT.
  Defined.

  Global Instance door_inh : Inhabited door := {| default_value := left |}.

  Global Instance door_compdec : CompDec door := {|
    Eqb := door_eqbtype;
    Ordered := door_ord;
    Comp := door_comp;
    Inh := door_inh
  |}.

  Definition door_typ_compdec := Typ_compdec door door_compdec.
End CompDec_door.

Inductive DOORS : interface :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Definition sel : door -> Ω -> bool := fun d : door => match d with
                      | left => fst
                      | right => snd
                      end
.
Definition co := fun d : door => match d with
                     | left => right
                     | right => left
                     end.
Inductive doors_o_caller : Ω -> forall a : Type, DOORS a -> Prop :=
    req_is_open : forall (d : door) (ω : Ω), doors_o_caller ω bool (IsOpen d)
  | req_toggle : forall (d : door) (ω : Ω),
                 (sel d ω = false -> sel (co d) ω = false) -> doors_o_caller ω unit (Toggle d).

Inductive doors_o_callee : Ω -> forall a : Type, DOORS a -> a -> Prop :=
    doors_o_callee_is_open : forall (d : door) (ω : Ω) (x : bool),
                             sel d ω = x -> doors_o_callee ω bool (IsOpen d) x
  | doors_o_callee_toggle : forall (d : door) (ω : Ω) (x : unit), doors_o_callee ω unit (Toggle d) x.


(* Inductive type => Boolean function
   + the arguments of type Type must be first *)

Definition doors_o_callee2 :  forall (a : Type), Ω -> forall (D :  DOORS a), (match D with 
| IsOpen _ =>  bool 
| Toggle _ => unit
end) -> bool :=
fun a ω D => match D with
| IsOpen d => fun x => Bool.eqb (sel d ω) x
| Toggle d => fun x => true
end.

Definition doors_o_caller2 : forall (a : Type), Ω -> forall (D : DOORS a), bool := 
fun a ω D => match D with
| IsOpen _ => true
| Toggle d => implb (negb (sel d ω)) (negb (sel (co d) ω))
end.


Variable H : MayProvide ix DOORS.
Variable H0 : Provide ix DOORS H.
Variable ω : Ω.
Variable d : door.



Goal doors_o_caller2 bool ω (IsOpen d).
Proof. scope. verit. Qed. (*TODO Chantal *)
 apply H6. Qed. 

Variable o_caller : doors_o_caller2 ω bool (IsOpen d).
Variable x : bool.
Variable eq_cond : x = true.
Variable o_caller0 : doors_o_callee2 ω bool (IsOpen d) x. 

Goal doors_o_caller2 ω unit (Toggle d).
Proof. scope. Fail verit. (* TODO Chantal *) 
rewrite H12 in o_caller0. 
unfold is_true in o_caller0. 
rewrite Bool.eqb_true_iff in o_caller0.
subst. rewrite H5. 
rewrite o_caller0. 
simpl. constructor. 
Qed.

Definition tog (d : door) (ω : Ω) : Ω :=
  match d with
  | left => (negb (fst ω), snd ω)
  | right => (fst ω, negb (snd ω))
  end.

End airlock1.

Section airlock2.

Definition is_open `{Provide ix DOORS} (d : door) : impure ix bool :=
  request (IsOpen d).

Definition toggle `{Provide ix DOORS} (d : door) : impure ix unit :=
  request (Toggle d).

Definition open_door `{Provide ix DOORS} (d : door) : impure ix unit :=
  let* open := is_open d in
  when (negb open) (toggle d).

Definition close_door `{Provide ix DOORS} (d : door) : impure ix unit :=
  let* open := is_open d in
  when open (toggle d).

Definition step (ω : Ω) (a : Type) (e : DOORS a) (x : a) :=
  match e with
  | Toggle d => tog d ω
  | _ => ω
  end.

Definition doors_contract : contract DOORS Ω :=
  make_contract step doors_o_caller doors_o_callee.

Variable ix : interface.
Variable H : MayProvide ix DOORS.
Variable H0 : Provide ix DOORS. 
Variable ω : Ω.
Variable d : door.
Variable safe : sel (co d) ω = false.

Print MayProvide.

Goal doors_o_caller2 ω bool (IsOpen d).
Proof.
scope. Fail verit. (* TODO Chantal. *) 
apply H9.
Qed.

Variable o_caller : doors_o_caller2 ω bool (IsOpen d).
Variable x : bool.
Variable o_caller0 : doors_o_callee2 ω bool (IsOpen d) x.
Variable equ_cond : x = false.



Goal doors_o_caller2 ω unit (Toggle d).
Proof. scope. Fail verit. (* TODO Chantal *) 
unfold is_true in o_caller0.
rewrite H15 in o_caller0.
rewrite Bool.eqb_true_iff in o_caller0.
subst.
rewrite H8. 
rewrite equ_cond. 
rewrite safe. 
auto.
Qed.

End airlock2.

Section airlock3.

Inductive CONTROLLER : interface :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Definition tick `{Provide ix CONTROLLER} : impure ix unit :=
  request Tick.

Definition request_open `{Provide ix CONTROLLER} (d : door) : impure ix unit :=
  request (RequestOpen d).


#[local] Opaque close_door.
#[local] Opaque open_door.
#[local] Opaque Nat.ltb.
#[local] Opaque sel.

Open Scope nat_scope.


Definition controller `{Provide ix DOORS, Provide ix (STORE nat)}
  : component CONTROLLER ix :=
  fun _ op =>
    match op with
    | Tick =>
      let* cpt := get in
      when (15 <? cpt) begin
        close_door left;;
        close_door right;;
        put 0
      end
    | RequestOpen d =>
        close_door (co d);;
        open_door d;;
        put 0
    end.

Lemma respectful_run_inv `{Provide ix DOORS} {a} (p : impure ix a)
    (ω : Ω) (safe : sel left ω = false \/ sel right ω = false)
    (x : a) (ω' : Ω) (hpre : pre (to_hoare doors_contract p) ω)
    (hpost : post (to_hoare doors_contract p) ω x ω')
  : sel left ω' = false \/ sel right ω' = false.


Admitted. (* Not something to do automatically *) 

Lemma controller_correct `{StrictProvide2 ix DOORS (STORE nat)}
  : correct_component controller
                      (no_contract CONTROLLER)
                      doors_contract
                      (fun _ ω => sel left ω = false \/ sel right ω = false).

Proof.
  intros ωc ωd pred a e req.
  assert (hpre : pre (to_hoare doors_contract (controller a e)) ωd).
    (destruct e; prove impure).
  - scope. (* TODO : Inductive predicates *) admit. 
  - admit.
  - admit. 
  - admit.
  - split; auto.
  intros x ωj' run.
  cbn.
  split.
  + auto with freespec.
  + apply respectful_run_inv in run; auto.
Admitted.  

End airlock3. 








