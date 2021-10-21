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

Inductive DOORS : interface :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.


(* One has to establish some properties on user-defined types,
   containing in particular the fact that it has a decidable equality,
   an order relation and an inhabitant.

  We plan to have these properties proved automatically.
 *)

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

(* Manipulating DOORS is tricky though, due to the dependency over a
   type. *)


Section CompDec_DOORS.
  Context `{HT : CompDec T}.

(*
  Let eqb : DOORS T -> DOORS T -> bool :=
    fun a b =>
      match a, b with
        | IsOpen d1, IsOpen d2 => SMT_classes.eqb d1 d2
        | Toggle d1, Toggle d2 => SMT_classes.eqb d1 d2
        | _, _ => false
      end.

  (* Let lt : DOORS T -> DOORS T -> Prop. *)
  (* Proof. *)
  (*   intro x. destruct x as [d1|d1]. *)
  (*   intro y. inversion y. *)

  Let lt : DOORS T -> DOORS T -> Prop :=
    fun a =>
      match a in DOORS i return DOORS i -> Prop with
        | IsOpen d1 =>
          fun b =>
            match b in DOORS bool return Prop with
            | IsOpen d2 => lt d1 d2
            | Toggle d2 => False_rect unit
            end
        | Toggle d1 => fun _ => True
      end.

  Let lt : DOORS T -> DOORS T -> Prop :=
    fun a b =>
      match a, b with
        | IsOpen d1, IsOpen d2 => lt d1 d2
        | IsOpen _, Toggle _ => True
        | Toggle _, IsOpen _ => False
        | Toggle d1, Toggle d2 => lt d1 d2
      end.

  Global Instance DOORS_ord : OrdType (DOORS T).
  Proof.
    exists lt.
    - intros x y z.
      destruct x as [d1|d1].
      inversion y.

 ; destruct y as [d2|d2]; destruct z as [d3|d3].
    - now intros [ | ] [ | ].
  Defined.

  Global Instance DOORS T_eqbtype : EqbType DOORS T.
  Proof.
    exists eqb.
    now intros [ | ] [ | ].
  Defined.

  Global Instance DOORS T_comp : @Comparable DOORS T DOORS T_ord.
  Proof.
    split.
    intros [ | ] [ | ]; try now apply OrderedType.EQ.
    - now apply OrderedType.LT.
    - now apply OrderedType.GT.
  Defined.

  Global Instance DOORS T_inh : Inhabited DOORS T := {| default_value := left |}.

  Global Instance DOORS T_compdec : CompDec DOORS T := {|
    Eqb := DOORS T_eqbtype;
    Ordered := DOORS T_ord;
    Comp := DOORS T_comp;
    Inh := DOORS T_inh
  |}.
*)

  Global Instance DOORS_compdec : CompDec (DOORS T).
  Admitted.

  Definition DOORS_typ_compdec := Typ_compdec (DOORS T) DOORS_compdec.
End CompDec_DOORS.


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
Proof. snipe. Qed.

Variable o_caller : doors_o_caller2 bool ω (IsOpen d).
Variable x : bool.
Variable eq_cond : x = true.
Variable o_caller0 : doors_o_callee2 bool ω (IsOpen d) x. 

Goal doors_o_caller2 unit ω (Toggle d).
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








