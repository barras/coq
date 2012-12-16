
(* Coq options: -noinit *)

Set Implicit Arguments.
Require Import Notations LogicClasses.
Notation "A -> B" := (forall _:A, B).

Global Instance type_logic_kind : logic_kind Type := fun X=>X.

Inductive TrueT := IT.
Inductive FalseT :=.
Scheme FalseTE := Minimality for FalseT Sort Type.
Hint Resolve IT : core. (* to create core hint base (otherwise bugs) *)


(* Pb: TrueT is in Prop! The zealous unification would decide
   that X is Prop and cannot find a logic_kind for Prop! *)
Global Instance type_true : trivial_prop (L:=type_logic_kind) TrueT IT.
Global Instance type_false : absurd_prop (L:=type_logic_kind) FalseT FalseTE.

Inductive prod (A B:Type) := pair (_:A) (_:B).
Definition fst {A B} (p:prod A B) : A :=
  let (a,_) := p in a.
Definition snd {A B} (p:prod A B) : B :=
  let (_,b) := p in b.

Global Instance type_and : conjunction prod (@pair) (@fst) (@snd).

Inductive sum (A B:Type) := inl (_:A) | inr (_:B).

Scheme sum_elim := Minimality for sum Sort Type.

Global Instance type_or : disjunction sum (@inl) (@inr) (@sum_elim).

Record iffT (A B:Type) := mkIffT {
  iffTE1 : A -> B;
  iffTE2 : B -> A
}.

Global Instance type_iff : equivalence iffT (@mkIffT) (@iffTE1) (@iffTE2).

Definition notT (A:Type) := A -> FalseT.

Global Instance type_prop_logic :
  propositional_logic type_and type_or notT type_iff type_true type_false Set.

Inductive sigT (A:Type) (P:A->Type) : Type :=
  existT (x:A) (_:P x).

Scheme type_ex := Minimality for sigT Sort Type.

Global Instance type_fol : first_order_logic sigT existT type_ex.
Global Instance type_logic :
  full_logic type_prop_logic type_fol.

(* Better force identity in Type rather than letting it land in Prop *)
Definition U:=Type.
Inductive identity (A:Type) (x:A) : A -> Type :=
| id_refl : identity x x.

Definition my_id_refl := id_refl.

Scheme idE := Minimality for identity Sort Type.

Definition id_sym {A} {x y:A} : identity x y -> identity y x.
destruct 1; constructor.
Qed.

Definition id_trans {A} {x y z:A} : identity x y -> identity y z -> identity x z.
destruct 1; trivial.
Qed.

Definition id_congr {A B} (f:A->B) {x y} : identity x y -> identity (f x) (f y).
destruct 1; reflexivity. (* uses constructor *)
Qed.

Inductive nat := O|S(_:nat).

Global Instance type_eq_logic :
  equational_logic (L:=type_logic_kind) identity idE my_id_refl (@id_sym) (@id_trans) (@id_congr).


(* At this level, many problems will fail because if identity is in Prop, then
   unification makes the bad assumption that X is Prop *)

Global Instance type_full_eq_logic : full_eq_logic type_prop_logic type_fol type_eq_logic | 1.

Lemma test_refl : identity O O.
reflexivity.
Show Proof. (* uses declared refl *)
Qed.

Lemma discr_nat X : identity O (S(S O)) -> X.
intros.
discriminate. (* Hopefully now even with identity in Prop, it works! *)
Qed.

Lemma inj_nat n : identity (S (S n)) (S n) -> identity n (S n).
intros.
injection H.
intro.
rewrite H0. (* internal_identity_rewr_r : rewrite recognized identity *)
reflexivity. (* reflexivity found refl by inspecting def *)
Show Proof.
Qed.

Inductive id2 (A:Type) : A->A->Type :=
 | id2_r : forall x, id2 x x.

Definition my_id2_r := id2_r.

Lemma id2E (A:Type) (x:A) (P:A->Type) (f:P x) (y:A) (e:id2 x y) : P y.
revert f; case e; trivial.
Qed.

Definition id2_sym {A} {x y:A} : id2 x y -> id2 y x.
destruct 1; constructor.
Qed.

Definition id2_trans {A} {x y z:A} : id2 x y -> id2 y z -> id2 x z.
destruct 1; trivial.
Qed.

Definition id2_congr {A B} (f:A->B) {x y} : id2 x y -> id2 (f x) (f y).
destruct 1; try reflexivity.
Qed.

Global Instance type_eq2_logic :
  equational_logic (L:=type_logic_kind) id2 id2E my_id2_r (@id2_sym) (@id2_trans) (@id2_congr).

Global Instance type_full_eq2_logic : full_eq_logic type_prop_logic type_fol type_eq2_logic | 0.


Lemma discr_nat_again X : identity O (S(S O)) -> X.
intros.
discriminate. (* Hopefully now even with identity in Prop, it works! *)
Show Proof.
Qed. (* reasoning on identity still works *)

Lemma discr2_nat X : id2 O (S(S O)) -> X.
intros.
discriminate.
Show Proof.
Qed.

Lemma inj2_nat n : id2 (S (S n)) (S n) -> identity n (S n).
intros.
injection H.
intro.
elim H0 using id2E. (* rewrite would not work here *)
Show Proof.
admit.
Qed.

Inductive le : nat -> nat -> Prop :=
| lenn : forall n, le n n
| leSn : forall m n, le m n -> le m (S n).

Lemma inv : forall m n, le (S (S m)) (S n) -> TrueT.
intros.
simple inversion H.
admit.
admit.
Qed.



