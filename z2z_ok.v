Require Import Logic.
Notation transp P e x := (eq_rect _ P x _ e).
Lemma cst_case {A C:Type} {x y:A} (e:x=y) {h h':C} :
  h = h' ->
  transp (fun _ => C) e h = h'.
intros eh.
destruct e.
exact eh.
Defined.
Lemma cst_case_sym_trans A (x y z:A) B w w' (e:w=w':>B) (h:x=y) (h':x=z) :
  eq_trans (eq_sym (cst_case e h)) (cst_case e h') =
  eq_trans (eq_sym h) h'.
case e; simpl.
reflexivity.
Qed.

(* The goal of this file is to show how the recursive HIT

   Inductive Z2 := O | S (_:nat) // mod : O = (S (S O)).

   can be encoded by first defining the type of points, and
   then by introducing Z2 as the type of the points "quotiented"
   by a modified version of the mod constructor above.
   The new mod needs to be generalized to consider paths obtained
   by iteratively applying the map property of S to the old mod.
 *)

Inductive nat := O | S : nat -> nat.

Inductive Z2 := | c (_:nat)
 // mod n : (c n) = (c (S (S n))).

(*
  Z2_rect
     : forall (P : Z2 -> Type) (f : forall n : nat, P (c n)),
       (forall n : nat, transp P (mod n) (f n) = f (S (S n))) ->
       forall z : Z2, P z
*)

(* Fundametal property of Z2_rect : mapping the path constructor produces
   the coherence proof given to Z2_rect.
   Here specialized to non-dependent functions. *)
Lemma Z2_rect_equiv Q f g n :
  f_equal (fun x => Z2_rect (fun _ => Q) f (fun n => cst_case _ (g n)) x) (mod n) =
  g n.
transitivity (eq_trans (eq_sym (cst_case (mod n) eq_refl)) (cst_case _ (g n))).
 change (let a:=c (S (S n)) in let e:=mod n in
   f_equal
     (fun x => Z2_rect (fun _ => Q) f (fun n => cst_case (mod n) (g n)) x) e =
   @eq_trans _ _ _ (Z2_rect (fun _ => Q) f (fun n => cst_case _ (g n)) a)
     (eq_sym (cst_case e eq_refl))
     (Z2_rect2 (fun _ => Q) f (fun n => cst_case (mod n) (g n)) (c n) a e)).
 case (mod n).
 lazy beta delta iota zeta.
 simpl. (* ??? *)
 reflexivity.

 rewrite cst_case_sym_trans; simpl.
 case (g n).
 reflexivity.
Qed.


(* Constructors *)
Definition Z20 : Z2 := c O.

Definition Z2S (x:Z2) : Z2 :=
  match x with
  | c n => c (S n)
  | mod n => cst_case _ (mod (S n))
  end.

Definition Z2mod : Z20 = Z2S (Z2S Z20) := mod O.

Lemma map_Z2S n : f_equal Z2S (mod n) = mod (S n).
apply Z2_rect_equiv.
Qed.

(* Example: normalization function *)

(* first define it for points *)
Fixpoint norm_nat n :=
  match n with
  | O => O
  | S O => S O
  | S (S x) => norm_nat x
  end.

Lemma norm_nat_ok n :
  transp (fun _ => Z2) (mod n) (c (norm_nat n)) = c (norm_nat (S (S n))).
apply cst_case.
simpl.
reflexivity.
Qed.

Definition norm (x:Z2) :=
  match x with
  | c n => c (norm_nat n)
  | mod n => norm_nat_ok n
  end.

(* Deriving the elimination scheme *)

Section EliminationScheme.

Variable P : Z2 -> Type.

Variable f0 : P Z20.
Variable fS : forall x:Z2, P x -> P (Z2S x).
Variable fmod : transp (fun x => P x) Z2mod f0 = fS _ (fS _ f0).

Fixpoint Z2_nat (n:nat) : P (c n) :=
  match n with
  | O => f0
  | S m => fS _ (Z2_nat m)
  end.


Lemma Z2_nat_ok n :
  transp (fun x => P x) (mod n) (Z2_nat n) = Z2_nat (S (S n)).
simpl.
induction n; simpl.
 apply fmod.

 rewrite <- IHn.
 rewrite <- map_Z2S.
 change ((fun (a : Z2) (e : c n = a) =>
   transp (fun x => P x) (f_equal Z2S e) (fS (c n) (Z2_nat n)) =
  fS a (transp (fun x => P x) e (Z2_nat n))) _ (mod n)).
 case (mod n).
 simpl.
 reflexivity.
Qed.

Definition Z2_rect' (x:Z2) : P x :=
  match x with
  | c n => Z2_nat n
  | mod n => Z2_nat_ok n
  end.

End EliminationScheme.
