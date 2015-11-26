Require Import Paths.

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
   the coherence proof given to Z2_rect. *)
Lemma Z2_rect_equiv Q f g n : apD (fun x => Z2_rect Q f g x) (mod n) = g n.
change (g n) with (Z2_rect2 Q f g _ _ (mod n)).
case (mod n).
reflexivity.
Qed.
(* A non-dependent specialized version: *)
Lemma Z2_rect_equiv_nodep Q f g n :
  f_equal (fun x => Z2_rect (fun _ => Q) f (fun n => cst_case _ (g n)) x) (mod n) =
  g n.
rewrite apD_f_equal.
rewrite Z2_rect_equiv.
rewrite cst_case_sym_trans; simpl.
destruct (g n).
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
apply Z2_rect_equiv_nodep.
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

Lemma Z2_rect'_def0 :
  Z2_rect' Z20 = f0.
reflexivity.
Defined.

(* Not yet...
Lemma Z2_rect'_defS z :
  Z2_rect' (Z2S z) = fS _ (Z2_rect' z).
*)

(*
Parameter magic:forall P,P.

Parameter Z2_01 : forall P, P Z20 -> P (Z2S Z20) -> forall z, P z.


Lemma Z2_rect'_defS z :
  Z2_rect' (Z2S z) = fS _ (Z2_rect' z).
eapply Z2_rect with (z:=z) (P:=fun z => Z2_rect' (Z2S z) = fS _ (Z2_rect' z))
  (f:= fun n => eq_refl).
clear z.
simpl.
intros.
rewrite transport_eqD; simpl.
rewrite eq_trans_idl.

unfold Z2_rect' at 1.

assert (tmp := Z2_rect_equiv).
unfold Z2_rect in tmp.
rewrite (tmp _ (fun n => Z2_nat n) (fun n => Z2_nat_ok n)).

eapply Z2_01 with (z:=z).
reflexivity.
reflexivity.

eapply Z2_rect with (z:=z) (P:=fun z => Z2_rect' (Z2S z) = fS _ (Z2_rect' z))
  (f:= fun n => eq_refl).
simpl.
intros.

rewrite transport_eqD; simpl.
rewrite eq_trans_idl.

simpl.
Set Printing Implicit.

Check fun (a : Z2) (e : c n = a) =>
 eq_trans (eq_sym (apD (fun x : Z2 => Z2_rect' (Z2S x)) e))
   (apD (fun x : Z2 => fS x (Z2_rect' x)) e).
Check fun (a : nat) (e : c n = c a) =>
 eq_trans (eq_sym (apD (fun x : Z2 => Z2_rect' (Z2S x)) e))
   (apD (fun x : Z2 => fS x (Z2_rect' x)) e).


 = eq_refl.
case (mod n).
Set Printing Implicit.

case (mod n).
specialize transport_eq with (f:=fun z => Z2_rect' (Z2S z))
  (g:=fun z => fS _ (Z2_rect' z)) (e:=mod n) (h:=eq_refl (fS _ (Z2_nat n))).

eapply eq_trans.
Set Printing Implicit.
specialize transport_eq with (f:=fun z => Z2_rect' (Z2S z))
  (g:=fun z => fS _ (Z2_rect' z)) (e:=mod n) (h:=eq_refl (fS _ (Z2_nat n))).
reflexivity.
apply magic.
Grab Existential Variables.
reflexivity.

refine (Z2_rect ( _ (magic _) z).

unfold Z2_rect'; simpl.
unfold Z2S.
eapply Z2_rect with (P:=fun z =>
  Z2_rect _ (fun n => Z2_nat n) (fun n => Z2_nat_ok n)
     (Z2_rect _ (fun n => c (S n)) (fun n => cst_case (mod n) (mod (S n))) z) =
   fS z
     (Z2_rect _ (fun n => Z2_nat n) (fun n => Z2_nat_ok n) z)).
 with (f:=
     end).
 (z:=z).
 with (z:=z).
reflexivity.
*)

End EliminationScheme.

Section AltScheme.

(* Showing that Z2 is actually isomorphic to bool... *)

Variable P : Z2 -> Type.

Variable f0 : P Z20.
Variable f1 : P (Z2S Z20).

Lemma modZ2 (z:Z2) : z = Z2S (Z2S z).
apply Z2_rect with (f:=mod) (z:=z).
intros n.
rewrite transport_eq.
rewrite f_equal_id.
rewrite eq_trans_assoc.
rewrite eq_trans_inv.
rewrite eq_trans_idl.
do 2 rewrite <- map_Z2S.
rewrite <- f_equal_comp with (f:=Z2S)(g:=Z2S)(e:=mod n).
reflexivity.
Defined.
(*
eapply Z2_rect' with (P:=fun z => z = Z2S (Z2S z)) (f0 := mod O)
 (fS := fun z h => f_equal Z2S h).
simpl.
unfold Z20.
unfold Z2mod.
rewrite transport_eq.
rewrite <- f_equal_comp with (f:=Z2S)(g:=Z2S)(e:=mod O).
rewrite f_equal_id.
rewrite eq_trans_assoc.
rewrite eq_trans_inv.
rewrite eq_trans_idl.
reflexivity.
Defined.
*)
Lemma Z2_rect_bin_aux (z:Z2) : P z * P (Z2S z).
eapply Z2_rect' with (P:=fun z => (P z * P (Z2S z))%type) (f0 := (f0,f1))
  (fS := fun z (h:P z * P (Z2S z)) => (snd h, transp P (modZ2 z) (fst h))).
simpl.
unfold Z2mod.
rewrite <- map_Z2S.
change (let z0 := c(S (S O)) in let e := mod O in
   @eq_rect Z2 Z20 (fun x : Z2 => (P x * P (Z2S x))%type) (f0, f1) z0 e =
   (@eq_rect Z2 Z20 P f0 z0 e,
    @eq_rect Z2 (c (S O)) P f1 _ (@f_equal Z2 Z2 Z2S (c O) z0 e))).
destruct (mod O); simpl.
reflexivity.
Defined.

Definition Z2_rect_01 : forall z, P z :=
  fun z => fst (Z2_rect_bin_aux z).

End AltScheme.

(* Now we can prove that Z2_rect' on Z2S behaves as expected,
   but propositionally. *)
Lemma Z2_rect'_defS P f g h z :
  Z2_rect' P f g h (Z2S z) = g _ (Z2_rect' P f g h z).
eapply Z2_rect_01 with (z:=z).
 reflexivity.
 reflexivity.
Qed.


(*
Definition Z2_eq z z' :=
  match z with
  | c n => match z' with
           | c m => norm_nat n = norm_nat m
           | mod m => cst_case _ eq_refl
           end
  | mod n => cst_case _ eq_refl
  end.
*)
(*Definition Z2_eq_norm_nat {n n'} (e:c n = c n') : c n = c n'.
revert n n' e.
fix Hrec 1.
destruct n.
 clear Hrec.
 fix Hrec 1.
 destruct n'.
  reflexivity.
 destruct n'.
  trivial.
 intros.
 apply eq_trans with (2:=mod n').
 apply Hrec.
 apply eq_trans with (2:=eq_sym (mod n')); trivial.

 destruct n'.
  trivial.
 intro.
 apply f_equal with (f:=Z2S) (x:=c n) (y:=c n').
 apply Hrec.
 apply eq_trans with (1:=mod n).
 apply eq_trans with (2:=eq_sym(mod n')).
 apply f_equal with (f:=Z2S) in e; trivial.
Defined.

Definition Z2_eq_norm_nat' {n z'} (e:c n = z') : c n = z'.
pattern z'.
 eapply Z2_rect'.
Show Existentials.

  with (f:=fun n' => @Z2_eq_norm_nat n n' e).


revert e.
pattern z'; eapply Z2_rect
  with (f:=fun n' e => @Z2_eq_norm_nat n n' e).
clear z'.
intros n'.
rewrite transport_eqD.
assert (magic:forall P,P).
 admit.
apply magic.


Definition Z2_eq_norm {z z':Z2} (e:z=z') : z=z'.
revert z' e.
pattern z; eapply Z2_rect.
assert 

' with (x:=z) (f0:=
*)
Definition Z2_eq_norm {z z':Z2} (e:z=z') : z=z'.
revert e.
apply Z2_rect_01 with (z:=z);
  apply Z2_rect_01 with (z:=z'); try reflexivity.
trivial.
trivial.
Defined.
(*Lemma L : @Z2_eq_norm = @Z2_eq_norm.
unfold Z2_eq_norm at 2.
unfold Z2_rect_01 at 1.
unfold Z2_rect_bin_aux.
simpl.
Notation subst e x := (eq_ind _ _ x _ e).
unfold Z2_rect'.
*)

Lemma Z2_eta {z z'} (e:z=z') : Z2_eq_norm e = e.
destruct e; simpl.
apply Z2_rect_01 with (z:=z); reflexivity.
Defined.
Lemma Z2_eq_norm_cst {z:Z2} (e:z=z) : Z2_eq_norm e = eq_refl.
revert e.
apply Z2_rect_01 with (z:=z); reflexivity.
Defined.
Lemma Z2_is_hset {z z':Z2} (e1 e2:z=z') : e1 = e2.
revert e1.
destruct e2.
intros.
rewrite <- (Z2_eta e1).
apply Z2_eq_norm_cst.
Defined.
