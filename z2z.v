
Lemma cst_case {A C:Type} {x y:A} (e:x=y) {h h':C} :
  h = h' ->
  eq_rect x (fun _ => C) h y e = h'.
intros eh.
destruct e.
exact eh.
Defined.

(* This file shows the problem with (point) recursive HITs, when
   trying to derive the (dependent) recursive eliminator (or in
   fact any recursive function) from pattern-matching and guarded
   fixpoint. 
 *)

Inductive Z2 := | O | S (_:Z2) // mod : O = (S (S O)).

(* Let's try to define the function norm s.t.
   norm O = O, norm (S O) = (S O), norm (S (S n)) = norm n
 *)

(* We can first write the "body" of norm, i.e. a function computing norm x
   assuming we have a function f that computes norm for values structurally
   smaller than x.
   We need to assume that f behaves as norm should at O and (S O). *)
Definition norm_body (f:Z2->Z2) (f0 : O = f O) (f1 : S O = f (S O)) (x:Z2) : Z2 :=
  match x with
  | O => O
  | S x' => match x' with
            | O => (S O)
            | S x'' => f x''
            | mod => cst_case mod f1 
            end
  | mod => cst_case mod f0
  end.

Record res (x:Z2) := mkR { resz : Z2 ; res0 : x=O -> O=resz;  res1 : x=S O -> S O=resz }.

Require Import Program.
(*
Parameter magic: forall P, P.
Program Definition norm_body' (norm:forall x, res x) (x:Z2) : res x :=
  mkR x (norm_body (fun x => resz _ (norm x)) (magic _)
    (magic _) x) _ _.*)

Program Definition norm_body' (norm:forall x, res x) (x:Z2) : res x :=
  mkR x (norm_body (fun x => resz _ (norm x))
          (res0 _ (norm O) eq_refl) (res1 _ (norm (S O)) eq_refl) x) (* Garde! *)
    _ _.

Fail Fixpoint norm (x:Z2) : res x :=
  norm_body' norm x. (* Garde!!! *)
