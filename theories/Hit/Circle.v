Require Import Paths.

Inductive Circle : Type :=
    | base : Circle
   // loop : base = base.

Lemma Circle_rect_equiv (P : Type) fbase floop :
  f_equal (Circle_rect (fun _ => P) fbase (cst_case _ floop)) loop = floop.
Proof.
  transitivity (eq_sym (cst_case loop eq_refl) ^ cst_case _ floop).
  - exact (
    match loop as e in (_ = y) return (
      f_equal (Circle_rect (fun _ => P) fbase (cst_case _ floop)) e =
      @eq_trans _ _ _ (Circle_rect (fun _ => P) fbase (cst_case _ floop) y)
        (eq_sym (cst_case _ eq_refl))
        (Circle_rect2 (fun _ => P) fbase (cst_case _ floop) base y e))
    with
    | eq_refl => eq_refl
    end).
  - rewrite cst_case_sym_trans. simpl. apply eq_trans_idl.
Qed.
