Require Export Logic.

Scheme eq_indd := Induction for eq Sort Prop.

Infix "^" := eq_trans.
Notation transp P e x := (eq_rect _ P x _ e). (*(only parsing)*)

Lemma eq_sym_sym {A} {a b:A} (e:a=b) :
  eq_sym (eq_sym e) = e.
destruct e; reflexivity.
Defined.

Lemma eq_trans_idl {A} {a b:A} (e:a=b) :
  eq_refl ^ e = e.
destruct e; reflexivity.
Defined.

Lemma eq_trans_assoc {A} {a0 a1 a2 a3:A} (e1:a0=a1) (e2:_=a2) (e3:_=a3):
  e1 ^ e2 ^ e3 = (e1 ^ e2) ^ e3.
destruct e3; simpl.
reflexivity.
Defined.

Lemma eq_trans_inv {A} {a b:A} (e:a=b): eq_sym e ^ e = eq_refl.
destruct e; reflexivity.
Defined.

Lemma eq_trans_syml {A:Type} {x y z:A} (e:x=y) (e':x=z) (e'':y=z) :
  eq_sym e ^ e' = e'' -> e' = e ^ e''.
revert e''; destruct e.
simpl; intros.
rewrite eq_trans_idl in H |-*.
trivial.
Defined.

Lemma eq_trans_syml' {A:Type} {x y z:A} (e:x=y) (e':y=z) (e'':x=z) :
  e ^ e' = e'' -> e' = eq_sym e ^ e''.
revert e'; destruct e.
simpl; intros.
rewrite eq_trans_idl in H |-*.
trivial.
Defined.

(* f_equal *)

Lemma f_equal_id A (a a':A) (e:a=a') :
  f_equal (fun x=>x) e = e.
destruct e; reflexivity.
Defined.

Lemma f_equal_comp A B C (f:B->C) (g:A->B) a a' (e:a=a') :
  f_equal f (f_equal g e) = f_equal (fun x => f (g x)) e.
destruct e; reflexivity.
Defined.

Lemma f_equal_cst {A B:Type}{x:B}{y y':A} (p:y=y'):
  f_equal (fun _ => x) p = eq_refl x.
destruct p.
reflexivity.
Defined.

Lemma transport_trans {A} {a b c:A} (e':a=b) (e:b=c) {P:A->Type} (h:P a) :
  transp P e (transp P e' h) = transp P (e' ^ e) h.
destruct e.
reflexivity.
Defined.

Lemma transport_comp {A B} {f:A->B} {P:B->Prop} {a b:A} (e:a=b) (h:P (f a)) :
  transp (fun x => P (f x)) e h = transp P (f_equal f e) h.
destruct e.
reflexivity.
Defined.

Lemma transport_cst {A C:Type} {x y:A} (e:x=y) {h:C} :
  transp (fun _ => C) e h = h.
destruct e; reflexivity.
Defined.

Lemma transport_eq A B (f:A->B) (g:A->B) a a' (h:f a=g a) (e:a=a') :
  transp (fun x => f x = g x) e h =
  eq_sym (f_equal f e) ^ h ^ f_equal g e.
destruct e.
simpl.
destruct h; reflexivity.
Defined.

Lemma transp_f_equal A B (y:B) (g:A->B) a a' (h:y=g a) (e:a=a') :
  transp (fun x => y = g x) e h =
  h ^ f_equal g e.
destruct e.
reflexivity.
Defined.

Definition apD {X Y} (f:forall x:X,Y x) {x x'} (e:x=x') :
  transp Y e (f x) = f x'.
destruct e; reflexivity.
Defined.

Lemma transport_eqD A B (f g:forall a:A,B a) a a' (h:f a=g a) (e:a=a') :
  transp (fun x => f x = g x) e h =
  eq_sym (apD f e) ^ f_equal (fun b => transp _ e b) h ^ apD g e.
destruct e; simpl.
rewrite eq_trans_idl.
rewrite f_equal_id.
reflexivity.
Defined.

Lemma cst_case {A C:Type} {x y:A} (e:x=y) {h h':C} :
  h = h' ->
  transp (fun _ => C) e h = h'.
intros eh.
destruct e.
exact eh.
Defined.

Lemma cst_case_sym_trans A (x y z:A) B w w' (e:w=w':>B) (h:x=y) (h':x=z) :
  eq_sym (cst_case e h) ^ cst_case e h' =
  eq_sym h ^ h'.
case e; simpl.
reflexivity.
Qed.

Lemma apD_f_equal {X Y} (f:X->Y) {x x': X} (e:x=x') :
  f_equal f e = eq_sym (cst_case e eq_refl) ^ apD f e.
destruct e; reflexivity.
Qed.
