(** The menagerie *)

(* Several notations and utility functions *)

Notation "'transp' P e x" := (eq_rect _ P x _ e)
  (at level 10, P at next level, e at next level, x at next level, no associativity).
Scheme eq_indd := Induction for eq Sort Prop.
Lemma eq_rect_cst (A:Type) (x y:A) (e:x=y) (P:Type) (p:P) :
  transp (fun _ => P) e p = p.
case e; reflexivity.
Qed.
Definition apD {X:Type}{Y:X->Type}(f:forall x:X,Y x){x x':X}(e:x=x')
   : transp Y e (f x) = f x' :=
  match e in _=z return eq_rect x Y (f x) z e=f z with
  | eq_refl => eq_refl (f x)
  end.


(* Now the HITs *)


Inductive Circle : Type :=
    | base : Circle
with paths :=
    | loop : base = base.

Check Circle_rect.
(*
Circle_rect
     : forall (P : Circle -> Type) (f : P base),
       transp P loop f = f -> forall c : Circle, P c
*)
Print Circle_rect.
(*
fun (P : Circle -> Type) (f : P base) (g : transp P loop f = f) (c : Circle) =>
fixmatch {h} c as c0 return (P c0) with
| base => f
| loop => g
end
*)
(* fixmatch and match are the same thing: *)
Check fun (P : Circle -> Type) (f : P base) (g : transp P loop f = f) (c : Circle) =>
  match c return (P c) with
  | base => f
  | loop => g
  end.

Print Circle_rect2.
(*
Circle_rect2 = 
fun (P : Circle -> Type) (f : P base) (g : transp P loop f = f)
  (c c0 : Circle) (e : c = c0) =>
fixmatch {h} e as c1 return (P c1) with
| base => f
| loop => g
end
     : forall (P : Circle -> Type) (f : P base) (g : transp P loop f = f)
         (c c0 : Circle) (e : c = c0),
       transp (fun c1 : Circle => P c1) e
       fixmatch {h} c return (P c) with
       | base => f
       | loop => g
       end =
       fixmatch {h} c0 return (P c0) with
       | base => f
       | loop => g
       end
*)
Check (Circle_rect2 : forall
 (P:Circle->Type) (pt:P base) (lp:transp P loop pt = pt) c c' (w:c=c'),
 transp P w (Circle_rect P pt lp c) = Circle_rect P pt lp c').

Section CircleComputation.

Variable P : Circle -> Type.
Variable pt : P base.
Variable lp : transp _ loop pt = pt.

Eval compute in Circle_rect P pt lp base. (* = pt *)

Lemma compute_base : Circle_rect P pt lp base = pt.
Proof (refl_equal pt). (* definitional equality *)

Lemma compute_loop :
      apD (Circle_rect P pt lp) loop = lp.
(* uses: (Circle_rect2 ... loop) reduces to lp *)
change (apD (Circle_rect P pt lp) loop = Circle_rect2 P pt lp _ _ loop).
case loop.
(* uses: (Circle_rect2 ... eq_refl) reduces to eq_refl (and the usual reduction of J) *)
compute.
lazy beta delta iota.
reflexivity.
Qed.
Print compute_loop. (* propositional equality *)

Eval compute in transp P loop pt.
(* A match over a constructor, and it does not compute!
       match loop in (_ = y) return (P y) with
       | eq_refl => pt
       end
 => canonicity lost!
*)

End CircleComputation.


Inductive Circle' : Type :=
  | east : Circle'
  | west : Circle'
with paths :=
  | upper : west = east
  | lower : east = west.

Check Circle'_rect.
(*
Circle'_rect
     : forall (P : Circle' -> Type) (f : P east) (f0 : P west),
       transp P upper f0 = f ->
       transp P lower f = f0 -> forall c : Circle', P c
*)

Require Import Program.

Lemma C2C_ob1 : transp (fun _ : Circle' => Circle) upper base = base.
rewrite eq_rect_cst.
apply eq_refl.
Defined.
Lemma C2C_ob2 : transp (fun _ : Circle' => Circle) lower base = base.
rewrite eq_rect_cst.
apply loop.
Defined.

Definition Circle'2Circle (c:Circle') : Circle :=
  Circle'_rect (fun _ => Circle) base base C2C_ob1 C2C_ob2 c.

Program Definition Circle2Circle' (c:Circle) : Circle' :=
  Circle_rect (fun _ => Circle') east _ c.
Next Obligation.
rewrite eq_rect_cst.
transitivity west.
 apply lower.
 apply upper.
Defined.

Eval compute in Circle2Circle' base.

Inductive Interval : Type :=
    | left : Interval
    | right : Interval
with paths :=
    | segment : left = right.

Check Interval_rect.
(*
Interval_rect
     : forall (P : Interval -> Type) (f : P left) (f0 : P right),
       transp P segment f = f0 -> forall i : Interval, P i
*)
Print Interval_rect.
(*
Interval_rect = 
fun (P : Interval -> Type) (f : P left) (f0 : P right) 
  (g : transp P segment f = f0) (i : Interval) =>
match i as i0 return (P i0) with
| left => f
| right => f0
| segment => g
end
*)

Lemma Interval_contractible (x:Interval): x=right.
eapply Interval_rect with (i:=x).
Show Existentials.
instantiate (1:=eq_refl).
instantiate (1:=segment).
exact (eq_indd _ left (fun z (e:left=z) =>
  match e in _=y return y=z with eq_refl => e end = @eq_refl _ z) eq_refl right segment).
Defined.



(* Not accepted: 2-constructor *)
(*
Inductive Sphere2 : Type :=
    | base2 : Sphere2
with paths :=
    | surf2 : (@refl_equal _ base2) = (@refl_equal _ base2).
*)


Inductive Susp (X : Type) : Type :=
    | north : Susp X
    | south : Susp X
with paths :=
    | merid (x:X) : north = south.

Check Susp_rect.
(*
Susp_rect
     : forall (X : Type) (P : Susp X -> Type) (f : P (north X))
         (f0 : P (south X)),
       (forall x : X, transp P (merid X x) f = f0) -> forall s : Susp X, P s
*)
Check (Susp_rect2 :
  forall X P (f:P(north X)) (f0:P(south X)) (g:forall x:X, transp P (merid X x) f = f0)
    (s s' : Susp X) (e:s=s'),
  transp P e (Susp_rect X P f f0 g s) = Susp_rect X P f f0 g s').


Inductive Cyl {X Y : Type} (g : X -> Y) : Y -> Type :=
    | cyl_base : forall y:Y, Cyl g y
    | cyl_top : forall x:X, Cyl g (g x)
with paths :=
    | cyl_seg (x:X) : (cyl_top x) = (cyl_base (g x)).

Check Cyl_rect.
(*
Cyl_rect
     : forall (X Y : Type) (g : X -> Y) (P : forall y : Y, Cyl g y -> Type)
         (f : forall y : Y, P y (cyl_base g y))
         (f0 : forall x : X, P (g x) (cyl_top g x)),
       (forall x : X, transp (P (g x)) (cyl_seg X Y g x) (f0 x) = f (g x)) ->
       forall (y : Y) (c : Cyl g y), P y c
*)
Check (Cyl_rect2 : forall (X Y : Type) (g : X -> Y) (P : forall y : Y, Cyl g y -> Type)
         (f : forall y : Y, P y (cyl_base g y))
         (f0 : forall x : X, P (g x) (cyl_top g x))
         (g0:forall x : X, transp (P (g x)) (cyl_seg X Y g x) (f0 x) = f (g x))
         (y : Y) (c c' : Cyl g y) (e:c=c'),
  transp (P y) e (Cyl_rect X Y g P f f0 g0 y c) = Cyl_rect X Y g P f f0 g0 y c').


Inductive prop_tr (X:Type) : Type :=
    | proj : X -> prop_tr X
with paths :=
    | contr (y y' : prop_tr X) : y=y'.
Check prop_tr_rect.
(*
prop_tr_rect
     : forall (X : Type) (P : prop_tr X -> Type),
       (forall x : X, P (proj X x)) ->
       (forall (y : prop_tr X) (h : P y) (y' : prop_tr X) (h0 : P y'),
        transp P (contr X y y') h = h0) -> forall i : prop_tr X, P i
*)
Check (prop_tr_rect2 :
       forall (X : Type) (P : prop_tr X -> Type)
       (f:forall x : X, P (proj X x))
       (g:forall (y : prop_tr X) (h : P y) (y' : prop_tr X) (h0 : P y'),
        transp P (contr X y y') h = h0)
       (i i': prop_tr X) (e:i=i'),
       transp P e (prop_tr_rect X P f g i) = prop_tr_rect X P f g i').

(* Recursive 1-constructors not allowed yet (+ defines 2-constructor):
Inductive tr0 (X:Type) : Type :=
    | incl : X -> tr0 X
with paths :=
    | contr (z : tr0 X) (p : z=z): p = (eq_refl z).
*)

(* Set truncation *)
Inductive τ_0 X : Type :=
  | truncn : X -> τ_0 X
  | hub : (Circle -> τ_0 X) -> τ_0 X
with paths :=
  | spoke (l : Circle -> τ_0 X) (s : Circle) : (hub l) = (l s).
Check τ_0_rect.
(*
τ_0_rect
     : forall (X : Type) (P : τ_0 X -> Type),
       (forall x : X, P (truncn X x)) ->
       forall f0 : forall τ : Circle -> τ_0 X, P (hub X τ),
       (forall (l : Circle -> τ_0 X) (h : forall H : Circle, P (l H))
          (s : Circle), transp P (spoke X l s) (f0 l) = h s) ->
       forall τ : τ_0 X, P τ
*)
Check τ_0_rect2.

(* 2-constructor
Inductive quotient (A : Type) (R : A -> A -> Prop) : Type :=
| qproj : A -> quotient A R
with paths :=
| relate (x y : A) (h:R x y) : (qproj x) = (qproj y)
| contr1 (x y : quotient A R) (p q : x=y) : p = q.
 *)


Inductive hpushout {A B C : Type} (f : A -> B) (g : A -> C) : Type :=
  | inl : B -> hpushout f g
  | inr : C -> hpushout f g
with paths :=
  | glue (a : A) : (inl (f a)) = (inr (g a)).
Check hpushout_rect.
(*
hpushout_rect
     : forall (A B C : Type) (f : A -> B) (g : A -> C)
         (P : hpushout f g -> Type) (f0 : forall b : B, P (inl f g b))
         (f1 : forall c : C, P (inr f g c)),
       (forall a : A, transp P (glue A B C f g a) (f0 (f a)) = f1 (g a)) ->
       forall h : hpushout f g, P h
*)
Check hpushout_rect2.
