(** The menagerie *)

(* Several notations and utility functions *)

Notation "'transp' P e x" := (eq_rect _ P x _ e)
  (at level 10, P at next level, e at next level, x at next level, no associativity).
Scheme eq_indd := Induction for eq Sort Prop.
Lemma eq_rect_cst (A:Type) (x y:A) (e:x=y) (P:Type) (p:P) :
  eq_rect x (fun _ => P) p y e = p.
case e; reflexivity.
Qed.
Definition dmap {X:Type}{Y:X->Type}(f:forall x:X,Y x){x x':X}(e:x=x')
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
       loop @ f = f -> forall c : Circle, P c
*)
Print Circle_rect.
(*
fun (P : Circle -> Type) (f : P base) (g : transp P loop f = f) (c : Circle) =>
fixmatch {h} c as c0 return (P c0) with
| base => f
| loop _ => g
end
*)

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

Program Definition Circle'2Circle (c:Circle') : Circle :=
  Circle'_rect (fun _ => Circle) base base _ _ c.
Next Obligation.
apply eq_rect_cst.
Defined.
Next Obligation.
apply eq_rect_cst.
Defined.

Program Definition Circle2Circle' (c:Circle) : Circle' :=
  Circle_rect (fun _ => Circle') east _ c.
Next Obligation.
apply eq_rect_cst.
Defined.

Eval compute in Circle2Circle' base.

Eval compute in fun (P:Circle->Type) (x:P base) =>
  transp P loop x.
(* A match over a constructor, and it does not compute!
       match loop in (_ = y) return (P y) with
       | eq_refl => x
       end
*)

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
| segment x => g x
end
*)

Lemma Interval_connected (x:Interval): x=right.
eapply Interval_rect with (i:=x).
Show Existentials.
instantiate (1:=eq_refl).
instantiate (1:=segment).
unfold eq_rect.
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

Inductive isInhab (X:Type) : Type :=
    | proj : X -> isInhab X
with paths :=
    | contr (y y' : isInhab X) : y=y'.
Check isInhab_rect.
(*
isInhab_rect
     : forall (X : Type) (P : isInhab X -> Type),
       (forall x : X, P (proj X x)) ->
       (forall (y : isInhab X) (h : P y) (y' : isInhab X) (h0 : P y'),
        transp P (contr X y y') h = h0) -> forall i : isInhab X, P i
*)

(* Recursive 1-constructors not allowed yet (+ defines 2-constructor):
Inductive tr0 (X:Type) : Type :=
    | incl : X -> tr0 X
with paths :=
    | contr (z : tr0 X) (p : z=z): p = (eq_refl z).
*)

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
