(** The menagerie *)

Notation "e @ x" := (eq_rect _ _ x _ e) (at level 60, right associativity).
Definition dmap {X:Type}{Y:X->Type}(f:forall x:X,Y x){x x':X}(e:x=x')
   : eq_rect x Y (f x) x' e = f x' :=
  match e in _=z return eq_rect x Y (f x) z e=f z with
  | eq_refl => eq_refl (f x)
  end.


Inductive Interval : Type :=
    | left : Interval
    | right : Interval
with paths :=
    | segment : left = right.

Check Interval_rect.
(*
Interval_rect
     : forall (P : Interval -> Type) (f : P left) (f0 : P right),
       ((forall H : Interval, P H) -> segment @ f = f0) ->
       forall i : Interval, P i
*)
Print Interval_rect.
(*
Interval_rect = 
fun (P : Interval -> Type) (f : P left) (f0 : P right)
  (g : (forall H : Interval, P H) -> segment @ f = f0) 
  (i : Interval) =>
match i as i0 return (P i0) with
| left => f
| right => f0
| segment {h} => g h
end
*)

Inductive Circle : Type :=
    | base : Circle
with paths :=
    | loop : base = base.

Check Circle_rect.
(*
Circle_rect
     : forall (P : Circle -> Type) (f : P base),
       ((forall H : Circle, P H) -> loop @ f = f) ->
       forall c : Circle, P c
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
       ((forall H : Circle', P H) -> upper @ f0 = f) ->
       ((forall H : Circle', P H) -> lower @ f = f0) ->
       forall c : Circle', P c
*)

(* Not accepted: use of refl *)
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
    | merid (x:X) : north = south. (* name x is required ?! *)

Check Susp_rect.
(*
Susp_rect
     : forall (X : Type) (P : Susp X -> Type) (f : P (north X))
         (f0 : P (south X)),
       ((forall H : Susp X, P H) -> forall x : X, merid X x @ f = f0) ->
       forall s : Susp X, P s
*)

Inductive Cyl {X Y : Type} (f : X -> Y) : Y -> Type :=
    | cyl_base : forall y:Y, Cyl f y
    | cyl_top : forall x:X, Cyl f (f x)
with paths :=
    | cyl_seg (x:X) : (cyl_top x) = (cyl_base (f x)).

Check Cyl_rect.
(*
Cyl_rect
     : forall (X Y : Type) (f : X -> Y) (P : forall y : Y, Cyl f y -> Type)
         (f0 : forall y : Y, P y (cyl_base f y))
         (f1 : forall x : X, P (f x) (cyl_top f x)),
       ((forall (H : Y) (H0 : Cyl f H), P H H0) ->
        forall x : X, cyl_seg X Y f x @ f1 x = f0 (f x)) ->
       forall (y : Y) (c : Cyl f y), P y c
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
       (forall (h : forall H : isInhab X, P H) (y y' : isInhab X),
        contr X y y' @ h y = h y') -> forall i : isInhab X, P i
*)
(*Axiom isInhab_rect : forall (X:Type),
         forall (P : isInhab X -> Type)
                (d_proj : forall x:X, P (proj x))
                (d_contr : forall (z z' : isInhab X) (w : P z) (w' : P z'), (contr z z') @ w = w'),
         forall z : isInhab X, P z
*)

(* Recursive 1-constructors not allowed yet:
Inductive tr0 (X:Type) : Type :=
    | incl : X -> tr0 X
with paths :=
    | contr (z : tr0 X) (p : z=z): p = (eq_refl z).
*)

(* 1-constructor builds equalities in X instead of tr0 X:
Inductive tr0 (X:Type) : Type :=
    | incl : X -> tr0 X
with paths :=
    | contr (l : Circle -> X) : (eq_refl (l base)) = (dmap l loop).
*)

(* Equivalent def: *)
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
       (forall (h : forall H : τ_0 X, P H) (l : Circle -> τ_0 X) (s : Circle),
        spoke X l s @ f0 l = h (l s)) -> forall τ : τ_0 X, P τ
*)

(*
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
     : forall (A B C : Type) (f : A -> B) (g : A -> C)
         (P : hpushout f g -> Type)
         (f0 : forall b : B, P (inl f g b))
         (f1 : forall f1 : C, P (inr f g f1)),
       ((forall H : hpushout f g, P H) ->
        forall a : A, glue A B C f g a @ f0 (f a) = f1 (g a)) ->
       forall h : hpushout f g, P h
*)
