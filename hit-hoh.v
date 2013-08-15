Definition U := Type.
Axiom magic:forall T,T.
Notation "'transp' P e x" := (eq_rect _ P x _ e)
  (at level 10, P at next level, e at next level, x at next level, no associativity).
Lemma eq_rect_cst (A:Type) (x y:A) (e:x=y) (P:Type) (p:P) :
  transp (fun _ => P) e p = p.
case e; reflexivity.
Qed.


Inductive Circle : Type :=
    | Base (n n':nat) : Circle
with paths :=
    | Loop n m : (Base n n) = (Base m m).

Print Circle_rect.
Check
fun (P : Circle -> Type)
 (f : forall n n', P (Base n n'))
 (g : forall n m, transp P (Loop n m) (f n n) = (f m m)) (c : Circle) =>
fixmatch {h'} c as c0 return (P c0) with
| Base n n' => f n n'
| Loop n m => g n m
end.



Inductive Circlep (X:Type) : Type :=
    | Basep (n n':X) : Circlep X
with paths :=
    | Loopp n m : (Basep n n) = (Basep m m).
Implicit Arguments Basep [X].
Implicit Arguments Loopp [X].
Print Circlep_rect2.
Check
fun X (P : Circlep X -> Type)
 (f : forall n n', P (Basep n n'))
 (g : forall n m, transp P (Loopp n m) (f n n) = (f m m))
 (c : Circlep X) =>
fixmatch {h'} c as c0 return (P c0) with
| Basep n n' => f n n'
| Loopp n m => g n m
end.


Inductive circle : U :=
  base
with paths :=
  loop : base=base.

Definition test_match_circle (c:circle) : nat :=
  fixmatch{h} c with
  | base => 0
  | loop => magic _ h (* TODO: usage of h... *)
  end.


Print circle.

Eval compute in (fun P f => circle_rect P f (magic _) base).
Eval compute in (fun P f c => circle_rect P f (magic _) c).


Lemma L : base=base.
(*case loop.*)
elim loop. (* case does not work... *)
exact loop.
Defined.
Print L.
Eval compute in L.
(* --> match loop with ... end stuck *)

Inductive circle' : U :=
  base' (n:nat)
| base''
with paths :=
  loop0 : base''=base''
| loop1 (n:_) : (base' n)=base''
| loop2 (n:circle') : base''=base''.

Print circle'_rect.

Check (fun (P : circle' -> Type) (f : forall n : nat, P (base' n)) 
  (f0 : P base'') (g : transp P loop0 f0 = f0)
  (g0 : forall n : nat, transp P (loop1 n) (f n) = f0)
  (g1 : forall n : circle', P n -> transp P (loop2 n) f0 = f0) 
  (c : circle') =>
fixmatch {h} c as c0 return (P c0) with
| base' x => f x
| base'' => f0
| loop0 => g
| loop1 n => g0 n
| loop2 n => g1 n (h n)
end).

Inductive isInhabn : Type :=
    | projn : nat -> isInhabn
with paths :=
    | contrn (y y' : isInhabn) (x x':nat) : (projn x) = (projn x').
Print isInhabn_rect.
Print isInhabn_rect2.
Check (fun (P : isInhabn -> Type) (f : forall n : nat, P (projn n))
  (g : forall y : isInhabn,
       P y ->
       forall y' : isInhabn,
       P y' -> forall x x' : nat, transp P (contrn y y' x x') (f x) = f x')
  (i : isInhabn) =>
fixmatch {h} i as i0 return (P i0) with
| projn x => f x
| contrn y y' x x' => g y (h y) y' (h y') x x'
end).

Inductive isInhab0 (X:Type) : Type :=
    | proj0 : X -> isInhab0 X
with paths :=
    | contr0 (y y' : isInhab0 X) (x x':X) : (proj0 x) = (proj0 x').
Implicit Arguments proj0 [X].
Implicit Arguments contr0 [X].
Print isInhab0_rect.
Print isInhab0_rect2.
Check (fun (X : Type) (P : isInhab0 X -> Type) (f : forall x : X, P (proj0 x))
  (g : forall y : isInhab0 X,
       P y ->
       forall y' : isInhab0 X,
       P y' -> forall x x' : X, transp P (contr0 y y' x x') (f x) = f x')
  (i : isInhab0 X) =>
fixmatch {h} i as i0 return (P i0) with
| proj0 x => f x
| contr0 y y' x x' => g y (h y) y' (h y') x x'
end).

Inductive isInhab1 (X:Type) : Type :=
    | proj1 (x: X): isInhab1 X
with paths :=
    | contr1 (y y' : nat->isInhab1 X) (n:nat) : (y n)=(y' 1).
Implicit Arguments proj1 [X].
Implicit Arguments contr1 [X].
Print isInhab1_rect.
Check (fun (X : Type) (P : isInhab1 X -> Type) (f : forall x : X, P (proj1 x))
  (g : forall (y : nat -> isInhab1 X) (h : forall H : nat, P (y H))
         (y' : nat -> isInhab1 X) (h0 : forall H : nat, P (y' H)) 
         (n : nat), transp P (contr1 y y' n) (h n) = h0 1) 
  (i : isInhab1 X) =>
fixmatch {h} i as i0 return (P i0) with
| proj1 x => f x
| contr1 y y' n =>
    g y (fun H : nat => h (y H)) y' (fun H : nat => h (y' H)) n
end).


(*Unset Elimination Schemes.*)
(*Inductive isInhab2 (X:Type) : Type :=
    | proj2 (x: X): isInhab2 X
with paths :=
    | contr2 (n:nat)(m:=0)(y y' : forall p:nat,n=p->isInhab2 X) (a:=0)(b:=0) : (y n eq_refl)=(y' 1 (magic _)).
Print isInhab2_rect. (* buggy eta expansion of branches *)
Notation "e @ x" := (eq_rect _ _ x _ e) (at level 60, right associativity).
*)

Inductive IPA (X:Type)(u:X->X) : X->X->Type :=
    | C3  (n:nat)(x x':X) (y y' : IPA X u (u x') x) : IPA X u x x'
with paths :=
    | P3  (n:nat)(x x':X) (y y' : IPA X u (u x') x) : y=y'.
Implicit Arguments C3 [X u].
Implicit Arguments P3 [X u].
Print IPA_rect.
Check (fun
 (X : Type) (u : X -> X) (P : forall x x0 : X, IPA X u x x0 -> Type)
  (f : forall (n : nat) (x x' : X) (y y' : IPA X u (u x') x),
       P x x' (C3 n x x' y y'))
  (g : forall (n : nat) (x x' : X) (y : IPA X u (u x') x) 
         (h : P (u x') x y) (y' : IPA X u (u x') x) 
         (h0 : P (u x') x y'), transp (P (u x') x) (P3 n x x' y y') h = h0)
  (y y0 : X) (i : IPA X u y y0) =>
fixmatch {h} i as i0 in (IPA _ _ y1 y2) return (P y1 y2 i0) with
| C3 x x0 x1 x2 x3 => f x x0 x1 x2 x3
| P3 n x x' y1 y' => g n x x' y1 (h (u x') x y1) y' (h (u x') x y')
end).


Inductive isInhab3 (X:Type)(f:X->X) : X->X->Type :=
    | proj3 (x: X): isInhab3 X f x x
with paths :=
    | contr3  (n:nat)(x x':X) (y y' : isInhab3 X f (f x') x) : y=y'.
Implicit Arguments proj3 [X f].
Implicit Arguments contr3 [X f].
Print isInhab3_rect.


Check (fun (X : Type) (f : X -> X) (P : forall x x0 : X, isInhab3 X f x x0 -> Type)
  (f0 : forall x : X, P x x (proj3 x))
  (g : forall (n : nat) (x x' : X) (y : isInhab3 X f (f x') x)
         (h : P (f x') x y) (y' : isInhab3 X f (f x') x) 
         (h0 : P (f x') x y'),
       transp (P (f x') x) (contr3 n x x' y y') h = h0) 
  (y y0 : X) (i : isInhab3 X f y y0) =>
fixmatch {h} i as i0 in (isInhab3 _ _ y1 y2) return (P y1 y2 i0) with
| proj3 x => f0 x
| contr3 n x x' y1 y' => g n x x' y1 (h (f x') x y1) y' (h (f x') x y')
end).

Inductive isInhab (X:Type)(f:X->X) : X->X->Type :=
    | proj (x: X): isInhab X f x x
with paths :=
    | contr  (n:nat)(x x':X) (y y' : nat->isInhab X f (f x') x) : (y n)=(y' 1).
Print isInhab_rect.

Inductive Z2Z :=
| ze
| su (_:Z2Z)
with paths :=
| mod : ze = (su (su ze)).
Check Z2Z_rect.

Definition Z2Z_case' (P:Type) (f:P) (f0:Z2Z->P) (g:f = f0 (su ze)) (z:Z2Z) : P :=
  fixmatch {h} z return P with
  | ze => f
  | su k => f0 k
  | mod => eq_trans (eq_rect_cst _ _ _ mod P f) g
  end.

Lemma eq2 P f f0 g : Z2Z_case' P f f0 g (su ze) = Z2Z_case' P f f0 g (su (su (su ze))).
simpl.
apply f_equal.
exact mod.
Defined.

Require Import Program.
Program Fixpoint Z2Z_rect' (P:Type) (f:P) (f0:Z2Z->P->P) (g:f=f0 (su ze) (f0 ze f)) (z:Z2Z) {struct z}: P :=
  Z2Z_case' P f (fun z' => f0 z' (Z2Z_rect' P f f0 g z')) _ z.
Next Obligation.
apply eq_trans with (1:=g).
f_equal.
admit. (* f0 ze f = Z2Z_rect' P f f0 g (su ze) *)
Abort.

(*Fixpoint F (z:Z2Z) : nat :=
  Z2Z_rect' nat 0 (fun z' => Z2Z_rect' nat 0 (fun z''
*)
(*
 forall (P : Z2Z -> Type) (f : P ze) (f0 : forall z : Z2Z, P (su z)),
       ((forall H : Z2Z, P H) -> mod @ f = f0 (su ze)) ->
       forall z : Z2Z, P z
*)
(*
Check (fun (P:Z2Z->Type)
   (f:P ze)
   (f':forall z, P z -> P (su z))
   (g: mod @ f = f' (su ze) (f' ze f)) =>
  fix Zrec (z:Z2Z) :=
    Z2Z_rect P f (fun z' => f' z' (Zrec z')) (fun _ => g Zrec) z
).
*)

Inductive circlep (A:Type): nat->U :=
  basep : circlep A 0
| basep1 (_:nat->circlep A 0) : circlep A 1
| basepn (n:nat) : circlep A n
with paths :=
  loopp (n:nat)(x:A)(c:nat->circlep A 0) : (basepn 1)=(basep1 c).
Print circlep_rect.
Check (fun (A : Type) (P : forall n : nat, circlep A n -> Type) 
  (f : P 0 (basep A)) (f0 : forall c : nat -> circlep A 0, P 1 (basep1 A c))
  (f1 : forall n : nat, P n (basepn A n))
  (g : forall (n : nat) (x : A) (c : nat -> circlep A 0),
       (forall H : nat, P 0 (c H)) ->
       transp (P 1) (loopp A n x c) (f1 1) = f0 c) 
  (n : nat) (c : circlep A n) =>
fixmatch {h} c as c0 in (circlep _ n0) return (P n0 c0) with
| @basep _ => f
| @basep1 _ x => f0 x
| @basepn _ x => f1 x
| @loopp _ n0 x c0 => g n0 x c0 (fun H : nat => h 0 (c0 H))
end).

Section CirclepRec.

Definition dmap {X:Type}{Y:X->Type}(f:forall x:X,Y x){x x':X}(e:x=x')
   : eq_rect x Y (f x) x' e = f x' :=
  match e in _=z return eq_rect x Y (f x) z e=f z with
  | eq_refl => eq_refl (f x)
  end.

Lemma circlep_eqn : forall A P f f0 f1 g n x c,
  dmap (circlep_rect A P f f0 f1 g _) (loopp A n x c) =
  g n x c (fun m => circlep_rect A P f f0 f1 g _ (c m)).
intros.
pose (H := circlep_rect2 A P f f0 f1 g _ _ _ (loopp A n x c)).
(* simpl in H. bogus *)
unfold circlep_rect2 in H. (* FIXME: closure.ml *)
transitivity (circlep_rect2 A P f f0 f1 g _ _ _ (loopp A n x c)).
2:unfold circlep_rect2.
Set Printing All.
Check ( @eq
     (@eq (P (S O) (basep1 A c))
        (@eq_rect (circlep A (S O)) (basepn A (S O)) 
           (P (S O)) (circlep_rect A P f f0 f1 g (S O) (basepn A (S O)))
           (basep1 A c) (loopp A n x c))
        (circlep_rect A P f f0 f1 g (S O) (basep1 A c)))
     (@dmap (circlep A (S O)) (P (S O)) (circlep_rect A P f f0 f1 g (S O))
        (basepn A (S O)) (basep1 A c) (loopp A n x c))
     (circlep_rect2 A P f f0 f1 g (S O) (basepn A (S O)) 
        (basep1 A c) (loopp A n x c)) ).
case (loopp A n x c).
Check (  @eq
     (@eq (P (S O) (basepn A (S O)))
        (@eq_rect (circlep A (S O)) (basepn A (S O)) 
           (P (S O)) (circlep_rect A P f f0 f1 g (S O) (basepn A (S O)))
           (basepn A (S O)) (@eq_refl (circlep A (S O)) (basepn A (S O))))
        (circlep_rect A P f f0 f1 g (S O) (basepn A (S O))))
     (@dmap (circlep A (S O)) (P (S O)) (circlep_rect A P f f0 f1 g (S O))
        (basepn A (S O)) (basepn A (S O))
        (@eq_refl (circlep A (S O)) (basepn A (S O))))
     (circlep_rect2 A P f f0 f1 g (S O) (basepn A (S O)) 
        (basepn A (S O)) (@eq_refl (circlep A (S O)) (basepn A (S O)))) ).
lazy beta delta [circlep_rect2].
lazy beta delta iota. (* bug: closure.ml *)
Check ( @eq (@eq (P (S O) (basepn A (S O))) (f1 (S O)) (f1 (S O)))
     (@eq_refl (P (S O) (basepn A (S O))) (f1 (S O)))
     (@eq_refl (fun c0 : circlep A (basepn A (S O)) => P (basepn A (S O)) c0)
        (f1 (S O))) ).

Unset Printing Notations.

Variable
  (A : Type) (P : forall n : nat, circlep A n -> Type)
  (f : P 0 (basep A))
  (f0: forall c : nat -> circlep A 0, (forall n, P 0 (c n)) -> P 1 (basep1 A c))
  (f1 : forall n : nat, P n (basepn A n))
  (g: forall (h:forall (n : nat) (c : circlep A n), P n c)
             (n : nat) (x : A) (c : nat -> circlep A 0),
      eq_rect _ (P 1) (f1 1) _ (loopp A n x c) = f0 c (fun n => h 0 (c n))).


(*
Fixpoint circlep_recu (n : nat) (c : circlep A n) : P n c :=
  circlep_rect A P
    f
    (fun c => f0 c (fun n => circlep_recu 0 (c n)))
    f1
    g
    n c.

*)
(* TODO: non-unif params anomaly *)
(*Inductive circle0 (n:nat): U :=
  base0 : circle0 0
with paths := loop0 : base0=base0. 
*)


Inductive circle1 (n:nat) : nat->U :=
  base1 m : circle1 n m
with paths := loop1_ m : (base1 m ) = (base1 m).

Inductive circle2 (n:nat) : nat->U :=
  base2 m : circle2 n m
with paths := loop2_ (m:nat) : (base2 m) = (base2 m).

(*
Drop.
#use"include";;
#trace build_induction_scheme;;
#trace Inductive.build_path_rec_branch_type;;


#trace check_inductive;;
#trace get_constructors;;
#trace build_induction_scheme;;
#trace Inductive.build_path_branch_type;;


get_path_constructor;;



Drop.
#use"include";;
let base = constr_of_string "base";;
let ind = fst(destConstruct base);;
let eqind = (fst ind,-1);;
let (mib,mip) = lookup_mind_specif (Global.env()) ind;;
let a = arities_of_constructors (Global.env()) ind;;
let a = arities_of_constructors (Global.env()) eqind;;
*)