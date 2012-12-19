Definition U := Type.
Axiom magic:forall T,T.


Inductive circle : U :=
  base
with paths :=
  loop : base=base.

(*
Definition test_match_circle (c:circle) : nat :=
  fixmatch{h} c with
  | base => 0
  | loop => magic _ h
  end.
*)


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


Inductive isInhab0 (X:Type) : Type :=
    | proj0 : X -> isInhab0 X
with paths :=
    | contr0 (y y' : isInhab0 X) (x x':X) : (proj0 x) = (proj0 x').

Inductive isInhab1 (X:Type) : Type :=
    | proj1 (x: X): isInhab1 X
with paths :=
    | contr1 (y y' : nat->isInhab1 X) (n:nat) : (y n)=(y' 1).
Print isInhab1_rect.


(*Unset Elimination Schemes.*)
(*Inductive isInhab2 (X:Type) : Type :=
    | proj2 (x: X): isInhab2 X
with paths :=
    | contr2 (n:nat)(m:=0)(y y' : forall p:nat,n=p->isInhab2 X) (a:=0)(b:=0) : (y n eq_refl)=(y' 1 (magic _)).
Print isInhab2_rect. (* buggy eta expansion of branches *)
Notation "e @ x" := (eq_rect _ _ x _ e) (at level 60, right associativity).
*)

Inductive isInhab3 (X:Type)(f:X->X) : X->X->Type :=
    | proj3 (x: X): isInhab3 X f x x
with paths :=
    | contr3  (n:nat)(x x':X) (y y' : isInhab3 X f (f x') x) : y=y'.
Print isInhab3_rect.


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
unfold dmap.
Unset Printing Notations.
Implicit Arguments eq [ ].
(*
change 
((let y := basep1 A c in
 fun e : eq _ _ y =>
   eq
     (eq (P (S O) (basep1 A c))
        (eq_rect (basepn A (S O)) (P (S O))
           (circlep_rect A P f f0 f1 g (S O) (basepn A (S O))) 
           (basep1 A c) e)
        (circlep_rect A P f f0 f1 g (S O) (basep1 A c)))
     match
       e as e in (eq _ _ z)
       return
         (eq (P (S O) z)
            (eq_rect (basepn A (S O)) (P (S O))
               (circlep_rect A P f f0 f1 g (S O) (basepn A (S O))) z e)
            (circlep_rect A P f f0 f1 g (S O) z))
     with
     | eq_refl => eq_refl
     end (g n x c (fun m : nat => circlep_rect A P f f0 f1 g O (c m)))
)
(loopp A n x c)
).
*)


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