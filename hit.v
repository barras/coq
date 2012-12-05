Definition U := Type.

Inductive circle : U :=
  base
with paths :=
  loop : base=base.

Print circle.

Axiom magic:forall T,T.
Eval compute in (fun P f => circle_rect P f (fun h => magic _) base). (* Array.map3 *)
Eval compute in (fun P f c => circle_rect P f (fun h => magic _) c). (* Array.map3 *)


Lemma L : base=base.
elim loop. (* case does not work... *)
exact loop.
Defined.
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

Inductive circlep (A:Type): nat->U :=
  basep : circlep A 0
| basep1 (_:nat) : circlep A 1
| basepn (n:nat) : circlep A n
with paths :=
  loopp (n:nat)(x:A)(c:A->circlep A 0) : basep=(basepn 0).
Print circlep_rect.


(* TODO: constructor not generalized/params! *)
(*Inductive circle0 (n:nat): U :=
  base0 : circle0 0
with paths := loop0 : base0=base0.*)
(*
Inductive circle1 (n:nat) : nat->U :=
  base1 m : circle1 n m
with paths := loop1 m : (base1 m ) = (base1 m). (* Evar! *)
*)

(* why rejected ??? *)
(*
Inductive circle2 (n:nat) : nat->U :=
  base2 m : circle2 n m
with paths := loop2 (m:nat) : (base2 m) = (base2 m).
*)


Drop.
#use"include";;
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
