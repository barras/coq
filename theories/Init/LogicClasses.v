(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Set Implicit Arguments.

Require Import Notations.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Section LogicClasses.

Local Generalizable All Variables.

Class logic_kind (X:Type) := prop_to_type : X->Type.
Local Notation T := (@prop_to_type _ _).

Class propositional_logic `{L:logic_kind X}
  (* Propositional connectives *)
  (iff and or:X->X->X) (not:X->X)
  (* (trivial is a sort containing propositions True and False) *)
  (True False:X) (trivial_kind:Type)
  (* Intro/elim rules (the or-elim and ex-falso might be restricted at some
     point) *)
(*  (T:=@prop_to_type X L) BUG: this is considered as an arg! *)
  (I:T True)
  (iffLR: forall (A B:X), T(iff A B) -> T A -> T B) 
  (iffRL: forall (A B:X), T(iff A B) -> T B -> T A) 
  (conj : forall (A B:X), T A -> T B -> T(and A B)) := {}.

Class first_order_logic `{L:logic_kind X} (ex:forall A:Type,(A->X)->X) := {}.

Class equational_logic `{L:logic_kind X} (eq:forall A:Type,A->A->X)
(*  (T:=prop_to_type L)*)
  (ind : forall (A:Type)(x:A)(P:A->X), T(P x) -> forall y, T(eq A x y) -> T(P y))
  (refl : forall (A:Type)(x:A), T(eq A x x))
  (sym : forall (A:Type)(x y:A), T(eq A x y)->T(eq A y x))
  (trans : forall (A:Type)(x y z:A), T(eq A x y)->T(eq A y z)->T(eq A x z))
  (* needs eq other two types! *)
  (congr : forall (A B:Type)(f:A->B)(x y:A), T(eq A x y) -> T(eq B (f x) (f y))) :=
  {}.

(** Classes joining the above data to form complete sets of connectives *)
Class full_logic
  `(PL:propositional_logic X True False trivial_kind iff and or not
         I iffLR iffRL conj)
  `(FOL:!first_order_logic ex).
Class full_eq_logic
  `(PL:propositional_logic X True False trivial_kind iff and or not
         I iffLR iffRL conj)
  `(FOL:!first_order_logic ex)
  `(EQL:!equational_logic eq ind refl sym trans congr).


End LogicClasses.

(* By default an eq logic can be deduced from its components *)
Existing Instances Build_full_logic Build_full_eq_logic | 10.


(*
Class default_logic :=
  { kind : Type ;
    log : logic_kind kind;
    plog : propositional_logic log Tr Fa ;
    eqlog : equational_logic }.
*)(*
Parameter other_log : logic_kind Type.
Instance other_dflt : default_logic :={|log:=other_log|}.
Existing Instance prop_is_dflt.
*)
