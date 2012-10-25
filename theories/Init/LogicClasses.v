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

(* All class fields are dummy *)
Local Generalizable All Variables.
Class logic_kind (X:Type) := prop_to_type : X->Type.
Local Notation T := (@prop_to_type _ _).
Class propositional_logic `{L:logic_kind X}
  (* connectives *)
  (True False:X) (trivial_kind:Type) (iff and or:X->X->X) (not:X->X)
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
  (refl : forall (A:Type)(x:A), T(eq A x x))
  (sym : forall (A:Type)(x y:A), T(eq A x y)->T(eq A y x))
  (trans : forall (A:Type)(x y z:A), T(eq A x y)->T(eq A y z)->T(eq A x z)) :=
  {}.
Class full_logic
  `(PL:propositional_logic X True False trivial_kind iff and or not
         I iffLR iffRL conj)
  `(FOL:!first_order_logic ex).
Class full_eq_logic
  `(PL:propositional_logic X True False trivial_kind iff and or not
         I iffLR iffRL conj)
  `(FOL:!first_order_logic ex)
  `(EQL:!equational_logic eq refl sym trans).


End LogicClasses.

(* By default an eq logic can be deduced from its components *)
Existing Instances Build_full_logic Build_full_eq_logic.
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
