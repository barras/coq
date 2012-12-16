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

(** The declaration of a logic begins with a logic_kind instance that
    identifies the sort propositions live in. *)
Class logic_kind (X:Type) := prop_as_type : X->Type.
Local Notation T := (@prop_as_type _ _).

(** Then, each connective is declared as a separate class which
    arguments are first the connective itself, followed by the
    introduction and elimination rules. *)

Class trivial_prop `{L:logic_kind X}
  (true : X)
  (trueI : T true) := {}.

Class absurd_prop `{L:logic_kind X}
  (false : X)
  (falseE : forall Q:X, T false -> T Q) := {}.

Class conjunction `{L:logic_kind X}
  (and: X->X->X)
  (andI: forall A B:X, T A -> T B -> T (and A B))
  (andE1: forall A B:X, T (and A B) -> T A)
  (andE2: forall A B:X, T (and A B) -> T B) := {}.

Class disjunction `{L:logic_kind X}
  (or: X->X->X)
  (orI1: forall A B:X, T A -> T (or A B))
  (orI2: forall A B:X, T B -> T (or A B))
  (orE: forall A B Q:X, (T A->T Q)->(T B->T Q)->T(or A B) -> T Q) := {}.

Class equivalence `{L:logic_kind X}
  (iff: X->X->X)
  (iffI : forall A B:X, (T A->T B) -> (T B -> T A) -> T (iff A B))
  (iffE1 : forall A B:X, T (iff A B) -> T A -> T B)
  (iffE2 : forall A B:X, T (iff A B) -> T B -> T A) := {}.

(** We assume that implication is represented by the non-dependent
    product of Coq (->). trivial_kind is a sort containing propositions
    True and False. Negation is assumed to be defined as a combination
    of implication and absurd, thus no intro/elim rule is needed. *)
Class propositional_logic
  `(And:conjunction X and andI andE1 andE2)
  `(Or:!disjunction or orI1 orI2 orE)
  (not:X->X)
  `(Iff:!equivalence iff iffI iffE1 iffE2)
  `(True:!trivial_prop true trueI)
  `(False:!absurd_prop false falseE)
  (trivial_kind:Type) := {}.

(** We assume that universal qunatification is always represented
    by the dependent product (forall) of Coq. *)
Class first_order_logic `{L:logic_kind X}
  (ex : forall A:Type,(A->X)->X)
  (exI : forall (A:Type) (P:A->X) (x:A), T (P x) -> T (ex A P))
  (exE : forall (A:Type) (P:A->X) (Q:X), (forall x, T(P x)->T Q) ->
         T (ex A P) -> T Q) := {}.

Class equational_logic `{L:logic_kind X}
  (eq:forall A:Type,A->A->X)
  (ind : forall (A:Type)(x:A)(P:A->X), T(P x) ->
         forall y, T(eq A x y) -> T(P y))
  (refl : forall (A:Type)(x:A), T(eq A x x))
  (sym : forall (A:Type)(x y:A), T(eq A x y)->T(eq A y x))
  (trans : forall (A:Type)(x y z:A), T(eq A x y)->T(eq A y z)->T(eq A x z))
  (congr : forall (A B:Type)(f:A->B)(x y:A),
           T(eq A x y) -> T(eq B (f x) (f y))) := {}.

(** Classes joining the above data to form complete sets of connectives.
    Declaring a logic consists in producing an instance of one the two
    classes below. Then, compliant tactics can look up for a logic
    for a class of propositions. *)
Class full_logic
  `(PL:propositional_logic X and andI andE1 andE2 or orI1 orI2 orE
         iff iffI iffE1 iffE2 True TrueI False FalseE trivial_kind)
  `(FOL:!first_order_logic ex exI exE) := {}.

Class full_eq_logic
  `(PL:propositional_logic X and andI andE1 andE2 or orI1 orI2 orE
         iff iffI iffE1 iffE2 True TrueI False FalseE trivial_kind)
  `(FOL:!first_order_logic ex exI exE)
  `(EQL:!equational_logic eq ind refl sym trans congr) := {}.

End LogicClasses.

(** By default an eq logic can be deduced from its components,
    but with a low priority. However, it is strongly adviced to
    produce the full_logic/full_eq_logic instance directly, as it
    is more efficient and enables more features. As an example,
    the logic is then considered in the (finite!) list of
    available logics (for tactics doing a linear search for a
    logic).
 *)
Existing Instances Build_full_logic Build_full_eq_logic | 10.

