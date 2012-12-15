(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Libnames
open Globnames
open Nametab
open Term
open Pattern
open Util

(** This module collects the global references, constructions and
    patterns of the standard library used in ocaml files *)

(** {6 ... } *)
(** [find_reference caller_message [dir;subdir;...] s] returns a global
   reference to the name dir.subdir.(...).s; the corresponding module
   must have been required or in the process of being compiled so that
   it must be used lazyly; it raises an anomaly with the given message
   if not found *)

type message = string

val find_reference : message -> string list -> string -> global_reference

(** [coq_reference caller_message [dir;subdir;...] s] returns a
   global reference to the name Coq.dir.subdir.(...).s *)

val coq_reference : message -> string list -> string -> global_reference

(** idem but return a term *)

val coq_constant : message -> string list -> string -> constr

(** Synonyms of [coq_constant] and [coq_reference] *)

val gen_constant : message -> string list -> string -> constr
val gen_reference :  message -> string list -> string -> global_reference

(** Search in several modules (not prefixed by "Coq") *)
val gen_constant_in_modules : string->string list list-> string -> constr
val arith_modules : string list list
val zarith_base_modules : string list list
val init_modules : string list list

(** For tactics/commands requiring vernacular libraries *)
val check_required_library : string list -> unit

(** {6 Global references } *)

(** Modules *)
val logic_type_module : dir_path

val datatypes_module_name : string list

(** Natural numbers *)
val nat_path : full_path
val glob_nat : global_reference
val path_of_O : constructor
val path_of_S : constructor
val glob_O : global_reference
val glob_S : global_reference

(** Booleans *)
val glob_bool : global_reference
val path_of_true : constructor
val path_of_false : constructor
val glob_true : global_reference
val glob_false : global_reference

(************************************************************************)
(** A generic notion of logic *)

type coq_logic = {
  (** The False proposition *)
  log_False : constr;
  log_FalseE : constr;

  (** The True proposition and its unique proof *)
  log_True : constr;
  log_TrueI : constr;

  (** The "minimal sort" containing both True and False *)
  log_bottom_sort : sorts;

  (** Negation *)
  log_not : constr;

  (** Conjunction *)
  log_and : constr;
  log_andI : constr;
  log_andE1 : constr;
  log_andE2 : constr;

  (** Disjunction *)
  log_or : constr;
  log_orI1 : constr;
  log_orI2 : constr;

  (* Equivalence *)
  log_iff : constr;
  log_iffI : constr;
  log_iffE1 : constr;
  log_iffE2 : constr;

  (** Existential quantifier *)
  log_ex : constr;
  log_exI : constr;
  log_exE : constr
}

(** Lookup for a logic. The logic_id is a "key" to search the
    logic corresponding to (for instance) the type of its
    propositions. *)
type logic_id = sorts
val find_logic : Environ.env -> logic_id option -> coq_logic

(** Linear search for a logic satisfying a predicate. Only the
    logics declared through the full_logic will be considered
    by search_logic. *)
val search_logic : (coq_logic -> bool) -> coq_logic list

(************************************************************************)

type coq_eq_data = {
  eq   : constr; (* forall A, A -> A -> s *)
  ind  : constr; (* forall A x P, P x -> forall y, eq x y -> P y *)
  refl : constr; (* forall A x, eq x x *)
  sym  : constr; (* forall A x y, eq x y -> eq y x *)
  trans: constr; (* forall A x y z, eq x y -> eq y z -> eq x z *)
  congr: constr  (* forall A B (f:A->B) x y, eq x y -> eq (f x) (f y) *)
}

(** Data needed for discriminate and injection *)

type coq_inversion_data = {
  inv_eq   : constr; (** : forall params, args -> Prop *)
  inv_ind  : constr; (** : forall params P (H : P params) args, eq params args 
			 ->  P args *)
  inv_congr: constr  (** : forall params B (f:t->B) args, eq params args -> 
			 f params = f args *)
}

type coq_equality = {
  eq_logic : coq_logic;
  eq_data : coq_eq_data;
  eq_inv : coq_inversion_data delayed
}

(** Equalities are identified by the connective (eq,identity,etc.) *)
type equality_id = constr

(** Look up and linear search for an equational theory (and the associated
    logic). As above, only the instances declared through full_eq_logic will
    be considered by search_equality. *)
val find_equality : Environ.env -> equality_id option -> coq_equality
val search_equality : (coq_equality -> bool) -> coq_equality list

(************************************************************************)
(** {6 ... } *)
(** Constructions and patterns related to Coq initial state are unknown
   at compile time. Therefore, we can only provide methods to build
   them at runtime. This is the purpose of the [constr delayed] and
   [constr_pattern delayed] types. Objects of this time needs to be
   forced with [delayed_force] to get the actual constr or pattern 
   at runtime. *)

type coq_bool_data = {
  andb : constr;
  andb_prop : constr;
  andb_true_intro : constr}
val build_bool_type : coq_bool_data delayed

(** {6 For Equality tactics } *)
type coq_sigma_data = {
  proj1 : constr;
  proj2 : constr;
  elim  : constr;
  intro : constr;
  typ   : constr }
val build_sigma_type : coq_sigma_data delayed
val coq_existT_ref : global_reference lazy_t

(** Non-dependent pairs in Set from Datatypes *)
val build_prod : coq_sigma_data delayed

(** Specif and decidability *)
val build_coq_sumbool : constr delayed

(** A (soon deprecated?) module [roviding access to constants of
    the standard library by their name. For logic and theory of
    equality, it is advised to use the above API. *)

module Std : sig

val logic_module : dir_path
val logic_module_name : string list

val coq_eq_equality : coq_equality delayed
val coq_prop_logic : coq_logic delayed

(** Equality *)
val glob_eq : global_reference
val glob_identity : global_reference
val glob_jmeq : global_reference

val build_coq_identity_data : coq_eq_data delayed
val build_coq_jmeq_data : coq_eq_data delayed
val build_coq_jmeq_full : coq_equality delayed

val build_coq_f_equal2 : constr delayed

val build_coq_inversion_identity_data : coq_inversion_data delayed
val build_coq_inversion_jmeq_data : coq_inversion_data delayed
val build_coq_inversion_eq_true_data : coq_inversion_data delayed

val coq_eq_ref : global_reference lazy_t
val coq_identity_ref : global_reference lazy_t
val coq_jmeq_ref : global_reference lazy_t
val coq_eq_true_ref : global_reference lazy_t
val coq_existS_ref : global_reference lazy_t
val coq_exist_ref : global_reference lazy_t
val coq_not_ref : global_reference lazy_t
val coq_False_ref : global_reference lazy_t
val coq_sumbool_ref : global_reference lazy_t
val coq_sig_ref : global_reference lazy_t

val coq_or_ref : global_reference lazy_t
val coq_iff_ref : global_reference lazy_t

(** Sigma (sig and sigS) *)
val build_sigma : coq_sigma_data delayed
val build_sigma_set : coq_sigma_data delayed

end
