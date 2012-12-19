(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Names
open Univ
open Term
open Termops
open Namegen
open Declarations
open Environ
open Reductionops

(* The following three functions are similar to the ones defined in
   Inductive, but they expect an env *)

let type_of_inductive env ind =
 let specif = Inductive.lookup_mind_specif env ind in
  Inductive.type_of_inductive env specif

(* Return type as quoted by the user *)
let type_of_constructor env cstr =
 let specif =
  Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
 Inductive.type_of_constructor cstr specif

(* Return constructor types in user form *)
let type_of_constructors env ind =
  let specif = Inductive.lookup_mind_specif env ind in
  (Inductive.type_of_constructors ind specif,
   Inductive.arities_of_path_constructors ind specif)

(* Return constructor types in normal form *)
let arities_of_constructors env ind =
  let specif = Inductive.lookup_mind_specif env ind in
  (Inductive.arities_of_constructors ind specif,
   Inductive.arities_of_path_constructors ind specif)

(* [inductive_family] = [inductive_instance] applied to global parameters *)
type inductive_family = inductive * constr list

let make_ind_family (mis, params) = (mis,params)
let dest_ind_family (mis,params) = (mis,params)

let map_ind_family f (mis,params) = (mis, List.map f params)

let liftn_inductive_family n d = map_ind_family (liftn n d)
let lift_inductive_family n = liftn_inductive_family n 1

let substnl_ind_family l n = map_ind_family (substnl l n)


type inductive_type = IndType of inductive_family * constr list

let make_ind_type (indf, realargs) = IndType (indf,realargs)
let dest_ind_type (IndType (indf,realargs)) = (indf,realargs)

let map_inductive_type f (IndType (indf, realargs)) =
  IndType (map_ind_family f indf, List.map f realargs)

let liftn_inductive_type n d = map_inductive_type (liftn n d)
let lift_inductive_type n = liftn_inductive_type n 1

let substnl_ind_type l n = map_inductive_type (substnl l n)

let mkAppliedInd (IndType ((ind,params), realargs)) =
  applist (mkInd ind,params@realargs)

(* Does not consider imbricated or mutually recursive types *)
let mis_is_recursive_subset listind rarg =
  let one_is_rec rvec =
    List.exists
      (fun ra ->
        match dest_recarg ra with
	  | Mrec (_,i) -> List.mem i listind
          | _ -> false) rvec
  in
  Array.exists one_is_rec (dest_subterms rarg)

let mis_is_recursive (ind,mib,mip) =
  mis_is_recursive_subset (List.interval 0 (mib.mind_ntypes - 1))
    mip.mind_recargs

let mis_nf_constructor_type (ind,mib,mip) j =
  let specif = mip.mind_nf_lc
  and ntypes = mib.mind_ntypes
  and nconstr = Array.length mip.mind_consnames in
  let make_Ik k = mkInd ((fst ind),ntypes-k-1) in
  if j > nconstr then error "Not enough constructors in the type.";
  substl (List.tabulate make_Ik ntypes) specif.(j-1)

(* Arity of constructors excluding parameters and local defs *)

let mis_constr_nargs indsp =
  let (mib,mip) = Global.lookup_inductive indsp in
  let recargs = dest_subterms mip.mind_recargs in
  let precargs = dest_subterms mip.mind_precargs in
  Array.map List.length recargs,
  Array.map List.length precargs

let mis_constr_nargs_env env (kn,i) =
  let mib = Environ.lookup_mind kn env in
  let mip = mib.mind_packets.(i) in
  let recargs = dest_subterms mip.mind_recargs in
  let precargs = dest_subterms mip.mind_precargs in
  Array.map List.length recargs,
  Array.map List.length precargs

(* Arity of constructors excluding local defs *)

let mis_constructor_nargs (indsp,j) =
  let (mib,mip) = Global.lookup_inductive indsp in
  if j <= Array.length mip.mind_consnames then
    recarg_length mip.mind_recargs j + mib.mind_nparams
  else
    recarg_length mip.mind_precargs (j-Array.length mip.mind_consnames)
    + mib.mind_nparams

let mis_constructor_nargs_env env ((kn,i),j) =
  let mib = Environ.lookup_mind kn env in
  let mip = mib.mind_packets.(i) in
  if j <= Array.length mip.mind_consnames then
    recarg_length mip.mind_recargs j + mib.mind_nparams
  else
    recarg_length mip.mind_precargs (j-Array.length mip.mind_consnames)
    + mib.mind_nparams

(* Arity of constructors with arg and defs *)

let mis_constructor_nhyps (indsp,j) =
  let (mib,mip) = Global.lookup_inductive indsp in
  if j <= Array.length mip.mind_consnames then
    mip.mind_consnrealdecls.(j-1) + rel_context_length (mib.mind_params_ctxt)
  else
    mip.mind_pconsnrealdecls.(j-1-Array.length mip.mind_consnames) + rel_context_length (mib.mind_params_ctxt)

let mis_constructor_nhyps_env env ((kn,i),j) =
  let mib = Environ.lookup_mind kn env in
  let mip = mib.mind_packets.(i) in
  if j <= Array.length mip.mind_consnames then
    mip.mind_consnrealdecls.(j-1) + rel_context_length (mib.mind_params_ctxt)
  else
    mip.mind_pconsnrealdecls.(j-1-Array.length mip.mind_consnames) + rel_context_length (mib.mind_params_ctxt)

let constructor_nrealargs env (ind,j) =
  let (_,mip) = Inductive.lookup_mind_specif env ind in
  if j<=Array.length mip.mind_consnames then
    recarg_length mip.mind_recargs j
  else
    rel_context_nhyps (mip.mind_pathcons.(j-Array.length mip.mind_consnames-1).c1_args)+1
    
let constructor_nrealhyps (ind,j) =
  let (mib,mip) = Global.lookup_inductive ind in
  if j<=Array.length mip.mind_consnames then
    mip.mind_consnrealdecls.(j-1)
  else
    mip.mind_pconsnrealdecls.(j-Array.length mip.mind_consnames-1)

let get_full_arity_sign env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_arity_ctxt

let nconstructors ind =
  let (mib,mip) = Inductive.lookup_mind_specif (Global.env()) ind in
  Array.length mip.mind_consnames

let npconstructors ind =
  let (mib,mip) = Inductive.lookup_mind_specif (Global.env()) ind in
  Array.length mip.mind_pathcons

let mis_constructor_has_local_defs (indsp,j) =
  let (mib,mip) = Global.lookup_inductive indsp in
  if j <= Array.length mip.mind_consnames then
    let l1 = mip.mind_consnrealdecls.(j-1) + rel_context_length (mib.mind_params_ctxt) in
    let l2 = recarg_length mip.mind_recargs j + mib.mind_nparams in
    not (Int.equal l1 l2)
  else
    let j' = j - Array.length mip.mind_consnames in
    let pc = mip.mind_pathcons.(j'-1) in
    List.exists (fun (na,b,ty) -> b<>None) pc.c1_args

let inductive_has_local_defs ind =
  let (mib,mip) = Global.lookup_inductive ind in
  let l1 = rel_context_length (mib.mind_params_ctxt) + mip.mind_nrealargs_ctxt in
  let l2 = mib.mind_nparams + mip.mind_nrealargs in
  not (Int.equal l1 l2)

(* Length of arity (w/o local defs) *)

let inductive_nparams ind =
  (fst (Global.lookup_inductive ind)).mind_nparams

let inductive_nargs ind =
  let (mib,mip) = Global.lookup_inductive ind in
  (rel_context_length (mib.mind_params_ctxt), mip.mind_nrealargs_ctxt)

let inductive_nargs_env env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  (rel_context_length (mib.mind_params_ctxt), mip.mind_nrealargs_ctxt)

let allowed_sorts env (kn,i as ind) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  mip.mind_kelim

(* Annotation for cases *)
let make_case_info env ind style =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let print_info = { ind_nargs = mip.mind_nrealargs_ctxt; style = style } in
  { ci_ind     = ind;
    ci_npar    = mib.mind_nparams;
    ci_cstr_ndecls = mip.mind_consnrealdecls;
    ci_cstr_npdecls = mip.mind_pconsnrealdecls;
    ci_pp_info = print_info }

(*s Useful functions *)

type point_constructor_summary = {
  cs0_cstr : constructor;    (* internal name of the constructor *)
  cs0_params : constr list;  (* parameters of the constructor in current ctx *)
  cs0_nargs : int;           (* length of arguments signature (letin included) *)
  cs0_args : rel_context;    (* signature of the arguments (letin included) *)
  cs0_concl_realargs : constr array; (* actual realargs in the concl of cstr *)
}
type path_constructor_summary = {
  cs1_cstr : constructor;    (* internal name of the constructor *)
  cs1_params : constr list;  (* parameters of the constructor in current ctx *)
  cs1_nargs : int;           (* length of arguments signature (letin included) *)
  cs1_args : rel_context;    (* signature of the arguments (letin included) *)
  cs1_args_info : (rel_context * constr array) option array;
  cs1_inst : constr array;   (* instance of the equation *)
  cs1_lhs : constr;          (* lhs of path *)
  cs1_rhs : constr;          (* rhs of path *)
}
type constructor_summary =
  | Point of point_constructor_summary
  | Path of path_constructor_summary

let lift_point_constructor n cs = {
  cs0_cstr = cs.cs0_cstr;
  cs0_params = List.map (lift n) cs.cs0_params;
  cs0_nargs = cs.cs0_nargs;
  cs0_args = lift_rel_context n cs.cs0_args;
  cs0_concl_realargs = Array.map (liftn n (cs.cs0_nargs+1)) cs.cs0_concl_realargs
}

let map_path_constructor f cs =
  let {c1_args=args;c1_args_info=argsi;c1_inst=inst;c1_lhs=lhs;c1_rhs=rhs} =
    map_pathconstructor f
      {c1_name=id_of_string"_";c1_args=cs.cs1_args;c1_args_info=cs.cs1_args_info;
       c1_inst=cs.cs1_inst;c1_lhs=cs.cs1_lhs;c1_rhs=cs.cs1_rhs} in
  { cs1_cstr = cs.cs1_cstr;
    cs1_params = List.map f cs.cs1_params;
    cs1_nargs = cs.cs1_nargs;
    cs1_args = args;
    cs1_args_info = argsi;
    cs1_inst = inst;
    cs1_lhs = lhs;
    cs1_rhs = rhs }

let lift_path_constructor n cs =
  map_path_constructor (lift n) cs

(* Accept less parameters than in the signature *)

let instantiate_params t args sign =
  let rec inst s t = function
    | ((_,None,_)::ctxt,a::args) ->
	(match kind_of_term t with
	   | Prod(_,_,t) -> inst (a::s) t (ctxt,args)
	   | _ -> anomaly"instantiate_params: type, ctxt and args mismatch")
    | ((_,(Some b),_)::ctxt,args) ->
	(match kind_of_term t with
	   | LetIn(_,_,_,t) -> inst ((substl s b)::s) t (ctxt,args)
	   | _ -> anomaly"instantiate_params: type, ctxt and args mismatch")
    | _, [] -> substl s t
    | _ -> anomaly"instantiate_params: type, ctxt and args mismatch"
  in inst [] t (List.rev sign,args)

let get_constructor (ind,mib,mip,params) j =
  assert (j <= Array.length mip.mind_consnames);
  let typi = mis_nf_constructor_type (ind,mib,mip) j in
  let typi = instantiate_params typi params mib.mind_params_ctxt in
  let (args,ccl) = decompose_prod_assum typi in
  let (_,allargs) = decompose_app ccl in
  let vargs = List.skipn (List.length params) allargs in
  { cs0_cstr = ith_constructor_of_inductive ind j;
    cs0_params = params;
    cs0_nargs = rel_context_length args;
    cs0_args = args;
    cs0_concl_realargs = Array.of_list vargs }

(* copied from inductive.ml. bad! *)
let ind_subst mind mib =
  let ntypes = mib.mind_ntypes in
  let make_Ik k = mkInd (mind,ntypes-k-1) in
  List.tabulate make_Ik ntypes
let cstr_subst ind (mib,mip) params =
  let ncstr0 = Array.length mip.mind_consnames in
  let make_Ck k = mkApp(mkConstruct(ind,ncstr0-k),params) in
  List.tabulate make_Ck ncstr0


let get_path_constructor (ind,mib,mip,params) =
  if Array.length mip.mind_pathcons = 0 then
    fun _ -> assert false
  else
  let vp = Array.of_list params in
  let ipc_subst =
    cstr_subst ind (mib,mip) vp @
      Sign.subst_of_rel_context_args mib.mind_params_ctxt vp @
      ind_subst (fst ind) mib in
  fun j ->
    assert (j <= Array.length mip.mind_pathcons);
    let j' = j+Array.length mip.mind_consnames in
    let pc = map_pathconstructor
      (substl ipc_subst) mip.mind_pathcons.(j-1) in
    { cs1_cstr = ith_constructor_of_inductive ind j';
      cs1_params = params;
      cs1_nargs = rel_context_length pc.c1_args;
      cs1_args = pc.c1_args;
      cs1_args_info = pc.c1_args_info;
      cs1_inst = pc.c1_inst;
      cs1_lhs = pc.c1_lhs;
      cs1_rhs = pc.c1_rhs }

let get_constructors env (ind,params) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let mk_path_cstr = get_path_constructor (ind,mib,mip,params) in
  (Array.init (Array.length mip.mind_consnames)
     (fun j -> get_constructor (ind,mib,mip,params) (j+1)),
   Array.init (Array.length mip.mind_pathcons)
     (fun i -> mk_path_cstr (i+1)))

(* substitution in a signature *)

let substnl_rel_context subst n sign =
  let rec aux n = function
  | d::sign -> substnl_decl subst n d :: aux (n+1) sign
  | [] -> []
  in List.rev (aux n (List.rev sign))

let substl_rel_context subst = substnl_rel_context subst 0

let instantiate_context sign args =
  let rec aux subst = function
  | (_,None,_)::sign, a::args -> aux (a::subst) (sign,args)
  | (_,Some b,_)::sign, args -> aux (substl subst b::subst) (sign,args)
  | [], [] -> subst
  | _ -> anomaly "Signature/instance mismatch in inductive family"
  in aux [] (List.rev sign,args)

let get_arity env (ind,params) =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let parsign =
    (* Dynamically detect if called with an instance of recursively
       uniform parameter only or also of non recursively uniform
       parameters *)
    let parsign = mib.mind_params_ctxt in
    let nnonrecparams = mib.mind_nparams - mib.mind_nparams_rec in
    if Int.equal (List.length params) (rel_context_nhyps parsign - nnonrecparams) then
      snd (List.chop nnonrecparams mib.mind_params_ctxt)
    else
      parsign in
  let arproperlength = List.length mip.mind_arity_ctxt - List.length parsign in
  let arsign,_ = List.chop arproperlength mip.mind_arity_ctxt in
  let subst = instantiate_context parsign params in
  (substl_rel_context subst arsign, Inductive.inductive_sort_family mip)

(* Functions to build standard types related to inductive *)
let build_dependent_constructor cs =
  mkApp(applist(mkConstruct cs.cs0_cstr,
		List.map (lift cs.cs0_nargs) cs.cs0_params),
	Sign.args_of_rel_context 0 cs.cs0_args)

let build_dependent_inductive env ((ind, params) as indf) =
  let arsign,_ = get_arity env indf in
  let nrealargs = List.length arsign in
  mkApp(applist(mkInd ind,List.map (lift nrealargs) params),
	Sign.args_of_rel_context 0 arsign)

(* builds the arity of an elimination predicate in sort [s] *)

let make_arity_signature env dep indf =
  let (arsign,_) = get_arity env indf in
  if dep then
    (* We need names everywhere *)
    name_context env
      ((Anonymous,None,build_dependent_inductive env indf)::arsign)
      (* Costly: would be better to name once for all at definition time *)
  else
    (* No need to enforce names *)
    arsign

let make_arity env dep indf s = mkArity (make_arity_signature env dep indf, s)

(* [p] is the predicate and [cs] a constructor summary *)
let build_branch_type env dep p cs =
  let base = mkApp(lift cs.cs0_nargs p, cs.cs0_concl_realargs) in
  if dep then
    it_mkProd_or_LetIn_name env
      (mkApp(base,[|build_dependent_constructor cs|]))
      cs.cs0_args
  else
    it_mkProd_or_LetIn base cs.cs0_args


let build_path_branch_type ~recu env dep pj cs br =
  let ind = fst cs.cs1_cstr in
  let (_,mip as specif) = Inductive.lookup_mind_specif env ind in
  Inductive.build_path_branch_type ~recu ind specif (Array.of_list cs.cs1_params) pj dep br
    (snd cs.cs1_cstr-Array.length mip.mind_consnames,
     {c1_name=id_of_string"_";c1_args=cs.cs1_args;c1_args_info=cs.cs1_args_info;
      c1_inst=cs.cs1_inst;c1_lhs=cs.cs1_lhs;c1_rhs=cs.cs1_rhs})
let build_path_rec_branch_type env dep pj cs br =
  let ind = fst cs.cs1_cstr in
  let (_,mip as specif) = Inductive.lookup_mind_specif env ind in
  Inductive.build_path_rec_branch_type ind specif (Array.of_list cs.cs1_params) pj dep br
    (snd cs.cs1_cstr-Array.length mip.mind_consnames,
     {c1_name=id_of_string"_";c1_args=cs.cs1_args;c1_args_info=cs.cs1_args_info;
      c1_inst=cs.cs1_inst;c1_lhs=cs.cs1_lhs;c1_rhs=cs.cs1_rhs})

(**************************************************)

let extract_mrectype t =
  let (t, l) = decompose_app t in
  match kind_of_term t with
    | Ind ind -> (ind, l)
    | _ -> raise Not_found

let find_mrectype env sigma c =
  let (t, l) = decompose_app (whd_betadeltaiota env sigma c) in
  match kind_of_term t with
    | Ind ind -> (ind, l)
    | _ -> raise Not_found

let find_rectype env sigma c =
  let (t, l) = decompose_app (whd_betadeltaiota env sigma c) in
  match kind_of_term t with
    | Ind ind ->
        let (mib,mip) = Inductive.lookup_mind_specif env ind in
        let (par,rargs) = List.chop mib.mind_nparams l in
        IndType((ind, par),rargs)
    | _ -> raise Not_found

let find_inductive env sigma c =
  let (t, l) = decompose_app (whd_betadeltaiota env sigma c) in
  match kind_of_term t with
    | Ind ind
        when (fst (Inductive.lookup_mind_specif env ind)).mind_finite ->
        (ind, l)
    | _ -> raise Not_found

let find_coinductive env sigma c =
  let (t, l) = decompose_app (whd_betadeltaiota env sigma c) in
  match kind_of_term t with
    | Ind ind
        when not (fst (Inductive.lookup_mind_specif env ind)).mind_finite ->
        (ind, l)
    | _ -> raise Not_found


(***********************************************)
(* find appropriate names for pattern variables. Useful in the Case
   and Inversion (case_then_using et case_nodep_then_using) tactics. *)

let is_predicate_explicitly_dep env pred arsign =
  let rec srec env pval arsign =
    let pv' = whd_betadeltaiota env Evd.empty pval in
    match kind_of_term pv', arsign with
      | Lambda (na,t,b), (_,None,_)::arsign ->
	  srec (push_rel_assum (na,t) env) b arsign
      | Lambda (na,_,_), _ ->

       (* The following code has an impact on the introduction names
	  given by the tactics "case" and "inversion": when the
	  elimination is not dependent, "case" uses Anonymous for
	  inductive types in Prop and names created by mkProd_name for
	  inductive types in Set/Type while "inversion" uses anonymous
	  for inductive types both in Prop and Set/Type !!

	  Previously, whether names were created or not relied on
	  whether the predicate created in Indrec.make_case_com had a
	  dependent arity or not. To avoid different predicates
	  printed the same in v8, all predicates built in indrec.ml
	  got a dependent arity (Aug 2004). The new way to decide
	  whether names have to be created or not is to use an
	  Anonymous or Named variable to enforce the expected
	  dependency status (of course, Anonymous implies non
	  dependent, but not conversely).

          At the end, this is only to preserve the compatibility: a
          check whether the predicate is actually dependent or not
          would indeed be more natural! *)

          begin match na with
          | Anonymous -> false
          | Name _ -> true
          end

      | _ -> anomaly "Non eta-expanded dep-expanded \"match\" predicate"
  in
  srec env pred arsign

let is_elim_predicate_explicitly_dependent env pred indf =
  let arsign,_ = get_arity env indf in
  is_predicate_explicitly_dep env pred arsign

let set_names env n brty =
  let (ctxt,cl) = decompose_prod_n_assum n brty in
  it_mkProd_or_LetIn_name env cl ctxt

let set_pattern_names env ind brv =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let arities =
    Array.map
      (fun c ->
        rel_context_length ((prod_assum c)) -
        mib.mind_nparams)
      mip.mind_nf_lc in
  Array.map2 (set_names env) arities brv

let type_case_branches_with_names env indspec p c =
  let (ind,args) = indspec in
  let (mib,mip as specif) = Inductive.lookup_mind_specif env ind in
  let nparams = mib.mind_nparams in
  let (params,realargs) = List.chop nparams args in
  let lbrty = Inductive.build_branches_type ind specif params p in
  (* Build case type *)
  let conclty = Reduction.beta_appvect p (Array.of_list (realargs@[c])) in
  (* Adjust names *)
  if is_elim_predicate_explicitly_dependent env p (ind,params) then
    (set_pattern_names env ind lbrty, conclty)
  else (lbrty, conclty)

(* Type of Case predicates *)
let arity_of_case_predicate env (ind,params) dep k =
  let arsign,_ = get_arity env (ind,params) in
  let mind = build_dependent_inductive env (ind,params) in
  let concl = if dep then mkArrow mind (mkSort k) else mkSort k in
  it_mkProd_or_LetIn concl arsign

(***********************************************)
(* Inferring the sort of parameters of a polymorphic inductive type
   knowing the sort of the conclusion *)

(* Compute the inductive argument types: replace the sorts
   that appear in the type of the inductive by the sort of the
   conclusion, and the other ones by fresh universes. *)
let rec instantiate_universes env scl is = function
  | (_,Some _,_ as d)::sign, exp ->
      d :: instantiate_universes env scl is (sign, exp)
  | d::sign, None::exp ->
      d :: instantiate_universes env scl is (sign, exp)
  | (na,None,ty)::sign, Some u::exp ->
      let ctx,_ = Reduction.dest_arity env ty in
      let s =
	(* Does the sort of parameter [u] appear in (or equal)
           the sort of inductive [is] ? *)
        if univ_depends u is then
          scl (* constrained sort: replace by scl *)
        else
          (* unconstriained sort: replace by fresh universe *)
          new_Type_sort() in
      (na,None,mkArity(ctx,s)):: instantiate_universes env scl is (sign, exp)
  | sign, [] -> sign (* Uniform parameters are exhausted *)
  | [], _ -> assert false

(* Does not deal with universes, but only with Set/Type distinction *)
let type_of_inductive_knowing_conclusion env mip conclty =
  match mip.mind_arity with
  | Monomorphic s ->
      s.mind_user_arity
  | Polymorphic ar ->
      let _,scl = Reduction.dest_arity env conclty in
      let ctx = List.rev mip.mind_arity_ctxt in
      let ctx =
        instantiate_universes
          env scl ar.poly_level (ctx,ar.poly_param_levels) in
      mkArity (List.rev ctx,scl)

(***********************************************)
(* Guard condition *)

(* A function which checks that a term well typed verifies both
   syntactic conditions *)

let control_only_guard env c =
  let check_fix_cofix e c = match kind_of_term c with
    | CoFix (_,(_,_,_) as cofix) ->
	Inductive.check_cofix e cofix
    | Fix (_,(_,_,_) as fix) ->
	Inductive.check_fix e fix
    | _ -> ()
  in
  let rec iter env c =
    check_fix_cofix env c;
    iter_constr_with_full_binders push_rel iter env c
  in
  iter env c

let subst_inductive subst (kn,i as ind) =
  let kn' = Mod_subst.subst_ind subst kn in
  if kn == kn' then ind else (kn',i)
