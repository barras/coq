(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This module instantiates the structure of generic deBruijn terms to Coq *)

open Util
open Pp
open Names
open Univ
open Esubst

type 'constr kind_of_term =
  | Rel       of int
  | Var       of identifier
  | Meta      of Term.metavariable
  | Evar      of 'constr Term.pexistential
  | Sort      of Term.sorts
  | Cast      of 'constr * Term.cast_kind * 'constr
  | Prod      of name * 'constr * 'constr
  | Lambda    of name * 'constr * 'constr
  | LetIn     of name * 'constr * 'constr * 'constr
  | App       of 'constr * 'constr array
  | Const     of constant
  | Ind       of inductive
  | Construct of constructor
  | Case      of Term.case_info * 'constr * 'constr * 'constr array
  | Fix       of 'constr Term.pfixpoint
  | CoFix     of 'constr Term.pcofixpoint


let map_term f c =
  match c with
    | Term.Rel i -> Rel i
    | Term.Var id -> Var id
    | Term.Meta mv -> Meta mv
    | Term.Evar(ev,args) -> Evar(ev,Array.map f args)
    | Term.Sort s -> Sort s
    | Term.Cast(c,ck,t) -> Cast(f c, ck, f t)
    | Term.Prod(na,a,b) -> Prod(na,f a,f b)
    | Term.Lambda(na,a,b) -> Lambda(na,f a,f b)
    | Term.LetIn(na,a,b,c) -> LetIn(na,f a,f b,f c)
    | Term.App(h,args) -> App(f h, Array.map f args)
    | Term.Const c -> Const c
    | Term.Ind i -> Ind i
    | Term.Construct c -> Construct c
    | Term.Case(ci,p,c,br) -> Case(ci,f p,f c,Array.map f br)
    | Term.Fix(i,(na,ty,b)) -> Fix(i,(na,Array.map f ty, Array.map f b))
    | Term.CoFix(i,(na,ty,b)) -> CoFix(i,(na,Array.map f ty, Array.map f b))


let norm_ind (mi,i) =
  (mind_of_kn (canonical_mind mi), i)

let norm_ci ci =
  { ci with
    Term.ci_ind = norm_ind ci.Term.ci_ind;
    Term.ci_pp_info = {Term.ind_nargs=0;Term.style=Term.RegularStyle }}

let norm_sgn deref nk = function
  | App(f,args) ->
    (match deref f with
      App(f',args') -> App (f',Array.append args' (Array.map nk args))
    | _ -> App(f,Array.map nk args))
  | Cast(c,_,_) -> deref c
  | Prod(_,a,b) -> Prod(Anonymous,nk a, nk b)
  | Lambda(_,a,b) -> Lambda(Anonymous,nk a, nk b)
  | LetIn(_,a,b,c) -> LetIn(Anonymous,nk a, nk b, nk c)
  | Const c -> Const (constant_of_kn (canonical_con c))
  | Ind (mi,i) -> Ind(mind_of_kn (canonical_mind mi), i)
  | Construct ((mi,i),j) -> Construct((mind_of_kn (canonical_mind mi), i),j)
  | Case(ci,p,c,br) -> Case(norm_ci ci, nk p, nk c, Array.map nk br)
  | Fix(fi,(na,ty,bd)) ->
    Fix(fi,(Array.map(fun _->Anonymous)na,
	    Array.map nk ty, Array.map nk bd))
  | CoFix(fi,(na,ty,bd)) ->
    CoFix(fi,(Array.map(fun _->Anonymous)na,
	      Array.map nk ty, Array.map nk bd))
  | (Rel _| Var _|Sort _|Meta _|Evar _ as s) -> s


(* *)

let current_session = ref 0
let get_fresh_key () =
  assert (!current_session <> -1);
  incr current_session;
  !current_session


module SgnMap =
  Map.Make
    (struct type t = int kind_of_term let compare=Pervasives.compare end)


module EnvSgnMap =
  Map.Make
    (struct type t = (name * int option * int) * int 
	    let compare=Pervasives.compare end)


(* Signature maps (term & envs): signatures and keys *not* normalized *)
let key_tab = ref Intmap.empty
let sgn_tab = ref SgnMap.empty
let sgn_env_tab = ref EnvSgnMap.empty
let nil = (-1)

(* Map of canonical repr of a term from arbitrary key *)
let norm_tab = ref Intmap.empty
(* Signature map (and reverse) of *canonical* keys and sgn
   (canonical keys are a subset of keys) *)
let nkey_tab = ref Intmap.empty
let nsgn_tab = ref SgnMap.empty

let nkey k = Intmap.find k !norm_tab
let nsgn k =
  Intmap.find (nkey k) !nkey_tab

let add_nsgn nk nsgn =
  nsgn_tab := SgnMap.add nsgn nk !nsgn_tab;
  nkey_tab := Intmap.add nk nsgn !nkey_tab

let add_sgn k sgn =
  sgn_tab := SgnMap.add sgn k !sgn_tab;
  key_tab := Intmap.add k sgn !key_tab;
  let sgn' = norm_sgn nsgn nkey sgn in
  let nk =
    try
      SgnMap.find sgn' !nsgn_tab
    with Not_found -> (add_nsgn k sgn'; k) in
  norm_tab := Intmap.add k nk !norm_tab

(*let get_alias normt =
  let a = ref Intmap.empty in
  Intmap.iter (fun k nk ->
    if k<>nk then
      try
	a := Intmap.add nk (k::Intmap.find nk !a) !a
      with Not_found ->
	a := Intmap.add nk [k] !a) normt*)
let get_alias normt =
  let a = ref Intmap.empty in
  Intmap.iter (fun k nk ->
    if k<>nk then
      try
	let l = Intmap.find nk !a in
	l := k::!l
      with Not_found ->
	a := Intmap.add nk (ref[k]) !a) normt;
  !a

(* Assumes subterms are already shared, otherwise sign_of_term fails *)
let share_term sgn =
  try SgnMap.find sgn !sgn_tab
  with Not_found ->
    (* if not, allocate a new key associated to this signature *)
    let k = get_fresh_key () in
    add_sgn k sgn;
    k

let rec share t =
  share_term (map_term share t)

let share_cons esgn =
  try EnvSgnMap.find esgn !sgn_env_tab
  with Not_found ->
    (* if not, allocate a new key associated to this signature *)
    let k = get_fresh_key () in
    sgn_env_tab := EnvSgnMap.add esgn k !sgn_env_tab;
    k

let share_env ((na,ob,ty),tle) =
  share_cons ((na,Option.map share ob, share ty),tle)

let rec share_sign ctxt =
  match ctxt with
      [] -> nil
    | d::tl -> share_env (d,share_sign tl)


open Declarations

type histo_item =
| Typing of int * int * int
| Constant of constant * int * int option
| Inductive of string * mutual_inductive * int *
    (identifier * int * (identifier * int) array) array

let histo = ref []

let share_judge env (t,ty) =
  let kenv = share_sign (Environ.rel_context env) in
  let t' = share t in
  let ty' = share ty in
  histo := Typing(kenv,t',ty') :: !histo;
  (kenv,t',ty')

let share_cb env (mp,l) cb =
  let c = make_con mp empty_dirpath l in
  let bd =
    match body_of_constant cb with
      Some t -> Some (force_constr t)
    | _ -> None in
  let ty =
    match cb.const_type with
    | NonPolymorphicType t -> t
    | PolymorphicArity (ctxt,par) ->
      Term.it_mkProd_or_LetIn (Term.Sort (Term.Type par.poly_level)) ctxt in
  histo := Constant (c,share ty,Option.map share bd) :: !histo


let ind_kw mib =
  match mib.mind_record, mib.mind_finite with
  | true, _ -> "Record"
  | false, true -> "Inductive"
  | false, false -> "Coinductive"

let share_one_ind mip =
  let arity =
    match mip.mind_arity with
    | Monomorphic m -> m.mind_user_arity
    | Polymorphic p ->
      Term.it_mkProd_or_LetIn (Term.Sort(Term.Type p.poly_level))
	mip.mind_arity_ctxt in
  let cstrs = Array.mapi
    (fun i c -> (c,share mip.mind_user_lc.(i))) mip.mind_consnames in
  (mip.mind_typename,share arity,cstrs)

let share_ind kn mib =
  Inductive
    (ind_kw mib,kn,share_sign mib.mind_params_ctxt,
     Array.map share_one_ind mib.mind_packets)

let share_mib env (mp,l) mib =
  let kn = make_mind mp empty_dirpath l in
(*  let kn = mind_of_delta res kn in*)
  histo := share_ind kn mib :: !histo


let rec share_module_body env mb =
  match mb.mod_expr with
  | (None|Some (SEBapply _)) -> share_expr env mb.mod_mp mb.mod_type
  | Some e -> share_expr env mb.mod_mp e

and share_expr env mp me =
  match me with
  | SEBstruct sb -> share_struct env mp sb
  | SEBident mp' -> (* alias! *)
    share_module_body env (Environ.lookup_module mp' env)
  | SEBapply _ -> (* compute result *)
    assert false
(*      share_struct env mp mb.mod_type.typ_expr*)
  | SEBfunctor _ -> ()
  | SEBwith _ -> assert false

and share_struct env mp l =
  let share_elem (l,e) =
    match e with
    | SFBconst cb -> share_cb env (mp,l) cb
    | SFBmind mib -> share_mib env (mp,l) mib
    | SFBmodule mb -> share_module_body env mb
    | SFBmodtype _ -> () in
  List.iter share_elem l

(*let lt = ref ([]:Term.constr list)
let share t = lt := t :: !lt

let _ = at_exit (fun _ ->
  let oc = open_out "terms.obj" in
  List.iter (output_value oc) (List.rev !lt);
  close_out oc)
*)

(*
let rec nf env t =
  map_constr_with_binders push_rel nf env t

let share_nf env t =
  share t;
  share (nf env t)
*)
let dump_sgn_map () =
  List.rev (SgnMap.fold (fun k c l -> (k,c)::l) !sgn_tab [])


let string_of_name = function
  | Anonymous -> "_"
  | Name id -> string_of_id id

let output_int oc i = output_string oc (string_of_int i)

let pp_string pp =
  let _ = Format.flush_str_formatter() in
  pp_with Format.str_formatter pp;
  Format.flush_str_formatter ()

let output_term oc f = function
  | Rel i -> output_string oc ("#"^string_of_int i)
  | Var v -> output_string oc ("var "^string_of_id v)
  | Sort (Term.Prop Term.Null) -> output_string oc ("Prop ")
  | Sort (Term.Prop Term.Pos) -> output_string oc ("Set ")
  | Sort (Term.Type u) ->
    output_string oc ("Type "^pp_string (pr_uni u))
  | Cast(c,Term.DEFAULTcast,t) -> 
    (f c; output_string oc " : "; f t)
  | Cast(c,Term.VMcast,t) -> 
    (f c; output_string oc " :vm "; f t)
  | Prod(na,a,b) ->
    output_string oc ("forall "^string_of_name na^" : ");
    f a;
    output_string oc ". ";
    f b
  | Lambda(na,a,b) ->
    output_string oc ("fun "^string_of_name na^" : ");
    f a;
    output_string oc ". ";
    f b
  | LetIn(na,a,b,c) ->
    output_string oc ("let "^string_of_name na^" := ");
    f a;
    output_string oc " : ";
    f b;
    output_string oc " in ";
    f c
  | App(h,args) ->
    output_string oc "@ ";
    f h;
    Array.iter (fun t -> output_string oc " "; f t) args
  | Const c -> output_string oc ("cst "^string_of_con c)
  | Ind (mi,i) ->
    output_string oc ("ind "^string_of_mind mi^"/"^string_of_int i)
  | Construct ((mi,i),j) ->
    output_string oc
      ("constr "^string_of_mind mi^"/"^string_of_int i^"/"^string_of_int j)
  | Case(ci,p,c,br) ->
    output_string oc "match ";
    f c;
    output_string oc " return ";
    f p; 
    output_string oc " with";
    Array.iter (fun t -> output_string oc " "; f t) br;
    output_string oc " end"
  | Fix ((_,i),(na,ty,bd)) ->
    output_string oc ("fix "^string_of_name na.(i));
    for i = 0 to Array.length na - 1 do
      output_string oc (" ("^string_of_name na.(i)^" : ");
      f ty.(i);
      output_string oc " := ";
      f bd.(i);
      output_string oc (")")
    done
  | CoFix (i,(na,ty,bd)) ->
    output_string oc ("cofix "^string_of_name na.(i));
    for i = 0 to Array.length na - 1 do
      output_string oc (" ("^string_of_name na.(i)^" : ");
      f ty.(i);
      output_string oc " := ";
      f bd.(i);
      output_string oc (")")
    done
  | (Meta _|Evar _) -> assert false

let hfile = ref "histo"

let output_one_ind oc i (id,ar,lc) =
  if i > 0 then output_string oc " with ";
  output_string oc (string_of_id id ^ " : ");
  output_int oc ar;
  output_string oc " := ";
  Array.iter (fun (c,ty) ->
    output_string oc (" | "^string_of_id c^" : ");
    output_int oc ty) lc

let dump_histo h =
  let oc = open_out (!hfile^".obj") in
  output_value oc h;
  close_out oc;
  let oc = open_out (!hfile^".txt") in
  List.iter (fun i ->
    match i with
    | Typing (e,t,ty) ->
      output_string oc "Typing\t";
      output_int oc e;
      output_string oc "\t";
      output_int oc t;
      output_string oc " : ";
      output_int oc ty;
      output_string oc "\n"
    | Constant(c,ty,bd) ->
      output_string oc ("Definition "^string_of_con c);
      output_string oc " : ";
      output_int oc ty;
      (match bd with
      | Some b -> output_string oc " := "; output_int oc b
      | _ -> ());
      output_string oc "\n"
    | Inductive(kw,mi,par,lind) ->
      output_string oc (kw^"("^string_of_mind mi^" ");
      output_int oc par;
      output_string oc (") ");
      Array.mapi (output_one_ind oc) lind;
      output_string oc "\n") h;
  close_out oc

let dump_txt f tbl etbl =
  let oc = open_out f in
  SgnMap.iter (fun sgn k ->
    output_int oc k;
    output_string oc " := ";
    output_term oc (output_int oc) sgn;
    output_string oc "\n")
    tbl;
  output_string oc "\n";
  output_string oc "ENV";
  output_string oc "\n";
  EnvSgnMap.iter (fun ((na,ob,ty),tle) k ->
    output_int oc k;
    output_string oc (" := decl "^string_of_name na);
    (match ob with
	Some d -> output_string oc " := "; output_int oc d
      | None -> ());
    output_string oc " : ";
    output_int oc ty;
    output_string oc " ; ";
    output_int oc tle;
    output_string oc "\n")
    etbl;
  close_out oc

let dump_txt_alias f (tbl,alias) =
  let oc = open_out f in
  SgnMap.iter (fun sgn k ->
    let kl = try List.rev !(Intmap.find k alias) with Not_found -> [] in
    List.iter (fun k -> output_int oc k; output_string oc " ") (k::kl);
    output_string oc ":= ";
    output_term oc (output_int oc) sgn;
    output_string oc "\n")
    tbl;
  close_out oc

let shfile = ref "sharing"
let normfile = ref "normsharing"

let dump_sharing () =
  prerr_endline ("TOTAL NUMBER OF SUBTERMS : "^string_of_int !current_session);
  let oc = open_out (!shfile^".obj") in
  output_value oc !sgn_tab;
  output_value oc !sgn_env_tab;
  close_out oc;
  dump_txt (!shfile^".txt") !sgn_tab !sgn_env_tab;
  prerr_endline ("Wrote "^ !shfile ^".txt")

let dump_norm () =
  let oc = open_out (!normfile^".obj") in
  output_value oc !norm_tab;
  output_value oc !nsgn_tab;
  output_value oc !nkey_tab;
  close_out oc;
  dump_txt_alias (!normfile^".txt") (!nsgn_tab,get_alias !norm_tab)

let load_sharing () =
  let ic = open_in (!shfile^".obj") in
  let (sgn:int SgnMap.t) = input_value ic in
  let (esgn:int EnvSgnMap.t) = input_value ic in
  close_in ic;
  prerr_endline "input file read";
  sgn_tab := sgn;
  sgn_env_tab := esgn

let load_norm () =
  let ic = open_in (!normfile^".obj") in
  let (norm:int Intmap.t) = input_value ic in
  let (nsgn:int SgnMap.t) = input_value ic in
  let (nkey:int kind_of_term Intmap.t) = input_value ic in
  close_in ic;
  prerr_endline "input file read";
  norm_tab := norm;
  nsgn_tab := nsgn;
  nkey_tab := nkey

(*
let redump () =
  let ic = open_in "sharing.obj" in
  let (sgn:int SgnMap.t) = input_value ic in
  close_in ic;
  dump_txt "resharing.txt" sgn
let _=redump()
*)

let reverse_table tbl =
  SgnMap.fold (fun s k l -> Intmap.add k s l) tbl Intmap.empty

(*
let count_redexes sgnm =
  let beta = ref 0 in
  let iota = ref 0 in
  let rtbl = reverse_table sgnm in
  SgnMap.iter (fun sgn k ->
    match sgn with
	App(f,args) ->
	  (match Intmap.find rtbl f with
	      Lambda _ -> incr beta
	    | _ -> ())
      | _ -> ()) sgnm;
  !beta
*)

(* rtbl: reverse signature table (key -> sgn) *)
let norm_sign rtbl =
  (* new signature table *)
  let tbl = ref SgnMap.empty in
  (* new reverse signature (domain is the same as rtbl) *)
  let nktab = ref Intmap.empty in
  (* deref also works for non canonical keys, but output is canonical *)
  let deref k = Intmap.find k !nktab in
  (* normalizes key *)
  let nk k = SgnMap.find (deref k) !tbl in
  (* Alias table *)
  let cont = ref Intmap.empty in
  Intmap.iter (fun k sgn ->
    let sgn' = norm_sgn deref nk sgn in
    nktab := Intmap.add k sgn' !nktab;
    try
      let r = Intmap.find (SgnMap.find sgn' !tbl) !cont in
      r := k :: !r
    with Not_found ->
      tbl := SgnMap.add sgn' k !tbl;
      cont := Intmap.add k (ref []) !cont) rtbl;
  !tbl, !cont

(* manque env tbl *)
let compute_norm () =
(*  let rtbl = reverse_table !sgn_tab in
  prerr_endline "signature table reversed";*)
  let (ntbl,alias) = norm_sign !key_tab in
  prerr_endline "signature table normalized";
  dump_txt_alias (!normfile^".txt") (ntbl,alias)


let redump_norm () =
  load_sharing();
  compute_norm()

let top = ref false

let dump_all () =
  if not !top then begin
    dump_sharing();
    dump_norm();
    dump_histo (List.rev !histo);
(*  compute_norm ()*)
  end

let _ = at_exit dump_all

(*let _ = redump_norm()*)
(*
open Vo

let load_vo () =
  let t1 = System.get_time() in
  List.iter (fun f ->
    let ic = open_in f in
    let i = input_binary_int ic in
    let v = input_value ic in
    close_in ic) all_vo;
  let t2 = System.get_time() in
  prerr_endline "marshal_in:";
  Pp.msgnl (System.fmt_time_difference t1 t2);
  let t1 = System.get_time() in
  List.iter (fun f ->
    let ic = open_in f in
    let i = input_binary_int ic in
    let v = Marshalin.input_value ic in
    close_in ic) all_vo;
  let t2 = System.get_time() in
  prerr_endline "myinput_value:";
  Pp.msgnl (System.fmt_time_difference t1 t2)
*)
(*
let _ = load_vo()
*)
