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

(*
  let rec norm = function
    | App(f,args) ->
      (match norm (deref f) with
	App(f',args') -> App (f',args'@Array.map norm args)
      | f' -> App(f',Array.map norm args))
    | Cast(c,_,_) -> norm (deref c)
    | Prod(_,a,b) -> Prod(Anonymous,norm a, norm b)
    | Lambda(_,a,b) -> Lambda(Anonymous,norm a, norm b)
    | LetIn(_,a,b,c) -> LetIn(Anonymous,norm a, norm b, norm c)
    | Const c -> Const (constant_of_kn (canonical_con c))
    | Ind (mi,i) -> Ind(mind_of_kn (canonical_mind mi), i)
    | Construct ((mi,i),j) -> Construct((mind_of_kn (canonical_mind mi), i),j)
    | Case(ci,p,c,br) -> Case(norm_ci ci, norm p, norm c, Array.map norm br)
    | Fix(fi,(na,ty,bd)) ->
      Fix(fi,(Array.map(fun _->Anonymous)na,
	      Array.map norm ty, Array.map norm bd))
    | CoFix(fi,(na,ty,bd)) ->
      CoFix(fi,(Array.map(fun _->Anonymous)na,
		Array.map norm ty, Array.map norm bd))
    | (Rel _| Var _|Sort _|Meta _|Evar _ as s) -> s
*)

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
let norm_ind (mi,i) =
  (mind_of_kn (canonical_mind mi), i)

let norm_ci ci =
  { ci with
    Term.ci_ind = norm_ind ci.Term.ci_ind;
    Term.ci_pp_info = {Term.ind_nargs=0;Term.style=Term.RegularStyle }}

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
  let norm = function
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
    | (Rel _| Var _|Sort _|Meta _|Evar _ as s) -> s in
  (* Alias table *)
  let cont = ref Intmap.empty in
  Intmap.iter (fun k sgn ->
    let sgn' = norm sgn in
    nktab := Intmap.add k sgn' !nktab;
    try
      let r = Intmap.find (SgnMap.find sgn' !tbl) !cont in
      r := k :: !r
    with Not_found ->
      tbl := SgnMap.add sgn' k !tbl;
      cont := Intmap.add k (ref []) !cont) rtbl;
  !tbl, !cont

let sgn_tab = ref SgnMap.empty
let sgn_env_tab = ref EnvSgnMap.empty
let nil = (-1)

(* Assumes subterms are already shared, otherwise sign_of_term fails *)
let share_term sgn =
  try SgnMap.find sgn !sgn_tab
  with Not_found ->
    (* if not, allocate a new key associated to this signature *)
    let k = get_fresh_key () in
    sgn_tab := SgnMap.add sgn k !sgn_tab;
    k

let rec share t =
  prerr_string ".";
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
    output_int oc ty)
    etbl;
  close_out oc

let dump_txt_alias f (tbl,alias) =
  let oc = open_out f in
  SgnMap.iter (fun sgn k ->
    let kl = k :: List.rev !(Intmap.find k alias) in
    List.iter (fun k -> output_int oc k; output_string oc " ") kl;
    output_string oc ":= ";
    output_term oc (output_int oc) sgn;
    output_string oc "\n")
    tbl;
  close_out oc


let dump_sharing () =
  prerr_endline ("TOTAL NUMBER OF SUBTERMS : "^string_of_int !current_session);
  let oc = open_out "sharing.obj" in
  output_value oc !sgn_tab;
  output_value oc !sgn_env_tab;
  close_out oc;
  dump_txt "sharing.txt" !sgn_tab !sgn_env_tab;
  prerr_endline "Wrote sharing.txt"

let load_sharing () =
  let ic = open_in "sharing.obj" in
  let (sgn:int SgnMap.t) = input_value ic in
  let (esgn:int EnvSgnMap.t) = input_value ic in
  close_in ic;
  prerr_endline "input file read";
  sgn_tab := sgn;
  sgn_env_tab := esgn

(*
let redump () =
  let ic = open_in "sharing.obj" in
  let (sgn:int SgnMap.t) = input_value ic in
  close_in ic;
  dump_txt "resharing.txt" sgn
let _=redump()
*)

(* manque env tbl *)
let compute_norm () =
  let rtbl = reverse_table !sgn_tab in
  prerr_endline "signature table reversed";
  let (ntbl,alias) = norm_sign rtbl in
  prerr_endline "signature table normalized";
  dump_txt_alias "normsharing.txt" (ntbl,alias)


let redump_norm () =
  load_sharing();
  compute_norm()

let dump_all () =
  dump_sharing();
  compute_norm ()

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
