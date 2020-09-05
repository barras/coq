open Pp             (* lib/pp.ml4 *)
open Util           (* lib/util.ml *)
module No = Nameops (* library/nameops.ml *)
module L = Libnames (* library/libnames.ml *)
open Names (* kernel/names.ml *)

(*

TODO Unit testing
Implement a similar unit test for Scala extraction https://github.com/coq/coq/blob/master/test-suite/success/extraction.v
Modify the compile function to provide Scala support for the Extract TestCompile command
See in https://github.com/coq/coq/blob/master/plugins/extraction/extract_env.ml#L700

*)



module T = Table
open Miniml
module MU = Mlutil
module C = Common

let (!%) = Printf.sprintf
let ($) g f x = g (f x)
let p = print_endline
let slist f xs = String.concat ";" (List.map f xs)
let sarray f xs = slist f (Array.to_list xs)
let id x = x
let list_mapi f = Array.to_list $ Array.mapi f $ Array.of_list
let tryo f x = try Some (f x) with _ -> None
let string1 = String.make 1
let (|>) x f = f x
let (--) a b =
  let rec iter store a bi =
    if a = bi then bi::store
    else iter (bi::store) a (bi - 1)
  in
  if a <= b then iter [] a b
  else List.rev (iter [] b a)

(* see Scala language specification: {{field{*fldinst{HYPERLINK http://www.scala-lang.org/sites/default/files/linuxsoft_archives/docu/files/ScalaReference.pdf }}{\fldrslt{http://www.scala-lang.org/sites/default/files/linuxsoft_archives/docu/files/ScalaReference.pdf\ul0\cf0}}}}\f0\fs22  *)
let keywords =
  List.fold_right (fun s -> Id.Set.add (Id.of_string s))
  [ "abstract"; "do"; "finally"; "import"; "object"; "return"; "trait"; "var";
    "_"; "case"; "else"; "for"; "lazy"; "override"; "sealed"; "try"; "while";
    "catch"; "extends"; "forSome"; "match"; "package"; "super"; "true"; "with";
    "class"; "false"; "if"; "new"; "private"; "this"; "type"; "yield"; "def";
    "final"; "implicit"; "null"; "protected"; "throw"; "val"; ]
  Id.Set.empty

let preamble mod_name used_modules usf _ = str ""

let prarray_with_sep pp f xs = prlist_with_sep pp f (Array.to_list xs)
let prlist_with_comma f xs = prlist_with_sep (fun () -> str ", ") f xs
let prlist_with_space f xs = prlist_with_sep (fun () -> str " ") f xs

let pp_global k r =
  if T.is_inline_custom r then str (T.find_custom r)
  else str (Common.pp_global k r)

let pr_id id =
  let s = Id.to_string id in
  str Str.(global_replace (regexp "'") "$prime" s)

let free_type_vars typ =
  let module S = Set.Make(struct type t = int let compare = compare end) in
  let rec iter = function
    | Tmeta _ | Tvar' _ -> S.empty
    | Tvar (i:int) ->  S.singleton i
    | Tglob (r, l) ->
 List.fold_left (fun store typ ->
   S.union store (iter typ)) S.empty l
    | Tarr (t1,t2) ->
 S.union (iter t1) (iter t2)
    | Tdummy _
    | Tunknown
    | Taxiom -> S.empty
  in
  S.elements (iter typ)

let name_of_tvar i =
  "T" ^ string_of_int i

let name_of_tvar' i =
  if 1 <= i && i <= 26 then
    string1 (char_of_int (int_of_char 'A' + i - 1))
  else
    "A" ^ string_of_int i

let rec pp_type (tvs:Id.t list) = function
    | Tmeta m -> begin match m.contents with
      | Some t -> pp_type tvs t
      | None -> str "MetaNone"
    end
    | Tvar' i -> str (name_of_tvar' i)
    | Tvar i ->
 begin match tryo (List.nth tvs) (i-1) with
 | Some v -> pr_id v
(* | None -> str (name_of_tvar2 i)*)
        | None -> str "Any"
 end
    | Tglob (r, l) ->
 pp_global C.Type r
   ++ if l = [] then mt ()
      else str "[" ++ prlist_with_comma (pp_type tvs) l ++ str "]"
    | Tarr (t1,t2) ->
 str "(" ++ pp_type tvs t1 ++ str " => " ++ pp_type tvs t2 ++ str")"
    | Tdummy _ -> str "Unit"
    | Tunknown -> str "Any"
    | Taxiom -> str "Unit // AXIOM TO BE REALIZED" ++ Pp.fnl()

let rec pp_expr (tvs: Id.t list) (env: C.env)  : ml_ast -> 'a =
  function
    | MLrel (i, ts) ->
 let id = C.get_db_name i env in
        let type_annot = if ts = [] then mt()
            else str "[" ++ prlist_with_comma (pp_type tvs) ts ++ str "]"
        in
 pr_id id ++ type_annot
    | MLapp ((f: ml_ast), (args: ml_ast list)) ->
 pp_expr tvs env f ++ str "("
   ++ prlist_with_sep (fun () -> str ")(") (pp_expr tvs env) args ++ str ")"
    | MLlam (_, _, _) as a ->
       let fl,a' = MU.collect_lams' a in
        let (ids,tys) = List.split fl in
 let ids',env' = C.push_vars (List.map MU.id_of_mlid ids) env in
        let fl' = List.combine ids' tys in
        let pp_arg (id,ty) = str "(" ++ pr_id id ++ str ":"
            ++ pp_type tvs ty ++ str ") =>"
        in
          prlist_with_space pp_arg (List.rev fl') ++ Pp.fnl()
          ++ str"{" ++ Pp.fnl()
          ++ pp_expr tvs env' a' ++ Pp.fnl()
          ++ str "}"
    | MLletin ((mlid: ml_ident), (i,mlty), (a1: ml_ast), (a2: ml_ast)) ->
 let id = MU.id_of_mlid mlid in
 let (ids', env2) = C.push_vars [id] env in
 str "{" ++ Pp.fnl()
          ++ local_def' tvs env (List.hd ids') i mlty a1 ++ str ";" ++ Pp.fnl()
   ++ pp_expr tvs env2 a2 ++ Pp.fnl() ++ str "}" ++ Pp.fnl()
    | MLglob (r, ty_args) ->
        let type_annot = if ty_args = [] then mt()
          else str"[" ++ prlist_with_comma (pp_type tvs) ty_args ++ str "]"
        in
        pp_global C.Term r ++ type_annot
    | MLcons (_, r, args) ->
 pp_global C.Cons r ++ str "("
   ++ prlist_with_comma (pp_expr tvs env) args ++ str ")"
    | MLcase (_, t, pv)  ->
 pp_expr tvs env t ++ str " match {" ++ Pp.fnl()
   ++ prarray_with_sep Pp.fnl (pp_case tvs env) pv
   ++ Pp.fnl() ++ str "}"
    | MLfix ((i: int), idtys ,(defs: ml_ast array)) ->
        let ids,tys = Array.to_list idtys |> List.split in
 let ids',env' = C.push_vars (List.rev ids) env in
 let ids'' = List.rev ids' in
 let local_defs =
   prlist_with_sep Pp.fnl id
     (List.map3 (fun id ty def -> local_def' tvs env' id 0 ty def)
        ids'' tys (Array.to_list defs))
 in
 let body = pr_id (List.nth ids'' i) in
 str"{" ++Pp.fnl()++ local_defs ++Pp.fnl()++ body ++ str"}" ++Pp.fnl()
    | MLexn (s: string) -> str ("throw new Exception(\"" ^s^ "\")")
    | MLdummy _ -> str "()"
    | MLmagic (a, ty) ->
 str "(" ++ pp_expr tvs env a ++ str ").asInstanceOf[" ++ pp_type tvs ty ++ str"]"
    | MLaxiom -> str "() // AXIOM TO BE REALIZED" ++ Pp.fnl()

  (*
    \'e5\~\'b4\'e5\'90\f1\'88\f0\'e5\f1\'88\'86\f0\'e3\'81\lquote\'e3\'81\'ae\'e4\'b8\'80\'e3\'81\'a4\'e3\'81\'aecase\'e3\'81\'ab\'e3\'81\'a4\'e3\'81\f1\'84\f0\'e3\'81\'a6
    name\'e3\'81\'af\'e3\'82\'b3\'e3\f2\u402?\f0\'b3\'e3\'82\'b9\'e3\f2\u402?\f1\'88\f0\'e3\f2\u402?\f0\'a9\'e3\'82\'af\'e3\'82\'bf\'e5\'90\'8d\'e3\'80\'81ids\'e3\'81\'af\'e6\'9d\f2\u376?\f0\'e7\'b8\f1\'9b\f0\'e3\'81\f1\bullet\f0\'e3\'82\f2\u338?\f0\'e3\'82\f1\'8b\f0\'e5\'a4\f1\'89\f0\'e6\f1\bullet\f0\'b0\'e5\'90\'8d\'e3\'81\'ae\'e9\'85\'8d\'e5\f1\'88\emdash\f0\'e3\'80\'81t\'e3\'81\'af\'e5\'bc\'8f
   *)

and pp_cons_pat r ppl =
    pp_global C.Cons r ++ str "(" ++ prlist_with_comma identity ppl ++ str ")"

and pp_gen_pat ids env = function
  | Pcons (r, l) -> pp_cons_pat r (List.map (pp_gen_pat ids env) l)
  | Pusual r -> pp_cons_pat r (List.map pr_id ids)
  | Ptuple l -> str "(" ++ prlist_with_comma (pp_gen_pat ids env) l ++ str ")"
  | Pwild -> str "_"
  | Prel n -> pr_id (C.get_db_name n env)

and pp_case tvs env ((ids, p,t): ml_branch) = (* TODO fix pattern translation  *)
  let ids, env' = C.push_vars (List.rev_map MU.id_of_mlid ids) env in
  str "case " ++ (pp_gen_pat (List.rev ids) env' p) ++ str " => "
    ++ pp_expr tvs env' t

and local_def tvs env (id: Id.t) (def: ml_ast) =
  str "def " ++ pr_id id ++ str " = " ++ pp_expr tvs env def

and local_def' tvs env (id: Id.t) i (ty: ml_type) (def: ml_ast) =
  let new_tvars =
    let n = List.length tvs in
    if i=0 then []
    else (n+1)--(n+i)
    |> List.map (Id.of_string $ name_of_tvar)
  in
  let tvs' = List.rev new_tvars @ tvs in
  let pp_tvars = if new_tvars = [] then mt() else
    str "[" ++ prlist_with_comma pr_id new_tvars ++ str "]"
  in
  str "def " ++ pr_id id ++ pp_tvars ++ str ": " ++ pp_type tvs' ty
    ++ str " = " ++ pp_expr tvs' env def

let pp_def glob body typ =
  let ftvs = free_type_vars typ in
  let tvars = if ftvs = [] then mt() else
    str "[" ++ prlist_with_comma (str $ name_of_tvar') ftvs ++ str "]"
  in
  let tvs = List.map (fun i -> Id.of_string (name_of_tvar' i)) ftvs in
  let pbody =
    if T.is_custom glob then str (T.find_custom glob)
    else pp_expr [] (C.empty_env()) body
  in
  str "def " ++ pp_global C.Term glob ++ tvars ++ str " : " ++ pp_type tvs typ
    ++ str " = " ++ pbody ++ Pp.fnl()

let pp_singleton kn packet =
  let l = packet.ip_vars in
  let l' = List.rev l in
  let params = if l = [] then mt ()
      else str "[" ++ prlist_with_comma pr_id l ++ str "]"
  in
  str "type " ++ pp_global C.Type (GlobRef.IndRef (kn, 0)) ++ params
    ++ str " = " ++ pp_type l' (List.hd packet.ip_types.(0)) ++ fnl()

let pp_one_ind (ip: inductive) (tvars: Id.t list)
    (cv: ml_type list array) =
  let tname = pp_global C.Type (GlobRef.IndRef ip) in
  let pp_tvars vs =
    if vs = [] then mt()
    else str "[" ++ prlist_with_comma pr_id vs ++ str "]"
  in
  let pp_constructor (r,typs) =
    str "case class " ++ pp_global C.Cons r ++ pp_tvars tvars ++ str "("
      ++ prlist_with_comma
        (fun (i, typ) ->
   let vname = str "x" ++ int i in
   vname ++ str ": " ++ pp_type tvars typ)
        (list_mapi (fun i typ -> (i+1,typ)) typs)
      ++ str ") extends " ++ tname ++ pp_tvars tvars
  in
  str "sealed abstract class " ++ tname ++ pp_tvars tvars ++ fnl()
    ++ prvect_with_sep Pp.fnl pp_constructor
      (Array.mapi (fun j typ -> (GlobRef.ConstructRef(ip,j+1), typ)) cv)


let pp_decl = function
  | Dind (kn,i) when i.ind_kind = Singleton ->
      pp_singleton kn i.ind_packets.(0) ++ fnl ()
  | Dind (kn, ind) ->
      let mind = kn in
      let rec iter i =
 if i >= Array.length ind.ind_packets then mt()
 else
   let packet = ind.ind_packets.(i) in
   let ip = (mind,i) in
   pp_one_ind ip packet.ip_vars packet.ip_types ++ fnl ()
     ++ iter (i+1)
      in
      iter 0
  | Dtype (r, l, t) ->
      if T.is_inline_custom r then mt()
      else
        let name = pp_global C.Type r in
 let l = C.rename_tvars keywords l in
        let ty_args, def = match tryo T.find_type_custom r with
          | Some (ids,s) -> List.map str ids, str s
          | None -> List.map pr_id l, pp_type l t
        in
        let tparams = if ty_args = [] then mt()
            else str "[" ++ prlist_with_comma id ty_args ++ str "]"
        in
        str "type " ++ name ++ tparams ++ str " = " ++ def ++ Pp.fnl()
  | Dfix (rv, defs, typs) ->
      let max = Array.length rv in
      let rec iter i =
 if i = max then mt ()
 else
   pp_def rv.(i) defs.(i) typs.(i) ++ iter (i+1)
      in
      iter 0
  | Dterm (r, a, t) ->
      if T.is_inline_custom r then mt ()
      else pp_def r a t

let rec pp_structure_elem = function
  | (l,SEdecl d) -> pp_decl d
  | (l,SEmodule m) -> pp_module_expr m.ml_mod_expr
  | (l,SEmodtype m) -> mt ()
and pp_module_expr = function
  | MEstruct (mp,sel) -> (*
  TODO find a better translation for Coq Modules
str "object CoqModule {" ++ Pp.fnl()
 ++*) prlist_strict pp_structure_elem sel
 (*++ str "}" ++ Pp.fnl()*)
  | MEfunctor _ -> mt ()
  | MEident _ | MEapply _ -> assert false

let pp_struct (sts: ml_structure) =
  let pp_sel (mp,sel) =
    C.push_visible mp [];
    let p =
      prlist_strict pp_structure_elem sel
    in
    C.pop_visible (); p
  in
  str "object CoqMain {" ++ Pp.fnl()
    ++ prlist_strict pp_sel sts
    ++ str "}" ++ Pp.fnl()

let scala_descr = {
  keywords = keywords;
  file_suffix = ".scala";
  file_naming = T.file_of_modfile;
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ _ -> mt ());
  pp_sig = (fun _ -> mt ());
  pp_decl = pp_decl;
}
