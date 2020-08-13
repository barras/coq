{\rtf1\ansi\ansicpg1252\deff0\nouicompat\deflang1033{\fonttbl{\f0\fnil\fcharset0 Calibri;}{\f1\fnil Calibri;}{\f2\fnil\fcharset238 Calibri;}}
{\colortbl ;\red0\green0\blue255;}
{\*\generator Riched20 10.0.14393}\viewkind4\uc1
\pard\sa200\sl276\slmult1\f0\fs22\lang9 open Pp             (* lib/pp.ml4 *)\par
open Util           (* lib/util.ml *)\par
module N = Names    (* kernel/names.ml *)\par
module No = Nameops (* library/nameops.ml *) \par
module L = Libnames (* library/libnames.ml *)\par
\par
module T = Table\par
open Miniml\par
module MU = Mlutil\par
module C = Common\par
\par
let (!%) = Printf.sprintf\par
let ($) g f x = g (f x)\par
let p = print_endline\par
let slist f xs = String.concat ";" (List.map f xs)\par
let sarray f xs = slist f (Array.to_list xs)\par
let id x = x\par
let list_mapi f = Array.to_list $ Array.mapi f $ Array.of_list\par
let tryo f x = try Some (f x) with _ -> None\par
let string1 = String.make 1\par
let (|>) x f = f x\par
let (--) a b =\par
  let rec iter store a bi =\par
    if a = bi then bi::store\par
    else iter (bi::store) a (bi - 1)\par
  in\par
  if a <= b then iter [] a b\par
  else List.rev (iter [] b a)\par
\par
(* see Scala language specification: {{\field{\*\fldinst{HYPERLINK http://www.scala-lang.org/sites/default/files/linuxsoft_archives/docu/files/ScalaReference.pdf }}{\fldrslt{http://www.scala-lang.org/sites/default/files/linuxsoft_archives/docu/files/ScalaReference.pdf\ul0\cf0}}}}\f0\fs22  *)\par
let keywords =\par
  List.fold_right (fun s -> N.Idset.add (N.id_of_string s))\par
  [ "abstract"; "do"; "finally"; "import"; "object"; "return"; "trait"; "var"; \par
    "_"; "case"; "else"; "for"; "lazy"; "override"; "sealed"; "try"; "while";\par
    "catch"; "extends"; "forSome"; "match"; "package"; "super"; "true"; "with";\par
    "class"; "false"; "if"; "new"; "private"; "this"; "type"; "yield"; "def";\par
    "final"; "implicit"; "null"; "protected"; "throw"; "val"; ]\par
  N.Idset.empty\par
\par
let preamble mod_name used_modules usf = str ""\par
\par
let prarray_with_sep pp f xs = prlist_with_sep pp f (Array.to_list xs)\par
let prlist_with_comma f xs = prlist_with_sep (fun () -> str ", ") f xs\par
let prlist_with_space f xs = prlist_with_sep (fun () -> str " ") f xs\par
\par
let pp_global k r =\par
  if T.is_inline_custom r then str (T.find_custom r)\par
  else str (Common.pp_global k r)\par
\par
let pr_id id =\par
  let s = N.string_of_id id in\par
  let ss = List.map (function | "\\'" -> "$prime" | c -> c) (explode s) in\par
  str (String.concat "" ss)\par
\par
let free_type_vars typ =\par
  let module S = Set.Make(struct type t = int let compare = compare end) in\par
  let rec iter = function\par
    | Tmeta _ | Tvar' _ -> S.empty\par
    | Tvar (i:int) ->  S.singleton i\par
    | Tglob ((r: L.global_reference), (l: ml_type list)) ->\par
\tab List.fold_left (fun store typ ->\par
\tab   S.union store (iter typ)) S.empty l\par
    | Tarr (t1,t2) ->\par
\tab S.union (iter t1) (iter t2)\par
    | Tdummy _\par
    | Tunknown\par
    | Taxiom -> S.empty\par
  in\par
  S.elements (iter typ)\par
\par
let name_of_tvar i =\par
  "T" ^ string_of_int i\par
\par
let name_of_tvar' i =\par
  if 1 <= i && i <= 26 then\par
    string1 (char_of_int (int_of_char 'A' + i - 1))\par
  else\par
    "A" ^ string_of_int i\par
\par
let rec pp_type (tvs:N.identifier list) = function\par
    | Tmeta m -> begin match m.contents with\par
      | Some t -> pp_type tvs t\par
      | None -> str "MetaNone"\par
    end\par
    | Tvar' i -> str (name_of_tvar' i)\par
    | Tvar i ->\par
\tab begin match tryo (List.nth tvs) (i-1) with\par
\tab | Some v -> pr_id v\par
(*\tab | None -> str (name_of_tvar2 i)*)\par
        | None -> str "Any"\par
\tab end\par
    | Tglob ((r: L.global_reference), (l: ml_type list)) ->\par
\tab pp_global C.Type r\par
\tab   ++ if l = [] then mt ()\par
\tab      else str "[" ++ prlist_with_comma (pp_type tvs) l ++ str "]"\par
    | Tarr (t1,t2) ->\par
\tab str "(" ++ pp_type tvs t1 ++ str " => " ++ pp_type tvs t2 ++ str")"\par
    | Tdummy _ -> str "Unit"\par
    | Tunknown -> str "Any"\par
    | Taxiom -> str "Unit // AXIOM TO BE REALIZED" ++ Pp.fnl()\par
\par
let rec pp_expr (tvs: N.identifier list) (env: C.env) : ml_ast -> 'a =\par
  function\par
    | MLrel (i, ts) ->\par
\tab let id = C.get_db_name i env in\par
        let type_annot = if ts = [] then mt()\par
            else str "[" ++ prlist_with_comma (pp_type tvs) ts ++ str "]"\par
        in\par
\tab pr_id id ++ type_annot\par
    | MLapp ((f: ml_ast), (args: ml_ast list)) ->\par
\tab pp_expr tvs env f ++ str "("\par
\tab   ++ prlist_with_sep (fun () -> str ")(") (pp_expr tvs env) args ++ str ")"\par
    | MLlam (_, _, _) as a ->\par
      \tab let fl,a' = MU.collect_lams' a in\par
        let (ids,tys) = List.split fl in\par
\tab let ids',env' = C.push_vars (List.map MU.id_of_mlid ids) env in\par
        let fl' = List.combine ids' tys in\par
        let pp_arg (id,ty) = str "(" ++ pr_id id ++ str ":"\par
            ++ pp_type tvs ty ++ str ") =>"\par
        in\par
\tab str"\{" ++ Pp.fnl()\par
          ++ prlist_with_space pp_arg (List.rev fl') ++ Pp.fnl()\par
          ++ pp_expr tvs env' a' ++ Pp.fnl()\par
          ++ str "\}"\par
    | MLletin ((mlid: ml_ident), (i,mlty), (a1: ml_ast), (a2: ml_ast)) ->\par
\tab let id = MU.id_of_mlid mlid in\par
\tab let (ids', env2) = C.push_vars [id] env in\par
\tab str "\{" ++ Pp.fnl()\par
          ++ local_def' tvs env (List.hd ids') i mlty a1 ++ Pp.fnl()\par
\tab   ++ pp_expr tvs env2 a2 ++ Pp.fnl() ++ str "\}" ++ Pp.fnl()\par
    | MLglob (r, ty_args) ->\par
        let type_annot = if ty_args = [] then mt()\par
          else str"[" ++ prlist_with_comma (pp_type tvs) ty_args ++ str "]"\par
        in\par
        pp_global C.Term r ++ type_annot\par
    | MLcons ((_: constructor_info), (r: L.global_reference), (args: ml_ast list)) ->\par
\tab pp_global C.Cons r ++ str "("\par
\tab   ++ prlist_with_comma (pp_expr tvs env) args ++ str ")"\par
    | MLcase ((_: match_info), (t: ml_ast), (pv: ml_branch array))  ->\par
\tab pp_expr tvs env t ++ str " match \{" ++ Pp.fnl()\par
\tab   ++ prarray_with_sep Pp.fnl (pp_case tvs env) pv\par
\tab   ++ Pp.fnl() ++ str "\}"\par
    | MLfix ((i: int), idtys ,(defs: ml_ast array)) ->\par
        let ids,tys = Array.to_list idtys |> List.split in\par
\tab let ids',env' = C.push_vars (List.rev ids) env in\par
\tab let ids'' = List.rev ids' in\par
\tab let local_defs =\par
\tab   prlist_with_sep Pp.fnl id\par
\tab     (list_map3 (fun id ty def -> local_def' tvs env' id 0 ty def)\par
\tab        ids'' tys (Array.to_list defs))\par
\tab in\par
\tab let body = pr_id (List.nth ids'' i) in\par
\tab str"\{" ++Pp.fnl()++ local_defs ++Pp.fnl()++ body ++ str"\}" ++Pp.fnl()\par
    | MLexn (s: string) -> str ("throw new Exception(\\"" ^s^ "\\")")\par
    | MLdummy -> str "()"\par
    | MLmagic (a, ty) ->\par
\tab str "(" ++ pp_expr tvs env a ++ str ").asInstanceOf[" ++ pp_type tvs ty ++ str"]"\par
    | MLaxiom -> str "() // AXIOM TO BE REALIZED" ++ Pp.fnl()\par
\par
  (*\par
    \'e5\~\'b4\'e5\'90\f1\'88\f0\'e5\f1\'88\'86\f0\'e3\'81\lquote\'e3\'81\'ae\'e4\'b8\'80\'e3\'81\'a4\'e3\'81\'aecase\'e3\'81\'ab\'e3\'81\'a4\'e3\'81\f1\'84\f0\'e3\'81\'a6\par
    name\'e3\'81\'af\'e3\'82\'b3\'e3\f2\u402?\f0\'b3\'e3\'82\'b9\'e3\f2\u402?\f1\'88\f0\'e3\f2\u402?\f0\'a9\'e3\'82\'af\'e3\'82\'bf\'e5\'90\'8d\'e3\'80\'81ids\'e3\'81\'af\'e6\'9d\f2\u376?\f0\'e7\'b8\f1\'9b\f0\'e3\'81\f1\bullet\f0\'e3\'82\f2\u338?\f0\'e3\'82\f1\'8b\f0\'e5\'a4\f1\'89\f0\'e6\f1\bullet\f0\'b0\'e5\'90\'8d\'e3\'81\'ae\'e9\'85\'8d\'e5\f1\'88\emdash\f0\'e3\'80\'81t\'e3\'81\'af\'e5\'bc\'8f\par
   *)\par
and pp_case tvs env ((name,ids,t): ml_branch) =\par
  let (ids, env') = C.push_vars (List.rev_map MU.id_of_mlid ids) env in\par
  str "case " ++ pp_global C.Cons name ++ str "(" ++\par
    prlist_with_comma pr_id (List.rev ids)\par
    ++ str ")" ++ str " => "\par
    ++ pp_expr tvs env' t\par
\par
and local_def tvs env (id: N.identifier) (def: ml_ast) =\par
  str "def " ++ pr_id id ++ str " = " ++ pp_expr tvs env def\par
\par
and local_def' tvs env (id: N.identifier) i (ty: ml_type) (def: ml_ast) =\par
  let new_tvars =\par
    let n = List.length tvs in\par
    if i=0 then []\par
    else (n+1)--(n+i)\par
    |> List.map (N.id_of_string $ name_of_tvar)\par
  in\par
  let tvs' = List.rev new_tvars @ tvs in\par
  let pp_tvars = if new_tvars = [] then mt() else\par
    str "[" ++ prlist_with_comma pr_id new_tvars ++ str "]"\par
  in\par
  str "def " ++ pr_id id ++ pp_tvars ++ str ": " ++ pp_type tvs' ty\par
    ++ str " = " ++ pp_expr tvs' env def\par
\par
let pp_def glob body typ =\par
  let ftvs = free_type_vars typ in\par
  let tvars = if ftvs = [] then mt() else\par
    str "[" ++ prlist_with_comma (str $ name_of_tvar') ftvs ++ str "]"\par
  in\par
  let tvs = List.map (fun i -> N.id_of_string (name_of_tvar' i)) ftvs in\par
  let pbody =\par
    if T.is_custom glob then str (T.find_custom glob)\par
    else pp_expr [] (C.empty_env()) body\par
  in\par
  str "def " ++ pp_global C.Term glob ++ tvars ++ str " : " ++ pp_type tvs typ\par
    ++ str " = " ++ pbody ++ Pp.fnl()\par
\par
let pp_singleton kn packet =\par
  let l = packet.ip_vars in\par
  let l' = List.rev l in\par
  let params = if l = [] then mt ()\par
      else str "[" ++ prlist_with_comma pr_id l ++ str "]"\par
  in\par
  str "type " ++ pp_global C.Type (L.IndRef (kn, 0)) ++ params \par
    ++ str " = " ++ pp_type l' (List.hd packet.ip_types.(0)) ++ fnl()\par
\par
let pp_one_ind (ip: N.inductive) (tvars: N.identifier list)\par
    (cv: ml_type list array) =\par
  let tname = pp_global C.Type (L.IndRef ip) in\par
  let pp_tvars vs =\par
    if vs = [] then mt()\par
    else str "[" ++ prlist_with_comma pr_id vs ++ str "]"\par
  in\par
  let pp_constructor (r,typs) =\par
    str "case class " ++ pp_global C.Cons r ++ pp_tvars tvars ++ str "("\par
      ++ prlist_with_comma\par
        (fun (i, typ) ->\par
\tab   let vname = str "x" ++ int i in\par
\tab   vname ++ str ": " ++ pp_type tvars typ)\par
        (list_mapi (fun i typ -> (i+1,typ)) typs)\par
      ++ str ") extends " ++ tname ++ pp_tvars tvars\par
  in\par
  str "sealed abstract class " ++ tname ++ pp_tvars tvars ++ fnl()\par
    ++ prvect_with_sep Pp.fnl pp_constructor\par
      (Array.mapi (fun j typ -> (L.ConstructRef(ip,j+1), typ)) cv)\par
    \par
\par
let pp_decl : ml_decl -> std_ppcmds = function\par
  | Dind (kn,i) when i.ind_kind = Singleton ->\par
      pp_singleton (N.mind_of_kn kn) i.ind_packets.(0) ++ fnl ()\par
  | Dind ((kn: N.kernel_name), (ind: ml_ind)) ->\par
      let mind = N.mind_of_kn kn in\par
      let rec iter i =\par
\tab if i >= Array.length ind.ind_packets then mt()\par
\tab else\par
\tab   let packet = ind.ind_packets.(i) in\par
\tab   let ip = (mind,i) in\par
\tab   pp_one_ind ip packet.ip_vars packet.ip_types ++ fnl ()\par
\tab     ++ iter (i+1)\par
      in\par
      iter 0\par
  | Dtype ((r:L.global_reference), (l: N.identifier list), (t: ml_type)) ->\par
      if T.is_inline_custom r then mt()\par
      else\par
        let name = pp_global C.Type r in\par
\tab let l = C.rename_tvars keywords l in\par
        let ty_args, def = match tryo T.find_type_custom r with\par
          | Some (ids,s) -> List.map str ids, str s\par
          | None -> List.map pr_id l, pp_type l t\par
        in\par
        let tparams = if ty_args = [] then mt()\par
            else str "[" ++ prlist_with_comma id ty_args ++ str "]"\par
        in\par
        str "type " ++ name ++ tparams ++ str " = " ++ def ++ Pp.fnl()\par
  | Dfix ((rv: L.global_reference array), (defs: ml_ast array), (typs: ml_type array)) ->\par
      let max = Array.length rv in\par
      let rec iter i =\par
\tab if i = max then mt ()\par
\tab else\par
\tab   pp_def rv.(i) defs.(i) typs.(i) ++ iter (i+1)\par
      in\par
      iter 0\par
  | Dterm ((r: L.global_reference), (a: ml_ast), (t: ml_type)) ->\par
      if T.is_inline_custom r then mt ()\par
      else pp_def r a t\par
\par
let rec pp_structure_elem = function\par
  | (l,SEdecl d) -> pp_decl d\par
  | (l,SEmodule m) -> pp_module_expr m.ml_mod_expr\par
  | (l,SEmodtype m) -> mt ()\par
and pp_module_expr = function\par
  | MEstruct (mp,sel) -> str "object CoqModule \{" ++ Pp.fnl()\par
\tab ++ prlist_strict pp_structure_elem sel\par
\tab ++ str "\}" ++ Pp.fnl()\par
  | MEfunctor _ -> mt ()\par
  | MEident _ | MEapply _ -> assert false\par
\par
let pp_struct (sts: ml_structure) =\par
  let pp_sel (mp,sel) =\par
    C.push_visible mp [];\par
    let p =\par
      prlist_strict pp_structure_elem sel\par
    in\par
    C.pop_visible (); p\par
  in\par
  str "object CoqMain \{" ++ Pp.fnl()\par
    ++ prlist_strict pp_sel sts\par
    ++ str "\}" ++ Pp.fnl()\par
\par
\par
let descr = \{\par
  keywords = keywords;\par
  file_suffix = ".scala";\par
  preamble = preamble;\par
  pp_struct = pp_struct;\par
  sig_suffix = None;\par
  sig_preamble = (fun _ _ _ -> mt ());\par
  pp_sig = (fun _ -> mt ());\par
  pp_decl = pp_decl;\par
\}\par
}
 