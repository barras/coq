
(* Beginning of lib defs *)

let array_map_k f v kv =
  let rec fold_k i k =
    if i < 0 then k []
    else f v.(i) (fun vi' -> fold_k (i-1) (fun acc -> k (vi'::acc)))
  in
  fold_k (Array.length v - 1) (fun acc -> kv (Array.of_list acc))

let array_for_all2 f v1 v2 =
  let n = Array.length v1 in
  let rec proc i =
    if i<n then f v1.(i) v2.(i) && proc (i+1)
    else true in
  proc 0

let array_for_all2_k f v1 v2 kb =
  assert (Array.length v1 = Array.length v2);
  let rec fold_k i =
    if i < 0 then kb true
    else
      f v1.(i) v2.(i)
	(fun bi -> if bi then fold_k (i-1) else kb false)
  in
  fold_k (Array.length v1 - 1)

(* End of lib defs *)

(* Terms *)

type lam =
  | Ref of int
  | Cst of string
  | Abs of string*lam
  | App of lam*lam
  | Cstr of int
  | Sw of lam * lam array
  | Fix of int * lam

let app(h,v) = Array.fold_left (fun h a -> App(h,a)) h v
let appl(h,v) = List.fold_left (fun h a -> App(h,a)) h v

(* Substitution: s(i,k) = val of dB i, shifted by k *)
type sub = int -> int -> lam
type lifted_sub = int * sub
let rec sub_rec (k,s as sb) t =
  match t with
  | Ref i -> if i<k then t else s (i-k) k
  | (Cst _ | Cstr _) -> t
  | Abs(x,b) -> Abs(x,sub_rec (k+1,s) b)
  | App(a,b) -> App(sub_rec sb a, sub_rec sb b)
  | Sw(h,b) -> Sw(sub_rec sb h, Array.map (sub_rec sb) b)
  | Fix(n,b) -> Fix(n,sub_rec sb b)

let lft n i k = Ref(n+i+k)		   

let sid = lft 0

let sterm t k =
  if k=0 then t else sub_rec (0,lft k) t
let scons(t,s) i k =
  if i=0 then sterm t k
  else s (i-1) k

let subst v b = sub_rec (0,scons(v,sid)) b;;

(* Stacks *)
		    
type 'a stk_elt =
    Zapp of 'a list
  | Zsw of 'a array
  | Zfix of 'a * 'a list
	       
let zapp(v,stk) =
  match stk with
  | Zapp l::stk' -> Zapp(v::l)::stk'
  | _ -> Zapp[v]::stk
let zappl (l,stk) =
  match l,stk with
    [],_ -> stk
  | _,Zapp l'::stk' -> Zapp (l@l') :: stk'
  | _ -> Zapp l :: stk
let rec (@@) s1 s2 =
  match s1 with
    [] -> s2
  | [Zapp v] -> zappl(v,s2)
  | z::s1 -> z::(s1@@s2)

let rec zip f (t, stk) =
  match stk with
  | [] -> t
  | Zapp args :: stk' -> zip f (appl(t,List.map f args), stk')
  | Zsw b :: stk' -> zip f (Sw(t,Array.map f b), stk')
  | Zfix(fx,par)::stk' -> zip f (App(appl(f fx,List.map f par), t), stk')
  		     
let split_nth_arg stk n =
  let rec proc rpar n stk =
    match (n,stk) with
    | 0, Zapp(v::l)::stk' -> Some(List.rev rpar,v,zappl(l,stk'))
    | n, Zapp(v::l)::stk' -> proc (v::rpar) (n-1) (zappl(l,stk'))
    | _ -> None in
  proc [] n stk

let eq_stk_elt_shape = function
  | Zapp l1, Zapp l2 -> List.length l1=List.length l2
  | Zsw b1, Zsw b2 -> Array.length b1 = Array.length b2
  | Zfix(_,par1), Zfix(_,par2) -> List.length par1=List.length par2
  | _ -> false

let rec eq_stack_shape = function
  | [],[] -> true
  | i1::s1, i2::s2 -> eq_stk_elt_shape(i1,i2) && eq_stack_shape(s1,s2)
  | _ -> false

(* assumes stack shapes match *)
let raw_compare_stacks f s1 s2 =
  let f' t1 t2 = f ((t1,[]), (t2,[])) in
  let cmp_it = function
    | Zapp l1, Zapp l2 -> List.for_all2 f' l1 l2
    | Zsw b1, Zsw b2 -> array_for_all2 f' b1 b2
    | Zfix(fx1,par1),Zfix(fx2,par2) ->
       f' fx1 fx2 && List.for_all2 f' par1 par2
    | _ -> assert false
  in
  let rec cmp_rec = function
      [],[] -> true
    | i1::s1, i2::s2 -> cmp_it (i1,i2) && cmp_rec (s1,s2)
    | _ -> assert false in
  cmp_rec (s1,s2)

let compare_stacks f s1 s2 =
  eq_stack_shape (s1,s2) && raw_compare_stacks f s1 s2

(* Reduction machines *)  

type stack = lam stk_elt list
		    
let rec whd_stack (t,stk as st) =
  match t with
  | App(h,v) -> whd_stack (h, zapp(v,stk))
  | Sw(h,b) -> whd_stack (h, Zsw b::stk)
  | Fix(n,b) ->
     (match split_nth_arg stk n with
      | Some(par,h,stk') -> whd_stack (h, Zfix(t,par)::stk')
      | None -> st)
  | (Ref _ | Cst _ | Cstr _ | Abs _) -> st

(* Type identifying a reduction and the data needed to compute
   its rhs *)
type redex =
  | IotaSw of int * lam list * lam array
  | IotaFix of lam * lam list * int * lam list
  | Beta of string * lam * lam
  | Delta of lam

(* Assumes (t,stk) results from whd_stack *)	       
let reducible env (t,stk) =
  match t,stk with
  | Abs(x,b), Zapp(v::l)::stk' -> Some(Beta(x,b,v),zappl(l, stk'))
  | Cstr i, Zsw b::stk' -> Some(IotaSw(i,[],b),stk')
  | Cstr i, Zapp l::Zsw b::stk' -> Some(IotaSw(i,l,b),stk')
  | Cstr i, Zfix(fx,par)::stk' -> Some(IotaFix(fx,par,i,[]),stk')
  | Cstr i, Zapp l::Zfix(fx,par)::stk' -> Some(IotaFix(fx,par,i,l),stk')
  | Cst x, _ ->
     (match env x with
      | Some def -> Some(Delta def, stk)
      | None -> None)
  | (App _,_ | Sw _,_) -> assert false
  | _ -> None

let reduce (rdx,stk) =
  match rdx with
  | Delta t -> (t, stk)
  | Beta(_,b,v) -> (subst v b, stk)
  | IotaSw(i,par,b) -> (b.(i), zappl(par,stk))
  | IotaFix(Fix(_,b) as fx, par, i, l) ->
     (b, zappl(fx::par, zapp(appl(Cstr i,l), stk)))
  | IotaFix _ -> assert false

(* Head-normal-form (no delta) *)
let rec hnf st =
  let hd = whd_stack st in
  match reducible (fun _ -> None) hd with
    Some rdx -> hnf (reduce rdx)
  | None -> hd
	      
let rec hnf_all env st =
  let hd = whd_stack st in
  match reducible env hd with
    Some rdx -> hnf_all env (reduce rdx)
  | None -> hd

let rec nf env st =
  zip (fun t -> nf env (t,[])) (nf_sub env (hnf_all env st))
and nf_sub env = function
  | Abs(x,b), stk -> (Abs(x, nf env (b,[])), stk)
  | Fix(n,b), stk -> (Fix(n, nf env (b,[])), stk)
  | ((Cstr _|Ref _|Cst _), stk as st) -> st
  | _ -> assert false

(* Conversion algorithms *)

(* Global ref to record where conv found a mismatch *)	   
let init = ((Cst"init",[]),(Cst"init",[]));;
let failure = ref init;;

module Old = struct

let rec conv env (st1,st2) =
  let (t1,s1 as hd1) = hnf st1 in
  let (t2,s2 as hd2) = hnf st2 in
  let fail () = failure := (hd1,hd2); false in
  match t1,t2 with
  | Ref i, Ref j -> i = j && conv_stacks env s1 s2
  | Cstr i, Cstr j -> i = j && conv_stacks env s1 s2
  | Abs(_,u1), Abs(_,u2) ->
     conv_stacks env s1 s2 && conv env ((u1,[]), (u2,[]))
  | Fix(n1,b1),Fix(n2,b2) ->
     n1=n2 && conv_stacks env s1 s2 && conv env ((b1,[]), (b2,[]))
  | Cst c1, Cst c2 when c1=c2 ->
     (match env c1 with
      | Some def1 ->
	 conv_stacks env s1 s2 || conv env (hd1,(def1,s2))
      | None -> conv_stacks env s1 s2)
  | Cst c1, Cst c2 ->
     (match env c2 with
      | Some def2 -> conv env (hd1,(def2,s2))
      | None ->
	 (match env c1 with
	  | Some def1 -> conv env ((def1,s1),hd2)
	  | None -> fail()))
  | Cst c1, _ ->
     (match env c1 with
      | Some def1 -> conv env ((def1,s1),hd2)
      | None -> fail())
  | _, Cst c2 ->
     (match env c2 with
      | Some def2 -> conv env (hd1,(def2,s2))
      | None -> fail())
  | ( App _,_ | Sw _, _
    | _,App _ | _, Sw _) -> assert false
  | _ -> fail()

and conv_stacks env s1 s2 =
  if eq_stack_shape (s1,s2) then raw_compare_stacks (conv env) s1 s2
  else (failure :=((Cst"shape",s1),(Cst"shape",s2)); false)

end


(* Conversion problem classification: only the flex case
   requires a choice to be made *)	 
type conv_status =
  (* both top term constructors are rigid and match *)
  | Rigid of ((lam*stack) * (lam*stack)) list
  (* 2 defined symbols *)
  | Flex of (string*lam) * (string*lam)
  (* defined symbol in the lhs, rigid rhs *)
  | ReduceLeft of string*lam
  (* defined symbol in the rhs, rigid lhs *)
  | ReduceRight of string*lam
  (* top term constructors are rigid and do not match *)
  | Fail

let conv_head env = function
  | Ref i, Ref j -> if i = j then Rigid[] else Fail
  | Cstr i, Cstr j -> if i = j then Rigid[] else Fail
  | Abs(_,u1), Abs(_,u2) -> Rigid[((u1,[]),(u2,[]))]
  | Fix(n1,b1),Fix(n2,b2) ->
     if n1=n2 then Rigid[((b1,[]),(b2,[]))] else Fail
  | Cst c1, Cst c2 ->
     if c1 = c2 then
       match env c1 with
       | Some def -> Flex((c1,def),(c2,def))
       | None -> Rigid[]
     else
       (match env c1, env c2 with
	| Some def1, Some def2 -> Flex((c1,def1),(c2,def2))
	| Some def1, None -> ReduceLeft (c1,def1)
	| None, Some def2 -> ReduceRight (c2,def2)
	| None, None -> Fail)
  | _, Cst c2 ->
    (match env c2 with
    | Some def2 -> ReduceRight (c2,def2)
    | _ -> Fail)
  | Cst c1, _ ->
    (match env c1 with
    | Some def1 -> ReduceLeft (c1,def1)
    | _ -> Fail)
  | ( App _,_ | Sw _, _
    | _,App _ | _, Sw _) -> assert false  
  | _ -> Fail

(* Roughly the same algorithm as above, but more compact
   and abstract. *)	       
let rec conv env (st1,st2) =
  let (t1,s1 as hd1) = hnf st1 in
  let (t2,s2 as hd2) = hnf st2 in
  let fail () = failure := (hd1,hd2); false in
  match conv_head env (t1,t2) with
  | Rigid l ->
      (* Improvement: compare shapes before subterms *)
      if eq_stack_shape(s1,s2) then
	List.for_all (conv env) l &&
	  raw_compare_stacks (conv env) s1 s2
      else (failure :=((Cst"shape",s1),(Cst"shape",s2)); false)
  | Flex((c1,_),(c2,def2)) ->
    if c1=c2 && eq_stack_shape(s1,s2) then
      (* If raw_compare_stacks fails,
	 we could get better idea of what to do *)
      raw_compare_stacks (conv env) s1 s2 || conv env (hd1,(def2,s2))
    else
      (* Here, comparing stack shapes could help... *)
      conv env (hd1,(def2,s2))
  | ReduceLeft (c1,def1) -> conv env ((def1,s1),hd2)
  | ReduceRight (c2,def2) -> conv env (hd1,(def2,s2))
  | Fail -> fail()

module New = struct

(* Result of stack comparison:
   - Match means that both stacks match
     (either by shape for shape_share or also by content for
      compare_stacks_share)
   - Prefix means that one stack is a strict prefix of the other one
     (shapewise).
     (c1,s1@@stk) vs (c2,stk')
     This means that either c1 may consume s1, or c2 may produce s1.
     So the oracle applies.
   - Differ (c1,ds1@@stk1) vs (c2,ds2@@stk2) where
     * stk1 and stk2 have same shape (and their content have *not* been
     compared)
     * ds1 and ds2 differ either by shape or by content of their
     outermost item. 
     Thus c1 or c2 *need* to consume at least resp. ds1 and ds2.
*)
  type stack_match =
  | Match
  | Prefix
  | Differ of ((stack*stack)*(stack*stack))
		  
(* acc1 and acc2 have same shape; s1 and s2 in reverse order *)
  let rec eq_stack_shape_rev (acc1,acc2) = function
    | [],[] -> Match
    | Zapp l1::s1, [Zapp l2] when List.length l2 < List.length l1 ->
      Prefix
    | [Zapp l1], Zapp l2::s2 when List.length l1 < List.length l2 ->
      Prefix
    | i1::s1, i2::s2 ->
      if eq_stk_elt_shape(i1,i2) then
	eq_stack_shape_rev (i1::acc1,i2::acc2) (s1,s2)
      else Differ((List.rev (i1::s1),acc1), (List.rev (i2::s2),acc2))
    (* one stack is a (shape) prefix of the other one: cannot conclude *)
    | s1,s2 -> Prefix

(* Compare stack shapes outside-in *)
  let shape_share (s1,s2) =
    eq_stack_shape_rev ([],[]) (List.rev s1, List.rev s2)


(* if compare_stacks returns false, then cs_fail contains (ds1,ds2,s1',s2')
   s.t. ds1 and ds2 differ in shape or in its last (outermost) item,
   and s1' and s2' have same shape (but haven't been compared by f).
   This means that conversion can succeed only if t1 and t2 eat ds1 and ds2. *)

let raw_compare_stacks_share f s1 s2 =
  let f' t1 t2 = f ((t1,[]), (t2,[])) in
  let rec cmp_it (acc1,acc2) (i1,i2) =
    match i1,i2 with
    | Zapp (v1::l1), Zapp (v2::l2) ->
      if f' v1 v2 then cmp_it (v1::acc1,v2::acc2) (Zapp l1, Zapp l2)
      else Differ(([Zapp(List.rev(v1::acc1))],zappl(l1,[])),
		  ([Zapp(List.rev(v2::acc2))],zappl(l2,[])))
    | Zapp[], Zapp[] -> Match
    | Zsw b1, Zsw b2 ->
      if array_for_all2 f' b1 b2 then Match
      else Differ(([i1],[]),([i2],[]))
    | Zfix(fx1,par1),Zfix(fx2,par2) ->
       if f' fx1 fx2 && List.for_all2 f' par1 par2 then Match
       else Differ(([i1],[]),([i2],[]))
    | _ -> assert false
  in
  let rec cmp_rec (acc1,acc2) = function
      [],[] -> Match
    | i1::s1, i2::s2 ->
       (match cmp_it ([],[]) (i1,i2) with
       | Match -> cmp_rec (i1::acc1,i2::acc2) (s1,s2)
       | Prefix -> assert false
       | Differ((dsi1,si1),(dsi2,si2)) ->
	 Differ((List.rev (dsi1@acc1), si1@@s1),
		(List.rev (dsi2@acc2), si2@@s2)))
    | _ -> assert false in
  assert (shape_share(s1,s2)=Match);
  cmp_rec ([],[]) (s1,s2)

let compare_stacks_share f s1 s2 =
  match shape_share (s1,s2) with
  | Match -> raw_compare_stacks_share f s1 s2
  | st -> st


let rec consume_stack env (t,stk as st) =    
  match reducible env st with
  | Some (_,[] as rdx) -> (* success *)
     true, reduce rdx
  | Some rdx ->
     consume_stack env (whd_stack (reduce rdx))
  | None -> false, st (* failed to "consume" all the stack *)

(*let rec consume_stack env (t,stk as st) =    
  if stk=[] then st (* success *)
  else
    match reducible env st with
    | Some rdx -> consume_stack env (whd_stack (reduce rdx))
    | None -> st (* failed to "eat" all the stack *)
 *)

let is_intro = function
  | (Abs _|Cstr _|Fix _) -> true
  | (Sw _|App _) -> assert false
  | (Ref _| Cst _) -> false

let alt_consume_stack env (t,stk) =
  let it::rstk = List.rev stk in
  let stk = List.rev rstk in
  let (t',stk') = hnf_all env (t,stk) in
  (is_intro t',(t',stk'@@[it]))

let sync_both_stacks env (t1,t2) ((ds1,s1),(ds2,s2)) =
  (* To ensure consume_stack will make progress... *)
  assert (ds1<>[] && ds2<>[]);
  match alt_consume_stack env (t1, ds1),alt_consume_stack env (t2, ds2) with
  | (co1,(t1',ds1')), (co2,(t2',ds2')) when co1||co2 ->
     true, ((t1',ds1'@@s1),(t2',ds2'@@s2))
  | (_,st1), (_,st2) -> false,(st1,st2)

let alt_sync_both_stacks env (t1,t2) ((ds1,s1),(ds2,s2)) =
  (* To ensure consume_stack will make progress... *)
  assert (ds1<>[] && ds2<>[]);
  let (ok2,(t2',ds2' as st2)) = alt_consume_stack env (t2, ds2) in
  if ok2 then (true,((t1,ds1@@s1),(t2',ds2'@@s2)))
  else
    let (ok1,(t1',ds1' as st1)) = alt_consume_stack env (t1, ds1) in
    if ok1 then (true,((t1',ds1'@@s1),(t2,ds2@@s2)))
    else (false,(st1,st2))

let rec conv env (st1,st2) =
  let (t1,s1 as hd1) = hnf st1 in
  let (t2,s2 as hd2) = hnf st2 in
  let fail () = failure := (hd1,hd2); false in
  match conv_head env (t1,t2) with
  | Rigid l ->
      if eq_stack_shape(s1,s2) then
	List.for_all (conv env) l &&
	raw_compare_stacks (conv env) s1 s2
      else fail()
  | Flex((c1,_),(c2,def2)) ->
    let oracle() = conv env (hd1,(def2,s2)) in (* expand c2 *)
    let sync_stacks diff =
      let (ok,st) = alt_sync_both_stacks env (t1,t2) diff in
      if ok then conv env st
      else (failure := st; false) in
    if c1=c2 then
      match shape_share (s1,s2) with
      | Match ->
	(match raw_compare_stacks_share (conv env) s1 s2 with
	| Match -> true
	| Differ diff -> sync_stacks diff
	| Prefix -> assert false) 
      | _ -> oracle()
    else
      oracle()
  | ReduceLeft (c1,def1) -> conv env ((def1,s1),hd2)
  | ReduceRight (c2,def2) -> conv env (hd1,(def2,s2))
  | Fail -> fail()

end
						
(* FTR: Tail-recursive version of older algo (cps) *)

let rec zip_k f (t,stk) k =
  match stk with
  | [] -> k t
  | Zapp(v::args)::stk' ->
     f v (fun v' -> zip_k f (App(t,v), (zappl(args, stk'))) k)
  | Zsw b :: stk' ->
     array_map_k f b (fun b' -> zip_k f (Sw(t,b'), stk') k)
  | Zfix(fx,par)::stk' ->
     zip_k f (fx,[Zapp par]) (fun fx' -> zip_k f (App(fx',t), stk') k)
  | Zapp[]::_ -> assert false			  

let rec compare_stacks_k f s1 s2 kb =
  let f' t1 t2 k = f ((t1,[]), (t2,[])) k in
  let rec cmp_it k = function
    | Zapp[],Zapp[] -> k()
    | Zapp(v1::l1), Zapp(v2::l2) ->
       f' v1 v2 (fun _ -> cmp_it k (Zapp l1, Zapp l2))
    | Zsw b1, Zsw b2 ->
       array_for_all2_k f' b1 b2
	 (fun b -> if b then k()
		   else (failure:=((Cst"",[Zsw b1]),(Cst"",[Zsw b2]));kb false))
    | Zfix(fx1,par1),Zfix(fx2,par2) ->
       f' fx1 fx2 (fun _ -> cmp_it k (Zapp par1, Zapp par2))
    | _ -> assert false
  in
  let rec cmp_rec = function
      [],[] -> failure:=init; kb true
    | i1::s1, i2::s2 -> cmp_it (fun _ -> cmp_rec(s1,s2)) (i1,i2)
    | _ -> assert false in
  if eq_stack_shape (s1,s2) then cmp_rec (s1,s2)
  else (failure:=((Cst"shape",s1),(Cst"shape",s2)); kb false)


let rec conv_k env (st1,st2) k =
  let (t1,s1 as hd1) = hnf st1 in
  let (t2,s2 as hd2) = hnf st2 in
  let fail () = failure := (hd1,hd2); k false in
  match t1,t2 with
  | Ref i, Ref j ->
     if i = j then compare_stacks_k (conv_k env) s1 s2 k else fail()
  | Cstr i, Cstr j ->
     if i = j then compare_stacks_k (conv_k env) s1 s2 k else fail()
  | Abs(_,u1), Abs(_,u2) ->
     compare_stacks_k (conv_k env) s1 s2
	(fun b -> if b then conv_k env ((u1,[]), (u2,[])) k else k false)
  | Fix(n1,b1),Fix(n2,b2) ->
     if n1=n2 then
       compare_stacks_k (conv_k env) s1 s2
	 (fun b -> if b then conv_k env ((b1,[]), (b2,[])) k else k false)
     else fail()
  | Cst c1, Cst c2 when c1=c2 ->
     (match env c1 with
      | Some def1 ->
	 compare_stacks_k (conv_k env) s1 s2
	   (fun b -> if b then k true else conv_k env (hd1,(def1,s2)) k)
      | None -> compare_stacks_k (conv_k env) s1 s2 k)
  | Cst c1, Cst c2 ->
     (match env c2 with
      | Some def2 -> conv_k env (hd1,(def2,s2)) k
      | None ->
	 (match env c1 with
	  | Some def1 -> conv_k env ((def1,s1),hd2) k
	  | None -> fail()))
  | Cst c1, _ ->
     (match env c1 with
      | Some def1 -> conv_k env ((def1,s1),hd2) k
      | None -> fail())
  | _, Cst c2 ->
     (match env c2 with
      | Some def2 -> conv_k env (hd1,(def2,s2)) k
      | None -> fail())
  | ( App _,_ | Sw _, _
    | _,App _ | _, Sw _) -> assert false
  | _ -> fail()
;;
  
let conv_term env t1 t2 = New.conv env ((t1,[]),(t2,[]))

(* Example *)

let rec of_int n z =
  if n>0 then App(Cstr 1,of_int(n-1) z) else z
let ih = Cst "ih"
let g x = App(Cst"G",x)

(* Fixpoint fff n rec :=
     match n with O => ih | S n0 => g (fff n0 (fff n0 rec)) end *)
let fff =
  let v =
    [|ih;
      Abs("n0",g(app(Ref 3,[|Ref 0;app(Ref 3,[|Ref 0;Ref 1|])|])))|] in
  Fix(0,Abs("fff",Abs("n",Abs("rec",Sw(Ref 1,v)))))

let env = function
  | "fff" -> Some fff
  | "Sn" -> Some (App(Cstr 1, Cst"n"))
  | _ -> None

let trm n x = Sw(app(Cst"fff",[|of_int n (Cst"nn");ih|]),[|x|])
(* match fff n ih with _ => x end  =?  match fff n ih with _ => y end *)
let test n = ((trm n (Cst"x"),[]), (trm n (Cst"y"),[]))
let trm2 n x z = Sw(Sw(app(Cst"fff",[|of_int n (Cst"nn");ih|]),[|x|]),[|z|])
let test2 n = ((trm2 n (Cst"x") (Cst"z1"),[]), (trm2 n (Cst"y") (Cst"z2"),[]))

(* fast *)
let _ =
  New.conv env (test 150)
(* slow *)
let _ =
  conv_k env (test 15) (fun b -> b)
(* stack_overflow *)
let _ =
  conv env (test 15)

let _ =
  conv_term
    env
    (Sw(Cst"Sn",[|Cst"a";Cst "b"|]))
    (Sw(Cst"Sn",[|Cst"a'";Cst "b"|]))

(* Example from Peano.v *)

let plus =
  Fix(0,Abs("plus",
	    Abs("n",Abs("m",
			Sw(Ref 1,[|Ref 0;
				   Abs("p",App(Cstr 1,
					       app(Ref 3,[|Ref 0;Ref 1|])))|])))))

let mult =
  Fix(0,Abs("mult",
	    Abs("n",Abs("m",
			Sw(Ref 1,[|Cstr 0;
				   Abs("p",app(Cst"plus",[|
				     Ref 1;
				     app(Ref 3,[|Ref 0;Ref 1|])|]))|])))))

let envpe = function
  | "plus" -> Some plus
  | "mult" -> Some mult
  | _ -> None

let testpe n = app(Cst"mult",[|n;Cstr 0|])

(* test: n*0 convertible to S(n)*0 *)
let _ = New.conv envpe
  ((testpe (Cst"n"),[]), (testpe (App(Cstr 1,Cst"n")),[]));;

(* Wf *)

let fix_F = Fix(0,Abs("Fix_F",Cst"fxb"))

let envwf = function
  | "Fix_F" -> Some fix_F
  | "a" -> Some(Cst "b")
  | _ -> None

let _ = New.conv envwf
  ((App(fix_F,Cst"a"),[]), (App(Cst"Fix_F",Cst"a"),[]))

let (true,it) =
  New.alt_consume_stack (fun _ -> Some(Fix(0,Cst""))) (Cst"fx",[Zapp[Ref 0]])
