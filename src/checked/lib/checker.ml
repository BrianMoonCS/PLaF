(* Names: Adib Osmany, Brian Moon
   Pledge: I pledge my honor that I have abided by the Stevens Honor System*)
open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser
       
let rec chk_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error
         "LetRec: Type of recursive function does not match declaration")


  (* Task 1 *)
  | NewRef(e) -> 
    chk_expr e >>= fun t ->
    return @@ RefType(t) 
  | DeRef(e) -> 
    chk_expr e >>= ref_of_refType "deref: " >>= fun t ->
    return t
  | SetRef(e1,e2) -> 
    chk_expr e1 >>= ref_of_refType "setref: " >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if t1=t2
    then return UnitType
    else error "setref: type of e1 and e2 do not match"
  | BeginEnd([]) -> return UnitType
  | BeginEnd(es) -> 
    List.fold_left (fun _ e -> chk_expr e) (return UnitType) es

(* Task 2 *)
  | EmptyList(Some t) -> 
    return @@ ListType(t)
  | EmptyList(None) ->
    error "emptyList: Type is Required"
  | Cons(e1,e2) ->     
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= list_of_listType "cons: " >>= fun t2 ->
    if t1=t2
    then return @@ ListType(t1)
    else error "cons: type of head and tail do not match"
  | IsEmpty(e) -> 
    chk_expr e >>= fun n ->
    (match n with
    | ListType l -> return BoolType
    | TreeType t -> return BoolType
    | _ -> error "Empty?: Expected a List or Tree type")
  | Hd(e) -> 
    chk_expr e >>= list_of_listType "Hd: " >>= fun t ->
    return t
  | Tl(e) ->     
    chk_expr e >>= list_of_listType "TL: " >>= fun t ->
    return @@ ListType(t)



  (* Task 3 *)
  | EmptyTree(Some t) -> 
    return @@ TreeType(t)
  | EmptyTree(None) ->
    error "emptyTree: Type is Required"
  | Node(de, le, re) -> 
    chk_expr de >>= fun d ->
    chk_expr le >>= tree_of_TreeType "le:">>= fun left ->
    chk_expr re >>= tree_of_TreeType "re:">>= fun right ->
    if (d=left && d=right)
      then return @@ TreeType(d)
      else error "node: types do not match"

  | CaseT (target, emptycase, id1, id2, id3, nodecase) -> chk_expr target >>= fun targ ->
    (match targ with
      | TreeType t -> chk_expr emptycase >>= fun e -> 
        (extend_tenv id1 t) >>+ (extend_tenv id2 (TreeType t)) >>+ (extend_tenv id3 (TreeType t)) >>+ chk_expr nodecase >>= fun n ->
        if e=n
        then return e
        else error "CaseT: types do not match"
      | _ -> error "CaseT: target must be a tree")
        

  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint"
  | _ -> failwith "chk_expr: implement"    
and
  chk_prog (AProg(_,e)) =
  chk_expr e

(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)



