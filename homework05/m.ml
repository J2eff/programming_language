type program = exp
and exp = 
	| TRUE
	| FALSE
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

exception TypeError

type typ = TyInt | TyBool 
	| TyFun of typ * typ (* t1 -> t2 *) 
	| TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list (* t1 = t2 *)

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ "\n")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  = fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the substitution and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  = fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
= fun tenv e ty ->
  match e with
    | CONST n -> [(ty,TyInt)]
    | TRUE -> [(ty,TyBool)]
    | FALSE ->  [(ty,TyBool)]
    | VAR x -> 
        let typeOfVar = (TEnv.find tenv x) in  [(ty,typeOfVar)]
    | ADD(e1,e2) -> [(ty,TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
    | SUB(e1,e2) -> [(ty,TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
    | MUL(e1,e2) -> [(ty,TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
    | DIV(e1,e2) -> [(ty,TyInt)] @ (gen_equations tenv e1 TyInt) @ (gen_equations tenv e2 TyInt)
    | ISZERO e -> [(ty,TyBool)] @  (gen_equations tenv e TyInt)
    | READ -> [(ty,TyInt )]
    | IF(e1,e2,e3) ->
      let li =  (gen_equations tenv e1 TyBool)@ (gen_equations tenv e2 ty)@ (gen_equations tenv e3 ty)
      in li

    | LET (variable,e1,e2)-> 
      let tyVariable = fresh_tyvar () in
      let newTenv = TEnv.extend (variable,tyVariable) tenv in
        (gen_equations tenv e1 tyVariable) @  (gen_equations newTenv e2 ty) 
    
      
    | LETREC (functionV,variable,e1,e2) -> 
        let tyVariable2 = fresh_tyvar () in
        let tyVariable1 = fresh_tyvar () in
        let newTenv1 = (TEnv.extend (functionV, TyFun (tyVariable2,tyVariable1)) tenv) in
        let newTenv2 = (TEnv.extend (variable,tyVariable2) newTenv1) in
        (gen_equations newTenv2 e1 tyVariable1)@(gen_equations newTenv1 e2 ty) 



    | PROC (variable,e)->
      let tyVariable1 = fresh_tyvar () in
      let tyVariable2 = fresh_tyvar () in
      let newTenv = (TEnv.extend (variable,tyVariable1) tenv) in
      [(ty, TyFun ( tyVariable1, tyVariable2) )] @ (gen_equations newTenv e tyVariable2) 
    
    | CALL (e1,e2) ->
      let tyVariable = fresh_tyvar () in
      (gen_equations tenv e1 (TyFun (tyVariable,ty)) ) @  (gen_equations tenv e2 tyVariable) 
    

let is_substring string substring = 
  let ssl = String.length substring and sl = String.length string in 
  if ssl = 0 || ssl > sl then false else 
    let max = sl - ssl and clone = String.create ssl in
    let rec check pos = 
      pos <= max && (
        String.blit string pos clone 0 ssl ; clone = substring 
        || check (String.index_from string (succ pos) substring.[0])
      )
    in             
    try check (String.index string substring.[0])
    with Not_found -> false

let rec unify t1 t2 subst =
  match (t1,t2) with
  | (TyInt,TyInt) -> subst
  | (TyBool,TyBool) -> subst
  | (TyVar x,TyVar y) ->  (Subst.extend x t2 subst)
  | (TyVar x, _) -> 
    if (is_substring (string_of_type t2) x )
    then
      raise TypeError
    else
      (Subst.extend x t2 subst)

  | (_, TyVar x) -> unify t2 t1 subst

  | (TyFun (ty1, ty2),TyFun (ty1', ty2')) ->
    let subst' = unify ty1 ty1' subst in
    let subst'' = unify (Subst.apply ty2 subst')  (Subst.apply ty2' subst' ) subst' in subst''
  
  | (_,_) -> raise TypeError

let rec unifyall eqns li =
  match eqns with
  | [] -> li
  | (hd1,hd2)::tl -> 
    let hd1' = Subst.apply hd1 li in
    let hd2' = Subst.apply hd2 li in
    let li' = unify hd1' hd2' li in unifyall tl li'
      

let solve : typ_eqn -> Subst.t
= fun eqns -> unifyall eqns []


(* typeof: Do not modify this function *)
let typeof : exp -> typ 
= fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns in
  try 
    let subst = solve eqns in
    let ty = Subst.apply new_tv subst in
     print_endline "= Substitution = ";
      Subst.print subst;
      print_endline "";
      print_endline ("Type of the given program: " ^ string_of_type ty);
      print_endline "";
      ty
  with TypeError -> (print_endline "The program does not have type. Rejected."); exit (1)




  
