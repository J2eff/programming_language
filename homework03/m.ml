type program = exp
and exp = 
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
  | NEWREF of exp 
  | DEREF of exp
  | SETREF of exp * exp
  | SEQ of exp * exp
  | BEGIN of exp
and var = string

type value = 
    Int of int 
  | Bool of bool 
  | Procedure of var * exp * env 
  | RecProcedure of var * var * exp * env
  | Loc of loc
and loc = int
and env = (var * value) list
and mem = (loc * value) list

(* conversion of value to string *)
let value2str v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Loc l -> "Loc "^(string_of_int l)
  | Procedure (x,e,env) -> "Procedure "
  | RecProcedure (f,x,e,env) -> "RecProcedure "^f

(* environment *)
let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec apply_env e x = 
  match e with
  | [] -> raise (Failure (x ^ " is unbound in Env"))
  | (y,v)::tl -> if x = y then v else apply_env tl x

(* memory *)
let empty_mem = [] 
let extend_mem (l,v) m = (l,v)::m
let rec apply_mem m l = 
  match m with
  | [] -> raise (Failure ("Location " ^ string_of_int l ^ " is unbound in Mem"))
  | (y,v)::tl -> if l = y then v else apply_mem tl l

(* use the function 'new_location' to generate a fresh memory location *)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

(*****************************************************************)
(* 

TODO: Implement the eval function. Modify this function only. 
현재 PROC 까지 구현   남은 evaluation match는
  | CALL of exp * exp
  | 
  | 
  | 
  | SEQ of exp * exp
  | BEGIN of exp
  + read
  
*)
(*****************************************************************)
let rec eval : exp -> env -> mem -> value * mem
= fun exp env mem -> 
  match exp with
  | CONST n -> ( (Int n) ,mem)

  | VAR x -> 
      let l = (apply_env env x) in 
      let v = apply_mem mem (val2int l) in (v,mem)

  | ADD(e1,e2) ->  
    let (val1,mem') = eval e1 env mem in 
      let (val2,mem'') = eval e2 env mem' in 
        ( Int ((val2int val1)+(val2int val2)) , mem'')

  | MUL(e1,e2) ->   
    let (val1,mem') = eval e1 env mem in 
      let (val2,mem'') = eval e2 env mem' in 
      ( Int ((val2int val1)*(val2int val2)) ,mem'')

  | SUB(e1,e2) ->  
    let (val1,mem') = eval e1 env mem in 
      let (val2,mem'') = eval e2 env mem' in 
        ( Int ((val2int val1)-(val2int val2)) ,mem'')

  | DIV(e1,e2) ->  
    let (val1,mem') = eval e1 env mem in 
      let (val2,mem'') = eval e2 env mem' in 
        (Int ((val2int val1)/(val2int val2)) ,mem'')

  | ISZERO e -> 
    let (val1,mem') = eval e env mem in 
      if (val2int val1) = 0 
        then (Bool true,mem')
        else (Bool false,mem')

  | READ ->
    let x = read_int() in (Int x ,mem)

  | IF(e1,e2,e3) ->
    let (val1,mem') = eval e1 env mem in 
    if (val2bool val1) = true 
      then eval e2 env mem'
      else eval e3 env mem'

  | LET (v1,e1,e2) ->
      let loc = new_location () in 
        let (val1,mem') = eval e1 env mem in
          let env' = (extend_env (v1,Loc loc) env) in
            let mem'' = (extend_mem (loc , val1) mem') in eval e2 env' mem''


  | LETREC (f,x,e1,e2) ->
      let loc = new_location() in
        eval e2 (extend_env (f,Loc loc) env) (extend_mem (loc ,RecProcedure (f ,x ,e1,env)) mem)

  | PROC (v1,e1) ->
    (Procedure (v1,e1,env),mem)

  | CALL (e1,e2) ->
     let (val1,mem') = eval e1 env mem in
        (
          match val1 with 
          | Procedure (x,e,env') ->
            let (val2,mem'') = eval e2 env mem' in 
              let loc = new_location () in
                eval e (extend_env (x,Loc loc) env') (extend_mem (loc, val2) mem'')
          | RecProcedure (f,x,e,env') -> 
            let (val2,mem'') = eval e2 env mem' in 
              let loc1 = new_location () in
                let loc2 = new_location () in
                  eval e (extend_env (x,Loc loc2) (extend_env (f,Loc loc1) env'))   (extend_mem (loc2,val2)  (extend_mem (loc1, val1) mem''))
          | _ -> raise UndefinedSemantics
               
        )
        
            
          
        
  | NEWREF e1 ->
    let (val1,mem') = eval e1 env mem in
     let loc = new_location () in
      let mem'' = extend_mem (loc,val1) mem' in ( (Loc loc), mem'')

  | DEREF e1 ->
    let (l,mem') = eval e1 env mem in
      let loc1 = (apply_mem mem' (val2int l)) in (( loc1 ) ,mem')

  | SETREF (e1,e2) ->
    let (l,mem') = eval e1 env mem in
      let (v,mem'') = eval e2 env mem' in  (v, (extend_mem ((val2int l),v) mem'' )   )

  | SEQ (e1,e2) ->
    let (v1,mem') = eval e1 env mem in let (v2,mem'') = eval e2 env mem' in (v2,mem'')

  | BEGIN e1 ->
    let (v1,mem') = eval e1 env mem in (v1,mem')
  


and val2int value =
  match value with
    | Int n -> n
    | Loc l -> l
    | _ -> raise UndefinedSemantics
and val2bool value = 
  match value with
    | Bool b -> b
    | _ -> raise UndefinedSemantics


(* driver code *)
let run : program -> value
= fun pgm -> (fun (v,_) -> v) (eval pgm empty_env empty_mem) 



