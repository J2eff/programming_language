type program = exp
and exp =
	| SKIP
	| TRUE
	| FALSE
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
	| LE of exp * exp
	| EQ of exp * exp
	| NOT of exp 
  | IF of exp * exp * exp
	| WHILE of exp * exp 
	| LET of var * exp * exp
	| PROC of var list * exp 
	| CALLV of exp * exp list 
	| CALLR of exp * var list
	| ASSIGN of var * exp 
				(* to do*)
	| RECORD of (var * exp) list 
	| FIELD of exp * var
	| ASSIGNF of exp * var * exp 
		(* ----------------*)
  | READ of var (* 이미 구현되어 있음 *)
	| PRINT of exp (* 이미 구현되어 있음 *)
  | SEQ of exp * exp
  | BEGIN of exp
and var = string

type value = 
    Int of int
  | Bool of bool
	| Unit
  | Procedure of var list * exp * env
	| Record of record
  | Loc of loc
and loc = int 
and env = (var * loc) list
and mem = (loc * value) list
and record = (var * loc) list

(* conversion of value to string *)
let value2str v =
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "."  
	| Procedure (params,e,env) -> "Procedure "
  | Record record -> "Record "
	| Loc l -> "Loc "^(string_of_int l)

	let value2int v =
		match v with
		| Int n -> n
		| Loc n -> n
		| _ -> raise (Failure ("Type error"))
	let value2bool v =
			match v with
			|	Bool true -> true
			| Bool false -> false
			| _ -> raise (Failure ("Type error"))

(* environment *)
let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec apply_env e x = 
  match e with
  | [] -> raise (Failure (x ^ " is unbound in Env"))
  | (y,v)::tl -> if x = y then v else apply_env tl x

(* memory *)
let empty_mem = [] 
let extend_mem (l,v) m = (l,v)::(List.filter (fun (l',_) -> l != l') m)
let rec apply_mem m l = 
  match m with
  | [] -> raise (Failure ("Location " ^ string_of_int (l) ^ " is unbound in Mem"))
  | (y,v)::tl -> if l = y then v else apply_mem tl l

let counter = ref 0
let new_location () = counter:=!counter+1; (!counter)

(* conversion of env to string *)
let string_of_env env = 
	List.fold_left (fun str (x,l) -> Printf.sprintf "%s\n%s -> %d" str x l) "" env  
(* conversion of mem to string *)
let string_of_mem mem = 
	List.fold_left (fun str (l,v) -> Printf.sprintf "%s\n%d -> %s" str l (value2str v)) "" mem 		
		
exception NotImplemented
exception UndefinedSemantics
(* if the following variable is set true, gc will work (otherwise, gc simply returns a given memory). *)
let remove_garbage = ref false 

let gc: env * mem -> mem
= fun (env, mem) ->
	if (not !remove_garbage) then mem 
	else 
		raise NotImplemented (* TODO *)

let rec eval : program -> env -> mem -> (value * mem)
=fun pgm env mem ->  
  match pgm with
  | READ x -> (Unit, extend_mem (apply_env env x, Int (read_int())) mem) (* Do not modify *)
	| PRINT e ->
		let v, mem' = eval e env mem in
		let _ = print_endline (value2str v) in
		(v, gc(env,mem')) (* Do not modify *) 
	| SKIP -> (Unit,mem)
	| TRUE -> ((Bool true),mem)
	| FALSE -> ((Bool false),mem)
	| CONST n ->  ((Int n),mem)
	| VAR v ->  let loc = apply_env env v in 
								let v' = apply_mem mem loc in ((v',mem)) 
	| ADD (e1,e2) -> let (val1,mem') = eval e1 env mem in 
										 let (val2,mem'') = eval e2 env mem' in (Int ((value2int val1)+(value2int val2)) , mem'' ) 
										 
  | SUB (e1,e2)-> let (val1,mem') = eval e1 env mem in 
									let (val2,mem'') = eval e2 env mem' in (Int ((value2int val1)-(value2int val2)) , mem'' ) 

  | MUL (e1,e2)-> let (val1,mem') = eval e1 env mem in 
									let (val2,mem'') = eval e2 env mem' in (Int ((value2int val1)*(value2int val2)) , mem'' ) 

  | DIV (e1,e2)-> let (val1,mem') = eval e1 env mem in 
										let (val2,mem'') = eval e2 env mem' in (Int ((value2int val1)/(value2int val2)) , mem'' ) 
																	
	| LE (e1,e2) -> let (val1,mem') = eval e1 env mem in	
										let (val2,mem'') = eval e2 env mem' in 
											let sub = (value2int val1) - (value2int val2) in
												if (sub <= 0) then (Bool true,mem'') else   (Bool false,mem'')

	| EQ (e1,e2) ->  let (val1,mem') = eval e1 env mem in	
										let (val2,mem'') = eval e2 env mem' in 
											(match (val1,val2) with
											| (Int n1 , Int n2) -> if n1=n2 then (Bool true,mem'') else   (Bool false,mem'')
											|	(Bool b1,Bool b2) ->  if b1=b2 then (Bool true,mem'') else   (Bool false,mem'')
											| _ -> (Bool false,mem'')
											)
	| NOT e1 -> let (val1,mem') = eval e1 env mem in (Bool (not (value2bool val1)),mem' )

	| IF (e1,e2,e3) ->  let (val1,mem') = eval e1 env mem in	
											if (value2bool val1) then eval e2 env mem' else  eval e3 env mem'
	
	| WHILE (e1,e2) ->  let (val1,mem') = eval e1 env mem in	
												if (value2bool val1)  
													then  
														let (val2,mem') = eval e2 env mem' in eval (WHILE (e1,e2)) env mem'
													else
														(Unit ,mem')


	| LET (variable,e1,e2) ->  let (val1,mem') = eval e1 env mem in	
															let newLocation = new_location () in
																let  mem'' = extend_mem (newLocation,val1) mem' in
																	let env' = extend_env (variable,newLocation) env in eval e2 env' mem'' 
	
	| PROC (varList,e1) -> (Procedure (varList,e1,env),mem)

	| CALLV  (e1,valListForFuntionCall) ->  
		let ( (Procedure (varListInFuntion,expr,envForFuntionCall)) ,mem') = eval e1 env mem in
		let (envforFun,envFormem) = callByValue varListInFuntion valListForFuntionCall env envForFuntionCall mem' in eval expr envforFun envFormem
	
	| CALLR (e1,varList) ->	
			let ( (Procedure (varListInFuntion,expr,envForFuntionCall)) ,mem') = eval e1 env mem in
			let (envforFun,envFormem) = callByRef varListInFuntion varList env mem' in eval expr envforFun envFormem

	| ASSIGN (variable,expr) ->
			let (value1,mem') = eval expr env mem in
				let envLoc = apply_env env variable in
					let mem'' = extend_mem (envLoc,value1) mem' in (value1,mem'')


	| SEQ (e1,e2) ->
		let (v1,mem') = eval e1 env mem in let (v2,mem'') = eval e2 env mem' in (v2,mem'')
			
	| BEGIN e1 ->
		let (v1,mem') = eval e1 env mem in (v1,mem')
				
	| _ -> raise NotImplemented (* TODO *)

	
and callByValue varList valList rootenv targetenv mem =
	match (varList,valList) with 
	| ([],[]) ->  (targetenv,mem)
	| (hd1::tl1,hd2::tl2) -> 
			let newLoc = new_location () in
			let (valForvar,mem') = eval hd2 rootenv mem in
			let envForFuntionCall = extend_env (hd1,newLoc) targetenv in  
			let mem'' = extend_mem (newLoc,valForvar) mem' in callByValue tl1 tl2 rootenv envForFuntionCall mem''
	| ([],_) -> raise UndefinedSemantics
	| (_,[]) -> raise UndefinedSemantics

	and callByRef varList valList env mem =
	match (varList,valList) with 
	| ([],[]) ->  (env,mem)
	| (hd1::tl1,hd2::tl2) -> 
			let (loc,mem') =  (eval (VAR hd2) env mem) in
			let envForFuntionCall = extend_env (hd1,(value2int loc)) env in callByRef tl1 tl2 envForFuntionCall mem'
	| ([],_) -> raise UndefinedSemantics
	| (_,[]) -> raise UndefinedSemantics
			


let run : program -> bool -> bool -> unit 
= fun pgm with_gc print_mem_size ->
	let _ = remove_garbage := with_gc in 
	let mem = snd (eval pgm empty_env empty_mem) in   
	if (print_mem_size) then 
		print_endline (Printf.sprintf "Final mem size: %d" (List.length mem))
	
	
