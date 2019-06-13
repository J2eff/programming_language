open M

(* exp environment : var -> exp *)
module EEnv = struct
  type t = var -> exp
  let empty = fun _ -> raise (Failure "Exp Env is empty")
  let extend (x,t) eenv = fun y -> if x = y then t else (eenv y)
  let find eenv x = eenv x
end




let expand: exp -> exp 
= fun exp -> 
  match exp with
  | LET(var1,e1,e2) -> 
  EEnv.extend (var1,e1) (EEnv.find [] var1)
  | _ -> exp

(* typeof: Do not modify this function *)
let typeof : exp -> typ 
= fun exp -> 
	let exp' = expand exp in 
	M.typeof exp'  
