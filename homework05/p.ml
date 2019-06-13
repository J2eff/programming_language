open M

(* exp environment : var -> exp *)
module EEnv = struct
  type t = var -> exp
  let empty = fun _ -> raise (Failure "Exp Env is empty")
  let extend (x,t) eenv = fun y -> if x = y then t else (eenv y)
  let find eenv x = eenv x
end


let rec change rootExp eenv = 
  match rootExp with
  | LET(var1,e1,e2) -> 
      let e1' = change e1 eenv in
      let eenv' = EEnv.extend (var1,e1') eenv in 
      let e2' = change e2 eenv' in e2'

  | TRUE -> TRUE
	| FALSE -> FALSE
  | CONST n ->  CONST n
  | VAR x -> (try EEnv.find eenv x with _ -> VAR x)
  | ADD(e1,e2) ->
    let e1' =  change e1 eenv in 
    let e2' =  change e2 eenv in  ADD(e1',e2')

  | SUB(e1,e2) ->
    let e1' =  change e1 eenv in 
    let e2' =  change e2 eenv in  SUB(e1',e2')
  | MUL(e1,e2)->
    let e1' =  change e1 eenv in 
    let e2' =  change e2 eenv in  MUL(e1',e2')

  | DIV (e1,e2) ->
    let e1' =  change e1 eenv in 
    let e2' =  change e2 eenv in  DIV(e1',e2')

  | ISZERO e1 ->
    let e1' =  change e1 eenv in  (ISZERO e1')

  | READ -> READ

  | IF(e1,e2,e3) ->
      let e1' =  change e1 eenv in 
      let e2' =  change e2 eenv in
      let e3' =  change e3 eenv in IF(e1',e2',e3')

  | LETREC( varFun,varX, e1, e2)->
    let e1' =  change e1 eenv  in LETREC(varFun,varX, e1', e2)
    

  | PROC(var1,e1)-> 
    let e1' =  change e1 eenv in  PROC(var1,e1')

  | CALL(e1,e2) ->
    let e1' =  change e1 eenv in 
    let e2' =  change e2 eenv in CALL(e1',e2')



let expand: exp -> exp 
= fun exp -> change exp EEnv.empty



(* typeof: Do not modify this function *)
let typeof : exp -> typ 
= fun exp -> 
	let exp' = expand exp in 
	M.typeof exp'  



