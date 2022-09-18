(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;

let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let list_eq eq l1 l2 = (List.length l1) = (List.length l2) && List.for_all2 eq l1 l2;;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        list_eq expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
   match pe with
      | ScmConst(x) -> ScmConst'(x)
      | ScmIf(test, dit, dif) -> ScmIf'((run test params env), 
                                        (run dit params env), 
                                        (run dif params env))
      | ScmSeq(exprs)-> ScmSeq'(List.map (fun expr -> run expr params env) exprs)
      | ScmSet(ScmVar(var1), val1) -> ScmSet'(tag_lexical_address_for_var var1 params env, run val1 params env)
      | ScmDef (ScmVar(var1), val1) -> ScmDef'(tag_lexical_address_for_var var1 params env, run val1 params env)
      | ScmOr (exprs)-> ScmOr'(List.map (fun expr -> run expr params env) exprs)
      | ScmApplic(operator, operands) -> 
              ScmApplic'((run operator params env), (List.map (fun expr -> run expr params env) operands))
      | ScmVar(x)-> ScmVar'(tag_lexical_address_for_var x params env)
      | ScmLambdaSimple(lambda_params, body) -> 
              ScmLambdaSimple'(lambda_params, 
                                (run body lambda_params (List.append [params] env)))
      | ScmLambdaOpt(lambda_params, opt_param, body) -> 
              let concat_params = List.append lambda_params [opt_param] in
              ScmLambdaOpt'(lambda_params, opt_param, 
                              (run body concat_params (List.append [params] env)))
      | _ -> raise X_this_should_not_happen     
   in 
   run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;

  let rec car_cdr = function
    | e::rest -> e, rest
    | _ -> raise X_this_should_not_happen 
  
  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail =
    match pe with
      | ScmConst'(x) -> ScmConst'(x)
      | ScmVar'(x) -> ScmVar'(x)
      | ScmIf'(test, dit, dif) -> ScmIf'(test, (run dit in_tail), (run dif in_tail))
      | ScmSet'(var1, val1) -> ScmSet'(var1, run val1 false)
      | ScmDef'(var1, val1) -> ScmDef'(var1, run val1 false)
      | ScmSeq'(exprs) -> 
          let firsts, last = rdc_rac exprs in
          let firsts = List.map (fun expr -> run expr false) firsts in
          let last = run last in_tail in
          ScmSeq'(List.append firsts [last])
      | ScmOr'(exprs) -> 
          let firsts, last = rdc_rac exprs in
          let firsts = List.map (fun expr -> run expr false) firsts in
          let last = run last in_tail in
          ScmOr'(List.append firsts [last])
      | ScmLambdaSimple'(lambda_params, body) -> ScmLambdaSimple'(lambda_params, (run body true))
      | ScmLambdaOpt'(lambda_params, opt_param, body) -> ScmLambdaOpt'(lambda_params, opt_param, (run body true))
      | ScmApplic'(operator, operands) ->
            if in_tail
            then ScmApplicTP'((run operator false), (List.map (fun expr -> run expr false) operands))
            else ScmApplic'((run operator false), (List.map (fun expr -> run expr false) operands))
      | _ -> raise X_this_should_not_happen
   in 
   run pe false;;


  (* boxing *)

  let index_list lst = 
    let n = List.length lst in
    let buildList i n =
        let rec aux acc i =
          if i <= n then
            aux (i::acc) (i+1)
          else (List.rev acc)
        in
        aux [] i in
    let indexes = buildList 0 (n-1) in
    List.map2 (fun p i -> (p, i)) lst indexes;;

  let rec find_writes name expr lambda_of_expr is_bounded = (* lambda_of_expr is the imidiate lambda enclosing expr *)
    let handle_exprs exprs = 
      let maped = List.map (fun e -> find_writes name e lambda_of_expr is_bounded) exprs in
      List.fold_left (fun w lst -> List.append lst w) [] maped in
    match expr with 
      | ScmSet'(VarFree(x), _) when x=name -> []
      | ScmSet'(VarBound(x,mj,mn), _) when x=name -> [VarBound(name,mj,mn),lambda_of_expr]
      | ScmSet'(VarParam(x,i), _) when x=name -> [VarParam(name,i), lambda_of_expr]
      | ScmSet'(x, val1) -> []
      | ScmVar'(_) -> []
      | ScmConst'(_) -> []
      | ScmDef'(_, val1) -> find_writes name val1 lambda_of_expr is_bounded
      | ScmIf'(test, dit, dif) -> 
        let test = find_writes name test lambda_of_expr is_bounded in
        let dit = find_writes name dit lambda_of_expr is_bounded in
        let dif = find_writes name dif lambda_of_expr is_bounded in
        List.append (List.append test dit) dif
      | ScmSeq'(exprs) -> handle_exprs exprs
      | ScmOr'(exprs) -> handle_exprs exprs
      | ScmLambdaSimple'(lambda_params, body) as enc_lambda -> 
                if not(List.mem name lambda_params)
                 then (if is_bounded
                      then find_writes name body lambda_of_expr is_bounded
                      else find_writes name body enc_lambda true)
                else []
      | ScmLambdaOpt'(lambda_params, opt_param, body) as enc_lambda-> 
                if not(List.mem name (List.append lambda_params [opt_param]))
                 then (if is_bounded
                      then find_writes name body lambda_of_expr is_bounded
                      else find_writes name body enc_lambda true)
                else []
      | ScmApplic'(operator, operands) -> List.append (find_writes name operator lambda_of_expr is_bounded) (handle_exprs operands)
      | ScmApplicTP'(operator, operands) -> List.append (find_writes name operator lambda_of_expr is_bounded) (handle_exprs operands)
      | _ -> []

  let rec find_reads name expr lambda_of_expr is_bounded = (* lambda_of_expr is the imidiate lambda enclosing expr *)
    let handle_exprs exprs = 
      let maped = List.map (fun e -> find_reads name e lambda_of_expr is_bounded) exprs in
      List.fold_left (fun w lst -> List.append lst w) [] maped in
    match expr with 
      | ScmVar'(VarFree(x)) when x=name -> []
      | ScmVar'(VarBound(x,mj,mn)) when x=name -> [VarBound(name,mj,mn),lambda_of_expr]
      | ScmVar'(VarParam(x,i)) when x=name -> [VarParam(name,i),lambda_of_expr]
      | ScmSet'(var1, val1) -> find_reads name val1 lambda_of_expr is_bounded
      | ScmConst'(_) -> []
      | ScmDef'(_, val1) -> find_reads name val1 lambda_of_expr is_bounded
      | ScmIf'(test, dit, dif) -> 
        let test = find_reads name test lambda_of_expr is_bounded in
        let dit = find_reads name dit lambda_of_expr is_bounded in
        let dif = find_reads name dif lambda_of_expr is_bounded in
        List.append (List.append test dit) dif
      | ScmSeq'(exprs) -> handle_exprs exprs
      | ScmOr'(exprs) -> handle_exprs exprs
      | ScmLambdaSimple'(lambda_params, body) as enc_lambda -> 
                if not(List.mem name lambda_params)
                 then (if is_bounded
                      then find_reads name body lambda_of_expr is_bounded
                      else find_reads name body enc_lambda true)
                else []
      | ScmLambdaOpt'(lambda_params, opt_param, body) as enc_lambda-> 
                if not(List.mem name (List.append lambda_params [opt_param]))
                 then (if is_bounded
                      then find_reads name body lambda_of_expr is_bounded
                      else find_reads name body enc_lambda true)
                else []
      | ScmApplic'(operator, operands) -> List.append (find_reads name operator lambda_of_expr is_bounded) (handle_exprs operands)
      | ScmApplicTP'(operator, operands) -> List.append (find_reads name operator lambda_of_expr is_bounded) (handle_exprs operands)
      | _ -> [];;


  let rec boxing expr =
    match expr with
    | ScmConst'(exp) -> ScmConst'(exp)
    | ScmVar'(var) -> ScmVar'(var)
    | ScmBox'(var) -> ScmBox'(var)
    | ScmBoxGet'(var) -> ScmBoxGet'(var)
    | ScmBoxSet'(var, exp) -> ScmBoxSet'(var, (boxing exp))
    | ScmIf'(test, dit, dif) -> ScmIf'((boxing test), (boxing dit), (boxing dif))
    | ScmSeq'(exps) -> ScmSeq'(List.map boxing exps)
    | ScmSet'(set_var, set_val) -> ScmSet'(set_var, (boxing set_val)) 
    | ScmDef'(def_var, def_val) -> ScmDef'(def_var, (boxing def_val))
    | ScmOr'(exps) -> ScmOr'(List.map boxing exps)
    | ScmLambdaSimple'(params, body) as enc_lambda -> ScmLambdaSimple'(params, (handle_lambda params (boxing body) enc_lambda))
    | ScmLambdaOpt'(params, opt_param, body) as enc_lambda -> ScmLambdaOpt'(params, opt_param, (handle_lambda (List.append params [opt_param]) (boxing body) enc_lambda))   
    | ScmApplic'(operator, args) -> ScmApplic'((boxing operator), (List.map boxing args))
    | ScmApplicTP'(operator, args) -> ScmApplicTP'((boxing operator), (List.map boxing args))


    and should_box_var name expr enc_lambda =
      let reads_list = find_reads name expr enc_lambda false in
      let writes_list = find_writes name expr enc_lambda false in
      let match_ri_wj ri wj =
        match (ri, wj) with
        | ((VarParam(_,_), _), (VarBound (_, _, _), _)) -> true
        | ((VarBound (_, _, _), _), (VarParam(_,_), _)) -> true
        | ((VarParam(_,_), _),  (VarParam(_,_), _)) -> false
        | ((VarBound (_, mj1, mn1), read_lambda), (VarBound (_, mj2, mn2), write_lambda)) 
              -> not(expr'_eq read_lambda write_lambda)
        | _ -> raise X_this_should_not_happen in
      let match_ri_writes ri = List.map (fun wj -> match_ri_wj ri wj) writes_list in
      let check_ri ri = List.fold_left (fun x y -> x||y) false (match_ri_writes ri) in
      let match_reads = List.map (fun ri -> check_ri ri) reads_list in
      List.fold_left (fun x y -> x||y) false (match_reads)

    and handle_lambda params body enc_lambda = 
      let new_params = index_list params in
      let new_params = List.map (fun (x,ind) -> ((x,ind), should_box_var x body enc_lambda)) new_params in 
      let new_params = List.filter (fun (x, should) -> should) new_params in
      let new_params = List.map (fun (x, _) -> x) new_params in
      let new_body = if (List.length new_params) = 0
                  then body
                  else apply_box_to_body new_params body in
      let new_body = if (List.length new_params) = 0
                    then new_body
                    else handle_body new_params new_body in
      new_body

    
    and handle_body params body =
      match body with
      | ScmSeq'(exprs) -> ScmSeq'((List.append (make_boxes params) exprs))
      | e -> ScmSeq'((List.append (make_boxes params) [e]))
    
    and apply_box_to_body params body = 
      let apply_pi (pi_name, i) new_body = box_gets_sets pi_name new_body in
      let rec apply_params ps new_body = 
        match ps with
        | [] -> new_body
        | [pn] -> apply_pi pn new_body
        | pi::rest -> apply_params rest (apply_pi pi new_body)  in
      apply_params params body
    
    and make_box v minor = ScmSet'(VarParam(v, minor), ScmBox'(VarParam(v,minor)))
    and make_boxes params = 
      match params with 
      | [] -> []
      | (pi, i)::rest -> List.append [make_box pi i] (make_boxes rest)

    and box_gets_sets name expr = 
      let handle_exprs exprs = List.map (fun e -> box_gets_sets name e) exprs in
      match expr with 
        | ScmVar'(VarBound(x,mj,mn)) when x=name -> ScmBoxGet'(VarBound(name,mj,mn))
        | ScmVar'(VarParam(x,i)) when x=name -> ScmBoxGet'(VarParam(name,i))
        | ScmSet'(VarBound(x,mj,mn), val1) when x=name -> ScmBoxSet'(VarBound(x,mj,mn), (box_gets_sets x val1))
        | ScmSet'(VarParam(x,i), val1) when x=name -> ScmBoxSet'(VarParam(x,i), (box_gets_sets name val1))
        | ScmSet'(var1, val1) -> ScmSet'(var1, (box_gets_sets name val1))
        | ScmDef'(var1, val1) -> ScmDef'(var1, (box_gets_sets name val1))
        | ScmIf'(test, dit, dif) -> 
          let test = box_gets_sets name test in
          let dit = box_gets_sets name dit in
          let dif = box_gets_sets name dif in
          ScmIf'(test, dit, dif)
        | ScmSeq'(exprs) -> ScmSeq'(handle_exprs exprs)
        | ScmOr'(exprs) -> ScmOr'(handle_exprs exprs)
        | ScmLambdaSimple'(lambda_params, body) -> 
                  if not(List.mem name lambda_params)
                  then ScmLambdaSimple'(lambda_params, (box_gets_sets name body))
                  else ScmLambdaSimple'(lambda_params, body)
        | ScmLambdaOpt'(lambda_params, opt_param, body) -> 
                  if not(List.mem name (List.append lambda_params [opt_param]))
                  then ScmLambdaOpt'(lambda_params, opt_param, (box_gets_sets name body))
                  else ScmLambdaOpt'(lambda_params, opt_param, body)
        | ScmApplic'(operator, operands) -> ScmApplic'((box_gets_sets name operator), (handle_exprs operands))
        | ScmApplicTP'(operator, operands) -> ScmApplicTP'((box_gets_sets name operator), (handle_exprs operands))
        | _ -> expr;;
    
  let rec box_set expr = boxing expr;;

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
