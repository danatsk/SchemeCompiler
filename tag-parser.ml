#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec is_propper_list = function
| ScmNil -> true
| ScmPair(_, ScmNil) -> true
| _ -> false
 
let rec all_different = function
| ScmNil -> true
| ScmPair(hd, ScmNil) -> true
| ScmPair(hd,tl) -> (not (List.mem hd (scm_list_to_list tl) )) && all_different tl
| _ -> raise X_proper_list_error

let rec all_different_strings = function
| [] -> true
| hd::[] -> true
| hd::tl -> (all_different_strings tl) && (not (List.mem hd tl));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;


module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;


let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 

(* 2.1.1 Constants *) 
  | ScmNil -> (ScmConst ScmNil)
  | ScmBoolean(x) -> ScmConst(ScmBoolean x)
  | ScmChar(x) -> ScmConst(ScmChar x)
  | ScmString(x) -> ScmConst(ScmString x)
  | ScmNumber(x) -> ScmConst(ScmNumber x) 
  | ScmPair(ScmSymbol("quote"), ScmPair(x, ScmNil)) -> ScmConst x
  | ScmVector(x) -> ScmConst(ScmVector(x))

(* 2.1.2 Variables *)
  | ScmSymbol(x) -> if (List.mem x reserved_word_list)
                  then raise (X_syntax_error(ScmSymbol(x), "reserved word"))
                  else ScmVar(x)

(* 2.1.3 Cond *) 
  | ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmPair(dif, ScmNil)))) ->
      ScmIf(tag_parse_expression test, tag_parse_expression dit, tag_parse_expression dif)
  | ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmNil))) ->
      ScmIf(tag_parse_expression test, tag_parse_expression dit, ScmConst ScmVoid)

(* 2.1.4 Disjunctions *) 
  | ScmPair(ScmSymbol("or"), ScmNil) -> tag_parse_expression (ScmBoolean(false))
  | ScmPair(ScmSymbol("or"), ScmPair(x, ScmNil)) -> tag_parse_expression x
  | ScmPair(ScmSymbol("or"), sexprs) -> ScmOr(List.map tag_parse_expression (make_list_loop sexprs))


(* 2.1.5 Lambda forms *)
  (* variadic lambda *)
  |ScmPair(ScmSymbol "lambda", ScmPair(ScmSymbol var, body)) ->
    let parseBody = function
      | ScmPair(e, ScmNil) -> tag_parse_expression e
      | exp -> ScmSeq(List.map tag_parse_expression (scm_list_to_list exp)) in
    let final = ScmLambdaOpt ([], var, parseBody body) in
    final

    (* simple lambda *)
  |ScmPair(ScmSymbol "lambda", ScmPair(vars, body)) when (scm_is_list vars) ->
    let rec parseVars = function
      | ScmNil -> []
      | ScmPair(ScmSymbol hd, ScmNil) when not(List.mem hd reserved_word_list) -> [hd]
      | ScmPair(ScmSymbol hd, ScmSymbol tl) when not(List.mem hd reserved_word_list)
                                            && not(List.mem tl reserved_word_list)-> [hd; tl]
      | ScmPair(ScmSymbol hd, tl) -> [hd]@(parseVars tl)
      | _ -> raise (X_syntax_error (sexpr, "Expected var name in lambda param list")) in
    let parseBody = function
      |ScmPair(e, ScmNil) -> tag_parse_expression e
      | exp -> ScmSeq(List.map tag_parse_expression (scm_list_to_list exp)) in
    let vars = parseVars vars in
    if(not (all_different_strings vars))
      then raise (X_syntax_error (sexpr, "same var name used more than once"))
    else
    let final = ScmLambdaSimple(vars, parseBody body) in
    final
  (* optional arguments lambda *)
  |ScmPair(ScmSymbol "lambda", ScmPair(vars, body)) -> 
    let rec split_tail = function
      | a::[] -> [], a
      | a::b -> let heads, tail = split_tail b in
        (a::heads), tail
      | _ -> raise X_proper_list_error in
    let rec parseVars = function
      | ScmPair(ScmSymbol hd, ScmNil) when not(List.mem hd reserved_word_list) -> [hd]
      | ScmPair(ScmSymbol hd, ScmSymbol tl) when not(List.mem hd reserved_word_list)
                                            && not(List.mem tl reserved_word_list)-> [hd; tl]
      | ScmPair(ScmSymbol hd, tl) -> [hd]@(parseVars tl)
      | _ -> raise (X_syntax_error (sexpr, "Expected var name in lambda param list")) in
    let parseBody = function
      |ScmPair(e, ScmNil) -> tag_parse_expression e
      | exp -> ScmSeq(List.map tag_parse_expression (scm_list_to_list exp)) in
    let vars = parseVars vars in
    if(not (all_different_strings vars))
      then raise (X_syntax_error (sexpr, "same var name used more than once"))
    else
    let firsts, last = split_tail vars in
    let final = ScmLambdaOpt(firsts, last, parseBody body) in
    final


(* 2.1.6 Define *) 
  (* 1. Simple define
  2. MIT-style define *)
  | ScmPair(ScmSymbol("define"), ScmPair(ScmSymbol(name), ScmPair(exp, ScmNil))) -> 
      ScmDef(tag_parse_expression (ScmSymbol(name)), tag_parse_expression exp)

(* 2.1.7 Assignments *) 
  | ScmPair(ScmSymbol "set!", ScmPair(ScmSymbol (var), ScmPair (x, ScmNil))) ->
      ScmSet (ScmVar var, tag_parse_expression x)
  |ScmPair(ScmSymbol "set!", ScmPair(_ , ScmPair (x, ScmNil))) ->
      raise (X_syntax_error (sexpr, "Expected variable on LHS of set!"))
    

(* 2.1.9 Sequences *) 
  | ScmPair(ScmSymbol("begin"), ScmPair(e1, ScmNil)) -> (tag_parse_expression e1)
  | ScmPair(ScmSymbol("begin"), es) ->
    let rec parse_exps = function
      | ScmPair(e1, ScmNil) -> [(tag_parse_expression e1)]
      | ScmPair(e1, es) -> [(tag_parse_expression e1)]@(parse_exps es) 
      | x -> [tag_parse_expression x] in
    ScmSeq(parse_exps es)

  (* macro-expand quasiquote *)
  | ScmPair(ScmSymbol ("quasiquote"), ScmPair(expression ,ScmNil)) -> tag_parse_expression (expand_quasiquote expression)

  (* macro-expand and *) 
  | ScmPair(ScmSymbol("and"), sexpr) -> tag_parse_expression (expand_and sexpr)
  
  (* macro-expand MIT-define *) 
  | ScmPair(ScmSymbol("define"), ScmPair(ScmPair(ScmSymbol(var), args), body)) -> tag_parse_expression (expand_mitdefine (ScmSymbol(var)) args body)

  (* macro-expand cond *) 
  | ScmPair(ScmSymbol("cond"), ribs_list) -> tag_parse_expression (expand_cond ribs_list)

    (* 2.1.8 Applications *)
  | ScmPair(x, args) -> if (verify_nil_terminated args)
                        then (ScmApplic(tag_parse_expression x, make_argslist args)) 
                        else raise (X_syntax_error (args, "there is no nil exp"))

  | _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))



and macro_expand sexpr =
match sexpr with 


| ScmPair(ScmSymbol "let", ScmPair(ScmNil, ScmPair(body, ScmNil))) ->
    let exp = ScmPair(
      ScmPair(ScmSymbol "lambda", ScmPair(ScmNil, ScmPair(macro_expand body, ScmNil))),
      ScmNil) in exp

|ScmPair(ScmSymbol "let",ScmPair(bindings, body)) ->
    let vars = scm_map (fun x -> List.hd (scm_list_to_list x)) bindings in
    if(not (all_different vars)) 
      then raise (X_syntax_error(sexpr, "multipul definitions to same var in let"))
    else
    let vals = scm_map (fun x -> List.hd (List.tl (scm_list_to_list x))) bindings in 
    let lambda_exp = ScmPair(ScmSymbol "lambda",ScmPair(vars, macro_expand body)) in
    let applic_exp = ScmPair(lambda_exp, vals) in 
    applic_exp

| ScmPair(ScmSymbol "let*", ScmPair(ScmNil, body)) ->
    macro_expand (ScmPair(ScmSymbol "let", ScmPair(ScmNil, body)))

| ScmPair(ScmSymbol "let*", ScmPair(ScmPair(ScmPair(var1, val1), ScmNil), body)) ->
    macro_expand (ScmPair(ScmSymbol "let", ScmPair(ScmPair(ScmPair(var1, val1), ScmNil), body))) 

| ScmPair(ScmSymbol "let*",
    ScmPair(ScmPair(rib, ribs), body)) ->
      let new_exp = ScmPair(ScmSymbol ("let"),
                            ScmPair(ScmPair(rib, ScmNil),
                                    ScmPair(ScmPair(ScmSymbol ("let*"), ScmPair(ribs, body)), ScmNil))) in
     macro_expand new_exp
    
  |ScmPair(ScmSymbol "letrec", ScmPair(bindings, body)) ->
    let vars = scm_map (fun x -> List.hd (scm_list_to_list x)) bindings in
      if(not (all_different vars)) 
        then raise (X_syntax_error(sexpr, "multipul definitions to same var in let"))
    else
    let rec refine_defs = function
      | ScmPair(ScmPair(vari, _), rest) -> 
          ScmPair(ScmPair(vari,
                  ScmPair(
                          ScmPair(ScmSymbol "quote",
                          ScmPair(ScmSymbol "whatever", ScmNil)),
                          ScmNil)), (refine_defs rest))
      | _ -> ScmNil in
      
    let rec new_body bindings body = 
      match bindings with
      | ScmPair(ScmPair(vari, vali), rest) ->
        ScmPair(ScmPair(ScmSymbol "set!", ScmPair(vari, vali)), (new_body rest body))
      | _ -> body in
    let fixed_let = ScmPair(ScmSymbol "let", ScmPair((refine_defs bindings), (new_body bindings body))) in
    macro_expand fixed_let
  | _ -> sexpr


and verify_nil_terminated args = 
  match args with
  | ScmNil -> true
  | ScmPair(car, cdr) -> (verify_nil_terminated cdr)
  | _ -> false


and make_argslist args = match args with
                         | ScmNil -> []
                         | ScmSymbol(x) -> [tag_parse_expression (ScmSymbol(x))]
                         | ScmPair(car, cdr) -> tag_parse_expression car :: make_argslist cdr
                         | _ -> raise (X_syntax_error(args, "given bad exp"))


and make_list_loop sexprlist = match sexprlist with
                        | ScmNil -> []
                        | ScmPair(car, cdr) -> car :: make_list_loop cdr
                        | _ -> raise (X_syntax_error(sexprlist, "given empty list"))


and expand_quasiquote expression =
  match expression with
  | ScmPair(ScmSymbol("unquote"),ScmPair(sexpr,ScmNil)) -> sexpr
  | ScmPair(ScmSymbol("unquote-splicing"),ScmPair(sexpr,ScmNil)) ->
      ScmPair(ScmSymbol("quote"), ScmPair(ScmPair(ScmSymbol("unquote-splicing"),ScmPair(sexpr,ScmNil)), ScmNil))
  | ScmNil -> ScmPair(ScmSymbol("quote"),ScmPair(ScmNil,ScmNil))
  | ScmSymbol(a) -> ScmPair(ScmSymbol ("quote"), ScmPair(ScmSymbol(a), ScmNil))
  | ScmPair(ScmPair(ScmSymbol ("unquote-splicing"),ScmPair(sexpr , ScmNil)),b) ->
      ScmPair(ScmSymbol("append"),ScmPair(sexpr ,ScmPair((expand_quasiquote b),ScmNil)))
  | ScmPair(a,ScmPair(ScmSymbol ("unquote-splicing"),ScmPair(sexpr,ScmNil)))->
      ScmPair(ScmSymbol("cons"),ScmPair(expand_quasiquote a,ScmPair(sexpr,ScmNil)))
  | ScmPair(car, cdr) -> ScmPair(ScmSymbol "cons", ScmPair(expand_quasiquote car, ScmPair(expand_quasiquote cdr, ScmNil)))
  | ScmVector(l) -> ScmPair(ScmSymbol("list->vector"), ScmPair(expand_quasiquote (list_to_proper_list l), ScmNil))
  | _ -> expression


and expand_and sexpr =
  match sexpr with
  | ScmNil -> ScmBoolean(true)
  | ScmPair(car, ScmNil) -> car
  | ScmPair(car, cdr) -> ScmPair(ScmSymbol("if"), ScmPair(car, ScmPair(ScmPair(ScmSymbol("and"), cdr), ScmPair(ScmBoolean(false), ScmNil))))
  | _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))



and expand_cond ribs_list =
  match ribs_list with
  | ScmPair(ScmPair(test, ScmPair(ScmSymbol("=>"), body)), ScmNil) -> let if_expr = ScmPair(ScmSymbol("if"), ScmPair(ScmSymbol("value"), ScmPair(ScmPair(ScmPair(ScmSymbol("f"), ScmNil), ScmPair(ScmSymbol("value"), ScmNil)), ScmNil))) in
                                                        let lambda_expr = ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, body)) in
                                                        let args = ScmPair(ScmPair(ScmSymbol("value"), ScmPair(test, ScmNil)),
                                                                    ScmPair(ScmPair(ScmSymbol("f"), ScmPair(lambda_expr, ScmNil)), ScmNil)) in
                                                        ScmPair(ScmSymbol("let"), ScmPair(args, ScmPair(if_expr, ScmNil)))
  | ScmPair(ScmPair(test, ScmPair(ScmSymbol("=>"), body)), rest_ribs) ->  let res = expand_cond rest_ribs in
                                                              let ribs = (match res with
                                                                        | ScmNil -> ScmNil
                                                                        | _ -> ScmPair(res, ScmNil) )in
                                                              let rest = ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, ribs)) in
                                                              let if_expr = ScmPair(ScmSymbol("if"), ScmPair(ScmSymbol("value"), ScmPair(ScmPair (ScmPair (ScmSymbol("f"), ScmNil), ScmPair (ScmSymbol "value", ScmNil)), ScmPair(ScmPair(ScmSymbol("rest"), ScmNil), ScmNil)))) in
                                                              let lambda_expr = ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, body)) in
                                                              let args = ScmPair(ScmPair(ScmSymbol("value"), ScmPair(test, ScmNil)),
                                                                          ScmPair(ScmPair(ScmSymbol("f"), ScmPair(lambda_expr, ScmNil)),
                                                                          ScmPair(ScmPair(ScmSymbol("rest"), ScmPair(rest, ScmNil)), ScmNil))) in
                                                              ScmPair(ScmSymbol("let"), ScmPair(args, ScmPair(if_expr, ScmNil)))
  | ScmPair(ScmPair(ScmSymbol("else"), ScmPair(e1, ScmNil)), cont) -> e1
  | ScmPair(ScmPair(ScmSymbol("else"), body), cont) -> ScmPair(ScmSymbol("begin"), body)
  | ScmPair(ScmPair(test, body), rest_ribs) -> let res = expand_cond rest_ribs in
                                          let ribs = match res with
                                                    | ScmNil -> ScmNil
                                                    | _ -> ScmPair(res, ScmNil) in
                                                    ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(ScmPair(ScmSymbol("begin"), body), ribs)))
  | ScmNil -> ScmNil
  | _ -> raise (X_syntax_error (ribs_list, "ribs_list structure not recognized"))

and expand_mitdefine var args body =
  let exp = ScmPair(ScmSymbol("lambda"), ScmPair(args, body)) in
  ScmPair(ScmSymbol("define"), ScmPair(var, ScmPair(exp,ScmNil)))

end;; 

