#use "semantic-analyser.ml";;

exception X_this_should_not_happen;;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;


(* CONST TABLE *)

  let base_consts = [ScmVoid; ScmNil; ScmBoolean false; ScmBoolean true];;

  let rec make_consts sexpr = 
    match sexpr with
    | ScmSymbol(s) -> [ScmString(s); sexpr]
    | ScmVector(sexprs) -> (List.flatten (List.map
                                          (fun s -> make_consts s) sexprs)) @ [sexpr]
    (* | ScmPair(ScmSymbol "quote", cdr) -> make_consts cdr                                       *)
    | ScmPair(car, cdr) -> (make_consts car)@(make_consts cdr)@[sexpr]
    | _ -> [sexpr];;

  let rec find_consts ast =
      let handle_expr_list exprs = 
        let maped = List.map (fun e -> find_consts e) exprs in
        List.fold_left (fun w lst -> List.append lst w) [] maped in 
      match ast with
      | ScmConst'(x) -> make_consts x
      | ScmBoxSet'(_, val1) -> find_consts val1
      | ScmIf'(test, dit, dif) -> (find_consts test)@(find_consts dit)@(find_consts dif)
      | ScmSeq'(exprs) -> handle_expr_list exprs
      | ScmSet'(_, val1) -> find_consts val1
      | ScmDef'(_, val1) -> find_consts val1
      | ScmOr'(exprs) ->  handle_expr_list exprs
      | ScmLambdaSimple'(_, body) -> find_consts body
      | ScmLambdaOpt'(_, _, body) -> find_consts body
      | ScmApplic'(operator, operands) ->  (find_consts operator)@(handle_expr_list operands)
      | ScmApplicTP'(operator, operands) ->  (find_consts operator)@(handle_expr_list operands)
      | _ -> [];;
  
  let remove_duplicates lst =
    List.rev (List.fold_left (fun rest e -> 
                                  if (not (List.mem e rest))
                                  then e::rest
                                  else rest) [] lst);;
  
  let sob_size sexpr =
    match sexpr with
    | ScmVoid -> 1
    | ScmNil -> 1
    | ScmBoolean(_) -> 2
    | ScmChar(_) -> 2
    | ScmNumber(ScmRational(_,_)) -> 17
    | ScmNumber(ScmReal(_)) -> 9
    | ScmString(s) -> 9 + (String.length s)
    | ScmSymbol(_) -> 9 
    | ScmVector(expers) -> 9 + (List.length expers)*8
    | ScmPair(_,_) -> 17;;
  
  let rec make_offsets lst =
    match lst with
    | [] -> []
    | [e] -> [(e,0)]
    | e::rest -> 
              let prev_lst = make_offsets rest in
              let prev = List.hd prev_lst in
              [(e, (snd prev)+(sob_size (fst prev)))]@prev_lst;;

  let get_offset c ctbl = (List.assoc c ctbl);;

  let vector_macro sexprs ctbl = 
    match (List.length sexprs) with
    | 0 -> "MAKE_LITERAL_VECTOR "
    | _ -> 
        let pointers = List.fold_left (fun s e -> s^"const_tbl+ "^(string_of_int (get_offset e ctbl))^ ", ") "" sexprs in
        let macro = "MAKE_LITERAL_VECTOR "(*^(string_of_int (List.length sexprs))^", "*)^ pointers in
        let macro = String.sub macro 0 ((String.length macro) - 2) in
        macro;;

  let make_macro sexpr ctbl = 
    match sexpr with
      | ScmVoid -> "db T_VOID"
      | ScmNil -> "db T_NIL"
      | ScmBoolean(true) -> "db T_BOOL, 1"
      | ScmBoolean(false) -> "db T_BOOL, 0" 
      | ScmChar(c) -> "MAKE_LITERAL_CHAR ("^ (string_of_int(int_of_char c))^")"
      | ScmNumber(ScmReal(x)) -> "MAKE_LITERAL_REAL("^(string_of_float x)^")"
      | ScmNumber(ScmRational(n,d)) ->
                  "MAKE_LITERAL_RATIONAL("^(string_of_int n)^", "^(string_of_int d)^")"
      | ScmString(s) -> "MAKE_LITERAL_STRING \""^s^"\""
      | ScmSymbol(s) -> 
                let offset = get_offset (ScmString s) ctbl in
                "MAKE_LITERAL_SYMBOL(const_tbl+"^(string_of_int offset)^")"
      | ScmVector(sexprs) -> vector_macro sexprs ctbl
      | ScmPair(car,cdr) -> 
                let car_offset = get_offset car ctbl in
                let cdr_offset = get_offset cdr ctbl in
                "MAKE_LITERAL_PAIR(const_tbl+"^(string_of_int car_offset)^", const_tbl+"^(string_of_int cdr_offset)^")";;

  let create_costs_tbl asts = 
    let ctbl = List.map (fun ast -> find_consts ast) asts in
    let ctbl = List.flatten ctbl in
    let ctbl = base_consts@ctbl in
    let ctbl = remove_duplicates ctbl in
    let ctbl = make_offsets (List.rev ctbl) in
    let ctbl = List.rev ctbl in 
    let ctbl = List.map (fun (e,i) -> (e, (i, (make_macro e ctbl)))) ctbl in
    ctbl;;



(* FREE-VARS TABLE *)

let unitify = fun x -> ()
let car = fun x y -> x

let rec get_all_fvars_expr' expr'=
  let global_list = ref [] in
  let rec func expr' = 
    match expr' with
    | ScmVar'(VarFree(var)) -> (let a = global_list := List.append !global_list [var] in
                             unitify a)
    | ScmVar'(var) -> ()
    | ScmConst'(var) -> () (* should saparate to Sexpr and ScmVoid? *)
    | ScmBox'(var) -> ()
    | ScmBoxGet'(var) -> ()
    | ScmBoxSet'(var, expr) -> (func expr)
    | ScmIf'(test, dit, dif) -> (unitify (List.map func [test; dit; dif])) 
    | ScmSeq'(exprs) -> (unitify (List.map func exprs))
    | ScmSet'(set_var, set_val) -> (unitify (List.map func [ScmVar'(set_var); set_val])) (* to make sure *)
    | ScmDef'(def_var, def_val) -> (unitify (List.map func [ScmVar'(def_var); def_val])) (* to make sure *)
    | ScmOr'(exprs) -> (unitify (List.map func exprs))
    | ScmLambdaSimple'(params, body) -> (unitify (func body))
    | ScmLambdaOpt'(params, opt_param, body) -> (unitify (func body))
    | ScmApplic'(operator, args) -> (let a = [func operator] in
                                  let b = List.map func args in
                                  unitify [a; b])
    | ScmApplicTP'(operator, args) -> (let a = [func operator] in
                                    let b = List.map func args in
                                    unitify [a; b]) in

  let update_global_list = func expr' in
  car !global_list update_global_list;;


let unique_cons xs x = 
  if List.mem x xs 
  then xs
  else x :: xs

let remove_dups_from_left xs = List.rev (List.fold_left unique_cons [] xs)

let get_all_fvars_asts asts = List.flatten (List.map get_all_fvars_expr' asts) (* to make sure *)

let get_fvar_offset fvars_table fvar_name =
  try 
    (let (name, offset) = List.find (fun (name, offset) -> String.equal fvar_name name) fvars_table in
     offset)
  with Not_found -> (-1);;

let create_fvars_tbl asts =
  let init_fvars = [("boolean?",0); ("flonum?",1); ("rational?",2);
                       ("pair?",3); ("null?",4);("char?",5); ("string?",6);
                       ("procedure?",7); ("symbol?",8);  ("string-length",9) ;
                       ("string-ref",10); ("string-set!",11); ("make-string",12);
                       ("symbol->string",13); ("char->integer",14); 
                       ("integer->char",15); ("exact->inexact",16); ("eq?",17);
                       ("+",18); ("*",19); ("/",20); ("=",21); ("<",22);
                       ("numerator",23) ; ("denominator",24) ; ("gcd",25);
                       ("apply",26); ("car",27); ("cdr",28); ("cons", 29); ("set-car!",30);("set-cdr!",31)] in
  let rec add_fvars fvars_main_table fvars_list = 
    let add_fvar fvars_table fvar = 
      let fvar_offset = get_fvar_offset fvars_table fvar in
      if fvar_offset = (-1)   (* doesn't exist in the curr fvars table *)
      then List.append fvars_table [(fvar, (List.length fvars_table))]
      else fvars_table in
    match fvars_list with
    | fvar_name :: rest -> add_fvars (add_fvar fvars_main_table fvar_name) rest
    | [] -> fvars_main_table in
  let fvars_from_ast = remove_dups_from_left (get_all_fvars_asts asts) in
  add_fvars init_fvars fvars_from_ast;;



(* GENERATOR *)

let label_counter = ref 0;;

let rec get_expr_offset const const_table = 
  match const_table with
  | tuple :: rest -> (match tuple with
                      | (sexp, (offset, str)) -> (if (sexpr_eq const sexp)
                                                  then offset
                                                  else (get_expr_offset const rest)))
  | [] -> (-1);;


let rec main_generate consts fvars depth expr' =
  match expr' with
  | ScmConst'(c) -> (const_helper consts c)
  | ScmVar'(v) -> (var_helper fvars depth v)
  | ScmSeq'(lst) -> (seq_helper consts fvars depth lst)
  | ScmSet'(exp_var, exp_val) -> (set_helper consts fvars depth exp_var exp_val)
  | ScmDef'(exp_var, exp_val) -> (def_helper consts fvars depth exp_var exp_val)
  | ScmOr'(lst) -> (or_helper consts fvars depth lst)
  | ScmIf'(test, dit, dif) -> (if_helper consts fvars depth test dit dif)
  | ScmBox'(v) -> (box_helper v fvars depth)
  | ScmBoxSet'(v, val1) -> (box_set_helper v val1 consts fvars depth)
  | ScmBoxGet'(v) -> (box_get_helper v consts fvars depth)
  | ScmLambdaSimple'(params, body) -> (lambda_simple_helper consts fvars depth params body)
  | ScmLambdaOpt'(params, opt_param, body) -> (lambda_opt_helper consts fvars depth params opt_param body)
  | ScmApplic'(proc, args) -> applic_helper proc args consts fvars depth
  | ScmApplicTP'(proc, args) -> applicTP_helper proc args consts fvars depth
  (* |_ -> raise X_this_should_not_happen *)


  and box_helper v fvars depth =
    (var_helper fvars depth v) ^
    "push r11
    MALLOC r11, 8
    mov qword [r11], rax
    mov rax, r11
    pop r11\n"
                  
  and box_get_helper v consts fvars depth = 
    (var_helper fvars depth v) ^
    "mov rax, qword[rax]\n"

  and box_set_helper v val1 consts fvars depth = 
    (main_generate consts fvars depth val1)^
    "push rax
    "^(var_helper fvars depth v) ^
    "pop qword[rax]
    mov rax, SOB_VOID_ADDRESS
    "

  and applic_helper rator rands consts fvars depth = 
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    let str_num = (string_of_int current_label_counter) in
    let magic = "push SOB_NIL_ADDRESS\n" in
    let rands_gen = List.fold_left (fun acc rand -> (main_generate consts fvars depth  rand)^
    "push rax
    "^acc) "" rands in
    let rest_gen = 
    "push "^(string_of_int (List.length rands))^"
    "^(main_generate consts fvars depth rator)^" 
    .check_if_closur:
    cmp byte[rax], T_CLOSURE
    je call_proc"^str_num^"
    mov rax, 1
    mov rdx, 0
    div rdx 
    call_proc"^str_num^":
    mov rbx, qword [rax+TYPE_SIZE]
    push rbx
    CLOSURE_CODE rax, rax
    call rax
    add rsp, 8*1
    pop rbx
    lea rsp, [rsp+8*rbx]
    pop rbx
    " 
    in "applic"^str_num^":
    "^magic^rands_gen^rest_gen
  
  and applicTP_helper rator rands consts fvars depth =
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    let str_num = (string_of_int current_label_counter) in
    let arg_count = (List.length rands) in
    let magic = "push SOB_NIL_ADDRESS\n" in
    let rands_gen = List.fold_left (fun acc rand -> (main_generate consts fvars depth  rand)^
    "push rax
    "^acc) "" rands in
    let rest_gen = 
    "push "^(string_of_int arg_count)^"
    "^(main_generate consts fvars depth rator)^"
    .check_if_closur: 
    cmp byte[rax], T_CLOSURE
    je call_proc"^str_num^"
    mov rax, 1
    mov rdx, 0
    div rdx 
    call_proc"^str_num^":
      mov rbx, qword [rax+TYPE_SIZE]
      push rbx
      push qword[rbp+8*1]
      SHIFT_FRAME "^(string_of_int (arg_count+3+2))^" 
      CLOSURE_CODE rax, rax
      jmp rax
      "
      in "applicTP"^str_num^":
      "^magic^rands_gen^rest_gen

  and const_helper consts c = 
    let offset = string_of_int (get_expr_offset c consts) in
    "mov rax, const_tbl+" ^ offset ^ "\n"

  and var_helper fvars depth v =
    match v with
    | VarFree(name) -> "mov rax, qword FVAR("^(string_of_int (get_fvar_offset fvars name))^")\n " 
    | VarParam(name, minor) -> "mov rax, qword [rbp + "^(string_of_int (8*(4+minor)))^"]\n"
    | VarBound(name, major, minor) ->
      "mov rax, qword [rbp + 16]
      mov rax, qword [rax + "^(string_of_int (8*major))^"]
      mov rax, qword [rax + "^(string_of_int (8*minor))^"]\n"

  and seq_helper consts fvars depth lst =
    List.fold_left (fun acc curr -> acc ^ "\n" ^ (main_generate consts fvars depth curr) ^ "\n") "" lst

  and set_helper consts fvars depth exp_var exp_val =
    match exp_var with
    | VarFree(name) -> (main_generate consts fvars depth exp_val) ^
                        "mov qword FVAR("^(string_of_int (get_fvar_offset fvars name))^ "), rax \n
                        mov rax, SOB_VOID_ADDRESS \n"
    | VarParam(name, minor) -> (main_generate consts fvars depth exp_val) ^
                                "mov qword [rbp + " ^ (string_of_int (8*(4+minor))) ^ "], rax \n
                                mov rax, SOB_VOID_ADDRESS \n"
    | VarBound(name, major, minor) -> (main_generate consts fvars depth exp_val) ^ 
                                      "mov rbx, qword [rbp + 16]
                                      mov rbx, qword [rbx + " ^ (string_of_int (8*major)) ^ "]
                                      mov qword [rbx + " ^ (string_of_int (8*minor)) ^ "], rax
                                      mov rax, SOB_VOID_ADDRESS \n"

  and def_helper consts fvars depth exp_var exp_val =
    set_helper consts fvars depth exp_var exp_val

  and or_helper consts fvars depth lst =
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    (List.fold_left (fun acc curr -> acc ^ (main_generate consts fvars depth curr) ^ 
                                      " cmp rax, SOB_FALSE_ADDRESS \n jne Lexit_" ^ 
                                      (string_of_int current_label_counter) ^ " \n") "" lst) ^
                                      "Lexit_" ^ (string_of_int current_label_counter) ^ ":\n"

  and if_helper consts fvars depth test dit dif =
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    let else_label = "Lelse_" ^ (string_of_int current_label_counter) in 
    let exit_label = "Lexit_" ^ (string_of_int current_label_counter) in 
    (main_generate consts fvars depth test) ^ "\n" ^
    "cmp rax, SOB_FALSE_ADDRESS\n" ^
    "je " ^ (else_label) ^ "\n" ^
    (main_generate consts fvars depth dit) ^ "\n" ^
    "jmp " ^ (exit_label) ^ "\n" ^
    (else_label) ^ ":\n" ^
    (main_generate consts fvars depth dif) ^ "\n" ^
    (exit_label) ^ ":\n";

  and lambda_simple_helper consts fvars depth params body =
    if depth = 0
    then (top_lambda_helper consts fvars (depth+1) body)
    else (nested_lambda_helper consts fvars (depth+1) body)

  and lambda_opt_helper consts fvars depth params opt_param body =
    if depth = 0
    then (top_lambda_opt_helper consts fvars (depth+1) params opt_param body)
    else (nested_lambda_opt_helper consts fvars (depth+1) params opt_param body)


  (* lambdas helpers *)
  and top_lambda_helper consts fvars depth body =
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    let str_num = (string_of_int current_label_counter) in
      ";creating lambda top layer:
      MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode"^str_num^")
      jmp Lcont"^str_num^"
      Lcode"^str_num^":
      push rbp
      mov rbp, rsp
      "^(main_generate consts fvars depth body)^
      "leave
      ret
      Lcont"^str_num^":\n"
  
  and nested_lambda_helper consts fvars depth body =
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    let str_num = (string_of_int current_label_counter) in
    let ext_env = 
      ";ext_env code\n"^
      "MALLOC rdx, WORD_SIZE*"^(string_of_int depth)^"\n"^
      "; store old env in rbx \n"^
      "mov rbx, qword[rbp+ 8*2]\n"^
      "mov r8, rdx ;store 0 index of ext_env\n"^
      "add rdx, WORD_SIZE ;rdx point to index 1 ext_env\n"^
      "checking"^str_num^":\n"^
      "mov rcx, "^(string_of_int (depth-2))^" ; num of iterations \n"^
      "cmp rcx, 0\n"^
      "je cont_ext_env"^str_num^" ;if (depth-1) is 0 then there is nothing to copy besides params\n"^
      "copy_ext_env_loop"^str_num^":\n"^
      "mov r10, qword[rbx]\n"^
      "mov [rdx], r10 ; now extEnv[i+1]= oldEnv[i]\n"^
      "add rbx, WORD_SIZE ; add 8 to the next vector oldEnv\n"^
      "add rdx, WORD_SIZE ; add 8 to the next vector extEnv\n"^
      "loop copy_ext_env_loop"^str_num^"\n"^
      ";copy the oldEnv params to extEnv index 0\n"^
      "cont_ext_env"^str_num^":\n"^
      "mov rdx, r8 ;restore index 0\n"^
      "mov qword[rdx], SOB_NIL_ADDRESS ;in case n==0\n"^
      "mov rcx, qword[rbp+ 8*3] ;rcx = num of params\n"^
      "check1"^str_num^":\n"^
      "cmp rcx, 0\n"^
      "je cont_allocate_closure"^str_num^"\n"^
      "check2"^str_num^":\n"^
      "mov r11, rcx ;unchange rcx\n"^
      "shl r11, 3 ; mutiply n*8-> number of bytes to allocate\n"^
      "inc r11 ; saving space for the magic\n"^
      "MALLOC r10, r11 ;allocating memory for index 0 in extEnv\n"^
      "mov [rdx], r10 ; now ext env 0 pointing to the allocated memory\n"^
      "mov rdx, r10 ; rdx is the start of allocated memory' the atcual vector of ext env 0\n"^
      "mov r14, 32 ; 8*4-> qwors[rbp+ 8*4]=A0\n"^
      "copy_params_ext_env_loop"^str_num^":\n"^
      "mov rbx, qword[rbp+r14] ; rbx= A0\n"^
      "mov [rdx], rbx ; Ai -> extEnx[0][i] \n"^
      "add r14, WORD_SIZE\n"^
      "add rdx, WORD_SIZE\n"^
      "loop copy_params_ext_env_loop"^str_num^"\n"^
      "mov qword[rdx], SOB_NIL_ADDRESS ; magic at the and of extEnv 0\n"^
      "cont_allocate_closure"^str_num^":\n"^
      ";done extending env\n" in
    let lcode = 
      "Lcode"^str_num^":\n"^
      "push rbp\n"^
      "mov rbp, rsp\n"^
      (main_generate consts fvars depth body)^"\n"^
      "leave\n"^
      "ret\n"^
      ";end of body \n"^
      "Lcont"^str_num^":\n" in

    ";creating lambda nested layers\n"^ ext_env ^
    "MAKE_CLOSURE(rax, r8, Lcode"^str_num^")\n" ^
    "jmp Lcont"^str_num^"\n"^lcode;



  and top_lambda_opt_helper consts fvars depth params opt_param body =
    let params_length = (List.length params) in
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    let str_num = (string_of_int current_label_counter) in  
    let adjust_stack = 
      "push rbp\n"^
      "mov rbp, rsp\n"^
      "mov rbx, qword[rbp+ 8*3] ; rbp=n (num of initial params)\n"^
      "mov r8, "^(string_of_int (List.length params))^" ; r8= num of must params\n"^
      "cmp rbx, r8 ;comparing the numbers of params with the number of the must params \n"^
      "je after_adjust"^str_num^"\n"^
      ";now code to adjust the params \n"^
      "mov rcx, rbx ; ecx in now num of params \n"^
      "sub rcx, r8; ecx now is num of iterations=> (num of params)- (num of must params)\n"^
      "add rbx, 3  ; \n"^
      "shl rbx, 3 ; mutiply (n+3)*8-> distance from the An to rbx\n"^
      "mov r9, [rbp+rbx] ;r9=A0\n"^
      "mov r10, [rbp+rbx+WORD_SIZE] ;r10 holds the magic\n"^
      "MAKE_PAIR(r11, r9, r10) ; r11 now point to the pair(An, SOB_NIl_ADDRESS\n"^
      "sub rcx, 1 ; one less iteraition\n"^
      "cmp rcx, 0\n"^
      "je cont_done_list"^str_num^"\n"^
      "sub rbx, WORD_SIZE\n"^
      "make_list_loop"^str_num^":\n"^
      ";Looop invariant r11 always points to the last Pair\n"^
      "mov r8, r11 ; now r8 point to the last Pair\n"^
      "mov r9, [rbp+rbx]; r9 point to A(i-1)\n"^
      "MAKE_PAIR(r11, r9, r8)\n"^
      "sub rbx, WORD_SIZE\n"^
      "loop make_list_loop"^str_num^"\n"^
      "cont_done_list"^str_num^":\n"^
      ";now r11 point to the Pairs. to the list\n"^
      "mov qword [rbp + (4+"^(string_of_int params_length)^")*8], r11 ;the pointer to the list is right above the last must params\n"^
      "mov qword [rbp + (4+"^(string_of_int (params_length+1))^")*8], SOB_NIL_ADDRESS ; magic above the list\n"^
      "after_adjust"^str_num^":\n" in
    let lcode =
      (main_generate consts fvars depth body)^
      "leave\n"^
      "ret\n"^
      ";end of the body (closure)\n"^
      "Lcont"^str_num^":\n" in

    ";creating lambda_opt top layer:\n"^
    "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode"^str_num^")\n"^
    "jmp Lcont"^str_num^"\n"^
    "Lcode"^str_num^":\n"^
    adjust_stack ^ lcode;

  and nested_lambda_opt_helper consts fvars depth params opt_param body =
    let params_length= (List.length params) in
    let () = (label_counter := !label_counter+1) in
    let current_label_counter = !label_counter in
    let str_num = (string_of_int current_label_counter) in
    let ext_env =
      ";ext_env code\n"^
      "MALLOC rdx, WORD_SIZE*"^(string_of_int depth)^"\n"^
      "; store old env in rbx \n"^
      "mov rbx, qword[rbp+ 8*2]\n"^
      "mov r8, rdx ;store 0 index of ext_env\n"^
      "add rdx, WORD_SIZE ;rdx point to index 1 ext_env\n"^
      "checking"^str_num^":\n"^
      "mov rcx, "^(string_of_int (depth-2))^" ;num of iterations \n"^
      "cmp rcx, 0\n"^
      "je cont_ext_env"^str_num^" ;if (depth-1) is 0 then there is nothing to copy besides params\n"^
      "copy_ext_env_loop"^str_num^":\n"^
      "mov r10, qword[rbx]\n"^
      "mov [rdx], r10 ; now extEnv[i+1] = oldEnv[i]\n"^
      "add rbx, WORD_SIZE ; add 8 to the next vector oldEnv\n"^
      "add rdx, WORD_SIZE ; add 8 to the next vector extEnv\n"^
      "loop copy_ext_env_loop"^str_num^"\n"^
      ";copy the oldEnv params to extEnv index 0\n"^
      "cont_ext_env"^str_num^":\n"^
      "mov rdx, r8 ;restore index 0\n"^
      "mov qword[rdx], SOB_NIL_ADDRESS ;in case n==0\n"^
      "mov rcx, qword[rbp+ 8*3] ;rcx = num of params\n"^
      "check1"^str_num^":\n"^
      "cmp rcx, 0\n"^
      "je cont_allocate_closure"^str_num^"\n"^
      "check2"^str_num^":\n"^
      "mov r11, rcx ;unchange rcx\n"^
      "shl r11, 3 ; multiply n*8-> number of bytes to allocate\n"^
      "MALLOC r10, r11 ;allocating memory for index 0 in extEnv\n"^
      "mov [rdx], r10 ; now ext env 0 pointing to the allocated memory\n"^
      "mov rdx, r10 ; rdx is the start of allocated memory the atcual vector of ext env 0\n"^
      "mov r14, 32 ; 8*4-> qwors[rbp+ 8*4]=A0\n"^
      "copy_params_ext_env_loop"^str_num^":\n"^
      "mov rbx, qword[rbp+r14] ; rbx= A0\n"^
      "mov [rdx], rbx ; Ai -> extEnx[0][i] \n"^
      "add r14, WORD_SIZE\n"^
      "add rdx, WORD_SIZE\n"^
      "loop copy_params_ext_env_loop"^str_num^"\n"^
      "cont_allocate_closure"^str_num^":\n"^
      ";done extending env\n" in
    let adjust_stack = 
      "push rbp\n"^
      "mov rbp, rsp\n"^
      "mov rbx, qword[rbp+ 8*3] ; rbp=n (num of initial params)\n"^
      "mov r8, "^(string_of_int (List.length params))^" ; r8 = num of must params\n"^
      "cmp rbx, r8 ;comparing the numbers of params with the number of the must params \n"^
      "je after_adjust"^str_num^"\n"^
      ";now code to adjust the params \n"^
      "mov rcx, rbx ; ecx in now num of params \n"^
      "sub rcx, r8; ecx now is num of iterations=> (num of params)- (num of must params)\n"^
      "add rbx, 3  ; \n"^
      "shl rbx, 3 ; mutiply (n+3)*8-> distance from the An to rbx\n"^
      "mov r9, [rbp+rbx] ;r9=A0\n"^
      "mov r10, [rbp+rbx+WORD_SIZE] ;r10 holds the magic\n"^
      "MAKE_PAIR(r11, r9, r10) ; r11 now point to the pair(An, SOB_NIL_ADDRESS)\n"^
      "sub rcx, 1 ; one less iteraition\n"^
      "cmp rcx, 0\n"^
      "je after_set_list"^str_num^"\n"^
      "sub rbx, WORD_SIZE\n"^
      "make_list_loop"^str_num^":\n"^
      ";Looop invariant r11 always points to the last Pair\n"^
      "mov r8, r11 ; now r8 point to the last Pair\n"^
      "mov r9, [rbp+rbx]; r9 point to A(i-1)\n"^
      "MAKE_PAIR(r11, r9,r8)\n"^
      "sub rbx, WORD_SIZE\n"^
      "loop make_list_loop"^str_num^"\n"^
      "after_set_list"^str_num^":\n"^
      ";now r11 point to the Pairs. to the list\n"^
      "mov qword [rbp + (4+"^(string_of_int params_length)^")*8], r11 ;the pointer to the list is right above the last must params\n"^
      "mov qword [rbp + (4+"^(string_of_int (params_length+1))^")*8], SOB_NIL_ADDRESS ; magic above the list\n"^
      "after_adjust"^str_num^":\n" in
    let lcode =
      (main_generate consts fvars depth body)^
      "leave\n"^
      "ret\n"^
      ";end of the body (closure)\n"^
      "Lcont"^str_num^":\n" in

    ";creating lambda_opt nested layers:\n"^
    ext_env ^ "MAKE_CLOSURE(rax, r8, Lcode"^str_num^")\n"^
    "jmp Lcont"^str_num^"\n"^
    "Lcode"^str_num^":\n" ^
    adjust_stack ^ lcode;



module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = create_costs_tbl asts;;
  let make_fvars_tbl asts = create_fvars_tbl asts;;
  let generate consts fvars e = main_generate consts fvars 0 e;;
end;;

