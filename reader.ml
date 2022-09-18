(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

let rec pow a exp = 
    match exp with 
        | 0 -> 1
        | 1 -> a
        | n -> a*pow a (exp-1);;

let sign = function 
  | Some('-') -> (-1)
  | _ -> 1;;
  
type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;

(* turns snything nt found to () *)
type string_part =
  | Static of string
  | Dynamic of sexpr;;

let unitify nt = pack nt (fun _ -> ());;

let left_paren = (char '(');;
let right_paren = (char ')');;
let dot_char = (char '.');;

let quote = (word "\'");;
let quasi_quote = (word "`");;
let unquote = (word ",");;
let splice = (word ",@");;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str

(*
------------ comment ------------
*)

and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str

and nt_line_comment str = 
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end_of_line_or_file in (* any char exept '\n' or EOI *)
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end_of_line_or_file) in
  let nt1 = unitify nt1 in
  nt1 str

and nt_paired_comment str = 
  let nt1 = char '{' in
  let nt2 = disj_list [unitify nt_char;
                       unitify nt_string;
                       unitify nt_comment] in
  let nt3 = disj nt2 (unitify (disj (char '{') (char '}'))) in
  let nt4 = unitify (diff nt_any nt3) in
  let nt4 = disj nt4 nt2 in
  let nt4 = star nt4 in
  let nt5 = char '}' in
  let nt1 = unitify (caten nt1 (caten nt4 nt5)) in
  nt1 str

and nt_sexpr_comment str =
  let nt1 = unitify (caten (word "#;") nt_sexpr) in
  nt1 str

and nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1


(*
------------ number ------------
*)

and nt_digit str = 
  let nt1 = range '0' '9' in
  let nt1 = pack nt1 (fun c -> (int_of_char c) - (int_of_char '0')) in
  nt1 str
and nt_natural str =  
  let nt1 = plus nt_digit in
  let nt1 = pack nt1 (fun ds ->
                        List.fold_left
                        (fun n d -> 10 * n + d)
                        0
                        ds) in
  nt1 str
and nt_int str =
  let nt1 = maybe (one_of "+-") in
  let nt1 = caten nt1 nt_natural in
  let nt1 = not_followed_by nt1 (one_of "./eE*") in
  let nt1 = pack nt1 (fun (s, n)-> (sign s)*n) in
  nt1 str

and nt_frac str =
  let nt1 = maybe (one_of "+-") in
  let nt1 = caten nt1 nt_natural in
  let nt1 = pack nt1 (fun (s, n)-> (sign s)*n) in
  let nt1 = caten nt1 (char '/') in
  let nt1 = pack nt1 (fun (n,_)-> n) in
  let nt2 = only_if nt_natural (fun n-> n!=0) in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (n,d)->ScmRational (n / (gcd n d),d / (gcd n d))) in
  nt1 str

and nt_integer_part str = 
  let nt_digits = plus nt_digit in
  let nt_digits = pack nt_digits (fun ds ->
                                    List.fold_left
                                    (fun n d -> 10.0 *. n +. (float_of_int d))
                                    0.0
                                    ds) in
  nt_digits str

and nt_mantissa str =
  let nt1 = plus nt_digit in
  let nt1 = pack nt1 (fun ds ->
                        List.fold_right
                        (fun d n -> (n +. (float_of_int d)) /. 10.0)
                        ds
                        0.0) in
  nt1 str

and nt_exponent_token str =
  let nt1 = unitify (word_ci "e") in
  let nt2 = word "*10" in
  let nt3 = disj (word "**") (word "^") in
  let nt2 = unitify (caten nt2 nt3) in
  let nt1 = disj nt1 nt2 in
  nt1 str

and nt_exponent str = 
  let nt1 = caten nt_exponent_token nt_int in
  let nt1 = pack nt1 (fun (_, e)-> Float.pow 10. (float_of_int e)) in
  nt1 str

and nt_float_c str = 
  let nt1 = caten nt_integer_part nt_exponent in
  let nt1 = pack nt1 (fun (ip, e) -> ip*.e) in
  nt1 str

and nt_float_b str = 
  let nt1 = maybe nt_exponent in
  let nt1 = pack nt1 (function
                        | Some(e) -> e
                        |_ -> 1.0 ) in
  let nt2 = caten (char '.') nt_mantissa in
  let nt2 = pack nt2 (fun (_, m) -> m) in
  let nt2 = caten nt2 nt1 in
  let nt2 = pack nt2 (fun (m,e)-> m *. e)
  in nt2 str

and nt_float_a str = 
  let nt_e = maybe nt_exponent in
  let nt_e = pack nt_e (function
                        | Some(e) -> e
                        |_ -> 1.0 ) in
  let nt_m = maybe nt_mantissa in 
  let nt_m = pack nt_m (function
                        | Some(m) -> m
                        |_ -> 0.0 ) in
  let nt1 = caten nt_integer_part (char '.') in
  let nt1 = pack nt1 (fun (ip, _)-> ip) in
  let nt1 = caten (caten nt1 nt_m) nt_e in
  let nt1 = pack nt1 (fun ((ip, m), e)-> (ip +. m) *. e) in
  nt1 str

and nt_float str = 
  let nt1 = maybe (one_of "+-") in
  let nt2 = disj (disj nt_float_a nt_float_b) nt_float_c in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (o,n)->(float_of_int (sign o))*.n) in
  let nt1 = pack nt1 (fun n-> ScmReal n) in
  nt1 str
and nt_number str =
  let nt1 = pack nt_int (fun n-> ScmNumber(ScmRational (n,1))) in
  let nt2 = pack nt_float (fun f -> ScmNumber f) in
  let nt3 = pack nt_frac (fun f -> ScmNumber f) in
  let nt1 = disj (disj nt1 nt2) nt3 in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  (* let nt1 = not_followed_by nt1 (diff nt_any (one_of "eE*")) in *)
  nt1 str

(*
------------ boolean ------------
*)

and nt_boolean str = 
  let nt1 = word_ci "#f" in
  let nt1 = pack nt1 (fun _-> false) in
  let nt2 = word_ci "#t" in
  let nt2 = pack nt2 (fun _-> true) in
  let nt1 = disj nt1 nt2 in
  let nt1 = pack nt1 (fun b -> ScmBoolean b) in
  nt1 str


(*
------------ symbols ------------
*)

and nt_char_simple str = 
  let nt1 = only_if nt_any (fun c -> (int_of_char c) > 32) in
  let nt1 = pack nt1 (fun c-> ScmChar c) in
  nt1 str

and make_named_char char_name ch =
  let nt_name = word_ci char_name in
  let nt_name = pack nt_name (fun _ -> ScmChar ch) in
  nt_name

and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "nul" '\000');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str

and nt_hex_char str =
  let nt1 = range '0' '9' in
  let nt1 = pack nt1 (let delta = int_of_char '0' in
                      fun c -> (int_of_char c) - delta) in
  let nt2 = range_ci 'a' 'f' in
  let nt2 = pack nt2 (let delta = int_of_char 'a'- 10 in
                      fun c -> (int_of_char (lowercase_ascii c) - delta)) in
  let nt1 = disj nt1 nt2 in
  nt1 str

and nt_hexadecimal_char str = 
  let nt1 = plus nt_hex_char in
  let nt1 = pack nt1 (fun ds -> 
                        List.fold_left
                        (fun x y -> x * 16 + y)
                        0
                        ds) in
  let nt1 = caten (char 'x') nt1 in
  let nt1 = pack nt1 (fun (_, x)-> ScmChar(char_of_int x)) in 
  nt1 str

and nt_char str = 
  let nt1 = disj (disj nt_hexadecimal_char nt_char_named) nt_char_simple in
  let nt1 = caten (word "#\\") nt1 in
  let nt1 = not_followed_by nt1 (range_ci 'a' 'z') in
  let nt1 = pack nt1 (fun (_, sc)-> sc) in
  nt1 str

and nt_symbol_char str = 
  let nt1 = range '0' '9' in
  let nt2 = range_ci 'a' 'z' in
  let nt3 = one_of "!$^*-_=+<>?/:" in
  let nt1 = disj (disj nt1 nt2) nt3 in
  nt1 str

and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str


(*
------------ string ------------
*)

and nt_hex_digit str = 
  nt_hex_char str

and nt_hex_nat str =
  let nt = plus nt_hex_digit in
  let nt = pack nt
             (fun digits ->
               List.fold_left
                 (fun num digit -> 16 * num + digit)
                 0
                 digits) in
  nt str
and nt_string_literal_char str = 
  let nt1 = diff nt_any (one_of "\\\"~") in
  nt1 str
and make_nt_string_meta_char str ch =
  pack (word_ci str) (fun _ -> ch)
and nt_string_meta_char str = 
  let nt1 = disj_list [ make_nt_string_meta_char "\\\\" '\\';
                        make_nt_string_meta_char "\\\"" '"';
                        make_nt_string_meta_char "\\t" '\t';
                        make_nt_string_meta_char "\\n" '\n';
                        make_nt_string_meta_char "\\r" '\r';
                        make_nt_string_meta_char "\\f" '\012';
                        make_nt_string_meta_char "~~" '~' ] in
  nt1 str
  
and nt_string_hex_char str =
  let nt1 = caten (word "\\x") (caten nt_hex_nat (char ';')) in
  let nt1 = pack nt1 (fun (_, (n, _)) -> n) in
  let nt1 = only_if nt1 (fun n -> n < 256) in
  let nt1 = pack nt1 char_of_int in
  nt1 str
and nt_string_dynamic_part str =
  let nt1 = caten (word "~{") (caten nt_sexpr (char '}')) in
  let nt1 = pack nt1 (fun (_, (sexpr, _)) -> sexpr) in
  let nt1 = pack nt1
              (fun sexpr ->
                ScmPair(ScmSymbol "format",
                        ScmPair(ScmString "~a",
                                ScmPair(sexpr, ScmNil)))) in
  let nt1 = pack nt1 (fun sexpr -> Dynamic sexpr) in
  nt1 str
and nt_string_static_part str =
  let nt1 = disj_list [nt_string_literal_char;
                       nt_string_meta_char;
                       nt_string_hex_char] in
  let nt1 = pack (plus nt1) list_to_string in
  let nt1 = pack nt1 (fun str -> Static str) in
  nt1 str
and nt_string_part str =
  let nt1 = disj nt_string_static_part nt_string_dynamic_part in
  nt1 str
and nt_string str =
  let nt1 = char '\"' in
  let nt2 = star nt_string_part in
  let nt1 = caten nt1 (caten nt2 nt1) in
  let nt1 = pack nt1 (fun (_, (parts, _)) -> parts) in
  let nt1 = pack nt1
              (function
               | [] -> ScmString ""
               | [Static str] -> ScmString str
               | [Dynamic sexpr] -> sexpr
               | parts ->
                  let rest =
                    (List.fold_right
                       (fun car cdr ->
                         ScmPair((match car with
                                  | Static str -> ScmString str
                                  | Dynamic sexpr -> sexpr),
                                 cdr))
                       parts
                       ScmNil) in
                  ScmPair(ScmSymbol "string-append", rest)) in
  nt1 str


and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str

and nt_list_improper str =
    let nt1 = caten (caten (caten (caten left_paren (plus nt_sexpr)) dot_char) nt_sexpr) right_paren in
    let nt1 = pack nt1 (fun (((((l, sexps), d), sexp), r)) -> List.fold_right
                                                                (fun a b -> ScmPair(a, b))
                                                                sexps
                                                                sexp) in
    nt1 str

and nt_list_proper str =
  let nt3 = caten (caten left_paren nt_skip_star) right_paren in
  let nt3 = pack nt3 (fun _ -> ScmNil) in
  let nt1 = caten (caten left_paren (star nt_sexpr)) right_paren  in
  let nt1 = pack nt1 (fun ((_, s), _) -> List.fold_right
                                          (fun a b -> ScmPair(a, b))
                                          s
                                          ScmNil) in
  let nt1 = disj nt3 nt1 in
  nt1 str

and nt_list str =
  let nt1 = disj nt_list_proper nt_list_improper in
  nt1 str

and quoted str = pack (caten quote nt_sexpr) (fun (name, str) -> ScmPair(ScmSymbol("quote"), ScmPair(str, ScmNil))) str
and quasi_quoted str = pack (caten quasi_quote nt_sexpr) (fun (name, str) -> ScmPair(ScmSymbol("quasiquote"), ScmPair(str, ScmNil))) str
and unquoted str = pack (caten unquote nt_sexpr) (fun (name, str) -> ScmPair(ScmSymbol("unquote"), ScmPair(str, ScmNil))) str
and unquoted_and_spliced str = pack (caten splice nt_sexpr) (fun (name, str) -> ScmPair(ScmSymbol("unquote-splicing"), ScmPair(str, ScmNil))) str
and nt_quoted_forms str =
  let nt1 = disj_list [quoted;
                      quasi_quoted;
                      unquoted;
                      unquoted_and_spliced] in
  nt1 str

and nt_sexpr str =
  let nt1 =
    disj_list [nt_symbol;nt_number; nt_boolean; nt_char; 
               nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;
  

end;; (* end of struct Reader *)


let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;



