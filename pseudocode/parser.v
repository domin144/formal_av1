Require Import Bool Arith List String Ascii ZArith.
Import ListNotations.

Require Import formal_av1.pseudocode.definitions.

Module Parser.

(* From logic foundations *)

Inductive operator_parsing_parameters :=
  | opp : any_operator -> string -> operator_parsing_parameters.

Inductive binding_direction :=
  | bd_left_to_right
  | bd_right_to_left
  | bd_unary_left
  | bd_unary_right.

(* Operator parsing parameters. Ordered by decreasing precedence. *)
Definition opps :
    list (binding_direction * (list operator_parsing_parameters)) :=
  [
    ( bd_right_to_left,
      [
        opp (ano_aso aso_assign) "=";
        opp (ano_aso aso_addassign) "+=";
        opp (ano_aso aso_subassign) "-=";
        opp (ano_aso aso_mulassign) "*=";
        opp (ano_aso aso_divassign) "/=";
        opp (ano_aso aso_borassign) "|=";
        opp (ano_aso aso_bandassign) "&=";
        opp (ano_aso aso_xorassign) "^=";
        opp (ano_so so_turnary) "?"
      ]);
    ( bd_left_to_right,
      [
        opp (ano_lo lo_or) "||"
      ]);
    ( bd_left_to_right,
      [
        opp (ano_lo lo_and) "&&"
      ]);
    ( bd_left_to_right,
      [
        opp (ano_bo bo_or) "|"
      ]);
    ( bd_left_to_right,
      [
        opp (ano_bo bo_xor) "^"
      ]);
    ( bd_left_to_right,
      [
        opp (ano_bo bo_and) "&"
      ]);
    ( bd_left_to_right,
      [
        opp (ano_ro ro_eq) "==";
        opp (ano_ro ro_neq) "!="
      ]);
    ( bd_left_to_right,
      [
        opp (ano_ro ro_lt) "<";
        opp (ano_ro ro_le) "<=";
        opp (ano_ro ro_gt) ">";
        opp (ano_ro ro_ge) ">="
      ]);
    ( bd_left_to_right,
      [
        opp (ano_bo bo_lshift) "<<";
        opp (ano_bo bo_rshift) ">>"
      ]);
    ( bd_left_to_right,
      [
        opp (ano_ao ao_plus) "+";
        opp (ano_ao ao_minus) "-"
      ]);
    ( bd_left_to_right,
      [
        opp (ano_ao ao_mult) "*";
        opp (ano_ao ao_div) "/";
        opp (ano_ao ao_mod) "%"
      ]);
    ( bd_unary_left,
      [
        opp (ano_lo lo_not) "!";
        opp (ano_bo bo_neg) "~";
        opp (ano_ao ao_minus_unary) "-"
      ]);
    ( bd_unary_right,
      [
        opp (ano_aso aso_postinc) "++";
        opp (ano_aso aso_postdec) "--";
        opp (ano_so so_subscript) "[";
        opp (ano_so so_function_call) "("
      ])
  ].

Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (beq_nat n 32) (* space *)
      (beq_nat n 9). (* tab *)
Definition isEndLine (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (beq_nat n 10) (* linefeed *)
      (beq_nat n 13). (* Carriage return. *)
Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).
Definition isUnderscore (c : ascii) : bool :=
  let n := nat_of_ascii c in beq_nat n 95.
Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (orb (andb (65 <=? n) (n <=? 90))
             (andb (97 <=? n) (n <=? 122)))
        (isUnderscore c).
Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Inductive chartype := white | endline | alpha | digit | other.
Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isEndLine c then
    endline
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition reserved_words :=
  ["if"; "else"; "do"; "while"; "for"; "return"]%string.

Definition is_valid_identifier (s : string) : bool :=
  match s with
    | EmptyString => false
    | String x s' =>
      isAlpha x
      && forallb
        (fun c => isAlpha c || isDigit c || isUnderscore c)
        (list_of_string s')
      && beq_nat (count_occ string_dec reserved_words s) 0
  end.

Definition token := string.
Definition endline_char : ascii :=
  ascii_of_nat 10.
Definition endline_token : token :=
  string_of_list [endline_char].

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [ rev acc ] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "(" =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")" =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, _, "[" =>
      tk ++ ["["]::(tokenize_helper other [] xs')
    | _, _, "]" =>
      tk ++ ["]"]::(tokenize_helper other [] xs')
    | _, _, "{" =>
      tk ++ ["{"]::(tokenize_helper other [] xs')
    | _, _, "}" =>
      tk ++ ["}"]::(tokenize_helper other [] xs')
    | _, _, ";" =>
      tk ++ [";"]::(tokenize_helper other [] xs')
    | endline, white, _ =>
      tokenize_helper endline (" " :: acc) xs'
    | _, white, _ =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x =>
      tokenize_helper digit (x::acc) xs'
    | alpha,digit,x =>
      tokenize_helper digit (x::acc) xs'
    | digit,alpha,x =>
      tokenize_helper alpha (x::acc) xs'
    | other,other,x =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

(* Keeps line breaks with spaces following them. *)
Definition tokenize_break (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Definition decompose_endline (x : token) : option nat :=
  match list_of_string x with
  | [] => None (* invalid: empty token *)
  | y :: ys =>
    if isEndLine y
    then Some (List.length ys)
    else None
  end.

Fixpoint filter_double_breaks (xs : list string) (acc : option string) : list string :=
  match acc with
  | None =>
    match xs with
    | [] => []
    | x :: xs' =>
      match decompose_endline x with
      | None => x :: filter_double_breaks xs' None
      | Some n => filter_double_breaks xs' (Some x)
      end
    end
  | Some acc2 =>
    match xs with
    | [] => [acc2]
    | x :: xs' =>
      match decompose_endline x with
      | None => acc2 :: x :: filter_double_breaks xs' None
      | Some n => filter_double_breaks xs' (Some x)
      end
    end
  end %string.

Fixpoint filter_breaks (ident_level : nat) (xs : list string) : list string :=
  match xs with
  | [] => []
  | "{" :: x :: xs' =>
    match list_of_string x with
    | [] => [] (* invalid: empty token *)
    | y :: ys' =>
      if isEndLine y
      then "{" :: endline_token :: filter_breaks (List.length ys') xs'
      else "{" :: x :: filter_breaks ident_level xs'
    end
  | x :: xs' =>
    match list_of_string x with
    | [] => [] (* invalid: empty token *)
    | y :: ys' =>
      if isEndLine y
      then
        if (List.length ys') <=? ident_level
        then endline_token :: filter_breaks (List.length ys') xs'
        else filter_breaks ident_level xs'
      else x :: filter_breaks ident_level xs'
    end
  end %string.

Fixpoint filter_comments (comment_open : bool) (xs : list string) : list string :=
  match xs with
  | [] => []
  | x :: xs' =>
    if comment_open
    then
      match decompose_endline x with
      | Some _ => x :: filter_comments false xs'
      | None => filter_comments true xs'
      end
    else
      match x with
      | "//" => filter_comments true xs'
      | _ => x :: filter_comments false xs'
      end
  end %string.

Definition tokenize (s : string) : list string :=
  filter_breaks 0
    (
      filter_double_breaks
        (filter_comments false (tokenize_break s))
        None).

Example tokenize_ex1 :
    tokenize "abc12=3 223*(3+(a+c))" %string
  = ["abc12"; "="; "3"; "223";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")"]%string.
Proof. reflexivity. Qed.

Example tokenize_ex2 :
  tokenize "for ( i = 0; i < 2; i++ ) {
                @@update_mode_delta                                        f(1)
                if ( update_mode_delta == 1 )
                    @@loop_filter_mode_deltas[ i ]                         su(6)
                // some comment
                palette_colors_u[ idx ] = // another comment
                        Clip1( palette_colors_u[ idx - 1 ] +
                               palette_delta_u )
            }"%string
  = [ "for"; "("; "i"; "="; "0"; ";"; "i"; "<"; "2"; ";"; "i"; "++"; ")"; "{";
      endline_token;
      "@@"; "update_mode_delta"; "f"; "("; "1"; ")"; endline_token;
      "if"; "("; "update_mode_delta"; "=="; "1"; ")";
      "@@"; "loop_filter_mode_deltas"; "["; "i"; "]"; "su"; "("; "6"; ")";
      endline_token;
      "palette_colors_u"; "["; "idx"; "]"; "=";
      "Clip1"; "("; "palette_colors_u"; "["; "idx"; "-"; "1"; "]"; "+";
      "palette_delta_u"; ")"; endline_token;
      "}"
    ]%string.
Proof. reflexivity. Qed.

Definition beq_token (s1 s2 : token) : bool :=
  if string_dec s1 s2 then true else false.

Inductive optionE (X:Type) : Type :=
  | SomeE : X -> optionE X
  | NoneE : string -> optionE X.
Arguments SomeE {X}.
Arguments NoneE {X}.

Notation "'DO' ( x , y ) <== e1 ; e2"
   := (match e1 with
         | SomeE (x,y) => e2
         | NoneE err => NoneE err
       end)
   (right associativity, at level 60).
Notation "'DO' ( x , y ) <-- e1 ; e2 'OR' e3"
   := (match e1 with
         | SomeE (x,y) => e2
         | NoneE err => e3
       end)
   (right associativity, at level 60, e2 at next level).

Open Scope string_scope.

Definition parser (T : Type) :=
  list token -> optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | 0, _ =>
      NoneE "Too many recursive calls"
  | _, NoneE _ =>
      SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') =>
      many_helper p (t::acc) steps' xs'
  end.

Definition many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

Definition one_or_more
    {T}
    (p : parser T)
    (steps : nat)
    (xs : list token)
    : optionE (list T * list token) :=
  DO(e, xs) <== p xs;
  many_helper p [e] steps xs.

Definition first_expect_custom_parser
    {T}
    (first_p : parser unit)
    (p : parser T)
    (xs : list token)
    : optionE (T * list token) :=
  DO (_, xs) <== first_p xs;
  DO (e, xs) <== p xs;
  SomeE (e, xs).

Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs => match xs with
            | x::xs' =>
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] =>
              NoneE ("expected '" ++ t ++ "'.")
            end.

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE(tt, xs)).

Definition ignore_optional
    (t : token)
    (xs : list token)
    : optionE (unit * list token) :=
  DO (_, xs) <-- expect t xs;
    SomeE (tt, xs)
  OR
    SomeE (tt, xs).

Definition many_separated_custom_parser
    {T}
    (p : parser T)
    (separator_parser : parser unit)
    (steps : nat)
    (xs : list token)
    : optionE (list T * list token) :=
  DO (e, xs) <-- p xs;
    many_helper (first_expect_custom_parser separator_parser p) [e] steps xs
  OR
    SomeE ([], xs).

Definition many_separated
    {T}
    (p : parser T)
    (separator : token)
    (steps : nat)
    (xs : list token)
    : optionE (list T * list token) :=
  DO (e, xs) <-- p xs;
    many_helper (firstExpect separator p) [e] steps xs
  OR
    SomeE ([], xs).

Definition parseIdentifier (xs : list token)
                         : optionE (string * list token) :=
match xs with
| [] => NoneE "Expected identifier"
| x::xs' =>
    if is_valid_identifier x then
      SomeE (x, xs')
    else
      NoneE ("Illegal identifier:'" ++ x ++ "'")
end.

Definition hex_to_number (c : ascii) : optionE nat :=
  match c with
  | "0"%char => SomeE 0
  | "1"%char => SomeE 1
  | "2"%char => SomeE 2
  | "3"%char => SomeE 3
  | "4"%char => SomeE 4
  | "5"%char => SomeE 5
  | "6"%char => SomeE 6
  | "7"%char => SomeE 7
  | "8"%char => SomeE 8
  | "9"%char => SomeE 9
  | "a"%char => SomeE 10
  | "b"%char => SomeE 11
  | "c"%char => SomeE 12
  | "d"%char => SomeE 13
  | "e"%char => SomeE 14
  | "f"%char => SomeE 15
  | "A"%char => SomeE 10
  | "B"%char => SomeE 11
  | "C"%char => SomeE 12
  | "D"%char => SomeE 13
  | "E"%char => SomeE 14
  | "F"%char => SomeE 15
  | _ => NoneE "expected hex digit"
  end.

Definition is_hex_digit (c : ascii) : bool :=
  match hex_to_number c with
  | SomeE _ => true
  | NoneE _ => false
  end.

Definition parseNumber (xs : list token)
                     : optionE (nat * list token) :=
match xs with
| [] => NoneE "Expected number"
| x::xs' =>
      if forallb isDigit (list_of_string x) then
        SomeE (fold_left
                 (fun n d =>
                    10 * n + (nat_of_ascii d -
                              nat_of_ascii "0"%char))
                 (list_of_string x)
                 0,
               xs')
      else
        match (list_of_string x) with
        | "0"%char :: "x"%char :: tx =>
          if forallb is_hex_digit tx then
            SomeE (fold_left
                     (fun n d =>
                        match hex_to_number d with
                        | SomeE dd => 16 * n + dd
                        | _ => 0
                        end)
                     tx
                     0,
                   xs')
          else
            NoneE "Expected number"
        | _ =>
          NoneE "Expected number"
        end
end.

Definition parse_operator
    (opps_at_level : list operator_parsing_parameters)
    (xs : list token)
    : optionE (any_operator * list token) :=
  match xs with
  | [] => NoneE "expected operator"
  | symbol :: rest =>
    let
      test :=
        fun opp_i => match
          opp_i with opp op op_symbol => beq_token op_symbol symbol
        end
    in match find test opps_at_level with
    | Some (opp op op_symbol) => SomeE (op, rest)
    | None => NoneE "expected operator"
    end
  end.

Example parse_operator_ex0 :
  let opps_at_level :=
    [
      opp (ano_aso aso_assign) "=";
      opp (ano_aso aso_addassign) "+=";
      opp (ano_aso aso_subassign) "-="
    ]
  in
    parse_operator opps_at_level ["+="; "foo"] =
      SomeE (ano_aso aso_addassign, ["foo"]).
Proof. reflexivity. Qed.

Definition dummy_expr : expression := expr_number 0.

Definition parse_argument_separator
    (xs : list token)
    : optionE (unit * list token) :=
  DO (_, xs) <== expect "," xs;
  ignore_optional endline_token xs.

Fixpoint parse_primary_expression
    (steps : nat)
    (xs : list token)
    : optionE (expression * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    DO (i, xs) <-- parseIdentifier xs ;
      SomeE (expr_variable i, xs)
    OR DO (n, xs) <-- parseNumber xs ;
      SomeE (expr_number (Z.of_nat n), xs)
    OR (
      DO (e, xs) <==
        firstExpect "(" (parse_operator_expression steps' opps None) xs ;
      DO (_, xs) <== expect ")" xs ;
      SomeE(e, xs))
  end
with parse_operator_expression
    (steps : nat)
    (opps_left : list (binding_direction * list operator_parsing_parameters))
    (accum_expr : option expression)
    (xs : list token)
    : optionE (expression * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    match opps_left with
    | [] => parse_primary_expression steps' xs
    | (bd, opps_at_level) :: other_opps =>
      match bd with
      | bd_left_to_right =>
        DO (e1, xs) <==
          match accum_expr with
          | None => parse_operator_expression steps' other_opps None xs
          | Some e => SomeE (e, xs)
          end ;
        DO (op, xs) <-- parse_operator opps_at_level xs ;
          DO (e2, xs) <== parse_operator_expression steps' other_opps None xs ;
          parse_operator_expression
            steps'
            opps_left
            (Some (expr_op2 op e1 e2))
            xs
        OR
          SomeE (e1, xs)
      | bd_right_to_left =>
        DO (e1, xs) <== parse_operator_expression steps' other_opps None xs ;
        DO (op, xs) <--
          parse_operator opps_at_level xs ;
          DO (e2, xs) <== parse_operator_expression steps' opps_left None xs ;
          match op with
          | (ano_so so_turnary) =>
            DO (_, xs) <== expect ":" xs ;
            DO (e3, xs) <== parse_operator_expression steps' opps_left None xs ;
            SomeE (expr_op1n op e1 [e2; e3], xs)
          | _ =>
            SomeE (expr_op2 op e1 e2, xs)
          end
        OR
          SomeE (e1, xs)
      | bd_unary_left =>
        DO (op, xs) <-- parse_operator opps_at_level xs ;
          DO (e, xs) <== parse_operator_expression steps' opps_left None xs ;
          SomeE (expr_op1 op e, xs)
        OR
          parse_operator_expression steps' other_opps None xs
      | bd_unary_right =>
        DO (e, xs) <==
          match accum_expr with
          | None => parse_operator_expression steps' other_opps None xs
          | Some e => SomeE (e, xs)
          end ;
        DO (op, xs) <-- parse_operator opps_at_level xs ;
          match op with
          | ano_so so_subscript =>
            DO (e_2, xs) <== parse_operator_expression steps' opps None xs;
            firstExpect
              "]"
              (parse_operator_expression
                steps'
                opps_left
                (Some (expr_op2 op e e_2)))
              xs
          | ano_so so_function_call =>
            DO (args, xs) <==
              many_separated_custom_parser
                (parse_operator_expression steps' opps None)
                parse_argument_separator
                steps'
                xs;
            firstExpect
                ")"
                (parse_operator_expression
                  steps'
                  opps_left
                  (Some (expr_op1n op e args)))
                xs
          | _ =>
            parse_operator_expression
              steps'
              opps_left
              (Some (expr_op1 op e))
              xs
          end
        OR
          SomeE (e, xs)
      end
    end
  end.

Definition parse_expression
    (steps : nat)
    (xs : list token)
    : optionE (expression * list token) :=
  parse_operator_expression steps opps None xs.

Example parse_expression_ex_0 :
  parse_expression 100 (tokenize "eob += ( 1 << eobShift )")
  = SomeE (
    expr_op2 (ano_aso aso_addassign) (expr_variable "eob") (
      expr_op2 (ano_bo bo_lshift) (expr_number 1) (expr_variable "eobShift")),
    []).
Proof. reflexivity. Qed.

Example parse_expression_ex_1 :
  parse_expression 100 (tokenize "a + 3 * 5")
  = SomeE (
    expr_op2
      (ano_ao ao_plus)
      (expr_variable "a")
      (expr_op2 (ano_ao ao_mult) (expr_number 3) (expr_number 5)),
    []).
Proof. reflexivity. Qed.

Example parse_expression_ex_2 :
  parse_expression 100 (tokenize "3 * 5 + a")
  = SomeE (
    expr_op2
      (ano_ao ao_plus)
      (expr_op2 (ano_ao ao_mult) (expr_number 3) (expr_number 5))
      (expr_variable "a"),
    []).
Proof. reflexivity. Qed.

Example parse_expression_ex_3 :
  parse_expression 100 (tokenize "c[5] + a")
  = SomeE (
    expr_op2
      (ano_ao ao_plus)
      (expr_op2 (ano_so so_subscript) (expr_variable "c") (expr_number 5))
      (expr_variable "a"),
    []).
Proof. reflexivity. Qed.

Example parse_expression_ex_4 :
  parse_expression
    100
    (tokenize "maxLog2TileCols = tile_log2(1, Min(MaxSbCols, MAX_TILE_COLS))")
  = SomeE
    (
      expr_op2
        (ano_aso aso_assign)
        (expr_variable "maxLog2TileCols")
        (
          expr_op1n
            (ano_so so_function_call)
            (expr_variable "tile_log2")
            [
              expr_number 1;
              expr_op1n
                (ano_so so_function_call)
                (expr_variable "Min")
                [expr_variable "MaxSbCols"; expr_variable "MAX_TILE_COLS"]]),
     []).
Proof. reflexivity. Qed.

Example parse_expression_ex_5 :
  parse_expression
    100
    (tokenize "maxLog2TileCols = tile_log2()")
  = SomeE
    (
      expr_op2
        (ano_aso aso_assign)
        (expr_variable "maxLog2TileCols")
        (expr_op1n (ano_so so_function_call) (expr_variable "tile_log2") []),
     []).
Proof. reflexivity. Qed.

Example parse_expression_ex_6 :
  parse_expression 100 (tokenize "a = b = 3 + 5 + a")
  = SomeE (
      expr_op2
        (ano_aso aso_assign)
        (expr_variable "a")
        (
          expr_op2 (ano_aso aso_assign) (expr_variable "b")
          (
            expr_op2
              (ano_ao ao_plus)
              (expr_op2 (ano_ao ao_plus) (expr_number 3) (expr_number 5))
              (expr_variable "a"))),
      []).
Proof. reflexivity. Qed.

Example parse_expression_ex_7 :
  parse_expression 100 (tokenize "1 ? 2 : 3 ? 4 : 5")
  = SomeE (
    expr_op1n
      (ano_so so_turnary)
      (expr_number 1)
      [
        (expr_number 2);
        expr_op1n
          (ano_so so_turnary)
          (expr_number 3)
          [(expr_number 4); (expr_number 5)]],
    []).
Proof. reflexivity. Qed.

Example parse_expression_ex_8 :
  parse_expression 100 (tokenize "refresh_frame_flags = 0xFF")
  = SomeE (
    expr_op2
      (ano_aso aso_assign)
      (expr_variable "refresh_frame_flags")
      (expr_number 255),
    []).
Proof. reflexivity. Qed.

Example parse_expression_ex_9 :
 parse_expression 100 (tokenize "FeatureData[ i ][ j ] *= -1")
  = SomeE (
    expr_op2
      (ano_aso aso_mulassign)
      (
        expr_op2
          (ano_so so_subscript)
          (
            expr_op2
              (ano_so so_subscript)
              (expr_variable "FeatureData")
              (expr_variable "i"))
          (expr_variable "j"))
      (
        expr_op1
          (ano_ao ao_minus_unary)
          (expr_number 1)),
    []).
Proof. reflexivity. Qed.

Definition parse_stmt_expression
    (steps : nat)
    (xs : list token)
    : optionE (statement * list token) :=
  DO (e, xs) <== parse_expression steps xs;
    DO (_, xs) <== expect endline_token xs;
      SomeE (stmt_expression e, xs).

Definition parse_pd
    (steps : nat)
    (xs : list token)
    : optionE (parsing_descriptor * list token) :=
  match xs with
  | x :: rest =>
    match x with
    | "f" =>
      DO (_, rest) <== expect "(" rest;
        DO (e, rest) <== parse_expression steps rest;
          DO (_, rest) <== expect ")" rest;
            SomeE (pd_fixed e, rest)
    | "le" =>
      DO (_, rest) <== expect "(" rest;
        DO (e, rest) <== parse_expression steps rest;
          DO (_, rest) <== expect ")" rest;
            SomeE (pd_little_endian e, rest)
    | "su" =>
      DO (_, rest) <== expect "(" rest;
        DO (e, rest) <== parse_expression steps rest;
          DO (_, rest) <== expect ")" rest;
            SomeE (pd_signed e, rest)
    | "L"  =>
      DO (_, rest) <== expect "(" rest;
        DO (e, rest) <== parse_expression steps rest;
          DO (_, rest) <== expect ")" rest;
            SomeE (pd_ae_literal e, rest)
    | "S" => SomeE (pd_ae_alphabet, rest)
    | "U" =>
      DO (_, rest) <== expect "(" rest;
        DO (e, rest) <== parse_expression steps rest;
          DO (_, rest) <== expect ")" rest;
            SomeE (pd_ae_unsigned e, rest)
    | _ => NoneE "invalid parsing description"
    end
  | [] => NoneE "expeced parsing descritpion"
  end.

Definition parse_stmt_syntax_element
    (steps : nat)
    (xs : list token)
    : optionE (statement * list token) :=
  DO (_, xs) <== expect "@@" xs;
  DO (e, xs) <== parse_expression steps xs;
  DO (pd, xs) <== parse_pd steps xs;
  DO (_, xs) <== expect endline_token xs;
  SomeE (stmt_syntax_element e pd, xs).

Definition parse_stmt_return
    (steps : nat)
    (xs : list token)
    : optionE (statement * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    DO (_, xs) <== expect "return" xs;
    DO (e, xs) <-- parse_expression steps xs;
      DO (_, xs) <== expect endline_token xs;
      SomeE (stmt_return e, xs)
    OR
      DO (_, xs) <== expect endline_token xs;
      SomeE (stmt_return (expr_number 0), xs)
  end.

Fixpoint parse_stmt
    (steps : nat)
    (xs : list token)
    : optionE (statement * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    DO (s, xs) <-- parse_stmt_expression steps' xs;
      SomeE (s, xs)
    OR DO (s, xs) <-- parse_stmt_syntax_element steps' xs;
      SomeE (s, xs)
    OR DO (s, xs) <-- parse_stmt_group steps' xs;
      SomeE (s, xs)
    OR DO (s, xs) <-- parse_stmt_if steps' xs;
      SomeE (s, xs)
    OR DO (s, xs) <-- parse_stmt_while steps' xs;
      SomeE (s, xs)
    OR DO (s, xs) <-- parse_stmt_do_while steps' xs;
      SomeE (s, xs)
    OR DO (s, xs) <-- parse_stmt_for steps' xs;
      SomeE (s, xs)
    OR DO (s, xs) <-- parse_stmt_return steps' xs;
      SomeE (s, xs)
    OR DO (_, xs) <== expect endline_token xs;
      SomeE (stmt_empty, xs)
  end
with parse_stmt_group
    (steps : nat)
    (xs : list token)
    : optionE (statement * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    DO (_, xs) <== expect "{" xs;
    DO (_, xs) <== expect endline_token xs;
    DO (statments, xs) <== many (parse_stmt steps') steps' xs;
    DO (_, xs) <== expect "}" xs;
    DO (_, xs) <-- expect endline_token xs;
      SomeE (stmt_group statments, xs)
    OR
      SomeE (stmt_group statments, xs)
  end
with parse_stmt_while
    (steps : nat)
    (xs : list token)
    : optionE (statement * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    DO (_, xs) <== expect "while" xs;
    DO (_, xs) <== expect "(" xs;
    DO (e, xs) <== parse_expression steps' xs;
    DO (_, xs) <== expect ")" xs;
    DO (statements, xs) <== parse_stmt steps' xs;
    SomeE (stmt_while e statements, xs)
  end
with parse_stmt_do_while
    (steps : nat)
    (xs : list token)
    : optionE (statement * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    DO (_, xs) <== expect "do" xs;
    DO (statements, xs) <== parse_stmt steps' xs;
    DO (_, xs) <== expect "while" xs;
    DO (_, xs) <== expect "(" xs;
    DO (e, xs) <== parse_expression steps' xs;
    DO (_, xs) <== expect ")" xs;
    DO (_, xs) <== expect endline_token xs;
    SomeE (stmt_do_while statements e, xs)
  end
with parse_stmt_if
    (steps : nat)
    (xs : list token)
    : optionE (statement * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    DO (_, xs) <== expect "if" xs;
    DO (_, xs) <== expect "(" xs;
    DO (e, xs) <== parse_expression steps' xs;
    DO (_, xs) <== expect ")" xs;
    DO (statements_if, xs) <== parse_stmt steps' xs;
    DO (_, xs) <-- expect "else" xs;
      DO (statements_else, xs) <== parse_stmt steps' xs;
      SomeE (stmt_if_else e statements_if statements_else, xs)
    OR
      SomeE (stmt_if e statements_if, xs)
  end
with parse_stmt_for
    (steps : nat)
    (xs : list token)
    : optionE (statement * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    DO (_, xs) <== expect "for" xs;
    DO (_, xs) <== expect "(" xs;
    DO (e_0, xs) <== parse_expression steps' xs;
    DO (_, xs) <== expect ";" xs;
    DO (e_1, xs) <== parse_expression steps' xs;
    DO (_, xs) <== expect ";" xs;
    DO (e_2, xs) <== parse_expression steps' xs;
    DO (_, xs) <== expect ")" xs;
    DO (statements, xs) <== parse_stmt steps' xs;
    SomeE (stmt_for e_0 e_1 e_2 statements, xs)
  end.

Example parse_stmt_ex_0 :
  parse_stmt 100 ["sz"; endline_token]
  = SomeE
      (
        stmt_expression (expr_variable "sz"),
        []).
Proof. reflexivity. Qed.

Example parse_stmt_ex_1 :
  parse_stmt 100 ((tokenize "sz -= 1 + obu_extension_flag") ++ [endline_token])
  = SomeE
      (
        stmt_expression
          (
            expr_op2
              (ano_aso aso_subassign)
              (expr_variable "sz")
              (
                expr_op2
                  (ano_ao ao_plus)
                  (expr_number 1)
                  (expr_variable "obu_extension_flag"))),
       []).
Proof. reflexivity. Qed.

Example parse_stmt_ex_2 :
  parse_stmt 100 ((tokenize "@@obu_forbidden_bit f(1)") ++ [endline_token])
  = SomeE
      (
        stmt_syntax_element
          (expr_variable "obu_forbidden_bit")
          (pd_fixed (expr_number 1)),
        []).
Proof. reflexivity. Qed.

Definition parse_array_dimension
    (steps : nat)
    (xs : list token)
    : optionE (expression * list token) :=
  DO(_, xs) <== expect "[" xs;
  DO(e, xs) <== parse_expression steps xs;
  DO(_, xs) <== expect "]" xs;
  SomeE (e, xs).

(* TODO: skip endlines in separated lists *)

Fixpoint parse_array_contents
    (depth : nat)
    (steps : nat)
    (xs : list token)
    : optionE (list expression * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    DO (_, xs) <== expect "{" xs;
    DO (_, xs) <== ignore_optional endline_token xs;
    match depth with
    | 0 => NoneE "invalid depth"
    | 1 =>
      DO (es, xs) <== many_separated_custom_parser (parse_expression steps') parse_argument_separator steps' xs;
      DO (_, xs) <== ignore_optional "," xs;
      DO (_, xs) <== ignore_optional endline_token xs;
      DO (_, xs) <== expect "}" xs;
      SomeE (es, xs)
    | S depth' =>
      DO (ll, xs) <==
        many_separated_custom_parser (parse_array_contents depth' steps') parse_argument_separator steps' xs;
      DO (_, xs) <== ignore_optional "," xs;
      DO (_, xs) <== ignore_optional endline_token xs;
      DO (_, xs) <== expect "}" xs;
      SomeE (List.concat ll, xs)
    end
  end.

Definition parse_declaration
    (steps : nat)
    (xs : list token)
    : optionE (declaration * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    DO (_, xs) <== ignore_optional endline_token xs;
    DO (identifier, xs) <== parseIdentifier xs;
    DO (_, xs) <-- expect "=" xs;
      DO (e, xs) <== parse_expression steps' xs;
      DO (_, xs) <== ignore_optional endline_token xs;
      SomeE (decl_constant identifier e, xs)
    OR DO (dims, xs) <-- one_or_more (parse_array_dimension steps') steps' xs;
      DO (_, xs) <== expect "=" xs;
      DO (contents, xs) <== parse_array_contents (List.length dims) steps' xs;
      DO (_, xs) <== ignore_optional endline_token xs;
      SomeE (decl_constant_array identifier dims contents, xs)
    OR DO (_, xs) <-- expect "(" xs;
      DO (params, xs) <== many_separated parseIdentifier "," steps' xs;
      DO (_, xs) <== expect ")" xs;
      DO (stmts, xs) <== parse_stmt steps' xs;
      DO (_, xs) <== ignore_optional endline_token xs;
      SomeE (decl_function identifier params stmts, xs)
    OR
      NoneE "invalid declaration"
  end.

Example parse_declaration_ex0 :
  parse_declaration 100 (tokenize "f_1(a, b, c, d) {
}")
  = SomeE (decl_function "f_1" ["a"; "b"; "c"; "d"] (stmt_group []), []).
Proof. reflexivity. Qed.

Example parse_declaration_ex1 :
  parse_declaration 100 (tokenize "x[1][2][3] = {{{0, 1, 2},{3, 4, 5}}}")
  = SomeE (
    decl_constant_array
      "x"
      [expr_number 1; expr_number 2; expr_number 3]
      [
        expr_number 0; expr_number 1; expr_number 2; expr_number 3;
        expr_number 4; expr_number 5],
    []).
Proof. reflexivity. Qed.

Example parse_declaration_ex2 :
  parse_declaration 100 (tokenize "x = 2 + y")
  = SomeE (
    decl_constant
      "x"
      (expr_op2 (ano_ao ao_plus) (expr_number 2) (expr_variable "y")),
    []).
Proof. reflexivity. Qed.

Example parse_declaration_ex3 :
  parse_declaration 100 (tokenize "
obu_header() {
    @@obu_forbidden_bit f(1)
}")
  = SomeE
    (
      decl_function "obu_header" []
        (
          stmt_group
          [
            stmt_syntax_element
              (expr_variable "obu_forbidden_bit")
              (pd_fixed (expr_number 1))]),
      []).
Proof. reflexivity. Qed.

Definition tokenize_pseudocode (pc : pseudocode) : list token :=
  match pc with
  | pseudocode_intro s => tokenize s
  end.

Definition parse_pseudocode (pc : pseudocode) : optionE (list declaration * list token) :=
  let ts := tokenize_pseudocode pc in
  let l := (List.length ts) * 20 in
    many (parse_declaration l) l ts.

End Parser.
