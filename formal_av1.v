(* 
 * Copyright 2018 Dominik Wójt
 * 
 * This file is part of formal_av1.
 * 
 * formal_av1 is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * formal_av1 is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with formal_av1.  If not, see <http://www.gnu.org/licenses/>.
 *
 *)

Require Import Bool Arith List.
Import ListNotations.
Require Import String.
Require Import Ascii.
Require Import ZArith.

Module av1.

Inductive pseudocode : Type :=
  | pseudocode_intro : string -> pseudocode.

(* symbols *)

Definition global_constants_pseudocode :=
  pseudocode_intro "
REFS_PER_FRAME = 7
TOTAL_REFS_PER_FRAME = 8
MV_FR_SIZE = 4
BLOCK_SIZE_GROUPS = 4
BLOCK_SIZES = 24
BLOCK_INVALID = 14
MAX_SB_SIZE = 128
MAX_SB_SIZE_LOG2 = 7
MI_SIZE = 4
MI_SIZE_LOG2 = 2
MAX_TILE_WIDTH_SB = 4096 / MAX_SB_SIZE
MAX_TILE_AREA = 4096 * 2304
MAX_TILE_AREA_SB = MAX_TILE_AREA / ( MAX_SB_SIZE * MAX_SB_SIZE )
MAX_TILE_ROWS = 64
MAX_TILE_COLS = 64
NUM_REF_FRAMES = 8
MAX_REF_FRAMES = 4
IS_INTER_CONTEXTS = 4
COMP_MODE_CONTEXTS = 5
REF_CONTEXTS = 5
MAX_SEGMENTS = 8
SEG_LVL_ALT_Q = 0
SEG_LVL_ALT_LF_Y_V = 1
SEG_LVL_ALT_LF_Y_H = 2
SEG_LVL_ALT_LF_U = 3
SEG_LVL_ALT_LF_V = 4
SEG_LVL_REF_FRAME = 5
SEG_LVL_SKIP = 6
SEG_LVL_GLOBALMV = 7
SEG_LVL_MAX = 8
BLOCK_TYPES = 2
REF_TYPES = 2
COEF_BANDS = 6
PREV_COEF_CONTEXTS = 6
DC_COEF_CONTEXTS = 3
UNCONSTRAINED_NODES = 3
DC_HEAD_TOKENS = 6
AC_HEAD_TOKENS = 5
TAIL_TOKENS = 9
TX_SIZE_CONTEXTS = 2
INTERP_FILTERS = 3
INTERP_FILTER_CONTEXTS = 16
SKIP_CONTEXTS = 3
PARTITION_CONTEXTS_W8 = 4
PARTITION_CONTEXTS = 20
PARTITION_TYPES_W8 = 4
PARTITION_TYPES = 10
TX_SIZES = 5
TX_SIZES_ALL = 13
TX_MODES = 6
DCT_DCT = 0
ADST_DCT = 1
DCT_ADST = 2
ADST_ADST = 3
FLIPADST_DCT = 4
DCT_FLIPADST = 5
FLIPADST_FLIPADST = 6
ADST_FLIPADST = 7
FLIPADST_ADST = 8
IDTX = 9
V_DCT = 10
H_DCT = 11
V_ADST = 12
H_ADST = 13
V_FLIPADST = 14
H_FLIPADST = 15
TX_TYPES = 16
MB_MODE_COUNT = 17
INTRA_MODES = 13
UV_INTRA_MODES = 14
COMPOUND_MODES = 8
COMPOUND_MODE_CONTEXTS = 7
NEW_MV_CONTEXTS = 7
ZERO_MV_CONTEXTS = 2
REF_MV_CONTEXTS = 9
DRL_MODE_CONTEXTS = 5
MV_CONTEXTS = 3
MV_JOINTS = 4
MV_CLASSES = 11
CLASS0_SIZE = 2
MV_OFFSET_BITS = 10
MAX_PROB = 255
MAX_MODE_LF_DELTAS = 2
COMPANDED_MVREF_THRESH = 8
MAX_LOOP_FILTER = 63
REF_SCALE_SHIFT = 14
SUBPEL_BITS = 4
SUBPEL_SHIFTS = 16
SUBPEL_MASK = 15
SCALE_SUBPEL_BITS = 10
MV_BORDER = 128
INTERP_EXTEND = 4
BORDERINPIXELS = 160
MAX_UPDATE_FACTOR = 128
COUNT_SAT = 20
BOTH_ZERO = 0
ZERO_PLUS_PREDICTED = 1
BOTH_PREDICTED = 2
NEW_PLUS_NON_INTRA = 3
BOTH_NEW = 4
INTRA_PLUS_NON_INTRA = 5
BOTH_INTRA = 6
INVALID_CASE = 9
UNUSED_PROB = 128
PALETTE_COLOR_CONTEXTS = 5
PALETTE_MAX_COLOR_CONTEXT_HASH = 8
PALETTE_BLOCK_SIZES = 13
PALETTE_Y_MODE_CONTEXTS = 3
PALETTE_UV_MODE_CONTEXTS = 2
PALETTE_SIZES = 7
PALETTE_COLORS = 8
PALETTE_NUM_NEIGHBORS = 3
DELTA_Q_SMALL = 3
DELTA_LF_SMALL = 3
QM_TOTAL_SIZE = 2708
MAX_ANGLE_DELTA = 3
DIRECTIONAL_MODES = 8
ANGLE_STEP = 3
TX_SETS_INTRA = 3
TX_SETS_INTER = 4
TX_SET_TYPES = 6
FRAME_CONTEXTS = 8
WARPEDMODEL_PREC_BITS = 16
IDENTITY = 0
TRANSLATION = 1
ROTZOOM = 2
AFFINE = 3
GM_ABS_TRANS_BITS = 12
GM_ABS_TRANS_ONLY_BITS = 9
GM_ABS_ALPHA_BITS = 12
DIV_LUT_PREC_BITS = 14
DIV_LUT_BITS = 8
DIV_LUT_NUM = 257
MOTION_MODES = 3
SIMPLE = 0
OBMC = 1
LOCALWARP = 2
LEAST_SQUARES_SAMPLES_MAX = 8
TRIM_THR = 16
LS_MV_MAX = 256
LS_MAT_DOWN_BITS = 2
LS_MAT_MIN = -(1<<22)
LS_MAT_MAX = (1<<22)-1
WARPEDMODEL_TRANS_CLAMP = 1<<23
WARPEDMODEL_NONDIAGAFFINE_CLAMP = 1<<13
WARPEDPIXEL_PREC_SHIFTS = 1<<6
WARPEDDIFF_PREC_BITS = 10
GM_ALPHA_PREC_BITS = 15
GM_TRANS_PREC_BITS = 6
GM_TRANS_ONLY_PREC_BITS = 3
INTERINTRA_MODES = 4
WEDGE_DIRECTIONS = 6
MAX_WEDGE_SIZE = 32
MASK_MASTER_SIZE = 64
CDEF_VERY_LARGE = 30000
SEGMENT_ID_PREDICTED_CONTEXTS = 3
IS_INTER_CONTEXTS = 4
SKIP_CONTEXTS = 3
FWD_REFS = 4
BWD_REFS = 3
SINGLE_REFS = 7
UNIDIR_COMP_REFS = 4
COMPOUND_TYPES = 3
CFL_JOINT_SIGNS = 8
CFL_ALPHABET_SIZE = 16
COMP_INTER_CONTEXTS = 5
COMP_REF_TYPE_CONTEXTS = 5
UNI_COMP_REF_CONTEXTS = 3
CFL_ALPHA_CONTEXTS = 6
INTRA_MODE_CONTEXTS = 5
INTRA_EDGE_KERNELS = 3
INTRA_EDGE_TAPS = 5
FRAME_LF_COUNT = 4
MAX_VARTX_DEPTH = 2
TXFM_PARTITION_CONTEXTS = 22
REF_CAT_LEVEL = 640
MAX_REF_MV_STACK_SIZE = 8
MFMV_STACK_SIZE = 3
MAX_TX_DEPTH = 2
WEDGE_TYPES = 16
FILTER_BITS = 7
WIENER_COEFFS = 3
EXTRAPREC_BITS = 2
SGRPROJ_PARAMS_BITS = 4
SGRPROJ_PRJ_SUBEXP_K = 4
SGRPROJ_PRJ_BITS = 7
SGRPROJ_RST_BITS = 4
SGRPROJ_MTABLE_BITS = 20
SGRPROJ_RECIP_BITS = 8
SGRPROJ_SGR_BITS = 8
EC_PROB_SHIFT = 6
EC_MIN_PROB = 4
SELECT_INTEGER_MV = 2
RESTORATION_TILESIZE_MAX = 256
MAX_OFFSET_WIDTH = 8
MAX_OFFSET_HEIGHT = 0
WARP_PARAM_REDUCE_BITS = 6
NUM_BASE_LEVELS = 2
COEFF_BASE_RANGE = 12
BR_CDF_SIZE = 4
SIG_COEF_CONTEXTS_EOB = 4
SIG_COEF_CONTEXTS_2D = 26
SIG_COEF_CONTEXTS = 46
SIG_REF_OFFSET_NUM = 5
BR_CONTEXT_POSITION_NUM = 8
SUPERRES_NUM = 8
SUPERRES_DENOM_MIN = 9
SUPERRES_DENOM_BITS = 3
SUPERRES_FILTER_BITS = 6
SUPERRES_FILTER_SHIFTS = 1 << 6
SUPERRES_SCALE_BITS = 14
SUPERRES_SCALE_MASK = (1 << 14) - 1
SUPERRES_EXTRA_BITS = 8
".

(* conventions *)

Inductive arithmetic_operator : Type :=
  | ao_plus
  | ao_minus
  | ao_minus_unary
  | ao_mult
  | ao_div
  | ao_mod.

Inductive logical_operator : Type :=
  | lo_and
  | lo_or
  | lo_not.

Inductive relational_operator : Type :=
  | ro_gt
  | ro_ge
  | ro_lt
  | ro_le
  | ro_eq
  | ro_neq.

Inductive bitwise_operator : Type :=
  | bo_and
  | bo_or
  | bo_xor
  | bo_neg
  | bo_rshift
  | bo_lshift.

Inductive assignment_operator : Type :=
  | aso_assign
  | aso_postinc
  | aso_postdec
  | aso_addassign
  | aso_subassign.

Inductive special_operator : Type :=
  | so_function_call
  | so_subscript
  | so_tunrary.

Inductive any_operator :=
  | ano_ao : arithmetic_operator -> any_operator
  | ano_lo : logical_operator -> any_operator
  | ano_ro : relational_operator -> any_operator
  | ano_bo : bitwise_operator -> any_operator
  | ano_aso : assignment_operator -> any_operator
  | ano_so : special_operator -> any_operator.

Definition formulas_pseudocode :=
  pseudocode_intro
"abs(x) {
  if (x >= 0)
    return x
  else
    return -x
}

Clip3(x,y,z) {
  if (z < x)
    return x
  else if (z > y)
    return y
  else
    return z
}

Clip1(x) {
  return Clip3(0, (1 << BitDepth)-1, x)
}

Min(x,y) {
  if (x <= y)
    return x
  else
    return y
}

Max(x,y) {
  if (x >= y)
    return x
  else
    return y
}

Round2(x,n) {
  return (x+(1 << (n-1)))/(1 << n)
}

Round2Signed(x,n) {
  if (x >= 0)
    return Round2(x,n)
  else
    return -Round2(-x,n)
}
".

Inductive expression : Type :=
  | expr_number : Z -> expression
  | expr_variable : string -> expression
  | expr_op1 : any_operator -> expression -> expression
  | expr_op2 : any_operator -> expression -> expression -> expression
  | expr_op1n : any_operator -> expression -> list expression -> expression.

Inductive parsing_descriptor : Type :=
  | pd_fixed : expression -> parsing_descriptor
  | pd_little_endian : expression -> parsing_descriptor
  | pd_signed : expression -> parsing_descriptor
  | pd_ae_literal : expression -> parsing_descriptor
  | pd_ae_alphabet : parsing_descriptor
  | pd_ae_unsigned : expression -> parsing_descriptor.

Definition ae_unsigned_decode_pseudocode :=
  pseudocode_intro "
U( n ) {
    w = floor(log2(n)) + 1
    m = (1 << w) - n
    @@v                                                                        L( w - 1 )
    if (v < m)
        return v
    @@extra_bit                                                                L( 1 )
    return (v << 1) - m + extra_bit
}
".

Inductive statement : Type :=
  | stmt_expression : expression -> statement
  | stmt_syntax_element : expression -> parsing_descriptor -> statement
  | stmt_group : list statement -> statement
  | stmt_while : expression -> statement -> statement
  | stmt_do_while : statement -> expression -> statement
  | stmt_if : expression -> statement -> statement
  | stmt_if_else : expression -> statement -> statement -> statement
  | stmt_for : expression -> expression -> expression -> statement -> statement
  | stmt_return : expression -> statement
  | stmt_empty : statement.

Inductive declaration : Type :=
  | decl_constant : string -> expression -> declaration
  | decl_constant_array :
    string -> list expression -> list expression -> declaration
  | decl_function : string -> list string -> statement -> declaration.

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
        opp (ano_so so_tunrary) "?"
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
Fixpoint string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.
Definition reserved_words :=
  ["if"; "else"; "do"; "while"; "for"; "return"]%string.
Fixpoint is_valid_identifier (s : string) : bool :=
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
    | _, white, _ =>
      tk ++ (tokenize_helper white [] xs')
    | endline, endline, _ =>
      tokenize_helper endline [endline_char] xs'
    | _, endline, _ =>
      tk ++ (tokenize_helper endline [endline_char] xs')
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
Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).
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
            }"%string
  = [ "for"; "("; "i"; "="; "0"; ";"; "i"; "<"; "2"; ";"; "i"; "++"; ")"; "{";
      endline_token;
      "@@"; "update_mode_delta"; "f"; "("; "1"; ")"; endline_token;
      "if"; "("; "update_mode_delta"; "=="; "1"; ")"; endline_token;
      "@@"; "loop_filter_mode_deltas"; "["; "i"; "]"; "su"; "("; "6"; ")";
      endline_token;
      "}" ]%string.
Proof. reflexivity. Qed.

Definition beq_token (s1 s2 : token) : bool :=
  if string_dec s1 s2 then true else false.

Inductive optionE (X:Type) : Type :=
  | SomeE : X -> optionE X
  | NoneE : string -> optionE X.
Implicit Arguments SomeE [[X]].
Implicit Arguments NoneE [[X]].

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

Fixpoint many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

Definition one_or_more
    {T}
    (p : parser T)
    (steps : nat)
    (xs : list token)
    : optionE (list T * list token) :=
  DO(e, xs) <== p xs;
  many_helper p [e] steps xs.

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

Fixpoint many_separated
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
      NoneE "Expected number"
end.

Fixpoint parse_operator
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

(* TODO: parse turnary operator *)

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
      DO (u, xs) <== expect ")" xs ;
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
          | (ano_so so_tunrary) =>
            DO (u, xs) <== expect ":" xs ;
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
              many_separated
                (parse_operator_expression steps' opps None)
                ","
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
      (ano_so so_tunrary)
      (expr_number 1)
      [
        (expr_number 2);
        expr_op1n
          (ano_so so_tunrary)
          (expr_number 3)
          [(expr_number 4); (expr_number 5)]],
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
    DO (e, xs) <== parse_expression steps xs;
    DO (_, xs) <== expect endline_token xs;
    SomeE (stmt_return e, xs)
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
    DO (_, xs) <== ignore_optional endline_token xs;
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
    DO (_, xs) <== ignore_optional endline_token xs;
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
    DO (_, xs) <== ignore_optional endline_token xs;
    DO (statements_if, xs) <== parse_stmt steps' xs;
    DO (_, xs) <-- expect "else" xs;
      DO (_, xs) <== ignore_optional endline_token xs;
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
    DO (_, xs) <== ignore_optional endline_token xs;
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

Fixpoint parse_array_dimension
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
      DO (es, xs) <== many_separated (parse_expression steps') "," steps' xs;
      DO (_, xs) <== ignore_optional endline_token xs;
      DO (_, xs) <== expect "}" xs;
      SomeE (es, xs)
    | S depth' =>
      DO (ll, xs) <==
        many_separated (parse_array_contents depth' steps') "," steps' xs;
      DO (_, xs) <== ignore_optional endline_token xs;
      DO (_, xs) <== expect "}" xs;
      SomeE (concat ll, xs)
    end
  end.

Fixpoint parse_declaration
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


Compute parse_declaration 1000 (tokenize "
color_config( ) {
        BitDepth = ten_or_twelve_bit ? 12 : 10
}").

Compute parse_declaration 1000 (tokenize "
color_config( ) {
    if ( Profile >= 2 ) {
        @@ten_or_twelve_bit                                                    f(1)
        BitDepth = ten_or_twelve_bit ? 12 : 10
    } else {
        BitDepth = 8
    }
    @@color_space                                                              f(5)
    @@transfer_function                                                        f(5)
    if ( color_space != CS_SRGB ) {
        @@color_range                                                          f(1)
        if ( Profile == 1 || Profile == 3 ) {
            @@subsampling_x                                                    f(1)
            @@subsampling_y                                                    f(1)
            @@reserved_zero                                                    f(1)
        } else {
            subsampling_x = 1
            subsampling_y = 1
        }
        if (subsampling_x && subsampling_y) {
            @@chroma_sample_position                                           f(2)
        }
    } else {
        color_range = 1
        if ( Profile == 1 || Profile == 3 ) {
            subsampling_x = 0
            subsampling_y = 0
            @@reserved_zero                                                    f(1)
        }
    }
}").

Definition tokenize_pseudocode (pc : pseudocode) : list token :=
  match pc with
  | pseudocode_intro s => tokenize s
  end.

Fixpoint parse_pseudocode (pc : pseudocode) : optionE (list declaration * list token) :=
  let ts := tokenize_pseudocode pc in
  let l := List.length ts in
    many (parse_declaration l) l ts.

End Parser.

Definition syntax_pseudocode_open_bitstream_unit :=
  pseudocode_intro "
open_bitstream_unit( sz ) {
    obu_header()
    sz -= 1 + obu_extension_flag
    if ( obu_type == OBU_SEQUENCE_HEADER )
        sequence_header_obu()
    else if ( obu_type == OBU_TD )
        temporal_delimiter_obu()
    else if ( obu_type == OBU_FRAME_HEADER )
        frame_header_obu( )
    else if ( obu_type == OBU_TILE_GROUP )
        tile_group_obu( sz )
    else if ( obu_type == OBU_METADATA )
        metadata_obu( sz )
    else if ( obu_type == OBU_PADDING )
        padding_obu()
    else
        reserved_obu( sz )
    trailing_bits()
}".

Definition syntax_pseudocode_obu_header :=
  pseudocode_intro "
obu_header() {
    @@obu_forbidden_bit                                                        f(1)
    @@obu_type                                                                 f(4)
    @@obu_reserved_2bits                                                       f(2)
    @@obu_extension_flag                                                       f(1)
    if ( obu_extension_flag == 1 )
        obu_extension_header()
}".

Definition syntax_pseudocode_obu_extension_header :=
  pseudocode_intro "
obu_extension_header() {
    @@temporal_id                                                              f(3)
    @@spatial_id                                                               f(2)
    @@quality_id                                                               f(2)
    @@reserved_flag                                                            f(1)
}".

Definition syntax_pseudocode_trailing_bits :=
  pseudocode_intro "
trailing_bits( ) {
    while ( get_position( ) & 7 )
        @@zero_bit                                                             f(1)
}".

Definition syntax_pseudocode_reserved_obu :=
  pseudocode_intro "
reserved_obu( sz ) {
    for ( i = 0; i < sz; i++ )
        @@reserved_obu_payload_byte                                            f(8)
}".

Definition syntax_pseudocode_sequence_header_obu :=
  pseudocode_intro "
sequence_header_obu( ) {
    @@profile_low_bit                                                          f(1)
    @@profile_high_bit                                                         f(1)
    Profile = (profile_high_bit << 1) + profile_low_bit
    if ( Profile == 3 )
        @@reserved_zero                                                        f(1)
    @@level                                                                    f(4)
    @@frame_width_bits_minus_1                                                 f(4)
    @@frame_height_bits_minus_1                                                f(4)
    n = frame_width_bits_minus_1 + 1
    @@max_frame_width_minus_1                                                  f(n)
    n = frame_height_bits_minus_1 + 1
    @@max_frame_height_minus_1                                                 f(n)
    @@frame_id_numbers_present_flag                                            f(1)
    if ( frame_id_numbers_present_flag ) {
        @@frame_id_length_minus7                                               f(4)
        @@delta_frame_id_length_minus2                                         f(4)
    }
    color_config( )
}".

Definition syntax_pseudocode_color_config :=
  pseudocode_intro "
color_config( ) {
    if ( Profile >= 2 ) {
        @@ten_or_twelve_bit                                                    f(1)
        BitDepth = ten_or_twelve_bit ? 12 : 10
    } else {
        BitDepth = 8
    }
    @@color_space                                                              f(5)
    @@transfer_function                                                        f(5)
    if ( color_space != CS_SRGB ) {
        @@color_range                                                          f(1)
        if ( Profile == 1 || Profile == 3 ) {
            @@subsampling_x                                                    f(1)
            @@subsampling_y                                                    f(1)
            @@reserved_zero                                                    f(1)
        } else {
            subsampling_x = 1
            subsampling_y = 1
        }
        if (subsampling_x && subsampling_y) {
            @@chroma_sample_position                                           f(2)
        }
    } else {
        color_range = 1
        if ( Profile == 1 || Profile == 3 ) {
            subsampling_x = 0
            subsampling_y = 0
            @@reserved_zero                                                    f(1)
        }
    }
}".

Definition syntax_pseudocode_temporal_delimiter_obu :=
  pseudocode_intro "
temporal_delimiter_obu( ) {
    SeenFrameHeader = 0
}".

Definition syntax_pseudocode_padding_obu :=
  pseudocode_intro "
padding_obu( ) {
    @@obu_padding_length                                                       f(8)
    for ( i = 0; i < obu_padding_length; i++ )
        @@obu_padding_byte                                                     f(8)
}".

Definition syntax_pseudocode_metadata_obu :=
  pseudocode_intro "
metadata_obu( sz ) {
    @@metadata_type                                                            f(16)
    if ( metadata_type == METADATA_TYPE_PRIVATE_DATA )
        metadata_private_data( sz − 2 )
    else if ( metadata_type == METADATA_TYPE_HDR_CLL ) 
        metadata_hdr_cll( sz − 2 )
    else if ( metadata_type == METADATA_TYPE_HDR_MDCV )
        metadata_hdr_mdcv( sz − 2 )
}".

Definition syntax_pseudocode_metadata_private_data :=
  pseudocode_intro "
metadata_private_data( sz ) {
    for ( i = 0; i < sz; i++ )
        @@metadata_private_data_payload_byte[ i ]                              f(8)
}".

Definition syntax_pseudocode_metadata_hdr_cll :=
  pseudocode_intro "
metadata_hdr_cll( sz ) {
    @@max_cll                                                                  f(16)
    @@max_fall                                                                 f(16)
}".

Definition syntax_pseudocode_metadata_hdr_mdcv :=
  pseudocode_intro "
metadata_hdr_mdcv( sz ) {
    for ( i = 0; i < 3; i++ ) {    
        @@primary_chromaticity_x[ i ]                                          f(16)
        @@primary_chromaticity_y[ i ]                                          f(16)
    }
    @@white_point_chromaticity_x                                               f(16)
    @@white_point_chromaticity_y                                               f(16)
    @@luminance_max                                                            f(32)
    @@luminance_min                                                            f(32)
}".

Definition syntax_pseudocode_frame_header_obu :=
  pseudocode_intro "
frame_header_obu( ) {
    if ( SeenFrameHeader == 1 ) {
        frame_header_copy()
    } else {
        SeenFrameHeader = 1
        uncompressed_header( )
        trailing_bits( )
        if ( show_existing_frame ) {
            decode_frame( )
            SeenFrameHeader = 0
        } else {
            TileNum = 0
            MaxTileSize = 0
            SeenFrameHeader = 1
        }
    }
}".

Definition syntax_pseudocode_uncompressed_header :=
  pseudocode_intro "
uncompressed_header( ) {
    idLen = frame_id_length_minus7 + 7
    @@show_existing_frame                                                      f(1)
    if ( show_existing_frame == 1 ) {
        @@frame_to_show_map_idx                                                f(3)
        refresh_frame_flags = 0
        for ( i = 0; i < FRAME_LF_COUNT; i++ )
            loop_filter_level[ i ] = 0
        if (frame_id_numbers_present_flag) {
            @@display_frame_id                                                 f(idLen)
        }
        CurrentVideoFrame += 1
        return
    }
    @@frame_type                                                               f(2)
    @@show_frame                                                               f(1)
    @@error_resilient_mode                                                     f(1)
    if ( frame_id_numbers_present_flag ) {
        @@current_frame_id                                                     f(idLen)
    }
    @@frame_size_override_flag                                                 f(1)
    FrameIsIntra = (frame_type == INTRA_ONLY_FRAME || 
                    frame_type == KEY_FRAME)
    if ( frame_type == KEY_FRAME ) {
        frame_size( )
        render_size( )
        @@use_128x128_superblock                                               f(1)
        @@allow_screen_content_tools                                           f(1)
        refresh_frame_flags = 0xFF
        CurrentVideoFrame = 0
        if (allow_screen_content_tools) {
            @@seq_choose_integer_mv                                            f(1)
            if ( seq_choose_integer_mv ) {
                seq_force_integer_mv = SELECT_INTEGER_MV
            } else {
                @@seq_force_integer_mv                                         f(1)
            }
        } else {
            seq_force_integer_mv = 0
        }
    } else {
        if ( frame_type == INTRA_ONLY_FRAME ) {
            @@allow_screen_content_tools                                       f(1)
        }
        if ( frame_type == INTRA_ONLY_FRAME ) {
            @@refresh_frame_flags                                              f(8)
            frame_size( )
            render_size( )
            @@use_128x128_superblock                                           f(1)
        } else {
            if (frame_type == SWITCH_FRAME ) {
                refresh_frame_flags = 0xFF
            } else {
                @@refresh_frame_flags                                          f(8)
            }
            for( i = 0; i < REFS_PER_FRAME; i++ ) {
                @@ref_frame_idx[ i ]                                           f(3)
                if (frame_type == SWITCH_FRAME ) {
                    ref_frame_sign_bias[ LAST_FRAME + i ] = 0
                } else {
                    @@ref_frame_sign_bias[ LAST_FRAME + i ]                    f(1)
                }
                if (frame_id_numbers_present_flag) {
                    n = delta_frame_id_length_minus2 + 2
                    @@delta_frame_id_minus1                                    f(n)
                    DeltaFrameId = delta_frame_id_minus1 + 1
                    RefFrameId = ((current_frame_id -
                                  DeltaFrameId ) % (1 << idLen))
                }
            }
            if ( frame_size_override_flag && !error_resilient_mode ) {
                frame_size_with_refs( )
            } else {
                frame_size( )
                render_size( )
            }
            if ( seq_force_integer_mv == SELECT_INTEGER_MV )
                @@force_integer_mv                                             f(1)
            else
                force_integer_mv = seq_force_integer_mv
            if ( force_integer_mv ) {
                allow_high_precision_mv = 0
            } else {
                @@allow_high_precision_mv                                      f(1)
            }
            read_interpolation_filter( )
            if ( error_resilient_mode ) {
                can_use_previous = 0
            } else {
                @@can_use_previous                                             f(1)
            }
        }
    }
    if (show_frame == 0) {
        @@frame_offset_update                                                  f(4)
        DecodeOrder = CurrentVideoFrame + frame_offset_update
    } else {
        DecodeOrder = CurrentVideoFrame
        CurrentVideoFrame += 1
    }
    if ( !FrameIsIntra ) {
        for( i = 0; i < REFS_PER_FRAME; i++ ) {
            DecodeOrders[ LAST_FRAME + i ] = RefDecodeOrder[ ref_frame_idx[ i ] ]
        }
    }
    if ( error_resilient_mode ) {
        frame_parallel_decoding_mode = 1
    } else {
        @@frame_parallel_decoding_mode                                         f(1)
    }
    if ( FrameIsIntra || error_resilient_mode ) {
        setup_past_independence ( )
    } else {
        load_cdfs( ref_frame_idx[ 0 ] )
        load_previous( )
    }
    loop_filter_params( )
    quantization_params( )
    segmentation_params( )
    delta_q_params( )
    AllLossless = 1
    for ( segmentId = 0; segmentId < MAX_SEGMENTS; segmentId++ ) {
        qindex = get_qindex( 1, segmentId )
        LosslessArray[ segmentId ] = qindex == 0 && deltaQYDc == 0 && deltaQUVAc == 0 && deltaQUVDc == 0
        if ( !LosslessArray[ segmentId ] )
            AllLossless = 0
        if ( using_qmatrix ) {
            if ( LosslessArray[ segmentId ] ) {
                qmLevel = 15
            } else {
                qmLevel = min_qmlevel + ( base_q_idx * ( max_qmlevel - min_qmlevel + 1 ) ) / 256
            }
            SegQMLevel[ segmentId ] = qmLevel
        }
    }
    delta_lf_params( )
    cdef_params( )
    lr_params( )
    read_tx_mode( )
    global_motion_params( )
    frame_reference_mode( )
    @@reduced_tx_set                                                           f(1)
    tile_info( )
}".

Definition syntax_pseudocode_frame_size :=
  pseudocode_intro "
frame_size( ) {
    if (frame_size_override_flag) {
        n = frame_width_bits_minus_1 + 1
        @@frame_width_minus_1                                                  f(n)
        n = frame_height_bits_minus_1 + 1
        @@frame_height_minus_1                                                 f(n)
        FrameWidth = frame_width_minus_1 + 1
        FrameHeight = frame_height_minus_1 + 1
    } else {
        FrameWidth = max_frame_width_minus_1 + 1
        FrameHeight = max_frame_height_minus_1 + 1
    }
    compute_image_size( )
}".

Definition syntax_pseudocode_render_size :=
  pseudocode_intro "
render_size( ) {
    @@render_and_frame_size_different                                          f(1)
    if ( render_and_frame_size_different == 1 ) {
        @@render_width_minus_1                                                 f(16)
        @@render_height_minus_1                                                f(16)
        RenderWidth = render_width_minus_1 + 1
        RenderHeight = render_height_minus_1 + 1
    } else {
        RenderWidth = FrameWidth
        RenderHeight = FrameHeight
    }
}".

Definition syntax_pseudocode_frame_size_with_refs :=
  pseudocode_intro "
frame_size_with_refs( ) {
    for ( i = 0; i < REFS_PER_FRAME; i++ ) {
        @@found_ref                                                            f(1)
        if ( found_ref == 1 ) {
            FrameWidth = RefFrameWidth[ ref_frame_idx[ i ] ]
            FrameHeight = RefFrameHeight[ ref_frame_idx[ i ] ]
            RenderWidth = FrameWidth
            RenderHeight = FrameHeight
            break
        }
    }
    if ( found_ref == 0 ) {
        frame_size( )
        render_size( )
    } else {
        compute_image_size( )
    }
}".

Definition syntax_pseudocode_compute_image_size :=
  pseudocode_intro "
compute_image_size( ) {
    MiCols = 2 * ( ( FrameWidth + 7 ) >> 3 )
    MiRows = 2 * ( ( FrameHeight + 7 ) >> 3 )
    MaxSbCols = ( MiCols + 31 ) >> 5
    MaxSbRows = ( MiRows + 31 ) >> 5
}".

Definition syntax_pseudocode_read_interpolation_filter :=
  pseudocode_intro "
read_interpolation_filter( ) {
    @@is_filter_switchable                                                     f(1)
    if ( is_filter_switchable == 1 ) {
        interpolation_filter = SWITCHABLE
    } else {
        @@interpolation_filter                                                 f(2)
    }
}".

Definition syntax_pseudocode_loop_filter_params :=
  pseudocode_intro "
loop_filter_params( ) {
    @@loop_filter_level[ 0 ]                                                   f(6)
    @@loop_filter_level[ 1 ]                                                   f(6)
    if ( loop_filter_level[ 0 ] || loop_filter_level[ 1 ] ) {
        @@loop_filter_level[ 2 ]                                               f(6)
        @@loop_filter_level[ 3 ]                                               f(6)
    }
    @@loop_filter_sharpness                                                    f(3)
    @@loop_filter_delta_enabled                                                f(1)
    if ( loop_filter_delta_enabled == 1 ) {
        @@loop_filter_delta_update                                             f(1)
        if ( loop_filter_delta_update == 1 ) {
            for ( i = 0; i < TOTAL_REFS_PER_FRAME; i++ ) {
                @@update_ref_delta                                             f(1)
                if ( update_ref_delta == 1 )
                    @@loop_filter_ref_deltas[ i ]                              su(6)
                for ( i = 0; i < 2; i++ ) {
                    @@update_mode_delta                                        f(1)
                    if ( update_mode_delta == 1 )
                        @@loop_filter_mode_deltas[ i ]                         su(6)
                }
            }
        }
    }
}".

Definition syntax_pseudocode_quantization_params :=
  pseudocode_intro "
quantization_params( ) {
    @@base_q_idx                                                               f(8)
    deltaQYDc = read_delta_q( )
    deltaQUVDc = read_delta_q( )
    deltaQUVAc = read_delta_q( )
    @@using_qmatrix                                                            f(1)
    if (using_qmatrix) {
        @@min_qmlevel                                                          f(4)
        @@max_qmlevel                                                          f(4)
    }
}".

Definition syntax_pseudocode_read_delta_q :=
  pseudocode_intro "
read_delta_q( ) {
    @@delta_coded                                                              f(1)
    if ( delta_coded ) {
        @@delta_q                                                              su(6)
    } else {
        delta_q = 0
    }
    return delta_q
}".

Definition syntax_pseudocode_segmentation_params :=
  pseudocode_intro "
segmentation_params( ) {
    @@segmentation_enabled                                                     f(1)
    if ( segmentation_enabled == 1 ) {
        if ( FrameIsIntra || error_resilient_mode ) {
            segmentation_update_map = 1
            segmentation_temporal_update = 0
        } else {
            @@segmentation_update_map                                          f(1)
            if ( segmentation_update_map == 1 )
                @@segmentation_temporal_update                                 f(1)
        }
        @@segmentation_update_data                                             f(1)
        if ( segmentation_update_data == 1 ) {
            for ( i = 0; i < MAX_SEGMENTS; i++ ) {
                for ( j = 0; j < SEG_LVL_MAX; j++ ) {
                    feature_value = 0
                    @@feature_enabled                                          f(1)
                    FeatureEnabled[ i ][ j ] = feature_enabled
                    if ( feature_enabled == 1 ) {
                        bitsToRead = Segmentation_Feature_Bits[ j ]
                        @@feature_value                                        f(bitsToRead)
                        if ( Segmentation_Feature_Signed[ j ] == 1 ) {
                            @@feature_sign                                     f(1)
                        }
                    }
                    FeatureData[ i ][ j ] = feature_value
                    if ( feature_sign == 1 )
                        FeatureData[ i ][ j ] *= -1
                }
            }
        }
    }
}

Segmentation_Feature_Bits[ SEG_LVL_MAX ] = { 8, 6, 6, 6, 6, 3, 0, 0 }
Segmentation_Feature_Signed[ SEG_LVL_MAX ] = { 1, 1, 1, 1, 1, 0, 0, 0 }
".

Definition syntax_pseudocode_tile_info :=
  pseudocode_intro "
tile_info ( ) {
    minLog2TileCols = tile_log2(MAX_TILE_WIDTH_SB, MaxSbCols)
    maxLog2TileCols = tile_log2(1, Min(MaxSbCols, MAX_TILE_COLS))
    maxLog2TileRows = tile_log2(1, Min(MaxSbRows, MAX_TILE_ROWS))
    minLog2Tiles = Max(minLog2TileCols, 
                       tile_log2(MAX_TILE_AREA_SB, MaxSbRows * MaxSbCols))

    @@uniform_tile_spacing_flag                                                f(1)
    if ( uniform_tile_spacing_flag ) {
        TileColsLog2 = minLog2TileCols
        while ( TileColsLog2 < maxLog2TileCols ) {
            @@increment_tile_cols_log2                                         f(1)
            if ( increment_tile_cols_log2 == 1 )
                TileColsLog2++
            else
                break
        }
        sizeSb = (MaxSbCols + (1 << TileColsLog2) - 1) >> TileColsLog2
        i = 0
        for (startSb = 0; startSb < MaxSbCols; startSb += sizeSb) {
          MiColStarts[ i ] = startSb << (MAX_SB_SIZE_LOG2 - MI_SIZE_LOG2)
          i += 1
        }
        MiColStarts[i] = MiCols
        TileCols = i
        
        minLog2TileRows = Max( minLog2Tiles - TileColsLog2, 0)
        maxTileHeightSb = MaxSbRows >> minLog2TileRows
        TileRowsLog2 = minLog2TileRows
        while ( TileRowsLog2 < maxLog2TileRows ) {
            @@increment_tile_rows_log2                                         f(1)
            if ( increment_tile_rows_log2 == 1 )
                TileRowsLog2++
            else
                break
        }
        sizeSb = (MaxSbCols + (1 << TileRowsLog2) - 1) >> TileRowsLog2
        i = 0
        for (startSb = 0; startSb < MaxSbRows; startSb += sizeSb) {
          MiRowStarts[ i ] = startSb << (MAX_SB_SIZE_LOG2 - MI_SIZE_LOG2)
          i += 1
        }
        MiRowStarts[i] = MiRows
        TileRows = i
    } else {
        widestTileSb = 0
        startSb = 0
        for ( i = 0; startSb < MaxSbCols && i < MAX_TILE_COLS; i++ ) {
            MiColStarts[ i ] = startSb << (MAX_SB_SIZE_LOG2 - MI_SIZE_LOG2)
            maxWidth = Min(MaxSbCols - startSb, MAX_TILE_WIDTH_SB)
            sizeSb = decode_uniform(maxWidth) + 1
            widestTileSb = Max( sizeSb, widestTileSb )
            startSb += sizeSb
        }
        MiColStarts[i] = MiCols
        TileCols = i
        TileColsLog2 = tile_log2(1, TileCols)

        if ( minLog2Tiles > 0 )
            maxTileAreaSb = (MaxSbRows * MaxSbCols) >> (minLog2Tiles + 1)
        else
            maxTileAreaSb = MaxSbRows * MaxSbCols
        maxTileHeightSb = Max( maxTileAreaSb / widestTileSb, 1 )

        startSb = 0
        for ( i = 0; startSb < MaxSbRows && i < MAX_TILE_ROWS; i++ ) {
            MiRowStarts[ i ] = startSb << (MAX_SB_SIZE_LOG2 - MI_SIZE_LOG2)
            maxHeight = Min(MaxSbRows - startSb, maxTileHeightSb)
            sizeSb = decode_uniform(maxHeight) + 1
            startSb += sizeSb
        }
        MiRowStarts[ i ] = MiRows
        TileRows = i
        TileRowsLog2 = tile_log2(1, TileRows)
    }
    startMi = 0
    maxTileHeightMi = maxTileHeightSb << (MAX_SB_SIZE_LOG2 - MI_SIZE_LOG2)
    for (i = 0; i < TileRows; i++) {
      if (MiRowStarts[i+1] - startMi > maxTileHeightMi) {
        AllowDependentTileRow[i] = 0
        startMi = MiRowStarts[i+1]
      } else {
        AllowDependentTileRow[i] = 1
      }
    }
    if ( TileRowsLog2 > 0 )
        @@dependent_tiles                                                      f(1)
    else
        dependent_tiles = 0
    if ( TileRowsLog2 > 0 || TileColsLog2 > 0 )
        @@loop_filter_across_tiles                                             f(1)
    else
        loop_filter_across_tiles = 0
    @@tile_size_bytes_minus_1                                                  f(2)
    TileSizeBytes = tile_size_bytes_minus_1 + 1
}".

Definition syntax_pseudocode_tile_log2 :=
  pseudocode_intro "
tile_log2( blkSize, target) {
  for (k = 0; (blkSize << k) < target; k++) {
  }
  return k
}".

Definition syntax_pseudocode_delta_q_params :=
  pseudocode_intro "
delta_q_params( ) {
    segmentQuantizerActive = 0
    for ( i = 0; i < MAX_SEGMENTS; i++ ) {
        if ( seg_feature_active_idx( i, SEG_LVL_ALT_Q ) ) {
            segmentQuantizerActive = 1
        }
    }
    delta_q_res = 0
    delta_q_present = 0
    if ( segmentQuantizerActive == 0 && base_q_idx > 0 ) {
        @@delta_q_present                                                      f(1)
    }
    if ( delta_q_present ) {
        @@delta_q_res                                                          f(2)
    }
}".

Definition syntax_pseudocode_delta_lf_params :=
  pseudocode_intro "
delta_lf_params( ) {
    delta_lf_present = 0
    delta_lf_res = 0
    delta_lf_multi = 0
    if ( delta_q_present ) {
        @@delta_lf_present                                                     f(1)
        if ( delta_lf_present ) {
            @@delta_lf_res                                                     f(2)
            @@delta_lf_multi                                                   f(1)
        }
    }
}".

Definition syntax_pseudocode_cdef_params :=
  pseudocode_intro "
cdef_params( ) {
    if ( !AllLossless ) {
        @@cdef_damping_minus_3                                                 f(2)
        CdefDamping = cdef_damping_minus_3 + 3
        @@cdef_bits                                                            f(2)
        for (i = 0; i < (1 << cdef_bits); i++) {
            @@cdef_y_pri_strength[i]                                           f(4)
            @@cdef_y_sec_strength[i]                                           f(2)
            if (cdef_y_sec_strength[i] == 3)
                cdef_y_sec_strength[i] += 1
            @@cdef_uv_pri_strength[i]                                          f(4)
            @@cdef_uv_sec_strength[i]                                          f(2)
            if (cdef_uv_sec_strength[i] == 3)
                cdef_uv_sec_strength[i] += 1
        }
    }
}".

Definition syntax_pseudocode_lr_params :=
  pseudocode_intro "
lr_params( ) {
    usesLr = 0
    usesChromaLr = 0
    for (i = 0; i < 3; i++) {
        @@lr_type                                                              f(2)
        FrameRestorationType[i] = Remap_Lr_Type[lr_type]
        if (FrameRestorationType[i] != RESTORE_NONE) {
            usesLr = 1
            if ( i > 0 ) {
                usesChromaLr = 1
            }
        }
    }
    if ( usesLr ) {
        @@lr_unit_shift                                                        f(1)
        if ( lr_unit_shift ) {
            @@lr_unit_extra_shift                                              f(1)
            lr_unit_shift += lr_unit_extra_shift
        }
        LoopRestorationSize[ 0 ] = RESTORATION_TILESIZE_MAX >> (2 - lr_unit_shift)
        if (subsampling_x && subsampling_y && usesChromaLr ) {
            @@lr_uv_shift                                                      f(1)
        } else {
            lr_uv_shift = 0
        }
        LoopRestorationSize[1] = LoopRestorationSize[0] >> lr_uv_shift
        LoopRestorationSize[2] = LoopRestorationSize[0] >> lr_uv_shift
    }
}

Remap_Lr_Type[4] = {
  RESTORE_NONE, RESTORE_SWITCHABLE, RESTORE_WIENER, RESTORE_SGRPROJ
}".

Definition syntax_pseudocode_read_tx_mode :=
  pseudocode_intro "
read_tx_mode( ) {
    if ( AllLossless == 1 ) {
        TxMode = ONLY_4X4
    } else {
        @@tx_mode_select                                                       f(1)
        if ( tx_mode_select ) {
            TxMode = TX_MODE_SELECT
        } else {
            @@tx_mode                                                          f(2)
            TxMode = tx_mode
        }
        if (TxMode == ALLOW_32X32) {
            @@tx_mode_64x64                                                    f(1)
            TxMode += tx_mode_64x64
        }
    }
}".

Definition syntax_pseudocode_frame_reference_mode :=
  pseudocode_intro "
frame_reference_mode( ) {
    if ( FrameIsIntra ) {
        compoundReferenceAllowed = 0
    } else {
        compoundReferenceAllowed = 0
        for ( i = 1; i < REFS_PER_FRAME; i++ )
            if ( ref_frame_sign_bias[ i + 1 ] != ref_frame_sign_bias[ 1 ] )
                compoundReferenceAllowed = 1
    }
    if ( compoundReferenceAllowed ) {
        @@reference_select                                                     f(1)
        if ( reference_select ) {
            ReferenceMode = REFERENCE_MODE_SELECT
        } else {
            @@non_single_reference                                             f(1)
            if (non_single_reference == 0 )
                ReferenceMode = SINGLE_REFERENCE
            else
                ReferenceMode = COMPOUND_REFERENCE
        }
    } else {
        ReferenceMode = SINGLE_REFERENCE
    }
    if ( FrameIsIntra || comp_pred_mode == COMPOUND_REFERENCE) {
        allow_interintra_compound = 0
    } else {
        @@allow_interintra_compound                                            f(1)
    }
    if ( FrameIsIntra || comp_pred_mode == SINGLE_REFERENCE) {
        allow_masked_compound = 0
    } else {
        @@allow_masked_compound                                                f(1)
    }
}".

Definition syntax_pseudocode_global_motion_params :=
  pseudocode_intro "
global_motion_params( ) {
    if ( FrameIsIntra || error_resilient_mode || !can_use_previous) {
        for (ref = LAST_FRAME; ref <= ALTREF_FRAME; ref++) {
            gm_type[ref] = IDENTITY
            for ( i = 0; i < 6; i++ )
                gm_params[ ref ][ i ] = (i%3 == 2) ? 1 << WARPEDMODEL_PREC_BITS : 0
        }
    }
    if ( FrameIsIntra )
        return
    for (ref = LAST_FRAME; ref <= ALTREF_FRAME; ref++) {
        @@is_global                                                            f(1)
        if (is_global) {
            @@is_rot_zoom                                                      f(1)
            if (is_rot_zoom) {
                type = ROTZOOM
            } else {
                @@is_translation                                               f(1)
                type = is_translation ? TRANSLATION : AFFINE
            }
        } else {
            type = IDENTITY
        }
        gm_type[ref] = type

        if (type >= ROTZOOM) {
            read_global_param(type,ref,2)
            read_global_param(type,ref,3)
            if (type == AFFINE) {
                read_global_param(type,ref,4)
                read_global_param(type,ref,5)
            } else {
                gm_params[ref][4] = -gm_params[ref][3]
                gm_params[ref][5] = gm_params[ref][2]
            }
        }
        if (type >= TRANSLATION) {
            read_global_param(type,ref,0)
            read_global_param(type,ref,1)
        }
    }
}".

Definition syntax_pseudocode_read_global_param :=
  pseudocode_intro "
read_global_param( type, ref, idx ) {
    absBits = GM_ABS_ALPHA_BITS
    precBits = GM_ALPHA_PREC_BITS
    if (idx < 2) {
        if (type == TRANSLATION) {
            absBits = GM_ABS_TRANS_ONLY_BITS - !allow_high_precision_mv
            precBits = GM_TRANS_ONLY_PREC_BITS - !allow_high_precision_mv
        } else {
            absBits = GM_ABS_TRANS_BITS
            precBits = GM_TRANS_PREC_BITS
        }
    }
    precDiff = WARPEDMODEL_PREC_BITS - precBits
    round = (i % 3) == 2 ? (1 << WARPEDMODEL_PREC_BITS) : 0
    sub = (i % 3) == 2 ? (1 << precDiff) : 0
    mx = (1 << absBits)
    r = (gm_params[ref][idx] >> precDiff) - sub
    gm_params[ref][idx] = (decode_signed_subexp_with_ref( -mx, mx + 1, r ) << precDiff) + round
}".

Definition syntax_pseudocode_decode_signed_subexp_with_ref :=
  pseudocode_intro "
decode_signed_subexp_with_ref( low, high, r ) {
    x = decode_unsigned_subexp_with_ref(high - low, r - low)
    return x + low
}".

Definition syntax_pseudocode_decode_unsigned_subexp_with_ref :=
  pseudocode_intro "
decode_unsigned_subexp_with_ref( mx, r ) {
    v = decode_subexp( mx )
    if ((r << 1) <= mx) {
        return inverse_recenter(r, v)
    } else {
        return mx - 1 - inverse_recenter(mx - 1 - r, v)
    }
}".

Definition syntax_pseudocode_decode_subexp :=
  pseudocode_intro "
decode_subexp( numSyms ) {
    i = 0
    mk = 0
    k = 3
    while (1) {
        b2 = i ? k + i - 1 : k
        a = 1 << b2
        if (numSyms <= mk + 3 * a) {
            return decode_uniform(numSyms - mk) + mk
        } else {
            @@subexp_more_bits                                                 f(1)
            if (subexp_more_bits) {
               i++
               mk += a
            } else {
               @@subexp_bits                                                   f(b2)
               return subexp_bits + mk
            }
        }
    }
}".

Definition syntax_pseudocode_decode_uniform :=
  pseudocode_intro "
decode_uniform( n ) {
    w = floor(log2(n)) + 1
    m = (1 << w) - n
    @@v                                                                        f( w - 1 )
    if (v < m)
        return v
    @@extra_bit                                                                f( 1 )
    return (v << 1) - m + extra_bit
}".

Definition syntax_pseudocode_inverse_recenter :=
  pseudocode_intro "
inverse_recenter( r, v ) {
  if (v > 2 * r)
    return v
  else if (v & 1)
    return r - ((v + 1) >> 1)
  else
    return r + (v >> 1)
}".

Definition syntax_pseudocode_inv_recenter_nonneg :=
  pseudocode_intro "
inv_recenter_nonneg( v, m ) {
    if ( v > 2 * m )
        return v
    if ( v & 1 )
        return m - ((v + 1) >> 1)
    return m + (v >> 1)
}".

Definition syntax_pseudocode_tile_group_obu :=
  pseudocode_intro "
tile_group_obu( sz ) {
    NumTiles = TileCols * TileRows
    startBitPos = get_position( )
    tileBits = TileColsLog2 + tile_rows_log2
    @@tg_start                                                                 f(tileBits)
    @@tg_end                                                                   f(tileBits)
    trailing_bits( )
    endBitPos = get_position( )
    headerBytes = (endBitPos - startBitPos) / 8
    sz -= headerBytes
    
    for ( TileNum = tg_start; TileNum <= tg_end; TileNum++ ) {
        tileRow = TileNum / TileCols
        tileCol = TileNum % TileCols
        lastTile = TileNum == tg_end
        if ( lastTile ) {
            tile_size = sz
        } else {
            @@tile_size                                                        le(TileSizeBytes)
            sz -= tile_size + TileSizeBytes
        }
        MiRowStart = MiRowStarts[ tileRow ]
        MiRowEnd = MiRowStarts[ tileRow + 1 ]
        MiColStart = MiColStarts[ tileCol ]
        MiColEnd = MiColStarts[ tileCol + 1 ]
        if ( TileNum == tg_start ) {
            tileGroupRowStart = tileRow
            tileGroupColStart = tileCol
        }
        if (tileCol >= tileGroupColStart)
            AboveSameTileGroup = tileRow > tileGroupRowStart
        else
            AboveSameTileGroup = tileRow >= tileGroupRowStart
        if ( !AllowDependentTileRow[ tileRow ] )
            AboveSameTileGroup = 0
        CurrentQIndex = base_q_idx
        init_bool( tile_size )
        decode_tile( )
        exit_bool( )
    }
    if (tg_end == NumTiles - 1) {
        if ( !error_resilient_mode && !frame_parallel_decoding_mode ) {
            update_cdf( )
        }
        decode_frame( )
        SeenFrameHeader = 0
    }
}".

Definition syntax_pseudocode_decode_tile :=
  pseudocode_intro "
decode_tile( ) {
    if ( !dependent_tiles || TileNum == tg_start) {
        clear_above_context( )
    }
    for ( i = 0; i < FRAME_LF_COUNT; i++ )
        DeltaLF[ i ] = 0
    for ( plane = 0; plane < 3; plane++ ) {
        for ( pass = 0; pass < 2; pass++ ) {
            RefSgrXqd[ plane ][ pass ] = Sgrproj_Xqd_Mid[ pass ]
            for ( i = 0; i < WIENER_COEFFS; i++ ) {
                RefLrWiener[ plane ][ pass ][ i ] = Wiener_Taps_Mid[ i ]
            }
        }
    }
    sbSize = use_128x128_superblock ? BLOCK_128X128 : BLOCK_64X64
    sbSize4 = Num_4x4_Blocks_Wide[ sbSize ]
    for ( r = MiRowStart; r < MiRowEnd; r += sbSize4 ) {
        clear_left_context( )
        for ( c = MiColStart; c < MiColEnd; c += sbSize4 ) {
            ReadDeltas = delta_q_present
            clear_cdef( r, c )
            clear_block_decoded_flags( c < ( MiColEnd - 1 ) )
            decode_partition( r, c, sbSize )
            decode_lr( r, c, sbSize )
        }
    }
}

Wiener_Taps_Mid[3] = {  3,  -7,  15 }

Sgrproj_Xqd_Mid[2] = { -32,  31 }".

Definition syntax_pseudocode_clear_block_decoded_flags :=
  pseudocode_intro "
clear_block_decoded_flags( notLastColumn ) {
    sbSize = use_128x128_superblock ? 128 : 64
    for ( plane = 0; plane < 1 + HasChroma * 2; plane++ ) {
        subX = (plane > 0) ? subsampling_x : 0
        subY = (plane > 0) ? subsampling_y : 0
        for ( y = -1; y <= ( sbSize >> ( MI_SIZE_LOG2 + subY ) ); y++ ) 
            for ( x = -1; x <= ( sbSize >> ( MI_SIZE_LOG2 + subX ) ); x++ ) {
                BlockDecoded[ plane ][ y ][ x ] = ( y < 0 || x < 0 )
            }
        BlockDecoded[ plane ][ -1 ][ sbSize >> ( MI_SIZE_LOG2 + subX ) ] = notLastColumn
        BlockDecoded[ plane ][ sbSize >> ( MI_SIZE_LOG2 + subY ) ][ -1 ] = 0
    }
}".

Definition syntax_pseudocode_decode_partition :=
  pseudocode_intro "
decode_partition( r, c, bSize ) {
    if ( r >= MiRows || c >= MiCols )
        return 0
    num4x4 = Num_4x4_Blocks_Wide[ bSize ]
    halfBlock4x4 = num4x4 >> 1
    quarterBlock4x4 = halfBlock4x4 >> 1
    hasRows = ( r + halfBlock4x4 ) < MiRows
    hasCols = ( c + halfBlock4x4 ) < MiCols
    if (bSize < BLOCK_8X8) {
        partition = PARTITION_NONE
    } else if ( hasRows && hasCols ) {
        @@partition                                                            S
    } else if ( hasCols ) {
        @@split_or_horz                                                        S
        partition = split_or_horz ? PARTITION_SPLIT : PARTITION_HORZ
    } else if ( hasRows ) {
        @@split_or_vert                                                        S
        partition = split_or_vert ? PARTITION_SPLIT : PARTITION_VERT
    } else {
        partition = PARTITION_SPLIT
    }
    subSize = Partition_Subsize[ partition ][ bSize ]
    splitSize = Partition_Subsize[ PARTITION_SPLIT ][ bSize ]
    if ( partition == PARTITION_NONE ) {
        decode_block( r, c, subSize )
    } else if ( partition == PARTITION_HORZ ) {
        decode_block( r, c, subSize )
        if ( hasRows )
            decode_block( r + halfBlock4x4, c, subSize )
    } else if ( partition == PARTITION_VERT ) {
        decode_block( r, c, subSize )
        if ( hasCols )
            decode_block( r, c + halfBlock4x4, subSize )
    } else if ( partition == PARTITION_SPLIT ) {
        decode_partition( r, c, subSize )
        decode_partition( r, c + halfBlock4x4, subSize )
        decode_partition( r + halfBlock4x4, c, subSize )
        decode_partition( r + halfBlock4x4, c + halfBlock4x4, subSize )
    } else if ( partition == PARTITION_HORZ_A ) {
        decode_block( r, c, splitSize )
        decode_block( r, c + halfBlock4x4, splitSize )
        decode_block( r + halfBlock4x4, c, subSize )
    } else if ( partition == PARTITION_HORZ_B ) {
        decode_block( r, c, subSize )
        decode_block( r + halfBlock4x4, c, splitSize )
        decode_block( r + halfBlock4x4, c + halfBlock4x4, splitSize )
    } else if ( partition == PARTITION_VERT_A ) {
        decode_block( r, c, splitSize )
        decode_block( r + halfBlock4x4, c, splitSize )
        decode_block( r, c + halfBlock4x4, subSize )
    } else if ( partition == PARTITION_VERT_B ) {
        decode_block( r, c, subSize )
        decode_block( r, c + halfBlock4x4, splitSize )
        decode_block( r + halfBlock4x4, c + halfBlock4x4, splitSize )
    } else if ( partition == PARTITION_HORZ_4 ) {
        decode_block( r + quarterBlock4x4 * 0, c, subSize )
        decode_block( r + quarterBlock4x4 * 1, c, subSize )
        decode_block( r + quarterBlock4x4 * 2, c, subSize )
        decode_block( r + quarterBlock4x4 * 3, c, subSize )
    } else {
        decode_block( r, c + quarterBlock4x4 * 0, subSize )
        decode_block( r, c + quarterBlock4x4 * 1, subSize )
        decode_block( r, c + quarterBlock4x4 * 2, subSize )
        decode_block( r, c + quarterBlock4x4 * 3, subSize )
    }
}".

Definition syntax_pseudocode_decode_block :=
  pseudocode_intro "
decode_block( r, c, subSize ) {
    MiRow = r
    MiCol = c
    MiSize = subSize
    AvailU = is_inside( r - 1, c )
    AvailL = is_inside( r, c - 1 )
    bw4 = Num_4x4_Blocks_Wide[ subSize ]
    bh4 = Num_4x4_Blocks_High[ subSize ]
    if ( bh4 == 1 && subsampling_y && (MiRow & 1) == 0 )
        HasChroma = 0
    else if ( bw4 == 1 && subsampling_x && (MiCol & 1) == 0 )
        HasChroma = 0
    else
        HasChroma = 1
    mode_info( )
    for ( y = 0; y < bh4; y++ ) {
        for ( x = 0; x < bw4; x++ ) {
            YModes [ r + y ][ c + x ] = YMode
            for( refList = 0; refList < 2; refList++ )
                RefFrames[ r + y ][ c + x ][ refList ] = RefFrame[ refList ]
            if ( is_inter ) {
                for ( dir = 0; dir < 2; dir++ ) {
                    InterpFilters[ r + y ][ c + x ][ dir ] = interp_filter[ dir ]
                }
                for( refList = 0; refList < 2; refList++ ) {
                    Mvs[ r + y ][ c + x ][ refList ] = Mv[ refList ]
                    PredMvs[ r + y ][ c + x ][ refList ] = PredMv[ refList ]
                }
            }
        }
    }
    residual( )
    for ( y = 0; y < bh4; y++ ) {
        for ( x = 0; x < bw4; x++ ) {
            Skips[ r + y ][ c + x ] = skip
            TxSizes[ r + y ][ c + x ] = tx_size
            MiSizes[ r + y ][ c + x ] = MiSize
            TileNums[ r + y ][ c + x ] = TileNum
            TileStarts[ r + y ][ c + x ] = tg_start
            SegmentIds[ r + y ][ c + x ] = segment_id
            PaletteSizes[ 0 ][ r + y ][ c + x ] = PaletteSizeY
            PaletteSizes[ 1 ][ r + y ][ c + x ] = PaletteSizeUV
            for ( i = 0; i < PaletteSizeY; i++ )
                PaletteColors[ 0 ][ r + y ][ c + x ][ i ] = palette_colors_y[ i ]
            for ( i = 0; i < PaletteSizeUV; i++ )
                PaletteColors[ 1 ][ r + y ][ c + x ][ i ] = palette_colors_u[ i ]
            for ( i = 0; i < FRAME_LF_COUNT; i++ )
                DeltaLFs[ r + y ][ c + x ][ i ] = DeltaLF[ i ]
        }
    }
}".

Definition syntax_pseudocode_mode_info :=
  pseudocode_intro "
mode_info( ) {
    if ( FrameIsIntra )
        intra_frame_mode_info( )
    else
        inter_frame_mode_info( )
}".

Definition syntax_pseudocode_intra_frame_mode_info :=
  pseudocode_intro "
intra_frame_mode_info( ) {
    intra_segment_id( )
    read_skip( )
    read_cdef( )
    read_delta_qindex( )
    read_delta_lf( )
    ReadDeltas = 0
    read_tx_size( 1 )
    RefFrame[ 0 ] = INTRA_FRAME
    RefFrame[ 1 ] = NONE
    is_inter = 0
    @@intra_frame_y_mode                                                       S
    YMode = intra_frame_y_mode
    if (HasChroma) {
        @@uv_mode                                                              S
        UVMode = uv_mode
        if (UVMode == UV_CFL_PRED) {
            read_cfl_alphas( )
        }
    }
    intra_angle_info( )
    PaletteSizeY = 0
    PaletteSizeUV = 0
    if (( MiSize >= BLOCK_8X8 ) && ( MiSize <= BLOCK_64X64 ) &&
          allow_screen_content_tools )
        palette_mode_info( )
}".

Definition syntax_pseudocode_intra_segment_id :=
  pseudocode_intro "
intra_segment_id( ) {
    if ( segmentation_enabled && segmentation_update_map )
        @@segment_id                                                           S
    else
        segment_id = 0
    Lossless = LosslessArray[ segment_id ]
}".

Definition syntax_pseudocode_read_skip :=
  pseudocode_intro "
read_skip() {
    if ( seg_feature_active( SEG_LVL_SKIP ) ) {
        skip = 1
    } else {
        @@skip                                                                 S
    }
}".

Definition syntax_pseudocode_read_delta_qindex :=
  pseudocode_intro "
read_delta_qindex( ) {
    if ( MiSize == BLOCK_LARGEST && skip )
        return
    if ( ReadDeltas ) {
        @@delta_q_abs                                                          S
        if ( delta_q_abs == DELTA_Q_SMALL ) {
            @@delta_q_rem_bits                                                 L(3)
            delta_q_rem_bits++
            @@delta_q_abs_bits                                                 L(delta_q_rem_bits)
            delta_q_abs = delta_q_abs_bits + (1 << delta_q_rem_bits) + 1
        }
        if (delta_q_abs) {
            @@delta_q_sign_bit                                                 L(1)
            reducedDeltaQIndex = delta_q_sign_bit ? -delta_q_abs : delta_q_abs
            CurrentQIndex = Clip3(1, 255, CurrentQIndex + (reducedDeltaQIndex << delta_q_res))
        }
    }
}".

Definition syntax_pseudocode_read_delta_lf :=
  pseudocode_intro "
read_delta_lf( ) {
    if ( MiSize == BLOCK_LARGEST && skip )
        return
    if ( ReadDeltas && delta_lf_present ) {
        for ( i = 0; i < ( delta_lf_multi ? FRAME_LF_COUNT : 1 ); i++ ) {
            @@delta_lf_abs                                                     S
            if ( delta_lf_abs == DELTA_LF_SMALL ) {
                @@delta_lf_rem_bits                                            L(3)
                n = delta_lf_rem_bits + 1
                @@delta_lf_abs_bits                                            L(n)
                deltaLfAbs = delta_lf_abs_bits +
                               ( 1 << n ) + 1
            } else {
                deltaLfAbs = delta_lf_abs
            }
            if ( deltaLfAbs ) {
                @@delta_lf_sign_bit                                            L(1)
                reducedDeltaLfLevel = delta_lf_sign_bit ?
                                      -deltaLfAbs :
                                       deltaLfAbs
                DeltaLF[ i ] = Clip3( 0, MAX_LOOP_FILTER, DeltaLF[ i ] +
                                  (reducedDeltaLfLevel << delta_lf_res) )
            }
        }
    }
}".

Definition syntax_pseudocode_seg_feature_active_idx :=
  pseudocode_intro "
seg_feature_active_idx( idx, feature ) {
    return segmentation_enabled && FeatureEnabled[ idx ][ feature ]
}".

Definition syntax_pseudocode_seg_feature_active :=
  pseudocode_intro "
seg_feature_active( feature ) {
    return seg_feature_active_idx( segment_id, feature )
}".

Definition syntax_pseudocode_read_tx_size :=
  pseudocode_intro "
read_tx_size( allowSelect ) {
    largestTxSize = Tx_Mode_To_Biggest_Tx_Size[ TxMode ]
    maxTxSize = Max_Tx_Size[ MiSize ]
    maxRectTxSize = Max_Tx_Size_Rect[ MiSize ]
    maxCodedTxSize = maxTxSize + Rect_Tx_Allowed[ MiSize ]
    if ( MiSize > BLOCK_4X4 ) {
        if ( allowSelect && TxMode == TX_MODE_SELECT ) {
            @@tx_size                                                          S
            if (tx_size > maxTxSize )
                tx_size = maxRectTxSize
        } else {
            if ( Tx_Size_Sqr_Up[ maxRectTxSize ] <= largestTxSize )
                tx_size = maxRectTxSize
            else
                tx_size = largestTxSize
        }
    } else {
        tx_size = maxRectTxSize
    }
}

Rect_Tx_Allowed[ BLOCK_SIZES ] = {
    0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0,
    0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1,
}

Tx_Mode_To_Biggest_Tx_Size[ TX_MODES ] = {
    TX_4X4,
    TX_8X8,
    TX_16X16,
    TX_32X32,
    TX_64X64,
    TX_64X64
}".

Definition syntax_pseudocode_read_inter_tx_size :=
  pseudocode_intro "
read_inter_tx_size( ) {
    bw4 = Num_4x4_Blocks_Wide[ MiSize ]
    bh4 = Num_4x4_Blocks_High[ MiSize ]
    if (tx_mode == TX_MODE_SELECT && 
          MiSize > BLOCK_4X4 && is_inter &&
          !skip && !Lossless) {
        MinTxSize = TX_32X32
        maxTxSz = Max_Tx_Size_Rect[ MiSize ]
        txW4 = Tx_Width[ maxTxSz ] / MI_SIZE
        txH4 = Tx_Height[ maxTxSz ] / MI_SIZE
        for ( row = MiRow; row < MiRow + bh4; row += txH4 )
            for ( col = MiCol; col < MiCol + bw4; col += txW4 )
                read_var_tx_size( row, col, maxTxSz, 0 )
    } else {
        read_tx_size(!skip || !is_inter)
        for ( row = MiRow; row < MiRow + bh4; row++ )
            for ( col = MiCol; col < MiCol + bw4; col++ )
                InterTxSizes[ row ][ col ] = tx_size
        MinTxSize = Tx_Size_Sqr[ tx_size ]
    }
}".

Definition syntax_pseudocode_read_var_tx_size :=
  pseudocode_intro "
read_var_tx_size( row, col, txSz, depth) {
    if ( row >= MiRows || col >= MiCols )
        return
    if (txSz == TX_4X4 || depth == MAX_VARTX_DEPTH) {
        txfm_split = 0
    } else {
        @@txfm_split                                                           S
    }
    w4 = Tx_Width[ txSz ] / MI_SIZE
    h4 = Tx_Height[ txSz ] / MI_SIZE
    if (txfm_split) {
        subTxSz = Split_Tx_Size[ txSz ]
        step4 = Tx_Width[ subTxSz ] / MI_SIZE
        for (i = 0; i < h4; i += step4)
            for (j = 0; j < w4; j += step4)
                read_var_tx_size( row + i, col + j, subTxSz, depth+1)
    } else {
        for (i = 0; i < h4; i++ )
            for (j = 0; j < w4; j++ )
                InterTxSizes[ row + i ][ col + j ] = txSz
        MinTxSize = Min( MinTxSize, Tx_Size_Sqr[ txSz ] )
        tx_size = txSz
    }
}

Split_Tx_Size[TX_SIZES_ALL] = {
  TX_4X4,
  TX_4X4,
  TX_8X8,
  TX_16X16,
  TX_32X32,
  TX_4X4,
  TX_4X4,
  TX_8X8,
  TX_8X8,
  TX_16X16,
  TX_16X16,
  TX_32X32,
  TX_32X32,
}".

Definition syntax_pseudocode_inter_frame_mode_info :=
  pseudocode_intro "
inter_frame_mode_info( ) {
    LeftRefFrame[ 0 ] = AvailL ? RefFrames[ MiRow ][ MiCol-1 ][ 0 ] : INTRA_FRAME
    AboveRefFrame[ 0 ] = AvailU ? RefFrames[ MiRow-1 ][ MiCol ][ 0 ] : INTRA_FRAME
    LeftRefFrame[ 1 ] = AvailL ? RefFrames[ MiRow ][ MiCol-1 ][ 1 ] : NONE
    AboveRefFrame[ 1 ] = AvailU ? RefFrames[ MiRow-1 ][ MiCol ][ 1 ] : NONE
    LeftIntra = LeftRefFrame[ 0 ] <= INTRA_FRAME
    AboveIntra = AboveRefFrame[ 0 ] <= INTRA_FRAME
    LeftSingle = LeftRefFrame[ 1 ] <= INTRA_FRAME
    AboveSingle = AboveRefFrame[ 1 ] <= INTRA_FRAME
    inter_segment_id( )
    read_skip( )
    read_cdef( )
    read_delta_qindex( )
    read_delta_lf( )
    ReadDeltas = 0
    read_is_inter( )
    read_inter_tx_size( )
    if ( is_inter )
        inter_block_mode_info( )
    else
        intra_block_mode_info( )
}".

Definition syntax_pseudocode_inter_segment_id :=
  pseudocode_intro "
inter_segment_id( ) {
    if ( segmentation_enabled ) {
        predictedSegmentId = get_segment_id( )
        if ( segmentation_update_map ) {
            if ( segmentation_temporal_update == 1 ) {
                @@seg_id_predicted                                             S
                if ( seg_id_predicted )
                    segment_id = predictedSegmentId
                else
                    @@segment_id                                               S
                for ( i = 0; i < Num_4x4_Blocks_Wide[ MiSize ]; i++ )
                    AboveSegPredContext[ MiCol + i ] = seg_id_predicted
                for ( i = 0; i < Num_4x4_Blocks_High[ MiSize ]; i++ )
                    LeftSegPredContext[ MiRow + i ] = seg_id_predicted
            } else {
                @@segment_id                                                   S
            }
        } else {
            segment_id = predictedSegmentId
        }
    } else {
        segment_id = 0
    }
    Lossless = LosslessArray[ segment_id ]
}".

Definition syntax_pseudocode_read_is_inter :=
  pseudocode_intro "
read_is_inter( ) {
    if ( seg_feature_active ( SEG_LVL_REF_FRAME ) )
        is_inter = FeatureData[ segment_id ][ SEG_LVL_REF_FRAME ] != INTRA_FRAME
    else
        @@is_inter                                                             S
}".

Definition syntax_pseudocode_get_segment_id :=
  pseudocode_intro "
get_segment_id( ) {
    bw4 = Num_4x4_Blocks_Wide[ MiSize ]
    bh4 = Num_4x4_Blocks_High[ MiSize ]
    xMis = Min( MiCols - MiCol, bw4 )
    yMis = Min( MiRows - MiRow, bh4 )
    seg = 7
    for ( y = 0; y < yMis; y++ )
        for ( x = 0; x < xMis; x++ )
            seg = Min( seg, PrevSegmentIds[ MiRow + y ][ MiCol + x ] )
    return seg
}".

Definition syntax_pseudocode_intra_block_mode_info :=
  pseudocode_intro "
intra_block_mode_info( ) {
    RefFrame[ 0 ] = INTRA_FRAME
    RefFrame[ 1 ] = NONE
    @@y_mode                                                                   S
    YMode = y_mode
    if (HasChroma) {
        @@uv_mode                                                              S
        UVMode = uv_mode
        if (UVMode == UV_CFL_PRED) {
            read_cfl_alphas( )
        }
    }
    intra_angle_info( )
    PaletteSizeY = 0
    PaletteSizeUV = 0
    if (( MiSize >= BLOCK_8X8 ) && ( MiSize <= BLOCK_64X64 ) &&
          allow_screen_content_tools )
        palette_mode_info( )
}".

Definition syntax_pseudocode_inter_block_mode_info :=
  pseudocode_intro "
inter_block_mode_info( ) {
    PaletteSizeY = 0
    PaletteSizeUV = 0
    read_ref_frames( )
    for ( j = 0; j < 2; j++ ) {
        if ( RefFrame[ j ] > INTRA_FRAME ) {
            find_mv_list( j )
            find_mv_stack( j )
        }
    }
    isCompound = RefFrame[ 1 ] > INTRA_FRAME
    if ( isCompound ) {
        compound_context( )
        find_mv_stack( -1 )
    }
    if ( seg_feature_active( SEG_LVL_SKIP ) ||
         seg_feature_active( SEG_LVL_GLOBALMV ) ) {
        YMode = GLOBALMV
    } else if ( isCompound ) {
        @@compound_mode                                                        S
        YMode = NEAREST_NEARESTMV + compound_mode
    } else {
        @@new_mv                                                               S
        if ( new_mv == 0 ) {
            YMode = NEWMV
        } else if ( AllZero ) {
            YMode = GLOBALMV
        } else {
            @@zero_mv                                                          S
            if ( zero_mv == 0 ) {
                YMode = GLOBALMV
            } else {
                @@ref_mv                                                       S
                YMode = (ref_mv == 0) ? NEARESTMV : NEARMV
            }
        }
        YMode = NEARESTMV + inter_mode
    }
    RefMvIdx = 0
    if (YMode == NEWMV || YMode == NEW_NEWMV) {
        for (idx = 0; idx < 2; idx++) {
            if (NumMvFound > idx + 1) {
                @@drl_mode                                                     S
                if (drl_mode == 0) {
                  RefMvIdx = idx
                  break
                }
                RefMvIdx = idx + 1
            }
        }
    } else if ( has_nearmv( ) ) {
        RefMvIdx = 1
        for (idx = 1; idx < 3; idx++) {
            if (NumMvFound > idx + 1) {
                @@drl_mode                                                     S
                if ( drl_mode == 0 ) {
                    RefMvIdx = idx
                    break
                }
                RefMvIdx = idx + 1
            }
        }
    }
    assign_mv( isCompound )
    read_interintra_mode( isCompound )
    read_motion_mode( isCompound )
    read_compound_type( isCompound )
    if ( interpolation_filter == SWITCHABLE ) {
        for ( dir = 0; dir < 2; dir++ ) {
            if ( needs_interp_filter( ) ) {
                @@interp_filter[ dir ]                                         S
            } else {
                interp_filter[ dir ] = EIGHTTAP
            }
        }
    } else {
        for ( dir = 0; dir < 2; dir++ )
            interp_filter[ dir ] = interpolation_filter
    }
}".

Definition syntax_pseudocode_has_nearmv :=
  pseudocode_intro "
has_nearmv( ) {
    return (YMode == NEARMV || YMode == NEAR_NEARMV
            || YMode == NEAR_NEWMV || YMode == NEW_NEARMV)
}".

Definition syntax_pseudocode_needs_interp_filter :=
  pseudocode_intro "
needs_interp_filter( ) {
    if (YMode == GLOBALMV) {
        return gm_type[ RefFrame[ 0 ] ] <= TRANSLATION
    } else if (YMode == GLOBAL_GLOBALMV ) {
        return gm_type[ RefFrame[ 0 ] ] <= TRANSLATION || gm_type[ RefFrame[ 1 ] ] <= TRANSLATION
    } else {
        return 1
    }
}".

Definition syntax_pseudocode_read_ref_frames :=
  pseudocode_intro "
read_ref_frames( ) {
    if ( seg_feature_active( SEG_LVL_REF_FRAME ) ) {
        RefFrame[ 0 ] = FeatureData[ segment_id ][ SEG_LVL_REF_FRAME ]
        RefFrame[ 1 ] = NONE
    } else if ( seg_feature_active( SEG_LVL_SKIP ) ||
                seg_feature_active( SEG_LVL_GLOBALMV ) ) {
        RefFrame[ 0 ] = LAST_FRAME
        RefFrame[ 1 ] = NONE
    } else {
        if ( ReferenceMode == REFERENCE_MODE_SELECT )
            @@comp_mode                                                        S
        else
            comp_mode = ReferenceMode
        if ( comp_mode == COMPOUND_REFERENCE ) {
            @@comp_ref_type                                                    S
            if (comp_ref_type == UNIDIR_COMP_REFERENCE) {
                @@uni_comp_ref                                                 S
                if (uni_comp_ref) {
                    RefFrame[0] = BWDREF_FRAME
                    RefFrame[1] = ALTREF_FRAME
                } else {
                    @@uni_comp_ref_p1                                          S
                    if (uni_comp_ref_p1) {
                        @@uni_comp_ref_p2                                      S
                        if (uni_comp_ref_p2) {
                          RefFrame[0] = LAST_FRAME
                          RefFrame[1] = GOLDEN_FRAME
                        } else {
                          RefFrame[0] = LAST_FRAME
                          RefFrame[1] = LAST3_FRAME
                        }
                    } else {
                        RefFrame[0] = LAST_FRAME
                        RefFrame[1] = LAST2_FRAME
                    }
                }
            } else {
                @@comp_ref                                                     S
                if ( comp_ref == 0 ) {
                    @@comp_ref_p1                                              S
                    RefFrame[ 0 ] = comp_ref_p1 ?
                                    LAST_FRAME : LAST2_FRAME
                } else {
                    @@comp_ref_p2                                              S
                    RefFrame[ 0 ] = comp_ref_p2 ?
                                    GOLDEN_FRAME : LAST3_FRAME
                }
                @@comp_bwdref                                                  S
                if ( comp_bwdref == 0 ) {
                    @@comp_bwdref_p1                                           S
                    RefFrame[ 1 ] = comp_bwdref_p1 ?
                                     ALTREF2_FRAME : BWDREF_FRAME
                } else {
                    RefFrame[ 1 ] = ALTREF_FRAME
                }
            }
        } else {
            @@single_ref_p1                                                    S
            if ( single_ref_p1 ) {
                @@single_ref_p2                                                S
                if ( single_ref_p2 == 0 ) {
                    @@single_ref_p6                                            S
                    RefFrame[ 0 ] = single_ref_p6 ?
                                     ALTREF2_FRAME : BWDREF_FRAME
                } else {
                    RefFrame[ 0 ] = ALTREF_FRAME
                }
            } else {
                @@single_ref_p3                                                S
                if ( single_ref_p3 == 0 ) {
                    @@single_ref_p5                                            S
                    RefFrame[ 0 ] = single_ref_p5 ?
                                     GOLDEN_FRAME : LAST3_FRAME
                } else {
                    @@single_ref_p4                                            S
                    RefFrame[ 0 ] = single_ref_p4 ?
                                     LAST2_FRAME : LAST_FRAME
                }
            }
            RefFrame[ 1 ] = NONE
        }
    }
}".

Definition syntax_pseudocode_assign_mv :=
  pseudocode_intro "
assign_mv( isCompound ) {
    bw = Block_Width[ MiSize ]
    bh = Block_Height[ MiSize ]
    Mv[ 1 ] = ZeroMvs[ 1 ]
    PredMv[ 1 ] = ZeroMvs[ 1 ]
    for ( i = 0; i < 1 + isCompound; i++ ) {
        compMode = get_mode( i )
        if ( compMode == GLOBALMV ) {
            PredMv[ i ] = ZeroMvs[ i ]
        } else {
            pos = ( compMode == NEARESTMV ) ? 0 : RefMvIdx
            useStack = pos < NumMvFound
            if ( compMode == NEWMV && NumMvFound <= 1)
                useStack = 0
            if ( useStack ) {
                PredMv[ i ] = RefStackMv[ pos ][ i ]
                if ( YMode == NEARMV && pos > 1 ) {
                    // No clamping
                } else {
                    PredMv[ i ][ 0 ] = clamp_mv_row( PredMv[ i ][ 0 ], MV_BORDER + bh * 8)
                    PredMv[ i ][ 1 ] = clamp_mv_col( PredMv[ i ][ 1 ], MV_BORDER + bw * 8)
                }
            } else {
                PredMv[ i ] = RefListMv[ i ][ pos ]
            }
        }
        if ( compMode == NEWMV )
            read_mv( i )
    }
}".

Definition syntax_pseudocode_read_motion_mode :=
  pseudocode_intro "
read_motion_mode( isCompound ) {
    if ( Min( Block_Width[ MiSize ],
              Block_Height[ MiSize ] ) < 8 ) {
        motion_mode = SIMPLE
        return
    }
    if ( !force_integer_mv && 
         ( YMode == GLOBALMV || YMode == GLOBAL_GLOBALMV ) ) {
        if (gm_type[ RefFrame[ 0 ] ] > TRANSLATION) {
            motion_mode = SIMPLE
            return
        }
    }
    if ( isCompound || !has_overlappable_candidates( ) ) {
        motion_mode = SIMPLE
        return
    }
    find_warp_samples()
    if ( force_integer_mv || NumSamples == 0) {
        @@use_obmc                                                             S
        motion_mode = use_obmc ? OBMC : SIMPLE
    } else {
        @@motion_mode                                                          S
    }
}".

Definition syntax_pseudocode_read_interintra_mode :=
  pseudocode_intro "
read_interintra_mode( isCompound ) {
    if ( allow_interintra_compound && !isCompound && 
         MiSize >= BLOCK_8X8 && MiSize <= BLOCK_32X32) {
        @@interintra                                                           S
        if (interintra) {
            @@interintra_mode                                                  S
            RefFrame[1] = INTRA_FRAME
            AngleDeltaY = 0
            AngleDeltaUV = 0
            n = Wedge_Bits[ MiSize ]
            if ( n > 0 ) {
                @@wedge_interintra                                             S
                if (wedge_interintra) {
                    @@wedge_index                                              L(n)
                    wedge_sign = 0
                }
            } else {
                wedge_interintra = 0
            }
        }
    } else {
        interintra = 0
    }
}".

Definition syntax_pseudocode_read_compound_type :=
  pseudocode_intro "
read_compound_type( isCompound ) {
    if ( allow_masked_compound && isCompound && motion_mode == SIMPLE && MiSize >= BLOCK_8X8) {
        n = Wedge_Bits[ MiSize ]
        if ( n == 0 ) {
            @@compound_type                                                    S
        } else {
            @@compound_avg                                                     L(1)
            compound_type = compound_avg ?
                            COMPOUND_AVERAGE : COMPOUND_SEG
        }
        if ( compound_type == COMPOUND_WEDGE ) {
            @@wedge_index                                                      L(n)
            @@wedge_sign                                                       L(1)
        } else if ( compound_type == COMPOUND_SEG ) {
            @@mask_type                                                        L(1)
        }
    } else {
        if ( interintra ) {
            compund_type = wedge_interintra ? COMPOUND_WEDGE : COMPOUND_INTRA
        } else {
            compound_type = COMPOUND_AVERAGE
        }
    }
}".

Definition syntax_pseudocode_get_mode :=
  pseudocode_intro "
get_mode( refList ) {
    if ( refList == 0 ) {
        if (YMode < NEAREST_NEARESTMV)
            compMode = YMode
        else if (YMode == NEW_NEWMV || YMode == NEW_NEARESTMV || YMode == NEW_NEARMV)
            compMode = NEWMV
        else if (YMode == NEAREST_NEARESTMV || YMode == NEAREST_NEWMV)
            compMode = NEARESTMV
        else if (YMode == NEAR_NEARMV || YMode == NEAR_NEWMV)
            compMode = NEARMV
        else
            compMode = GLOBALMV
    } else {
        if (YMode == NEW_NEWMV || YMode == NEAREST_NEWMV || YMode == NEAR_NEWMV)
            compMode = NEWMV
        else if (YMode == NEAREST_NEARESTMV || YMode == NEW_NEARESTMV)
            compMode = NEARESTMV
        else if (YMode == NEAR_NEARMV || YMode == NEW_NEARMV)
            compMode = NEARMV
        else
            compMode = GLOBALMV
    }
    return compMode
}".

Definition syntax_pseudocode_read_mv :=
  pseudocode_intro "
read_mv( ref ) {
    diffMv[ 0 ] = 0
    diffMv[ 1 ] = 0
    if ( has_nearmv( ) )
        idx = RefMvIdx - 1
    else
        idx = RefMvIdx
    if ( idx < NumMvFound )
        MvCtx = MvCtxStack[ idx ][ ref ]
    else
        MvCtx = 0
    @@mv_joint                                                                 S
    if ( mv_joint == MV_JOINT_HZVNZ || mv_joint == MV_JOINT_HNZVNZ )
        diffMv[ 0 ] = read_mv_component( 0 )
    if ( mv_joint == MV_JOINT_HNZVZ || mv_joint == MV_JOINT_HNZVNZ )
        diffMv[ 1 ] = read_mv_component( 1 )
    Mv[ ref ][ 0 ] = PredMv[ ref ][ 0 ] + diffMv[ 0 ]
    Mv[ ref ][ 1 ] = PredMv[ ref ][ 1 ] + diffMv[ 1 ]
}".

Definition syntax_pseudocode_read_mv_component :=
  pseudocode_intro "
read_mv_component( comp ) {
    @@mv_sign                                                                  S
    @@mv_class                                                                 S
    if ( mv_class == MV_CLASS_0 ) {
        @@mv_class0_bit                                                        S
        if ( force_integer_mv )
            mv_class0_fr = 3
        else
            @@mv_class0_fr                                                     S
        if ( allow_high_precision_mv )
            mv_class0_hp = 1
        else
            @@mv_class0_hp                                                     S
        mag = ( ( mv_class0_bit << 3 ) |
                ( mv_class0_fr << 1 ) |
                  mv_class0_hp ) + 1
    } else {
        d = 0
        for ( i = 0; i < mv_class; i++ ) {
            @@mv_bit                                                           S
            d |= mv_bit << i
        }
        mag = CLASS0_SIZE << ( mv_class + 2 )
        if ( force_integer_mv )
            mv_fr = 3
        else
            @@mv_fr                                                            S
        if ( allow_high_precision_mv )
            mv_hp = 1
        else
            @@mv_hp                                                            S
        mag += ( ( d << 3 ) | ( mv_fr << 1 ) | mv_hp ) + 1
    }
    return mv_sign ? -mag : mag
}".

Definition syntax_pseudocode_residual :=
  pseudocode_intro "
residual( ) {
    palette_tokens( )

    sbMask = use_128x128_superblock ? 31 : 15
    subBlockMiRow = MiRow & sbMask
    subBlockMiCol = MiCol & sbMask

    for ( plane = 0; plane < 1 + HasChroma * 2; plane++ ) {
        txSz = get_tx_size( plane, tx_size )
        stepX = Tx_Width[ txSz ] >> 2
        stepY = Tx_Height[ txSz ] >> 2
        planeSz = get_plane_residual_size( MiSize, plane )
        num4x4W = Num_4x4_Blocks_Wide[ planeSz ]
        num4x4H = Num_4x4_Blocks_High[ planeSz ]
        log2W = MI_SIZE_LOG2 + Mi_Width_Log2[ planeSz ]
        log2H = MI_SIZE_LOG2 + Mi_Height_Log2[ planeSz ]
        subX = (plane > 0) ? subsampling_x : 0
        subY = (plane > 0) ? subsampling_y : 0
        baseX = (MiCol >> subX) * MI_SIZE
        baseY = (MiRow >> subY) * MI_SIZE
        candRow = (MiRow >> subY) << subY
        candCol = (MiCol >> subX) << subX

        IsInterIntra = ( is_inter && RefFrame[ 1 ] == INTRA_FRAME )
        IsCFL = (plane > 0 && !is_inter && UVMode == UV_CFL_PRED)

        if ( IsInterIntra ) {
            if ( interintra_mode == II_DC_PRED ) mode = DC_PRED
            else if ( interintra_mode == II_V_PRED ) mode = V_PRED
            else if ( interintra_mode == II_H_PRED ) mode = H_PRED
            else mode = SMOOTH_PRED
        } else {
            mode = DC_PRED
        }

        if ( IsInterIntra || IsCFL ) {
            predict_intra( plane, baseX, baseY,
                           AvailL,
                           AvailU,
                           BlockDecoded[ plane ]
                                       [ ( subBlockMiRow >> subY ) - 1 ]
                                       [ ( subBlockMiCol >> subX ) + num4x4W ],
                           BlockDecoded[ plane ]
                                       [ ( subBlockMiRow >> subY ) + num4x4H ]
                                       [ ( subBlockMiCol >> subX ) - 1 ],
                           mode,
                           log2W, log2H )
        }

        if ( is_inter ) {
            predW = Block_Width[ MiSize ] >> subX
            predH = Block_Height[ MiSize ] >> subY
            someUseIntra = 0
            for( r = 0; r < num4x4H; r++ )
                for( c = 0; c < num4x4W; c++ )
                    if ( RefFrames[ candRow + r ][ candCol + c ][ 0 ] == INTRA_FRAME )
                        someUseIntra = 1
            if ( someUseIntra ) {
                predW = num4x4W * 4
                predH = num4x4H * 4
                candRow = MiRow
                candCol = MiCol
            }
            r = 0
            for( y = 0; y < num4x4H * 4; y += predH ) {
                c = 0
                for( x = 0; x < num4x4W * 4; x += predW ) {
                    predict_inter( plane, baseX + x, baseY + y,
                                   predW, predH,
                                   candRow + r, candCol + c)
                    c++
                }
                r++
            }
        }

        maxX = (MiCols * MI_SIZE) >> subX
        maxY = (MiRows * MI_SIZE) >> subY
        if (is_inter) {
            transform_tree( plane, baseX, baseY, num4x4W * 4, num4x4H * 4 )
        } else {
            for( y = 0; y < num4x4H; y += stepY )
                for( x = 0; x < num4x4W; x += stepX )
                    transform_block( plane, baseX, baseY, txSz, x, y)
        }
    }
}".

Definition syntax_pseudocode_transform_block :=
  pseudocode_intro "
transform_block(plane, baseX, baseY, txSz, x, y) {
    startX = baseX + 4 * x
    startY = baseY + 4 * y
    subX = (plane > 0) ? subsampling_x : 0
    subY = (plane > 0) ? subsampling_y : 0
    row = ( startY << subY ) >> MI_SIZE_LOG2
    col = ( startX << subX ) >> MI_SIZE_LOG2
    sbMask = use_128x128_superblock ? 31 : 15
    subBlockMiRow = row & sbMask
    subBlockMiCol = col & sbMask
    stepX = Tx_Width[ txSz ] >> MI_SIZE_LOG2
    stepY = Tx_Height[ txSz ] >> MI_SIZE_LOG2
    maxX = (MiCols * MI_SIZE) >> subX
    maxY = (MiRows * MI_SIZE) >> subY
    if ( startX >= maxX || startY >= maxY ) {
        return
    }
    if ( !is_inter ) {
        if ( ( ( plane == 0 ) && PaletteSizeY ) ||
             ( ( plane != 0 ) && PaletteSizeUV ) ) {
            predict_palette( plane, startX, startY, x, y, txSz )
        } else if ( IsCFL ) {
            predict_chroma_from_luma( plane, startX, startY, txSz )
        } else {
            mode = ( plane == 0 ) ? YMode : UVMode
            log2W = Tx_Width_Log2[ txSz ]
            log2H = Tx_Height_Log2[ txSz ]
            predict_intra( plane, startX, startY,
                           AvailL || x > 0,
                           AvailU || y > 0,
                           BlockDecoded[ plane ]
                                       [ ( subBlockMiRow >> subY ) + y - 1 ]
                                       [ ( subBlockMiCol >> subX ) + x + stepX ],
                           BlockDecoded[ plane ]
                                       [ ( subBlockMiRow >> subY ) + y + stepY ]
                                       [ ( subBlockMiCol >> subX ) + x - 1 ],
                           mode,
                           log2W, log2H )
        }
        if (plane == 0) {
            MaxLumaW = startX + stepX * 4
            MaxLumaH = startY + stepY * 4
        }
    }
    if ( !skip ) {
        eob = coeffs( plane, startX, startY, txSz )
        if ( eob > 0 )
            reconstruct( plane, startX, startY, txSz )
    }
    for ( i = 0; i < stepY; i++ ) {
        for ( j = 0; j < stepX; j++ ) {
            LoopfilterTxSizes[ plane ]
                             [ (row >> subY) + i ]
                             [ (col >> subX) + j ] = txSz
            BlockDecoded[ plane ]
                        [ ( subBlockMiRow >> subY ) + y + i ]
                        [ ( subBlockMiCol >> subX ) + x + j ] = 1
        }
    }
}".

Definition syntax_pseudocode_transform_tree :=
  pseudocode_intro "
transform_tree( plane, startX, startY, w, h ) {
    subX = (plane > 0) ? subsampling_x : 0
    subY = (plane > 0) ? subsampling_y : 0
    maxX = (MiCols * MI_SIZE) >> subX
    maxY = (MiRows * MI_SIZE) >> subY
    if ( startX >= maxX || startY >= maxY ) {
        return
    }
    row = ( startY << subY ) >> MI_SIZE_LOG2
    col = ( startX << subX ) >> MI_SIZE_LOG2
    lumaTxSz = InterTxSizes[ row ][ col ]
    lumaW = Tx_Width[ lumaTxSz ]
    lumaH = Tx_Height[ lumaTxSz ]
    uses64 = w >= 64 || h >= 64 
    isSubsampled = subX || subY
    forceSplit = uses64 && isSubsampled
    if ( (isSubsampled && !uses64) ||
         (!isSubsampled && w <= lumaW && h <= lumaH) ) {
        txSz = find_tx_size( w, h )
        transform_block( plane, startX, startY, txSz, 0, 0 )
    } else {
        if ( w > h ) {
            transform_tree( plane, startX, startY, w/2, h )
            transform_tree( plane, startX + w / 2, startY, w/2, h )
        } else if ( w < h ) {
            transform_tree( plane, startX, startY, w, h/2 )
            transform_tree( plane, startX, startY + h/2, w, h/2 )
        } else {
            transform_tree( plane, startX, startY, w/2, h/2 )
            transform_tree( plane, startX + w/2, startY, w/2, h/2 )
            transform_tree( plane, startX, startY + h/2, w/2, h/2 )
            transform_tree( plane, startX + w/2, startY + h/2, w/2, h/2 )
        }
    }
}".

Definition syntax_pseudocode_find_tx_size :=
  pseudocode_intro "
find_tx_size( w, h ) {
    for( txSz = 0; txSz < TX_SIZES_ALL; txSz++ )
        if ( Tx_Width[ txSz ] == w && Tx_Height[ txSz ] == h )
            break
    return txSz
}".

Definition syntax_pseudocode_get_tx_size :=
  pseudocode_intro "
get_tx_size( plane, txSz ) {
    return plane > 0 ? Uv_Tx_Size[ MiSize ][ txSz ][ subsampling_x ][ subsampling_y ] : txSz
}".

Definition syntax_pseudocode_get_plane_residual_size :=
  pseudocode_intro "
get_plane_residual_size( subsize, plane ) {
    subx = plane > 0 ? subsampling_x : 0
    suby = plane > 0 ? subsampling_y : 0
    return Subsampled_Size[ subsize ][ subx ][ suby ]
}".

Definition syntax_pseudocode_Subsampled_Size :=
  pseudocode_intro "
Subsampled_Size[ BLOCK_SIZES ][ 2 ][ 2 ] = {
  { { BLOCK_4X4,    BLOCK_4X4},      {BLOCK_4X4,     BLOCK_4X4} },
  { { BLOCK_4X8,    BLOCK_4X4},      {BLOCK_INVALID, BLOCK_4X4} },
  { { BLOCK_8X4,    BLOCK_INVALID},  {BLOCK_4X4,     BLOCK_4X4} },
  { { BLOCK_8X8,    BLOCK_8X4},      {BLOCK_4X8,     BLOCK_4X4} },
  { {BLOCK_8X16,    BLOCK_8X8},      {BLOCK_INVALID, BLOCK_4X8} },
  { {BLOCK_16X8,    BLOCK_INVALID},  {BLOCK_8X8,     BLOCK_8X4} },
  { {BLOCK_16X16,   BLOCK_16X8},     {BLOCK_8X16,    BLOCK_8X8} },
  { {BLOCK_16X32,   BLOCK_16X16},    {BLOCK_INVALID, BLOCK_8X16} },
  { {BLOCK_32X16,   BLOCK_INVALID},  {BLOCK_16X16,   BLOCK_16X8} },
  { {BLOCK_32X32,   BLOCK_32X16},    {BLOCK_16X32,   BLOCK_16X16} },
  { {BLOCK_32X64,   BLOCK_32X32},    {BLOCK_INVALID, BLOCK_16X32} },
  { {BLOCK_64X32,   BLOCK_INVALID},  {BLOCK_32X32,   BLOCK_32X16} },
  { {BLOCK_64X64,   BLOCK_64X32},    {BLOCK_32X64,   BLOCK_32X32} }
  { {BLOCK_64X128,  BLOCK_64X64},    {BLOCK_INVALID, BLOCK_32X64} },
  { {BLOCK_128X64,  BLOCK_INVALID},  {BLOCK_64X64,   BLOCK_64X32} },
  { {BLOCK_128X128, BLOCK_128X64},   {BLOCK_64X128,  BLOCK_64X64} },
  { {BLOCK_4X16,    BLOCK_4X8},      {BLOCK_INVALID, BLOCK_4X8} },
  { {BLOCK_16X4,    BLOCK_INVALID},  {BLOCK_8X4,     BLOCK_8X4} },
  { {BLOCK_8X32,    BLOCK_8X16},     {BLOCK_INVALID, BLOCK_4X16} },
  { {BLOCK_32X8,    BLOCK_INVALID},  {BLOCK_16X8,    BLOCK_16X4} },
  { {BLOCK_16X64,   BLOCK_16X32},    {BLOCK_INVALID, BLOCK_8X32} },
  { {BLOCK_64X16,   BLOCK_INVALID},  {BLOCK_32X16,   BLOCK_32X8} },
  { {BLOCK_32X128,  BLOCK_32X64},    {BLOCK_INVALID, BLOCK_16X64} },
  { {BLOCK_128X32,  BLOCK_INVALID},  {BLOCK_64X32,   BLOCK_64X16} },
}".

Definition syntax_pseudocode_coeffs :=
  pseudocode_intro "
coeffs( plane, startX, startY, txSz ) {
    txSzCtx = Tx_Size_Sqr_Up[txSz]
    PlaneTxType = TxTypes[ startY ][ startX ]
    ptype = plane > 0
    if ( txSzCtx == TX_64X64 )
        txScale = 2
    else if ( txSzCtx == TX_32X32 )
        txScale = 1
    else 
        txScale = 0
    denom = 1 << txScale
    segEob = Min( 1024, Tx_Width[ txSz ] * Tx_Height[ txSz ] )
    
    for ( c = 0; c < segEob; c++ )
        Quant[c] = 0
    
    eob = 0
    culLevel = 0
    dcCategory = 0
    
    @@all_zero                                                                 S
    if ( all_zero ) {
        c = 0
        if ( plane == 0 ) {
            for ( i = 0; i < ( Tx_Width[ txSz ] >> 2 ); i++ ) {
                for ( j = 0; j < ( Tx_Height[ txSz ] >> 2 ); j++ ) {
                    TxTypes[ startY + j ][ startX + i ] = DCT_DCT
                }
            }
        }
    } else {
        if ( plane == 0 )
            transform_type( startX, startY, Tx_Size_Sqr[ txSz ] )
        scan = get_scan( plane, txSz )
    
        maxEobPt = ceil( log2( segEob ) ) + 1
        for ( eobPt = 1; eobPt < maxEobPt; eobPt++ ) {
            @@is_eob                                                           S
            if ( is_eob )
                break
        }

        eob = ( eobPt < 2 ) ? eobPt : ( ( 1 << ( eobPt - 2 ) ) + 1 )
        eobShift = Max( -1, eobPt - 3 )
        if ( eobShift >= 0 ) {
            @@eob_extra                                                        S
            if ( eob_extra ) {
                eob += ( 1 << eobShift )
            }

            for ( i = 1; i < Max( 0, eobPt - 2 ); i++ ) {
                eobShift = Max( 0, eobPt - 2 ) - 1 - i
                @@eob_extra_bit                                                L(1)
                if ( eob_extra_bit ) {
                    eob += ( 1 << eobShift )
                }
            }
        }
        for ( c = eob - 1; c >= 0; c-- ) {
            if ( c == ( eob - 1 ) ) {
                @@coeff_base_eob                                               S
                level = coeff_base_eob + 1
            } else {
                @@coeff_base                                                   S
                level = coeff_base
            }
            Quant[ scan[ c ] ] = level
        }
        
        for ( c = 0; c < eob; c++ ) {
            if ( Quant[ scan[ c ] ] != 0 ) {
                if ( c == 0 ) {
                    @@dc_sign                                                  S
                    signs[ c ] = dc_sign
                } else {
                    @@sign_bit                                                 L(1)
                    signs[ c ] = sign_bit
                }
            } else {
                signs[ c ] = 0
            }
        }
        
        for ( c = eob - 1; c >= 0; c-- ) {
            if ( Quant[ scan[ c ] ] > NUM_BASE_LEVELS ) {
              for ( idx = 0;
                    idx < COEFF_BASE_RANGE / ( BR_CDF_SIZE - 1 );
                    idx++ ) {
                  @@coeff_br                                                   S
                  Quant[ scan[ c ] ] += coeff_br
                  if ( coeff_br < ( BR_CDF_SIZE - 1 ) )
                      break
              }
              if ( Quant[ scan[ c ] ] >
                  ( NUM_BASE_LEVELS + COEFF_BASE_RANGE ) ) {
                  length = 0
                  do {
                      length++
                      @@golomb_length_bit                                      L(1)
                  } while ( !golomb_length_bit )
                  x = 1
                  for ( i = length - 2; i >= 0; i-- ) {
                      @@golomb_data_bit                                        L(1)
                      x = ( x << 1 ) | golomb_data_bit
                  }
                  Quant[ scan[ c ] ] = x + COEFF_BASE_RANGE + NUM_BASE_LEVELS
              }
            }
        }
        
        for ( c = 0; c < eob; c++ ) {
            culLevel += Quant[ scan[ c ] ]
        }
        
        for ( c = 0; c < eob; c++ ) {
            if ( signs[ c ] )
                Quant[ scan[ c ] ] = - Quant[ scan[ c ] ]
        }

        culLevel = Min( 63, culLevel )
        
        if ( Quant[ 0 ] < 0 ) {
            dcCategory = 1
        } else if ( Quant[ 0 ] > 0 ) {
            dcCategory = 2
        }
    }
    
    for( i = 0; i < w; i++ ) {
        AboveLevelContext[ plane ][ x4 + i ] = culLevel
        AboveDcContext[ plane ][ x4 + i ] = dcCategory
    }
    for( i = 0; i < h; i++ ) {
        LeftLevelContext[ plane ][ y4 + i ] = culLevel
        LeftDcContext[ plane ][ y4 + i ] = dcCategory
    }
    return eob
}".

Definition syntax_pseudocode_compute_tx_type :=
  pseudocode_intro "
compute_tx_type( plane, txSz, blockX, blockY ) {
    txSzSqr = Tx_Size_Sqr[ txSz ]
    
    if ( Lossless || txSzSqr >= TX_32X32 )
        return DCT_DCT
        
    set = get_tx_set( txSz )
    
    if ( plane == 0 ) {
        txType = TxTypes[ blockY ][ blockX ]
        if ( RefFrame[ 0 ] != INTRA_FRAME && !Tx_Type_In_Set[ set ][ txType ] )
            return DCT_DCT
        return txType
    }
    
    if ( RefFrame[ 0 ] != INTRA_FRAME ) {
        txType = TxTypes[ blockY << subsampling_y ][ blockX << subsampling_x ]
        if ( !Tx_Type_In_Set[ set ][ txType ] )
            return DCT_DCT
        return txType
    }
    
    return Mode_To_Txfm[ UVMode ]
}".

Definition syntax_pseudocode_get_mrow_scan :=
  pseudocode_intro "
get_mrow_scan( txSz ) {
    if ( txSz == TX_4X4 )
        return Mrow_Scan_4x4
    else if ( txSz == TX_4X8 )
        return Mrow_Scan_4x8
    else if ( txSz == TX_8X4 )
        return Mrow_Scan_8x4
    else if ( txSz == TX_8X8 )
        return Mrow_Scan_8x8
    else if ( txSz == TX_8X16 )
        return Mrow_Scan_8x16
    else if ( txSz == TX_16X8 )
        return Mrow_Scan_16x8
    else if ( txSz == TX_16X16 )
        return Mrow_Scan_16x16
    else if ( txSz == TX_16X32 )
        return Mrow_Scan_16x32
    else if ( txSz == TX_32X16 )
        return Mrow_Scan_32x16
    return Mrow_Scan_32x32
}".

Definition syntax_pseudocode_get_row_scan :=
  pseudocode_intro "
get_row_scan( txSz ) {
    if ( txSz == TX_4X4 )
        return Row_Scan_4x4
    else if ( txSz == TX_8X8 )
        return Row_Scan_8x8
    return Row_Scan_16x16
}".

Definition syntax_pseudocode_get_mcol_scan :=
  pseudocode_intro "
get_mcol_scan( txSz ) {
    if ( txSz == TX_4X4 )
        return Mcol_Scan_4x4
    else if ( txSz == TX_4X8 )
        return Mcol_Scan_4x8
    else if ( txSz == TX_8X4 )
        return Mcol_Scan_8x4
    else if ( txSz == TX_8X8 )
        return Mcol_Scan_8x8
    else if ( txSz == TX_8X16 )
        return Mcol_Scan_8x16
    else if ( txSz == TX_16X8 )
        return Mcol_Scan_16x8
    else if ( txSz == TX_16X16 )
        return Mcol_Scan_16x16
    else if ( txSz == TX_16X32 )
        return Mcol_Scan_16x32
    else if ( txSz == TX_32X16 )
        return Mcol_Scan_32x16
    return Mcol_Scan_32x32
}".

Definition syntax_pseudocode_get_col_scan :=
  pseudocode_intro "
get_col_scan( txSz ) {
    if ( txSz == TX_4X4 )
        return Col_Scan_4x4
    else if ( txSz == TX_8X8 )
        return Col_Scan_8x8
    return Col_Scan_16x16
}".

Definition syntax_pseudocode_get_default_scan :=
  pseudocode_intro "
get_default_scan( txSz ) {
    if ( txSz == TX_4X4 )
        return Default_Scan_4x4
    else if ( txSz == TX_4X8 )
        return Default_Scan_4x8
    else if ( txSz == TX_8X4 )
        return Default_Scan_8x4
    else if ( txSz == TX_8X8 )
        return Default_Scan_8x8
    else if ( txSz == TX_8X16 )
        return Default_Scan_8x16
    else if ( txSz == TX_16X8 )
        return Default_Scan_16x8
    else if ( txSz == TX_16X16 )
        return Default_Scan_16x16
    else if ( txSz == TX_16X32 )
        return Default_Scan_16x32
    else if ( txSz == TX_32X16 )
        return Default_Scan_32x16
    return Default_Scan_32x32
}".

Definition syntax_pseudocode_get_scan :=
  pseudocode_intro "
get_scan( plane, txSz ) {
    if ( Tx_Size_Sqr_Up[ txSz ] == TX_64X64 ) {
        return Default_Scan_32x32
    }
    
    preferRow = ( PlaneTxType == ADST_DCT ||
                  PlaneTxType == V_DCT ||
                  PlaneTxType == V_ADST ||
                  PlaneTxType == V_FLIPADST )

    preferCol = ( PlaneTxType == DCT_ADST ||
                  PlaneTxType == H_DCT ||
                  PlaneTxType == H_ADST ||
                  PlaneTxType == H_FLIPADST )

    usesIdTx  = ( PlaneTxType == IDTX ||
                  PlaneTxType == V_DCT ||
                  PlaneTxType == V_ADST ||
                  PlaneTxType == V_FLIPADST ||
                  PlaneTxType == H_DCT ||
                  PlaneTxType == H_ADST ||
                  PlaneTxType == H_FLIPADST )

    preferRaster = !( txSz == TX_4X4 ||
                      txSz == TX_8X8 ||
                      txSz == TX_16X16 )

    if ( !usesIdTx ) {
        if ( txSz == TX_32X32 ) {
            if ( PlaneTxType == DCT_DCT )
                return Default_Scan_32x32
            else if ( PlaneTxType == ADST_DCT ||
                      PlaneTxType == FLIPADST_DCT )
                return H2_Scan_32x32
            else if ( PlaneTxType == DCT_ADST ||
                      PlaneTxType == DCT_FLIPADST )
                return V2_Scan_32x32
            return Qtr_Scan_32x32
        } else if ( is_inter ) {
            preferRow = 0
            preferCol = 0
        }
    }

    if (preferRow) {
        return preferRaster ? get_mrow_scan( txSz ) : get_row_scan( txSz )
    } else if (preferCol) {
        return preferRaster ? get_mcol_scan( txSz ) : get_col_scan( txSz )
    }
    return get_default_scan( txSz )
}".

Definition syntax_pseudocode_read_coef :=
  pseudocode_intro "
read_coef( token ) {
    cat = Extra_Bits[ token ][ 0 ]
    minValue = Extra_Bits[ token ][ 2 ]
    if ( cat == 0 )
        return token
    
    if ( cat < 6 ) {
        extraBitCount = Extra_Bits[ token ][ 1 ]
    } else {
        extraBitCount = BitDepth + 3 + Max( 0, Tx_Size_Sqr_Up[ Min( TX_32X32, tx_size ) ] )
        extraBitCount = Min( 18, ( ( extraBitCount + 3 ) >> 2 ) << 2 )
    }
    
    coef = 0
    count = 0
    cdfIndex = 0
    while ( count < extraBitCount ) {
        bits = Min( extraBitCount - count, 4 )
        @@coef_extra_bits                                                S
        coef |= coef_extra_bits << count
        count += bits
        cdfIndex += 1
    }
    return minValue + coef
}

Extra_Bits[ 11 ][ 3 ] = {
    { 0, 0, 0 },
    { 0, 0, 1 },
    { 0, 0, 2 },
    { 0, 0, 3 },
    { 0, 0, 4 },
    { 1, 1, 5 },
    { 2, 2, 7 },
    { 3, 3, 11 },
    { 4, 4, 19 },
    { 5, 5, 35 },
    { 6, 14, 67 }
}".

Definition syntax_pseudocode_intra_angle_info :=
  pseudocode_intro "
intra_angle_info( ) {
    if ( MiSize >= BLOCK_8X8 ) {
        if ( is_directional_mode( YMode ) ) {
            @@angle_delta_y                                                    S
            AngleDeltaY = angle_delta_y - MAX_ANGLE_DELTA
        }
        if ( is_directional_mode( UVMode ) ) {
            @@angle_delta_uv                                                   S
            AngleDeltaUV = angle_delta_uv - MAX_ANGLE_DELTA
        }
    }
}".

Definition syntax_pseudocode_is_directional_mode :=
  pseudocode_intro "
is_directional_mode( mode ) {
    if ( ( mode >= V_PRED ) && ( mode <= D63_PRED ) ) {
        return 1
    }
    return 0
}".

Definition syntax_pseudocode_read_cfl_alphas :=
  pseudocode_intro "
read_cfl_alphas() {
    @@cfl_alpha_signs                                                          S
    signU = (cfl_alpha_signs + 1 ) / 3
    signV = (cfl_alpha_signs + 1 ) % 3
    if (signU != CFL_SIGN_ZERO) {
        @@cfl_alpha_u                                                          S
        CflAlphaU = 1 + cfl_alpha_u
        if (signU == CFL_SIGN_NEG)
            CflAlphaU = -CflAlphaU
    } else {
      CflAlphaU = 0
    }
    if (signV != CFL_SIGN_ZERO) {
        @@cfl_alpha_v                                                          S
        CflAlphaV = 1 + cfl_alpha_v
        if (signV == CFL_SIGN_NEG)
            CflAlphaV = -CflAlphaV
    } else {
      CflAlphaV = 0
    }
}".

Definition syntax_pseudocode_palette_mode_info :=
  pseudocode_intro "
palette_mode_info( ) {
    if ( YMode == DC_PRED ) {
        @@has_palette_y                                                        S
        if ( has_palette_y ) {
            @@palette_size_y_minus_2                                           S
            PaletteSizeY = palette_size_y_minus_2 + 2
            cacheN = get_palette_cache( 0 )
            idx = 0
            for ( i = 0; i < cacheN && idx < PaletteSizeY; i++ ) {
                @@use_palette_color_cache_y                                    L(1)
                if ( use_palette_color_cache_y ) {
                    palette_colors_y[ idx ] = PaletteCache[ i ]
                    idx++
                }
            }
            if ( idx < PaletteSizeY ) {
                @@palette_colors_y[ idx ]                                      L(BitDepth)
                idx++
            }
            if ( idx < PaletteSizeY ) {
                minBits = BitDepth - 3
                @@palette_num_extra_bits_y                                     L(2)
                paletteBits = minBits + palette_num_extra_bits_y
            }
            while ( idx < PaletteSizeY ) {
                @@palette_delta_y                                              L(paletteBits)
                palette_delta_y++
                palette_colors_y[ idx ] =
                          Clip1( palette_colors_y[ idx - 1 ] +
                                 palette_delta_y )
                range = ( 1 << BitDepth ) - palette_colors_y[ idx ] - 1
                paletteBits = Min( paletteBits, ceil( log2( range ) ) )
                idx++
            }
            sort( palette_colors_y, 0, PaletteSizeY - 1 )
        }
    }
    if ( UVMode == DC_PRED ) {
        @@has_palette_uv                                                       S
        if ( has_palette_uv ) {
            @@palette_size_uv_minus_2                                          S
            PaletteSizeUV = palette_size_uv_minus_2 + 2
            cacheN = get_palette_cache( 1 )
            idx = 0
            for ( i = 0; i < cacheN && idx < PaletteSizeUV; i++ ) {
                @@use_palette_color_cache_u                                    L(1)
                if ( use_palette_color_cache_u ) {
                    palette_colors_u[ idx ] = PaletteCache[ i ]
                    idx++
                }
            }
            if ( idx < PaletteSizeUV ) {
                @@palette_colors_u[ idx ]                                      L(BitDepth)
                idx++
            }
            if ( idx < PaletteSizeUV ) {
                minBits = BitDepth - 3
                @@palette_num_extra_bits_u                                     L(2)
                paletteBits = minBits + palette_num_extra_bits_u
            }
            while ( idx < PaletteSizeUV ) {
                @@palette_delta_u                                              L(paletteBits)
                palette_colors_u[ idx ] = 
                          Clip1( palette_colors_u[ idx - 1 ] +
                                 palette_delta_u )
                range = ( 1 << BitDepth ) - palette_colors_u[ idx ]
                paletteBits = Min( paletteBits, ceil( log2( range ) ) )
                idx++
            }
            sort( palette_colors_u, 0, PaletteSizeUV - 1 )
            
            @@delta_encode_palette_colors_v                                    L(1)
            if ( delta_encode_palette_colors_v ) {
                minBits = BitDepth - 4
                maxVal = 1 << BitDepth
                @@palette_num_extra_bits_v                                     L(2)
                paletteBits = minBits + palette_num_extra_bits_v
                @@palette_colors_v[ 0 ]                                        L(BitDepth)
                for ( idx = 1; idx < PaletteSizeUV; idx++ ) {
                    @@palette_delta_v                                          L(paletteBits)
                    if ( palette_delta_v ) {
                        @@palette_delta_sign_bit_v                             L(1)
                        if ( palette_delta_sign_bit_v ) {
                            palette_delta_v = -palette_delta_v
                        }
                    }
                    val = palette_colors_v[ idx - 1 ] + palette_delta_v
                    if ( val < 0 ) val += maxVal
                    if ( val >= maxVal ) val -= maxVal
                    palette_colors_v[ idx ] = Clip1( val )
                }
            } else {
                for ( idx = 0; idx < PaletteSizeUV; idx++ ) {
                    @@palette_colors_v[ idx ]                                  L(BitDepth)
                }
            }
        }
    }
}".

Definition syntax_pseudocode_get_palette_cache :=
  pseudocode_intro "
get_palette_cache( plane ) {
    aboveN = 0
    if ( ( ( MiRow * MI_SIZE ) % 64 ) && AvailU ) {
        aboveN = PaletteSizes[ plane ][ MiRow - 1 ][ MiCol ]
    }
    leftN = 0
    if ( AvailL ) {
        leftN = PaletteSizes[ plane ][ MiRow ][ MiCol - 1 ]
    }
    aboveIdx = 0
    leftIdx = 0
    n = 0
    while ( aboveIdx < aboveN  && leftIdx < leftN ) {
        aboveC = PaletteColors[ plane ][ MiRow - 1 ][ MiCol ][ aboveIdx ]
        leftC = PaletteColors[ plane ][ MiRow ][ MiCol - 1 ][ leftIdx ]
        if ( leftC < aboveC ) {
            if ( n == 0 || leftC != PaletteCache[ n - 1 ] ) {
                PaletteCache[ n ] = leftC
                n++
            }
            leftIdx++
        } else {
            if ( n == 0 || aboveC != PaletteCache[ n - 1 ] ) {
                PaletteCache[ n ] = aboveC
                n++
            }
            aboveIdx++
            if ( leftC == aboveC ) {
                leftIdx++
            }
        }
    }
    while ( aboveIdx < aboveN ) {
        val = PaletteColors[ plane ][ MiRow - 1 ][ MiCol ][ aboveIdx ]
        aboveIdx++
        if ( n == 0 || val != PaletteCache[ n - 1 ] ) {
            PaletteCache[ n ] = val
            n++
        }
    }
    while ( leftIdx < leftN ) {
        val = PaletteColors[ plane ][ MiRow ][ MiCol - 1 ][ leftIdx ]
        leftIdx++
        if ( n == 0 || val != PaletteCache[ n - 1 ] ) {
            PaletteCache[ n ] = val
            n++
        }
    }
    return n
}".

Definition syntax_pseudocode_transform_type :=
  pseudocode_intro "
transform_type( startX, startY, txSz ) {
    set = get_tx_set( txSz )

    if ( set > 0 &&
         ( segmentation_enabled ? get_qindex( 1, segment_id ) : base_q_idx ) > 0 &&
         !skip &&
         !seg_feature_active( SEG_LVL_SKIP ) ) {
        if ( is_inter ) {
            @@inter_tx_type                                                    S
            TxType = inter_tx_type
        } else {
            @@intra_tx_type                                                    S
            TxType = intra_tx_type
        }
    } else {
        TxType = DCT_DCT
    }
    for ( i = 0; i < ( Tx_Width[ txSz ] >> 2 ); i++ ) {
        for ( j = 0; j < ( Tx_Height[ txSz ] >> 2 ); j++ ) {
            TxTypes[ startY + j ][ startX + i ] = TxType
        }
    }
}".

Definition syntax_pseudocode_get_tx_set :=
  pseudocode_intro "
get_tx_set( txSz ) {
    txSzSqr = Tx_Size_Sqr[ txSz ]
    txSzSqrUp = Tx_Size_Sqr_Up[ txSz ]
    if ( txSzSqr > TX_32X32 )
        return TX_SET_DCTONLY
    if ( is_inter ) {
        if ( reduced_tx_set || txSzSqrUp == TX_32X32 ) return TX_SET_INTER_3
        else if ( txSzSqr == TX_16X16 ) return TX_SET_INTER_2
        return TX_SET_INTER_1
    }
    else {
        if ( reduced_tx_set ) return TX_SET_INTRA_2
        else if ( txSzSqrUp == TX_32X32 ) return TX_SET_DCTONLY
        else if ( txSzSqr == TX_16X16 ) return TX_SET_INTRA_2
        return TX_SET_INTRA_1
    }
}".

Definition syntax_pseudocode_palette_tokens :=
  pseudocode_intro "
palette_tokens( ) {
    blockHeight = Block_Height[ MiSize ]
    blockWidth = Block_Width[ MiSize ]
    onscreenHeight = Min( blockHeight, (MiRows - MiRow) * MI_SIZE )
    onscreenWidth = Min( blockWidth, (MiCols - MiCol) * MI_SIZE )

    if ( PaletteSizeY ) {
        @@color_index_map_y                                                    U(PaletteSizeY)
        ColorMapY[0][0] = color_index_map_y
        for ( i = 1; i < onscreenHeight + onscreenWidth - 1; i++ ) {
            for ( j = Min( i, onscreenWidth - 1 ); j >= Max( 0, i - onscreenHeight + 1 ); j-- ) {
                get_palette_color_context( ColorMapY, ( i - j ), j, PaletteSizeY )
                @@palette_color_idx_y                                   S
                ColorMapY[ i - j ][ j ] = ColorOrder[ palette_color_idx_y ]
            }
        }
        for ( i = 0; i < onscreenHeight; i++ ) {
            for ( j = onscreenWidth; j < blockWidth; j++ ) {
                ColorMapY[ i ][ j ] = ColorMapY[ i ][ onscreenWidth - 1 ]
            }
        }
        for ( i = onscreenHeight; i < blockHeight; i++ ) {
            for ( j = 0; j < blockWidth; j++ ) {
                ColorMapY[ i ][ j ] = ColorMapY[ onscreenHeight - 1 ][ j ]
            }
        }
    }

    if ( PaletteSizeUV ) {
        @@color_index_map_uv                                                   U(PaletteSizeUV)
        ColorMapUV[0][0] = color_index_map_uv
        blockHeight = blockHeight >> subsampling_y
        blockWidth = blockWidth >> subsampling_x
        onscreenHeight = onscreenHeight >> subsampling_y
        onscreenWidth = onscreenWidth >> subsampling_x

        for ( i = 1; i < onscreenHeight + onscreenWidth - 1; i++ ) {
            for ( j = Min( i, onscreenWidth - 1 ); j >= Max( 0, i - onscreenHeight + 1 ); j-- ) {
                get_palette_color_context( ColorMapUV, ( i - j ), j, PaletteSizeUV )
                @@palette_color_idx_uv                                  S
                ColorMapUV[ i - j ][ j ] = ColorOrder[ palette_color_idx_uv ]
            }
        }
        for ( i = 0; i < onscreenHeight; i++ ) {
            for ( j = onscreenWidth; j < blockWidth; j++ ) {
                ColorMapUV[ i ][ j ] = ColorMapUV[ i ][ onscreenWidth - 1 ]
            }
        }
        for ( i = onscreenHeight; i < blockHeight; i++ ) {
            for ( j = 0; j < blockWidth; j++ ) {
                ColorMapUV[ i ][ j ] = ColorMapUV[ onscreenHeight - 1 ][ j ]
            }
        }
    }
}".

Definition syntax_pseudocode_get_palette_color_context :=
  pseudocode_intro "
get_palette_color_context( colorMap, r, c, n ) {
    for( i = 0; i < PALETTE_COLORS; i++ ) {
        scores[ i ] = 0
        ColorOrder[i] = i
    }
    if ( c > 0 ) {
        neighbor = colorMap[ r ][ c - 1 ]
        scores[ neighbor ] += 2
    }
    if ( ( r > 0 ) && ( c > 0 ) ) {
        neighbor = colorMap[ r - 1 ][ c - 1 ]
        scores[ neighbor ] += 1
    }
    if ( r > 0 ) {
        neighbor = colorMap[ r - 1 ][ c ]
        scores[ neighbor ] += 2
    }
    for ( i = 0; i < PALETTE_NUM_NEIGHBORS; i++ ) {
        maxScore = scores[ i ]
        maxIdx = i
        for ( j = i + 1; j < n; j++ ) {
            if (scores[ j ] > maxScore) {
                maxScore = scores[ j ]
                maxIdx = j
            }
        }
        if ( maxIdx != i ) {
            maxScore = scores[ maxIdx ]
            maxColorOrder = ColorOrder[ maxIdx ]
            for ( k = maxIdx; k > i; k-- ) {
                scores[ k ] = scores[ k - 1 ]
                ColorOrder[ k ] = ColorOrder[ k - 1 ]
            }
            scores[ i ] = maxScore
            ColorOrder[ i ] = maxColorOrder
        }
    }
    ColorContextHash = 0
    for( i = 0; i < PALETTE_NUM_NEIGHBORS; i++ ) {
        ColorContextHash += scores[ i ] * Palette_Color_Hash_Multipliers[ i ]
    }
}".

Definition syntax_pseudocode_ref_checks :=
  pseudocode_intro "
is_inside( candidateR, candidateC ) {
    if (candidateC >= MiColStart &&
        candidateC < MiColEnd &&
        candidateR < MiRowEnd) {
        if (candidateR >= MiRowStart)
            return 1
        if (dependent_tiles && AboveSameTileGroup) {
            return 1
        }
    }
    return 0
}

check_forward(refFrame) {
  return ( (refFrame >= LAST_FRAME) && (refFrame <= GOLDEN_FRAME) )
}

check_backward(refFrame) {
  return ( (refFrame >= BWDREF_FRAME) && (refFrame <= ALTREF_FRAME) )
}

check_last_or_last2(refFrame) {
  return ( (refFrame == LAST_FRAME) || (refFrame == LAST2_FRAME) )
}

check_golden_or_last3(refFrame) {
  return ( (refFrame == GOLDEN_FRAME) || (refFrame == LAST3_FRAME) )
}

check_last(refFrame) {
  return (refFrame == LAST_FRAME)
}

check_last2(refFrame) {
  return (refFrame == LAST2_FRAME)
}

check_last3(refFrame) {
  return (refFrame == LAST3_FRAME)
}

check_golden(refFrame) {
  return (refFrame == GOLDEN_FRAME)
}".

Definition syntax_pseudocode_clamp_mv_row :=
  pseudocode_intro "
clamp_mv_row( mvec, border ) {
    bh4 = Num_4x4_Blocks_High[ MiSize ]
    mbToTopEdge = -((MiRow * MI_SIZE) * 8)
    mbToBottomEdge = ((MiRows - bh4 - MiRow) * MI_SIZE) * 8
    return Clip3( mbToTopEdge - border, mbToBottomEdge + border, mvec )
}".

Definition syntax_pseudocode_clamp_mv_col :=
  pseudocode_intro "
clamp_mv_col( mvec, border ) {
    bw4 = Num_4x4_Blocks_Wide[ MiSize ]
    mbToLeftEdge = -((MiCol * MI_SIZE) * 8)
    mbToRightEdge = ((MiCols - bw4 - MiCol) * MI_SIZE) * 8
    return Clip3( mbToLeftEdge - border, mbToRightEdge + border, mvec )
}".

Definition syntax_pseudocode_clear_cdef :=
  pseudocode_intro "
clear_cdef( r, c ) {
    cdef_idx[ r ][ c ] = -1
    if ( use_128x128_superblock ) {
        cdefSize4 = Num_4x4_Blocks_Wide[ BLOCK_64X64 ]
        cdef_idx[ r ][ c + cdefSize4 ] = -1
        cdef_idx[ r + cdefSize4][ c ] = -1
        cdef_idx[ r + cdefSize4][ c + cdefSize4 ] = -1
    }
}".

Definition syntax_pseudocode_read_cdef :=
  pseudocode_intro "
read_cdef( ) {
    if ( !AllLossless && !skip) {
        cdefSize4 = Num_4x4_Blocks_Wide[ BLOCK_64X64 ]
        cdefMask4 = ~(cdefSize4 - 1)
        r = MiRow & cdefMask4
        c = MiCol & cdefMask4
        if ( cdef_idx[ r ][ c ] == -1 ) {
            @@cdef_idx[ r ][ c ]                                               L(cdef_bits)
            w4 = Num_4x4_Blocks_Wide[ MiSize ]
            h4 = Num_4x4_Blocks_High[ MiSize ]
            for (i = r; i < r + h4 ; i += cdefSize4) {
                for (j = c; j < j + w4 ; j += cdefSize4) {
                    cdef_idx[ i ][ j ] = cdef_idx[ r ][ c ]
                }
            }
        }
    }
}".

Definition syntax_pseudocode_decode_lr :=
  pseudocode_intro "
decode_lr( r, c, bSize ) {
    for (plane = 0; plane < 3; plane++) {
        if (FrameRestorationType[ plane ] == RESTORE_NONE)
            continue
        subX = (plane == 0) ? 0 : subsampling_x
        subY = (plane == 0) ? 0 : subsampling_y
        w = Num_4x4_Blocks_Wide[ bSize ]
        h = Num_4x4_Blocks_High[ bSize ]
        unitSize = LoopRestorationSize[ plane ]
        unitRows = count_units_in_tile( unitSize, (MiRowEnd - MiRowStart) * MI_SIZE >> subY )
        unitCols = count_units_in_tile( unitSize, (MiColEnd - MiColStart) * MI_SIZE >> subX )
        relMiRow = r - MiRowStart
        relMiCol = c - MiColStart
        unitRowStart = ( relMiRow * ( MI_SIZE >> subY) ) / unitSize
        unitRowEnd = Min( unitRows, ( (relMiRow + h) * ( MI_SIZE >> subY) ) / unitSize)
        unitColStart = ( relMiCol * ( MI_SIZE >> subX) ) / unitSize
        unitColEnd = Min( unitCols, ( (relMiCol + w) * ( MI_SIZE >> subX) ) / unitSize)
        for (unitRow = unitRowStart; unitRow < unitRowEnd; unitRow++) {
            for (unitCol = unitColStart; unitCol < unitColEnd; unitCol++) {
                decode_lr_unit(plane, unitRow, unitCol)
            }
        }
    }
}".

Definition syntax_pseudocode_count_units_in_tile :=
  pseudocode_intro "
count_units_in_tile(unitSize, tileSize) {
  return Max((tileSize + (unitSize >> 1)) / unitSize, 1)
}".

Definition syntax_pseudocode_decode_lr_unit :=
  pseudocode_intro "
decode_lr_unit(plane, unitRow, unitCol) {
    if (FrameRestorationType[ plane ] == RESTORE_NONE) {
        restoration_type = RESTORE_NONE
    } else if (FrameRestorationType[ plane ] == RESTORE_WIENER) {
        @@use_wiener                                                           S
        restoration_type = use_wiener ? RESTORE_WIENER : RESTORE_NONE
      } else if (FrameRestorationType[ plane ] == RESTORE_SGRPROJ) {
        @@use_sgrproj                                                          S
        restoration_type = use_sgrproj ? RESTORE_SGRPROJ : RESTORE_NONE
    } else {
        @@restoration_type                                                     S
    }
    LrType[ TileNum ][ plane ][ unitRow ][ unitCol ] = restoration_type
    if (restoration_type == RESTORE_WIENER) {
        for ( pass = 0; pass < 2; pass++ ) {
            if (plane) {
                firstCoeff = 1
                LrWiener[ TileNum ][ plane ]
                        [ unitRow ][ unitCol ][ pass ][0] = 0
            } else {
                firstCoeff = 0
            }
            for (j = firstCoeff; j < 3; j++) {
                min = Wiener_Taps_Min[ j ]
                max = Wiener_Taps_Max[ j ]
                k = Wiener_Taps_K[ j ]
                v = decode_signed_subexp_with_ref_bool(
                        min, max + 1, k, RefLrWiener[ plane ][ pass ][ j ] )
                LrWiener[ TileNum ][ plane ]
                        [ unitRow ][ unitCol ][ pass ][ j ] = v
                RefLrWiener[ plane ][ pass ][ j ] = v
            }
        }
    } else if (restoration_type == RESTORE_SGRPROJ) {
        @@lr_sgr_set                                                           U(SGRPROJ_PARAMS_BITS)
        LrSgrSet[ TileNum ][ plane ][ unitRow ][ unitCol ] = lr_sgr_set
        for (i = 0; i < 2; i++) {
            min = Sgrproj_Xqd_Min[i]
            max = Sgrproj_Xqd_Max[i]
            v = decode_signed_subexp_with_ref_bool(
                     min, max + 1, SGRPROJ_PRJ_SUBEXP_K, RefSgrXqd[ plane ][ i ])
            LrSgrXqd[ TileNum ][ plane ][ unitRow ][ unitCol ][ i ] = v
            RefSgrXqd[ plane ][ i ] = v
        }
    } 
}

Wiener_Taps_Min[3] = { -5, -23, -17 }
Wiener_Taps_Max[3] = { 10,   8,  46 }
Wiener_Taps_K[3] = { 1, 2, 3 }

Sgrproj_Xqd_Min[2] = { -96, -32 }
Sgrproj_Xqd_Max[2] = {  31,  95 }".

Definition syntax_pseudocode_decode_signed_subexp_with_ref_bool :=
  pseudocode_intro "
decode_signed_subexp_with_ref_bool( low, high, k, r ) {
    x = decode_unsigned_subexp_with_ref_bool(high - low, k, r - low)
    return x + low
}".

Definition syntax_pseudocode_decode_unsigned_subexp_with_ref_bool :=
  pseudocode_intro "
decode_unsigned_subexp_with_ref_bool( mx, k, r ) {
    v = decode_subexp_bool( mx, k )
    if ((r << 1) <= mx) {
        return inverse_recenter(r, v)
    } else {
        return mx - 1 - inverse_recenter(mx - 1 - r, v)
    }
}".

Definition syntax_pseudocode_decode_subexp_bool :=
  pseudocode_intro "
decode_subexp_bool( numSyms, k ) {
    i = 0
    mk = 0
    while (1) {
        b2 = i ? k + i - 1 : k
        a = 1 << b2
        if (numSyms <= mk + 3 * a) {
            @@subexp_unif_bools                                                U(numSyms - mk)
            return subexp_unif_bools + mk
        } else {
            @@subexp_more_bools                                                L(1)
            if (subexp_more_bools) {
               i++
               mk += a
            } else {
               @@subexp_bools                                                  L(b2)
               return subexp_bools + mk
            }
        }
    }
}
".

Definition syntax_pseudocodes :=
  [
    syntax_pseudocode_open_bitstream_unit;
    syntax_pseudocode_obu_header;
    syntax_pseudocode_obu_extension_header;
    syntax_pseudocode_trailing_bits;
    syntax_pseudocode_reserved_obu;
    syntax_pseudocode_sequence_header_obu;
    syntax_pseudocode_color_config;
    syntax_pseudocode_temporal_delimiter_obu;
    syntax_pseudocode_padding_obu;
    syntax_pseudocode_metadata_obu;
    syntax_pseudocode_metadata_private_data;
    syntax_pseudocode_metadata_hdr_cll;
    syntax_pseudocode_metadata_hdr_mdcv;
    syntax_pseudocode_frame_header_obu;
    syntax_pseudocode_uncompressed_header;
    syntax_pseudocode_frame_size;
    syntax_pseudocode_render_size;
    syntax_pseudocode_frame_size_with_refs;
    syntax_pseudocode_compute_image_size;
    syntax_pseudocode_read_interpolation_filter;
    syntax_pseudocode_loop_filter_params;
    syntax_pseudocode_quantization_params;
    syntax_pseudocode_read_delta_q;
    syntax_pseudocode_segmentation_params;
    syntax_pseudocode_tile_info;
    syntax_pseudocode_tile_log2;
    syntax_pseudocode_delta_q_params;
    syntax_pseudocode_delta_lf_params;
    syntax_pseudocode_cdef_params;
    syntax_pseudocode_lr_params;
    syntax_pseudocode_read_tx_mode;
    syntax_pseudocode_frame_reference_mode;
    syntax_pseudocode_global_motion_params;
    syntax_pseudocode_read_global_param;
    syntax_pseudocode_decode_signed_subexp_with_ref;
    syntax_pseudocode_decode_unsigned_subexp_with_ref;
    syntax_pseudocode_decode_subexp;
    syntax_pseudocode_decode_uniform;
    syntax_pseudocode_inverse_recenter;
    syntax_pseudocode_inv_recenter_nonneg;
    syntax_pseudocode_tile_group_obu;
    syntax_pseudocode_decode_tile;
    syntax_pseudocode_clear_block_decoded_flags;
    syntax_pseudocode_decode_partition;
    syntax_pseudocode_decode_block;
    syntax_pseudocode_mode_info;
    syntax_pseudocode_intra_frame_mode_info;
    syntax_pseudocode_intra_segment_id;
    syntax_pseudocode_read_skip;
    syntax_pseudocode_read_delta_qindex;
    syntax_pseudocode_read_delta_lf;
    syntax_pseudocode_seg_feature_active_idx;
    syntax_pseudocode_seg_feature_active;
    syntax_pseudocode_read_tx_size;
    syntax_pseudocode_read_inter_tx_size;
    syntax_pseudocode_read_var_tx_size;
    syntax_pseudocode_inter_frame_mode_info;
    syntax_pseudocode_inter_segment_id;
    syntax_pseudocode_read_is_inter;
    syntax_pseudocode_get_segment_id;
    syntax_pseudocode_intra_block_mode_info;
    syntax_pseudocode_inter_block_mode_info;
    syntax_pseudocode_has_nearmv;
    syntax_pseudocode_needs_interp_filter;
    syntax_pseudocode_read_ref_frames;
    syntax_pseudocode_assign_mv;
    syntax_pseudocode_read_motion_mode;
    syntax_pseudocode_read_interintra_mode;
    syntax_pseudocode_read_compound_type;
    syntax_pseudocode_get_mode;
    syntax_pseudocode_read_mv;
    syntax_pseudocode_read_mv_component;
    syntax_pseudocode_residual;
    syntax_pseudocode_transform_block;
    syntax_pseudocode_transform_tree;
    syntax_pseudocode_find_tx_size;
    syntax_pseudocode_get_tx_size;
    syntax_pseudocode_get_plane_residual_size;
    syntax_pseudocode_Subsampled_Size;
    syntax_pseudocode_coeffs;
    syntax_pseudocode_compute_tx_type;
    syntax_pseudocode_get_mrow_scan;
    syntax_pseudocode_get_row_scan;
    syntax_pseudocode_get_mcol_scan;
    syntax_pseudocode_get_col_scan;
    syntax_pseudocode_get_default_scan;
    syntax_pseudocode_get_scan;
    syntax_pseudocode_read_coef;
    syntax_pseudocode_intra_angle_info;
    syntax_pseudocode_is_directional_mode;
    syntax_pseudocode_read_cfl_alphas;
    syntax_pseudocode_palette_mode_info;
    syntax_pseudocode_get_palette_cache;
    syntax_pseudocode_transform_type;
    syntax_pseudocode_get_tx_set;
    syntax_pseudocode_palette_tokens;
    syntax_pseudocode_get_palette_color_context;
    syntax_pseudocode_ref_checks;
    syntax_pseudocode_clamp_mv_row;
    syntax_pseudocode_clamp_mv_col;
    syntax_pseudocode_clear_cdef;
    syntax_pseudocode_read_cdef;
    syntax_pseudocode_decode_lr;
    syntax_pseudocode_count_units_in_tile;
    syntax_pseudocode_decode_lr_unit;
    syntax_pseudocode_decode_signed_subexp_with_ref_bool;
    syntax_pseudocode_decode_unsigned_subexp_with_ref_bool;
    syntax_pseudocode_decode_subexp_bool
  ].

Module Syntax_processor.

Definition definitionsE :=
  (map Parser.parse_pseudocode syntax_pseudocodes).

Compute definitionsE.

Theorem all_definitions_parsed :
  forallb
    (
      fun x => match x with
      | Parser.SomeE (_, []) => true
      | _ => false
      end)
    definitionsE = true.
Proof.
(* TODO *)


Definition state := Parser.token -> Z.

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive 

End Syntax_processor.

Inductive bit := bit_0 | bit_1.
Inductive byte :=
  byte_intro : forall (_ _ _ _ _ _ _ _ : bit), byte.
Definition bytestream := list byte.

End av1.

