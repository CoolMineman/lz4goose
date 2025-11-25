
type __ = Obj.t

type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

val sub : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val add : nat -> nat -> nat

  val double : nat -> nat

  val mul : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val even : nat -> bool

  val odd : nat -> bool

  val div2 : nat -> nat

  val shiftl : nat -> nat -> nat

  val shiftr : nat -> nat -> nat

  val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat

  val coq_land : nat -> nat -> nat
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val ldiff : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat
 end

module Coq_Pos :
 sig
  val pred_double : positive -> positive

  val pred_N : positive -> n

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val ldiff : positive -> positive -> n
 end

module N :
 sig
  val succ_double : n -> n

  val double : n -> n

  val succ_pos : n -> positive

  val sub : n -> n -> n

  val compare : n -> n -> comparison

  val leb : n -> n -> bool

  val pos_div_eucl : positive -> n -> (n, n) prod

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val ldiff : n -> n -> n

  val coq_lxor : n -> n -> n
 end

module Coq_N :
 sig
  val succ_pos : n -> positive

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val ldiff : n -> n -> n
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val pow : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val to_nat : z -> nat

  val of_N : n -> z

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val div : z -> z -> z

  val modulo : z -> z -> z

  val quotrem : z -> z -> (z, z) prod

  val quot : z -> z -> z

  val rem : z -> z -> z

  val div2 : z -> z

  val shiftl : z -> z -> z

  val shiftr : z -> z -> z

  val coq_lor : z -> z -> z

  val coq_land : z -> z -> z

  val coq_lxor : z -> z -> z

  val pred : z -> z

  val ldiff : z -> z -> z

  val lnot : z -> z
 end

val firstn : nat -> 'a1 list -> 'a1 list

val skipn : nat -> 'a1 list -> 'a1 list

type ('k, 'a, 'm) lookup = 'k -> 'm -> 'a option

val lookup0 : ('a1, 'a2, 'a3) lookup -> 'a1 -> 'a3 -> 'a2 option

module Coq_list :
 sig
  val list_lookup : (nat, 'a1, 'a1 list) lookup
 end

module Coq_word :
 sig
  type word = { unsigned : (__ -> z); signed : (__ -> z); of_Z : (z -> __);
                add : (__ -> __ -> __); sub : (__ -> __ -> __);
                opp : (__ -> __); coq_or : (__ -> __ -> __);
                coq_and : (__ -> __ -> __); xor : (__ -> __ -> __);
                not : (__ -> __); ndn : (__ -> __ -> __);
                mul : (__ -> __ -> __); mulhss : (__ -> __ -> __);
                mulhsu : (__ -> __ -> __); mulhuu : (__ -> __ -> __);
                divu : (__ -> __ -> __); divs : (__ -> __ -> __);
                modu : (__ -> __ -> __); mods : (__ -> __ -> __);
                slu : (__ -> __ -> __); sru : (__ -> __ -> __);
                srs : (__ -> __ -> __); eqb : (__ -> __ -> bool);
                ltu : (__ -> __ -> bool); lts : (__ -> __ -> bool);
                sextend : (z -> __ -> __) }

  type rep = __

  val unsigned : z -> word -> rep -> z
 end

type rep0 = z
  (* singleton inductive, whose constructor was mk *)

val wrap : z -> z -> rep0

val signed0 : z -> rep0 -> z

type special_cases = { div_by_zero : (z -> z); mod_by_zero : (z -> z);
                       adjust_too_big_shift_amount : (z -> z) }

val gen_word : z -> special_cases -> Coq_word.word

val shift_overflow_special_case_handlers : special_cases

val w8_word_instance : Coq_word.word

type w8 = Coq_word.rep

type lz4_seq =
| Literal of w8 list * lz4_seq_cont
and lz4_seq_cont =
| Terminate
| MatchCopy of nat * nat * lz4_seq

val lz4_invalid_seq : lz4_seq

val var_int_parse : w8 list -> ((bool, nat) prod, nat) prod

val lz4_parse : w8 list -> (bool, lz4_seq) prod

val lz4_parse_cont : nat -> w8 list -> (bool, lz4_seq_cont) prod

val lz4_parse_skip_then_cont :
  nat -> nat -> w8 list -> (bool, lz4_seq_cont) prod

val lz4_parse_skip : nat -> w8 list -> (bool, lz4_seq) prod

val do_match_copy : w8 list -> nat -> nat -> w8 list

val lz4_decompress : lz4_seq -> w8 list -> (bool, w8 list) prod

val lz4_decompress_cont : lz4_seq_cont -> w8 list -> (bool, w8 list) prod

val lz4_byte_decompress : w8 list -> (bool, w8 list) prod
