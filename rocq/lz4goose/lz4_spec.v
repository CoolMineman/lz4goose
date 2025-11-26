From lz4goose Require Import prelude.

From New.golang.theory Require Import pkg.
From New.proof Require Import std.

Require Import Coq.Arith.PeanoNat.

Inductive lz4_seq :=
| Literal (lit: list w8) (next: lz4_seq_cont)
with lz4_seq_cont := 
| Terminate (matchlen: nat) (* spec is unclear if bottom bits may be non-zero *)
| MatchCopy (offset: w16) (matchlen: nat) (next: lz4_seq).

Definition lz4_invalid_seq_cont : lz4_seq_cont := Terminate 0%nat.
Definition lz4_invalid_seq : lz4_seq := Literal [] lz4_invalid_seq_cont.

Fixpoint var_int_parse (bs: list w8) : (bool * nat * nat) :=
match bs with
| [] => (false, 0%nat, 0%nat)
| b :: bs' =>
  match (uint.nat b =? 255)%nat with
  | true =>
    let (e, read) := var_int_parse(bs') in
    let (success, n) := e in
    match success with
    | false => (false, 0%nat, 0%nat)
    | true => (true, (255%nat + n)%nat, (read + 1)%nat)
    end
  | false => (true, uint.nat b, 1%nat)
  end
end.

Fixpoint lz4_parse (bs: list w8) {struct bs} : (bool * lz4_seq) :=
match bs with
| [] => (false, lz4_invalid_seq)
| token :: bs' =>
  let lit_len := Nat.shiftr (uint.nat token) 4 in
  let matchlen := Nat.land (uint.nat token) 15 in
  match (lit_len =? 15)%nat with
  | true =>
    let (e, skip) := var_int_parse(bs') in
    let (success, lit_len2) := e in
    match success with
    | true =>
        let (success2, cont) := (lz4_parse_skip_then_cont (skip + lit_len + lit_len2) matchlen bs') in
        match success2 with
        | true => (true, Literal (firstn (lit_len + lit_len2)%nat (skipn skip bs')) cont)
        | false => (false, lz4_invalid_seq)
        end
    | false => (false, lz4_invalid_seq)
    end
  | false =>
    let (success2, cont) :=
      match lit_len with
      | 0%nat => lz4_parse_cont matchlen bs'
      | _ => lz4_parse_skip_then_cont lit_len matchlen bs'
      end
    in
    match success2 with
    | true => (true, Literal (firstn lit_len bs') (cont))
    | false => (false, lz4_invalid_seq)
    end
  end
end
with lz4_parse_cont (matchlen_start: nat) (bs: list w8) {struct bs} : (bool * lz4_seq_cont) :=
match bs with
| off1 :: off2 :: bs' =>
  let offset := W16 (uint.nat off1 + (Nat.shiftl (uint.nat off2) 8))%nat in
  match (matchlen_start =? 15)%nat with
  | true =>
    let (e, skip) := var_int_parse(bs') in
    let (success, matchlen2) := e in
    match success with
    | true =>
      let (success2, next) := lz4_parse_skip skip bs' in
      match success2 with
      | true => (true, MatchCopy offset (matchlen_start + matchlen2) next)
      | false => (false, lz4_invalid_seq_cont)
      end
    | false => (false, lz4_invalid_seq_cont)
    end
  | false =>
    let (success, next) := lz4_parse(bs') in
    match success with
    | true => (true, MatchCopy offset matchlen_start next)
    | false => (false, lz4_invalid_seq_cont)
    end
  end
| [] => (true, Terminate matchlen_start)
| _ => (false, lz4_invalid_seq_cont)
end
with lz4_parse_skip_then_cont (skip: nat) (matchlen_start: nat) (bs: list w8) : (bool * lz4_seq_cont) :=
match skip with
| 0%nat => (false, lz4_invalid_seq_cont)
| S skip' =>
  match bs with
  | _ :: bs' =>
    match skip' with
    | 0%nat => lz4_parse_cont matchlen_start bs'
    | _ => lz4_parse_skip_then_cont skip' matchlen_start bs'
    end
  | [] => (false, lz4_invalid_seq_cont)
  end
end
with lz4_parse_skip (skip: nat) (bs: list w8) : (bool * lz4_seq) :=
match skip with
| 0%nat => (false, lz4_invalid_seq)
| S skip' =>
  match bs with
  | _ :: bs' =>
    match skip' with
    | 0%nat => lz4_parse bs'
    | _ => lz4_parse_skip skip' bs'
    end
  | [] => (false, lz4_invalid_seq)
  end
end.

Fixpoint do_match_copy (prev: list w8) (offset: w16) (matchlen: nat): list w8 :=
match matchlen with
| 0%nat => prev
| S matchlen' =>
  match (prev !! (length prev - uint.nat offset)%nat) with
  | Some v => do_match_copy (prev ++ [v]) offset matchlen'
  | _ => []
  end
end.

Fixpoint lz4_decompress (seq: lz4_seq) (prev: list w8) : (bool * list w8) :=
match seq with
| Literal bs next => lz4_decompress_cont next (prev ++ bs)
end
with lz4_decompress_cont (seq: lz4_seq_cont) (prev: list w8) : (bool * list w8) :=
match seq with
| Terminate _ => (true, prev)
| MatchCopy offset matchlen next =>
  match ((uint.nat offset <? 1) && (uint.nat offset <? length prev))%nat with
  | true => (false, [])
  | false => lz4_decompress next (do_match_copy prev offset (matchlen + 4)%nat)
  end
end.

Definition lz4_byte_decompress (bs: list w8) : (bool * list w8) :=
let (success, seq) := lz4_parse bs in
match success with
| true => lz4_decompress seq []
| false => (false, [])
end.
