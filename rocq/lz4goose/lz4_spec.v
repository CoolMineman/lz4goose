From lz4goose Require Import prelude.

From New.golang.theory Require Import pkg.
From New.proof Require Import std.

Require Import Coq.Arith.PeanoNat.

Inductive lz4_seq :=
| LitTerm (lit: list w8) (matchlen: nat) (* spec is unclear if bottom bits may be non-zero *)
| LitMatchCopy (lit: list w8) (offset: w16) (matchlen: nat) (next: lz4_seq).

Definition lz4_invalid_seq : lz4_seq := LitTerm [] 0%nat.

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
  let lit_len_start := Nat.shiftr (uint.nat token) 4 in
  let matchlen_start := Nat.land (uint.nat token) 15 in
  let (e, skip) :=
    match (lit_len_start =? 15)%nat with
    | true => var_int_parse(bs')
    | false => (true, 0%nat, 0%nat)
    end
  in
  let (success, lit_len) := e in
  match success with
  | true =>
    let bs'' := (skipn skip bs') in (* total_skip = skip *)
    let lit := (firstn (lit_len + lit_len_start)%nat bs'') in
    let bs''' := (skipn (lit_len + lit_len_start)%nat bs'') in (* total_skip = skip + lit_len + lit_len_start *)
    match bs''' with
    | [] => (true, LitTerm lit matchlen_start)
    | off1 :: off2 :: bs'''' => (* total_skip = skip + lit_len + lit_len_start + 2*)
      let offset := W16 (uint.nat off1 + (Nat.shiftl (uint.nat off2) 8))%nat in
      let (e2, skip2) :=
        match (matchlen_start =? 15) with
        | true => var_int_parse(bs'''')
        | false => (true, 0%nat, 0%nat)
        end
      in (* total_skip = skip + lit_len + lit_len_start + 2 + skip2*)
      let (success2, matchlen) := e2 in
      match success2 with
      | true =>
        let (success3, next) := lz4_skip_parse (skip + lit_len + lit_len_start + 2 + skip2)%nat bs' in
        (true, LitMatchCopy lit offset (matchlen + matchlen_start)%nat next)
      | false => (false, lz4_invalid_seq)
      end
    | _ => (false, lz4_invalid_seq)
    end
  | false => (false, lz4_invalid_seq)
  end
end
with lz4_skip_parse (skip: nat) (bs: list w8) : (bool * lz4_seq) :=
match skip with
| 0%nat => (false, lz4_invalid_seq)
| S skip' =>
  match bs with
  | _ :: bs' =>
    match skip' with
    | 0%nat => lz4_parse bs'
    | _ => lz4_skip_parse skip' bs'
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
| LitTerm lit _ => (true, prev ++ lit)
| LitMatchCopy lit offset matchlen next =>
  let prev' := prev ++ lit in
  match ((uint.nat offset <? 1) && (uint.nat offset <? length prev'))%nat with
  | true => (false, [])
  | false => lz4_decompress next (do_match_copy prev' offset (matchlen + 4)%nat)
  end
end.

Definition lz4_byte_decompress (bs: list w8) : (bool * list w8) :=
let (success, seq) := lz4_parse bs in
match success with
| true => lz4_decompress seq []
| false => (false, [])
end.
