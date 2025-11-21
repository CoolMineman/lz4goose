From lz4goose Require Import prelude.

From New.golang.theory Require Import pkg.
From New.proof Require Import std.

Require Import Coq.Arith.PeanoNat.

Inductive lz4_seq :=
| Literal (lit: list w8) (next: lz4_seq_cont)
with lz4_seq_cont := 
| Terminate
| MatchCopy (offset: nat) (matchlen: nat) (next: lz4_seq).

Definition lz4_invalid_seq : lz4_seq := Literal [] Terminate.

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
  let offset := (uint.nat off1 + (Nat.shiftl (uint.nat off2) 8))%nat in
  match (matchlen_start =? 15)%nat with
  | true =>
    let (e, skip) := var_int_parse(bs') in
    let (success, matchlen2) := e in
    match success with
    | true =>
      let (success2, next) := lz4_parse_skip skip bs' in
      match success2 with
      | true => (true, MatchCopy offset (matchlen_start + matchlen2) next)
      | false => (false, Terminate)
      end
    | false => (false, Terminate)
    end
  | false =>
    let (success, next) := lz4_parse(bs') in
    match success with
    | true => (true, MatchCopy offset matchlen_start next)
    | false => (false, Terminate)
    end
  end
| [] => (true, Terminate)
| _ => (false, Terminate)
end
with lz4_parse_skip_then_cont (skip: nat) (matchlen_start: nat) (bs: list w8) : (bool * lz4_seq_cont) :=
match skip with
| 0%nat => (false, Terminate)
| S skip' =>
  match bs with
  | _ :: bs' =>
    match skip' with
    | 0%nat => lz4_parse_cont matchlen_start bs'
    | _ => lz4_parse_skip_then_cont skip' matchlen_start bs'
    end
  | [] => (false, Terminate)
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


(*

lz4_skipn (skip: nat) (bs: list w8) {struct bs} : (bool * list w8) :=
match skip with
| 0%nat => (true, bs)
| S skip' => match bs with
  | _ :: bs' => lz4_skipn skip' bs'
  | [] => (false, [])
  end
end.


*)