(*
Generated using Gemini 3 Pro

Prompt:
"""
write an ocaml program that takes an input file and prints the result of lz4_parse

[lz4_parse.mli contents]
"""
*)
(* ============================================================ *)
(* DRIVER CODE: lz4_parse_cli.ml                                *)
(* ============================================================ *)

open Lz4_parse

(* --- 1. Helpers to convert OCaml Int -> Coq Z / Nat --- *)

let rec positive_of_int n =
  if n <= 1 then XH
  else if n mod 2 = 0 then XO (positive_of_int (n / 2))
  else XI (positive_of_int (n / 2))

let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (positive_of_int n)
  else Zneg (positive_of_int (-n))

let int_of_nat n =
  let rec aux acc = function
    | O -> acc
    | S x -> aux (acc + 1) x
  in aux 0 n

(* --- 2. Helpers to convert OCaml types -> Coq custom types --- *)

let w8_of_char c =
  let code = Char.code c in
  Obj.magic (w8_word_instance.of_Z (z_of_int code))

let rec coq_list_of_list = function
  | [] -> Nil
  | h :: t -> Cons (h, coq_list_of_list t)

let read_file_as_w8_list filename =
  let ic = open_in_bin filename in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic;
  let char_list = List.init len (String.get s) in
  let w8_l = List.map w8_of_char char_list in
  coq_list_of_list w8_l

(* --- 3. Pretty Printing the Output --- *)

let int_of_w8 w =
  match w8_word_instance.unsigned (Obj.magic w) with
  | Z0 -> 0
  | Zpos p -> 
      let rec p_to_int p acc = match p with
        | XH -> acc + 1
        | XO rest -> p_to_int rest (acc * 2)
        | XI rest -> p_to_int rest (acc * 2 + 1)
      in p_to_int p 0
  | Zneg _ -> -1

let rec print_w8_list = function
  | Nil -> ()
  | Cons (w, rest) ->
      Printf.printf "%02x " (int_of_w8 w);
      print_w8_list rest

(* Mutually recursive functions to handle the 
   type lz4_seq = Literal of ... * lz4_seq_cont
   and lz4_seq_cont = Terminate | MatchCopy of ... * lz4_seq
*)

let rec print_lz4_seq (seq : lz4_seq) =
  match seq with
  | Literal (bytes, cont) ->
      Printf.printf "  [Literal] Bytes: ";
      print_w8_list bytes;
      Printf.printf "\n";
      (* Pass the continuation to the helper function *)
      print_lz4_seq_cont cont

and print_lz4_seq_cont (cont : lz4_seq_cont) =
  match cont with
  | Terminate -> 
      Printf.printf "  [End of Sequence]\n"
  | MatchCopy (offset, length, next_seq) ->
      Printf.printf "  [Match]   Offset: %d, Length: %d\n" 
        (int_of_nat offset) (int_of_nat length);
      (* Recursively call the sequence printer for the next block *)
      print_lz4_seq next_seq

(* --- 4. Main Entry Point --- *)

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.printf "Usage: %s <input_file>\n" Sys.argv.(0);
    exit 1
  end;

  let filename = Sys.argv.(1) in
  Printf.printf "Parsing file: %s\n" filename;

  try
    let input_w8 = read_file_as_w8_list filename in
    let result = lz4_parse input_w8 in

    match result with
    | Pair (False, _) ->
        Printf.printf "Error: LZ4 Parsing Failed (Invalid Sequence)\n";
        exit 1
    | Pair (True, seq) ->
        Printf.printf "Success! Parsed Sequence:\n";
        print_lz4_seq seq

  with Sys_error msg ->
    Printf.printf "File error: %s\n" msg