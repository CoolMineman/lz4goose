(* 
Generated using Opus 4.5

Prompt:
"""
write a script that lz4_decomp_cli.ml that decompresses an input file using lz4_byte_decompress and prints to standard out and exits 1 on failure

lz4_rocq.mli:
```
[Contents of lz4_rocq.mli]
```

lz4_parse_cli.ml:
```
[Contents of lz4_parse_cli.ml]
```
"""
*)
(* lz4_decomp_cli.ml - LZ4 Decompression CLI *)

open Lz4_rocq

(* --- 1. Helpers to convert OCaml Int -> Coq Z --- *)

let rec positive_of_int n =
  if n <= 1 then XH
  else if n mod 2 = 0 then XO (positive_of_int (n / 2))
  else XI (positive_of_int (n / 2))

let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (positive_of_int n)
  else Zneg (positive_of_int (-n))

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

(* --- 3. Convert w8 back to char for output --- *)

let rec int_of_positive p = match p with
  | XH -> 1
  | XO rest -> 2 * int_of_positive rest
  | XI rest -> 2 * int_of_positive rest + 1

let int_of_w8 w =
  match w8_word_instance.unsigned (Obj.magic w) with
  | Z0 -> 0
  | Zpos p -> int_of_positive p
  | Zneg _ -> 0  (* Should not happen for unsigned w8 *)

let char_of_w8 w =
  Char.chr (int_of_w8 w land 0xFF)

let rec output_w8_list = function
  | Nil -> ()
  | Cons (w, rest) ->
      print_char (char_of_w8 w);
      output_w8_list rest

(* --- 4. Main Entry Point --- *)

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <input_file>\n" Sys.argv.(0);
    exit 1
  end;

  let filename = Sys.argv.(1) in

  try
    let input_w8 = read_file_as_w8_list filename in
    let result = lz4_byte_decompress input_w8 in

    match result with
    | Pair (False, _) ->
        Printf.eprintf "Error: LZ4 decompression failed\n";
        exit 1
    | Pair (True, decompressed) ->
        output_w8_list decompressed;
        flush stdout

  with
  | Sys_error msg ->
      Printf.eprintf "File error: %s\n" msg;
      exit 1
