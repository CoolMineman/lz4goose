
From Stdlib Require Extraction.
Set Extraction Output Directory "ml".
Extraction Language OCaml.

From lz4goose Require Import lz4_spec.

Extraction "lz4_rocq.ml" lz4_parse lz4_byte_decompress.