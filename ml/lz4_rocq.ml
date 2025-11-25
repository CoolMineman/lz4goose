
type __ = Obj.t

type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val sub : nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k -> (match m with
            | O -> n0
            | S l -> sub k l)

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

module Nat =
 struct
  (** val add : nat -> nat -> nat **)

  let rec add n0 m =
    match n0 with
    | O -> m
    | S p -> S (add p m)

  (** val double : nat -> nat **)

  let double n0 =
    add n0 n0

  (** val mul : nat -> nat -> nat **)

  let rec mul n0 m =
    match n0 with
    | O -> O
    | S p -> add m (mul p m)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n0 m =
    match n0 with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n0 m =
    match n0 with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n0 m =
    leb (S n0) m

  (** val even : nat -> bool **)

  let rec even = function
  | O -> True
  | S n1 -> (match n1 with
             | O -> False
             | S n' -> even n')

  (** val odd : nat -> bool **)

  let odd n0 =
    negb (even n0)

  (** val div2 : nat -> nat **)

  let rec div2 = function
  | O -> O
  | S n1 -> (match n1 with
             | O -> O
             | S n' -> S (div2 n'))

  (** val shiftl : nat -> nat -> nat **)

  let rec shiftl a = function
  | O -> a
  | S n1 -> double (shiftl a n1)

  (** val shiftr : nat -> nat -> nat **)

  let rec shiftr a = function
  | O -> a
  | S n1 -> div2 (shiftr a n1)

  (** val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat **)

  let rec bitwise op n0 a b =
    match n0 with
    | O -> O
    | S n' ->
      add (match op (odd a) (odd b) with
           | True -> S O
           | False -> O)
        (mul (S (S O)) (bitwise op n' (div2 a) (div2 b)))

  (** val coq_land : nat -> nat -> nat **)

  let coq_land a b =
    bitwise (fun b1 b2 -> match b1 with
                          | True -> b2
                          | False -> False) a a b
 end

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> False)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> False)
    | XH -> (match q with
             | XH -> True
             | _ -> False)

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)
 end

module Coq_Pos =
 struct
  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)
 end

module N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Pos.succ p

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Pos.sub_mask n' m' with
          | Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val pos_div_eucl : positive -> n -> (n, n) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> Pair ((Npos XH), N0)
          | _ -> Pair (N0, (Npos XH))))

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Pos.coq_lxor p q)
 end

module Coq_N =
 struct
  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Pos.succ p

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Pos.ldiff p q)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> True
             | _ -> False)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> False)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> False)

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> O

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val pos_div_eucl : positive -> z -> (z, z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      (match ltb r' b with
       | True -> Pair ((mul (Zpos (XO XH)) q), r')
       | False -> Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b)))
    | XH ->
      (match leb (Zpos (XO XH)) b with
       | True -> Pair (Z0, (Zpos XH))
       | False -> Pair ((Zpos XH), Z0))

  (** val div_eucl : z -> z -> (z, z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos _ ->
         let Pair (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let Pair (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let Pair (_, r) = div_eucl a b in r

  (** val quotrem : z -> z -> (z, z) prod **)

  let quotrem a b =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((of_N q), (of_N r))
       | Zneg b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair (Z0, a)
       | Zpos b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Pair ((of_N q), (opp (of_N r))))

  (** val quot : z -> z -> z **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : z -> z -> z **)

  let rem a b =
    snd (quotrem a b)

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Pos.div2 p))
  | Zneg p -> Zneg (Pos.div2_up p)

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Pos.iter div2 a p

  (** val shiftr : z -> z -> z **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_land (Pos.pred_N a0) (Pos.pred_N b0))))

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Pos.pred_N a0))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Pos.pred_N b0))))

  (** val coq_lxor : z -> z -> z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Pos.coq_lxor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.coq_lxor (Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Pos.pred_N a0) (Pos.pred_N b0)))

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val ldiff : z -> z -> z **)

  let ldiff a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.ldiff a0 b0)
       | Zneg b0 -> of_N (Coq_N.coq_land (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (Coq_N.succ_pos (Coq_N.coq_lor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (Coq_N.ldiff (Coq_Pos.pred_N b0) (Coq_Pos.pred_N a0)))

  (** val lnot : z -> z **)

  let lnot a =
    pred (opp a)
 end

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n0 l =
  match n0 with
  | O -> Nil
  | S n1 ->
    (match l with
     | Nil -> Nil
     | Cons (a, l0) -> Cons (a, (firstn n1 l0)))

(** val skipn : nat -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  match n0 with
  | O -> l
  | S n1 -> (match l with
             | Nil -> Nil
             | Cons (_, l0) -> skipn n1 l0)

type ('k, 'a, 'm) lookup = 'k -> 'm -> 'a option

(** val lookup0 : ('a1, 'a2, 'a3) lookup -> 'a1 -> 'a3 -> 'a2 option **)

let lookup0 lookup1 =
  lookup1

module Coq_list =
 struct
  (** val list_lookup : (nat, 'a1, 'a1 list) lookup **)

  let rec list_lookup i = function
  | Nil -> None
  | Cons (x, l0) ->
    (match i with
     | O -> Some x
     | S i0 -> lookup0 list_lookup i0 l0)
 end

module Coq_word =
 struct
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

  (** val unsigned : z -> word -> rep -> z **)

  let unsigned _ word0 =
    word0.unsigned
 end

type rep0 = z
  (* singleton inductive, whose constructor was mk *)

(** val wrap : z -> z -> rep0 **)

let wrap width z0 =
  Z.modulo z0 (Z.pow (Zpos (XO XH)) width)

(** val signed0 : z -> rep0 -> z **)

let signed0 width =
  let wrap_value = fun z0 -> Z.modulo z0 (Z.pow (Zpos (XO XH)) width) in
  (fun z0 ->
  Z.sub
    (wrap_value (Z.add z0 (Z.pow (Zpos (XO XH)) (Z.sub width (Zpos XH)))))
    (Z.pow (Zpos (XO XH)) (Z.sub width (Zpos XH))))

type special_cases = { div_by_zero : (z -> z); mod_by_zero : (z -> z);
                       adjust_too_big_shift_amount : (z -> z) }

(** val gen_word : z -> special_cases -> Coq_word.word **)

let gen_word width sp =
  let adjust_shift_amount = fun n0 ->
    match Z.ltb n0 width with
    | True -> n0
    | False -> sp.adjust_too_big_shift_amount n0
  in
  { Coq_word.unsigned = (Obj.magic (fun r -> r)); Coq_word.signed =
  (Obj.magic signed0 width); Coq_word.of_Z = (Obj.magic wrap width);
  Coq_word.add = (fun x y ->
  Obj.magic wrap width (Z.add (Obj.magic x) (Obj.magic y))); Coq_word.sub =
  (fun x y -> Obj.magic wrap width (Z.sub (Obj.magic x) (Obj.magic y)));
  Coq_word.opp = (fun x -> Obj.magic wrap width (Z.opp (Obj.magic x)));
  Coq_word.coq_or = (fun x y ->
  Obj.magic wrap width (Z.coq_lor (Obj.magic x) (Obj.magic y)));
  Coq_word.coq_and = (fun x y ->
  Obj.magic wrap width (Z.coq_land (Obj.magic x) (Obj.magic y)));
  Coq_word.xor = (fun x y ->
  Obj.magic wrap width (Z.coq_lxor (Obj.magic x) (Obj.magic y)));
  Coq_word.not = (fun x -> Obj.magic wrap width (Z.lnot (Obj.magic x)));
  Coq_word.ndn = (fun x y ->
  Obj.magic wrap width (Z.ldiff (Obj.magic x) (Obj.magic y))); Coq_word.mul =
  (fun x y -> Obj.magic wrap width (Z.mul (Obj.magic x) (Obj.magic y)));
  Coq_word.mulhss = (fun x y ->
  Obj.magic wrap width
    (Z.div
      (Z.mul (signed0 width (Obj.magic x)) (signed0 width (Obj.magic y)))
      (Z.pow (Zpos (XO XH)) width)));
  Coq_word.mulhsu = (fun x y ->
  Obj.magic wrap width
    (Z.div (Z.mul (signed0 width (Obj.magic x)) (Obj.magic y))
      (Z.pow (Zpos (XO XH)) width)));
  Coq_word.mulhuu = (fun x y ->
  Obj.magic wrap width
    (Z.div (Z.mul (Obj.magic x) (Obj.magic y)) (Z.pow (Zpos (XO XH)) width)));
  Coq_word.divu = (fun x y ->
  Obj.magic wrap width
    (match Z.eqb (Obj.magic y) Z0 with
     | True -> sp.div_by_zero (Obj.magic x)
     | False -> Z.div (Obj.magic x) (Obj.magic y)));
  Coq_word.divs = (fun x y ->
  Obj.magic wrap width
    (match Z.eqb (signed0 width (Obj.magic y)) Z0 with
     | True -> sp.div_by_zero (signed0 width (Obj.magic x))
     | False ->
       Z.quot (signed0 width (Obj.magic x)) (signed0 width (Obj.magic y))));
  Coq_word.modu = (fun x y ->
  Obj.magic wrap width
    (match Z.eqb (Obj.magic y) Z0 with
     | True -> sp.mod_by_zero (Obj.magic x)
     | False -> Z.modulo (Obj.magic x) (Obj.magic y)));
  Coq_word.mods = (fun x y ->
  Obj.magic wrap width
    (match Z.eqb (signed0 width (Obj.magic y)) Z0 with
     | True -> sp.mod_by_zero (signed0 width (Obj.magic x))
     | False ->
       Z.rem (signed0 width (Obj.magic x)) (signed0 width (Obj.magic y))));
  Coq_word.slu = (fun x y ->
  Obj.magic wrap width
    (Z.shiftl (Obj.magic x) (adjust_shift_amount (Obj.magic y))));
  Coq_word.sru = (fun x y ->
  Obj.magic wrap width
    (Z.shiftr (Obj.magic x) (adjust_shift_amount (Obj.magic y))));
  Coq_word.srs = (fun x y ->
  Obj.magic wrap width
    (Z.shiftr (signed0 width (Obj.magic x))
      (adjust_shift_amount (Obj.magic y))));
  Coq_word.eqb = (fun x y -> Z.eqb (Obj.magic x) (Obj.magic y));
  Coq_word.ltu = (fun x y -> Z.ltb (Obj.magic x) (Obj.magic y));
  Coq_word.lts = (fun x y ->
  Z.ltb (signed0 width (Obj.magic x)) (signed0 width (Obj.magic y)));
  Coq_word.sextend = (fun oldwidth z0 ->
  Obj.magic wrap width
    (Z.sub
      (Z.modulo
        (Z.add (Obj.magic z0)
          (Z.pow (Zpos (XO XH)) (Z.sub oldwidth (Zpos XH))))
        (Z.pow (Zpos (XO XH)) oldwidth))
      (Z.pow (Zpos (XO XH)) (Z.sub oldwidth (Zpos XH))))) }

(** val shift_overflow_special_case_handlers : special_cases **)

let shift_overflow_special_case_handlers =
  { div_by_zero = (fun _ -> Zneg XH); mod_by_zero = (fun x -> x);
    adjust_too_big_shift_amount = (fun n0 -> n0) }

(** val w8_word_instance : Coq_word.word **)

let w8_word_instance =
  gen_word (Zpos (XO (XO (XO XH)))) shift_overflow_special_case_handlers

type w8 = Coq_word.rep

type lz4_seq =
| Literal of w8 list * lz4_seq_cont
and lz4_seq_cont =
| Terminate
| MatchCopy of nat * nat * lz4_seq

(** val lz4_invalid_seq : lz4_seq **)

let lz4_invalid_seq =
  Literal (Nil, Terminate)

(** val var_int_parse : w8 list -> ((bool, nat) prod, nat) prod **)

let rec var_int_parse = function
| Nil -> Pair ((Pair (False, O)), O)
| Cons (b, bs') ->
  (match Nat.eqb (Z.to_nat (w8_word_instance.Coq_word.unsigned b)) (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
   | True ->
     let Pair (e, read) = var_int_parse bs' in
     let Pair (success, n0) = e in
     (match success with
      | True ->
        Pair ((Pair (True,
          (add (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            n0))),
          (add read (S O)))
      | False -> Pair ((Pair (False, O)), O))
   | False ->
     Pair ((Pair (True, (Z.to_nat (w8_word_instance.Coq_word.unsigned b)))),
       (S O)))

(** val lz4_parse : w8 list -> (bool, lz4_seq) prod **)

let rec lz4_parse = function
| Nil -> Pair (False, lz4_invalid_seq)
| Cons (token, bs') ->
  let lit_len =
    Nat.shiftr (Z.to_nat (w8_word_instance.Coq_word.unsigned token)) (S (S (S
      (S O))))
  in
  let matchlen =
    Nat.coq_land (Z.to_nat (w8_word_instance.Coq_word.unsigned token)) (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
  in
  (match Nat.eqb lit_len (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))) with
   | True ->
     let Pair (e, skip) = var_int_parse bs' in
     let Pair (success, lit_len2) = e in
     (match success with
      | True ->
        let Pair (success2, cont) =
          lz4_parse_skip_then_cont (add (add skip lit_len) lit_len2) matchlen
            bs'
        in
        (match success2 with
         | True ->
           Pair (True, (Literal
             ((firstn (add lit_len lit_len2) (skipn skip bs')), cont)))
         | False -> Pair (False, lz4_invalid_seq))
      | False -> Pair (False, lz4_invalid_seq))
   | False ->
     let Pair (success2, cont) =
       match lit_len with
       | O -> lz4_parse_cont matchlen bs'
       | S _ -> lz4_parse_skip_then_cont lit_len matchlen bs'
     in
     (match success2 with
      | True -> Pair (True, (Literal ((firstn lit_len bs'), cont)))
      | False -> Pair (False, lz4_invalid_seq)))

(** val lz4_parse_cont : nat -> w8 list -> (bool, lz4_seq_cont) prod **)

and lz4_parse_cont matchlen_start = function
| Nil -> Pair (True, Terminate)
| Cons (off1, l) ->
  (match l with
   | Nil -> Pair (False, Terminate)
   | Cons (off2, bs') ->
     let offset =
       add (Z.to_nat (w8_word_instance.Coq_word.unsigned off1))
         (Nat.shiftl (Z.to_nat (w8_word_instance.Coq_word.unsigned off2)) (S
           (S (S (S (S (S (S (S O)))))))))
     in
     (match Nat.eqb matchlen_start (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S O))))))))))))))) with
      | True ->
        let Pair (e, skip) = var_int_parse bs' in
        let Pair (success, matchlen2) = e in
        (match success with
         | True ->
           let Pair (success2, next) = lz4_parse_skip skip bs' in
           (match success2 with
            | True ->
              Pair (True, (MatchCopy (offset, (add matchlen_start matchlen2),
                next)))
            | False -> Pair (False, Terminate))
         | False -> Pair (False, Terminate))
      | False ->
        let Pair (success, next) = lz4_parse bs' in
        (match success with
         | True -> Pair (True, (MatchCopy (offset, matchlen_start, next)))
         | False -> Pair (False, Terminate))))

(** val lz4_parse_skip_then_cont :
    nat -> nat -> w8 list -> (bool, lz4_seq_cont) prod **)

and lz4_parse_skip_then_cont skip matchlen_start bs =
  match skip with
  | O -> Pair (False, Terminate)
  | S skip' ->
    (match bs with
     | Nil -> Pair (False, Terminate)
     | Cons (_, bs') ->
       (match skip' with
        | O -> lz4_parse_cont matchlen_start bs'
        | S _ -> lz4_parse_skip_then_cont skip' matchlen_start bs'))

(** val lz4_parse_skip : nat -> w8 list -> (bool, lz4_seq) prod **)

and lz4_parse_skip skip bs =
  match skip with
  | O -> Pair (False, lz4_invalid_seq)
  | S skip' ->
    (match bs with
     | Nil -> Pair (False, lz4_invalid_seq)
     | Cons (_, bs') ->
       (match skip' with
        | O -> lz4_parse bs'
        | S _ -> lz4_parse_skip skip' bs'))

(** val do_match_copy : w8 list -> nat -> nat -> w8 list **)

let rec do_match_copy prev offset = function
| O -> prev
| S matchlen' ->
  (match lookup0 Coq_list.list_lookup (sub (length prev) offset) prev with
   | Some v -> do_match_copy (app prev (Cons (v, Nil))) offset matchlen'
   | None -> Nil)

(** val lz4_decompress : lz4_seq -> w8 list -> (bool, w8 list) prod **)

let rec lz4_decompress seq prev =
  let Literal (bs, next) = seq in lz4_decompress_cont next (app prev bs)

(** val lz4_decompress_cont :
    lz4_seq_cont -> w8 list -> (bool, w8 list) prod **)

and lz4_decompress_cont seq prev =
  match seq with
  | Terminate -> Pair (True, prev)
  | MatchCopy (offset, matchlen, next) ->
    (match match Nat.ltb offset (S O) with
           | True -> Nat.ltb offset (length prev)
           | False -> False with
     | True -> Pair (False, Nil)
     | False ->
       lz4_decompress next
         (do_match_copy prev offset (add matchlen (S (S (S (S O)))))))

(** val lz4_byte_decompress : w8 list -> (bool, w8 list) prod **)

let lz4_byte_decompress bs =
  let Pair (success, seq) = lz4_parse bs in
  (match success with
   | True -> lz4_decompress seq Nil
   | False -> Pair (False, Nil))
