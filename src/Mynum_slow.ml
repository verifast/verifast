open Printf

let fprintff chan = kfprintf flush chan
let printff format = fprintff stdout format

type num =
  SmallNum of int * int
| BigNum of Num.num

let zero_num = SmallNum (0, 1)

let gcd p q =
  let rec iter a b =
    if b = 0 then
      a
    else
      iter b (a mod b)
  in
  let gcd_pos p q =
    if p < q then iter q p else iter p q
  in
  if p < 0 then
    gcd_pos (-p) q
  else
    gcd_pos p q

let num_of_ints p q =
  assert (0 < q);
  if p = min_int then
    BigNum (Num.div_num (Num.num_of_int p) (Num.num_of_int q))
  else begin
    if p = 0 then
      assert (q = 1)
    else
      assert (gcd p q = 1);
    SmallNum (p, q)
  end

let num_of_int p =
  if p = min_int then BigNum (Num.num_of_int p) else SmallNum (p, 1)

let num_of_big_int n =
  if Big_int.is_int_big_int n then
    let n = Big_int.int_of_big_int n in
    if n = min_int then BigNum (Num.num_of_int n) else SmallNum (n, 1)
  else
    BigNum (Num.num_of_big_int n)

let invert_num n =
  match n with
    SmallNum (p, q) ->
    assert (p <> 0);
    if p < 0 then SmallNum (-q, -p) else SmallNum (q, p)
  | BigNum n -> BigNum (Num.div_num (Num.num_of_int 1) n)

let big_num_of_num n =
  match n with
    SmallNum (p, q) -> Num.div_num (Num.num_of_int p) (Num.num_of_int q)
  | BigNum n -> n

let mult_num n1 n2 =
  match (n1, n2) with
    (SmallNum (p1, q1), SmallNum (p2, q2)) when
    (-32767) <= p1 && p1 <= 32767 && q1 <= 32767 &&
    (-32767) <= p2 && p2 <= 32767 && q2 <= 32767 ->
    let p = p1 * p2 in
    if p = 0 then SmallNum (0, 1) else
    let q = q1 * q2 in
    let d = gcd p q in
    (* printff "Mynum.mult_num: small multiplication\n"; *)
    SmallNum (p / d, q / d)
  | _ ->
    (* printff "Mynum.mult_num: big multiplication\n"; *)
    BigNum (Num.mult_num (big_num_of_num n1) (big_num_of_num n2))

let div_num n1 n2 = mult_num n1 (invert_num n2)

let compare_num n1 n2 =
  match (n1, n2) with
    (SmallNum (p1, q1), SmallNum (p2, q2)) when
    (-32767) <= p1 && p1 <= 32767 && q1 <= 32767 &&
    (-32767) <= p2 && p2 <= 32767 && q2 <= 32767 ->
    compare (p1 * q2) (p2 * q1)
  | _ -> Num.compare_num (big_num_of_num n1) (big_num_of_num n2)

let string_of_num n =
  match n with
    SmallNum (p, q) -> Printf.sprintf "%d/%d!" p q
  | BigNum n -> Num.string_of_num n

let num_of_string s =
  let n = Num.num_of_string s in
  let r = Num.ratio_of_num n in
  let p = Ratio.numerator_ratio r in
  let q = Ratio.denominator_ratio r in
  if Big_int.is_int_big_int p && Big_int.is_int_big_int q then
    num_of_ints (Big_int.int_of_big_int p) (Big_int.int_of_big_int q)
  else BigNum n

let add_num n1 n2 =
  match (n1, n2) with
    (SmallNum (p1, q1), SmallNum (p2, q2)) when
    (-32767) <= p1 && p1 <= 32767 && q1 <= 32767 &&
    (-32767) <= p2 && p2 <= 32767 && q2 <= 32767 ->
    let p = p1 * q2 + p2 * q1 in
    let q = q1 * q2 in
    if p = 0 then zero_num else
    let d = gcd p q in
    (* printff "Mynum.add_num: small addition\n"; *)
    SmallNum (p / d, q / d)
  | _ ->
    (* printff "Mynum.add_num: big addition\n"; *)
    BigNum (Num.add_num (big_num_of_num n1) (big_num_of_num n2))

let minus_num n =
  match n with
    SmallNum (p, q) -> SmallNum (-p, q)
  | BigNum n -> BigNum (Num.minus_num n)

let sub_num n1 n2 = add_num n1 (minus_num n2)

let eq_num n1 n2 =
  match (n1, n2) with
    (SmallNum (p1, q1), SmallNum (p2, q2)) ->
    p1 = p2 && q1 = q2
  | _ -> Num.eq_num (big_num_of_num n1) (big_num_of_num n2)

let (+/) = add_num
let (-/) = sub_num
let ( */ ) = mult_num
let (//) = div_num
let (=/) = eq_num

let sign_num n =
  match n with
    SmallNum (p, q) ->
    if p < 0 then -1 else if p = 0 then 0 else 1
  | BigNum n -> Num.sign_num n

let abs_num n =
  match n with
    SmallNum (p, q) ->
    SmallNum (abs p, q)
  | BigNum n -> BigNum (Num.abs_num n)

let (<=/) n1 n2 = compare_num n1 n2 <= 0
let (</) n1 n2 = compare_num n1 n2 < 0
