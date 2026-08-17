(** Scalar evolution: closed forms for values that evolve along a loop.

    A value whose per-iteration increment is a polynomial in the iteration index
    is itself a polynomial one degree higher.  Representing that polynomial in
    the binomial basis

      f(n) = a0*C(n,0) + a1*C(n,1) + ... + ad*C(n,d)

    is what makes the whole thing cheap and exact.  The coefficients in that
    basis are the finite differences of f at 0, so "start at v0 and add P on
    every iteration" is literally "prepend v0 to P's coefficients" -- no
    division, no rational arithmetic, no reconstruction of Faulhaber sums.

    Every coefficient is held modulo 2^32, which is the arithmetic the target
    actually implements: an accumulator that overflows during the loop must keep
    overflowing in the closed form, otherwise the rewrite would change the
    program's result.  Nothing here evaluates the loop -- the polynomial is
    derived from the shape of the recurrence, and its value at the trip count is
    read off with a binomial coefficient. *)

let mask = 0xFFFFFFFF

(* Coefficients live in [0, 2^32); [signed] is only applied on the way out, when
   a value becomes an IR immediate again. *)
let unsigned v = v land mask
let signed v = if v land 0x80000000 <> 0 then v - 0x100000000 else v

let addm a b = (a + b) land mask
let subm a b = (a - b) land mask

(* The product of two 32-bit values needs 64, which is one bit more than an
   OCaml int carries, so the multiply goes through Int64. *)
let mulm a b = Int64.(to_int (logand (mul (of_int a) (of_int b)) 0xFFFFFFFFL))

let negm a = subm 0 a

(* Past this the polynomials stop describing anything a ToyC program plausibly
   computes, and the samples needed to multiply them start to add up. *)
let max_degree = 6

type t = int array

let trim p =
  let length = ref (Array.length p) in
  while !length > 1 && p.(!length - 1) = 0 do decr length done;
  if !length = Array.length p then p else Array.sub p 0 !length

let degree p = Array.length (trim p) - 1
let const value = [| unsigned value |]

let const_value p =
  if degree p = 0 then Some (signed p.(0)) else None

let pad p length =
  if Array.length p >= length then p
  else Array.init length (fun i -> if i < Array.length p then p.(i) else 0)

let combine f p q =
  let length = max (Array.length p) (Array.length q) in
  let p = pad p length and q = pad q length in
  trim (Array.init length (fun i -> f p.(i) q.(i)))

let add p q = combine addm p q
let sub p q = combine subm p q
let neg p = trim (Array.map negm p)

(* Scaling is coefficient-wise in any basis. *)
let scale p factor =
  let factor = unsigned factor in
  trim (Array.map (fun a -> mulm a factor) p)

(* f evaluated at a small non-negative index, used to multiply polynomials by
   sampling.  The binomials here are tiny, so they are built incrementally in
   plain integers. *)
let sample p index =
  let acc = ref 0 in
  let binom = ref 1 in
  Array.iteri (fun k a ->
    if k > 0 then binom := !binom * (index - k + 1) / k;
    if a <> 0 && !binom <> 0 then acc := addm !acc (mulm a (unsigned !binom))
  ) p;
  !acc

(* The inverse of the finite-difference table: a_k = delta^k f(0). *)
let of_samples values =
  let count = Array.length values in
  let current = Array.copy values in
  let coeffs = Array.make count 0 in
  for k = 0 to count - 1 do
    coeffs.(k) <- current.(0);
    for j = 0 to count - k - 2 do
      current.(j) <- subm current.(j + 1) current.(j)
    done
  done;
  trim coeffs

(* Multiplication is the one operation the binomial basis does not make trivial,
   so it goes through values: sample both factors at 0..d, multiply pointwise,
   and difference the result back into coefficients.  Exact, because every step
   is a ring operation modulo 2^32. *)
let mul p q =
  let d = degree p + degree q in
  if d > max_degree then None
  else Some (of_samples (Array.init (d + 1) (fun j -> mulm (sample p j) (sample q j))))

(* f(n+1), from C(n+1,k) = C(n,k) + C(n,k-1). *)
let shift p =
  let length = Array.length p in
  trim (Array.init length (fun k -> if k + 1 < length then addm p.(k) p.(k + 1) else p.(k)))

(* The whole point of the basis: f with f(0) = init and f(n+1) - f(n) = step. *)
let antidifference init step =
  if Array.length step + 1 > max_degree + 1 then None
  else Some (trim (Array.append [| unsigned init |] step))

let equal p q = trim p = trim q

(* The inverse of an odd residue modulo 2^32.  Newton doubles the number of
   correct bits each round, and x = 1 is already correct modulo 2. *)
let inverse_odd o =
  let x = ref 1 in
  for _ = 1 to 5 do
    x := mulm !x (subm 2 (mulm o !x))
  done;
  !x

(* C(n,k) modulo 2^32, exactly.

   The product of k consecutive integers overflows long before 2^32 does, so the
   division by k! cannot wait until the end.  Its odd part is invertible modulo
   2^32 and gets multiplied in; its twos are cancelled against the factors
   themselves, which always carry enough of them because C(n,k) is an integer. *)
let binomial n k =
  if k = 0 then 1
  else if n < k then 0
  else begin
    let factorial = ref 1 in
    for j = 2 to k do factorial := !factorial * j done;
    let odd_part = ref !factorial and twos = ref 0 in
    while !odd_part land 1 = 0 do
      odd_part := !odd_part asr 1;
      incr twos
    done;
    let factors = Array.init k (fun j -> n - j) in
    Array.iteri (fun index value ->
      let value = ref value in
      while !twos > 0 && !value land 1 = 0 do
        value := !value asr 1;
        decr twos
      done;
      factors.(index) <- !value
    ) factors;
    let acc = ref (inverse_odd !odd_part) in
    Array.iter (fun value -> acc := mulm !acc (unsigned value)) factors;
    !acc
  end

(* The closed form read off at the trip count. *)
let eval p n =
  let acc = ref 0 in
  Array.iteri (fun k a ->
    if a <> 0 then acc := addm !acc (mulm a (binomial n k))
  ) p;
  signed !acc
