import OMAReductions.R_PolyTime_isPolyTime_primeFactorsList_R1
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Size
import Mathlib.Data.Num.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.DeriveFintype
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Nat.Sqrt
import Mathlib.Computability.Encoding

/-!
# Polynomial-time extension of bounded factorial comparisons

Credit: @neiam00

A finite-stack preprocessor evaluates the small and even cases and computes the integer square-root cutoff by bounded search using binary division. A second machine returns the forced constants or forwards the original comparator on the capped pair.
-/

/-
# Length of the encoded prime factor list

The integer-factorization conjecture encodes each prime in binary, writing two
bits per payload bit and one delimiter per factor. The total length is at most
five times the floor of the binary logarithm of the input. Powers of two attain
the bound.
-/

namespace FactorEncoding

open BitstringEncoding

private theorem length_encodePosNum (p : PosNum) :
    (Computability.encodePosNum p).length = p.natSize := by
  induction p <;> simp_all [Computability.encodePosNum, PosNum.natSize]

/-- The canonical encoding uses the usual number of binary digits. -/
theorem length_bitEncode_nat (n : ℕ) : (bitEncode n).length = n.size := by
  have hnum (m : Num) : (Computability.encodeNum m).length = m.natSize := by
    cases m with
    | zero => rfl
    | pos p => exact length_encodePosNum p
  calc
    (bitEncode n).length = (n : Num).natSize := hnum (n : Num)
    _ = n.size := by rw [Num.natSize_to_nat, Num.to_of_nat]

private theorem length_bitEncode_pos {n : ℕ} (hn : n ≠ 0) :
    (bitEncode n).length = n.log2 + 1 := by
  rw [length_bitEncode_nat]
  have hlo : n.log2 < n.size := Nat.lt_size.mpr (Nat.log2_self_le hn)
  have hhi : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  omega

private theorem length_bitEncode_cons (p : ℕ) (ps : List ℕ) :
    (bitEncode (p :: ps)).length = 2 * (bitEncode p).length + 1 + (bitEncode ps).length := by
  change (delimit (bitEncode p) ++ bitEncode ps).length = _
  rw [List.length_append, length_delimit]

private theorem length_bitEncode_le_log2_prod (ps : List ℕ) (h : ∀ p ∈ ps, 2 ≤ p) :
    (bitEncode ps).length ≤ 5 * ps.prod.log2 := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    have hp : 2 ≤ p := h p (by simp)
    have ht : ∀ q ∈ ps, 2 ≤ q := fun q hq => h q (by simp [hq])
    have hp0 : p ≠ 0 := by omega
    have ht0 : ps.prod ≠ 0 := by
      apply List.prod_ne_zero
      intro hz
      have := ht 0 hz
      omega
    have hbit : 1 ≤ p.log2 := (Nat.le_log2 hp0).mpr (by simpa using hp)
    have hlog : p.log2 + ps.prod.log2 ≤ (p * ps.prod).log2 := by
      apply (Nat.le_log2 (Nat.mul_ne_zero hp0 ht0)).mpr
      rw [pow_add]
      exact Nat.mul_le_mul (Nat.log2_self_le hp0) (Nat.log2_self_le ht0)
    have htail := ih ht
    rw [length_bitEncode_cons, length_bitEncode_pos hp0, List.prod_cons]
    omega

/-- A sharp upper bound on the length of the actual output in the conjecture. -/
theorem primeFactorsList_length_bound (n : ℕ) :
    (bitEncode n.primeFactorsList).length ≤ 5 * n.log2 := by
  by_cases hn : n = 0
  · subst n
    rw [Nat.primeFactorsList_zero]
    exact Nat.zero_le _
  · have h := length_bitEncode_le_log2_prod n.primeFactorsList
        (fun _ hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
    simpa only [Nat.prod_primeFactorsList hn] using h

/-- Each occurrence of the prime two contributes exactly five bits. -/
theorem primeFactorsList_length_two_pow (k : ℕ) :
    (bitEncode (2 ^ k).primeFactorsList).length = 5 * k := by
  rw [Nat.prime_two.primeFactorsList_pow]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, length_bitEncode_cons, ih]
    have htwo : (bitEncode (2 : ℕ)).length = 2 := by decide
    omega

end FactorEncoding

/-
# Cost of the comparator calls in the factor search

The recursion in the third hypothesis of the integer-factorization reduction
reads one threshold bit at a time. We record the pairs it passes to the
comparator. On an input of length `L`, the total of its comparator clocks is at
most `L * P.eval (3 * L + 1)`, for every clock polynomial `P` over the naturals.
This accounts for the oracle calls. A machine implementing the surrounding
control flow additionally needs to construct its queries and maintain its state.
-/

namespace FactorSearchClock

open BitstringEncoding

/-- The value and ordered oracle calls of a search in the interval
`[low, low + 2^k)`. -/
def run (query : ℕ × ℕ → Bool) (n : ℕ) : (k low : ℕ) → ℕ × List (ℕ × ℕ)
  | 0, low => (low, [])
  | k + 1, low =>
    let pivot := low + 2 ^ k - 1
    let next := if query (n, pivot) then low else low + 2 ^ k
    let rest := run query n k next
    (rest.1, (n, pivot) :: rest.2)

/-- Apply the guard and initial interval from the submitted reduction. -/
def search (query : ℕ × ℕ → Bool) (n : ℕ) : ℕ × List (ℕ × ℕ) :=
  if n < 2 then (2 - n, []) else run query n (n.log2 + 1) 0

private theorem run_value (query : ℕ × ℕ → Bool) (n k low : ℕ) :
    (run query n k low).1 =
      (Nat.rec (motive := fun _ => ℕ → ℕ) id
        (fun i search low =>
          if query (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i)) k) low := by
  induction k generalizing low with
  | zero => rfl
  | succ k ih =>
    simp only [run]
    split <;> apply ih

/-- Forgetting the trace gives the exact function in the third hypothesis. -/
theorem search_value (query : ℕ × ℕ → Bool) (n : ℕ) :
    (search query n).1 =
      if n < 2 then 2 - n else
        (Nat.rec (motive := fun _ => ℕ → ℕ) id
          (fun i search low =>
            if query (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i))
          (n.log2 + 1)) 0 := by
  by_cases hn : n < 2 <;> simp [search, hn, run_value]

private theorem run_queries (query : ℕ × ℕ → Bool) (n L k low : ℕ)
    (hi : low + 2 ^ k ≤ 2 ^ L) :
    (run query n k low).2.length = k ∧
    ∀ x ∈ (run query n k low).2, x.1 = n ∧ x.2 < 2 ^ L := by
  induction k generalizing low with
  | zero => simp [run]
  | succ k ih =>
    let next := if query (n, low + 2 ^ k - 1) then low else low + 2 ^ k
    rw [Nat.pow_succ] at hi
    have hp : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hnext : next + 2 ^ k ≤ 2 ^ L := by
      dsimp [next]
      split <;> omega
    obtain ⟨hc, hb⟩ := ih next hnext
    change ((n, low + 2 ^ k - 1) :: (run query n k next).2).length = k + 1 ∧ _
    constructor
    · simpa only [List.length_cons] using congrArg Nat.succ hc
    · intro x hx
      change x ∈ (n, low + 2 ^ k - 1) :: (run query n k next).2 at hx
      rcases List.mem_cons.mp hx with h | h
      · subst x
        exact ⟨rfl, by dsimp; omega⟩
      · exact hb x h

/-- The canonical binary pair format delimits its first component and appends
the bare encoding of its second component. -/
theorem pair_length (n b : ℕ) :
    (bitEncode (n, b)).length = 2 * n.size + 1 + b.size := by
  change (delimit (bitEncode n) ++ bitEncode b).length = _
  simp only [List.length_append, length_delimit, FactorEncoding.length_bitEncode_nat]

private theorem bit_length_eq_log2_succ {n : ℕ} (hn : n ≠ 0) : n.size = n.log2 + 1 := by
  have hlo := Nat.lt_size.mpr (Nat.log2_self_le hn)
  have hhi : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  omega

/-- The number of calls and the size of every queried pivot and encoded pair.
Inputs zero and one issue no calls. -/
theorem search_queries (query : ℕ × ℕ → Bool) (n : ℕ) :
    (search query n).2.length = (if n < 2 then 0 else (bitEncode n).length) ∧
      ∀ x ∈ (search query n).2,
        (bitEncode x.2).length ≤ (bitEncode n).length ∧
        (bitEncode x).length ≤ 3 * (bitEncode n).length + 1 := by
  by_cases hn : n < 2
  · simp [search, hn]
  · have hL := bit_length_eq_log2_succ (by omega : n ≠ 0)
    obtain ⟨hl, hq⟩ := run_queries query n (n.log2 + 1) (n.log2 + 1) 0 (by simp)
    simp only [search, if_neg hn, FactorEncoding.length_bitEncode_nat]
    refine ⟨hl.trans hL.symm, ?_⟩
    rintro ⟨n', b⟩ hx
    obtain ⟨heq, hb⟩ := hq _ hx
    change n' = n at heq
    subst n'
    have hbits : b.size ≤ n.size := hL ▸ Nat.size_le.mpr hb
    simpa only [pair_length, FactorEncoding.length_bitEncode_nat] using
      And.intro hbits (by omega : 2 * n.size + 1 + b.size ≤ 3 * n.size + 1)

private theorem eval_monotone (P : Polynomial ℕ) : Monotone P.eval := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    intro a b h
    simpa only [Polynomial.eval_add] using Nat.add_le_add (hp h) (hq h)
  | monomial k c =>
    intro a b h
    simpa only [Polynomial.eval_monomial] using
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

private theorem sum_map_le (f : α → ℕ) (xs : List α) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simpa only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_comm C]
      using Nat.add_le_add hx ht

/-- The aggregate time budget for the actual comparator calls, with the same
bit encoding as the comparator's polynomial-time Turing machine. -/
theorem search_clock (query : ℕ × ℕ → Bool) (P : Polynomial ℕ) (n : ℕ) :
    (((search query n).2.map (fun x => P.eval (bitEncode x).length)).sum) ≤
      (bitEncode n).length * P.eval (3 * (bitEncode n).length + 1) := by
  obtain ⟨hl, hq⟩ := search_queries query n
  apply (sum_map_le _ _ _ (fun x hx => eval_monotone P (hq x hx).2)).trans
  apply Nat.mul_le_mul_right
  rw [hl]
  split <;> omega

/-- As a polynomial in the input length, the bound is `X * P(3X+1)`. -/
theorem search_clock_polynomial (query : ℕ × ℕ → Bool) (P : Polynomial ℕ) (n : ℕ) :
    (((search query n).2.map (fun x => P.eval (bitEncode x).length)).sum) ≤
      (Polynomial.X * P.comp (3 * Polynomial.X + 1)).eval (bitEncode n).length := by
  simpa using search_clock query P n

/-- Each transition count comes from the comparator machine's certified evaluation
on the actual pair sent to it. The clock bound therefore applies to the sum of
these transition counts. -/
theorem comparator_steps {query : ℕ × ℕ → Bool}
    (machine : Turing.TM2ComputableInPolyTime bitEncode bitEncode query) (n : ℕ) :
    (((search query n).2.map (fun x => (machine.outputsFun x).steps)).sum) ≤
      (Polynomial.X * machine.time.comp (3 * Polynomial.X + 1)).eval (bitEncode n).length := by
  apply le_trans _ (search_clock_polynomial query machine.time n)
  exact List.sum_le_sum fun x _ => (machine.outputsFun x).steps_le_m

end FactorSearchClock

/-
# Building factor-search queries from bits

All words use the little-endian natural-number encoding in the factorization
conjecture. The search retains the already chosen high bits as a canonical
word. The remaining input bits serve as a counter, one bit per comparison.
-/

namespace FactorSearchBits

open Computability BitstringEncoding

/-- Extend the high prefix by a less significant digit, retaining the empty word
for zero. -/
def digit : Bool → List Bool → List Bool
  | false, [] => []
  | b, high => b :: high

/-- Each remaining bit supplies a low one in the last candidate of the lower
half. The zero immediately above these ones is significant when `high` is nonempty. -/
def pivot (remaining high : List Bool) : List Bool :=
  remaining.map (fun _ => true) ++ digit false high

/-- A raw query on the comparator's input stack. -/
def queryWord (input remaining high : List Bool) : List Bool :=
  delimit input ++ pivot remaining high

/-- Read one comparator answer per remaining bit, processing positions from
most to least significant. -/
def run (compare : List Bool → Bool) (input : List Bool) :
    List Bool → List Bool → List Bool
  | [], high => high
  | _ :: remaining, high =>
    let answer := compare (queryWord input remaining high)
    run compare input remaining (digit (!answer) high)

/-- Handle zero and one according to the search specification. For a canonical
input of length at least two, all bits contribute one comparison. -/
def search (compare : List Bool → Bool) (input : List Bool) : List Bool :=
  match input with
  | [] => [false, true]
  | [_] => [true]
  | _ :: _ :: _ => run compare input input []

/-- Extending a canonical prefix implements the binary place-value recurrence. -/
theorem digit_encode (b : Bool) (h : ℕ) :
    digit b (encodeNat h) = encodeNat (2 * h + b.toNat) := by
  have hb : 2 * h + b.toNat = Nat.bit b h := by cases b <;> simp [Nat.bit]
  change digit b (encodeNum (h : Num)) = encodeNum ((2 * h + b.toNat : ℕ) : Num)
  rw [hb, ← Num.ofNat'_eq (Nat.bit b h), Num.ofNat'_bit, Num.ofNat'_eq h]
  cases b <;> cases (h : Num) with
    | zero => rfl
    | pos p => cases p <;> rfl

private theorem leading_ones (remaining : List Bool) (x : ℕ) :
    remaining.map (fun _ => true) ++ encodeNat x =
      encodeNat ((x + 1) * 2 ^ remaining.length - 1) := by
  induction remaining with
  | nil => simp
  | cons bit rest ih =>
    change true :: (rest.map (fun _ => true) ++ encodeNat x) = _
    rw [ih]
    rw [← show digit true (encodeNat ((x + 1) * 2 ^ rest.length - 1)) =
        true :: encodeNat ((x + 1) * 2 ^ rest.length - 1) from rfl, digit_encode]
    congr 1
    have hp : 0 < (x + 1) * 2 ^ rest.length := Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
    simp only [Bool.toNat_true, List.length_cons, Nat.pow_succ, ← Nat.mul_assoc]
    omega

/-- For `k` bits after the queried position, the interval starts at
`h * 2^(k+1)`, and the query asks about its lower half's upper endpoint. -/
theorem pivot_encode (remaining : List Bool) (h : ℕ) :
    pivot remaining (encodeNat h) =
      encodeNat (h * 2 ^ (remaining.length + 1) + 2 ^ remaining.length - 1) := by
  rw [pivot, digit_encode, leading_ones]
  simp only [Bool.toNat_false, Nat.add_zero, Nat.pow_succ]
  congr 2
  ring

/-- The concrete query word uses the exact paired-input encoding of H3. -/
theorem queryWord_encode (n : ℕ) (remaining : List Bool) (h : ℕ) :
    queryWord (encodeNat n) remaining (encodeNat h) =
      bitEncode (n, h * 2 ^ (remaining.length + 1) + 2 ^ remaining.length - 1) := by
  change delimit (encodeNat n) ++ pivot remaining (encodeNat h) = _
  rw [pivot_encode]
  rfl

/-- Invariant of the word search. With `k` unprocessed bits, the numeric
search interval starts at `h * 2^k`. -/
theorem run_encode (compare : List Bool → Bool) (query : ℕ × ℕ → Bool)
    (hq : ∀ x, compare (bitEncode x) = query x) (n : ℕ) (remaining : List Bool) (h : ℕ) :
    run compare (encodeNat n) remaining (encodeNat h) =
      encodeNat (FactorSearchClock.run query n remaining.length (h * 2 ^ remaining.length)).1 := by
  induction remaining generalizing h with
  | nil => simp [run, FactorSearchClock.run]
  | cons bit rest ih =>
    simp only [run, queryWord_encode, hq, List.length_cons, FactorSearchClock.run]
    cases ha : query (n, h * 2 ^ (rest.length + 1) + 2 ^ rest.length - 1) <;>
      simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true,
        digit_encode, Bool.toNat_true, Bool.toNat_false, Nat.add_zero, ih]
    · congr 3
      rw [Nat.pow_succ]
      ring
    · congr 3
      rw [Nat.pow_succ]
      ring

/-- The output of the word-level algorithm is the canonical encoding of exactly
the guarded arithmetic recursion used in H3. -/
theorem search_encode (compare : List Bool → Bool) (query : ℕ × ℕ → Bool)
    (hq : ∀ x, compare (bitEncode x) = query x) (n : ℕ) :
    search compare (encodeNat n) = encodeNat
      (if n < 2 then 2 - n else
        (Nat.rec (motive := fun _ => ℕ → ℕ) id
          (fun i search low =>
            if query (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i))
          (n.log2 + 1)) 0) := by
  rw [← FactorSearchClock.search_value]
  by_cases hn : n < 2
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;>
      simp only [FactorSearchClock.search, if_pos hn] <;> rfl
  · have hlen : (encodeNat n).length = n.log2 + 1 := by
      change (bitEncode n).length = _
      rw [FactorEncoding.length_bitEncode_nat]
      have hlo := Nat.lt_size.mpr (Nat.log2_self_le (by omega : n ≠ 0))
      have hhi : n.size ≤ n.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
      omega
    have hlength : 2 ≤ (encodeNat n).length := by
      have := (Nat.le_log2 (by omega : n ≠ 0)).mpr (by omega : 2 ^ 1 ≤ n)
      omega
    have hstart : search compare (encodeNat n) = run compare (encodeNat n) (encodeNat n) [] := by
      cases hword : encodeNat n with
      | nil => simp [hword] at hlength
      | cons b rest =>
        cases rest <;> simp_all [search]
    rw [hstart, ← show encodeNat 0 = [] from rfl, run_encode compare query hq, hlen]
    simp [FactorSearchClock.search, hn]

end FactorSearchBits

/-
# Binary long division on canonical words

Read the numerator from the most significant bit. Each step appends the input
bit to the remainder and tests a subtraction of the denominator. The final
borrow determines the next quotient bit. All words passed to the next step use
the same little-endian encoding as the factorization target.
-/

namespace FactorDivisionBits

open Computability FactorSearchBits

/-- Arithmetic value of a little-endian word, including padded words. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * value bs + b.toNat

def diffBit (a b carry : Bool) : Bool := xor (xor a b) carry

def borrowBit (a b carry : Bool) : Bool := (!a && (b || carry)) || (b && carry)

/-- Scan the candidate from its low end. An exhausted denominator supplies zero
bits. A remaining nonempty suffix of a canonical denominator is nonzero. -/
def trial : List Bool → List Bool → Bool → Bool × List Bool
  | [], v, carry => (carry || !v.isEmpty, [])
  | a :: as, v, carry =>
    let b := v.head?.getD false
    let higher := trial as v.tail (borrowBit a b carry)
    (higher.1, diffBit a b carry :: higher.2)

/-- Drop high zeroes from a least-significant-bit-first word. -/
def trim (w : List Bool) : List Bool := (w.reverse.dropWhile (!·)).reverse

/-- The state holds the quotient prefix and the current remainder, in that order. -/
def divisionStep (den : List Bool) (qr : List Bool × List Bool) (b : Bool) :
    List Bool × List Bool :=
  let x := digit b qr.2
  let t := trial x den false
  (digit (!t.1) qr.1, if t.1 then x else trim t.2)

/-- The zero divisor returns the empty encoding of zero, matching natural division. -/
def divide (num den : List Bool) : List Bool :=
  if den.isEmpty then [] else (num.reverse.foldl (divisionStep den) ([], [])).1

private theorem toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

theorem digit_length (b : Bool) (w : List Bool) :
    (digit b w).length ≤ w.length + 1 := by
  cases b <;> cases w <;> simp [digit]

theorem trial_length (u v : List Bool) (c : Bool) :
    (trial u v c).2.length = u.length := by
  induction u generalizing v c with
  | nil => rfl
  | cons a as ih => simp [trial, ih]

theorem trim_length (w : List Bool) : (trim w).length ≤ w.length := by
  simpa [trim] using (List.dropWhile_sublist (l := w.reverse) (!·)).length_le

private theorem digit_value (b : Bool) (w : List Bool) :
    value (digit b w) = 2 * value w + b.toNat := by
  cases b <;> cases w <;> rfl

private theorem bit_arith (b : Bool) (n : ℕ) : Nat.bit b n = 2 * n + b.toNat := by
  cases b <;> simp [Nat.bit]

theorem value_encodeNat (n : ℕ) : value (encodeNat n) = n := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit b n ih => rw [bit_arith, ← digit_encode, digit_value, ih]

private def Canonical : List Bool → Prop
  | [] => True
  | b :: bs => (b = true ∨ 0 < value bs) ∧ Canonical bs

private theorem value_pos {b : Bool} {w : List Bool} (hw : Canonical (b :: w)) :
    0 < value (b :: w) := by
  rcases hw.1 with rfl | h <;> simp [value]
  omega

private theorem canonical_digit (b : Bool) (w : List Bool) (hw : Canonical w) :
    Canonical (digit b w) := by
  cases w with
  | nil => cases b <;> simp [digit, Canonical]
  | cons a as =>
    have hp := value_pos hw
    cases b <;> exact ⟨Or.inr hp, hw⟩

private theorem canonical_encode (n : ℕ) : Canonical (encodeNat n) := by
  induction n using Nat.binaryRec with
  | zero => trivial
  | bit b n ih => rw [bit_arith, ← digit_encode]; exact canonical_digit _ _ ih

private theorem trim_cons (b : Bool) (w : List Bool) : trim (b :: w) = digit b (trim w) := by
  simp only [trim, List.reverse_cons, List.dropWhile_append]
  cases h : (w.reverse.dropWhile (!·)) with
  | nil => cases b <;> rfl
  | cons a rest =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append]
    cases b <;> simp [digit]

theorem trim_encode (w : List Bool) : trim w = encodeNat (value w) := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [trim_cons, ih, digit_encode, value]

private theorem sub_digit_identity (a b c : Bool) :
    a.toNat + 2 * (borrowBit a b c).toNat = b.toNat + c.toNat + (diffBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

private theorem trial_spec (u v : List Bool) (c : Bool) (hv : Canonical v) :
    ((trial u v c).1 = true ↔ value u < value v + c.toNat) ∧
    ((trial u v c).1 = false → value (trial u v c).2 + value v + c.toNat = value u) := by
  induction u generalizing v c with
  | nil =>
    cases v with
    | nil => cases c <;> decide
    | cons b bs =>
      have hp := value_pos hv
      cases c <;> simp [trial, value] at *
      omega
  | cons a as ih =>
    let b := v.head?.getD false
    have htail : Canonical v.tail := by cases v with
      | nil => trivial
      | cons d ds => exact hv.2
    have hval : value v = 2 * value v.tail + b.toNat := by cases v <;> rfl
    obtain ⟨hborrow, hdiff⟩ := ih v.tail (borrowBit a b c) htail
    have hbit := sub_digit_identity a b c
    have hsmall := toNat_le_one (diffBit a b c)
    change ((trial as v.tail (borrowBit a b c)).1 = true ↔ 2 * value as + a.toNat < value v + c.toNat) ∧
      ((trial as v.tail (borrowBit a b c)).1 = false →
        2 * value (trial as v.tail (borrowBit a b c)).2 + (diffBit a b c).toNat +
          value v + c.toNat = 2 * value as + a.toNat)
    rw [hborrow, hval]
    constructor
    · omega
    · intro hc
      have := hdiff hc
      omega

/-- A single bit scan compares with the denominator and, on success, produces
the canonical nonnegative difference after trimming. -/
theorem trial_encode (u d : ℕ) :
    ((trial (encodeNat u) (encodeNat d) false).1 = true ↔ u < d) ∧
    (d ≤ u → trim (trial (encodeNat u) (encodeNat d) false).2 = encodeNat (u - d)) := by
  obtain ⟨hb, hs⟩ := trial_spec (encodeNat u) (encodeNat d) false (canonical_encode d)
  simp only [value_encodeNat, Bool.toNat_false, Nat.add_zero] at hb hs
  refine ⟨hb, fun h => ?_⟩
  have hf : (trial (encodeNat u) (encodeNat d) false).1 = false := by
    cases h' : (trial (encodeNat u) (encodeNat d) false).1 with
    | false => rfl
    | true => exact False.elim ((Nat.not_lt.mpr h) (hb.mp h'))
  rw [trim_encode]
  congr 1
  have := hs hf
  omega

/-- One input digit extends the value of the processed prefix from `a` to
`2*a+b`, preserving the exact quotient and remainder. -/
theorem divisionStep_encode (d a : ℕ) (hd : 0 < d) (b : Bool) :
    divisionStep (encodeNat d) (encodeNat (a / d), encodeNat (a % d)) b =
      (encodeNat ((2 * a + b.toNat) / d), encodeNat ((2 * a + b.toNat) % d)) := by
  let x := 2 * (a % d) + b.toNat
  have hx : x < 2 * d := by
    have := Nat.mod_lt a hd
    have := toNat_le_one b
    dsimp [x]
    omega
  have hsplit : 2 * a + b.toNat = x + d * (2 * (a / d)) := by
    have h := Nat.mod_add_div a d
    dsimp [x]
    calc
      2 * a + b.toNat = 2 * (a % d + d * (a / d)) + b.toNat := by rw [h]
      _ = _ := by ring
  have hq : (2 * a + b.toNat) / d = x / d + 2 * (a / d) := by
    rw [hsplit, Nat.add_mul_div_left _ _ hd]
  have hr : (2 * a + b.toNat) % d = x % d := by rw [hsplit, Nat.add_mul_mod_self_left]
  obtain ⟨hborrow, hdiff⟩ := trial_encode x d
  change (digit (!(trial (digit b (encodeNat (a % d))) (encodeNat d) false).1) (encodeNat (a / d)),
    if (trial (digit b (encodeNat (a % d))) (encodeNat d) false).1
      then digit b (encodeNat (a % d))
      else trim (trial (digit b (encodeNat (a % d))) (encodeNat d) false).2) = _
  rw [digit_encode b (a % d), hq, hr]
  change (digit (!(trial (encodeNat x) (encodeNat d) false).1) (encodeNat (a / d)),
    if (trial (encodeNat x) (encodeNat d) false).1 then encodeNat x
    else trim (trial (encodeNat x) (encodeNat d) false).2) = _
  by_cases h : x < d
  · simp [hborrow.mpr h, digit_encode, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
  · have hb : (trial (encodeNat x) (encodeNat d) false).1 = false :=
      Bool.eq_false_iff.mpr (fun e => h (hborrow.mp e))
    have hd' : d ≤ x := by omega
    have hsmall : x - d < d := by omega
    have hdiv : x / d = 1 := by rw [Nat.div_eq_sub_div hd hd', Nat.div_eq_of_lt hsmall]
    have hmod : x % d = x - d := by rw [Nat.mod_eq_sub_mod hd', Nat.mod_eq_of_lt hsmall]
    simp [hb, hdiff hd', hdiv, hmod, digit_encode, Nat.add_comm]

/-- The state after reading any prefix, stored here least significant bit first. -/
theorem fold_encode (w : List Bool) (d : ℕ) (hd : 0 < d) :
    w.reverse.foldl (divisionStep (encodeNat d)) ([], []) =
      (encodeNat (value w / d), encodeNat (value w % d)) := by
  induction w with
  | nil => simp [value]; rfl
  | cons b w ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    exact divisionStep_encode _ _ hd _

/-- Machine-level output specification including natural division by zero. -/
theorem divide_encode (n d : ℕ) :
    divide (encodeNat n) (encodeNat d) = encodeNat (n / d) := by
  by_cases hd : d = 0
  · subst d
    simp [divide]
    rfl
  · have hne : encodeNat d ≠ [] := by
      intro h
      have hv := value_encodeNat d
      rw [h] at hv
      exact hd hv.symm
    simp [divide, hne, fold_encode _ _ (by omega : 0 < d), value_encodeNat]

private theorem length_encode (n : ℕ) : (encodeNat n).length = n.size :=
  FactorEncoding.length_bitEncode_nat n

private theorem value_lt_pow (w : List Bool) : value w < 2 ^ w.length := by
  induction w with
  | nil => decide
  | cons b w ih =>
    have hb := toNat_le_one b
    simp only [value, List.length_cons, Nat.pow_succ]
    omega

/-- The quotient and remainder each grow by at most one bit in a single
iteration. This bound does not require a canonical incoming state. -/
theorem divisionStep_lengths (den : List Bool) (qr : List Bool × List Bool) (b : Bool) :
    (divisionStep den qr b).1.length ≤ qr.1.length + 1 ∧
    (divisionStep den qr b).2.length ≤ qr.2.length + 1 := by
  constructor
  · exact digit_length _ _
  · dsimp only [divisionStep]
    split
    · exact digit_length _ _
    · exact (trim_length _).trans ((trial_length _ _ _).le.trans (digit_length _ _))

/-- After `w.length` input digits the quotient has at most that many bits.
The remainder is also bounded by the denominator width. -/
theorem prefix_lengths (w : List Bool) (d : ℕ) (hd : 0 < d) :
    let qr := w.reverse.foldl (divisionStep (encodeNat d)) ([], [])
    qr.1.length ≤ w.length ∧ qr.2.length ≤ min w.length (encodeNat d).length := by
  dsimp only
  rw [fold_encode w d hd]
  simp only [length_encode, le_min_iff]
  have hv : (value w).size ≤ w.length := Nat.size_le.mpr (value_lt_pow w)
  exact ⟨(Nat.size_le_size (Nat.div_le_self _ _)).trans hv,
    (Nat.size_le_size (Nat.mod_le _ _)).trans hv, Nat.size_le_size (Nat.mod_lt _ hd).le⟩

/-- The candidate remainder and its raw trial-difference buffer have the
same length. Both use at most one bit beyond the smaller of the divisor width
and the number of digits processed before this step. -/
theorem trial_working_lengths (w : List Bool) (d : ℕ) (hd : 0 < d) (b : Bool) :
    let rem := (w.reverse.foldl (divisionStep (encodeNat d)) ([], [])).2
    let x := digit b rem
    x.length ≤ min w.length (encodeNat d).length + 1 ∧
    (trial x (encodeNat d) false).2.length = x.length := by
  dsimp only
  exact ⟨(digit_length _ _).trans (Nat.succ_le_succ (prefix_lengths w d hd).2),
    trial_length _ _ _⟩

end FactorDivisionBits

/- Finite control for comparing three little-endian words and selecting a guarded query. -/

namespace FactorGuardBits

open FactorDivisionBits Computability

structure Flags where
  first : Bool
  even : Bool
  boundLong : Bool
  rootLong : Bool
  inputLE : Bool
  boundLE : Bool
  deriving DecidableEq, Fintype

def initial : Flags := ⟨true, true, false, false, true, true⟩

def higher (prev a b : Bool) : Bool := if a = b then prev else b

def tick (g : Flags) (a b s : Option Bool) : Flags :=
  ⟨false, if g.first then !(a.getD false) else g.even,
    g.boundLong || (!g.first && b.isSome), g.rootLong || (!g.first && s.isSome),
    higher g.inputLE (a.getD false) (b.getD false), higher g.boundLE (b.getD false) (s.getD false)⟩

private def order (g : Bool) (m n : ℕ) : Bool := if m = n then g else decide (m < n)

private theorem order_digit (g a b : Bool) (x y : ℕ) :
    order (higher g a b) x y = order g (2*x+a.toNat) (2*y+b.toNat) := by
  cases a <;> cases b <;> simp only [higher, Bool.toNat_false, Bool.toNat_true,
    Bool.true_eq_false, Bool.false_eq_true, if_false, if_true, order] <;>
    split <;> split <;> simp_all <;> omega

def summary (g : Flags) (a b s : List Bool) : Flags :=
  let allEmpty := a.isEmpty && b.isEmpty && s.isEmpty
  ⟨g.first && allEmpty, if g.first && !allEmpty then !(a.head?.getD false) else g.even,
    g.boundLong || !(if g.first then b.tail else b).isEmpty,
    g.rootLong || !(if g.first then s.tail else s).isEmpty,
    order g.inputLE (value a) (value b), order g.boundLE (value b) (value s)⟩

theorem summary_nil (g : Flags) : summary g [] [] [] = g := by
  cases g with | mk f e b s i j => cases f <;> simp [summary, value, order]

theorem summary_tick (g : Flags) (a b s : List Bool) (h : ¬ (a=[] ∧ b=[] ∧ s=[])) :
    summary (tick g a.head? b.head? s.head?) a.tail b.tail s.tail = summary g a b s := by
  have hv (w : List Bool) : value w = 2*value w.tail + (w.head?.getD false).toNat := by cases w <;> rfl
  have ho₁ := order_digit g.inputLE (a.head?.getD false) (b.head?.getD false) (value a.tail) (value b.tail)
  have ho₂ := order_digit g.boundLE (b.head?.getD false) (s.head?.getD false) (value b.tail) (value s.tail)
  rw [← hv a, ← hv b] at ho₁
  rw [← hv b, ← hv s] at ho₂
  clear hv
  cases g with | mk f e bl sl i j =>
    cases f <;> cases a <;> cases b <;> cases s <;>
      simp_all [summary, tick, Bool.or_assoc]

inductive Action | reject | accept | useBound | useRoot deriving DecidableEq

def action (g : Flags) : Action :=
  if !g.boundLong then .reject
  else if g.inputLE || g.even then .accept
  else if !g.rootLong then .reject
  else if g.boundLE then .useBound else .useRoot

def prepare (root : ℕ → ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.2 < 2 then (0,0) else if p.1 ≤ p.2 then (0,1) else if 2 ∣ p.1 then (0,1)
  else if 2 ≤ min p.2 (root p.1) then (p.1, min p.2 (root p.1)) else (0,0)

private theorem long_encode (x : ℕ) : (!(encodeNat x).tail.isEmpty) = decide (2 ≤ x) := by
  have hlen : (encodeNat x).length = x.size := FactorEncoding.length_bitEncode_nat x
  have hsize : 1 < x.size ↔ 2 ≤ x := Nat.lt_size
  cases h : encodeNat x with
  | nil => simp [h] at hlen; simp [← hsize, ← hlen]
  | cons b t =>
    cases t <;> simp [h] at * <;> simp_all
    omega

private theorem even_encode (x : ℕ) : (!((encodeNat x).head?.getD false)) = decide (2 ∣ x) := by
  have hval := value_encodeNat x
  cases hx : encodeNat x with
  | nil => rw [hx] at hval; subst x; decide
  | cons b t =>
    rw [hx] at hval
    cases b <;> simp [value] at hval <;> simp <;> omega

theorem action_encode (n b s : ℕ) : action (summary initial (encodeNat n) (encodeNat b) (encodeNat s)) =
    if b < 2 then .reject else if n ≤ b then .accept else if 2 ∣ n then .accept
    else if 2 ≤ s then (if b ≤ s then .useBound else .useRoot) else .reject := by
  have ord (x y : ℕ) : order true x y = decide (x ≤ y) := by
    by_cases h : x=y <;> simp_all [order]
    omega
  have heven : (if !((encodeNat n).isEmpty && (encodeNat b).isEmpty && (encodeNat s).isEmpty)
      then !((encodeNat n).head?.getD false) else true) = decide (2 ∣ n) := by
    rw [← even_encode n]
    split
    · rfl
    · rename_i h
      simp at h
      rw [h.1.1]
      rfl
  simp only [action, summary, initial, Bool.true_and, Bool.false_or, if_true,
    long_encode, value_encodeNat, ord, heven]
  split_ifs <;> simp_all

end FactorGuardBits

/- Run a TM2 statement on selected stacks of a larger machine, leaving the other stacks
unchanged. Halting may transfer control to a specified continuation label. -/

namespace FactorMachineLift

open Turing.TM2

variable {K J Λ Λ' σ σ' : Type} {Γ : K → Type} {Γ' : J → Type}

/-- The stack/symbol embedding and register operations for a machine inside a caller. -/
structure Lift (Γ : K → Type) (Γ' : J → Type) (Λ Λ' σ σ' : Type) where
  stack : K ↪ J
  symbol : ∀ k, Γ k ≃ Γ' (stack k)
  label : Λ → Λ'
  exitLabel : Option Λ'
  read : σ' → σ
  write : σ' → σ → σ'
  read_write : ∀ w v, read (write w v) = v
  write_write : ∀ w v u, write (write w v) u = write w u

namespace Lift

variable (e : Lift Γ Γ' Λ Λ' σ σ')

def mapLabel : Option Λ → Option Λ'
  | none => e.exitLabel
  | some l => some (e.label l)

/-- Translate operations on the callee's stacks, registers and control labels. -/
def stmt : Stmt Γ Λ σ → Stmt Γ' Λ' σ'
  | .push k f q => .push (e.stack k) (fun w => e.symbol k (f (e.read w))) (stmt q)
  | .peek k f q => .peek (e.stack k)
      (fun w a => e.write w (f (e.read w) (a.map (e.symbol k).symm))) (stmt q)
  | .pop k f q => .pop (e.stack k)
      (fun w a => e.write w (f (e.read w) (a.map (e.symbol k).symm))) (stmt q)
  | .load f q => .load (fun w => e.write w (f (e.read w))) (stmt q)
  | .branch f qt qf => .branch (fun w => f (e.read w)) (stmt qt) (stmt qf)
  | .goto f => .goto (fun w => e.label (f (e.read w)))
  | .halt => match e.exitLabel with
    | none => .halt
    | some l => .goto (fun _ => l)

/-- The selected stacks encode the callee's stacks and every other stack retains its
contents from the start of the call. -/
structure StacksMatch (frozen : ∀ j, List (Γ' j))
    (s : ∀ k, List (Γ k)) (t : ∀ j, List (Γ' j)) : Prop where
  inside : ∀ k, t (e.stack k) = (s k).map (e.symbol k)
  outside : ∀ j, (∀ k, e.stack k ≠ j) → t j = frozen j

structure Matches (base : σ') (frozen : ∀ j, List (Γ' j))
    (c : Cfg Γ Λ σ) (C : Cfg Γ' Λ' σ') : Prop where
  label_eq : C.l = e.mapLabel c.l
  state_eq : C.var = e.write base c.var
  stack_eq : e.StacksMatch frozen c.stk C.stk

variable [DecidableEq K] [DecidableEq J]

theorem StacksMatch.update {frozen s t} (h : e.StacksMatch frozen s t)
    (k : K) (xs : List (Γ k)) :
    e.StacksMatch frozen (Function.update s k xs)
      (Function.update t (e.stack k) (xs.map (e.symbol k))) := by
  constructor
  · intro i
    by_cases hi : i = k
    · subst i
      simp
    · have hkey : e.stack i ≠ e.stack k := fun a => hi (e.stack.injective a)
      simpa [Function.update_of_ne hi, Function.update_of_ne hkey] using h.inside i
  · intro j hj
    have hkey : j ≠ e.stack k := (hj k).symm
    simpa [Function.update_of_ne hkey] using h.outside j hj

private theorem decode_head {α β : Type} (h : α ≃ β) (xs : List α) :
    ((xs.map h).head?).map h.symm = xs.head? := by
  cases xs <;> simp

/-- A source statement and its translation take exactly one step, including every nested
stack primitive before the next goto or halt. -/
theorem stepAux_stmt (q : Stmt Γ Λ σ) (base : σ') (frozen : ∀ j, List (Γ' j))
    (v : σ) (s : ∀ k, List (Γ k)) (t : ∀ j, List (Γ' j))
    (h : e.StacksMatch frozen s t) :
    e.Matches base frozen (stepAux q v s) (stepAux (e.stmt q) (e.write base v) t) := by
  induction q generalizing v s t with
  | push k f q ih =>
    simp only [stmt, stepAux, e.read_write, h.inside k]
    exact ih _ _ _ (h.update e k (f v :: s k))
  | peek k f q ih =>
    simp only [stmt, stepAux, e.read_write, e.write_write, h.inside k, decode_head]
    exact ih _ _ _ h
  | pop k f q ih =>
    simp only [stmt, stepAux, e.read_write, e.write_write, h.inside k, decode_head]
    simpa using ih _ _ _ (h.update e k (s k).tail)
  | load f q ih =>
    simp only [stmt, stepAux, e.read_write, e.write_write]
    exact ih _ _ _ h
  | branch f qt qf iht ihf =>
    simp only [stmt, stepAux, e.read_write]
    cases f v
    · exact ihf _ _ _ h
    · exact iht _ _ _ h
  | goto f =>
    exact ⟨by simp [stmt, stepAux, mapLabel, e.read_write], rfl, h⟩
  | halt =>
    cases hx : e.exitLabel with
    | none => exact ⟨by simp [stmt, stepAux, mapLabel, hx], by simp [stmt, stepAux, hx],
                       by simpa [stmt, stepAux, hx] using h⟩
    | some l => exact ⟨by simp [stmt, stepAux, mapLabel, hx], by simp [stmt, stepAux, hx],
                         by simpa [stmt, stepAux, hx] using h⟩

omit [DecidableEq K] [DecidableEq J] in
/-- The callee configuration, caller register base and untouched stacks determine the host. -/
theorem Matches.unique {base frozen c C D}
    (hc : e.Matches base frozen c C) (hd : e.Matches base frozen c D) : C = D := by
  have hl := hc.label_eq.trans hd.label_eq.symm
  have hv := hc.state_eq.trans hd.state_eq.symm
  have hs : C.stk = D.stk := by
    funext j
    by_cases hj : ∃ k, e.stack k = j
    · obtain ⟨k, rfl⟩ := hj
      exact (hc.stack_eq.inside k).trans (hd.stack_eq.inside k).symm
    · have hout : ∀ k, e.stack k ≠ j := fun k hk => hj ⟨k, hk⟩
      exact (hc.stack_eq.outside j hout).trans (hd.stack_eq.outside j hout).symm
  cases C
  cases D
  congr

variable {p : Λ → Stmt Γ Λ σ} {P : Λ' → Stmt Γ' Λ' σ'}

/-- A live transition produces an agreeing host configuration. The rest of the host
program, including the continuation's code, is unrestricted. -/
theorem step_matches (hprog : ∀ l, P (e.label l) = e.stmt (p l))
    {base frozen c d C} (hc : e.Matches base frozen c C) (hs : step p c = some d) :
    ∃ D, step P C = some D ∧ e.Matches base frozen d D := by
  cases c with
  | mk l v s =>
    cases l with
    | none => simp [step] at hs
    | some l =>
      cases C with
      | mk L V S =>
        have hL : L = some (e.label l) := hc.label_eq
        have hV : V = e.write base v := hc.state_eq
        subst L
        subst V
        have hd : stepAux (p l) v s = d := Option.some.inj hs
        subst d
        exact ⟨_, by simp [step, hprog], e.stepAux_stmt _ _ _ _ _ _ hc.stack_eq⟩

/-- Transfer an exact number of live transitions. An embedded halt may be a live
continuation label, so the statement ends on the same step as the callee. -/
theorem iterate_matches (hprog : ∀ l, P (e.label l) = e.stmt (p l))
    (n : ℕ) {base frozen c d C} (hc : e.Matches base frozen c C)
    (hs : (flip bind (step p))^[n] (some c) = some d) :
    ∃ D, (flip bind (step P))^[n] (some C) = some D ∧ e.Matches base frozen d D := by
  induction n generalizing c C with
  | zero =>
    have hd : c = d := Option.some.inj hs
    subst d
    exact ⟨C, rfl, hc⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hs ⊢
    change (flip bind (step p))^[n] (step p c) = some d at hs
    cases hnext : step p c with
    | none =>
      rw [hnext, Function.iterate_fixed (f := flip bind (step p)) (x := none) rfl n] at hs
      cases hs
    | some cnext =>
      obtain ⟨Cnext, hCnext, hmatch⟩ := e.step_matches hprog hc hnext
      obtain ⟨D, hsteps, hD⟩ := ih hmatch (hnext ▸ hs)
      exact ⟨D, by change (flip bind (step P))^[n] (step P C) = some D; rwa [hCnext], hD⟩

/-- Lift a time-bounded execution to named host configurations. Its step count is unchanged. -/
def evalsToInTime (hprog : ∀ l, P (e.label l) = e.stmt (p l))
    {base frozen c d C D budget} (hc : e.Matches base frozen c C)
    (hd : e.Matches base frozen d D)
    (run : StateTransition.EvalsToInTime (step p) c (some d) budget) :
    StateTransition.EvalsToInTime (step P) C (some D) budget where
  steps := run.steps
  steps_le_m := run.steps_le_m
  evals_in_steps := by
    obtain ⟨actual, ha, hactual⟩ := e.iterate_matches hprog run.steps hc run.evals_in_steps
    simpa only [hactual.unique e hd] using ha

end Lift

end FactorMachineLift

/- Compilation of finite-stack programs making calls to a Boolean-valued TM2 machine. -/

namespace FactorOracleMachine

open Turing FactorMachineLift StateTransition

structure OracleProgram where
  K : Type
  [kDec : DecidableEq K]
  [kFin : Fintype K]
  Λ : Type
  [lDec : DecidableEq Λ]
  [lFin : Fintype Λ]
  σ : Type
  [sFin : Fintype σ]
  k₀ : K
  k₁ : K
  arg : K
  main : Λ
  call : Λ
  resume : Λ
  initialState : σ
  m : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

instance (C : OracleProgram) : DecidableEq C.K := C.kDec
instance (C : OracleProgram) : Fintype C.K := C.kFin
instance (C : OracleProgram) : DecidableEq C.Λ := C.lDec
instance (C : OracleProgram) : Fintype C.Λ := C.lFin
instance (C : OracleProgram) : Fintype C.σ := C.sFin

namespace OracleProgram

variable (C : OracleProgram)

abbrev Cfg := TM2.Cfg (fun _ : C.K => Bool) C.Λ C.σ

def tm : FinTM2 where
  K := C.K
  Γ _ := Bool
  Λ := C.Λ
  σ := C.σ
  k₀ := C.k₀
  k₁ := C.k₁
  main := C.main
  initialState := C.initialState
  m := C.m

/-- An atomic call can be used only with a validly encoded argument. -/
inductive Run {A : Type} (encode : A → List Bool) (query : A → Bool) (cost : ℕ → ℕ) :
    C.Cfg → C.Cfg → ℕ → Prop
  | refl (c) : Run encode query cost c c 0
  | normal {c d} (hc : c.l ≠ some C.call) (hs : TM2.step C.m c = some d) : Run encode query cost c d 1
  | oracle (x : A) (v : C.σ) (s : C.K → List Bool) (h : s C.arg = encode x) :
      Run encode query cost ⟨some C.call, v, s⟩
        ⟨some C.resume, v, Function.update s C.arg [query x]⟩
        (cost (encode x).length + 2 * (encode x).length + 4)
  | trans {a b c t u} : Run encode query cost a b t → Run encode query cost b c u →
      Run encode query cost a c (t + u)
  | mono {a b t u} : Run encode query cost a b t → t ≤ u → Run encode query cost a b u

inductive Phase | reverse | transfer | finish deriving DecidableEq
instance : Fintype Phase := ⟨{.reverse, .transfer, .finish}, by intro p; cases p <;> simp⟩

variable (Q : FinTM2) (ei : Q.Γ Q.k₀ ≃ Bool) (eo : Q.Γ Q.k₁ ≃ Bool)

abbrev Index := C.K ⊕ (Q.K ⊕ Unit)
abbrev Label := C.Λ ⊕ (Q.Λ ⊕ Phase)
abbrev Register := C.σ × Q.σ × Option Bool
abbrev Alphabet : C.Index Q → Type := Sum.elim (fun _ => Bool) (Sum.elim Q.Γ (fun _ => Bool))
abbrev HostCfg := TM2.Cfg (C.Alphabet Q) (C.Label Q) (C.Register Q)

def caller : Lift (fun _ : C.K => Bool) (C.Alphabet Q) C.Λ (C.Label Q) C.σ (C.Register Q) where
  stack := ⟨Sum.inl, Sum.inl_injective⟩
  symbol _ := Equiv.refl _
  label := Sum.inl
  exitLabel := none
  read := Prod.fst
  write w v := (v, w.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def callee : Lift Q.Γ (C.Alphabet Q) Q.Λ (C.Label Q) Q.σ (C.Register Q) where
  stack := ⟨fun k => .inr (.inl k), fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩
  symbol _ := Equiv.refl _
  label l := .inr (.inl l)
  exitLabel := some (.inr (.inr .finish))
  read v := v.2.1
  write w v := (w.1, v, w.2.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def program : C.Label Q → TM2.Stmt (C.Alphabet Q) (C.Label Q) (C.Register Q)
  | .inl l => if l = C.call then .goto (fun _ => .inr (.inr .reverse)) else (C.caller Q).stmt (C.m l)
  | .inr (.inl l) => (C.callee Q).stmt (Q.m l)
  | .inr (.inr .reverse) =>
      .pop (.inl C.arg) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inr ())) (fun w => w.2.2.getD false) (.goto fun _ => .inr (.inr .reverse)))
          (.goto fun _ => .inr (.inr .transfer)))
  | .inr (.inr .transfer) =>
      .pop (.inr (.inr ())) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inl Q.k₀)) (fun w => ei.symm (w.2.2.getD false)) (.goto fun _ => .inr (.inr .transfer)))
          (.goto fun _ => .inr (.inl Q.main)))
  | .inr (.inr .finish) =>
      .pop (.inr (.inl Q.k₁)) (fun w o => (w.1, w.2.1, o.map eo))
        (.push (.inl C.arg) (fun w => w.2.2.getD false)
          (.load (fun w => (w.1, w.2.1, none)) (.goto fun _ => .inl C.resume)))

def compiled : FinTM2 :=
  letI := Q.kFin
  letI := Q.ΛFin
  letI := Q.σFin
  { K := C.Index Q
    Γ := C.Alphabet Q
    Λ := C.Label Q
    σ := C.Register Q
    k₀ := .inl C.k₀
    k₁ := .inl C.k₁
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    main := .inl C.main
    initialState := (C.initialState, Q.initialState, none)
    m := C.program Q ei eo }

def tapes (s : C.K → List Bool) (t : ∀ k, List (Q.Γ k)) (b : List Bool) :
    ∀ j, List (C.Alphabet Q j)
  | .inl k => s k
  | .inr (.inl k) => t k
  | .inr (.inr _) => b

def embed (c : C.Cfg) : C.HostCfg Q :=
  ⟨c.l.map Sum.inl, (c.var, Q.initialState, none), C.tapes Q c.stk (fun _ => []) []⟩

private abbrev Stores := ∀ k, List (Q.Γ k)

@[simp] private theorem tapes_c (s t b k) : C.tapes Q s t b (.inl k) = s k := rfl
@[simp] private theorem tapes_q (s t b k) : C.tapes Q s t b (.inr (.inl k)) = t k := rfl
@[simp] private theorem tapes_b (s t b) : C.tapes Q s t b (.inr (.inr ())) = b := rfl

@[simp] private theorem update_c (s t b k) (xs : List Bool) :
    Function.update (C.tapes Q s t b) (.inl k) xs = C.tapes Q (Function.update s k xs) t b := by
  funext j
  rcases j with i | i | u
  · by_cases h : i = k
    · subst i; simp [Function.update, tapes]
    · simp [Function.update, tapes, h]
  · simp [Function.update, tapes]
  · cases u; simp [Function.update, tapes]

@[simp] private theorem update_q (s t b k) (xs : List (Q.Γ k)) :
    Function.update (C.tapes Q s t b) (.inr (.inl k)) xs = C.tapes Q s (Function.update t k xs) b := by
  funext j
  rcases j with i | i | u
  · simp [Function.update, tapes]
  · by_cases h : i = k
    · subst i; simp [Function.update, tapes]
    · simp [Function.update, tapes, h]
  · cases u; simp [Function.update, tapes]

@[simp] private theorem update_b (s t b) (xs : List Bool) :
    Function.update (C.tapes Q s t b) (.inr (.inr ())) xs = C.tapes Q s t xs := by
  funext j
  rcases j with i | i | u
  · simp [Function.update, tapes]
  · simp [Function.update, tapes]
  · cases u; simp [Function.update, tapes]

private def oneStack {K : Type} [DecidableEq K] (Γ : K → Type) (k : K) (xs : List (Γ k)) :
    ∀ j, List (Γ j) := Function.update (fun j => ([] : List (Γ j))) k xs

private def stage (l : C.Label Q) (v : C.σ) (o : Option Bool) (s : C.K → List Bool)
    (t : Stores Q) (b : List Bool) : C.HostCfg Q :=
  ⟨some l, (v, Q.initialState, o), C.tapes Q s t b⟩

private def Exact (a b : C.HostCfg Q) (t : ℕ) : Prop :=
  (flip bind (TM2.step (C.program Q ei eo)))^[t] (some a) = some b

private theorem next {a b d t} (ab : TM2.step (C.program Q ei eo) a = some b)
    (bd : C.Exact Q ei eo b d t) : C.Exact Q ei eo a d (t+1) := by
  unfold Exact at *
  rw [Function.iterate_succ_apply]
  change (flip bind (TM2.step (C.program Q ei eo)))^[t] (TM2.step (C.program Q ei eo) a) = some d
  rwa [ab]

private theorem one {a b} (ab : TM2.step (C.program Q ei eo) a = some b) : C.Exact Q ei eo a b 1 := ab

private theorem join {a b d t u} (ab : C.Exact Q ei eo a b t) (bd : C.Exact Q ei eo b d u) :
    C.Exact Q ei eo a d (u+t) := by
  unfold Exact at *
  rw [Function.iterate_add_apply, ab, bd]

private theorem reverse_run (v : C.σ) (s : C.K → List Bool) (xs bs : List Bool) (o : Option Bool) :
    C.Exact Q ei eo
      (C.stage Q (.inr (.inr .reverse)) v o (Function.update s C.arg xs) (fun _ => []) bs)
      (C.stage Q (.inr (.inr .transfer)) v none (Function.update s C.arg []) (fun _ => []) (xs.reverse ++ bs))
      (xs.length+1) := by
  induction xs generalizing bs o with
  | nil => apply C.one; simp [stage, program, TM2.stepAux]
  | cons a xs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      (C.next Q ei eo (a := C.stage Q (.inr (.inr .reverse)) v o (Function.update s C.arg (a::xs)) (fun _ => []) bs)
        (by simp [stage, program, TM2.stepAux]) (ih (a::bs) (some a)))

private theorem transfer_run (v : C.σ) (s : C.K → List Bool) (bs : List Bool)
    (xs : List (Q.Γ Q.k₀)) (o : Option Bool) :
    C.Exact Q ei eo
      (C.stage Q (.inr (.inr .transfer)) v o s (oneStack Q.Γ Q.k₀ xs) bs)
      (C.stage Q (.inr (.inl Q.main)) v none s (oneStack Q.Γ Q.k₀ (bs.reverse.map ei.symm ++ xs)) [])
      (bs.length+1) := by
  induction bs generalizing xs o with
  | nil => apply C.one; simp [stage, program, TM2.stepAux]
  | cons a bs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using
      (C.next Q ei eo (a := C.stage Q (.inr (.inr .transfer)) v o s (oneStack Q.Γ Q.k₀ xs) (a::bs))
        (by simp [stage, program, TM2.stepAux, oneStack]) (ih (ei.symm a::xs) (some a)))

private theorem caller_match (c : C.Cfg) : (C.caller Q).Matches
    (C.initialState, Q.initialState, none) (fun _ => []) c (C.embed Q c) := by
  refine ⟨?_, rfl, ⟨?_, ?_⟩⟩
  · change c.l.map Sum.inl = (C.caller Q).mapLabel c.l
    cases c.l <;> rfl
  · intro k
    change c.stk k = (c.stk k).map id
    simp
  · rintro (k | k | u) h
    · exact False.elim (h k rfl)
    · rfl
    · cases u; rfl

private theorem ordinary_run {c d : C.Cfg} (hc : c.l ≠ some C.call) (hs : TM2.step C.m c = some d) :
    C.Exact Q ei eo (C.embed Q c) (C.embed Q d) 1 := by
  rcases c with ⟨_ | l, v, s⟩
  · contradiction
  · have hl : l ≠ C.call := fun h => hc (congrArg some h)
    have hd : TM2.stepAux (C.m l) v s = d := Option.some.inj hs
    subst d
    have hmatch := (C.caller Q).stepAux_stmt (C.m l) (C.initialState, Q.initialState, none)
      (fun _ => []) v s (C.tapes Q s (fun _ => []) []) (C.caller_match Q ⟨some l, v, s⟩).stack_eq
    apply C.one
    change some (TM2.stepAux (C.program Q ei eo (.inl l)) _ _) = _
    rw [show C.program Q ei eo (.inl l) = (C.caller Q).stmt (C.m l) by simp [program, hl]]
    exact congrArg some (hmatch.unique _ (C.caller_match Q _))

private def embedQuery (v : C.σ) (s : C.K → List Bool) (d : Q.Cfg) : C.HostCfg Q :=
  ⟨(C.callee Q).mapLabel d.l, (v, d.var, none), C.tapes Q s d.stk []⟩

private theorem callee_match (v : C.σ) (s : C.K → List Bool) (d : Q.Cfg) :
    (C.callee Q).Matches (v, Q.initialState, none) (C.tapes Q s (fun _ => []) []) d (C.embedQuery Q v s d) := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩⟩
  · intro k
    change d.stk k = (d.stk k).map id
    simp
  · rintro (k | k | u) h
    · rfl
    · exact False.elim (h k rfl)
    · cases u; rfl

private theorem init_tapes (T : FinTM2) (xs : List (T.Γ T.k₀)) :
    (initList T xs).stk = oneStack T.Γ T.k₀ xs := by
  funext j
  by_cases h : j = T.k₀
  · subst j; simp [initList, oneStack, Function.update]
  · simp [initList, oneStack, Function.update, h]

private theorem halt_tapes (T : FinTM2) (xs : List (T.Γ T.k₁)) :
    (haltList T xs).stk = oneStack T.Γ T.k₁ xs := by
  funext j
  by_cases h : j = T.k₁
  · subst j; simp [haltList, oneStack, Function.update]
  · simp [haltList, oneStack, Function.update, h]

private theorem nil_stack {K : Type} [DecidableEq K] (Γ : K → Type) (k : K) :
    oneStack Γ k [] = (fun _ => []) := by
  funext j
  by_cases h : j = k
  · subst j; simp [oneStack]
  · simp [oneStack, h]

private theorem start_call (v : C.σ) (s : C.K → List Bool) (w : List Bool) (harg : s C.arg = w) :
    C.Exact Q ei eo (C.embed Q ⟨some C.call, v, s⟩)
      (C.embedQuery Q v (Function.update s C.arg []) (initList Q (w.map ei.symm))) (2 * w.length + 3) := by
  have hrev := C.reverse_run Q ei eo v s w [] none
  have htrans := C.transfer_run Q ei eo v (Function.update s C.arg []) w.reverse [] none
  have hstart : Function.update s C.arg w = s := by rw [← harg]; exact Function.update_eq_self _ _
  rw [hstart, List.append_nil] at hrev
  rw [List.reverse_reverse, List.append_nil, nil_stack, List.length_reverse] at htrans
  have henter := C.one Q ei eo (a := C.embed Q ⟨some C.call, v, s⟩)
    (b := C.stage Q (.inr (.inr .reverse)) v none s (fun _ => []) []) (by simp [embed, stage, program, TM2.stepAux])
  have hs := C.join Q ei eo (C.join Q ei eo henter hrev) htrans
  convert hs using 1
  · unfold embedQuery stage
    rw [init_tapes]
    rfl
  · omega

private theorem finish_call (v : C.σ) (s : C.K → List Bool) (r : Bool) :
    C.Exact Q ei eo
      (C.embedQuery Q v (Function.update s C.arg []) (haltList Q [eo.symm r]))
      (C.embed Q ⟨some C.resume, v, Function.update s C.arg [r]⟩) 1 := by
  apply C.one
  unfold embedQuery embed
  rw [halt_tapes]
  change some (TM2.stepAux (C.program Q ei eo (.inr (.inr .finish)))
    (v, Q.initialState, none)
    (C.tapes Q (Function.update s C.arg []) (oneStack Q.Γ Q.k₁ [eo.symm r]) [])) = _
  simp [program, TM2.stepAux, oneStack]

private theorem call_run (v : C.σ) (s : C.K → List Bool) (w : List Bool) (r : Bool) (t : ℕ)
    (harg : s C.arg = w) (oracleRun : TM2OutputsInTime Q (w.map ei.symm) (some [eo.symm r]) t) :
    ∃ k ≤ t + 2*w.length + 4, C.Exact Q ei eo (C.embed Q ⟨some C.call, v, s⟩)
      (C.embed Q ⟨some C.resume, v, Function.update s C.arg [r]⟩) k := by
  let cleared := Function.update s C.arg []
  let middle := (C.callee Q).evalsToInTime (p := Q.m) (P := C.program Q ei eo) (fun _ => rfl)
    (C.callee_match Q v cleared (initList Q (w.map ei.symm)))
    (C.callee_match Q v cleared (haltList Q [eo.symm r])) oracleRun
  have hmiddle : C.Exact Q ei eo (C.embedQuery Q v cleared (initList Q (w.map ei.symm)))
      (C.embedQuery Q v cleared (haltList Q [eo.symm r])) middle.steps := middle.evals_in_steps
  have h := C.join Q ei eo (C.join Q ei eo (C.start_call Q ei eo v s w harg) hmiddle) (C.finish_call Q ei eo v s r)
  exact ⟨_, by have := middle.steps_le_m; omega, h⟩

private theorem simulate {A : Type} {encode : A → List Bool} {query : A → Bool} {cost : ℕ → ℕ}
    (oracleRun : ∀ x, TM2OutputsInTime Q ((encode x).map ei.symm) (some [eo.symm (query x)]) (cost (encode x).length))
    {a b : C.Cfg} {t : ℕ} (run : C.Run encode query cost a b t) :
    ∃ k ≤ t, C.Exact Q ei eo (C.embed Q a) (C.embed Q b) k := by
  induction run with
  | refl a => exact ⟨0, Nat.le_refl _, rfl⟩
  | normal hc hs => exact ⟨1, Nat.le_refl _, C.ordinary_run Q ei eo hc hs⟩
  | oracle x v s h => exact C.call_run Q ei eo v s _ _ _ h (oracleRun x)
  | trans _ _ ih ih' =>
    obtain ⟨k, hk, h⟩ := ih
    obtain ⟨j, hj, h'⟩ := ih'
    exact ⟨j+k, by omega, C.join Q ei eo h h'⟩
  | mono _ hle ih =>
    obtain ⟨k, hk, h⟩ := ih
    exact ⟨k, hk.trans hle, h⟩

private theorem singleCaller (k : C.K) (xs : List Bool) :
    C.tapes Q (oneStack (fun _ : C.K => Bool) k xs) (fun _ => []) [] =
      oneStack (C.Alphabet Q) (.inl k) xs := by
  have empty : C.tapes Q (fun _ => []) (fun _ => []) [] = (fun _ => []) := by
    funext j
    rcases j with i | i | u <;> rfl
  unfold oneStack
  rw [← update_c, empty]

private theorem embed_init (xs : List Bool) : C.embed Q (initList C.tm xs) =
    initList (C.compiled Q ei eo) xs := by
  apply congrArg (fun s => (⟨some (.inl C.main), (C.initialState, Q.initialState, none), s⟩ : C.HostCfg Q))
  change C.tapes Q (initList C.tm xs).stk (fun _ => []) [] = (initList (C.compiled Q ei eo) xs).stk
  exact (congrArg (fun s => C.tapes Q s (fun _ => []) []) (init_tapes C.tm xs)).trans
    ((C.singleCaller Q C.k₀ xs).trans (init_tapes (C.compiled Q ei eo) xs).symm)

private theorem embed_halt (xs : List Bool) : C.embed Q (haltList C.tm xs) =
    haltList (C.compiled Q ei eo) xs := by
  apply congrArg (fun s => (⟨none, (C.initialState, Q.initialState, none), s⟩ : C.HostCfg Q))
  change C.tapes Q (haltList C.tm xs).stk (fun _ => []) [] = (haltList (C.compiled Q ei eo) xs).stk
  exact (congrArg (fun s => C.tapes Q s (fun _ => []) []) (halt_tapes C.tm xs)).trans
    ((C.singleCaller Q C.k₁ xs).trans (halt_tapes (C.compiled Q ei eo) xs).symm)

/-- Any valid time-budgeted oracle program executes on a standard finite TM2 machine.
The caller's workspace survives every call and all callee workspace is cleared before resuming. -/
theorem compile_run {A : Type} {encode : A → List Bool} {query : A → Bool} {cost : ℕ → ℕ}
    (oracleRun : ∀ x, TM2OutputsInTime Q ((encode x).map ei.symm) (some [eo.symm (query x)]) (cost (encode x).length))
    {input output : List Bool} {t : ℕ}
    (run : C.Run encode query cost (initList C.tm input) (haltList C.tm output) t) :
    Nonempty (TM2OutputsInTime (C.compiled Q ei eo) input (some output) t) := by
  obtain ⟨k, hk, h⟩ := C.simulate Q ei eo oracleRun run
  unfold Exact at h
  rw [embed_init C Q ei eo, embed_halt C Q ei eo] at h
  exact ⟨⟨⟨k, h⟩, hk⟩⟩

end OracleProgram
end FactorOracleMachine

/- Output and stack growth bounds for the finite multitape machine used by `IsPolyTime`. -/

namespace FactorMachineBound

open Turing ComplexityTheory BitstringEncoding

private def pushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q | .pop _ _ q | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ | .halt => 0

private theorem stepAux_bound {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (j : K) :
    ((TM2.stepAux q v S).stk j).length ≤ (S j).length + pushes q := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [TM2.stepAux, pushes]
    have h := ih v (Function.update S k (f v :: S k))
    by_cases heq : j = k
    · subst j
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    · simp [Function.update_of_ne heq] at h
      omega
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [TM2.stepAux, pushes]
    have h := ih (f v (S k).head?) (Function.update S k (S k).tail)
    by_cases heq : j = k
    · subst j
      simpa only [Function.update_self] using h.trans
        (Nat.add_le_add_right (by simp) (pushes q))
    · simpa [Function.update_of_ne heq] using h
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    cases he : f v <;> simp only [TM2.stepAux, he, cond_true, cond_false, pushes]
    · exact (ihr v S).trans (Nat.add_le_add_left (le_max_right _ _) _)
    · exact (ihq v S).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

private def growth (M : FinTM2) : ℕ :=
  letI := M.ΛFin
  Finset.univ.sup fun l => pushes (M.m l)

private theorem step_bound (M : FinTM2) (x y : M.Cfg) (j : M.K) (h : M.step x = some y) :
    (y.stk j).length ≤ (x.stk j).length + growth M := by
  let _ := M.ΛFin
  rcases x with ⟨_ | l, v, S⟩
  · contradiction
  · change some (TM2.stepAux (M.m l) v S) = some y at h
    cases h
    exact (stepAux_bound (M.m l) v S j).trans
      (Nat.add_le_add_left (Finset.le_sup (f := fun l => pushes (M.m l)) (Finset.mem_univ l)) _)

private def stackLength (M : FinTM2) (j : M.K) : Option M.Cfg → ℕ
  | none => 0
  | some c => (c.stk j).length

private theorem iterate_bound (M : FinTM2) (j : M.K) (x : Option M.Cfg) (t : ℕ) :
    stackLength M j ((flip bind M.step)^[t] x) ≤ stackLength M j x + t * growth M := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply, Nat.succ_mul]
    have hs : stackLength M j ((flip bind M.step) x) ≤ stackLength M j x + growth M := by
      cases x with
      | none => exact Nat.zero_le _
      | some c =>
        change stackLength M j (M.step c) ≤ _
        cases he : M.step c with
        | none => exact Nat.zero_le _
        | some c' => exact step_bound M c c' j he
    have h := ih ((flip bind M.step) x)
    omega

/-- A machine can grow any designated output by only a constant number of cells per step. -/
theorem output_length_le (M : FinTM2) : ∃ c : ℕ,
    ∀ (input : List (M.Γ M.k₀)) (output : List (M.Γ M.k₁)) (t : ℕ),
      TM2OutputsInTime M input (some output) t → output.length ≤ input.length + t * c := by
  refine ⟨growth M, ?_⟩
  intro input output t h
  have hbound := iterate_bound M M.k₁ (some (initList M input)) h.steps
  rw [h.evals_in_steps] at hbound
  have hin (k : M.K) : ((initList M input).stk k).length ≤ input.length := by
    by_cases he : k = M.k₀
    · subst k
      simp [initList]
    · simp [initList, he]
  change ((haltList M output).stk M.k₁).length ≤ _ at hbound
  simpa [haltList] using hbound.trans (Nat.add_le_add (hin M.k₁) (Nat.mul_le_mul_right _ h.steps_le_m))

/-- A polynomial-time computation has polynomially bounded encoded outputs. -/
theorem polytime_output_bound {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} (hf : IsPolyTime f) : ∃ p : Polynomial ℕ,
    ∀ a, (bitEncode (f a)).length ≤ p.eval (bitEncode a).length := by
  obtain ⟨D⟩ := hf
  obtain ⟨c, hc⟩ := output_length_le D.tm
  refine ⟨Polynomial.X + D.time * Polynomial.C c, ?_⟩
  intro a
  have h := hc _ _ _ (D.outputsFun a)
  simpa [bitEncode] using h

end FactorMachineBound

/- Clocked finite-stack callers with word-valued subroutines on canonical bitstring encodings.
A call moves the input and result through a temporary stack to preserve their bit order. -/

namespace FactorWordOracle

open FactorOracleMachine Turing FactorMachineLift StateTransition

variable (C : OracleProgram)

/-- An atomic call can be used only with a validly encoded argument. -/
inductive Run {A B : Type} (encode : A → List Bool) (encodeOut : B → List Bool) (query : A → B) (cost : ℕ → ℕ) :
    C.Cfg → C.Cfg → ℕ → Prop
  | refl (c) : Run encode encodeOut query cost c c 0
  | normal {c d} (hc : c.l ≠ some C.call) (hs : TM2.step C.m c = some d) : Run encode encodeOut query cost c d 1
  | oracle (x : A) (v : C.σ) (s : C.K → List Bool) (h : s C.arg = encode x) :
      Run encode encodeOut query cost ⟨some C.call, v, s⟩
        ⟨some C.resume, v, Function.update s C.arg (encodeOut (query x))⟩
        (cost (encode x).length)
  | trans {a b c t u} : Run encode encodeOut query cost a b t → Run encode encodeOut query cost b c u →
      Run encode encodeOut query cost a c (t + u)
  | mono {a b t u} : Run encode encodeOut query cost a b t → t ≤ u → Run encode encodeOut query cost a b u

inductive Phase | reverse | transfer | collect | deliver deriving DecidableEq
instance : Fintype Phase := ⟨{.reverse, .transfer, .collect, .deliver}, by intro p; cases p <;> simp⟩

variable (Q : FinTM2) (ei : Q.Γ Q.k₀ ≃ Bool) (eo : Q.Γ Q.k₁ ≃ Bool)

abbrev Label := C.Λ ⊕ (Q.Λ ⊕ Phase)
abbrev HostCfg := TM2.Cfg (C.Alphabet Q) (Label C Q) (C.Register Q)

def caller : Lift (fun _ : C.K => Bool) (C.Alphabet Q) C.Λ (Label C Q) C.σ (C.Register Q) where
  stack := ⟨Sum.inl, Sum.inl_injective⟩
  symbol _ := Equiv.refl _
  label := Sum.inl
  exitLabel := none
  read := Prod.fst
  write w v := (v, w.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def callee : Lift Q.Γ (C.Alphabet Q) Q.Λ (Label C Q) Q.σ (C.Register Q) where
  stack := ⟨fun k => .inr (.inl k), fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩
  symbol _ := Equiv.refl _
  label l := .inr (.inl l)
  exitLabel := some (.inr (.inr .collect))
  read v := v.2.1
  write w v := (w.1, v, w.2.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def program : Label C Q → TM2.Stmt (C.Alphabet Q) (Label C Q) (C.Register Q)
  | .inl l => if l = C.call then .goto (fun _ => .inr (.inr .reverse)) else (caller C Q).stmt (C.m l)
  | .inr (.inl l) => (callee C Q).stmt (Q.m l)
  | .inr (.inr .reverse) =>
      .pop (.inl C.arg) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inr ())) (fun w => w.2.2.getD false) (.goto fun _ => .inr (.inr .reverse)))
          (.goto fun _ => .inr (.inr .transfer)))
  | .inr (.inr .transfer) =>
      .pop (.inr (.inr ())) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inl Q.k₀)) (fun w => ei.symm (w.2.2.getD false)) (.goto fun _ => .inr (.inr .transfer)))
          (.goto fun _ => .inr (.inl Q.main)))
  | .inr (.inr .collect) =>
      .pop (.inr (.inl Q.k₁)) (fun w o => (w.1, w.2.1, o.map eo))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inr (.inr ())) (fun w => w.2.2.getD false) (.goto fun _ => .inr (.inr .collect)))
          (.goto fun _ => .inr (.inr .deliver)))
  | .inr (.inr .deliver) =>
      .pop (.inr (.inr ())) (fun w o => (w.1, w.2.1, o))
        (.branch (fun w => w.2.2.isSome)
          (.push (.inl C.arg) (fun w => w.2.2.getD false) (.goto fun _ => .inr (.inr .deliver)))
          (.goto fun _ => .inl C.resume))

def compiled : FinTM2 :=
  letI := Q.kFin
  letI := Q.ΛFin
  letI := Q.σFin
  { K := C.Index Q
    Γ := C.Alphabet Q
    Λ := Label C Q
    σ := C.Register Q
    k₀ := .inl C.k₀
    k₁ := .inl C.k₁
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    main := .inl C.main
    initialState := (C.initialState, Q.initialState, none)
    m := program C Q ei eo }

def embed (c : C.Cfg) : HostCfg C Q :=
  ⟨c.l.map Sum.inl, (c.var, Q.initialState, none), C.tapes Q c.stk (fun _ => []) []⟩

private abbrev Stores := ∀ k, List (Q.Γ k)

private def oneStack {K : Type} [DecidableEq K] (Γ : K → Type) (k : K) (xs : List (Γ k)) :
    ∀ j, List (Γ j) := Function.update (fun j => ([] : List (Γ j))) k xs

private def stage (l : Label C Q) (v : C.σ) (o : Option Bool) (s : C.K → List Bool)
    (t : Stores Q) (b : List Bool) : HostCfg C Q :=
  ⟨some l, (v, Q.initialState, o), C.tapes Q s t b⟩

private def Exact (a b : HostCfg C Q) (t : ℕ) : Prop :=
  (flip bind (TM2.step (program C Q ei eo)))^[t] (some a) = some b

private theorem next {a b d t} (ab : TM2.step (program C Q ei eo) a = some b)
    (bd : Exact C Q ei eo b d t) : Exact C Q ei eo a d (t+1) := by
  unfold Exact at *
  rw [Function.iterate_succ_apply]
  change (flip bind (TM2.step (program C Q ei eo)))^[t] (TM2.step (program C Q ei eo) a) = some d
  rwa [ab]

private theorem one {a b} (ab : TM2.step (program C Q ei eo) a = some b) : Exact C Q ei eo a b 1 := ab

private theorem join {a b d t u} (ab : Exact C Q ei eo a b t) (bd : Exact C Q ei eo b d u) :
    Exact C Q ei eo a d (u+t) := by
  unfold Exact at *
  rw [Function.iterate_add_apply, ab, bd]

private theorem reverse_run (v : C.σ) (s : C.K → List Bool) (xs bs : List Bool) (o : Option Bool) :
    Exact C Q ei eo
      (stage C Q (.inr (.inr .reverse)) v o (Function.update s C.arg xs) (fun _ => []) bs)
      (stage C Q (.inr (.inr .transfer)) v none (Function.update s C.arg []) (fun _ => []) (xs.reverse ++ bs))
      (xs.length+1) := by
  induction xs generalizing bs o with
  | nil => apply one C; simp [stage, program, TM2.stepAux]
  | cons a xs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      (next C Q ei eo (a := stage C Q (.inr (.inr .reverse)) v o (Function.update s C.arg (a::xs)) (fun _ => []) bs)
        (by simp [stage, program, TM2.stepAux]) (ih (a::bs) (some a)))

private theorem transfer_run (v : C.σ) (s : C.K → List Bool) (bs : List Bool)
    (xs : List (Q.Γ Q.k₀)) (o : Option Bool) :
    Exact C Q ei eo
      (stage C Q (.inr (.inr .transfer)) v o s (oneStack Q.Γ Q.k₀ xs) bs)
      (stage C Q (.inr (.inl Q.main)) v none s (oneStack Q.Γ Q.k₀ (bs.reverse.map ei.symm ++ xs)) [])
      (bs.length+1) := by
  induction bs generalizing xs o with
  | nil => apply one C; simp [stage, program, TM2.stepAux]
  | cons a bs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using
      (next C Q ei eo (a := stage C Q (.inr (.inr .transfer)) v o s (oneStack Q.Γ Q.k₀ xs) (a::bs))
        (by simp [stage, program, TM2.stepAux, oneStack]) (ih (ei.symm a::xs) (some a)))

private theorem caller_match (c : C.Cfg) : (caller C Q).Matches
    (C.initialState, Q.initialState, none) (fun _ => []) c (embed C Q c) := by
  refine ⟨?_, rfl, ⟨?_, ?_⟩⟩
  · change c.l.map Sum.inl = (caller C Q).mapLabel c.l
    cases c.l <;> rfl
  · intro k
    change c.stk k = (c.stk k).map id
    simp
  · rintro (k | k | u) h
    · exact False.elim (h k rfl)
    · rfl
    · cases u; rfl

private theorem ordinary_run {c d : C.Cfg} (hc : c.l ≠ some C.call) (hs : TM2.step C.m c = some d) :
    Exact C Q ei eo (embed C Q c) (embed C Q d) 1 := by
  rcases c with ⟨_ | l, v, s⟩
  · contradiction
  · have hl : l ≠ C.call := fun h => hc (congrArg some h)
    have hd : TM2.stepAux (C.m l) v s = d := Option.some.inj hs
    subst d
    have hmatch := (caller C Q).stepAux_stmt (C.m l) (C.initialState, Q.initialState, none)
      (fun _ => []) v s (C.tapes Q s (fun _ => []) []) (caller_match C Q ⟨some l, v, s⟩).stack_eq
    apply one C
    change some (TM2.stepAux (program C Q ei eo (.inl l)) _ _) = _
    rw [show program C Q ei eo (.inl l) = (caller C Q).stmt (C.m l) by simp [program, hl]]
    exact congrArg some (hmatch.unique _ (caller_match C Q _))

private def embedQuery (v : C.σ) (s : C.K → List Bool) (d : Q.Cfg) : HostCfg C Q :=
  ⟨(callee C Q).mapLabel d.l, (v, d.var, none), C.tapes Q s d.stk []⟩

private theorem callee_match (v : C.σ) (s : C.K → List Bool) (d : Q.Cfg) :
    (callee C Q).Matches (v, Q.initialState, none) (C.tapes Q s (fun _ => []) []) d (embedQuery C Q v s d) := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩⟩
  · intro k
    change d.stk k = (d.stk k).map id
    simp
  · rintro (k | k | u) h
    · rfl
    · exact False.elim (h k rfl)
    · cases u; rfl

private theorem init_tapes (T : FinTM2) (xs : List (T.Γ T.k₀)) :
    (initList T xs).stk = oneStack T.Γ T.k₀ xs := by
  funext j
  by_cases h : j = T.k₀
  · subst j; simp [initList, oneStack, Function.update]
  · simp [initList, oneStack, Function.update, h]

private theorem halt_tapes (T : FinTM2) (xs : List (T.Γ T.k₁)) :
    (haltList T xs).stk = oneStack T.Γ T.k₁ xs := by
  funext j
  by_cases h : j = T.k₁
  · subst j; simp [haltList, oneStack, Function.update]
  · simp [haltList, oneStack, Function.update, h]

private theorem nil_stack {K : Type} [DecidableEq K] (Γ : K → Type) (k : K) :
    oneStack Γ k [] = (fun _ => []) := by
  funext j
  by_cases h : j = k
  · subst j; simp [oneStack]
  · simp [oneStack, h]

private theorem start_call (v : C.σ) (s : C.K → List Bool) (w : List Bool) (harg : s C.arg = w) :
    Exact C Q ei eo (embed C Q ⟨some C.call, v, s⟩)
      (embedQuery C Q v (Function.update s C.arg []) (initList Q (w.map ei.symm))) (2 * w.length + 3) := by
  have hrev := reverse_run C Q ei eo v s w [] none
  have htrans := transfer_run C Q ei eo v (Function.update s C.arg []) w.reverse [] none
  have hstart : Function.update s C.arg w = s := by rw [← harg]; exact Function.update_eq_self _ _
  rw [hstart, List.append_nil] at hrev
  rw [List.reverse_reverse, List.append_nil, nil_stack, List.length_reverse] at htrans
  have henter := one C Q ei eo (a := embed C Q ⟨some C.call, v, s⟩)
    (b := stage C Q (.inr (.inr .reverse)) v none s (fun _ => []) []) (by simp [embed, stage, program, TM2.stepAux])
  have hs := join C Q ei eo (join C Q ei eo henter hrev) htrans
  convert hs using 1
  · unfold embedQuery stage
    rw [init_tapes]
    rfl
  · omega

private theorem collect_run (v : C.σ) (s : C.K → List Bool) (xs bs : List Bool) (o : Option Bool) :
    Exact C Q ei eo
      (stage C Q (.inr (.inr .collect)) v o s (oneStack Q.Γ Q.k₁ (xs.map eo.symm)) bs)
      (stage C Q (.inr (.inr .deliver)) v none s (oneStack Q.Γ Q.k₁ []) (xs.reverse ++ bs))
      (xs.length + 1) := by
  induction xs generalizing bs o with
  | nil => apply one C; simp [stage, program, TM2.stepAux, oneStack]
  | cons a xs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      (next C Q ei eo (a := stage C Q (.inr (.inr .collect)) v o s (oneStack Q.Γ Q.k₁ ((a::xs).map eo.symm)) bs)
        (by simp [stage, program, TM2.stepAux, oneStack]) (ih (a::bs) (some a)))

private theorem deliver_run (v : C.σ) (s : C.K → List Bool) (bs xs : List Bool) (o : Option Bool) :
    Exact C Q ei eo
      (stage C Q (.inr (.inr .deliver)) v o (Function.update s C.arg xs) (fun _ => []) bs)
      (embed C Q ⟨some C.resume, v, Function.update s C.arg (bs.reverse ++ xs)⟩)
      (bs.length + 1) := by
  induction bs generalizing xs o with
  | nil => apply one C; simp [stage, program, TM2.stepAux, embed]
  | cons a bs ih =>
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      (next C Q ei eo (a := stage C Q (.inr (.inr .deliver)) v o (Function.update s C.arg xs) (fun _ => []) (a::bs))
        (by simp [stage, program, TM2.stepAux]) (ih (a::xs) (some a)))

private theorem finish_call (v : C.σ) (s : C.K → List Bool) (r : List Bool) :
    Exact C Q ei eo
      (embedQuery C Q v (Function.update s C.arg []) (haltList Q (r.map eo.symm)))
      (embed C Q ⟨some C.resume, v, Function.update s C.arg r⟩) (2*r.length + 2) := by
  have hcollect := collect_run C Q ei eo v (Function.update s C.arg []) r [] none
  have hdeliver := deliver_run C Q ei eo v s r.reverse [] none
  rw [List.append_nil, nil_stack] at hcollect
  rw [List.reverse_reverse, List.append_nil, List.length_reverse] at hdeliver
  have h := join C Q ei eo hcollect hdeliver
  convert h using 1
  · unfold embedQuery stage
    rw [halt_tapes]
    rfl
  · omega

private theorem call_run (v : C.σ) (s : C.K → List Bool) (w : List Bool) (r : List Bool) (t : ℕ)
    (harg : s C.arg = w) (oracleRun : TM2OutputsInTime Q (w.map ei.symm) (some (r.map eo.symm)) t) :
    ∃ k ≤ t + 2*w.length + 2*r.length + 5, Exact C Q ei eo (embed C Q ⟨some C.call, v, s⟩)
      (embed C Q ⟨some C.resume, v, Function.update s C.arg r⟩) k := by
  let cleared := Function.update s C.arg []
  let middle := (callee C Q).evalsToInTime (p := Q.m) (P := program C Q ei eo) (fun _ => rfl)
    (callee_match C Q v cleared (initList Q (w.map ei.symm)))
    (callee_match C Q v cleared (haltList Q (r.map eo.symm))) oracleRun
  have hmiddle : Exact C Q ei eo (embedQuery C Q v cleared (initList Q (w.map ei.symm)))
      (embedQuery C Q v cleared (haltList Q (r.map eo.symm))) middle.steps := middle.evals_in_steps
  have h := join C Q ei eo (join C Q ei eo (start_call C Q ei eo v s w harg) hmiddle) (finish_call C Q ei eo v s r)
  exact ⟨_, by have := middle.steps_le_m; omega, h⟩

private theorem simulate {A B : Type} {encode : A → List Bool} {encodeOut : B → List Bool} {query : A → B} {cost time : ℕ → ℕ}
    (oracleRun : ∀ x, TM2OutputsInTime Q ((encode x).map ei.symm) (some ((encodeOut (query x)).map eo.symm)) (time (encode x).length))
    (hcost : ∀ x, time (encode x).length + 2 * (encode x).length + 2 * (encodeOut (query x)).length + 5 ≤ cost (encode x).length)
    {a b : C.Cfg} {t : ℕ} (run : Run C encode encodeOut query cost a b t) :
    ∃ k ≤ t, Exact C Q ei eo (embed C Q a) (embed C Q b) k := by
  induction run with
  | refl a => exact ⟨0, Nat.le_refl _, rfl⟩
  | normal hc hs => exact ⟨1, Nat.le_refl _, ordinary_run C Q ei eo hc hs⟩
  | oracle x v s h =>
    obtain ⟨k, hk, steps⟩ := call_run C Q ei eo v s _ _ _ h (oracleRun x)
    exact ⟨k, hk.trans (hcost x), steps⟩
  | trans _ _ ih ih' =>
    obtain ⟨k, hk, h⟩ := ih
    obtain ⟨j, hj, h'⟩ := ih'
    exact ⟨j+k, by omega, join C Q ei eo h h'⟩
  | mono _ hle ih =>
    obtain ⟨k, hk, h⟩ := ih
    exact ⟨k, hk.trans hle, h⟩

private theorem singleCaller (k : C.K) (xs : List Bool) :
    C.tapes Q (oneStack (fun _ : C.K => Bool) k xs) (fun _ => []) [] =
      oneStack (C.Alphabet Q) (.inl k) xs := by
  have empty : C.tapes Q (fun _ => []) (fun _ => []) [] = (fun _ => []) := by
    funext j
    rcases j with i | i | u <;> rfl
  unfold oneStack
  have hu := show Function.update (C.tapes Q (fun _ => []) (fun _ => []) []) (.inl k) xs =
      C.tapes Q (Function.update (fun _ => []) k xs) (fun _ => []) [] by simp
  simpa only [empty] using hu.symm

private theorem embed_init (xs : List Bool) : embed C Q (initList C.tm xs) =
    initList (compiled C Q ei eo) xs := by
  apply congrArg (fun s => (⟨some (.inl C.main), (C.initialState, Q.initialState, none), s⟩ : HostCfg C Q))
  change C.tapes Q (initList C.tm xs).stk (fun _ => []) [] = (initList (compiled C Q ei eo) xs).stk
  exact (congrArg (fun s => C.tapes Q s (fun _ => []) []) (init_tapes C.tm xs)).trans
    ((singleCaller C Q C.k₀ xs).trans (init_tapes (compiled C Q ei eo) xs).symm)

private theorem embed_halt (xs : List Bool) : embed C Q (haltList C.tm xs) =
    haltList (compiled C Q ei eo) xs := by
  apply congrArg (fun s => (⟨none, (C.initialState, Q.initialState, none), s⟩ : HostCfg C Q))
  change C.tapes Q (haltList C.tm xs).stk (fun _ => []) [] = (haltList (compiled C Q ei eo) xs).stk
  exact (congrArg (fun s => C.tapes Q s (fun _ => []) []) (halt_tapes C.tm xs)).trans
    ((singleCaller C Q C.k₁ xs).trans (halt_tapes (compiled C Q ei eo) xs).symm)

/-- Any valid time-budgeted oracle program executes on a standard finite TM2 machine.
The caller's workspace survives every call and all callee workspace is cleared before resuming. -/
theorem compile_run {A B : Type} {encode : A → List Bool} {encodeOut : B → List Bool} {query : A → B} {cost time : ℕ → ℕ}
    (oracleRun : ∀ x, TM2OutputsInTime Q ((encode x).map ei.symm) (some ((encodeOut (query x)).map eo.symm)) (time (encode x).length))
    (hcost : ∀ x, time (encode x).length + 2 * (encode x).length + 2 * (encodeOut (query x)).length + 5 ≤ cost (encode x).length)
    {input output : List Bool} {t : ℕ}
    (run : Run C encode encodeOut query cost (initList C.tm input) (haltList C.tm output) t) :
    Nonempty (TM2OutputsInTime (compiled C Q ei eo) input (some output) t) := by
  obtain ⟨k, hk, h⟩ := simulate C Q ei eo oracleRun hcost run
  unfold Exact at h
  rw [embed_init C Q ei eo, embed_halt C Q ei eo] at h
  exact ⟨⟨⟨k, h⟩, hk⟩⟩

open ComplexityTheory BitstringEncoding

/-- A polynomial-time word-valued oracle can be substituted into any caller that runs
in polynomial time for every polynomial charge on the bit length of each query.
The charge used by the compiler also pays for copying the full result. -/
theorem polytime_from_runs {A B X Y : Type} [BitstringEncoding A] [BitstringEncoding B]
    [BitstringEncoding X] [BitstringEncoding Y] (C : OracleProgram) (q : A → B) (f : X → Y)
    (hq : IsPolyTime q)
    (runs : ∀ charge : Polynomial ℕ, ∃ total : Polynomial ℕ, ∀ x,
      Run C bitEncode bitEncode q charge.eval (initList C.tm (bitEncode x))
        (haltList C.tm (bitEncode (f x))) (total.eval (bitEncode x).length)) : IsPolyTime f := by
  obtain ⟨outputBound, hsize⟩ := FactorMachineBound.polytime_output_bound hq
  obtain ⟨Q⟩ := hq
  let charge : Polynomial ℕ := Q.time + 2 * Polynomial.X + 2 * outputBound + 5
  have budget (x : A) : Q.time.eval (bitEncode x).length + 2 * (bitEncode x).length +
      2 * (bitEncode (q x)).length + 5 ≤ charge.eval (bitEncode x).length := by
    have h := hsize x
    simp [charge]
    omega
  obtain ⟨total, run⟩ := runs charge
  refine ⟨{ tm := compiled C Q.tm Q.inputAlphabet Q.outputAlphabet
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := total
            outputsFun := fun x => ?_ }⟩
  let out := Classical.choice (compile_run C Q.tm Q.inputAlphabet Q.outputAlphabet
    (encode := bitEncode) (encodeOut := bitEncode) (query := q) (time := Q.time.eval)
    Q.outputsFun budget (run x))
  change TM2OutputsInTime (compiled C Q.tm Q.inputAlphabet Q.outputAlphabet) ((bitEncode x).map id)
    (some ((bitEncode (f x)).map id)) (total.eval (bitEncode x).length)
  erw [List.map_id, List.map_id]
  exact out

end FactorWordOracle

/- Finite-stack caller that retains the input, invokes the square-root subroutine, compares
the input, cutoff, and reply in parallel, and encodes either a sentinel or a capped query. -/

namespace FactorGuardController

open Turing.TM2 FactorGuardBits FactorOracleMachine

inductive Stack | io | arg | tmp | savedN | ns | br | sr deriving DecidableEq
inductive Label | parse | restore | ask | scan | emitRoot (a : Action) | emitBound (a : Action)
  | emitInput (a : Action) deriving DecidableEq

instance : Fintype Stack := Fintype.ofList [.io,.arg,.tmp,.savedN,.ns,.br,.sr] (by intro k; cases k <;> decide)
instance : Fintype Label := Fintype.ofList
  [.parse,.restore,.ask,.scan,.emitRoot .reject,.emitRoot .accept,.emitRoot .useBound,.emitRoot .useRoot,
   .emitBound .reject,.emitBound .accept,.emitBound .useBound,.emitBound .useRoot,
   .emitInput .reject,.emitInput .accept,.emitInput .useBound,.emitInput .useRoot]
  (by intro l; cases l <;> first | decide | (rename_i a; cases a <;> decide))

abbrev Reg := Flags × Option Bool × Option Bool × Option Bool
abbrev Code := Stmt (fun _ : Stack => Bool) Label Reg
abbrev Config := Cfg (fun _ : Stack => Bool) Label Reg
def blank (g : Flags) : Reg := (g,none,none,none)
def jump (l : Label) : Code := .load (fun r => blank r.1) (.goto fun _ => l)
def take (k : Stack) (item empty : Code) : Code := .pop k (fun r o => (r.1,o,r.2.2))
  (.branch (fun r => r.2.1.isSome) item empty)
def readBit : Reg → Bool := fun r => r.2.1.getD false
def maybeSave (k : Stack) (get : Reg → Option Bool) (next : Code) : Code :=
  .branch (fun r => (get r).isSome) (.push k (fun r => (get r).getD false) next) next
def isQuery (a : Action) : Bool := decide (a = .useBound ∨ a = .useRoot)

def program : Label → Code
  | .parse => .pop .io (fun r o => (r.1,o,r.2.2)) (.branch readBit
      (.pop .io (fun r o => (r.1,o,r.2.2)) (.push .tmp readBit (.push .savedN readBit (jump .parse))))
      (jump .restore))
  | .restore => take .tmp (.push .arg readBit (.push .ns readBit (jump .restore))) (jump .ask)
  | .ask => .halt
  | .scan => .pop .ns (fun r o => (r.1,o,r.2.2))
      (.pop .io (fun r o => (r.1,r.2.1,o,r.2.2.2))
        (.pop .arg (fun r o => (r.1,r.2.1,r.2.2.1,o))
          (.branch (fun r => r.2.1.isSome || r.2.2.1.isSome || r.2.2.2.isSome)
            (maybeSave .br (fun r => r.2.2.1) (maybeSave .sr (fun r => r.2.2.2)
              (.load (fun r => blank (tick r.1 r.2.1 r.2.2.1 r.2.2.2)) (.goto fun _ => .scan))))
            (.goto fun r => .emitRoot (action r.1)))))
  | .emitRoot a => take .sr
      (if a = .useRoot then .push .io readBit (jump (.emitRoot a)) else jump (.emitRoot a))
      (jump (.emitBound a))
  | .emitBound a => take .br
      (if a = .useBound then .push .io readBit (jump (.emitBound a)) else jump (.emitBound a))
      (if a = .accept then .push .io (fun _ => true) (.push .io (fun _ => false) (jump (.emitInput a)))
       else .push .io (fun _ => false) (jump (.emitInput a)))
  | .emitInput a => take .savedN
      (if isQuery a then .push .io readBit (.push .io (fun _ => true) (jump (.emitInput a))) else jump (.emitInput a))
      (.load (fun _ => blank initial) .halt)

def machine : OracleProgram where
  K := Stack
  Λ := Label
  σ := Reg
  k₀ := .io
  k₁ := .io
  arg := .arg
  main := .parse
  call := .ask
  resume := .scan
  initialState := blank initial
  m := program

def words (io arg tmp savedN ns br sr : List Bool) : Stack → List Bool
  | .io => io | .arg => arg | .tmp => tmp | .savedN => savedN | .ns => ns | .br => br | .sr => sr
def cfg (l : Option Label) (g : Flags) (io arg tmp savedN ns br sr : List Bool) : Config :=
  ⟨l, blank g, words io arg tmp savedN ns br sr⟩
abbrev atL (l : Label) := cfg (some l)

inductive Work : Config → Config → ℕ → Prop
  | refl (c) : Work c c 0
  | one {c d} (hc : c.l ≠ some .ask) (hs : step program c = some d) : Work c d 1
  | trans {a b c t u} : Work a b t → Work b c u → Work a c (t+u)
  | mono {a b t u} : Work a b t → t ≤ u → Work a b u

theorem workStep {l g io ar tmp saved ns br sr dest}
    (hc : l ≠ .ask)
    (hl : (stepAux (program l) (blank g) (words io ar tmp saved ns br sr)).l = dest.l)
    (hv : (stepAux (program l) (blank g) (words io ar tmp saved ns br sr)).var = dest.var)
    (hs : ∀ k, (stepAux (program l) (blank g) (words io ar tmp saved ns br sr)).stk k = dest.stk k) :
    Work (atL l g io ar tmp saved ns br sr) dest 1 := by
  apply Work.one (fun h => hc (Option.some.inj h))
  apply congrArg some
  change stepAux _ _ _ = dest
  have hw := funext hs
  cases he : stepAux (program l) (blank g) (words io ar tmp saved ns br sr) with
  | mk L V S => rw [he] at hl hv hw; cases dest; congr

theorem toRun (s : ℕ → ℕ) (c : ℕ → ℕ) {a b t} (h : Work a b t) :
    FactorWordOracle.Run machine BitstringEncoding.bitEncode BitstringEncoding.bitEncode s c a b t := by
  induction h with
  | refl => exact .refl _
  | one hc hs => exact .normal hc hs
  | trans _ _ ha hb => exact .trans ha hb
  | mono _ he ha => exact .mono ha he

def keepHead : List Bool → List Bool → List Bool
  | [], acc => acc
  | a::_, acc => a::acc

theorem scanDone (g : Flags) (saved br sr : List Bool) :
    Work (atL .scan g [] [] [] saved [] br sr) (atL (.emitRoot (action g)) g [] [] [] saved [] br sr) 1 := by
  apply workStep <;> first | decide | rfl | (intro k; cases k <;> rfl)

theorem scanStep (g : Flags) (n b s saved br sr : List Bool) (h : ¬(n=[] ∧ b=[] ∧ s=[])) :
    Work (atL .scan g b s [] saved n br sr)
      (atL .scan (tick g n.head? b.head? s.head?) b.tail s.tail [] saved n.tail
        (keepHead b br) (keepHead s sr)) 1 := by
  cases n <;> cases b <;> cases s
  · exact (h ⟨rfl,rfl,rfl⟩).elim
  all_goals apply workStep <;> first | decide | rfl | (intro k; cases k <;> rfl)

private theorem parseBits (n b acc : List Bool) : Work
    (atL .parse initial (BitstringEncoding.delimit n ++ b) [] acc acc [] [] [])
    (atL .restore initial b [] (n.reverse ++ acc) (n.reverse ++ acc) [] [] []) (n.length+1) := by
  induction n generalizing acc with
  | nil => apply workStep <;> first | decide | rfl | (intro k; cases k <;> rfl)
  | cons a ns ih =>
    have h : Work (atL .parse initial (BitstringEncoding.delimit (a::ns) ++ b) [] acc acc [] [] [])
      (atL .parse initial (BitstringEncoding.delimit ns ++ b) [] (a::acc) (a::acc) [] [] []) 1 := by
      apply workStep <;> first | decide | rfl | (intro k; cases k <;> rfl)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm 1 (ns.length+1)] using h.trans (ih (a::acc))

private theorem restoreBits (xs b saved acc : List Bool) : Work
    (atL .restore initial b acc xs saved acc [] [])
    (atL .ask initial b (xs.reverse ++ acc) [] saved (xs.reverse ++ acc) [] []) (xs.length+1) := by
  induction xs generalizing acc with
  | nil => apply workStep <;> first | decide | rfl | (intro k; cases k <;> rfl)
  | cons a xs ih =>
    have h : Work (atL .restore initial b acc (a::xs) saved acc [] [])
      (atL .restore initial b (a::acc) xs saved (a::acc) [] []) 1 := by
      apply workStep <;> first | decide | rfl | (intro k; cases k <;> rfl)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm 1 (xs.length+1)] using h.trans (ih (a::acc))

theorem prepare_call (n b : List Bool) : Work
    (atL .parse initial (BitstringEncoding.delimit n ++ b) [] [] [] [] [] [])
    (atL .ask initial b n [] n.reverse n [] []) (2*n.length+2) := by
  have a := parseBits n b []
  have z := restoreBits n.reverse b n.reverse []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at a z
  exact (a.trans z).mono (by omega)

end FactorGuardController

/- A single scan accumulates the high-order comparison results and reverses the
two candidate bound words. Each nonterminal transition consumes at least one bit. -/

namespace FactorGuardScan

open FactorGuardBits FactorGuardController

private theorem tail_work (n b s : List Bool) (h : ¬ (n = [] ∧ b = [] ∧ s = [])) :
    n.tail.length + b.tail.length + s.tail.length < n.length + b.length + s.length := by
  cases n <;> cases b <;> cases s <;> simp_all <;> omega

private theorem reassemble (w acc : List Bool) : w.tail.reverse ++ keepHead w acc = w.reverse ++ acc := by
  cases w <;> simp [keepHead, List.reverse_cons]

/-- Transfer the entire three-word scan and include the final dispatch transition. -/
theorem scanRun (g : Flags) (n b s saved br sr : List Bool) :
    Work (atL .scan g b s [] saved n br sr)
      (atL (.emitRoot (action (summary g n b s))) (summary g n b s)
        [] [] [] saved [] (b.reverse ++ br) (s.reverse ++ sr))
      (n.length + b.length + s.length + 1) := by
  by_cases h : n = [] ∧ b = [] ∧ s = []
  · rcases h with ⟨rfl, rfl, rfl⟩
    simpa [summary_nil] using scanDone g saved br sr
  · let g' := tick g n.head? b.head? s.head?
    have first : Work (atL .scan g b s [] saved n br sr)
        (atL .scan g' b.tail s.tail [] saved n.tail (keepHead b br) (keepHead s sr)) 1 := by
      exact scanStep g n b s saved br sr h
    have rest := scanRun g' n.tail b.tail s.tail saved (keepHead b br) (keepHead s sr)
    have sumEq : summary g' n.tail b.tail s.tail = summary g n b s :=
      summary_tick g n b s h
    rw [sumEq, reassemble, reassemble] at rest
    apply (first.trans rest).mono
    have := tail_work n b s h
    omega
termination_by n.length + b.length + s.length
decreasing_by exact tail_work n b s h

end FactorGuardScan

/-
# Encoding the guard decision

The output pass consumes the three words saved by the comparison scan. For a
genuine query it copies either the bound or the square root, then prefixes that
word with the self-delimited number. For a sentinel it writes a constant word.
Both paths empty every working stack before halting.
-/

namespace FactorGuardOutput

open FactorGuardController FactorGuardBits BitstringEncoding

/-- The four outputs produced by the three linear stack passes. -/
def emitWord : Action → List Bool → List Bool → List Bool → List Bool
  | .reject, _, _, _ => [false]
  | .accept, _, _, _ => [false, true]
  | .useBound, n, b, _ => delimit n ++ b
  | .useRoot, n, _, s => delimit n ++ s

private def rootWord : Action → List Bool → List Bool
  | .useRoot, s => s
  | _, _ => []

private def boundWord : Action → List Bool → List Bool → List Bool
  | .useRoot, _, s => s
  | .useBound, b, _ => b
  | _, _, _ => []

private theorem consume (stage : List Bool → List Bool → Config) (finish : List Bool → Config)
    (next : ∀ bit xs seen, Work (stage (bit :: xs) seen) (stage xs (bit :: seen)) 1)
    (done_ : ∀ seen, Work (stage [] seen) (finish seen) 1)
    (xs seen : List Bool) :
    Work (stage xs seen) (finish (xs.reverse ++ seen)) (xs.length + 1) := by
  induction xs generalizing seen with
  | nil => simpa using done_ seen
  | cons bit xs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm 1 (xs.length + 1)] using
      (next bit xs seen).trans (ih (bit :: seen))

/-- The clock includes one empty-stack check at the end of each pass. -/
theorem emitRun (a : Action) (g : Flags) (n b s : List Bool) :
    Work (atL (.emitRoot a) g [] [] [] n.reverse [] b.reverse s.reverse)
      (cfg none initial (emitWord a n b s) [] [] [] [] [] [])
      (s.length + b.length + n.length + 3) := by
  have root := consume
    (fun xs seen => atL (.emitRoot a) g (rootWord a seen) [] [] n.reverse [] b.reverse xs)
    (fun seen => atL (.emitBound a) g (rootWord a seen) [] [] n.reverse [] b.reverse [])
    (by intros; cases a <;> apply workStep <;> first | rfl | decide | (intro k; cases k <;> rfl))
    (by intros; cases a <;> apply workStep <;> first | rfl | decide | (intro k; cases k <;> rfl))
    s.reverse []
  have bound := consume
    (fun xs seen => atL (.emitBound a) g (boundWord a seen s) [] [] n.reverse [] xs [])
    (fun seen => atL (.emitInput a) g (emitWord a [] seen s) [] [] n.reverse [] [] [])
    (by intros; cases a <;> apply workStep <;> first | rfl | decide | (intro k; cases k <;> rfl))
    (by intros; cases a <;> apply workStep <;> first | rfl | decide | (intro k; cases k <;> rfl))
    b.reverse []
  have input := consume
    (fun xs seen => atL (.emitInput a) g (emitWord a seen b s) [] [] xs [] [] [])
    (fun seen => cfg none initial (emitWord a seen b s) [] [] [] [] [] [])
    (by intros; cases a <;> apply workStep <;> first | rfl | decide | (intro k; cases k <;> rfl))
    (by intros; cases a <;> apply workStep <;> first | rfl | decide | (intro k; cases k <;> rfl))
    n.reverse []
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at root bound input
  have emptyRoot : rootWord a [] = [] := by cases a <;> rfl
  have enterBound : boundWord a [] s = rootWord a s := by cases a <;> rfl
  rw [emptyRoot] at root
  rw [enterBound] at bound
  convert (root.trans bound).trans input using 1
  omega

end FactorGuardOutput

/- Assemble the guarded-query program on canonical pair encodings. -/

namespace FactorGuardMachine

open FactorGuardBits FactorGuardController FactorGuardOutput Computability BitstringEncoding Turing

private theorem emit_prepare (root : ℕ → ℕ) (n b : ℕ) :
    emitWord (action (summary initial (encodeNat n) (encodeNat b) (encodeNat (root n))))
      (encodeNat n) (encodeNat b) (encodeNat (root n)) = bitEncode (prepare root (n,b)) := by
  rw [action_encode]
  simp only [prepare]
  by_cases hb : b < 2
  · simp only [hb, if_true]; rfl
  by_cases hn : n ≤ b
  · simp only [hb, hn, if_false, if_true]; rfl
  by_cases he : 2 ∣ n
  · simp only [hb, hn, he, if_false, if_true]; rfl
  by_cases hr : 2 ≤ root n
  · have hb' : 2 ≤ b := by omega
    by_cases hsmall : b ≤ root n
    · simp only [hb, hn, he, hr, hb', hsmall, if_false, if_true, min_eq_left hsmall]; rfl
    · have hlarge : root n ≤ b := by omega
      simp only [hb, hn, he, hr, hsmall, if_false, if_true, min_eq_right hlarge]; rfl
  · have hm : ¬2 ≤ min b (root n) := fun h => hr (h.trans (min_le_right _ _))
    simp only [hb, hn, he, hr, hm, if_false]; rfl

private theorem start (n b : ℕ) : initList machine.tm (bitEncode (n,b)) =
    atL .parse initial (delimit (encodeNat n) ++ encodeNat b) [] [] [] [] [] [] := by
  apply congrArg (fun st => (⟨some Label.parse, blank initial, st⟩ : Config))
  funext k; cases k <;> rfl

private theorem finish (s : List Bool) : haltList machine.tm s = cfg none initial s [] [] [] [] [] [] := by
  apply congrArg (fun st => (⟨none, blank initial, st⟩ : Config))
  funext k; cases k <;> rfl

/-- The caller charges the square-root oracle once and pays linear cost in the three word lengths. -/
theorem machine_run (s : ℕ → ℕ) (charge : ℕ → ℕ) (n b : ℕ) :
    FactorWordOracle.Run machine bitEncode bitEncode s charge (initList machine.tm (bitEncode (n,b)))
      (haltList machine.tm (bitEncode (prepare s (n,b))))
      (4*(encodeNat n).length + 2*(encodeNat b).length + 2*(encodeNat (s n)).length + charge (encodeNat n).length + 6) := by
  let a := encodeNat n
  let w := encodeNat b
  let z := encodeNat (s n)
  let g := summary initial a w z
  have pre := toRun s charge (prepare_call a w)
  have query : FactorWordOracle.Run machine bitEncode bitEncode s charge
      (atL .ask initial w a [] a.reverse a [] []) (atL .scan initial w z [] a.reverse a [] []) (charge a.length) := by
    have h := FactorWordOracle.Run.oracle (C := machine) (encode := (bitEncode : ℕ → List Bool))
      (encodeOut := (bitEncode : ℕ → List Bool)) (query := s) (cost := charge) n (blank initial)
      (words w a [] a.reverse a [] []) rfl
    have hst : Function.update (words w a [] a.reverse a [] []) machine.arg (bitEncode (s n)) =
        words w z [] a.reverse a [] [] := by funext k; cases k <;> rfl
    erw [hst] at h
    exact h
  have scan := FactorGuardScan.scanRun initial a w z a.reverse [] []
  simp only [List.append_nil] at scan
  have final := emitRun (action g) g a w z
  have h := (pre.trans query).trans (toRun s charge (scan.trans final))
  rw [start, finish, ← emit_prepare]
  apply h.mono
  dsimp only [a, w, z]
  omega

end FactorGuardMachine

/- A clocked finite-stack caller with a Boolean-valued polynomial-time subroutine
is itself a polynomial-time function on the canonical input and output encodings. -/

namespace FactorOraclePolytime

open FactorOracleMachine Turing ComplexityTheory BitstringEncoding

variable {A X Y : Type} [BitstringEncoding A] [BitstringEncoding X] [BitstringEncoding Y]
variable {query : A → Bool} {f : X → Y}

/-- Package a concrete comparator and a proof of the caller's clock into the
polynomial-time witness used in the factorization conjecture. -/
theorem of_machine (C : OracleProgram)
    (Q : TM2ComputableInPolyTime bitEncode bitEncode query) (budget : Polynomial ℕ)
    (run : ∀ x, C.Run bitEncode query Q.time.eval (initList C.tm (bitEncode x))
      (haltList C.tm (bitEncode (f x))) (budget.eval (bitEncode x).length)) :
    IsPolyTime f := by
  have reply (a : A) : TM2OutputsInTime Q.tm ((bitEncode a).map Q.inputAlphabet.symm)
      (some [Q.outputAlphabet.symm (query a)]) (Q.time.eval (bitEncode a).length) :=
    Q.outputsFun a
  refine ⟨{ tm := C.compiled Q.tm Q.inputAlphabet Q.outputAlphabet
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := budget
            outputsFun := fun x => ?_ }⟩
  let result := Classical.choice
    (C.compile_run Q.tm Q.inputAlphabet Q.outputAlphabet reply (run x))
  change TM2OutputsInTime (C.compiled Q.tm Q.inputAlphabet Q.outputAlphabet) ((bitEncode x).map id)
    (some ((bitEncode (f x)).map id)) (budget.eval (bitEncode x).length)
  erw [List.map_id, List.map_id]
  exact result

/-- A clock transformation may depend on the comparator's polynomial. -/
theorem of_query (C : OracleProgram) (hq : IsPolyTime query)
    (budget : Polynomial ℕ → Polynomial ℕ)
    (run : ∀ (Q : TM2ComputableInPolyTime bitEncode bitEncode query) x,
      C.Run bitEncode query Q.time.eval (initList C.tm (bitEncode x))
        (haltList C.tm (bitEncode (f x))) ((budget Q.time).eval (bitEncode x).length)) :
    IsPolyTime f := by
  obtain ⟨Q⟩ := hq
  exact of_machine C Q (budget Q.time) (run Q)

end FactorOraclePolytime

/-
# The sentinel comparator

A pair whose first component is zero starts with a zero bit. The remaining
word is the second component, so its emptiness distinguishes a zero from a
positive sentinel. Every pair with a positive first component starts with a
one bit and can be forwarded intact to the supplied comparator.
-/

namespace FactorGuardPost

open Turing Computability ComplexityTheory BitstringEncoding FactorOracleMachine

def post (q : ℕ × ℕ → Bool) (p : ℕ × ℕ) : Bool :=
  if p.1 = 0 then decide (p.2 ≠ 0) else q p

private inductive Label
  | start | clear | ask | resume
  deriving DecidableEq

private instance : Fintype Label := Fintype.ofList [.start, .clear, .ask, .resume]
  (by intro l; cases l <;> decide)

private abbrev Code := TM2.Stmt (fun _ : Unit => Bool) Label Bool

private def jump (l : Label) : Code := .load (fun _ => false) (.goto (fun _ => l))

private def answer (b : Bool) : Code :=
  .push () (fun _ => b) (.load (fun _ => false) .halt)

private def program : Label → Code
  | .start =>
    .peek () (fun _ head => head.getD false) (.branch id (jump .ask)
      (.pop () (fun _ _ => false)
        (.peek () (fun _ head => head.isSome)
          (.branch id (jump .clear) (answer false)))))
  | .clear => .pop () (fun _ head => head.isSome) (.branch id (jump .clear) (answer true))
  | .ask => .halt
  | .resume => .halt

private abbrev driver : OracleProgram where
  K := Unit
  Λ := Label
  σ := Bool
  k₀ := ()
  k₁ := ()
  arg := ()
  main := .start
  call := .ask
  resume := .resume
  initialState := false
  m := program

private def cfg (l : Option Label) (w : List Bool) : driver.Cfg := ⟨l, false, fun _ => w⟩

private abbrev Runs (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) :=
  driver.Run (bitEncode (α := ℕ × ℕ)) q P.eval

private theorem initial (w : List Bool) : initList driver.tm w = cfg (some .start) w := by
  unfold initList cfg
  congr 1

private theorem finalCfg (w : List Bool) : haltList driver.tm w = cfg none w := by
  unfold haltList cfg
  congr 1

private theorem one (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) {l v w l'}
    (hne : l ≠ Label.ask)
    (hl : (TM2.stepAux (program l) false (fun _ => v)).l = l')
    (hv : (TM2.stepAux (program l) false (fun _ => v)).var = false)
    (hw : (TM2.stepAux (program l) false (fun _ => v)).stk () = w) :
    Runs q P (cfg (some l) v) (cfg l' w) 1 := by
  apply OracleProgram.Run.normal (fun h => hne (Option.some.inj h))
  apply congrArg some
  change TM2.stepAux _ _ _ = cfg _ _
  cases he : TM2.stepAux (program l) false (fun _ => v) with
  | mk L V S =>
    rw [he] at hl hv hw
    have hs : S = fun _ => w := by funext k; cases k; exact hw
    cases hl
    cases hv
    cases hs
    rfl

private theorem clear_run (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) (w : List Bool) :
    Runs q P (cfg (some .clear) w) (cfg none [true]) (w.length + 1) := by
  induction w with
  | nil => apply one <;> first | rfl | decide
  | cons b w ih =>
    have scan : Runs q P (cfg (some .clear) (b :: w)) (cfg (some .clear) w) 1 := by
      apply one <;> first | rfl | decide
    convert scan.trans ih using 1
    simp [Nat.add_comm]

private theorem forward (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) (x : ℕ × ℕ)
    (v : List Bool) (hx : bitEncode x = true :: v) :
    Runs q P (cfg (some .start) (bitEncode x)) (cfg none [q x])
      (P.eval (bitEncode x).length + 2 * (bitEncode x).length + 6) := by
  have entry : Runs q P (cfg (some .start) (bitEncode x)) (cfg (some .ask) (bitEncode x)) 1 := by
    rw [hx]
    apply one <;> first | rfl | decide
  have call := @OracleProgram.Run.oracle driver _ (bitEncode (α := ℕ × ℕ)) q P.eval x false
    (fun _ => bitEncode x) rfl
  have update : Function.update (fun _ : Unit => bitEncode x) () [q x] = fun _ => [q x] := by
    funext k
    cases k
    rfl
  change Runs q P (cfg (some .ask) (bitEncode x))
    ⟨some Label.resume, false, Function.update (fun _ : Unit => bitEncode x) () [q x]⟩ _ at call
  rw [update] at call
  have done_ : Runs q P (cfg (some .resume) [q x]) (cfg none [q x]) 1 := by
    apply one <;> first | rfl | decide
  convert (entry.trans call).trans done_ using 1
  omega

private theorem nat_nil (n : ℕ) : encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have h' := decode_encodeNat n
    rw [h] at h'
    exact h'.symm
  · rintro rfl
    rfl

private theorem full_run (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) (x : ℕ × ℕ) :
    Runs q P (initList driver.tm (bitEncode x)) (haltList driver.tm (bitEncode (post q x)))
      ((P + 2 * Polynomial.X + 6).eval (bitEncode x).length) := by
  rw [initial, finalCfg]
  rcases x with ⟨n, b⟩
  change Runs q P (cfg (some .start) (bitEncode (n, b))) (cfg none [post q (n, b)]) _
  by_cases hn : n = 0
  · subst n
    have shape : bitEncode (0, b) = false :: encodeNat b := rfl
    by_cases hb : b = 0
    · subst b
      have r : Runs q P (cfg (some .start) [false]) (cfg none [false]) 1 := by
        apply one <;> first | rfl | decide
      apply r.mono
      simp
    · have out : post q (0, b) = true := by simp [post, hb]
      rw [shape, out]
      have visit : Runs q P (cfg (some .start) (false :: encodeNat b))
          (cfg (some .clear) (encodeNat b)) 1 := by
        cases h : encodeNat b with
        | nil => exact (hb ((nat_nil b).mp h)).elim
        | cons a as => apply one <;> first | rfl | decide
      apply (visit.trans (clear_run q P _)).mono
      simp
      omega
  · have shape : ∃ v, bitEncode (n, b) = true :: v := by
      cases h : encodeNat n with
      | nil => exact (hn ((nat_nil n).mp h)).elim
      | cons a as =>
        refine ⟨a :: (delimit as ++ encodeNat b), ?_⟩
        change delimit (encodeNat n) ++ encodeNat b = _
        rw [h]
        rfl
    obtain ⟨v, hv⟩ := shape
    simpa [post, hn] using forward q P (n, b) v hv

theorem polytime_post (q : ℕ × ℕ → Bool) (hq : IsPolyTime q) : IsPolyTime (post q) := by
  apply FactorOraclePolytime.of_query driver hq (fun P => P + 2 * Polynomial.X + 6)
  intro Q x
  exact full_run q Q.time x

end FactorGuardPost

/-
# Shared stacks for two finite Turing machines

All stacks of the first machine keep their indices. Its output stack also serves
as the second machine's input. Every other stack of the second machine receives
a separate index.
-/

namespace FactorSharedStacks

open Turing

variable (M N : FinTM2)

abbrev Indices := M.K ⊕ {k : N.K // k ≠ N.k₀}

instance : Fintype (Indices M N) := by
  let _ := M.kFin
  let _ := N.kFin
  exact inferInstanceAs (Fintype (M.K ⊕ {k : N.K // k ≠ N.k₀}))

def Alphabet : Indices M N → Type
  | .inl k => M.Γ k
  | .inr k => N.Γ k.1

def left : M.K ↪ Indices M N := ⟨Sum.inl, Sum.inl_injective⟩

private def rightIndex (k : N.K) : Indices M N :=
  if h : k = N.k₀ then .inl M.k₁ else .inr ⟨k, h⟩

def right : N.K ↪ Indices M N where
  toFun := rightIndex M N
  inj' := by
    intro a b hab
    by_cases ha : a = N.k₀ <;> by_cases hb : b = N.k₀ <;>
      simp_all [rightIndex]

@[simp] theorem right_input : right M N N.k₀ = left M N M.k₁ := by
  change rightIndex M N N.k₀ = Sum.inl M.k₁
  simp [rightIndex]

theorem right_other (k : N.K) (hk : k ≠ N.k₀) : right M N k = .inr ⟨k, hk⟩ := by
  change rightIndex M N k = _
  simp [rightIndex, hk]

theorem overlap_iff (k : M.K) (j : N.K) :
    left M N k = right M N j ↔ k = M.k₁ ∧ j = N.k₀ := by
  by_cases hj : j = N.k₀
  · subst j
    simp
  · simp [right_other M N j hj, left, hj]

def leftAlphabet (k : M.K) : Alphabet M N (left M N k) ≃ M.Γ k := Equiv.refl _

def rightAlphabet (e : M.Γ M.k₁ ≃ N.Γ N.k₀) (k : N.K) :
    Alphabet M N (right M N k) ≃ N.Γ k :=
  if h : k = N.k₀ then
    (Equiv.cast (congrArg (Alphabet M N) ((congrArg (right M N) h).trans (right_input M N)))).trans
      (e.trans (Equiv.cast (congrArg N.Γ h.symm)))
  else Equiv.cast (congrArg (Alphabet M N) (right_other M N k h))

/-- A collection of empty stacks except for one word at the given index. -/
def singleton {K : Type} [DecidableEq K] (Γ : K → Type) (k : K) (word : List (Γ k)) :
    ∀ j, List (Γ j) := Function.update (fun j => ([] : List (Γ j))) k word

private theorem singleton_cast {K : Type} [DecidableEq K] (Γ : K → Type) {i j : K}
    (h : i = j) (word : List (Γ j)) :
    singleton Γ i (word.map (Equiv.cast (congrArg Γ h)).symm) = singleton Γ j word := by
  subst j
  simp

/-- The same physical stack contains the intermediate output and the next machine's input. -/
theorem handoff (e : M.Γ M.k₁ ≃ N.Γ N.k₀) (ys : List (M.Γ M.k₁)) :
    singleton (Alphabet M N) (left M N M.k₁) (ys.map (leftAlphabet M N M.k₁).symm) =
      singleton (Alphabet M N) (right M N N.k₀)
        ((ys.map e).map (rightAlphabet M N e N.k₀).symm) := by
  have hn := singleton_cast (Alphabet M N) (right_input M N) ys
  have hleft : ys.map (leftAlphabet M N M.k₁).symm = ys := List.map_id ys
  refine (congrArg (singleton (Alphabet M N) (left M N M.k₁)) hleft).trans (hn.symm.trans ?_)
  apply congrArg (singleton (Alphabet M N) (right M N N.k₀))
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  simp [Function.comp_def, rightAlphabet]
  change _ = (Equiv.cast (congrArg (Alphabet M N) (right_input M N))).symm (e.symm (e a))
  exact congrArg (Equiv.cast (congrArg (Alphabet M N) (right_input M N))).symm
    (e.symm_apply_apply a).symm

end FactorSharedStacks

/-
# Composition of polynomial-time TM2 computations

The two simulations share exactly one stack. The first machine halts with only
its output on that stack, in the configuration required to start the second.
The two clocks therefore add. A bound on the first machine's output length
turns that sum into a polynomial in the original input length.
-/

namespace FactorMachineComposition

open Turing FactorMachineLift FactorSharedStacks ComplexityTheory

variable (M N : FinTM2) (e : M.Γ M.k₁ ≃ N.Γ N.k₀)

def first : Lift M.Γ (Alphabet M N) M.Λ (M.Λ ⊕ N.Λ) M.σ (M.σ × N.σ) where
  stack := left M N
  symbol k := (leftAlphabet M N k).symm
  label := Sum.inl
  exitLabel := some (Sum.inr N.main)
  read := Prod.fst
  write w v := (v, w.2)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def second : Lift N.Γ (Alphabet M N) N.Λ (M.Λ ⊕ N.Λ) N.σ (M.σ × N.σ) where
  stack := right M N
  symbol k := (rightAlphabet M N e k).symm
  label := Sum.inr
  exitLabel := none
  read := Prod.snd
  write w v := (w.1, v)
  read_write _ _ := rfl
  write_write _ _ _ := rfl

def machine : FinTM2 :=
  letI := M.ΛFin
  letI := N.ΛFin
  letI := M.σFin
  letI := N.σFin
  { K := Indices M N
    Γ := Alphabet M N
    k₀ := left M N M.k₀
    k₁ := right M N N.k₁
    Γk₀Fin := M.Γk₀Fin
    Λ := M.Λ ⊕ N.Λ
    main := Sum.inl M.main
    σ := M.σ × N.σ
    initialState := (M.initialState, N.initialState)
    m := Sum.elim (fun l => (first M N).stmt (M.m l))
      (fun l => (second M N e).stmt (N.m l)) }

/-- A singleton collection represents an input, an intermediate word, or an output. -/
private theorem match_singleton {K J Λ Λ' σ σ' : Type} {Γ : K → Type} {Γ' : J → Type}
    [DecidableEq K] [DecidableEq J] (lift : Lift Γ Γ' Λ Λ' σ σ')
    (k : K) (xs : List (Γ k)) :
    lift.StacksMatch (fun _ => []) (singleton Γ k xs)
      (singleton Γ' (lift.stack k) (xs.map (lift.symbol k))) := by
  have hempty : lift.StacksMatch (fun _ => []) (fun _ => []) (fun _ => []) :=
    ⟨fun _ => rfl, fun _ _ => rfl⟩
  exact hempty.update lift k xs

private theorem init_stacks (T : FinTM2) (xs : List (T.Γ T.k₀)) :
    (initList T xs).stk = singleton T.Γ T.k₀ xs := by
  funext k
  by_cases h : k = T.k₀
  · subst k; simp [initList, FactorSharedStacks.singleton]
  · simp [initList, FactorSharedStacks.singleton, h]

private theorem halt_stacks (T : FinTM2) (ys : List (T.Γ T.k₁)) :
    (haltList T ys).stk = singleton T.Γ T.k₁ ys := by
  funext k
  by_cases h : k = T.k₁
  · subst k; simp [haltList, FactorSharedStacks.singleton]
  · simp [haltList, FactorSharedStacks.singleton, h]

def middle (ys : List (M.Γ M.k₁)) : (machine M N e).Cfg :=
  ⟨some (.inr N.main), (M.initialState, N.initialState),
   singleton (Alphabet M N) (left M N M.k₁) (ys.map (leftAlphabet M N M.k₁).symm)⟩

private theorem match_first_start (xs : List (M.Γ M.k₀)) :
    (first M N).Matches (M.initialState, N.initialState) (fun _ => []) (initList M xs)
      (initList (machine M N e) (xs.map (leftAlphabet M N M.k₀).symm)) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [init_stacks, init_stacks]
  exact match_singleton (first M N) _ _

private theorem match_first_end (ys : List (M.Γ M.k₁)) :
    (first M N).Matches (M.initialState, N.initialState) (fun _ => []) (haltList M ys)
      (middle M N e ys) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [halt_stacks]
  exact match_singleton (first M N) _ _

private theorem match_second_start (ys : List (M.Γ M.k₁)) :
    (second M N e).Matches (M.initialState, N.initialState) (fun _ => [])
      (initList N (ys.map e)) (middle M N e ys) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [init_stacks]
  change (second M N e).StacksMatch _ _ (singleton _ _ _)
  rw [handoff M N e ys]
  exact match_singleton (second M N e) _ _

private theorem match_second_end (zs : List (N.Γ N.k₁)) :
    (second M N e).Matches (M.initialState, N.initialState) (fun _ => []) (haltList N zs)
      (haltList (machine M N e) (zs.map (rightAlphabet M N e N.k₁).symm)) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [halt_stacks, halt_stacks]
  exact match_singleton (second M N e) _ _

/-- The simulations run back to back, with no copying transitions at the handoff. -/
def run {xs : List (M.Γ M.k₀)} {ys : List (M.Γ M.k₁)} {zs : List (N.Γ N.k₁)}
    {t u : ℕ} (hr : TM2OutputsInTime M xs (some ys) t)
    (hs : TM2OutputsInTime N (ys.map e) (some zs) u) :
    TM2OutputsInTime (machine M N e) (xs.map (leftAlphabet M N M.k₀).symm)
      (some (zs.map (rightAlphabet M N e N.k₁).symm)) (t + u) := by
  let front := (first M N).evalsToInTime (p := M.m) (P := (machine M N e).m) (fun _ => rfl)
    (match_first_start M N e xs) (match_first_end M N e ys) hr
  let back := (second M N e).evalsToInTime (p := N.m) (P := (machine M N e).m) (fun _ => rfl)
    (match_second_start M N e ys) (match_second_end M N e zs) hs
  exact ⟨front.toEvalsTo.trans _ _ _ _ back.toEvalsTo,
    Nat.add_comm t u ▸ Nat.add_le_add back.steps_le_m front.steps_le_m⟩

private theorem eval_le_eval (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) :
    p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial k c =>
    simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

/-- Compose actual witnesses for arbitrary list encodings. The result uses only the
polynomial clocks of the component machines and a bound on output growth per step. -/
theorem compose_witnesses {α β γ A B C : Type}
    {ea : α → List A} {eb : β → List B} {ec : γ → List C} {f : α → β} {g : β → γ}
    (F : TM2ComputableInPolyTime ea eb f) (G : TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (g ∘ f)) := by
  let bridge := F.outputAlphabet.trans G.inputAlphabet.symm
  obtain ⟨rate, hr⟩ := FactorMachineBound.output_length_le F.tm
  let sizeBound := Polynomial.X + F.time * Polynomial.C rate
  refine ⟨{ tm := machine F.tm G.tm bridge
            inputAlphabet := (leftAlphabet F.tm G.tm _).trans F.inputAlphabet
            outputAlphabet := (rightAlphabet F.tm G.tm bridge _).trans G.outputAlphabet
            time := F.time + G.time.comp sizeBound
            outputsFun := fun x => ?_ }⟩
  let xs := (ea x).map F.inputAlphabet.invFun
  let ys := (eb (f x)).map F.outputAlphabet.invFun
  let zs := (ec (g (f x))).map G.outputAlphabet.invFun
  have hF : TM2OutputsInTime F.tm xs (some ys) (F.time.eval (ea x).length) := F.outputsFun x
  have he : ys.map bridge = (eb (f x)).map G.inputAlphabet.invFun := by
    simp [ys, bridge, List.map_map, Function.comp_def, Equiv.invFun_as_coe]
  have hG : TM2OutputsInTime G.tm (ys.map bridge) (some zs) (G.time.eval (eb (f x)).length) :=
    he ▸ G.outputsFun (f x)
  let whole := run F.tm G.tm bridge hF hG
  have hsize : (eb (f x)).length ≤ sizeBound.eval (ea x).length := by
    simpa [sizeBound, xs, ys] using hr xs ys _ hF
  have htime : whole.steps ≤ (F.time + G.time.comp sizeBound).eval (ea x).length := by
    apply whole.steps_le_m.trans
    simpa only [Polynomial.eval_add, Polynomial.eval_comp] using
      Nat.add_le_add_left (eval_le_eval G.time hsize) (F.time.eval (ea x).length)
  refine ⟨⟨whole.steps, ?_⟩, htime⟩
  have map_inputs {U V W : Type} (u : U ≃ V) (v : V ≃ W) (word : List W) :
      word.map (u.trans v).invFun = (word.map v.invFun).map u.symm := by
    rw [List.map_map]
    rfl
  change (flip bind (machine F.tm G.tm bridge).step)^[whole.steps]
      (some (initList _ ((ea x).map ((leftAlphabet F.tm G.tm _).trans F.inputAlphabet).invFun))) =
    some (haltList _ ((ec (g (f x))).map
      ((rightAlphabet F.tm G.tm bridge _).trans G.outputAlphabet).invFun))
  erw [map_inputs (leftAlphabet F.tm G.tm _) F.inputAlphabet (ea x),
    map_inputs (rightAlphabet F.tm G.tm bridge _) G.outputAlphabet (ec (g (f x)))]
  exact whole.evals_in_steps

/-- Polynomial-time functions in the encoding used by the factoring conjecture are
closed under composition. -/
theorem isPolyTime_comp {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] {f : α → β} {g : β → γ}
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (g ∘ f) := by
  obtain ⟨F⟩ := hf
  obtain ⟨G⟩ := hg
  exact compose_witnesses F G

end FactorMachineComposition

/- Finite-stack controller for the bounded binary search. The oracle replaces the
input/output stack with one Boolean and resumes the controller at a fixed label. -/

namespace FactorSearchController

open Turing.TM2

inductive Stack
  | io | inputRev | fuel | high | scratch
  deriving DecidableEq

inductive Label
  | start | checkSecond | saveInput | round | saveHigh | restoreHigh | writeOnes
  | restoreFuel | writeInput | restoreInput | ask | resume | finishHigh | finishOut | clearInput
  deriving DecidableEq

instance : Fintype Stack := Fintype.ofList [.io, .inputRev, .fuel, .high, .scratch]
  (by intro k; cases k <;> decide)

instance : Fintype Label := Fintype.ofList
  [.start, .checkSecond, .saveInput, .round, .saveHigh, .restoreHigh, .writeOnes,
   .restoreFuel, .writeInput, .restoreInput, .ask, .resume, .finishHigh, .finishOut, .clearInput]
  (by intro l; cases l <;> decide)

abbrev Code := Stmt (fun _ : Stack => Bool) Label (Option Bool)
abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)

private def jump (l : Label) : Code := .load (fun _ => none) (.goto (fun _ => l))
private def stop : Code := .load (fun _ => none) .halt
private def putBit (k : Stack) (b : Bool) (q : Code) : Code := .push k (fun _ => b) q
private def putRead (k : Stack) (q : Code) : Code := .push k (fun s => s.getD false) q
private def take (k : Stack) (item empty : Code) : Code :=
  .pop k (fun _ b => b) (.branch Option.isSome item empty)
private def look (k : Stack) (item empty : Code) : Code :=
  .peek k (fun _ b => b) (.branch Option.isSome item empty)

/-- Each transfer executes one pop and a constant number of pushes per source bit. -/
def program : Label → Code
  | .start => take .io (putRead .inputRev (putRead .fuel (jump .checkSecond)))
      (putBit .io true (putBit .io false stop))
  | .checkSecond => look .io (jump .saveInput)
      (.pop .inputRev (fun s _ => s) (.pop .fuel (fun s _ => s) (putBit .io true stop)))
  | .saveInput => take .io (putRead .inputRev (putRead .fuel (jump .saveInput))) (jump .round)
  | .round => take .fuel (jump .saveHigh) (jump .finishHigh)
  | .saveHigh => take .high (putRead .scratch (jump .saveHigh)) (jump .restoreHigh)
  | .restoreHigh => take .scratch (putRead .high (putRead .io (jump .restoreHigh)))
      (look .high (putBit .io false (jump .writeOnes)) (jump .writeOnes))
  | .writeOnes => take .fuel (putRead .scratch (putBit .io true (jump .writeOnes)))
      (jump .restoreFuel)
  | .restoreFuel => take .scratch (putRead .fuel (jump .restoreFuel))
      (putBit .io false (jump .writeInput))
  | .writeInput => take .inputRev (putRead .scratch (putRead .io (putBit .io true (jump .writeInput))))
      (jump .restoreInput)
  | .restoreInput => take .scratch (putRead .inputRev (jump .restoreInput)) (jump .ask)
  | .ask => .halt
  | .resume => take .io
      (.branch (fun s => s.getD false)
        (look .high (putBit .high false (jump .round)) (jump .round))
        (putBit .high true (jump .round))) (jump .round)
  | .finishHigh => take .high (putRead .scratch (jump .finishHigh)) (jump .finishOut)
  | .finishOut => take .scratch (putRead .io (jump .finishOut)) (jump .clearInput)
  | .clearInput => take .inputRev (jump .clearInput) stop

def words (io inputRev fuel high scratch : List Bool) : Stack → List Bool
  | .io => io
  | .inputRev => inputRev
  | .fuel => fuel
  | .high => high
  | .scratch => scratch

def cfg (l : Option Label) (io inputRev fuel high scratch : List Bool) : Config :=
  ⟨l, none, words io inputRev fuel high scratch⟩

abbrev atL (l : Label) := cfg (some l)

/-- Ordinary paths exclude oracle calls, so are valid under every implementation of the oracle. -/
inductive Work : Config → Config → ℕ → Prop
  | refl (c) : Work c c 0
  | one {c d} : c.l ≠ some .ask → step program c = some d → Work c d 1
  | trans {a b c t u} : Work a b t → Work b c u → Work a c (t + u)

theorem workStep {l io nr fu hi sc d}
    (hne : l ≠ Label.ask)
    (hl : (stepAux (program l) none (words io nr fu hi sc)).l = d.l)
    (hv : (stepAux (program l) none (words io nr fu hi sc)).var = d.var)
    (hio : (stepAux (program l) none (words io nr fu hi sc)).stk .io = d.stk .io)
    (hnr : (stepAux (program l) none (words io nr fu hi sc)).stk .inputRev = d.stk .inputRev)
    (hfu : (stepAux (program l) none (words io nr fu hi sc)).stk .fuel = d.stk .fuel)
    (hhi : (stepAux (program l) none (words io nr fu hi sc)).stk .high = d.stk .high)
    (hsc : (stepAux (program l) none (words io nr fu hi sc)).stk .scratch = d.stk .scratch) :
    Work (atL l io nr fu hi sc) d 1 := by
  apply Work.one (fun h => hne (Option.some.inj h))
  apply congrArg some
  change stepAux _ _ _ = d
  have hstk : (stepAux (program l) none (words io nr fu hi sc)).stk = d.stk := by
    funext k
    cases k <;> assumption
  cases ha : stepAux (program l) none (words io nr fu hi sc) with
  | mk L V S =>
    rw [ha] at hl hv hstk
    cases d
    congr

/-- A stack pass reverses the source into its accumulator. The extra transition
detects the empty source and transfers to the next label. -/
theorem consume (stage : List Bool → List Bool → Config) (finish : List Bool → Config)
    (next : ∀ b xs acc, Work (stage (b :: xs) acc) (stage xs (b :: acc)) 1)
    (done_ : ∀ acc, Work (stage [] acc) (finish acc) 1)
    (xs acc : List Bool) : Work (stage xs acc) (finish (xs.reverse ++ acc)) (xs.length + 1) := by
  induction xs generalizing acc with
  | nil => simpa using done_ acc
  | cons b xs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm 1 (xs.length + 1)] using
      (next b xs acc).trans (ih (b :: acc))

theorem prepareRound (input remaining high : List Bool) (v : Bool) :
    Work (atL .round [] input.reverse (v :: remaining) high [])
      (atL .ask (FactorSearchBits.queryWord input remaining high) input.reverse remaining high [])
      (2 * high.length + 2 * remaining.length + 2 * input.length + 7) := by
  have a : Work (atL .round [] input.reverse (v :: remaining) high [])
      (atL .saveHigh [] input.reverse remaining high []) 1 := by
    apply workStep <;> first | rfl | decide
  have b := consume (fun xs acc => atL .saveHigh [] input.reverse remaining xs acc)
      (fun acc => atL .restoreHigh [] input.reverse remaining [] acc)
      (by intros; apply workStep <;> first | rfl | decide)
      (by intros; apply workStep <;> first | rfl | decide) high []
  have c := consume (fun xs acc => atL .restoreHigh acc input.reverse remaining acc xs)
      (fun acc => atL .writeOnes (FactorSearchBits.digit false acc) input.reverse remaining acc [])
      (by intros; apply workStep <;> first | rfl | decide)
      (by intro acc; cases acc <;> apply workStep <;> first | rfl | decide) high.reverse []
  let low := FactorSearchBits.digit false high
  have d := consume (fun xs acc => atL .writeOnes ((acc.map (fun _ => true)) ++ low)
        input.reverse xs high acc)
      (fun acc => atL .restoreFuel ((acc.map (fun _ => true)) ++ low) input.reverse [] high acc)
      (by intros; apply workStep <;> first | rfl | decide)
      (by intros; apply workStep <;> first | rfl | decide) remaining []
  let pivot := FactorSearchBits.pivot remaining high
  have e := consume (fun xs acc => atL .restoreFuel pivot input.reverse acc high xs)
      (fun acc => atL .writeInput (false :: pivot) input.reverse acc high [])
      (by intros; apply workStep <;> first | rfl | decide)
      (by intros; apply workStep <;> first | rfl | decide) remaining.reverse []
  have f := consume (fun xs acc => atL .writeInput (BitstringEncoding.delimit acc ++ pivot)
        xs remaining high acc)
      (fun acc => atL .restoreInput (BitstringEncoding.delimit acc ++ pivot) [] remaining high acc)
      (by intros; apply workStep <;> first | rfl | decide)
      (by intros; apply workStep <;> first | rfl | decide) input.reverse []
  have g := consume (fun xs acc => atL .restoreInput (FactorSearchBits.queryWord input remaining high)
        acc remaining high xs)
      (fun acc => atL .ask (FactorSearchBits.queryWord input remaining high) acc remaining high [])
      (by intros; apply workStep <;> first | rfl | decide)
      (by intros; apply workStep <;> first | rfl | decide) input []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at b c d e f g
  have hd : remaining.reverse.map (fun _ => true) = remaining.map (fun _ => true) := by simp
  rw [hd] at d
  convert ((((((a.trans b).trans c).trans d).trans e).trans f).trans g) using 1
  omega

theorem resumeRound (nr remaining high : List Bool) (answer : Bool) :
    Work (atL .resume [answer] nr remaining high [])
      (atL .round [] nr remaining (FactorSearchBits.digit (!answer) high) []) 1 := by
  cases answer <;> cases high <;> apply workStep <;> first | rfl | decide

end FactorSearchController

/-
# Startup and cleanup for the binary-search TM2 controller

The first two transitions distinguish the empty and singleton encodings from
longer inputs. For longer inputs the controller saves one copy each in the
input and fuel stacks. With the fuel exhausted, two passes move the result to
the I/O stack in the original order, and one pass clears the saved input.
-/

namespace FactorSearchController

/-- The empty input is zero, whose exceptional result is two. -/
theorem start_empty :
    Work (atL .start [] [] [] [] []) (cfg none [false, true] [] [] [] []) 1 := by
  apply workStep <;> first | rfl | decide

/-- The only canonical singleton encodes one. The controller handles either
singleton with the same two-step path. -/
theorem start_singleton (b : Bool) :
    Work (atL .start [b] [] [] [] []) (cfg none [true] [] [] [] []) 2 := by
  have first : Work (atL .start [b] [] [] [] []) (atL .checkSecond [] [b] [b] [] []) 1 := by
    apply workStep <;> first | rfl | decide
  have last : Work (atL .checkSecond [] [b] [b] [] []) (cfg none [true] [] [] [] []) 1 := by
    apply workStep <;> first | rfl | decide
  exact first.trans last

/-- An input of length `L ≥ 2` starts its first comparison round after
`L + 2` transitions, with independent reversed copies of input and fuel. -/
theorem start_long (b c : Bool) (rest : List Bool) :
    Work (atL .start (b :: c :: rest) [] [] [] [])
      (atL .round [] (b :: c :: rest).reverse (b :: c :: rest).reverse [] [])
      ((b :: c :: rest).length + 2) := by
  have first : Work (atL .start (b :: c :: rest) [] [] [] [])
      (atL .checkSecond (c :: rest) [b] [b] [] []) 1 := by
    apply workStep <;> first | rfl | decide
  have second : Work (atL .checkSecond (c :: rest) [b] [b] [] [])
      (atL .saveInput (c :: rest) [b] [b] [] []) 1 := by
    apply workStep <;> first | rfl | decide
  have save := consume (fun xs acc => atL .saveInput xs acc acc [] [])
    (fun acc => atL .round [] acc acc [] [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) (c :: rest) [b]
  convert (first.trans second).trans save using 1 <;>
    simp [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Once fuel runs out, finish with just the canonical prefix on the I/O stack.
The bound charges both passes over the prefix and the final erasure of the input. -/
theorem finish_round (nr high : List Bool) :
    Work (atL .round [] nr [] high []) (cfg none high [] [] [] [])
      (2 * high.length + nr.length + 4) := by
  have enter : Work (atL .round [] nr [] high []) (atL .finishHigh [] nr [] high []) 1 := by
    apply workStep <;> first | rfl | decide
  have stash := consume (fun xs acc => atL .finishHigh [] nr [] xs acc)
    (fun acc => atL .finishOut [] nr [] [] acc)
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) high []
  have output := consume (fun xs acc => atL .finishOut acc nr [] [] xs)
    (fun acc => atL .clearInput acc nr [] [] [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) high.reverse []
  have clear := consume (fun xs _ => atL .clearInput high xs [] [] [])
    (fun _ => cfg none high [] [] [] [])
    (by intros; apply workStep <;> first | rfl | decide)
    (by intros; apply workStep <;> first | rfl | decide) nr []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at stash output
  convert ((enter.trans stash).trans output).trans clear using 1
  omega

end FactorSearchController

/-
# Executing the binary-search controller

Every call contains a canonical pair. The accumulator and the unfinished low
bits together occupy at most as many bits as the original input. This bounds
the query clock as well as the ordinary transitions that prepare each call.
-/

namespace FactorSearchMachine

open Turing Computability ComplexityTheory BitstringEncoding FactorSearchController FactorOracleMachine

abbrev driver : OracleProgram where
  K := Stack
  Λ := Label
  σ := Option Bool
  k₀ := .io
  k₁ := .io
  arg := .io
  main := .start
  call := .ask
  resume := .resume
  initialState := none
  m := program

abbrev Runs (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) :=
  driver.Run (bitEncode (α := ℕ × ℕ)) q P.eval

theorem work_runs {a b t} (hw : Work a b t) (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) :
    Runs q P a b t := by
  induction hw with
  | refl c => exact OracleProgram.Run.refl (C := driver) c
  | one hn hs => exact .normal hn hs
  | trans _ _ hi hj => exact .trans hi hj

private def compareWord (q : ℕ × ℕ → Bool) (w : List Bool) : Bool :=
  ((bitDecode w : Option (ℕ × ℕ)).map q).getD false

private theorem compare_encode (q : ℕ × ℕ → Bool) (x : ℕ × ℕ) :
    compareWord q (bitEncode x) = q x := by simp [compareWord]

private theorem digit_length (b : Bool) (xs : List Bool) :
    (FactorSearchBits.digit b xs).length ≤ xs.length + 1 := by
  cases b <;> cases xs <;> simp [FactorSearchBits.digit]

private theorem result_length (q : List Bool → Bool) (input remaining high : List Bool) :
    (FactorSearchBits.run q input remaining high).length ≤ high.length + remaining.length := by
  induction remaining generalizing high with
  | nil => simp [FactorSearchBits.run]
  | cons v rest ih =>
    simp only [FactorSearchBits.run, List.length_cons]
    exact (ih _).trans (by have := digit_length (!(q (FactorSearchBits.queryWord input rest high))) high; omega)

private def stepBudget (P : Polynomial ℕ) (L : ℕ) := P.eval (3*L+1) + 12*L + 16

private theorem eval_mono (P : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : P.eval a ≤ P.eval b := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial k c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

private theorem doCall (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) (x : ℕ × ℕ)
    (nr fu high : List Bool) :
    Runs q P (atL .ask (bitEncode x) nr fu high [])
      (atL .resume [q x] nr fu high [])
      (P.eval (bitEncode x).length + 2 * (bitEncode x).length + 4) := by
  have hup : Function.update (words (bitEncode x) nr fu high []) .io [q x] =
      words [q x] nr fu high [] := by funext k; cases k <;> rfl
  have h := @OracleProgram.Run.oracle driver _ (bitEncode (α := ℕ × ℕ)) q P.eval x none
    (words (bitEncode x) nr fu high []) rfl
  change Runs q P _ ⟨some Label.resume, none,
    Function.update (words (bitEncode x) nr fu high []) Stack.io [q x]⟩ _ at h
  erw [hup] at h
  exact h

theorem rounds (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) (n : ℕ) (remaining : List Bool) (h : ℕ)
    (cap : remaining.length + (encodeNat h).length ≤ (encodeNat n).length) :
    Runs q P (atL .round [] (encodeNat n).reverse remaining (encodeNat h) [])
      (atL .round [] (encodeNat n).reverse []
        (FactorSearchBits.run (compareWord q) (encodeNat n) remaining (encodeNat h)) [])
      (remaining.length * stepBudget P (encodeNat n).length) := by
  induction remaining generalizing h with
  | nil => simpa [FactorSearchBits.run] using
      (OracleProgram.Run.refl (C := driver) (encode := bitEncode) (query := q) (cost := P.eval)
        (atL .round [] (encodeNat n).reverse [] (encodeNat h) []))
  | cons v rest ih =>
    let input := encodeNat n
    let high := encodeNat h
    let x : ℕ × ℕ := (n, h * 2 ^ (rest.length + 1) + 2 ^ rest.length - 1)
    let w := FactorSearchBits.queryWord input rest high
    have hw : w = bitEncode x := FactorSearchBits.queryWord_encode n rest h
    have ha : compareWord q w = q x := hw ▸ compare_encode q x
    have hnew : FactorSearchBits.digit (!(q x)) high = encodeNat (2*h + (!(q x)).toNat) :=
      FactorSearchBits.digit_encode _ _
    have hcap : rest.length + (encodeNat (2*h + (!(q x)).toNat)).length ≤ input.length := by
      rw [← hnew]
      change rest.length + 1 + high.length ≤ input.length at cap
      have := digit_length (!(q x)) high
      omega
    have hsize : w.length ≤ 3 * input.length + 1 := by
      change rest.length + 1 + high.length ≤ input.length at cap
      have hs := digit_length false high
      simp only [w, FactorSearchBits.queryWord, FactorSearchBits.pivot, List.length_append,
        length_delimit, List.length_map]
      omega
    have hprepare := work_runs (prepareRound input rest high v) q P
    have hcall := doCall q P x input.reverse rest high
    rw [← hw] at hcall
    have hresume := work_runs (resumeRound input.reverse rest high (q x)) q P
    have first := (hprepare.trans hcall).trans hresume
    rw [hnew] at first
    have later := ih (2*h + (!(q x)).toNat) hcap
    have both := first.trans later
    change Runs q P _ (atL .round [] input.reverse []
      (FactorSearchBits.run (compareWord q) input rest (FactorSearchBits.digit (!(compareWord q w)) high)) []) _
    rw [ha, hnew]
    apply both.mono
    change rest.length + 1 + high.length ≤ input.length at cap
    simp only [List.length_cons, Nat.succ_mul]
    change _ ≤ rest.length * stepBudget P input.length + stepBudget P input.length
    have hp := eval_mono P hsize
    dsimp only [stepBudget, input] at *
    omega

private theorem initial (w : List Bool) :
    initList driver.tm w = atL .start w [] [] [] [] := by
  unfold initList atL cfg
  congr 1
  funext k
  cases k <;> rfl

private theorem finalCfg (w : List Bool) :
    haltList driver.tm w = cfg none w [] [] [] [] := by
  unfold haltList cfg
  congr 1
  funext k
  cases k <;> rfl

/-- The controller saves the fuel in reverse order. Its bits are only counted. -/
private theorem run_reverse (q : ℕ × ℕ → Bool) (n : ℕ) :
    FactorSearchBits.run (compareWord q) (encodeNat n) (encodeNat n).reverse [] =
      FactorSearchBits.run (compareWord q) (encodeNat n) (encodeNat n) [] := by
  change FactorSearchBits.run (compareWord q) _ _ (encodeNat 0) =
    FactorSearchBits.run (compareWord q) _ _ (encodeNat 0)
  rw [FactorSearchBits.run_encode _ q (compare_encode q) n (encodeNat n).reverse 0,
    FactorSearchBits.run_encode _ q (compare_encode q) n (encodeNat n) 0, List.length_reverse]

private noncomputable def totalBudget (P : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X * (P.comp (3 * Polynomial.X + 1) + 12 * Polynomial.X + 16) +
    4 * Polynomial.X + 6

private theorem budget_eval (P : Polynomial ℕ) (L : ℕ) :
    (totalBudget P).eval L = L * stepBudget P L + 4*L + 6 := by
  simp [totalBudget, stepBudget]

theorem full_run (q : ℕ × ℕ → Bool) (P : Polynomial ℕ) (n : ℕ) :
    Runs q P (initList driver.tm (encodeNat n))
      (haltList driver.tm (FactorSearchBits.search (compareWord q) (encodeNat n)))
      ((totalBudget P).eval (encodeNat n).length) := by
  rw [initial, finalCfg, budget_eval]
  cases hw : encodeNat n with
  | nil =>
    exact (work_runs start_empty q P).mono (by simp)
  | cons b tail =>
    cases tail with
    | nil =>
      exact (work_runs (start_singleton b) q P).mono (by simp)
    | cons c rest =>
      let input := b :: c :: rest
      let out := FactorSearchBits.run (compareWord q) input input []
      have hbegin := work_runs (start_long b c rest) q P
      have hloop := rounds q P n (encodeNat n).reverse 0 (by simp [show encodeNat 0 = [] from rfl])
      rw [show encodeNat 0 = [] from rfl, run_reverse q n, hw, List.length_reverse] at hloop
      have hfinish := work_runs (finish_round input.reverse out) q P
      have path := (hbegin.trans hloop).trans hfinish
      have hlen : out.length ≤ input.length := by
        simpa using result_length (compareWord q) input input []
      apply path.mono
      change (input.length + 2 + input.length * stepBudget P input.length) +
        (2 * out.length + input.reverse.length + 4) ≤ _
      simp only [List.length_reverse]
      change _ ≤ input.length * stepBudget P input.length + 4 * input.length + 6
      omega

/-- The actual oracle-calling machine realizes the binary search on canonical inputs. -/
theorem search_polytime (q : ℕ × ℕ → Bool) (hq : IsPolyTime q) :
    IsPolyTime (fun n : ℕ =>
      if n < 2 then 2 - n else
      (Nat.rec (motive := fun _ => ℕ → ℕ) id
        (fun i search low => if q (n, low + 2 ^ i - 1) then search low else search (low + 2 ^ i))
        (n.log2 + 1)) 0) := by
  obtain ⟨Q⟩ := hq
  apply FactorOraclePolytime.of_machine driver Q (totalBudget Q.time)
  intro n
  have path := full_run q Q.time n
  rw [FactorSearchBits.search_encode _ q (compare_encode q)] at path
  exact path

end FactorSearchMachine

/-
# Computing the square root by threshold search

For a positive input, the first `b` at which `n / (b + 1) ≤ b` is the floor
square root. The existing binary search thus applies once its division-based
comparison is available in polynomial time. Its exceptional output for zero is
accounted for explicitly.
-/

namespace FactorSqrtBits

open Computability ComplexityTheory

/-- Increment a little-endian natural-number word, propagating the carry until
the first zero or the end of the input. -/
def succWord : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: succWord bs

private theorem succWord_pos (p : PosNum) :
    succWord (encodePosNum p) = encodePosNum p.succ := by
  induction p with
  | one => rfl
  | bit0 p => rfl
  | bit1 p ih => exact congrArg (false :: ·) ih

theorem succWord_encode (n : ℕ) : succWord (encodeNat n) = encodeNat (n + 1) := by
  change succWord (encodeNum (n : Num)) = encodeNum ((n + 1 : ℕ) : Num)
  rw [Nat.cast_succ, Num.add_one]
  cases (n : Num) with
  | zero => rfl
  | pos p => exact succWord_pos p

theorem succWord_length (w : List Bool) : (succWord w).length ≤ w.length + 1 := by
  induction w with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp [succWord]
    omega

/-- A more significant mismatch replaces the result accumulated from lower bits. -/
def leBit (a b state : Bool) : Bool := if a == b then state else !a

/-- Compare two little-endian words in one pass, supplying zeroes beyond the
end of the shorter word. Start with `true` for non-strict comparison. -/
def wordLE : List Bool → List Bool → Bool → Bool
  | [], [], state => state
  | [], b :: bs, state => wordLE [] bs (leBit false b state)
  | a :: as, [], state => wordLE as [] (leBit a false state)
  | a :: as, b :: bs, state => wordLE as bs (leBit a b state)
termination_by as bs _ => as.length + bs.length

private theorem leBit_spec (m n : ℕ) (a b s : Bool) :
    (m < n ∨ m = n ∧ leBit a b s = true) ↔
      2 * m + a.toNat < 2 * n + b.toNat ∨
        2 * m + a.toNat = 2 * n + b.toNat ∧ s = true := by
  cases a <;> cases b <;> cases s <;> simp [leBit] <;> omega

private theorem wordLE_spec (as bs : List Bool) (s : Bool) :
    wordLE as bs s = true ↔
      FactorDivisionBits.value as < FactorDivisionBits.value bs ∨
      FactorDivisionBits.value as = FactorDivisionBits.value bs ∧ s = true := by
  induction as generalizing bs s with
  | nil =>
    induction bs generalizing s with
    | nil => simp [wordLE, FactorDivisionBits.value]
    | cons b bs ih =>
      rw [wordLE, ih]
      simpa only [FactorDivisionBits.value, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
        using leBit_spec 0 (FactorDivisionBits.value bs) false b s
  | cons a as ih =>
    cases bs with
    | nil =>
      rw [wordLE, ih]
      simpa only [FactorDivisionBits.value, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
        using leBit_spec (FactorDivisionBits.value as) 0 a false s
    | cons b bs =>
      rw [wordLE, ih]
      exact leBit_spec _ _ _ _ _

theorem wordLE_encode (x b : ℕ) :
    wordLE (encodeNat x) (encodeNat b) true = decide (x ≤ b) := by
  apply Bool.eq_iff_iff.mpr
  rw [wordLE_spec, decide_eq_true_eq, FactorDivisionBits.value_encodeNat,
    FactorDivisionBits.value_encodeNat]
  simp only [and_true]
  omega

/-- The division-based upper threshold comparison. -/
def sqrtQuery (x : ℕ × ℕ) : Bool := decide (x.1 / (x.2 + 1) ≤ x.2)

theorem query_iff (n b : ℕ) : sqrtQuery (n, b) = true ↔ n.sqrt ≤ b := by
  change decide (n / (b + 1) ≤ b) = true ↔ n.sqrt ≤ b
  rw [decide_eq_true_eq, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (Nat.succ_pos b),
    ← Nat.sqrt_lt, Nat.lt_succ_iff]

private theorem run_sqrt (n k low : ℕ) (hl : low ≤ n.sqrt) (hh : n.sqrt < low + 2 ^ k) :
    (FactorSearchClock.run sqrtQuery n k low).1 = n.sqrt := by
  induction k generalizing low with
  | zero =>
    simp only [FactorSearchClock.run]
    simp only [Nat.pow_zero] at hh
    omega
  | succ i ih =>
    rw [Nat.pow_succ] at hh
    have hp : 0 < 2 ^ i := Nat.pow_pos (by decide)
    change (FactorSearchClock.run sqrtQuery n i (if sqrtQuery (n, low + 2 ^ i - 1)
      then low else low + 2 ^ i)).1 = n.sqrt
    by_cases h : n.sqrt ≤ low + 2 ^ i - 1
    · rw [if_pos ((query_iff _ _).mpr h)]
      exact ih low hl (by omega)
    · rw [if_neg (fun hq => h ((query_iff _ _).mp hq))]
      exact ih _ (by omega) (by omega)

/-- On positive inputs the guarded search returns the exact square root. -/
theorem search_eq (n : ℕ) (hn : n ≠ 0) :
    (FactorSearchClock.search sqrtQuery n).1 = n.sqrt := by
  by_cases hs : n < 2
  · have : n = 1 := by omega
    subst n
    rfl
  · rw [FactorSearchClock.search, if_neg hs]
    apply run_sqrt _ _ _ (Nat.zero_le _)
    simpa only [Nat.zero_add] using (Nat.sqrt_le_self n).trans_lt Nat.lt_log2_self

/-- The guard for zero recovers the square root on every input. -/
theorem search_guarded (n : ℕ) :
    (if n = 0 then 0 else (FactorSearchClock.search sqrtQuery n).1) = n.sqrt := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, search_eq n hn]

/-- The polynomial-time search driver realizes this total function. In the
outer factor comparison only positive inputs require a square-root call. -/
theorem search_polytime (hq : IsPolyTime sqrtQuery) :
    IsPolyTime (fun n : ℕ => if n = 0 then 2 else n.sqrt) := by
  have h := FactorSearchMachine.search_polytime sqrtQuery hq
  refine (congrArg (fun f : ℕ → ℕ => IsPolyTime f) ?_).mp h
  funext n
  rw [← FactorSearchClock.search_value]
  by_cases hn : n = 0
  · subst n
    rfl
  · simp only [if_neg hn, search_eq n hn]

/-- The guarded-comparison controller needs the square root only on inputs at
least three. The existing search machine already meets that interface. -/
theorem exists_sqrt (hq : IsPolyTime sqrtQuery) :
    ∃ s : ℕ → ℕ, IsPolyTime s ∧ ∀ n, 3 ≤ n → s n = n.sqrt := by
  refine ⟨fun n => if n = 0 then 2 else n.sqrt, search_polytime hq, ?_⟩
  intro n hn
  simp [show n ≠ 0 by omega]

end FactorSqrtBits

/- Interface for the two-input binary quotient routine inside factor extraction. -/

namespace FactorQuotientSpec

open Turing Computability

/-- Both arguments are little-endian natural number encodings. The quotient
replaces the numerator. The denominator and all private working stacks are
empty when the subroutine finishes. -/
structure Routine where
  K : Type
  [kDec : DecidableEq K]
  [kFin : Fintype K]
  Λ : Type
  [lDec : DecidableEq Λ]
  [lFin : Fintype Λ]
  σ : Type
  [sFin : Fintype σ]
  numerator : K
  denominator : K
  separate : numerator ≠ denominator
  entry : Λ
  initial : σ
  code : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

instance (D : Routine) : DecidableEq D.K := D.kDec
instance (D : Routine) : Fintype D.K := D.kFin
instance (D : Routine) : DecidableEq D.Λ := D.lDec
instance (D : Routine) : Fintype D.Λ := D.lFin
instance (D : Routine) : Fintype D.σ := D.sFin

namespace Routine

variable (D : Routine)

abbrev Cfg := TM2.Cfg (fun _ : D.K => Bool) D.Λ D.σ

/-- Denominator and numerator words in the otherwise empty division block. -/
def inputs (x y : List Bool) (k : D.K) : List Bool :=
  if k = D.numerator then x else if k = D.denominator then y else []

def beginCfg (x y : ℕ) : D.Cfg :=
  ⟨some D.entry, D.initial, D.inputs (encodeNat x) (encodeNat y)⟩

def endCfg (x y : ℕ) : D.Cfg :=
  ⟨none, D.initial, D.inputs (encodeNat (x / y)) []⟩

def CorrectIn (P : Polynomial ℕ) : Prop :=
  ∀ x y : ℕ, Nonempty (StateTransition.EvalsToInTime (TM2.step D.code)
    (D.beginCfg x y) (some (D.endCfg x y))
    (P.eval ((encodeNat x).length + (encodeNat y).length)))

end Routine
end FactorQuotientSpec

/- Restoring binary long division on finite Bool stacks. The input is reversed
once. Each round tries one subtraction, restores the divisor, and outputs one bit. -/

namespace FactorDivisionController

open Turing.TM2

inductive Stack
  | num | den | bits | rem | savedDen | savedRem | diff
  deriving DecidableEq

inductive Label
  | start | zero | reverseIn | readBit | subtract (borrow : Bool)
  | reject | restoreRem | clearDiff | accept | trim | writeRem | clearSaved
  | restoreDen | clearDen | clearRem
  deriving DecidableEq

instance : Fintype Stack := Fintype.ofList
  [.num, .den, .bits, .rem, .savedDen, .savedRem, .diff] (by intro k; cases k <;> decide)

instance : Fintype Label := Fintype.ofList
  [.start, .zero, .reverseIn, .readBit, .subtract false, .subtract true,
   .reject, .restoreRem, .clearDiff, .accept, .trim, .writeRem, .clearSaved,
   .restoreDen, .clearDen, .clearRem]
  (by intro l; cases l <;> first | decide | (rename_i borrow; cases borrow <;> decide))

abbrev Reg := Option Bool × Option Bool
abbrev Code := Stmt (fun _ : Stack => Bool) Label Reg
abbrev Config := Cfg (fun _ : Stack => Bool) Label Reg

private def go (l : Label) : Code := .load (fun _ => (none, none)) (.goto (fun _ => l))
private def stop : Code := .load (fun _ => (none, none)) .halt
private def put (k : Stack) (b : Bool) (q : Code) : Code := .push k (fun _ => b) q
private def bit₁ (r : Reg) : Bool := r.1.getD false
private def bit₂ (r : Reg) : Bool := r.2.getD false
private def pop (k : Stack) (item empty : Code) : Code :=
  .pop k (fun _ v => (v, none)) (.branch (fun r => r.1.isSome) item empty)
private def peek (k : Stack) (item empty : Code) : Code :=
  .peek k (fun _ v => (v, none)) (.branch (fun r => r.1.isSome) item empty)
private def skip (k : Stack) (q : Code) : Code := .pop k (fun r _ => r) q
private def transfer (from_ to_ : Stack) (again next : Label) : Code :=
  pop from_ (.push to_ bit₁ (go again)) (go next)

private def subtractBit (borrow : Bool) : Code :=
  let calculate := .push Stack.diff (fun r => FactorDivisionBits.diffBit (bit₁ r) (bit₂ r) borrow)
    (.branch (fun r => FactorDivisionBits.borrowBit (bit₁ r) (bit₂ r) borrow)
      (go (.subtract true)) (go (.subtract false)))
  .push .savedRem bit₁ (.pop .den (fun r v => (r.1, v))
    (.branch (fun r => r.2.isSome) (.push .savedDen bit₂ calculate) calculate))

def program : Label → Code
  | .start => peek .den (go .reverseIn) (go .zero)
  | .zero => pop .num (go .zero) stop
  | .reverseIn => transfer .num .bits .reverseIn .readBit
  | .readBit => pop .bits
      (.branch bit₁ (put .rem true (go (.subtract false)))
        (peek .rem (put .rem false (go (.subtract false))) (go (.subtract false))))
      (go .clearDen)
  | .subtract borrow => pop .rem (subtractBit borrow)
      (if borrow then go .reject else peek .den (go .reject) (go .accept))
  | .reject => peek .num (put .num false (go .restoreRem)) (go .restoreRem)
  | .restoreRem => transfer .savedRem .rem .restoreRem .clearDiff
  | .clearDiff => pop .diff (go .clearDiff) (go .restoreDen)
  | .accept => put .num true (go .trim)
  | .trim => peek .diff (.branch bit₁ (go .writeRem) (skip .diff (go .trim))) (go .writeRem)
  | .writeRem => transfer .diff .rem .writeRem .clearSaved
  | .clearSaved => pop .savedRem (go .clearSaved) (go .restoreDen)
  | .restoreDen => transfer .savedDen .den .restoreDen .readBit
  | .clearDen => pop .den (go .clearDen) (go .clearRem)
  | .clearRem => pop .rem (go .clearRem) stop

def division : FactorQuotientSpec.Routine where
  K := Stack
  Λ := Label
  σ := Reg
  numerator := .num
  denominator := .den
  separate := by decide
  entry := .start
  initial := (none, none)
  code := program

def words (num den bits rem savedDen savedRem diff : List Bool) : Stack → List Bool
  | .num => num
  | .den => den
  | .bits => bits
  | .rem => rem
  | .savedDen => savedDen
  | .savedRem => savedRem
  | .diff => diff

def cfg (l : Option Label) (num den bits rem sd sr df : List Bool) : Config :=
  ⟨l, (none, none), words num den bits rem sd sr df⟩
abbrev atL (l : Label) := cfg (some l)

inductive Work : Config → Config → ℕ → Prop
  | refl (c) : Work c c 0
  | one {c d} : step program c = some d → Work c d 1
  | trans {a b c t u} : Work a b t → Work b c u → Work a c (t + u)
  | mono {a b t u} : Work a b t → t ≤ u → Work a b u

private theorem workStep {l n d bs r sd sr df dest}
    (hl : (stepAux (program l) (none,none) (words n d bs r sd sr df)).l = dest.l)
    (hv : (stepAux (program l) (none,none) (words n d bs r sd sr df)).var = dest.var)
    (hs : ∀ k, (stepAux (program l) (none,none) (words n d bs r sd sr df)).stk k = dest.stk k) :
    Work (atL l n d bs r sd sr df) dest 1 := by
  apply Work.one
  apply congrArg some
  change stepAux _ _ _ = dest
  have hstk := funext hs
  cases ha : stepAux (program l) (none,none) (words n d bs r sd sr df) with
  | mk L V S =>
    rw [ha] at hl hv hstk
    cases dest
    congr

private theorem consume (stage : List Bool → List Bool → Config) (finish : List Bool → Config)
    (next : ∀ b xs acc, Work (stage (b :: xs) acc) (stage xs (b :: acc)) 1)
    (done_ : ∀ acc, Work (stage [] acc) (finish acc) 1)
    (xs acc : List Bool) : Work (stage xs acc) (finish (xs.reverse ++ acc)) (xs.length + 1) := by
  induction xs generalizing acc with
  | nil => simpa using done_ acc
  | cons b xs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm 1 (xs.length + 1)] using
      (next b xs acc).trans (ih (b :: acc))

private theorem clear (stage : List Bool → Config) (finish : Config)
    (next : ∀ b xs, Work (stage (b :: xs)) (stage xs) 1)
    (done_ : Work (stage []) finish 1)
    (xs : List Bool) : Work (stage xs) finish (xs.length + 1) := by
  have h := consume (fun xs _ => stage xs) (fun _ => finish)
    (fun b xs _ => next b xs) (fun _ => done_) xs []
  exact h

theorem initNonzero (x : List Bool) (d : Bool) (ds : List Bool) :
    Work (atL .start x (d :: ds) [] [] [] [] [])
      (atL .readBit [] (d :: ds) x.reverse [] [] [] []) (x.length + 2) := by
  have a : Work (atL .start x (d :: ds) [] [] [] [] [])
      (atL .reverseIn x (d :: ds) [] [] [] [] []) 1 := by
    apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have b := consume (fun xs acc => atL .reverseIn xs (d :: ds) acc [] [] [] [])
    (fun acc => atL .readBit [] (d :: ds) acc [] [] [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) x []
  simpa [Nat.add_comm 1 (x.length + 1)] using a.trans b

theorem initZero (x : List Bool) :
    Work (atL .start x [] [] [] [] [] []) (cfg none [] [] [] [] [] [] []) (x.length + 2) := by
  have a : Work (atL .start x [] [] [] [] [] []) (atL .zero x [] [] [] [] [] []) 1 := by
    apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have b := clear (fun xs => atL .zero xs [] [] [] [] [] []) (cfg none [] [] [] [] [] [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) x
  simpa [Nat.add_comm 1 (x.length + 1)] using a.trans b

theorem finishPath (q d r : List Bool) :
    Work (atL .readBit q d [] r [] [] []) (cfg none q [] [] [] [] [] [])
      (d.length + r.length + 3) := by
  have a : Work (atL .readBit q d [] r [] [] []) (atL .clearDen q d [] r [] [] []) 1 := by
    apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have b := clear (fun xs => atL .clearDen q xs [] r [] [] [])
    (atL .clearRem q [] [] r [] [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) d
  have c := clear (fun xs => atL .clearRem q [] [] xs [] [] [])
    (cfg none q [] [] [] [] [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) r
  convert (a.trans b).trans c using 1
  omega

private theorem subtractRun (q bs u : List Bool) (d : List Bool) (borrow : Bool) (sd sr df : List Bool) :
    Work (atL (.subtract borrow) q d bs u sd sr df)
      (atL (cond (FactorDivisionBits.trial u d borrow).1 .reject .accept)
        q (d.drop u.length) bs [] ((d.take u.length).reverse ++ sd)
        (u.reverse ++ sr) ((FactorDivisionBits.trial u d borrow).2.reverse ++ df)) (u.length + 1) := by
  induction u generalizing d borrow sd sr df with
  | nil =>
    cases d <;> cases borrow <;> apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  | cons a u ih =>
    cases d with
    | nil =>
      let c := FactorDivisionBits.borrowBit a false borrow
      let z := FactorDivisionBits.diffBit a false borrow
      have h : Work (atL (.subtract borrow) q [] bs (a :: u) sd sr df)
          (atL (.subtract c) q [] bs u sd (a :: sr) (z :: df)) 1 := by
        cases a <;> cases borrow <;> apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
      simpa [FactorDivisionBits.trial, c, z, List.reverse_cons, List.append_assoc,
        Nat.add_comm 1 (u.length + 1)] using h.trans (ih [] c sd (a :: sr) (z :: df))
    | cons y ys =>
      let c := FactorDivisionBits.borrowBit a y borrow
      let z := FactorDivisionBits.diffBit a y borrow
      have h : Work (atL (.subtract borrow) q (y :: ys) bs (a :: u) sd sr df)
          (atL (.subtract c) q ys bs u (y :: sd) (a :: sr) (z :: df)) 1 := by
        cases a <;> cases y <;> cases borrow <;> apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
      simpa [FactorDivisionBits.trial, c, z, List.reverse_cons, List.append_assoc,
        Nat.add_comm 1 (u.length + 1)] using h.trans (ih ys c (y :: sd) (a :: sr) (z :: df))

private theorem trimPath (q d bs sd sr df : List Bool) :
    Work (atL .trim q d bs [] sd sr df)
      (atL .writeRem q d bs [] sd sr (df.dropWhile (!·))) (df.length + 1) := by
  induction df with
  | nil => apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  | cons b df ih =>
    cases b with
    | false =>
      have h : Work (atL .trim q d bs [] sd sr (false :: df))
          (atL .trim q d bs [] sd sr df) 1 := by
        apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
      simpa [List.dropWhile, Nat.add_comm 1 (df.length + 1)] using h.trans ih
    | true =>
      have h : Work (atL .trim q d bs [] sd sr (true :: df))
          (atL .writeRem q d bs [] sd sr (true :: df)) 1 := by
        apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
      exact h.mono (by simp)

private theorem restoreDenPath (q d bs r sd : List Bool) :
    Work (atL .restoreDen q d bs r sd [] [])
      (atL .readBit q (sd.reverse ++ d) bs r [] [] []) (sd.length + 1) := by
  exact consume (fun xs acc => atL .restoreDen q acc bs r xs [] [])
    (fun acc => atL .readBit q acc bs r [] [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) sd d

private theorem rejectPath (q d bs sd sr df : List Bool) :
    Work (atL .reject q d bs [] sd sr df)
      (atL .readBit (FactorSearchBits.digit false q) (sd.reverse ++ d) bs sr.reverse [] [] [])
      (sr.length + df.length + sd.length + 4) := by
  let out := FactorSearchBits.digit false q
  have a : Work (atL .reject q d bs [] sd sr df) (atL .restoreRem out d bs [] sd sr df) 1 := by
    cases q <;> apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have b := consume (fun xs acc => atL .restoreRem out d bs acc sd xs df)
    (fun acc => atL .clearDiff out d bs acc sd [] df)
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) sr []
  have c := clear (fun xs => atL .clearDiff out d bs sr.reverse sd [] xs)
    (atL .restoreDen out d bs sr.reverse sd [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) df
  simp only [List.append_nil] at b
  convert ((a.trans b).trans c).trans (restoreDenPath out d bs sr.reverse sd) using 1
  omega

private theorem acceptPath (q d bs sd sr df : List Bool) :
    Work (atL .accept q d bs [] sd sr df)
      (atL .readBit (true :: q) (sd.reverse ++ d) bs (df.dropWhile (!·)).reverse [] [] [])
      (2 * df.length + sr.length + sd.length + 5) := by
  let out := true :: q
  let trimmed := df.dropWhile (!·)
  have a : Work (atL .accept q d bs [] sd sr df) (atL .trim out d bs [] sd sr df) 1 := by
    apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have b := trimPath out d bs sd sr df
  have c := consume (fun xs acc => atL .writeRem out d bs acc sd sr xs)
    (fun acc => atL .clearSaved out d bs acc sd sr [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) trimmed []
  simp only [List.append_nil] at c
  have e := clear (fun xs => atL .clearSaved out d bs trimmed.reverse sd xs [])
    (atL .restoreDen out d bs trimmed.reverse sd [] [])
    (by intros; apply workStep <;> first | rfl | (intro k; cases k <;> rfl))
    (by apply workStep <;> first | rfl | (intro k; cases k <;> rfl)) sr
  apply ((((a.trans b).trans c).trans e).trans (restoreDenPath out d bs trimmed.reverse sd)).mono
  have hlen : trimmed.length ≤ df.length := (List.dropWhile_sublist (l := df) (!·)).length_le
  omega

/-- Process one numerator bit. Trial subtraction and restoration inspect no more
denominator bits than there are bits of the shifted remainder. -/
theorem roundStep (q d bs r : List Bool) (b : Bool) :
    Work (atL .readBit q d (b :: bs) r [] [] [])
      (atL .readBit (FactorDivisionBits.divisionStep d (q, r) b).1 d bs
        (FactorDivisionBits.divisionStep d (q, r) b).2 [] [] [])
      (6 * (r.length + 1) + 10) := by
  let u := FactorSearchBits.digit b r
  let lhs := FactorDivisionBits.trial u d false
  have a : Work (atL .readBit q d (b :: bs) r [] [] [])
      (atL (.subtract false) q d bs u [] [] []) 1 := by
    cases b <;> cases r <;> apply workStep <;> first | rfl | (intro k; cases k <;> rfl)
  have sub := subtractRun q bs u d false [] [] []
  simp only [List.append_nil] at sub
  change Work _ (atL (cond lhs.1 .reject .accept) q (d.drop u.length) bs []
    (d.take u.length).reverse u.reverse lhs.2.reverse) _ at sub
  have hu : u.length ≤ r.length + 1 := FactorDivisionBits.digit_length b r
  have hraw : lhs.2.length = u.length := FactorDivisionBits.trial_length u d false
  have htake : (d.take u.length).length ≤ u.length := List.length_take_le ..
  change Work _ (atL .readBit (FactorSearchBits.digit (!lhs.1) q) d bs
    (if lhs.1 then u else FactorDivisionBits.trim lhs.2) [] [] []) _
  cases hb : lhs.1 with
  | false =>
    rw [hb] at sub
    have h := acceptPath q (d.drop u.length) bs (d.take u.length).reverse u.reverse lhs.2.reverse
    simp only [List.reverse_reverse, List.take_append_drop, List.length_reverse] at h
    exact ((a.trans sub).trans h).mono (by omega)
  | true =>
    rw [hb] at sub
    have h := rejectPath q (d.drop u.length) bs (d.take u.length).reverse u.reverse lhs.2.reverse
    simp only [List.reverse_reverse, List.take_append_drop, List.length_reverse] at h
    exact ((a.trans sub).trans h).mono (by omega)

end FactorDivisionController

/- A quadratic clock for finite-stack binary long division, in the sum of both input lengths. -/

namespace FactorDivisionTime

open FactorDivisionBits FactorDivisionController FactorQuotientSpec Computability Turing

theorem work_to_evals {a b : Config} {t : ℕ} (h : Work a b t) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program) a (some b) t) := by
  induction h with
  | refl c => exact ⟨StateTransition.EvalsToInTime.refl _ _⟩
  | one hs => exact ⟨⟨⟨1, hs⟩, Nat.le_refl _⟩⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨u⟩ := ih₁
    obtain ⟨v⟩ := ih₂
    exact ⟨⟨u.toEvalsTo.trans _ _ _ _ v.toEvalsTo, by
      dsimp [StateTransition.EvalsTo.trans]
      have := u.steps_le_m
      have := v.steps_le_m
      omega⟩⟩
  | mono _ hle ih =>
    obtain ⟨u⟩ := ih
    exact ⟨⟨u.toEvalsTo, u.steps_le_m.trans hle⟩⟩

noncomputable def divisionClock : Polynomial ℕ := 6 * Polynomial.X ^ 2 + 19 * Polynomial.X + 5

private theorem run_rounds (d bs : List Bool) (qr : List Bool × List Bool) (L : ℕ)
    (hsize : qr.2.length + bs.length ≤ L) :
    Work (atL .readBit qr.1 d bs qr.2 [] [] [])
      (atL .readBit (bs.foldl (divisionStep d) qr).1 d [] (bs.foldl (divisionStep d) qr).2 [] [] [])
      (bs.length * (6*(L+1)+10)) ∧ (bs.foldl (divisionStep d) qr).2.length ≤ L := by
  induction bs generalizing qr with
  | nil => exact ⟨by simpa using Work.refl (atL .readBit qr.1 d [] qr.2 [] [] []), by simpa using hsize⟩
  | cons b bs ih =>
    have hnew := (divisionStep_lengths d qr b).2
    simp only [List.length_cons] at hsize
    obtain ⟨hrest, hend⟩ := ih (divisionStep d qr b) (by omega)
    refine ⟨((roundStep qr.1 d bs qr.2 b).trans hrest).mono ?_, hend⟩
    simp only [List.length_cons, Nat.succ_mul]
    omega

private theorem clock_arith (L D R : ℕ) (hR : R ≤ L) :
    L + 2 + L * (6 * (L + 1) + 10) + (D + R + 3) ≤ divisionClock.eval (L+D) := by
  have hL : L ≤ L+D := by omega
  have hD : D ≤ L+D := by omega
  calc
    _ ≤ (L+D) + 2 + (L+D) * (6 * ((L+D) + 1) + 10) + (2 * (L+D) + 3) := by
      apply Nat.add_le_add
      · apply Nat.add_le_add (by omega)
        exact Nat.mul_le_mul hL (by omega)
      · omega
    _ = _ := by simp [divisionClock]; ring

private theorem divide_words (x den : List Bool) : Work
    (atL .start x den [] [] [] [] []) (cfg none (divide x den) [] [] [] [] [] [])
    (divisionClock.eval (x.length+den.length)) := by
  cases den with
  | nil =>
    apply (initZero x).mono
    simp [divisionClock]
    omega
  | cons d ds =>
    let den := d :: ds
    obtain ⟨hr, hlen⟩ := run_rounds den x.reverse ([], []) x.length (by simp)
    rw [List.length_reverse] at hr
    let finalState := x.reverse.foldl (divisionStep den) ([], [])
    have h := ((initNonzero x d ds).trans hr).trans (finishPath finalState.1 den finalState.2)
    exact h.mono (clock_arith x.length den.length finalState.2.length hlen)

private theorem start_cfg (x y : ℕ) : division.beginCfg x y = atL .start (encodeNat x) (encodeNat y) [] [] [] [] [] := by
  apply congrArg (fun s => (⟨some Label.start, (none,none), s⟩ : Config))
  funext k
  cases k <;> rfl

private theorem stop_cfg (x y : ℕ) : division.endCfg x y = cfg none (encodeNat (x/y)) [] [] [] [] [] [] := by
  apply congrArg (fun s => (⟨none, (none,none), s⟩ : Config))
  funext k
  cases k <;> rfl

/-- On natural number inputs the finite machine returns the encoded quotient, including at a zero divisor. -/
theorem division_correct : division.CorrectIn divisionClock := by
  intro x y
  have h := divide_words (encodeNat x) (encodeNat y)
  rw [divide_encode] at h
  rw [start_cfg, stop_cfg]
  exact work_to_evals h

/-- Polynomial-time witness for embedding the quotient subroutine. -/
theorem exists_clock : ∃ P : Polynomial ℕ, division.CorrectIn P := ⟨divisionClock, division_correct⟩

end FactorDivisionTime

/- An ordinary finite-stack machine for the square-root comparison
`n / (b + 1) ≤ b`. It separates the encoded pair, increments the denominator,
runs the binary division block, and compares the quotient with the saved bound. -/

namespace FactorSqrtMachine

open Turing Computability ComplexityTheory BitstringEncoding FactorMachineLift FactorSqrtBits

inductive Stage | parse | restoreNum | inc (carry : Bool) | restoreDen | restoreBound | cmp (le : Bool)
  deriving DecidableEq

instance : Fintype Stage := Fintype.ofList
  [.parse, .restoreNum, .inc true, .inc false, .restoreDen, .restoreBound, .cmp true, .cmp false]
  (by intro t; cases t <;> first | decide | (rename_i b; cases b <;> decide))

abbrev Key := FactorDivisionController.Stack ⊕ Unit
abbrev Lab := Stage ⊕ FactorDivisionController.Label
abbrev Reg := FactorDivisionController.Reg
abbrev Code := TM2.Stmt (fun _ : Key => Bool) Lab Reg
abbrev Config := TM2.Cfg (fun _ : Key => Bool) Lab Reg

private abbrev io : Key := .inr ()
private abbrev numerator : Key := .inl .num
private abbrev denominator : Key := .inl .den
private abbrev saved : Key := .inl .savedRem
private abbrev scratch : Key := .inl .diff

def inner : Lift (fun _ : FactorDivisionController.Stack => Bool) (fun _ : Key => Bool)
    FactorDivisionController.Label Lab Reg Reg where
  stack := ⟨Sum.inl, Sum.inl_injective⟩
  symbol _ := Equiv.refl _
  label := Sum.inr
  exitLabel := some (.inl (.cmp true))
  read := id
  write _ v := v
  read_write _ _ := rfl
  write_write _ _ _ := rfl

private def go (l : Lab) : Code := .load (fun _ => (none,none)) (.goto (fun _ => l))
private def jump (l : Stage) : Code := go (.inl l)
private def stop : Code := .load (fun _ => (none,none)) .halt
private def put (k : Key) (b : Bool) (q : Code) : Code := .push k (fun _ => b) q
private def bit₁ (r : Reg) : Bool := r.1.getD false
private def bit₂ (r : Reg) : Bool := r.2.getD false
private def take (k : Key) (item empty : Code) : Code :=
  .pop k (fun _ x => (x, none)) (.branch (fun r => r.1.isSome) item empty)
private def transfer (a b : Key) (again : Stage) (done_ : Lab) : Code :=
  take a (.push b bit₁ (jump again)) (go done_)

def stageCode : Stage → Code
  | .parse => take io (.branch bit₁
      (take io (.push saved bit₁ (jump .parse)) stop) (jump .restoreNum)) stop
  | .restoreNum => transfer saved numerator .restoreNum (.inl (.inc true))
  | .inc carry => take io (.push saved bit₁ (.push scratch (fun r => xor (bit₁ r) carry)
      (.branch (fun r => carry && bit₁ r) (jump (.inc true)) (jump (.inc false)))))
      (if carry then put scratch true (jump .restoreDen) else jump .restoreDen)
  | .restoreDen => transfer scratch denominator .restoreDen (.inl .restoreBound)
  | .restoreBound => transfer saved io .restoreBound (.inr .start)
  | .cmp prev => .pop numerator (fun _ x => (x, none)) (.pop io (fun r x => (r.1, x))
      (.branch (fun r => r.1.isSome || r.2.isSome)
        (.branch (fun r => leBit (bit₁ r) (bit₂ r) prev)
          (jump (.cmp true)) (jump (.cmp false))) (put io prev stop)))

def program : Lab → Code := Sum.elim stageCode (fun l => inner.stmt (FactorDivisionController.program l))

def machine : FinTM2 where
  K := Key
  Γ _ := Bool
  Λ := Lab
  σ := Reg
  k₀ := io
  k₁ := io
  main := .inl .parse
  initialState := (none,none)
  m := program

private def tapes (w n d r t : List Bool) : Key → List Bool :=
  Sum.elim (FactorDivisionController.words n d [] [] [] r t) (fun _ => w)

private def cfg (l : Option Lab) (w n d r t : List Bool) : Config :=
  ⟨l, (none,none), tapes w n d r t⟩

private abbrev atL (l : Stage) := cfg (some (.inl l))

private def Path (a b : Config) (t : ℕ) : Prop :=
  Nonempty (StateTransition.EvalsToInTime (TM2.step program) a (some b) t)

private theorem Path.trans {a b c t u} (h : Path a b t) (g : Path b c u) : Path a c (t+u) := by
  obtain ⟨h⟩ := h
  obtain ⟨g⟩ := g
  exact ⟨Nat.add_comm u t ▸ StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h g⟩

private theorem Path.mono {a b t u} (h : Path a b t) (ht : t ≤ u) : Path a b u := by
  obtain ⟨h⟩ := h
  exact ⟨⟨h.toEvalsTo, h.steps_le_m.trans ht⟩⟩

private theorem stepAt {l w n d r t dest}
    (hl : (TM2.stepAux (stageCode l) (none,none) (tapes w n d r t)).l = dest.l)
    (hv : (TM2.stepAux (stageCode l) (none,none) (tapes w n d r t)).var = dest.var)
    (hs : ∀ k, (TM2.stepAux (stageCode l) (none,none) (tapes w n d r t)).stk k = dest.stk k) :
    Path (atL l w n d r t) dest 1 := by
  refine ⟨⟨⟨1, ?_⟩, Nat.le_refl _⟩⟩
  apply congrArg some
  change TM2.stepAux (stageCode l) _ _ = dest
  have hstk := funext hs
  cases ha : TM2.stepAux (stageCode l) (none,none) (tapes w n d r t) with
  | mk L V S =>
    rw [ha] at hl hv hstk
    cases dest
    congr

private theorem consume (stage : List Bool → List Bool → Config) (finish : List Bool → Config)
    (next : ∀ b xs acc, Path (stage (b :: xs) acc) (stage xs (b :: acc)) 1)
    (done_ : ∀ acc, Path (stage [] acc) (finish acc) 1)
    (xs acc : List Bool) : Path (stage xs acc) (finish (xs.reverse ++ acc)) (xs.length + 1) := by
  induction xs generalizing acc with
  | nil => simpa using done_ acc
  | cons b xs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm 1 (xs.length + 1)] using
      (next b xs acc).trans (ih (b :: acc))

private theorem incPath (n b : List Bool) (carry : Bool) (s t : List Bool) :
    Path (atL (.inc carry) b n [] s t)
      (atL .restoreDen [] n [] (b.reverse ++ s) ((if carry then succWord b else b).reverse ++ t))
      (b.length + 1) := by
  induction b generalizing carry s t with
  | nil =>
    cases carry <;> apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl)
  | cons x bs ih =>
    have a : Path (atL (.inc carry) (x :: bs) n [] s t)
        (atL (.inc (carry && x)) bs n [] (x :: s) ((xor x carry) :: t)) 1 := by
      cases carry <;> cases x <;> apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl)
    have h := a.trans (ih (carry && x) (x :: s) ((xor x carry) :: t))
    cases carry <;> cases x <;>
      simpa [succWord, List.reverse_cons, List.append_assoc, Nat.add_comm 1 (bs.length+1)] using h

private theorem prepare (n b : List Bool) :
    Path (atL .parse (delimit n ++ b) [] [] [] [])
      (cfg (some (.inr .start)) b n (succWord b) [] [])
      (2*n.length + 2*b.length + (succWord b).length + 5) := by
  have a := consume (fun xs acc => atL .parse (delimit xs ++ b) [] [] acc [])
    (fun acc => atL .restoreNum b [] [] acc [])
    (by intros; apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl))
    (by intros; apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl)) n []
  have g := consume (fun xs acc => atL .restoreNum b acc [] xs [])
    (fun acc => atL (.inc true) b acc [] [] [])
    (by intros; apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl))
    (by intros; apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl)) n.reverse []
  have c := incPath n b true [] []
  have d := consume (fun xs acc => atL .restoreDen [] n acc b.reverse xs)
    (fun acc => atL .restoreBound [] n acc b.reverse [])
    (by intros; apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl))
    (by intros; apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl)) (succWord b).reverse []
  have e := consume (fun xs acc => atL .restoreBound acc n (succWord b) xs [])
    (fun acc => cfg (some (.inr .start)) acc n (succWord b) [] [])
    (by intros; apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl))
    (by intros; apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl)) b.reverse []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse, if_true] at a g c d e
  convert (((a.trans g).trans c).trans d).trans e using 1
  omega

private theorem comparePath (a b : List Bool) (s : Bool) :
    Path (atL (.cmp s) b a [] [] []) (cfg none [wordLE a b s] [] [] [] []) (a.length+b.length+1) := by
  cases a with
  | nil =>
    cases b with
    | nil => rw [wordLE]; apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl)
    | cons v vs =>
      let t := leBit false v s
      have step : Path (atL (.cmp s) (v :: vs) [] [] [] []) (atL (.cmp t) vs [] [] [] []) 1 := by
        cases s <;> cases v <;> apply stepAt <;> first | rfl | (rintro (k | u); cases k <;> rfl; cases u; rfl)
      rw [wordLE]
      apply (step.trans (comparePath [] vs t)).mono
      simp; omega
  | cons u us =>
    cases b with
    | nil =>
      let t := leBit u false s
      have step : Path (atL (.cmp s) [] (u :: us) [] [] []) (atL (.cmp t) [] us [] [] []) 1 := by
        cases s <;> cases u <;> apply stepAt <;> first | rfl | (rintro (k | v); cases k <;> rfl; cases v; rfl)
      rw [wordLE]
      apply (step.trans (comparePath us [] t)).mono
      simp; omega
    | cons v vs =>
      let t := leBit u v s
      have step : Path (atL (.cmp s) (v :: vs) (u :: us) [] [] []) (atL (.cmp t) vs us [] [] []) 1 := by
        cases u <;> cases v <;> cases s <;> apply stepAt <;> first | rfl | (rintro (k | z); cases k <;> rfl; cases z; rfl)
      rw [wordLE]
      apply (step.trans (comparePath us vs t)).mono
      simp; omega
termination_by a.length + b.length

private theorem dividePath (x y : ℕ) (w : List Bool) :
    Path (cfg (some (.inr .start)) w (encodeNat x) (encodeNat y) [] [])
      (atL (.cmp true) w (encodeNat (x / y)) [] [] [])
      (FactorDivisionTime.divisionClock.eval ((encodeNat x).length + (encodeNat y).length)) := by
  obtain ⟨run⟩ := FactorDivisionTime.division_correct x y
  let frozen := tapes w [] [] [] []
  let base : Reg := (none,none)
  have head : inner.Matches base frozen (FactorDivisionController.division.beginCfg x y)
      (cfg (some (.inr .start)) w (encodeNat x) (encodeNat y) [] []) := by
    refine ⟨rfl, rfl, ⟨?_, ?_⟩⟩
    · intro k
      change FactorDivisionController.words (encodeNat x) (encodeNat y) [] [] [] [] [] k =
        (FactorDivisionController.division.inputs (encodeNat x) (encodeNat y) k).map id
      rw [List.map_id]; cases k <;> rfl
    · rintro (k | u) hk
      · exact False.elim (hk k rfl)
      · rfl
  have tail : inner.Matches base frozen (FactorDivisionController.division.endCfg x y)
      (atL (.cmp true) w (encodeNat (x/y)) [] [] []) := by
    refine ⟨rfl, rfl, ⟨?_, ?_⟩⟩
    · intro k
      change FactorDivisionController.words (encodeNat (x/y)) [] [] [] [] [] [] k =
        (FactorDivisionController.division.inputs (encodeNat (x/y)) [] k).map id
      rw [List.map_id]; cases k <;> rfl
    · rintro (k | u) hk
      · exact False.elim (hk k rfl)
      · rfl
  exact ⟨inner.evalsToInTime (p := FactorDivisionController.program) (P := program)
    (fun _ => rfl) head tail run⟩

private noncomputable def clock : Polynomial ℕ := FactorDivisionTime.divisionClock + 8*Polynomial.X + 12

private theorem path (n b : ℕ) :
    Path (atL .parse (bitEncode (n,b)) [] [] [] []) (cfg none [sqrtQuery (n,b)] [] [] [] [])
      (clock.eval (bitEncode (n,b)).length) := by
  have prep := prepare (encodeNat n) (encodeNat b)
  have divi := dividePath n (b+1) (encodeNat b)
  have cmp := comparePath (encodeNat (n / (b+1))) (encodeNat b) true
  rw [succWord_encode] at prep
  rw [wordLE_encode] at cmp
  apply ((prep.trans divi).trans cmp).mono
  change _ ≤ clock.eval (delimit (encodeNat n) ++ encodeNat b).length
  rw [List.length_append, length_delimit]
  have hsucc := succWord_length (encodeNat b)
  rw [succWord_encode] at hsucc
  have hquot : (encodeNat (n/(b+1))).length ≤ (encodeNat n).length := by
    change (bitEncode (n/(b+1))).length ≤ (bitEncode n).length
    rw [FactorEncoding.length_bitEncode_nat, FactorEncoding.length_bitEncode_nat]
    exact Nat.size_le_size (Nat.div_le_self ..)
  let L := 2*(encodeNat n).length + 1 + (encodeNat b).length
  have hlen : (encodeNat n).length + (encodeNat (b+1)).length ≤ L := by dsimp [L]; omega
  have hpoly : FactorDivisionTime.divisionClock.eval ((encodeNat n).length + (encodeNat (b+1)).length) ≤
      FactorDivisionTime.divisionClock.eval L := by
    simp only [FactorDivisionTime.divisionClock, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X]
    gcongr
  change _ ≤ clock.eval L
  simp only [clock, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  dsimp only [L] at *
  omega

/-- The comparison used by threshold search is deterministic polynomial time. -/
theorem query_polytime : IsPolyTime sqrtQuery := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := clock
            outputsFun := fun x => ?_ }⟩
  obtain ⟨n,b⟩ := x
  let run := Classical.choice (path n b)
  have initial (w : List Bool) : initList machine w = atL .parse w [] [] [] [] := by
    apply congrArg (fun t => (⟨some (.inl .parse), (none,none), t⟩ : Config))
    funext k
    rcases k with k | u
    · cases k <;> rfl
    · cases u; rfl
  have finalCfg (w : List Bool) : haltList machine w = cfg none w [] [] [] [] := by
    apply congrArg (fun t => (⟨none, (none,none), t⟩ : Config))
    funext k
    rcases k with k | u
    · cases k <;> rfl
    · cases u; rfl
  change TM2OutputsInTime machine ((bitEncode (n,b)).map id) (some [sqrtQuery (n,b)])
    (clock.eval (bitEncode (n,b)).length)
  erw [List.map_id]
  change StateTransition.EvalsToInTime (TM2.step program) (initList machine (bitEncode (n,b)))
    (some (haltList machine [sqrtQuery (n,b)])) _
  erw [initial, finalCfg]
  exact run

end FactorSqrtMachine

/- Polynomial-time extension of the promised factorial-coprimality query to a total comparison. -/

namespace FactorGuardConclusion

open BitstringEncoding Computability ComplexityTheory

private theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial k c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

private theorem prepared_polytime (s : ℕ → ℕ) (hs : IsPolyTime s) :
    IsPolyTime (FactorGuardBits.prepare s) := by
  obtain ⟨size, hsize⟩ := FactorMachineBound.polytime_output_bound hs
  apply FactorWordOracle.polytime_from_runs FactorGuardController.machine s _ hs
  intro charge
  refine ⟨6 * Polynomial.X + 2 * size + charge + 6, ?_⟩
  rintro ⟨n,b⟩
  apply (FactorGuardMachine.machine_run s charge.eval n b).mono
  let N := (encodeNat n).length
  let B := (encodeNat b).length
  let L := (bitEncode (n,b)).length
  have hl : L = 2*N + 1 + B := by
    change (bitEncode (n,b)).length = 2*(bitEncode n).length + 1 + (bitEncode b).length
    simp only [FactorEncoding.length_bitEncode_nat]
    exact FactorSearchClock.pair_length n b
  have hn : N ≤ L := by omega
  have hb : B ≤ L := by omega
  have hr : (encodeNat (s n)).length ≤ size.eval L := (hsize n).trans (eval_mono size hn)
  have hc := eval_mono charge hn
  change 4*N + 2*B + 2*(encodeNat (s n)).length + charge.eval N + 6 ≤
    (6 * Polynomial.X + 2 * size + charge + 6).eval L
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

theorem guard_polytime (query : ℕ × ℕ → Bool) (hq : IsPolyTime query) :
    ∃ full : ℕ × ℕ → Bool, IsPolyTime full ∧
      ∀ n b : ℕ, full (n,b) =
        if b < 2 then false else if n ≤ b then true else if 2 ∣ n then true
        else if 2 ≤ min b n.sqrt then query (n, min b n.sqrt) else false := by
  obtain ⟨s, hs, hroot⟩ := FactorSqrtBits.exists_sqrt FactorSqrtMachine.query_polytime
  refine ⟨FactorGuardPost.post query ∘ FactorGuardBits.prepare s,
    FactorMachineComposition.isPolyTime_comp (prepared_polytime s hs)
      (FactorGuardPost.polytime_post query hq), ?_⟩
  intro n b
  by_cases hb : b < 2
  · simp [Function.comp_apply, FactorGuardBits.prepare, FactorGuardPost.post, hb]
  by_cases hnb : n ≤ b
  · simp [Function.comp_apply, FactorGuardBits.prepare, FactorGuardPost.post, hb, hnb]
  by_cases he : 2 ∣ n
  · simp [Function.comp_apply, FactorGuardBits.prepare, FactorGuardPost.post, hb, hnb, he]
  have hne : n ≠ 0 := by omega
  have hr := hroot n (by omega)
  by_cases hc : 2 ≤ min b n.sqrt <;>
    simp [Function.comp_apply, FactorGuardBits.prepare, FactorGuardPost.post, hb, hnb, he, hr, hc, hne]

end FactorGuardConclusion

theorem OMA.solution : OMA.R_PolyTime_isPolyTime_primeFactorsList_R1.H2 := by
  exact FactorGuardConclusion.guard_polytime
