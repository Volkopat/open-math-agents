import Mathlib

/-!
# A341309: Sum of odd divisors of n that are <= A003056(n).

Source: https://oeis.org/A341309
Credit: @ceejcake

Conjecture (OEIS A341309, Conjecture 1, Omar E. Pol, Mar 16 2022): `a(n)` is also the total number
of parts in all partitions of `n` into an odd number of consecutive parts.

Formalization notes:
* Only Conjecture 1 of the entry is formalized here (Conjecture 2, about row sums of A352269, and
  the conjectured formula `a(n) = A204217(n) - A352446(n)` are not).
* The sequence has offset `1`, so the claim is stated for `n ≥ 1`.
* `t n = floor((sqrt(8*n+1) - 1)/2)` is A003056(n), the largest `t` with `t*(t+1)/2 ≤ n`, written with
  the integer square root `Nat.sqrt` (this is exact: `floor(sqrt m) = Nat.sqrt m`).
* `a n` is the sum of the odd divisors `d` of `n` with `d ≤ t n`.
* A partition of `n` into `k` consecutive parts is `x, x+1, ..., x+k-1` with smallest part `x ≥ 1`
  and `x + (x+1) + ... + (x+k-1) = n`; it has `k` parts. `parts n` sums `k` times the number of
  such partitions over all odd `k`. The ranges `k ≤ n` and `x ≤ n` lose nothing for `n ≥ 1`, since
  every part and the number of parts are at most `n` (and `k = 0` gives the empty sum `0 ≠ n`).
* Initial values for `n = 1, ..., 20`: `1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 9, 1, 1, 4, 1, 6`.
-/

namespace OMA.S_oeis_a341309

/-- A003056: `t n = floor((sqrt(8*n+1) - 1)/2)`, the largest `t` with `t*(t+1)/2 ≤ n`. -/
def t (n : ℕ) : ℕ := (Nat.sqrt (8 * n + 1) - 1) / 2

/-- A341309: the sum of the odd divisors `d` of `n` with `d ≤ t n`. -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => Odd d ∧ d ≤ t n), d

/-- The total number of parts in all partitions of `n` into an odd number `k` of consecutive parts
`x, x+1, ..., x+k-1` with `x ≥ 1`. -/
def parts (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (n + 1)).filter Odd,
    k * ((Finset.Icc 1 n).filter (fun x => ∑ i ∈ Finset.range k, (x + i) = n)).card

/-- OEIS A341309, Conjecture 1: for `n ≥ 1`, `a n` equals the total number of parts in all
partitions of `n` into an odd number of consecutive parts. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = parts n := by
  sorry

end OMA.S_oeis_a341309
