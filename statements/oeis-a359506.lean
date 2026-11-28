import Mathlib

/-!
# A359506: a(n) is the least integer m such that there exists a strictly increasing integer sequence n = b_1 < b_2 < ... < b_t = m with the property that b_1 XOR b_2 XOR ... XOR b_t = 0.

Source: https://oeis.org/A359506
Credit: @agchua

Formula line of A359506 (Charles R Greathouse IV, Jan 12 2023), verbatim:
  For n > 1, a(n) >= n + 3. a(4n) = 4n + 3 for n > 0. Conjecture: a(n) <= 5(n+1)/3.
All three sentences are stated below, as one conjunction. The sequence has offset 0 (data 0, 3,
5, 6, 7, 10, ...; a(0) = 0 by the one-term sequence b_1 = 0), and the conjecture is read for all
n >= 0, with 5(n+1)/3 a rational number. A strictly increasing sequence n = b_1 < ... < b_t = m
is a list of numbers that is strictly increasing, starts with n and ends with m; all its terms
are at least n >= 0, so it is a list of natural numbers, and XOR is the bitwise exclusive or
`^^^` of natural numbers.
-/

namespace OMA.S_oeis_a359506

/-- There is a strictly increasing sequence `n = b_1 < b_2 < ... < b_t = m` whose XOR
`b_1 XOR b_2 XOR ... XOR b_t` is `0`. -/
def Good (n m : ℕ) : Prop :=
  ∃ l : List ℕ, l.Pairwise (· < ·) ∧ l.head? = some n ∧ l.getLast? = some m ∧
    l.foldl (· ^^^ ·) 0 = 0

/-- A359506: the least `m` such that `Good n m`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | Good n m}

/-- For n > 1, a(n) >= n + 3; a(4n) = 4n + 3 for n > 0; and the conjecture a(n) <= 5(n+1)/3. -/
theorem main : (∀ n : ℕ, 1 < n → n + 3 ≤ a n) ∧
    (∀ n : ℕ, 0 < n → a (4 * n) = 4 * n + 3) ∧
    (∀ n : ℕ, (a n : ℚ) ≤ 5 * ((n : ℚ) + 1) / 3) := by
  sorry

end OMA.S_oeis_a359506
