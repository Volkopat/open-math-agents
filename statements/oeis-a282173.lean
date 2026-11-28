import Mathlib

/-!
# A282173: Expansion of (Sum_{k>=0} x^(k*(k+1)*(2*k+1)/6))^6.

Source: https://oeis.org/A282173
Credit: @luciusacarr

a(n) is the number of ways to write n as an ordered sum of 6 square pyramidal numbers (A000330:
0, 1, 5, 14, 30, ...).

The entry's comments record three conjectures. `main` states all three, as a conjunction, in
the order the source gives them.

Conjecture: a(n) > 0 for all n.
Extended conjecture: every number is the sum of at most 6 square pyramidal numbers.
Generalized conjecture (Ilya Gutkovskiy, Feb 10 2017): every number is the sum of at most k+2
k-gonal pyramidal numbers (except k = 5).

Reading of the source:
* The square pyramidal numbers are `m(m+1)(2m+1)/6` for `m ≥ 0` (0 included, as in the
  generating function). a(n) > 0 says `n` is a sum of exactly 6 of them, in some order.
* The k-gonal pyramidal numbers are `m(m+1)((k-2)m - (k-5))/6` for `m ≥ 0` (k = 3: tetrahedral,
  k = 4: square pyramidal). The factor `(k-2)m - (k-5)` is written `(k-2)m + 5 - k` in ℕ; it is
  computed exactly for `m ≥ 1` (it is at least 3 there), and for `m = 0` the product is 0 either
  way. Pyramidal numbers are taken for polygons, `k ≥ 3`, with `k ≠ 5` as the source excepts.
* "Sum of at most j" means a sum of `r ≤ j` such numbers, repetitions allowed (summands indexed by
  `Fin r`; zero summands are allowed for n = 0).
* Numerically: every n ≤ 5000 is a sum of at most k + 2 k-gonal pyramidal numbers for
  k = 3, 4, 6, ..., 11 (and k = 5 fails at n = 35).
-/

namespace OMA.S_oeis_a282173

/-- `m` is a square pyramidal number (A000330), 0 included. -/
def IsSquarePyramidal (m : ℕ) : Prop := ∃ t : ℕ, m = t * (t + 1) * (2 * t + 1) / 6

/-- `m` is a `k`-gonal pyramidal number `t(t+1)((k-2)t - (k-5))/6`, 0 included. -/
def IsPyramidal (k m : ℕ) : Prop := ∃ t : ℕ, m = t * (t + 1) * ((k - 2) * t + 5 - k) / 6

theorem main :
    -- a(n) > 0: every n is a sum of 6 square pyramidal numbers.
    (∀ n : ℕ, ∃ b : Fin 6 → ℕ, (∀ i, IsSquarePyramidal (b i)) ∧ ∑ i, b i = n) ∧
    -- Every number is the sum of at most 6 square pyramidal numbers.
    (∀ n : ℕ, ∃ (r : ℕ) (b : Fin r → ℕ), r ≤ 6 ∧
      (∀ i, IsSquarePyramidal (b i)) ∧ ∑ i, b i = n) ∧
    -- For k ≥ 3, k ≠ 5: every number is the sum of at most k + 2 k-gonal pyramidal numbers.
    (∀ k : ℕ, 3 ≤ k → k ≠ 5 → ∀ n : ℕ, ∃ (r : ℕ) (b : Fin r → ℕ), r ≤ k + 2 ∧
      (∀ i, IsPyramidal k (b i)) ∧ ∑ i, b i = n) := by
  sorry

end OMA.S_oeis_a282173
