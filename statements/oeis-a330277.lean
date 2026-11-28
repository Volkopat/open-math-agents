import Mathlib

/-!
# A330277: a(n) = k such that A083016(k) = prime(n), or -1 if no such k exists.

Source: https://oeis.org/A330277 (and https://oeis.org/A083016 for the definition of A083016)
Credit: @cjchaffin

Conjecture (stated on the OEIS page): every prime occurs in A083016, so `k` always exists.

Conventions:
- A083016 is the greedy rearrangement of the primes in which the sum of two consecutive terms
  is a square, as defined on that page and implemented by the Maple program there: `a 1 = 2`,
  and each later term is the smallest prime not yet used whose sum with the previous term is a
  square. The present conjecture is that this listing is a permutation of the primes (in
  particular the process never gets stuck), so A330277 is a total function on `n ≥ 1` and never
  takes the value `-1`.
- Both sequences have offset 1. We index the greedy listing by positive integers as well.
-/

namespace OMA.S_oeis_a330277

/-- A prime `p` is eligible to follow `prev` given the primes already used. -/
def eligible (used : Finset ℕ) (prev p : ℕ) : Prop :=
  p.Prime ∧ p ∉ used ∧ IsSquare (prev + p)

/-- `a` is the greedy listing A083016, starting at `a 1 = 2`. -/
def IsGreedy (a : ℕ → ℕ) : Prop :=
  a 1 = 2 ∧
    ∀ n : ℕ, 1 ≤ n →
      eligible ((Finset.Icc 1 n).image a) (a n) (a (n + 1)) ∧
        ∀ p : ℕ, eligible ((Finset.Icc 1 n).image a) (a n) p → a (n + 1) ≤ p

theorem main : ∃ a : ℕ → ℕ, IsGreedy a ∧ ∀ p : ℕ, p.Prime → ∃ n : ℕ, 1 ≤ n ∧ a n = p := by
  sorry

end OMA.S_oeis_a330277
