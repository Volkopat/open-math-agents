import Mathlib

/-!
# A237839: a(n) = |{0 < k <= n: q = |{p <= k*n: p and p + 2 are both prime}| and q + 2 are both prime}|.

Source: https://oeis.org/A237839
Credit: @eltociear

Let `T(x)` be the number of primes `p ≤ x` with `p + 2` also prime. `a(n)` (offset 1) counts the
`k` with `0 < k ≤ n` such that `q = T(k n)` and `q + 2` are both prime. The entry conjectures
(Zhi-Wei Sun):

  a(n) > 0 for all n > 3, and a(n) = 1 only for n = 5, 9, 25, 77, 104.

`main` is the conjunction of the two parts.
-/

namespace OMA.S_oeis_a237839

/-- `T x`: the number of primes `p ≤ x` with `p + 2` prime. -/
def T (x : ℕ) : ℕ := ((Finset.range (x + 1)).filter (fun p => p.Prime ∧ (p + 2).Prime)).card

/-- OEIS A237839. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => (T (k * n)).Prime ∧ (T (k * n) + 2).Prime)).card

/-- The conjecture in OEIS A237839. -/
theorem main : (∀ n : ℕ, 3 < n → 0 < a n) ∧
    (∀ n : ℕ, 3 < n → a n = 1 → n ∈ ({5, 9, 25, 77, 104} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a237839
