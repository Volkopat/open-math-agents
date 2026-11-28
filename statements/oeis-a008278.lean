import Mathlib

/-!
# OEIS A008278: Stirling numbers and divisors of superprimorials

Source: https://oeis.org/A008278
`T(n, k) = S(n, n-k+1)` (Stirling numbers of the second kind), `1 ≤ k ≤ n`.
Conjecture (Gus Wiseman, 2020): `T(n, k)` is also the number of divisors of the
superprimorial `A006939(n-1) = ∏_{i=1}^{n-1} prime(i)^(n-i)` that have `k - 1` distinct prime
factors, all appearing with distinct multiplicities. (For `n = 4` the divisors of `360` are
counted as `1 | 2 3 4 5 8 9 | 12 18 20 24 40 45 72 | 360`.)

Conventions. `prime(i)` is `Nat.nth Nat.Prime (i - 1)`; Stirling numbers of the second kind are
defined by the usual recurrence (`stirling2`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a008278

/-- Stirling numbers of the second kind. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- The superprimorial `∏_{i=1}^{m} prime(i)^(m+1-i)` (A006939(m)). -/
noncomputable def superprimorial (m : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 m, Nat.nth Nat.Prime (i - 1) ^ (m + 1 - i)

/-- `d` has exactly `j` distinct prime factors and their multiplicities are pairwise distinct. -/
def Good (j d : ℕ) : Prop :=
  d.primeFactors.card = j ∧ Set.InjOn d.factorization d.primeFactors

theorem main :
    ∀ n k : ℕ, 1 ≤ k → k ≤ n →
      Set.ncard {d | d ∣ superprimorial (n - 1) ∧ Good (k - 1) d} =
        stirling2 n (n - k + 1) := by
  sorry

end OMA.S_oeis_a008278
