import Mathlib

/-!
# OEIS A093489: total signature symmetry

Source: https://oeis.org/A093489
The total signature symmetry `a(n)` is the number of `r` (with `0 < r < n`) such that `n - r` and
`n + r` have the same prime signature (equivalently, partitions of `2n` into two parts with
identical prime signatures). Conjectures: (1) no term is zero for `n > 3`; (2) every number `k`
appears only finitely many times. `main` is their conjunction.

Conventions. The prime signature of `m ≥ 1` is the multiset of exponents of its prime
factorisation. `r` ranges over `1 ≤ r < n`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a093489

/-- The prime signature of `m`. -/
noncomputable def sig (m : ℕ) : Multiset ℕ := m.primeFactors.val.map m.factorization

/-- A093489. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {r : ℕ | 1 ≤ r ∧ r < n ∧ sig (n - r) = sig (n + r)}

theorem main : (∀ n : ℕ, 3 < n → a n ≠ 0) ∧ ∀ k : ℕ, {n : ℕ | a n = k}.Finite := by
  sorry

end OMA.S_oeis_a093489
