import Mathlib

/-!
# Dividing up the unrestricted partitions

Source: https://www.openproblemgarden.org/op/dividing_up_the_unrestricted_partitions
Credit: @ishaanzee

Begin with the generating function for unrestricted partitions:
`(1 + x + x² + …)(1 + x² + x⁴ + …)(1 + x³ + x⁶ + …)⋯`. Now change some of the plus signs to minus
signs. The resulting series will have coefficients congruent, mod 2, to the coefficients of the
generating series for unrestricted partitions.

**Conjecture** (D. S. Newman). The signs may be chosen such that all the coefficients of the
series are either `1`, `-1`, or `0`.

Formalization:
* Changing signs means choosing, for each part size `k ≥ 1` and each `m ≥ 1`, a sign
  `ε k m ∈ {1, -1}` for the term `x^(k m)` of the `k`-th factor
  `1 + ε k 1 x^k + ε k 2 x^(2k) + ⋯` (the constant terms `1` carry no sign).
* Expanding the product, the coefficient of `x^N` is the sum over the partitions `p` of `N` of the
  product, over the distinct parts `k` of `p`, of `ε k (multiplicity of k in p)` (the factors with
  `m = 0` contribute `1`). Partitions of `N` are Mathlib's `Nat.Partition N`.
-/

namespace OMA.S_opg_dividing_up_the_unrestricted_partitions

/-- The coefficient of `x^N` in `∏_{k ≥ 1} (1 + ∑_{m ≥ 1} ε k m x^(k m))`. -/
def signedCoeff (ε : ℕ → ℕ → ℤ) (N : ℕ) : ℤ :=
  ∑ p : Nat.Partition N, ∏ k ∈ p.parts.toFinset, ε k (p.parts.count k)

/-- **Newman's conjecture**: some choice of signs makes every coefficient `1`, `-1` or `0`. -/
theorem main : ∃ ε : ℕ → ℕ → ℤ, (∀ k m, ε k m = 1 ∨ ε k m = -1) ∧
    ∀ N : ℕ, |signedCoeff ε N| ≤ 1 := by
  sorry

end OMA.S_opg_dividing_up_the_unrestricted_partitions
