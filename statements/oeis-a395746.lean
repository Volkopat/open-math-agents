import Mathlib

/-!
# OEIS A395746

For `n > 1` other than `15`, Chai Wah Wu conjectures that the gcd of the
interior binomial coefficients `choose (2n) (2k)` equals the squarefree
kernel of `n(2n−1)` exactly when both `n` and `2n−1` are prime powers.

Sources: https://oeis.org/A395746, https://oeis.org/A265388, https://oeis.org/A007947
Credit: @wtho704
-/

namespace OMA.S_oeis_a395746

/-- A265388, the gcd of `choose (2n) (2k)` over `1 ≤ k < n`. -/
def evenBinomialGcd (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).gcd fun k => (2 * n).choose (2 * k)

theorem main : ∀ n : ℕ, 1 < n → n ≠ 15 →
    (evenBinomialGcd n = UniqueFactorizationMonoid.radical (n * (2 * n - 1)) ↔
      IsPrimePow n ∧ IsPrimePow (2 * n - 1)) := by
  sorry

end OMA.S_oeis_a395746
