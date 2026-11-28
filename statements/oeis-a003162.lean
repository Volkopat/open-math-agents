import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

/-!
# OEIS A003162: binomial-difference divisibility and supercongruence

Source: https://oeis.org/A003162
The two claims are from Peter Bala's March 26, 2023 entry. The binomial
coefficient with lower index minus one is zero. Up to the midpoint,
successive binomial coefficients are nondecreasing, so natural subtraction
represents their ordinary difference.
-/

namespace OMA.S_oeis_a003162

/-- The difference between adjacent coefficients in row `n` of Pascal's triangle. -/
def delta (n : ℕ) : ℕ → ℕ
  | 0 => n.choose 0
  | k + 1 => n.choose (k + 1) - n.choose k

def powerSum (r n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), delta n k ^ r

def oddSubsequence (n : ℕ) : ℕ :=
  powerSum 3 (2 * n - 1) / powerSum 1 (2 * n - 1)

theorem main :
    (∀ r n : ℕ, r % 2 = 1 → powerSum 1 n ∣ powerSum r n) ∧
    (∀ n k p : ℕ, 0 < n → 0 < k → p.Prime → 5 ≤ p →
      oddSubsequence (n * p ^ k) ≡ oddSubsequence (n * p ^ (k - 1))
        [MOD p ^ (3 * k)]) := by
  sorry

end OMA.S_oeis_a003162
