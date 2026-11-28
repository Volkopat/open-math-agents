import Mathlib

/-!
# Divisibility-incomparable sums from OEIS A226806

Zhi-Wei Sun conjectured on May 1, 2023 that every integer greater than one
except four is a sum of distinct terms of A226806, with no summand dividing
another. Its terms have the form 2^j + 4^k for nonnegative exponents j and k.
The index of a term in the sequence plays no role. A finite set records the
distinct summands, and divisibility within that set is allowed only for equal
elements.

Source: https://oeis.org/A226806
Credit: @rleshner
-/

namespace OMA.S_oeis_a226806

theorem main : ∀ n : ℕ, 1 < n → n ≠ 4 → ∃ s : Finset ℕ,
    (∀ x ∈ s, ∃ j k : ℕ, x = 2^j + 4^k) ∧
    (∑ x ∈ s, x) = n ∧
    (∀ x ∈ s, ∀ y ∈ s, x ∣ y → x = y) := by
  sorry

end OMA.S_oeis_a226806
