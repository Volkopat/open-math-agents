import Mathlib

/-!
# Sun's representation conjecture for A303639

Source: https://oeis.org/A303639.
The sequence counts representations of n as the sum of two squares
and two terms of the form choose(2k+1,k). The indices are nonnegative,
with the two square bases and the two binomial indices each in
nondecreasing order. The conjecture asserts such a representation
exists for every n > 1.
-/

namespace OMA.S_oeis_a303639

def binomial (k : ℕ) : ℕ := (2*k+1).choose k

theorem main : ∀ n : ℕ, 1 < n → ∃ a b c d : ℕ,
    a ≤ b ∧ c ≤ d ∧ n = a^2 + b^2 + binomial c + binomial d := by
  sorry

end OMA.S_oeis_a303639
