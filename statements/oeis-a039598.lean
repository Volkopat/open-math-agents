import Mathlib

/-!
# A039598: harmonic identity for Catalan's triangle

Werner Schulte's identity relates a weighted sum of a row of A039598 to the
harmonic number and the Catalan number. The triangle uses the explicit
binomial formula from the OEIS entry, with zero-based indices.

Source: https://oeis.org/A039598
-/

namespace OMA.S_oeis_a039598

open Finset

def catalanTriangle (n k : ℕ) : ℚ :=
  if k ≤ n then
    (Nat.choose (2 * n + 1) (n - k) : ℚ) * (2 * ((k : ℚ) + 1)) /
      ((n : ℚ) + k + 2)
  else 0

theorem main : ∀ n : ℕ,
    (∑ k ∈ range (n + 1), catalanTriangle n k / ((k : ℚ) + 1) ^ 2) =
      harmonic (n + 1) * (catalan n : ℚ) * (2 * (n : ℚ) + 1) / ((n : ℚ) + 1) := by
  sorry

end OMA.S_oeis_a039598
