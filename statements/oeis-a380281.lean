import Mathlib

/-!
# Row sums in Thomas Scheuerle's triangle A380281

The triangle uses the rising factorial (1/2)_j. Its conjectured row
sums are A076729(n), defined by (2n+1)!! times the integral of
(1+x²)^n from zero to one. Both sequences start at n = 0.

Sources: https://oeis.org/A380281 and https://oeis.org/A076729
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a380281
open Finset

noncomputable def halfRising (j : ℕ) : ℝ :=
  ∏ i ∈ range j, ((i : ℝ) + 1/2)

noncomputable def entry (n k : ℕ) : ℝ :=
  2^n * (Nat.choose (2*n+1) (2*k+1) : ℝ) * halfRising (n-k) * halfRising k

def oddProduct (j : ℕ) : ℕ := ∏ i ∈ range j, (2*i+1)

theorem main : ∀ n : ℕ, ∑ k ∈ range (n+1), entry n k =
    (oddProduct (n+1) : ℝ) * ∫ x : ℝ in 0..1, (1+x^2)^n := by
  sorry

end OMA.S_oeis_a380281
