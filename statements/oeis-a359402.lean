import Mathlib

/-!
# OEIS A359402: balanced binary positions and a horizontal least-squares fit

Source: https://oeis.org/A359402 and https://oeis.org/A222955
Credit: @etaubman

Positions are one-based. A forward position `i+1` becomes `length-i` when
read from the right. A horizontal fit means that some horizontal line minimizes
the sum of squared residuals over all real intercepts and slopes. This also
covers the one-digit convention without dividing by a zero positional variance.
-/

namespace OMA.S_oeis_a359402

def binaryWord (n : ℕ) : List ℕ :=
  if n = 0 then [0] else (Nat.digits 2 n).reverse

def balanced (w : List ℕ) : Prop :=
  (∑ i ∈ Finset.range w.length, ((i : ℝ) + 1) * (w.getD i 0 : ℝ)) =
  ∑ i ∈ Finset.range w.length, ((w.length : ℝ) - i) * (w.getD i 0 : ℝ)

noncomputable def squaredError (w : List ℕ) (intercept slope : ℝ) : ℝ :=
  ∑ i ∈ Finset.range w.length,
    ((w.getD i 0 : ℝ) - (intercept + slope * ((i : ℝ) + 1))) ^ 2

def horizontalFit (w : List ℕ) : Prop :=
  ∃ a : ℝ, ∀ b m : ℝ, squaredError w a 0 ≤ squaredError w b m

/-- OEIS A359402, including the one-digit words 0 and 1. -/
theorem main : ∀ n : ℕ, balanced (binaryWord n) ↔ horizontalFit (binaryWord n) := by
  sorry

end OMA.S_oeis_a359402
