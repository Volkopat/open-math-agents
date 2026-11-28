import Mathlib

/-!
# The ladder column of OEIS A384616

Sela Fried's conjecture gives the maximum sum of absolute label differences along
edges of a rectangular grid with two rows and m columns, for every m ≥ 2.
Column two of the OEIS triangle starts at m = 2. The proposed value is
A067725(m-1)-1 = 3m²-4, since A067725(k) = 3k²+6k.

Source: https://oeis.org/A384616 and https://oeis.org/A067725
Credit: @arcstone09
-/

namespace OMA.S_oeis_a384616

/-- For a ladder of width n+1, a placement is a bijection onto 2(n+1) labels.
The zero-based ranks in Fin give the usual labels 1,...,2(n+1) after adding one,
which preserves all differences. Bool distinguishes the two rows. -/
abbrev Placement (n : ℕ) :=
  (Bool × Fin (n+1)) ≃ Fin ((n+1)+(n+1))

def label {n : ℕ} (p : Placement n) (row : Bool) (j : Fin (n+1)) : ℤ :=
  (p (row, j)).val

/-- Each rung and each horizontal edge of the two rails contributes once. -/
def score (n : ℕ) (p : Placement n) : ℤ :=
  (∑ j : Fin (n+1), |label p false j - label p true j|) +
    ∑ j : Fin n, (|label p false j.castSucc - label p false j.succ| +
                  |label p true j.castSucc - label p true j.succ|)

/-- The stated maximum, including attainability; the ladder has width k+2. -/
theorem main : ∀ k : ℕ, IsGreatest (Set.range (score (k+1))) (3*((k : ℤ)+2)^2-4) := by
  sorry

end OMA.S_oeis_a384616
