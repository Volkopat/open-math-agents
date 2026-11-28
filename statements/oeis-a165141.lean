import Mathlib

/-!
# First occurrences of the square, pentagonal and hexagonal representation count

The source collects three assertions: every positive count occurs at a positive
integer, the ratios above index 33 appear to lie between 0.9 and 1.6, and the
ratios are conjectured to converge to a number strictly between 1.1 and 1.2.
The middle clause records the empirical prediction separately.

Source: https://oeis.org/A165141
-/

namespace OMA.S_oeis_a165141

/-- Each coordinate is an ordinary nonnegative polygonal index. -/
def value (v : ℕ × ℕ × ℕ) : ℕ :=
  v.1^2 + 3*(v.2.1*(v.2.1-1)/2) + v.2.1
    + 4*(v.2.2*(v.2.2-1)/2) + v.2.2

/-- The number of ordered square, pentagonal and hexagonal representations. -/
noncomputable def count (n : ℕ) : ℕ :=
  Nat.card {v : ℕ × ℕ × ℕ // value v = n}

/-- The least positive input having count k, with the default zero when k
is unattained. The occurrence clause makes it well defined at every k > 0. -/
noncomputable def first (k : ℕ) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, 0 < n ∧ count n = k then Nat.find h else 0

noncomputable def ratio (k : ℕ) : ℝ := (first k : ℝ) / (k : ℝ)^2

theorem main :
    (∀ k : ℕ, 0 < k → ∃ n : ℕ, 0 < n ∧ count n = k) ∧
    (∀ k : ℕ, 33 < k → (9:ℝ)/10 < ratio k ∧ ratio k < (8:ℝ)/5) ∧
    (∃ c : ℝ, (11:ℝ)/10 < c ∧ c < (6:ℝ)/5 ∧
      Filter.Tendsto ratio Filter.atTop (nhds c)) := by
  sorry

end OMA.S_oeis_a165141
