import Mathlib

/-!
# Volume of a symplectically self-polar convex body

Source: Mark Berezovik and Roman Karasev, arXiv:2211.14630v3, Conjecture 1.1.
Credit: @my-other-github-account

We use position and momentum coordinates on standard symplectic space.
As in the definition preceding Conjecture 1.1, the convex body contains zero
in its interior. Central symmetry is a consequence, not an assumption.
-/

namespace OMA.S_arxiv_2211_14630

open scoped ENNReal

abbrev Phase (n : ℕ) := Fin (n + n) → ℝ

def symplecticPolar {n : ℕ} (X : Set (Phase n)) : Set (Phase n) :=
  {y | ∀ x ∈ X, (∑ i : Fin n, (x (Fin.castAdd n i) * y (Fin.natAdd n i) - x (Fin.natAdd n i) * y (Fin.castAdd n i))) ≤ 1}

theorem main : ∀ (n : ℕ) (X : Set (Phase n)), IsCompact X → Convex ℝ X →
    0 ∈ interior X → X = symplecticPolar X →
    (2 : ℝ≥0∞) ^ n / (n.factorial : ℝ≥0∞) ≤ MeasureTheory.volume X := by
  sorry

end OMA.S_arxiv_2211_14630
