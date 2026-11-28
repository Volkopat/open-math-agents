import Mathlib

/-!
# Continuity of Lebesgue volume in the Hausdorff metric

Source: Redeldio, https://mathoverflow.net/questions/364097 (CC BY-SA).
Credit: @connoranderson. Ville Salo observed that finite sets are dense, and
Pierre PC noted upper semicontinuity and conjectured the exact set of volumes
attained in every neighborhood. We use nonempty compact subsets in positive
Euclidean dimension, with the usual Hausdorff metric.
-/
namespace OMA.S_mo_364097
open Set MeasureTheory Metric
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (n+1))
noncomputable def vol {n : ℕ} (K : Set (E n)) : ℝ := volume.real K

theorem main : ∀ {n : ℕ} (K : Set (E n)), IsCompact K → K.Nonempty →
    (∀ ε : ℝ, 0<ε → ∃ δ>0, ∀ H : Set (E n), IsCompact H → H.Nonempty →
      hausdorffDist K H<δ → vol H < vol K+ε) ∧
    (∀ m : ℝ, m∈Icc 0 (vol K) ↔ ∀ δ : ℝ, 0<δ → ∃ H : Set (E n),
      IsCompact H ∧ H.Nonempty ∧ hausdorffDist K H<δ ∧ vol H=m) ∧
    ((∀ ε : ℝ, 0<ε → ∃ δ>0, ∀ H : Set (E n), IsCompact H → H.Nonempty →
      hausdorffDist K H<δ → |vol H-vol K|<ε) ↔ vol K=0) := by
  sorry
end OMA.S_mo_364097
