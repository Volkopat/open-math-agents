import Mathlib

-- Hadwiger covering conjecture (combinatorial geometry; Levi–Hadwiger)
-- Source: https://en.wikipedia.org/wiki/Hadwiger_conjecture_(combinatorial_geometry)
-- (catalogue entry: covering n-dimensional convex bodies with at most 2^n smaller copies)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source (lead and Formal statement): any convex body `K` in `n`-dimensional Euclidean space can be
covered by `2^n` bodies `s_i K + v_i` homothetic to it with `0 < s_i < 1`; furthermore, the upper
bound `2^n` is necessary if and only if `K` is a parallelepiped.

Conventions:
* `ℝ^n` is `Fin n → ℝ`. Only its affine structure and topology are used (convexity,
  compactness, interior, homotheties, affine images), which do not depend on the choice of norm.
* Convex body: compact convex set with nonempty interior (the source's lead). The source's
  formal statement says bounded convex set; the convex-body reading of the lead is used so that
  the parallelepiped clause is about genuine bodies.
* `CoveredBy K m`: `K ⊆ ⋃ i, (s_i K + v_i)` for some `m` scalars `0 < s_i < 1` and translations.
* `2^n` is necessary means `K` is not covered by `2^n - 1` such copies.
* Parallelepiped: the image of the unit cube `[0,1]^n` under an affine automorphism of `ℝ^n`.
* `n ≥ 1`.
-/

namespace OMA.S_wp_hadwiger_conjecture

/-- `K` is covered by `m` smaller positive homothetic copies `s_i K + v_i`, `0 < s_i < 1`. -/
def CoveredBy {n : ℕ} (K : Set (Fin n → ℝ)) (m : ℕ) : Prop :=
  ∃ (s : Fin m → ℝ) (v : Fin m → Fin n → ℝ), (∀ i, 0 < s i ∧ s i < 1) ∧
    K ⊆ ⋃ i, (fun x => s i • x + v i) '' K

/-- `K` is a parallelepiped: an affine image of the unit cube. -/
def IsParallelepiped {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  ∃ f : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ), K = f '' {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The Hadwiger covering conjecture, with its equality clause. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ K : Set (Fin n → ℝ), IsCompact K → Convex ℝ K →
    (interior K).Nonempty →
      CoveredBy K (2 ^ n) ∧ (¬ CoveredBy K (2 ^ n - 1) ↔ IsParallelepiped K) := by
  sorry

end OMA.S_wp_hadwiger_conjecture
