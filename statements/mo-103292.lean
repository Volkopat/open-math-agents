import Mathlib

/-!
# Strongly pseudomonotone but not strongly monotone maps in dimension at least two

Source: https://mathoverflow.net/questions/103292
Credit: @koolkao

Question (MathOverflow 103292, 2012; CC BY-SA 3.0). Let `K` be a closed convex subset of `ℝⁿ`
and `F : K → ℝⁿ`. `F` is strongly monotone on `K` if there is `γ > 0` with
`⟨F(y) - F(x), y - x⟩ ≥ γ ‖y - x‖²` for all `x, y ∈ K`, and strongly pseudomonotone on `K` if
there is `γ > 0` with `⟨F(x), y - x⟩ ≥ 0 ⟹ ⟨F(y), y - x⟩ ≥ γ ‖y - x‖²` for all `x, y ∈ K`.
Strongly monotone implies strongly pseudomonotone, and `F(x) = 2 - x` on `K = [0, 1]` shows that
the converse fails in dimension one. Can we find `F : K → ℝⁿ` with `n ≥ 2` and `K` with nonempty
interior that is strongly pseudomonotone but not strongly monotone on `K`?

`main` states that the answer is yes.

Translation choices:
* `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` with its standard inner product and norm;
* a map `F : K → ℝⁿ` is a function `F` on all of `ℝⁿ` of which only the values on `K` matter
  (both definitions only evaluate `F` at points of `K`);
* the two notions are `StronglyMonotoneOn` and `StronglyPseudomonotoneOn` below, transcribed
  from the source.
-/

namespace OMA.S_mo_103292

open scoped RealInnerProductSpace

/-- `F` is strongly monotone on `K`. -/
def StronglyMonotoneOn {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ x ∈ K, ∀ y ∈ K, ⟪F y - F x, y - x⟫ ≥ γ * ‖y - x‖ ^ 2

/-- `F` is strongly pseudomonotone on `K`. -/
def StronglyPseudomonotoneOn {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ x ∈ K, ∀ y ∈ K, ⟪F x, y - x⟫ ≥ 0 → ⟪F y, y - x⟫ ≥ γ * ‖y - x‖ ^ 2

/-- In some dimension `n ≥ 2` there are a closed convex `K ⊆ ℝⁿ` with nonempty interior and a map
that is strongly pseudomonotone but not strongly monotone on `K`. -/
theorem main :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsClosed K ∧ Convex ℝ K ∧
      (interior K).Nonempty ∧
      ∃ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        StronglyPseudomonotoneOn F K ∧ ¬ StronglyMonotoneOn F K := by
  sorry

end OMA.S_mo_103292
