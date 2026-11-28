import Mathlib

/-!
# Translations and scalings of equal-radius ball covers

Source: Hu xiyu, MathOverflow 291073 (2018, CC BY-SA 3.0).
https://mathoverflow.net/questions/291073/are-these-two-sets-always-coincide-after-a-translation-or-scaling

We use finite-dimensional real inner product spaces as Euclidean spaces.
At each radius, the same finite index set describes both covers. A
translation or a scalar multiplication changes the center of a ball
and preserves its radius, as in the two displayed formulas in the source.
-/

namespace OMA.S_mo_291073

def HasLayer {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Set E) (radius exponent : ℝ) : Prop :=
  ∃ (I : Type) (indices : Fintype I) (x y : I → E)
    (translations : Finset E) (scales : Finset ℝ),
    A = ⋃ i, Metric.ball (x i) radius ∧ B = ⋃ i, Metric.ball (y i) radius ∧
    (∀ i, (∃ d ∈ translations, y i = x i + d) ∨
          (∃ s ∈ scales, y i = s • x i)) ∧
    ((max translations.card scales.card : ℕ) : ℝ) <
      ((@Fintype.card I indices : ℕ) : ℝ) ^ exponent

theorem main : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (A B : Set E) (δ : ℕ → ℝ),
    StrictAnti δ → (∀ m, 0 < δ m) →
    (∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ m, HasLayer A B (δ m) c) →
    (∃ d : E, B = (fun x => d + x) '' A) ∨
    (∃ s : ℝ, B = (fun x => s • x) '' A) := by
  sorry

end OMA.S_mo_291073

