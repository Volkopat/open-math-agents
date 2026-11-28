import Mathlib

/-!
# Multiple mixing, 75 years of Rokhlin's problem

Source: https://arxiv.org/abs/2411.07234, Section 1.
Credit: @my-other-github-account

Ryzhikov counts k-fold mixing using k+1 sets A_0,...,A_k, so ordinary
mixing is 1-fold mixing. We state the affirmative form of his question
for invertible measure-preserving transformations of a probability space.
As in the displayed definition in Section 1, the iterates below are images,
not preimages, and the k natural gaps tend jointly to positive infinity.
The exponent for A_i is the sum of the gaps preceding slot i; in particular
A_0 has exponent zero. The pointwise order on Fin k → ℕ gives this joint limit.
No assertion about more general group actions or flows is included.
-/

namespace OMA.S_arxiv_2411_07234

open Filter Topology MeasureTheory
open scoped BigOperators

theorem main :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
      (T : X ≃ᵐ X),
      MeasurePreserving T μ μ →
      (∀ A B : Set X, MeasurableSet A → MeasurableSet B →
        Tendsto (fun n : ℕ => μ (A ∩ (⇑T)^[n] '' B)) atTop (𝓝 (μ A * μ B))) →
      ∀ k : ℕ, 1 ≤ k →
        ∀ A : Fin (k + 1) → Set X, (∀ i, MeasurableSet (A i)) →
          Tendsto
            (fun gaps : Fin k → ℕ =>
              μ (⋂ i : Fin (k + 1),
                (⇑T)^[∑ j : Fin k, if j.val < i.val then gaps j else 0] '' A i))
            atTop (𝓝 (∏ i : Fin (k + 1), μ (A i))) := by
  sorry

end OMA.S_arxiv_2411_07234
