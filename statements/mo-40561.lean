import Mathlib

/-!
# A combinatorial abstraction for the polynomial Hirsch conjecture (Hähnle's conjecture)

Source: https://mathoverflow.net/questions/40561
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Disjoint families `𝓕₁, …, 𝓕_t` satisfy `(*)` if for all `i < j < k`, `R ∈ 𝓕ᵢ` and `T ∈ 𝓕ₖ`
there is `S ∈ 𝓕ⱼ` containing `R ∩ T`. With all members multisets of size `d` over
`{1, …, n}`, `f*(d, n)` is the largest possible `t`. The question records Hähnle's conjecture
`f*(d, n) = d (n - 1) + 1`; `main` states it.

Conventions:
* Families are nonempty (otherwise `t` is unbounded trivially) and pairwise disjoint finite sets
  of multisets over `Fin n` of cardinality `d`; containment of multisets is `≤` and `∩` is
  multiset intersection. `d, n ≥ 1`.
* `f*(d, n) = d (n - 1) + 1` is stated as: every admissible sequence has `t ≤ d (n - 1) + 1`,
  and some admissible sequence has `t = d (n - 1) + 1`.
-/

namespace OMA.S_mo_40561

/-- `F : Fin t → Finset (Multiset (Fin n))` is admissible for size `d`. -/
def Admissible (d n t : ℕ) (F : Fin t → Finset (Multiset (Fin n))) : Prop :=
  (∀ i, (F i).Nonempty) ∧ (∀ i, ∀ R ∈ F i, Multiset.card R = d) ∧
  (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧
  ∀ i j k, i < j → j < k → ∀ R ∈ F i, ∀ T ∈ F k, ∃ S ∈ F j, R ∩ T ≤ S

/-- Hähnle's conjecture `f*(d, n) = d (n - 1) + 1`. -/
theorem main : ∀ d n : ℕ, 1 ≤ d → 1 ≤ n →
    (∀ t (F : Fin t → Finset (Multiset (Fin n))), Admissible d n t F → t ≤ d * (n - 1) + 1) ∧
    ∃ F : Fin (d * (n - 1) + 1) → Finset (Multiset (Fin n)), Admissible d n _ F := by
  sorry

end OMA.S_mo_40561
