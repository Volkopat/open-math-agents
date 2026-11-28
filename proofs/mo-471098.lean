import OMAStatements.S_mo_471098
import Mathlib
open OMA.S_mo_471098

/-! Counterexample with `k = 12` and `k₀ = 4` (so `√k < k₀ < k`): `A` consists of the vectors
with at most one `1`, `B` of the vectors with at most one `0`. For `x = e₀`, both `e₁` and `e₂`
are forced to be sent to the complement of `x`. -/

/-- The vector `x = e₀`. -/
def x0 : Fin 12 → Bool := fun i => decide (i = 0)

/-- The vector `e₁`. -/
def a0 : Fin 12 → Bool := fun i => decide (i = 1)

/-- The vector `e₂`. -/
def a1 : Fin 12 → Bool := fun i => decide (i = 2)

/-- The complement of `x`. -/
def v0 : Fin 12 → Bool := fun i => decide (i ≠ 0)

set_option maxRecDepth 100000 in
lemma forced0 : ∀ b : Fin 12 → Bool, 12 + 2 * 4 < 2 * cnt b true →
    (∀ i, a0 i ≠ b i → a0 i = x0 i) → b = v0 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma forced1 : ∀ b : Fin 12 → Bool, 12 + 2 * 4 < 2 * cnt b true →
    (∀ i, a1 i ≠ b i → a1 i = x0 i) → b = v0 := by
  decide +kernel

lemma x0A : x0 ∈ SetA 12 4 := by
  show 12 + 2 * 4 < 2 * cnt x0 false
  decide

lemma a0A : a0 ∈ SetA 12 4 := by
  show 12 + 2 * 4 < 2 * cnt a0 false
  decide

lemma a1A : a1 ∈ SetA 12 4 := by
  show 12 + 2 * 4 < 2 * cnt a1 false
  decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_471098.main) := by
  intro h
  obtain ⟨f, hB, hinj, hflip⟩ := h 12 4 (by norm_num) (by norm_num) x0 x0A
  have h0 : f a0 = v0 := forced0 (f a0) (hB a0 a0A) (hflip a0 a0A)
  have h1 : f a1 = v0 := forced1 (f a1) (hB a1 a1A) (hflip a1 a1A)
  have := hinj a0A a1A (h0.trans h1.symm)
  have hne : a0 ≠ a1 := by decide
  exact hne this
