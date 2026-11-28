import OMAStatements.S_oeis_a048819
import Mathlib

/-! The functional equations and continuity force five distinct fixed points.
It suffices to prove uniqueness in the open left half of the unit interval. -/
namespace OMA.R_oeis_a048819_R1
open Set

open Classical in
def H1 : Prop := ∀ f : ℝ → ℝ, (ContinuousOn f (Icc 0 1) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, f (x / (1 + x)) = f x / 2) ∧
    ∀ x ∈ Icc (0 : ℝ) 1, f (1 - x) = 1 - f x) → ∃ x ∈ Icc (1/3 : ℝ) (3/7),
      let s : Finset ℝ := {0, x, 1/2, 1-x, 1}
      s.card = 5 ∧ ↑s ⊆ {y ∈ Icc (0 : ℝ) 1 | f y = y}

def H2 : Prop := ∀ f : ℝ → ℝ, (ContinuousOn f (Icc 0 1) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, f (x / (1 + x)) = f x / 2) ∧
    ∀ x ∈ Icc (0 : ℝ) 1, f (1 - x) = 1 - f x) →
    ∀ x ∈ Ioo (0 : ℝ) (1/2), f x = x →
    ∀ y ∈ Ioo (0 : ℝ) (1/2), f y = y → x = y

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a048819.main := by
  classical
  intro lower unique f hc ht hr
  obtain ⟨x, hx, card, sub⟩ := lower f ⟨hc, ht, hr⟩
  let s : Finset ℝ := {0, x, 1/2, 1-x, 1}
  change s.card = 5 at card
  change ↑s ⊆ {y ∈ Icc (0 : ℝ) 1 | f y = y} at sub
  have xf : f x = x := (sub (show x ∈ s by simp [s])).2
  obtain ⟨xl, xu⟩ := hx
  have left : x ∈ Ioo (0 : ℝ) (1/2) := ⟨by linarith, by linarith⟩
  have eq : {y ∈ Icc (0 : ℝ) 1 | f y = y} = ↑s := by
    apply Subset.antisymm _ sub
    rintro y ⟨hy, yf⟩
    change y ∈ s
    by_cases zero : y = 0
    · simp [s, zero]
    by_cases one : y = 1
    · simp [s, one]
    rcases lt_trichotomy y (1/2) with lt | mid | gt
    · have same := unique f ⟨hc, ht, hr⟩ x left xf y ⟨lt_of_le_of_ne hy.1 (Ne.symm zero), lt⟩ yf
      simp [s, ← same]
    · simp [s, mid]
    · have reflected : f (1-y) = 1-y := by rw [hr y hy, yf]
      have inside : 1-y ∈ Ioo (0 : ℝ) (1/2) := by
        obtain ⟨_, yu⟩ := hy
        have strict : y < 1 := lt_of_le_of_ne yu one
        constructor <;> linarith
      have same := unique f ⟨hc, ht, hr⟩ x left xf (1-y) inside reflected
      have : y = 1-x := by linarith
      simp [s, this]
  rw [eq]
  simpa using card

end OMA.R_oeis_a048819_R1
