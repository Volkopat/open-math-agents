import Mathlib

namespace OMA.S_opg_the_robustness_of_the_tensor_product_0

open scoped BigOperators

abbrev Word (n : ℕ) := Fin n → ZMod 2
abbrev Code (n : ℕ) := Submodule (ZMod 2) (Word n)

/-- Relative Hamming distance, on a nonempty coordinate set in the statement below. -/
noncomputable def relativeHamming {ι : Type} [Fintype ι] [DecidableEq ι]
    (x y : ι → ZMod 2) : ℝ :=
  (hammingDist x y : ℝ) / Fintype.card ι

/-- The image of a nonempty finite code is finite and nonempty, so this is a minimum. -/
noncomputable def distanceTo {ι : Type} [Fintype ι] [DecidableEq ι]
    (x : ι → ZMod 2) (S : Set (ι → ZMod 2)) : ℝ :=
  sInf (relativeHamming x '' S)

def HasGoodParameters {n : ℕ} (C : Code n) : Prop :=
  (1 / 1000 : ℝ) ≤ (Module.finrank (ZMod 2) C : ℝ) / n ∧
    ∀ x ∈ C, ∀ y ∈ C, x ≠ y → (1 / 1000 : ℝ) ≤ relativeHamming x y

abbrev BinaryMatrix (rows cols : ℕ) := Matrix (Fin rows) (Fin cols) (ZMod 2)

/-- Every row lies in the row code and every column in the column code. -/
def tensorCode {rows cols : ℕ} (R : Code cols) (C : Code rows) :
    Set (Fin rows × Fin cols → ZMod 2) :=
  {w | (∀ i, (fun j => w (i, j)) ∈ R) ∧ (∀ j, (fun i => w (i, j)) ∈ C)}

noncomputable def tensorDistance {rows cols : ℕ} (R : Code cols) (C : Code rows)
    (M : BinaryMatrix rows cols) : ℝ :=
  distanceTo (fun ij => M ij.1 ij.2) (tensorCode R C)

noncomputable def rowColumnAverage {rows cols : ℕ} (R : Code cols) (C : Code rows)
    (M : BinaryMatrix rows cols) : ℝ :=
  ((∑ i : Fin rows, distanceTo (M i) (R : Set (Word cols))) / rows +
    (∑ j : Fin cols, distanceTo (fun i => M i j) (C : Set (Word rows))) / cols) / 2

/-- The Goldreich–Meir obstruction to a characterization by rate and distance:
two good binary linear code families can have no uniform tensor robustness. -/
theorem main :
    ∃ (rows cols : ℕ → ℕ) (R : ∀ k : ℕ, Code (cols k)) (C : ∀ k : ℕ, Code (rows k)),
      (∀ k : ℕ, k + 1 ≤ rows k ∧ k + 1 ≤ cols k ∧
        HasGoodParameters (R k) ∧ HasGoodParameters (C k)) ∧
      ∀ α : ℝ, 0 < α → α < 1 →
        ∃ (k : ℕ) (M : BinaryMatrix (rows k) (cols k)),
          rowColumnAverage (R k) (C k) M < α * tensorDistance (R k) (C k) M := by
  sorry

end OMA.S_opg_the_robustness_of_the_tensor_product_0
