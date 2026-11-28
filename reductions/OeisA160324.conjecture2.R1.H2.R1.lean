import OMAReductions.R_OeisA160324_conjecture2_R1
import Mathlib

/- In dimensions 12 through 65, Lagrange's four-square theorem and finite
residue covers settle every target. The five lower dimensions use ternary forms. -/
namespace OMA.R_OeisA160324_conjecture2_R1_H2_R1

def H1 : Prop := ∀ m : ℕ, 7 ≤ m → m < 12 → ∀ n : ℕ,
  ∃ x : Fin m → ℕ, n = ∑ i : Fin m, OeisA160324.polygonalNumber (m+(i:ℕ)+1) (x i)

def H2 : Prop := ∀ m : ℕ, 12 ≤ m → m < 66 → ∀ n : ℕ,
  ∃ x : Fin m → ℕ, n = ∑ i : Fin m, OeisA160324.polygonalNumber (m+(i:ℕ)+1) (x i)

theorem main : H1 → H2 → OMA.R_OeisA160324_conjecture2_R1.H2 := by
  intro low high m hm hhi n
  by_cases h : m < 12
  · exact low m hm h n
  · exact high m (by omega) hhi n

end OMA.R_OeisA160324_conjecture2_R1_H2_R1
