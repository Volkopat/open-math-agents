import FormalConjectures.OEIS.«160324»
import Mathlib

/- H1 isolates the four small dimensions. H2 has finite certificates using
three and four squares. H3 follows uniformly from the four-square theorem. -/

namespace OMA.R_OeisA160324_conjecture2_R1

/-- The four remaining dimensions, with n unrestricted. -/
def H1 : Prop := ∀ m : ℕ, 2 < m → m < 7 → ∀ n : ℕ,
  ∃ x : Fin m → ℕ, n = ∑ i : Fin m, OeisA160324.polygonalNumber (m + (i : ℕ) + 1) (x i)

/-- These dimensions admit finite residue covers and bounded initial checks. -/
def H2 : Prop := ∀ m : ℕ, 7 ≤ m → m < 66 → ∀ n : ℕ,
  ∃ x : Fin m → ℕ, n = ∑ i : Fin m, OeisA160324.polygonalNumber (m + (i : ℕ) + 1) (x i)

/-- These dimensions admit a uniform consecutive-order construction. -/
def H3 : Prop := ∀ m : ℕ, 66 ≤ m → ∀ n : ℕ,
  ∃ x : Fin m → ℕ, n = ∑ i : Fin m, OeisA160324.polygonalNumber (m + (i : ℕ) + 1) (x i)

theorem main : H1 → H2 → H3 → type_of% @OeisA160324.conjecture2 := by
  intro small middle large m hm n
  by_cases h : m < 7
  · exact small m hm h n
  by_cases h' : m < 66
  · exact middle m (by omega) h' n
  · exact large m (by omega) n

end OMA.R_OeisA160324_conjecture2_R1
