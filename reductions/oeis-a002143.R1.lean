import OMAStatements.S_oeis_a002143
import Mathlib

/-! Separate the trigonometric identity from the class-number formula.
Multiplication by a square root of -2 permutes the nonzero squares
when p is three modulo eight. The remaining identity is the cotangent
class-number formula of Berndt and Zaharescu, in Theorem 4.4 of Beck
and Halloran (arXiv:0804.0645), specialized to the Legendre character.
The formal class number here counts reduced forms. -/
namespace OMA.R_oeis_a002143_R1
open OMA.S_oeis_a002143 Real

def H1 : Prop := ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 8 = 3 →
  (∑ k ∈ Finset.Icc 1 ((p - 1) / 2), 1 / sin (2 * π * (k : ℝ) ^ 2 / p)) =
    ∑ k ∈ Finset.Icc 1 (p - 1), (legendreSym p k : ℝ) * cot (π * (k : ℝ) / p)

def H2 : Prop := ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 8 = 3 →
  2 * (h (-(p : ℤ)) : ℝ) * √p = ∑ k ∈ Finset.Icc 1 (p - 1), (legendreSym p k : ℝ) * cot (π * (k : ℝ) / p)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a002143.main := by
  intro trig arithmetic p hp hp3 h8
  let : Fact p.Prime := ⟨hp⟩
  exact (arithmetic p hp3 h8).trans (trig p hp3 h8).symm

end OMA.R_oeis_a002143_R1
