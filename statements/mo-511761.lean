import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Span

/-! Source: https://mathoverflow.net/questions/511761 -/

namespace OMA.S_mo_511761

abbrev R := MvPolynomial (Fin 3) ℂ

theorem main :
    ∀ A B C D : R, A ^ 2 * B ^ 2 * C ^ 2 * D ^ 2 ∈
      Ideal.span ({A ^ 3, B ^ 3, C ^ 3, D ^ 3} : Set R) := by
  sorry

end OMA.S_mo_511761
