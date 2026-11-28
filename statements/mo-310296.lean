import Mathlib

/-!
# Equality in a trace bound for Lyapunov equations

Source: https://mathoverflow.net/questions/310296
Credit: @LDJAI

For each real Hurwitz matrix of positive size, the question asks whether a
positive semidefinite input can attain the bound with a positive definite
Lyapunov solution. The spectrum of the complexified drift gives the Hurwitz
condition. For the real symmetric positive definite solution, the greatest
element of its real spectrum is its largest eigenvalue.
-/

namespace OMA.S_mo_310296

theorem main : ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
    (∀ z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), z.re < 0) →
    ∃ (Q P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (l : ℝ),
      Q.PosSemidef ∧ P.PosDef ∧ A * P + P * A.transpose = -Q ∧
      IsGreatest (spectrum ℝ P) l ∧ -2 * A.trace = Q.trace / l := by
  sorry

end OMA.S_mo_310296
