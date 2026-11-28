import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

namespace OMA.S_mo_467261

/-- Evaluate the complete homogeneous symmetric polynomial at n-i copies of one
followed by i copies of x. -/
noncomputable def repeatedEvaluation (n ell i : ℕ) (x : ℝ) : ℝ :=
  MvPolynomial.eval (fun j : Fin n => if j.val < n - i then 1 else x)
    (MvPolynomial.hsymm (Fin n) ℝ ell)

/-- The displayed ratio is strictly increasing above one for every specified index. -/
theorem main :
    ∀ (n ell i : ℕ), 4 ≤ n → 1 ≤ ell → 2 ≤ i → i ≤ n - 2 →
      StrictMonoOn (fun x : ℝ =>
        repeatedEvaluation n ell i x ^ 2 /
          (repeatedEvaluation n ell (i + 1) x * repeatedEvaluation n ell (i - 1) x))
        (Set.Ioi 1) := by
  sorry

end OMA.S_mo_467261
