import Mathlib

/-!
# MO 23163: independence for Beatty sequences

Source: https://mathoverflow.net/questions/23163

For every positive n we ask for real algebraic numbers alpha_i such that every
nonzero integer polynomial in n variables has only finitely many integer zeros when
evaluated at the floors of alpha_i*x.  The source states that n = 2 is known and
asks about n = 3; the statement below is the full question.  Only the body of `main`
is `sorry`; all definitions are Mathlib's.
-/

namespace OMA.S_mo_23163

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ α : Fin n → ℝ,
        (∀ i, IsAlgebraic ℚ (α i)) ∧
          ∀ p : MvPolynomial (Fin n) ℤ, p ≠ 0 →
            {x : ℤ | MvPolynomial.eval (fun i => ⌊α i * (x : ℝ)⌋) p = 0}.Finite := by
  sorry

end OMA.S_mo_23163
