import Mathlib.Analysis.Matrix.Order

/-!
# Equality in the r = 2 Araki-Lieb-Thirring inequality

Source: https://mathoverflow.net/questions/323234
The source expressly asks for the case r = 2. For complex positive semidefinite
matrices of any finite size, equality holds exactly when the two matrices commute.
This states that requested case, without making a claim about other real exponents.
The equality criterion was explained by Mikael de la Salle in comment 806565,
and acknowledged by the asker in comment 806984.
-/

open scoped ComplexOrder

namespace OMA.S_mo_323234

theorem main :
    ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
      A.PosSemidef → B.PosSemidef →
      (((B * A * B) ^ 2).trace = (B ^ 2 * A ^ 2 * B ^ 2).trace ↔
        A * B = B * A) := by
  sorry

end OMA.S_mo_323234
