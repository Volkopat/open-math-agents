import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a316586

/-- OEIS A316586: `T(n, k)` is the number of elements `x ∈ SL(2, ZMod n)` with `x ^ k = 1`.
Conjecture: `T(p, p) = p ^ 2` for every prime `p`. -/
theorem main :
    ∀ p : ℕ, p.Prime →
      Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) // x ^ p = 1} = p ^ 2 := by
  sorry

end OMA.S_oeis_a316586
