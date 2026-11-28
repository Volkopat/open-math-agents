import Mathlib

/-!
# MathOverflow 353633

Source: https://mathoverflow.net/questions/353633
-/

namespace OMA.S_mo_353633

open Matrix Finset

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (n k : ℕ) (x : Fin n → K),
    (Matrix.vandermonde x).rank = k → (Finset.univ.image x).card = k := by
  sorry

end OMA.S_mo_353633
