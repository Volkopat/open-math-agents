import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.PowerSeries.Basic

/-! # OEIS A228220

Source: https://oeis.org/A228220. R. H. Hardin, conjectures by Colin Barker.
Credit: @jiyongparkphysics
-/

namespace OMA.S_oeis_a228220

abbrev Word (n : ℕ) := Fin 5 → Fin (n + 1)

/-- The 3 signed second differences in their original order. -/
def differences {n : ℕ} (w : Word n) (i : Fin 3) : ℤ :=
  (w ⟨i.val, by omega⟩).val - 2 * ((w ⟨i.val+1, by omega⟩).val : ℤ)
    + (w ⟨i.val+2, by omega⟩).val

noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Word n)).image differences).card

noncomputable def ordinary : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ))

open PowerSeries in
theorem main :
    ordinary * (1-X)^4 = X*(31 + 75*X + 15*X^2 - X^3) ∧ (∀ n : ℕ, 4 < n → (a n : ℚ) = 4*(a (n-1):ℚ) - 6*(a (n-2):ℚ) + 4*(a (n-3):ℚ) - (a (n-4):ℚ)) := by
  sorry

end OMA.S_oeis_a228220
