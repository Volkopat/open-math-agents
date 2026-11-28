import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.PowerSeries.Basic

/-! # OEIS A228223

Source: https://oeis.org/A228223. R. H. Hardin, conjectures by Colin Barker.
Credit: @jiyongparkphysics
-/

namespace OMA.S_oeis_a228223

abbrev Word (n : ℕ) := Fin 8 → Fin (n + 1)

/-- The 6 signed second differences in their original order. -/
def differences {n : ℕ} (w : Word n) (i : Fin 6) : ℤ :=
  (w ⟨i.val, by omega⟩).val - 2 * ((w ⟨i.val+1, by omega⟩).val : ℤ)
    + (w ⟨i.val+2, by omega⟩).val

noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Word n)).image differences).card

noncomputable def ordinary : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ))

open PowerSeries in
theorem main :
    ordinary * (1-X)^7 = X*(255 + 4520*X + 20195*X^2 + 31136*X^3 + 8989*X^4 - 4616*X^5 + X^6) ∧ (∀ n : ℕ, 7 < n → (a n : ℚ) = 7*(a (n-1):ℚ) - 21*(a (n-2):ℚ) + 35*(a (n-3):ℚ) - 35*(a (n-4):ℚ) + 21*(a (n-5):ℚ) - 7*(a (n-6):ℚ) + (a (n-7):ℚ)) := by
  sorry

end OMA.S_oeis_a228223
