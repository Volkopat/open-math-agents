import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.PowerSeries.Basic

/-! # OEIS A228224

Source: https://oeis.org/A228224. R. H. Hardin, conjectures by Colin Barker.
Credit: @jiyongparkphysics
-/

namespace OMA.S_oeis_a228224

abbrev Word (n : ℕ) := Fin 9 → Fin (n + 1)

/-- The 7 signed second differences in their original order. -/
def differences {n : ℕ} (w : Word n) (i : Fin 7) : ℤ :=
  (w ⟨i.val, by omega⟩).val - 2 * ((w ⟨i.val+1, by omega⟩).val : ℤ)
    + (w ⟨i.val+2, by omega⟩).val

noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Word n)).image differences).card

noncomputable def ordinary : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ))

open PowerSeries in
theorem main :
    ordinary * (1-X)^8 = X*(511 + 15083*X + 103401*X^2 + 256585*X^3 + 252785*X^4 + 16749*X^5 - 40313*X^6 - X^7) ∧ (∀ n : ℕ, 8 < n → (a n : ℚ) = 8*(a (n-1):ℚ) - 28*(a (n-2):ℚ) + 56*(a (n-3):ℚ) - 70*(a (n-4):ℚ) + 56*(a (n-5):ℚ) - 28*(a (n-6):ℚ) + 8*(a (n-7):ℚ) - (a (n-8):ℚ)) := by
  sorry

end OMA.S_oeis_a228224
