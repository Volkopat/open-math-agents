import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.PowerSeries.Basic

/-! # OEIS A228221

Source: https://oeis.org/A228221. R. H. Hardin, conjectures by Colin Barker.
Credit: @jiyongparkphysics
-/

namespace OMA.S_oeis_a228221

abbrev Word (n : ℕ) := Fin 6 → Fin (n + 1)

/-- The 4 signed second differences in their original order. -/
def differences {n : ℕ} (w : Word n) (i : Fin 4) : ℤ :=
  (w ⟨i.val, by omega⟩).val - 2 * ((w ⟨i.val+1, by omega⟩).val : ℤ)
    + (w ⟨i.val+2, by omega⟩).val

noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Word n)).image differences).card

noncomputable def ordinary : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ))

open PowerSeries in
theorem main :
    ordinary * (1-X)^5 = X*(63 + 350*X + 456*X^2 - 30*X^3 + X^4) ∧ (∀ n : ℕ, 5 < n → (a n : ℚ) = 5*(a (n-1):ℚ) - 10*(a (n-2):ℚ) + 10*(a (n-3):ℚ) - 5*(a (n-4):ℚ) + (a (n-5):ℚ)) := by
  sorry

end OMA.S_oeis_a228221
