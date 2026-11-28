import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.PowerSeries.Basic

/-! # OEIS A228222

Source: https://oeis.org/A228222. Sequence by R. H. Hardin, conjectures by Colin Barker.
Credit: @jiyongparkphysics

The entries range independently from 0 through n. Their five signed second
differences are recorded in order, and equal vectors are counted once. The
generating function begins at n = 1, as in OEIS.
-/

namespace OMA.S_oeis_a228222

abbrev Word (n : ℕ) := Fin 7 → Fin (n + 1)

/-- The five signed second differences in their original order. -/
def differences {n : ℕ} (w : Word n) (i : Fin 5) : ℤ :=
  (w ⟨i.val, by omega⟩).val - 2 * ((w ⟨i.val+1, by omega⟩).val : ℤ)
    + (w ⟨i.val+2, by omega⟩).val

noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Word n)).image differences).card

noncomputable def ordinary : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ))

open PowerSeries in
theorem main :
    ordinary * (1-X)^6 =
      X*(127+1297*X+3604*X^2+2168*X^3-475*X^4-X^5) ∧
    (∀ n : ℕ, 6 < n → (a n : ℚ) =
      6*(a (n-1):ℚ) - 15*(a (n-2):ℚ) + 20*(a (n-3):ℚ)
      - 15*(a (n-4):ℚ) + 6*(a (n-5):ℚ) - (a (n-6):ℚ)) := by
  sorry

end OMA.S_oeis_a228222
