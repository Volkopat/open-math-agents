import Mathlib

/-!
# Rainbow AP(4) in an almost equinumerous coloring

Source: https://www.openproblemgarden.org/op/rainbow_ap_4_in_an_almost_equinumerous_coloring
Credit: @datdzrgb
-/

namespace OMA.S_opg_rainbow_ap_4_in_an_almost_equinumerous_coloring

def AlmostEquinumerous {p : ℕ} (col : ZMod p → Fin 4) : Prop :=
  ∀ k : Fin 4, let size := Set.ncard {x | col x = k}
    size = p / 4 ∨ size = (p + 3) / 4

/-- Every almost equinumerous four-coloring of the integers modulo a sufficiently
large prime has a rainbow four-term arithmetic progression. -/
theorem main :
    ∃ N : ℕ, ∀ p : ℕ, N ≤ p → p.Prime → ∀ col : ZMod p → Fin 4, AlmostEquinumerous col →
      ∃ a r : ZMod p, r ≠ 0 ∧ Function.Injective (fun i : Fin 4 => col (a + i.val * r)) := by
  sorry

end OMA.S_opg_rainbow_ap_4_in_an_almost_equinumerous_coloring
