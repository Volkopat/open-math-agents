import OMAStatements.S_oeis_a253247
import Mathlib.Tactic

namespace A253247
open OMA.S_oeis_a253247 Function

-- The only prime divisors of 484 are 2 and 11. Thus every
-- proper divisor of 484 divides 484/2 or 484/11.
private lemma smaller_divisors : ∀ d : Fin 485,
    (d : ℕ) ∣ 484 → (d : ℕ) ≠ 484 → (d : ℕ) ∣ 242 ∨ (d : ℕ) ∣ 44 := by
  decide +kernel

private lemma certified_period (m : ℕ)
    (h : IsPeriodicPt (step m) 484 (0,1))
    (h2 : ¬ IsPeriodicPt (step m) 242 (0,1))
    (h11 : ¬ IsPeriodicPt (step m) 44 (0,1)) : period m = 484 := by
  have hd : period m ∣ 484 := h.minimalPeriod_dvd
  by_contra hne
  have hlt : period m < 485 := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)
  rcases smaller_divisors ⟨period m,hlt⟩ hd hne with hdiv | hdiv
  · exact h2 (isPeriodicPt_iff_minimalPeriod_dvd.mpr hdiv)
  · exact h11 (isPeriodicPt_iff_minimalPeriod_dvd.mpr hdiv)

end A253247

open OMA.S_oeis_a253247 A253247 Function in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a253247.main) := by
  intro h
  have h1 : period 241 = 484 := by
    apply certified_period
    all_goals
      simp only [IsPeriodicPt, IsFixedPt]
      decide +kernel
  have h2 : period (241^2) = 484 := by
    apply certified_period
    all_goals
      simp only [IsPeriodicPt, IsFixedPt]
      decide +kernel
  have hfrac : (period (241^2) : ℚ) / (period 241 : ℚ) = 1 := by
    rw [h1,h2]
    norm_num
  exact (by decide : ¬ (241 = (1 : ℕ) ∨ 241 = 6)) ((h 241 (by decide)).mp hfrac)
