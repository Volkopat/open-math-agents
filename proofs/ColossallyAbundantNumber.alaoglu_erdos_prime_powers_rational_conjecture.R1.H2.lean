import OMAReductions.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1
import Mathlib.NumberTheory.Padics.PadicVal.Basic

-- Applying the p-adic valuation to r ^ t.den = p ^ t.num recovers the exponent.
theorem OMA.solution :
    OMA.R_ColossallyAbundantNumber_alaoglu_erdos_prime_powers_rational_conjecture_R1.H2 := by
  intro p t hp ⟨r, hr⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have ht : (t : ℝ) * (t.den : ℝ) = (t.num : ℝ) := by
    exact_mod_cast Rat.mul_den_eq_num t
  have heq : (r : ℝ) ^ t.den = (p : ℝ) ^ t.num := by
    rw [← hr, ← Real.rpow_mul_natCast hp0, ht, Real.rpow_intCast]
  have hrat : r ^ t.den = (p : ℚ) ^ t.num := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact heq
  have hv := congrArg (padicValRat p) hrat
  rw [padicValRat.pow, padicValRat.zpow, padicValRat.self hp.one_lt, mul_one] at hv
  refine ⟨padicValRat p r, ?_⟩
  apply (mul_left_inj' (show (t.den : ℚ) ≠ 0 by positivity)).mp
  calc
    t * t.den = (t.num : ℚ) := Rat.mul_den_eq_num t
    _ = (padicValRat p r : ℚ) * t.den := by
      exact_mod_cast hv.symm.trans (mul_comm _ _)
