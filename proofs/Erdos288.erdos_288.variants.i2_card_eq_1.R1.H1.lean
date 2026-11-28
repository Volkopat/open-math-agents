import OMAReductions.R_Erdos288_erdos_288_variants_i2_card_eq_1_R1
import Mathlib

-- Step Erdos288.erdos_288.variants.i2_card_eq_1.R1.H1: hypothesis H1 of reduction Erdos288.erdos_288.variants.i2_card_eq_1.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! If r + 1/d = z then r = (z d - 1)/d, and gcd(z d - 1, d) = 1, so den r = d and num r + 1 = z d.
Conversely, if den r = d divides num r + 1, then r + 1/d = (num r + 1)/d is an integer. -/

theorem OMA.solution : OMA.R_Erdos288_erdos_288_variants_i2_card_eq_1_R1.H1 := by
  intro r d
  have hd : (0 : ℤ) < d := by exact_mod_cast d.pos
  have hdq : (d : ℚ) ≠ 0 := by positivity
  constructor
  · rintro ⟨z, hz⟩
    have hr : r = ((z * d - 1 : ℤ) : ℚ) / ((d : ℤ) : ℚ) := by
      rw [eq_div_iff (by positivity)]
      push_cast
      field_simp at hz
      linarith
    have hcop : Nat.Coprime (z * d - 1 : ℤ).natAbs (d : ℤ).natAbs := by
      have h : IsCoprime (z * d - 1 : ℤ) (d : ℤ) := ⟨-1, z, by ring⟩
      simpa only [Int.gcd_eq_natAbs] using Int.isCoprime_iff_gcd_eq_one.mp h
    have hden := Rat.den_div_eq_of_coprime (a := z * d - 1) (b := (d : ℤ)) hd hcop
    have hnum := Rat.num_div_eq_of_coprime (a := z * d - 1) (b := (d : ℤ)) hd hcop
    rw [← hr] at hden hnum
    refine ⟨by exact_mod_cast hden, ?_⟩
    rw [hden, hnum]
    exact ⟨z, by ring⟩
  · rintro ⟨hden, ⟨k, hk⟩⟩
    rw [hden] at hk
    have hk' : (r.num : ℚ) + 1 = (d : ℚ) * k := by exact_mod_cast hk
    refine ⟨k, ?_⟩
    rw [← Rat.num_div_den r, hden]
    field_simp
    linarith
