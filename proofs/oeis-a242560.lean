import OMAStatements.S_oeis_a242560
import Mathlib

open OMA.S_oeis_a242560 in
theorem OMA.solution : type_of% @OMA.S_oeis_a242560.main := by
  intro n hn
  refine ⟨⟨by omega, by omega, ?_⟩, ?_⟩
  · apply Int.emod_eq_zero_of_dvd
    have h1 : ((2 * n : ℕ) : ℤ) - (n : ℤ) = (n : ℤ) := by push_cast; ring
    rw [h1]
    refine dvd_sub ?_ (dvd_refl _)
    exact_mod_cast Nat.dvd_factorial (by omega) (by omega : n ≤ 2 * n)
  · rintro k ⟨hk0, hkn, hd⟩
    by_contra hlt
    push_neg at hlt
    have hd' : ((2 * n : ℕ) : ℤ) - (k : ℤ) ∣ (((2 * n).factorial : ℕ) : ℤ) - (k : ℤ) :=
      Int.dvd_of_emod_eq_zero hd
    have hf : ((2 * n : ℕ) : ℤ) - (k : ℤ) ∣ (((2 * n).factorial : ℕ) : ℤ) := by
      have h2 : (2 * n - k) ∣ (2 * n).factorial := Nat.dvd_factorial (by omega) (by omega)
      rw [← Nat.cast_sub (show k ≤ 2 * n by omega)]
      exact_mod_cast h2
    have h3 := dvd_sub hf hd'
    rw [sub_sub_cancel] at h3
    have hpos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk0
    have h4 := Int.le_of_dvd hpos h3
    push_cast at h4
    omega
