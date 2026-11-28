import OMAStatements.S_oeis_a143727
import Mathlib

open OMA.S_oeis_a143727

private theorem smallPrime {q m : ℕ} (hq : 2 ≤ q) (hm : m.Prime) (hd : q ∣ m) : q = m :=
  (Nat.dvd_prime_two_le hm hq).mp hd

theorem OMA.solution : type_of% @OMA.S_oeis_a143727.main := by
  intro n h
  by_cases hn : n < 14
  · interval_cases n <;> norm_num [IsNearPrime, Nat.prime_def_lt] at h
  obtain ⟨hm2, hp2, hm4, hp4, _, _⟩ := h
  have h3 : n % 3 = 0 := by
    by_contra hn3
    by_cases h1 : n % 3 = 1
    · have hd : 3 ∣ n + 2 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      have := smallPrime (by decide) hp2 hd
      omega
    · have hd : 3 ∣ n + 4 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      have := smallPrime (by decide) hp4 hd
      omega
  have h5 : n % 5 = 0 := by
    by_contra hn5
    have hbound : n % 5 < 5 := Nat.mod_lt _ (by decide)
    interval_cases h : n % 5
    · omega
    · have hd : 5 ∣ n + 4 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      have := smallPrime (by decide) hp4 hd
      omega
    · have hd : 5 ∣ n - 2 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      have := smallPrime (by decide) hm2 hd
      omega
    · have hd : 5 ∣ n + 2 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      have := smallPrime (by decide) hp2 hd
      omega
    · have hd : 5 ∣ n - 4 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      have := smallPrime (by decide) hm4 hd
      omega
  exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)