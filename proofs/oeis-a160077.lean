import OMAStatements.S_oeis_a160077
import Mathlib

open OMA.S_oeis_a160077 in
theorem OMA.solution : type_of% @OMA.S_oeis_a160077.main := by
  have h19 : (19 : ZMod 13) ≠ 0 := by decide
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hrec : ∀ n : ℕ, hermiteAt (19 / 26) (n + 2)
      = 2 * (19 / 26) * hermiteAt (19 / 26) (n + 1)
        - 2 * ((n : ℚ) + 1) * hermiteAt (19 / 26) n := by
    intro n
    first | rfl | rw [hermiteAt] | simp only [hermiteAt]
  have h338 : (338 : ZMod 13) = 0 := by first | decide | rfl
  have P : ∀ n : ℕ,
      (∃ z : ℤ, (13 : ℚ) ^ n * hermiteAt (19 / 26) n = z ∧ (z : ZMod 13) = 19 ^ n) ∧
      (∃ z : ℤ, (13 : ℚ) ^ (n + 1) * hermiteAt (19 / 26) (n + 1) = z ∧
        (z : ZMod 13) = 19 ^ (n + 1)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨⟨1, ?_, ?_⟩, ⟨19, ?_, ?_⟩⟩
      · show (13 : ℚ) ^ 0 * 1 = ((1 : ℤ) : ℚ)
        norm_num
      · first | simp | norm_num
      · show (13 : ℚ) ^ (0 + 1) * (2 * (19 / 26)) = ((19 : ℤ) : ℚ)
        norm_num
      · first | simp | norm_num
    | succ k ih =>
      obtain ⟨⟨z0, h0, m0⟩, ⟨z1, h1, m1⟩⟩ := ih
      refine ⟨⟨z1, h1, m1⟩, ⟨19 * z1 - 338 * ((k : ℤ) + 1) * z0, ?_, ?_⟩⟩
      · show (13 : ℚ) ^ (k + 2) * hermiteAt (19 / 26) (k + 2)
            = ((19 * z1 - 338 * ((k : ℤ) + 1) * z0 : ℤ) : ℚ)
        rw [hrec k]
        push_cast
        linear_combination 19 * h1 - 338 * ((k : ℚ) + 1) * h0
      · push_cast
        linear_combination 19 * m1 - ((k : ZMod 13) + 1) * (z0 : ZMod 13) * h338
  have key : ∀ n : ℕ, (13 : ℚ) ^ n * hermiteAt (19 / 26) n = (a n : ℚ) := by
    intro n
    obtain ⟨z, hz, hm⟩ := (P n).1
    have hnd : ¬ (13 : ℤ) ∣ z := by
      intro hd
      have h0 : (z : ZMod 13) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z 13).mpr hd
      rw [hm] at h0
      exact pow_ne_zero n h19 h0
    have hH : hermiteAt (19 / 26) n = (z : ℚ) / ((13 ^ n : ℤ) : ℚ) := by
      rw [eq_div_iff (by positivity)]
      push_cast
      linear_combination hz
    have hcop : Nat.Coprime z.natAbs (13 ^ n : ℤ).natAbs := by
      rw [Int.natAbs_pow]
      apply Nat.Coprime.pow_right
      show Nat.Coprime z.natAbs 13
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
      intro hd
      first
        | exact hnd (Int.ofNat_dvd_left.mpr hd)
        | exact hnd ((Int.natAbs_dvd_natAbs (a := 13) (b := z)).mp hd)
    have ha : a n = z := by
      show (hermiteAt (19 / 26) n).num = z
      rw [hH]
      exact Rat.num_div_eq_of_coprime (by positivity) hcop
    rw [ha]
    exact hz
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 2 - 2 = k := by omega
  rw [e1, e2]
  have q0 := key k
  have q1 := key (k + 1)
  have q2 := key (k + 2)
  rw [hrec k] at q2
  have h : ((a (k + 2) - 19 * a (k + 1) + 338 * (((k + 2 : ℕ) : ℤ) - 1) * a k : ℤ) : ℚ) = 0 := by
    push_cast
    linear_combination -q2 + 19 * q1 - 338 * ((k : ℚ) + 1) * q0
  exact_mod_cast h
