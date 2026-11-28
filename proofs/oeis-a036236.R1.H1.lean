import OMAReductions.R_oeis_a036236_R1
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Following @ppleskov (#27071), retain the Dirichlet-prime construction and
three-modulus congruence argument. Use standard positivity, exponential bound,
and coprimality-below-a-prime lemmas for the auxiliary inequalities. -/

theorem OMA.solution : OMA.R_oeis_a036236_R1.H1 := by
  intro j hj
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨v, m, hm_odd, hj_eq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : j ≠ 0)
  have hm_pos : 0 < m := hm_odd.pos
  have htot_ne : m.totient ≠ 0 := (Nat.totient_pos.mpr hm_pos).ne'
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B (2 ^ j + j)) htot_ne (Nat.coprime_one_left m.totient)
  set k := j * p
  have hp_gtB : B < p := lt_of_le_of_lt (le_max_left _ _) hp_gt
  have hp_gt2j : 2 ^ j + j < p := lt_of_le_of_lt (le_max_right _ _) hp_gt
  have hk_gtB : B < k := by
    dsimp [k]
    calc B < p := hp_gtB
      _ = 1 * p := (one_mul p).symm
      _ ≤ j * p := Nat.mul_le_mul_right p hj
  have hk_pos : 0 < k := Nat.mul_pos (by omega) hp_prime.pos
  have h2j_lt_k : 2 ^ j < k := by
    dsimp [k]
    calc 2 ^ j < 2 ^ j + j := by omega
      _ < p := hp_gt2j
      _ = 1 * p := (one_mul p).symm
      _ ≤ j * p := Nat.mul_le_mul_right p hj
  -- Step 1: 2 ^ (j * p) ≡ 2 ^ j [MOD p]
  have hmod_p : 2 ^ k ≡ 2 ^ j [MOD p] := by
    dsimp [k]
    rw [pow_mul]
    have : Fact p.Prime := ⟨hp_prime⟩
    have hflt : ((2 ^ j : ℕ) : ZMod p) ^ p = ((2 ^ j : ℕ) : ZMod p) := ZMod.pow_card _
    rw [← ZMod.natCast_eq_natCast_iff]
    simp [Nat.cast_pow, hflt]
  -- Step 2: 2 ^ (j * p) ≡ 2 ^ j [MOD 2 ^ v]
  have hv_le_j : v ≤ j := by
    calc v ≤ 2 ^ v := (Nat.lt_two_pow_self (n := v)).le
      _ = 2 ^ v * 1 := (mul_one _).symm
      _ ≤ 2 ^ v * m := Nat.mul_le_mul_left _ hm_pos
      _ = j := hj_eq.symm
  have hv_le_k : v ≤ k := le_trans hv_le_j (Nat.le_mul_of_pos_right j hp_prime.pos)
  have hmod_2v : 2 ^ k ≡ 2 ^ j [MOD 2 ^ v] := by
    have h1 : 2 ^ k ≡ 0 [MOD 2 ^ v] := Nat.modEq_zero_iff_dvd.mpr (Nat.pow_dvd_pow 2 hv_le_k)
    have h2 : 2 ^ j ≡ 0 [MOD 2 ^ v] := Nat.modEq_zero_iff_dvd.mpr (Nat.pow_dvd_pow 2 hv_le_j)
    exact h1.trans h2.symm
  -- Step 3: 2 ^ (j * p) ≡ 2 ^ j [MOD m]
  have hmod_m : 2 ^ k ≡ 2 ^ j [MOD m] := by
    have hp1 : 1 ≤ p := hp_prime.one_le
    have htot_dvd : m.totient ∣ p - 1 := (Nat.modEq_iff_dvd' hp1).mp hp_mod.symm
    obtain ⟨t, ht⟩ := htot_dvd
    have hk_split : k = j + m.totient * (j * t) := by
      dsimp [k]
      have : p = 1 + m.totient * t := by omega
      rw [this]; ring
    rw [hk_split, pow_add, pow_mul]
    have hcop2m : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm_odd
    have heul : 2 ^ m.totient ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop2m
    have hpow : (2 ^ m.totient) ^ (j * t) ≡ 1 [MOD m] := by
      simpa using heul.pow (j * t)
    simpa using (Nat.ModEq.refl (2 ^ j)).mul hpow
  -- Combine via coprimality of 2 ^ v, m, p
  have hcop_2v_m : (2 ^ v).Coprime m := (Nat.coprime_two_left.mpr hm_odd).pow_left v
  have hmod_j : 2 ^ k ≡ 2 ^ j [MOD j] := by
    have h1 : 2 ^ k ≡ 2 ^ j [MOD 2 ^ v * m] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop_2v_m).mp ⟨hmod_2v, hmod_m⟩
    rwa [← hj_eq] at h1
  have hcop_j_p : j.Coprime p :=
    (Nat.coprime_of_lt_prime (n := j) (by omega)
      ((Nat.le_add_left j (2 ^ j)).trans_lt hp_gt2j) hp_prime).symm
  have hmod_k : 2 ^ k ≡ 2 ^ j [MOD k] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop_j_p).mp ⟨hmod_j, hmod_p⟩
  refine ⟨k, ⟨hk_pos, ?_⟩, hk_gtB⟩
  rw [Nat.ModEq, Nat.mod_eq_of_lt h2j_lt_k] at hmod_k
  exact hmod_k
