import OMAStatements.S_mse_3371305
import Mathlib

namespace DecimalPrefixes

open OMA.S_mse_3371305 Real Set

private theorem irrational_log : Irrational (logb 10 2) := by
  rintro ⟨q, hq⟩
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hc : 0 < logb (10 : ℝ) 2 := logb_pos (by norm_num) (by norm_num)
  have hcast : (q.num : ℝ) / (q.den : ℝ) = logb 10 2 := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Rat.num_div_den q)
    simpa [hq] using h
  have he : (q.num : ℝ) = logb 10 2 * q.den := (div_eq_iff hd.ne').mp hcast
  have ha : 0 < q.num := by exact_mod_cast (he ▸ mul_pos hc hd)
  have hn : (q.num.toNat : ℝ) = q.num := by exact_mod_cast Int.toNat_of_nonneg ha.le
  have hp : (10 : ℝ) ^ q.num.toNat = (2 : ℝ) ^ q.den := by
    rw [← rpow_natCast, hn, he, rpow_mul_natCast (by norm_num : 0 ≤ (10 : ℝ)),
      rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  have hp' : (10 : ℕ) ^ q.num.toNat = 2 ^ q.den := by exact_mod_cast hp
  have h5 : 5 ∣ (2 : ℕ) ^ q.den := by
    rw [← hp']
    obtain ⟨k, hk⟩ : ∃ k : ℕ, q.num.toNat = k + 1 := by
      exact Nat.exists_eq_succ_of_ne_zero (by omega)
    rw [hk, pow_succ]
    exact (show 5 ∣ (10 : ℕ) by decide).trans (dvd_mul_left _ _)
  exact (by decide : ¬ 5 ∣ (2 : ℕ)) ((by decide : Nat.Prime 5).dvd_of_dvd_pow h5)

private theorem digits_div (m j : ℕ) :
    Nat.digits 10 (m / 10 ^ j) = (Nat.digits 10 m).drop j := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', ← Nat.div_div_eq_div_mul, ih]
    by_cases h : m = 0
    · simp [h]
    · rw [Nat.digits_eq_cons_digits_div (by decide : 1 < (10 : ℕ)) h]
      rfl

private theorem leading (n : ℕ) (hn : 0 < n) :
    ∃ k j : ℕ, 2 ^ k / 10 ^ j = n := by
  let c := logb 10 2
  let Q : ℝ → AddCircle (1 : ℝ) := (↑)
  have hc : 0 < c := logb_pos (by norm_num) (by norm_num)
  have hdZ : DenseRange (fun k : ℤ => k • Q c) := by
    exact AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa [c] using irrational_log)
  have hdN : DenseRange (fun k : ℕ => Q ((k : ℝ) * c)) := by
    simpa only [Q, ← nsmul_eq_mul, AddCircle.coe_nsmul] using
      denseRange_zsmul_iff_nsmul.mp hdZ
  let a := logb 10 n
  let b := logb 10 (n + 1 : ℕ)
  have hnh : (0 : ℝ) < n := by exact_mod_cast hn
  have hab : a < b := logb_lt_logb (by norm_num) hnh (by exact_mod_cast Nat.lt_succ_self n)
  obtain ⟨m, hm⟩ := exists_nat_gt (b / c)
  have hb : b < (m : ℝ) * c := (div_lt_iff₀ hc).mp hm
  let I := Ioo (a - (m : ℝ) * c) (b - (m : ℝ) * c)
  have hopen : IsOpen (Q '' I) := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hin : (Q '' I).Nonempty := (nonempty_Ioo.mpr (sub_lt_sub_right hab _)).image _
  obtain ⟨_, ⟨x, hx, hqx⟩, ⟨k, hqk⟩⟩ := hdN.inter_open_nonempty _ hopen hin
  have heq : Q ((k : ℝ) * c - x) = 0 := by
    change ((↑((k : ℝ) * c - x)) : AddCircle (1 : ℝ)) = 0
    rw [AddCircle.coe_sub]
    change Q ((k : ℝ) * c) - Q x = 0
    change Q ((k : ℝ) * c) = _ at hqk
    rw [hqk, hqx, sub_self]
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp heq
  have hzR : (z : ℝ) = (k : ℝ) * c - x := by
    simpa only [zsmul_eq_mul, mul_one] using hz
  have hlo : a < x + (m : ℝ) * c := by linarith [hx.1]
  have hhi : x + (m : ℝ) * c < b := by linarith [hx.2]
  have hzpos : 0 < (z : ℝ) := by
    linarith [mul_nonneg (Nat.cast_nonneg k) hc.le]
  have hzN : (z.toNat : ℝ) = z := by exact_mod_cast Int.toNat_of_nonneg (by exact_mod_cast hzpos.le)
  let N := m + k
  have hs : (N : ℝ) * c = (x + (m : ℝ) * c) + (z.toNat : ℝ) := by
    dsimp [N]
    rw [Nat.cast_add, hzN, hzR]
    ring
  have hpow : (2 : ℝ) ^ N = (10 : ℝ) ^ (x + (m : ℝ) * c) * (10 : ℝ) ^ z.toNat := by
    rw [← rpow_natCast (10 : ℝ) z.toNat, ← rpow_add (by norm_num : 0 < (10 : ℝ)), ← hs]
    dsimp [c]
    rw [← logb_pow, rpow_logb (by norm_num) (by norm_num) (by positivity)]
  have h₁ : (n : ℝ) < (10 : ℝ) ^ (x + (m : ℝ) * c) := by
    rw [← rpow_logb (by norm_num : 0 < (10 : ℝ)) (by norm_num) hnh]
    exact rpow_lt_rpow_of_exponent_lt (by norm_num) hlo
  have h₂ : (10 : ℝ) ^ (x + (m : ℝ) * c) < (n + 1 : ℕ) := by
    rw [← rpow_logb (by norm_num : 0 < (10 : ℝ)) (by norm_num)
      (show (0 : ℝ) < (n + 1 : ℕ) by positivity)]
    exact rpow_lt_rpow_of_exponent_lt (by norm_num) hhi
  refine ⟨N, z.toNat, Nat.div_eq_of_lt_le ?_ ?_⟩
  · exact_mod_cast ((mul_lt_mul_of_pos_right h₁ (show (0 : ℝ) < 10 ^ z.toNat by positivity)).le.trans_eq hpow.symm)
  · exact_mod_cast (hpow.trans_lt (mul_lt_mul_of_pos_right h₂ (show (0 : ℝ) < 10 ^ z.toNat by positivity)))

theorem prove (n : ℕ) : ∃ k : ℕ, digs n <:+: digs (2 ^ k) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨10, by decide⟩
  · obtain ⟨k, j, h⟩ := leading n (Nat.pos_of_ne_zero hn)
    have hdrop := digits_div (2 ^ k) j
    rw [h] at hdrop
    refine ⟨k, ?_⟩
    simpa [digs, hn, pow_ne_zero k (by decide : (2 : ℕ) ≠ 0), hdrop] using
      (List.drop_suffix j (Nat.digits 10 (2 ^ k))).isInfix

end DecimalPrefixes

theorem OMA.solution : type_of% @OMA.S_mse_3371305.main := DecimalPrefixes.prove