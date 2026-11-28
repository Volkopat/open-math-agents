import OMAStatements.S_oeis_a184634

-- Problem: A184634: a(n) = floor(1/{(10+n^4)^(1/4)}), where {}=fractional part.
-- Upstream: formal-conjectures statements/oeis-a184634.lean:0 (declaration OMA.S_oeis_a184634.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (Robert Israel's argument in the entry): y = (10+n^4)^(1/4) satisfies y^4 = n^4 + 10,
-- so n < y < n+1 and d = {y} = y - n satisfies d*S = 10 with S = 4n^3+6n^2d+4nd^2+d^3. Hence
-- 1/d = S/10 lies strictly between 2n^3/5 and 2n^3/5 + 3/(2n). This fixes the floor in each
-- residue class mod 5; then 5*a(n) = 2n^3 - c(n mod 5) for n >= 4 gives the recurrence.

namespace M03A184634

open OMA.S_oeis_a184634

theorem bounds (n : ℕ) (hn : 1 ≤ n) :
    2 * (n : ℝ) ^ 3 / 5 < 1 / Int.fract (((10 : ℝ) + (n : ℝ) ^ 4) ^ ((1 : ℝ) / 4)) ∧
      1 / Int.fract (((10 : ℝ) + (n : ℝ) ^ 4) ^ ((1 : ℝ) / 4)) <
        2 * (n : ℝ) ^ 3 / 5 + 3 / (2 * (n : ℝ)) := by
  have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith [hN]
  have hB : (0 : ℝ) ≤ 10 + (n : ℝ) ^ 4 := by positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((10 : ℝ) + (n : ℝ) ^ 4) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hy]
  have hy0 : 0 ≤ y := by
    rw [hy]
    exact Real.rpow_nonneg hB _
  have hy4 : y ^ 4 = 10 + (n : ℝ) ^ 4 := by
    have h1 : y ^ ((4 : ℕ) : ℝ) = y ^ 4 := Real.rpow_natCast y 4
    have h2 : y ^ ((4 : ℕ) : ℝ) = (10 + (n : ℝ) ^ 4) ^ ((1 : ℝ) / 4 * ((4 : ℕ) : ℝ)) := by
      rw [hy, Real.rpow_mul hB]
    rw [← h1, h2, show (1 : ℝ) / 4 * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hp1 : 0 ≤ (n : ℝ) ^ 3 + (n : ℝ) ^ 2 * y + (n : ℝ) * y ^ 2 + y ^ 3 := by
    have h1 := pow_nonneg hN0.le 3
    have h2 := mul_nonneg (pow_nonneg hN0.le 2) hy0
    have h3 := mul_nonneg hN0.le (pow_nonneg hy0 2)
    have h4 := pow_nonneg hy0 3
    linarith [h1, h2, h3, h4]
  have hlt : (n : ℝ) < y := by
    by_contra h
    have hle : y ≤ (n : ℝ) := not_lt.mp h
    have hm := mul_nonneg (sub_nonneg.mpr hle) hp1
    have e : ((n : ℝ) - y) * ((n : ℝ) ^ 3 + (n : ℝ) ^ 2 * y + (n : ℝ) * y ^ 2 + y ^ 3) = -10 := by
      linear_combination (-1 : ℝ) * hy4
    linarith [hm, e]
  have hM0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith [hN0]
  have hp2 : 0 ≤ y ^ 3 + y ^ 2 * ((n : ℝ) + 1) + y * ((n : ℝ) + 1) ^ 2 + ((n : ℝ) + 1) ^ 3 := by
    have h1 := pow_nonneg hy0 3
    have h2 := mul_nonneg (pow_nonneg hy0 2) hM0
    have h3 := mul_nonneg hy0 (pow_nonneg hM0 2)
    have h4 := pow_nonneg hM0 3
    linarith [h1, h2, h3, h4]
  have hN2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hN
  have hN3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hN
  have hlt2 : y < (n : ℝ) + 1 := by
    by_contra h
    have hle : (n : ℝ) + 1 ≤ y := not_lt.mp h
    have hm := mul_nonneg (sub_nonneg.mpr hle) hp2
    have e : (y - ((n : ℝ) + 1)) *
        (y ^ 3 + y ^ 2 * ((n : ℝ) + 1) + y * ((n : ℝ) + 1) ^ 2 + ((n : ℝ) + 1) ^ 3) =
        9 - 4 * (n : ℝ) ^ 3 - 6 * (n : ℝ) ^ 2 - 4 * (n : ℝ) := by
      linear_combination hy4
    linarith [hm, e, hN, hN2, hN3]
  have hfr : Int.fract y = y - (n : ℝ) := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith [hlt], by linarith [hlt2], n, ?_⟩
    rw [Int.cast_natCast]
    ring
  rw [hfr]
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = y - (n : ℝ) := ⟨_, rfl⟩
  rw [← hdd]
  have hd : 0 < d := by
    rw [hdd]
    linarith [hlt]
  have hS : d * (4 * (n : ℝ) ^ 3 + 6 * (n : ℝ) ^ 2 * d + 4 * (n : ℝ) * d ^ 2 + d ^ 3) = 10 := by
    rw [hdd]
    linear_combination hy4
  have hinv : 1 / d =
      (4 * (n : ℝ) ^ 3 + 6 * (n : ℝ) ^ 2 * d + 4 * (n : ℝ) * d ^ 2 + d ^ 3) / 10 := by
    rw [div_eq_div_iff hd.ne' (by norm_num)]
    linear_combination (-1 : ℝ) * hS
  rw [hinv]
  have q1 : 0 < 6 * (n : ℝ) ^ 2 * d := mul_pos (mul_pos (by norm_num) (pow_pos hN0 2)) hd
  have q2 : 0 < 4 * (n : ℝ) * d ^ 2 := mul_pos (mul_pos (by norm_num) hN0) (pow_pos hd 2)
  have q3 : 0 < d ^ 3 := pow_pos hd 3
  have e : 15 - (n : ℝ) * (6 * (n : ℝ) ^ 2 * d + 4 * (n : ℝ) * d ^ 2 + d ^ 3) =
      5 * (n : ℝ) ^ 2 * d ^ 2 + 5 * (n : ℝ) * d ^ 3 + 3 / 2 * d ^ 4 := by
    linear_combination (-3 / 2 : ℝ) * hS
  have r1 : 0 < 5 * (n : ℝ) ^ 2 * d ^ 2 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hN0 2)) (pow_pos hd 2)
  have r2 : 0 < 5 * (n : ℝ) * d ^ 3 := mul_pos (mul_pos (by norm_num) hN0) (pow_pos hd 3)
  have r3 : 0 < 3 / 2 * d ^ 4 := mul_pos (by norm_num) (pow_pos hd 4)
  have hkey : (n : ℝ) * (6 * (n : ℝ) ^ 2 * d + 4 * (n : ℝ) * d ^ 2 + d ^ 3) < 15 := by
    linarith [e, r1, r2, r3]
  have h3 : (6 * (n : ℝ) ^ 2 * d + 4 * (n : ℝ) * d ^ 2 + d ^ 3) / 10 < 3 / (2 * (n : ℝ)) := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith [hN0])]
    have e2 : (6 * (n : ℝ) ^ 2 * d + 4 * (n : ℝ) * d ^ 2 + d ^ 3) * (2 * (n : ℝ)) =
        2 * ((n : ℝ) * (6 * (n : ℝ) ^ 2 * d + 4 * (n : ℝ) * d ^ 2 + d ^ 3)) := by
      ring
    linarith [e2, hkey]
  constructor
  · linarith [q1, q2, q3]
  · linarith [h3]

theorem floor_eq (n : ℕ) (hn : 1 ≤ n) (P : ℤ) (h1 : (P : ℝ) ≤ 2 * (n : ℝ) ^ 3 / 5)
    (h2 : 2 * (n : ℝ) ^ 3 / 5 + 3 / (2 * (n : ℝ)) ≤ (P : ℝ) + 1) : a n = P := by
  have hb := bounds n hn
  unfold a
  rw [Int.floor_eq_iff]
  exact ⟨by linarith [hb.1, h1], by linarith [hb.2, h2]⟩

theorem f0 (k : ℕ) (hk : 1 ≤ k) : a (5 * k) = 50 * (k : ℤ) ^ 3 := by
  have hK : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have e : 2 * (5 * (k : ℝ)) ^ 3 / 5 = 50 * (k : ℝ) ^ 3 := by ring
  have hq : 3 / (2 * (5 * (k : ℝ))) ≤ 1 := by
    rw [div_le_iff₀ (by linarith [hK])]
    linarith [hK]
  apply floor_eq (5 * k) (by omega)
  · push_cast
    linarith [e]
  · push_cast
    linarith [e, hq]

theorem f1 (k : ℕ) (hk : 1 ≤ k) :
    a (5 * k + 1) = 50 * (k : ℤ) ^ 3 + 30 * (k : ℤ) ^ 2 + 6 * (k : ℤ) := by
  have hK : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have e : 2 * (5 * (k : ℝ) + 1) ^ 3 / 5 =
      50 * (k : ℝ) ^ 3 + 30 * (k : ℝ) ^ 2 + 6 * (k : ℝ) + 2 / 5 := by ring
  have hq : 3 / (2 * (5 * (k : ℝ) + 1)) ≤ 3 / 5 := by
    rw [div_le_iff₀ (by linarith [hK])]
    linarith [hK]
  apply floor_eq (5 * k + 1) (by omega)
  · push_cast
    linarith [e]
  · push_cast
    linarith [e, hq]

theorem f2 (k : ℕ) :
    a (5 * k + 2) = 50 * (k : ℤ) ^ 3 + 60 * (k : ℤ) ^ 2 + 24 * (k : ℤ) + 3 := by
  have hK : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have e : 2 * (5 * (k : ℝ) + 2) ^ 3 / 5 =
      50 * (k : ℝ) ^ 3 + 60 * (k : ℝ) ^ 2 + 24 * (k : ℝ) + 3 + 1 / 5 := by ring
  have hq : 3 / (2 * (5 * (k : ℝ) + 2)) ≤ 4 / 5 := by
    rw [div_le_iff₀ (by linarith [hK])]
    linarith [hK]
  apply floor_eq (5 * k + 2) (by omega)
  · push_cast
    linarith [e]
  · push_cast
    linarith [e, hq]

theorem f3 (k : ℕ) (hk : 1 ≤ k) :
    a (5 * k + 3) = 50 * (k : ℤ) ^ 3 + 90 * (k : ℤ) ^ 2 + 54 * (k : ℤ) + 10 := by
  have hK : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have e : 2 * (5 * (k : ℝ) + 3) ^ 3 / 5 =
      50 * (k : ℝ) ^ 3 + 90 * (k : ℝ) ^ 2 + 54 * (k : ℝ) + 10 + 4 / 5 := by ring
  have hq : 3 / (2 * (5 * (k : ℝ) + 3)) ≤ 1 / 5 := by
    rw [div_le_iff₀ (by linarith [hK])]
    linarith [hK]
  apply floor_eq (5 * k + 3) (by omega)
  · push_cast
    linarith [e]
  · push_cast
    linarith [e, hq]

theorem f4 (k : ℕ) :
    a (5 * k + 4) = 50 * (k : ℤ) ^ 3 + 120 * (k : ℤ) ^ 2 + 96 * (k : ℤ) + 25 := by
  have hK : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have e : 2 * (5 * (k : ℝ) + 4) ^ 3 / 5 =
      50 * (k : ℝ) ^ 3 + 120 * (k : ℝ) ^ 2 + 96 * (k : ℝ) + 25 + 3 / 5 := by ring
  have hq : 3 / (2 * (5 * (k : ℝ) + 4)) ≤ 2 / 5 := by
    rw [div_le_iff₀ (by linarith [hK])]
    linarith [hK]
  apply floor_eq (5 * k + 4) (by omega)
  · push_cast
    linarith [e]
  · push_cast
    linarith [e, hq]

/-- The correction term: 5 * a(n) = 2 * n^3 - c(n) for n >= 4. -/
def c (n : ℕ) : ℤ :=
  if n % 5 = 0 then 0 else if n % 5 = 1 then 2 else if n % 5 = 2 then 1 else
    if n % 5 = 3 then 4 else 3

theorem cper (j : ℕ) : c (j + 5) = c j := by
  unfold c
  rw [show (j + 5) % 5 = j % 5 by omega]

theorem closed (n : ℕ) (hn : 4 ≤ n) : 5 * a n = 2 * (n : ℤ) ^ 3 - c n := by
  obtain ⟨k, h | h | h | h | h⟩ : ∃ k, n = 5 * k ∨ n = 5 * k + 1 ∨ n = 5 * k + 2 ∨
      n = 5 * k + 3 ∨ n = 5 * k + 4 := ⟨n / 5, by omega⟩
  · subst h
    have hc : c (5 * k) = 0 := by
      unfold c
      rw [if_pos (show 5 * k % 5 = 0 by omega)]
    rw [f0 k (by omega), hc]
    push_cast
    ring
  · subst h
    have hc : c (5 * k + 1) = 2 := by
      unfold c
      rw [if_neg (show ¬ ((5 * k + 1) % 5 = 0) by omega),
        if_pos (show (5 * k + 1) % 5 = 1 by omega)]
    rw [f1 k (by omega), hc]
    push_cast
    ring
  · subst h
    have hc : c (5 * k + 2) = 1 := by
      unfold c
      rw [if_neg (show ¬ ((5 * k + 2) % 5 = 0) by omega),
        if_neg (show ¬ ((5 * k + 2) % 5 = 1) by omega),
        if_pos (show (5 * k + 2) % 5 = 2 by omega)]
    rw [f2 k, hc]
    push_cast
    ring
  · subst h
    have hc : c (5 * k + 3) = 4 := by
      unfold c
      rw [if_neg (show ¬ ((5 * k + 3) % 5 = 0) by omega),
        if_neg (show ¬ ((5 * k + 3) % 5 = 1) by omega),
        if_neg (show ¬ ((5 * k + 3) % 5 = 2) by omega),
        if_pos (show (5 * k + 3) % 5 = 3 by omega)]
    rw [f3 k (by omega), hc]
    push_cast
    ring
  · subst h
    have hc : c (5 * k + 4) = 3 := by
      unfold c
      rw [if_neg (show ¬ ((5 * k + 4) % 5 = 0) by omega),
        if_neg (show ¬ ((5 * k + 4) % 5 = 1) by omega),
        if_neg (show ¬ ((5 * k + 4) % 5 = 2) by omega),
        if_neg (show ¬ ((5 * k + 4) % 5 = 3) by omega)]
    rw [f4 k, hc]
    push_cast
    ring

theorem recur (n : ℕ) (hn : 12 ≤ n) : a n = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) +
    a (n - 5) - 3 * a (n - 6) + 3 * a (n - 7) - a (n - 8) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  rw [show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega,
    show m + 12 - 3 = m + 9 by omega, show m + 12 - 5 = m + 7 by omega,
    show m + 12 - 6 = m + 6 by omega, show m + 12 - 7 = m + 5 by omega,
    show m + 12 - 8 = m + 4 by omega]
  have h12 := closed (m + 12) (by omega)
  have h11 := closed (m + 11) (by omega)
  have h10 := closed (m + 10) (by omega)
  have h9 := closed (m + 9) (by omega)
  have h7 := closed (m + 7) (by omega)
  have h6 := closed (m + 6) (by omega)
  have h5 := closed (m + 5) (by omega)
  have h4 := closed (m + 4) (by omega)
  have e12 : c (m + 12) = c (m + 7) := by
    have h := cper (m + 7)
    rw [show m + 7 + 5 = m + 12 by omega] at h
    exact h
  have e11 : c (m + 11) = c (m + 6) := by
    have h := cper (m + 6)
    rw [show m + 6 + 5 = m + 11 by omega] at h
    exact h
  have e10 : c (m + 10) = c (m + 5) := by
    have h := cper (m + 5)
    rw [show m + 5 + 5 = m + 10 by omega] at h
    exact h
  have e9 : c (m + 9) = c (m + 4) := by
    have h := cper (m + 4)
    rw [show m + 4 + 5 = m + 9 by omega] at h
    exact h
  rw [e12] at h12
  rw [e11] at h11
  rw [e10] at h10
  rw [e9] at h9
  push_cast at h12 h11 h10 h9 h7 h6 h5 h4
  have key : (5 : ℤ) * (a (m + 12) - (3 * a (m + 11) - 3 * a (m + 10) + a (m + 9) +
      a (m + 7) - 3 * a (m + 6) + 3 * a (m + 5) - a (m + 4))) = 0 := by
    linear_combination h12 - 3 * h11 + 3 * h10 - h9 - h7 + 3 * h6 - 3 * h5 + h4
  have key2 := (mul_eq_zero.mp key).resolve_left (by norm_num)
  linarith [key2]

end M03A184634

open OMA.S_oeis_a184634 M03A184634 in
theorem OMA.solution : type_of% @OMA.S_oeis_a184634.main := by
  refine ⟨fun n hn => ⟨(bounds n hn).2, (bounds n hn).1⟩, f0, f1, f2, f3, f4, recur⟩
