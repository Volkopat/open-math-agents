import OMAStatements.S_oeis_a289927

-- Original proof by @jleguina.

namespace OMA.S_oeis_a289927

open PowerSeries

/-- Lucas numbers. -/
def L : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | k + 2 => L (k + 1) + L k

lemma L_cast (k : ℕ) : (L k : ℝ) = Real.goldenRatio ^ k + Real.goldenConj ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · norm_num [L]
    · norm_num [L]
    · rw [L]
      push_cast
      rw [ih (k + 1) (by omega), ih k (by omega), pow_add Real.goldenRatio k 2,
        pow_add Real.goldenConj k 2, Real.goldenRatio_sq, Real.goldenConj_sq]
      ring

/-- floor(phi^k) = L(k) - [k even] for k >= 1. -/
lemma floor_phi (k : ℕ) (hk : 1 ≤ k) :
    ⌊((1 + Real.sqrt 5) / 2) ^ k⌋ = L k - (if k % 2 = 0 then 1 else 0) := by
  have hψ1 := Real.neg_one_lt_goldenConj
  have hψ2 := Real.goldenConj_neg
  have habs : |Real.goldenConj| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hpow : |Real.goldenConj ^ k| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg _) habs (by omega)
  have hL := L_cast k
  have hphi : ((1 + Real.sqrt 5) / 2) ^ k = (L k : ℝ) - Real.goldenConj ^ k := by
    rw [hL]; simp [Real.goldenRatio]
  rw [hphi, Int.floor_eq_iff]
  have hb := abs_lt.mp hpow
  rcases Nat.even_or_odd k with he | ho
  · have hpos : 0 < Real.goldenConj ^ k := he.pow_pos (ne_of_lt hψ2)
    rw [if_pos (Nat.even_iff.mp he)]
    push_cast
    constructor <;> linarith
  · have hneg : Real.goldenConj ^ k < 0 := ho.pow_neg hψ2
    rw [if_neg (by rw [Nat.odd_iff] at ho; omega)]
    push_cast
    constructor <;> linarith

/-- The coefficients of S. -/
noncomputable def s (k : ℕ) : ℚ := if k = 0 then 0 else ((⌊((1 + Real.sqrt 5) / 2) ^ k⌋ : ℤ) : ℚ)

lemma coeff_S (k : ℕ) : coeff k S = s k := by simp [S, s]

lemma s_pos (k : ℕ) (hk : 1 ≤ k) : s k = (L k : ℚ) - (if k % 2 = 0 then 1 else 0) := by
  rw [s, if_neg (by omega), floor_phi k hk]
  push_cast
  split_ifs <;> simp

lemma s_vals : s 1 = 1 ∧ s 2 = 2 ∧ s 3 = 4 ∧ s 4 = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [s_pos _ (by norm_num)] <;> norm_num [L]

lemma s_rec (n : ℕ) (hn : 5 ≤ n) :
    s n - s (n - 1) - 2 * s (n - 2) + s (n - 3) + s (n - 4) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    s_pos _ (by omega), s_pos _ (by omega), s_pos _ (by omega), s_pos _ (by omega),
    s_pos _ (by omega)]
  have l5 : L (m + 5) = L (m + 4) + L (m + 3) := rfl
  have l4 : L (m + 4) = L (m + 3) + L (m + 2) := rfl
  have l3 : L (m + 3) = L (m + 2) + L (m + 1) := rfl
  have e1 : (m + 5) % 2 = (m + 1) % 2 := by omega
  have e2 : (m + 4) % 2 = (m + 2) % 2 := by omega
  have e3 : (m + 3) % 2 = (m + 1) % 2 := by omega
  rw [e1, e2, e3, l5, l4, l3]
  have : (m + 2) % 2 = 0 ∨ (m + 2) % 2 = 1 := by omega
  have h' : (m + 1) % 2 = 0 ↔ (m + 2) % 2 = 1 := by omega
  rcases this with h | h <;> simp [h, h'] <;> ring

/-- S * (1 - x - 2x^2 + x^3 + x^4) = x + x^2 - x^4. -/
lemma S_mul : S * (1 - X ^ 1 - C (2 : ℚ) * X ^ 2 + X ^ 3 + X ^ 4) = X ^ 1 + X ^ 2 - X ^ 4 := by
  obtain ⟨v1, v2, v3, v4⟩ := s_vals
  have e : S * (1 - X ^ 1 - C (2 : ℚ) * X ^ 2 + X ^ 3 + X ^ 4) =
      S - S * X ^ 1 - C (2 : ℚ) * (S * X ^ 2) + S * X ^ 3 + S * X ^ 4 := by ring
  rw [e]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_S]
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> simp [s, v1, v2, v3, v4] <;> norm_num [s] at v1 v2 v3 v4 ⊢ <;> linarith
  · have hr := s_rec n hn
    simp (disch := omega) [if_pos, if_neg]
    linarith

lemma constCoeff_F : constantCoeff (1 - S - S ^ 2) = 1 := by
  have h0 : constantCoeff S = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_S]; simp [s]
  simp [h0]

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk a * (1 - 3 * X - 4 * X ^ 2 + 7 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 -
      4 * X ^ 6 + 3 * X ^ 7 + X ^ 8) = (1 - X ^ 2 + X ^ 3) * (1 + X - X ^ 3) := by
  set F := 1 - S - S ^ 2 with hF
  set I := F⁻¹ with hI
  have hFI : F * I = 1 := PowerSeries.mul_inv_cancel F (by rw [constCoeff_F]; norm_num)
  have hI0 : constantCoeff I = 1 := by
    have := congrArg constantCoeff hFI
    rw [map_mul, constCoeff_F, one_mul, map_one] at this
    exact this
  have hAX : PowerSeries.mk a * X = I - 1 := by
    ext n
    rcases n with _ | n
    · simp [coeff_zero_eq_constantCoeff_apply, hI0]
    · rw [coeff_succ_mul_X, coeff_mk, map_sub, coeff_one]
      simp [a, hI, hF]
  have hSD := S_mul
  set D0 : ℚ⟦X⟧ := 1 - X ^ 1 - C (2 : ℚ) * X ^ 2 + X ^ 3 + X ^ 4 with hD0
  set R : ℚ⟦X⟧ := X ^ 1 + X ^ 2 - X ^ 4 with hR
  have hE : F * D0 ^ 2 = D0 ^ 2 - R * D0 - R ^ 2 := by
    rw [hF, ← hSD]; ring
  have key : X * (PowerSeries.mk a * (D0 ^ 2 - R * D0 - R ^ 2)) =
      X * ((1 - X ^ 2 + X ^ 3) * (1 + X - X ^ 3)) := by
    rw [← hE]
    calc X * (PowerSeries.mk a * (F * D0 ^ 2)) = (PowerSeries.mk a * X) * F * D0 ^ 2 := by ring
      _ = (I - 1) * F * D0 ^ 2 := by rw [hAX]
      _ = (F * I - F) * D0 ^ 2 := by ring
      _ = (1 - F) * D0 ^ 2 := by rw [hFI]
      _ = (S * D0) * D0 + (S * D0) ^ 2 := by rw [hF]; ring
      _ = R * D0 + R ^ 2 := by rw [hSD]
      _ = X * ((1 - X ^ 2 + X ^ 3) * (1 + X - X ^ 3)) := by
          rw [hR, hD0, show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]; ring
  have hcancel := mul_left_cancel₀ PowerSeries.X_ne_zero key
  rw [← hcancel, hD0, hR, show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]
  ring

/-- Barker's recurrence for n > 7. -/
theorem recurrence (n : ℕ) (hn : 7 < n) :
    a n = 3 * a (n - 1) + 4 * a (n - 2) - 7 * a (n - 3) - 5 * a (n - 4) + 7 * a (n - 5) +
      4 * a (n - 6) - 3 * a (n - 7) - a (n - 8) := by
  have h := congrArg (coeff n) gf
  have eD : PowerSeries.mk a * (1 - 3 * X - 4 * X ^ 2 + 7 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 -
      4 * X ^ 6 + 3 * X ^ 7 + X ^ 8) = PowerSeries.mk a - C (3 : ℚ) * (PowerSeries.mk a * X ^ 1) -
      C (4 : ℚ) * (PowerSeries.mk a * X ^ 2) + C (7 : ℚ) * (PowerSeries.mk a * X ^ 3) +
      C (5 : ℚ) * (PowerSeries.mk a * X ^ 4) - C (7 : ℚ) * (PowerSeries.mk a * X ^ 5) -
      C (4 : ℚ) * (PowerSeries.mk a * X ^ 6) + C (3 : ℚ) * (PowerSeries.mk a * X ^ 7) +
      PowerSeries.mk a * X ^ 8 := by
    simp only [map_ofNat]
    ring

  have eN : ((1 - X ^ 2 + X ^ 3) * (1 + X - X ^ 3) : ℚ⟦X⟧) =
      1 + X ^ 1 - X ^ 2 - X ^ 3 + X ^ 4 + X ^ 5 - X ^ 6 := by ring
  rw [eD, eN] at h
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one, coeff_X_pow] at h
  simp (disch := omega) [if_pos, if_neg] at h
  linarith

end OMA.S_oeis_a289927

open OMA.S_oeis_a289927 in
theorem OMA.solution : type_of% @OMA.S_oeis_a289927.main :=
  ⟨gf, recurrence⟩
