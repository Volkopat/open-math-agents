import OMAStatements.S_oeis_a078124
import Mathlib

namespace OMA.P_oeis_a078124

open OMA.S_oeis_a078124

private noncomputable def invPow3 (j : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun r => if 3 ^ j ∣ r then (1 : ℤ) else 0)

private noncomputable def prodPow3 (d : ℕ) : PowerSeries ℤ :=
  ∏ j ∈ Finset.range (d + 1), invPow3 j

private noncomputable def b (d N : ℕ) : ℤ :=
  PowerSeries.coeff N (prodPow3 d)

private noncomputable def c (d q : ℕ) : ℤ :=
  b d (3 ^ d * q)

private lemma b_zero (N : ℕ) : b 0 N = 1 := by
  simp [b, prodPow3, invPow3]

private lemma c_zero_left (q : ℕ) : c 0 q = 1 := by
  simp [c, b_zero]

private lemma b_at_zero (d : ℕ) : b d 0 = 1 := by
  simp only [b, prodPow3, PowerSeries.coeff_zero_eq_constantCoeff, map_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [invPow3]

private lemma c_zero_right (d : ℕ) : c d 0 = 1 := by
  simp [c, b_at_zero]

private lemma invPow3_mul_one_sub (j : ℕ) :
    (1 - PowerSeries.X ^ (3 ^ j)) * invPow3 j = 1 := by
  ext r
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  have h1 : PowerSeries.coeff r (1 : PowerSeries ℤ) = if r = 0 then 1 else 0 := by
    cases r with
    | zero => simp
    | succ r => simp
  rw [h1]
  simp only [invPow3, PowerSeries.coeff_mk]
  by_cases hr0 : r = 0
  · subst hr0
    have h3 : 0 < 3 ^ j := by positivity
    simp [show ¬(3 ^ j ≤ 0) by omega]
  · simp only [hr0, ↓reduceIte]
    by_cases hle : 3 ^ j ≤ r
    · simp only [hle, ↓reduceIte]
      have hiff : 3 ^ j ∣ r ↔ 3 ^ j ∣ r - 3 ^ j := by
        constructor
        · rintro ⟨q, hq⟩
          exact ⟨q - 1, by
            have hq1 : 1 ≤ q := by
              by_contra h0; push Not at h0
              have : q = 0 := by omega
              subst this; simp at hq; omega
            rw [Nat.mul_sub_left_distrib, mul_one, ← hq]⟩
        · rintro ⟨q, hq⟩
          exact ⟨q + 1, by rw [Nat.mul_add, mul_one, ← hq, Nat.sub_add_cancel hle]⟩
      by_cases hd : 3 ^ j ∣ r
      · rw [if_pos hd, if_pos (hiff.mp hd), sub_self]
      · rw [if_neg hd, if_neg (mt hiff.mpr hd), sub_self]
    · simp only [hle, ↓reduceIte, sub_zero]
      have hnd : ¬(3 ^ j ∣ r) := fun ⟨q, hq⟩ => by
        rcases q with _ | q
        · simp at hq; omega
        · have : 3 ^ j ≤ 3 ^ j * (q + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos q)
          omega
      rw [if_neg hnd]

private lemma b_sub_step (d N : ℕ) (hN : 3 ^ (d + 1) ≤ N) :
    b (d + 1) N - b (d + 1) (N - 3 ^ (d + 1)) = b d N := by
  have hprod : (1 - PowerSeries.X ^ (3 ^ (d + 1))) * prodPow3 (d + 1) = prodPow3 d := by
    simp only [prodPow3, Finset.prod_range_succ]
    rw [mul_left_comm, invPow3_mul_one_sub, mul_one]
  have hc := congr_arg (PowerSeries.coeff N) hprod
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', if_pos hN] at hc
  exact hc

private lemma c_step (d q : ℕ) :
    c (d + 1) (q + 1) = c (d + 1) q + c d (3 * (q + 1)) := by
  have hle : 3 ^ (d + 1) ≤ 3 ^ (d + 1) * (q + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos q)
  have h := b_sub_step d (3 ^ (d + 1) * (q + 1)) hle
  have hsub : 3 ^ (d + 1) * (q + 1) - 3 ^ (d + 1) = 3 ^ (d + 1) * q := by
    rw [Nat.mul_add, mul_one, Nat.add_sub_cancel]
  have h3 : 3 ^ (d + 1) * (q + 1) = 3 ^ d * (3 * (q + 1)) := by
    rw [pow_succ]; ring
  rw [hsub] at h
  have h' : c (d + 1) (q + 1) - c (d + 1) q = c d (3 * (q + 1)) := by
    simpa only [c, h3] using h
  linarith

-- Key 2-variable convolution identity:
-- ∑_{r=0}^d c(d - r, u * 4^r - 1) * c(r, v - 1) = c(d, u + v - 1) for all d >= 0, u >= 1, v >= 1!
private lemma c_conv : ∀ (d : ℕ) (u v : ℕ), 1 ≤ u → 1 ≤ v →
    ∑ r ∈ Finset.range (d + 1), c (d - r) (u * 3 ^ r - 1) * c r (v - 1) = c d (u + v - 1) := by
  intro d
  induction d with
  | zero =>
    intro u v _ _
    simp [c_zero_left]
  | succ d ihd =>
    intro u v hu hv
    -- First prove v = 1!
    have hbase : ∀ w : ℕ, 1 ≤ w →
        ∑ r ∈ Finset.range (d + 2), c (d + 1 - r) (w * 3 ^ r - 1) = c (d + 1) w := by
      intro w hw
      rw [Finset.sum_range_succ']
      simp only [pow_zero, mul_one, Nat.sub_zero]
      have hshift : ∑ r ∈ Finset.range (d + 1), c (d + 1 - (r + 1)) (w * 3 ^ (r + 1) - 1) =
          ∑ r ∈ Finset.range (d + 1), c (d - r) ((3 * w) * 3 ^ r - 1) * c r (1 - 1) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [Nat.sub_self, c_zero_right, mul_one, Nat.succ_sub_succ_eq_sub]
        congr 2; rw [pow_succ']; ring
      rw [hshift, ihd (3 * w) 1 (by omega) (by omega)]
      have hstep := c_step d (w - 1)
      have hw1 : w - 1 + 1 = w := by omega
      rw [hw1] at hstep
      have h3w : 3 * w + 1 - 1 = 3 * w := by omega
      rw [h3w]
      linarith
    -- Now induct on v >= 1!
    obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
    induction v' with
    | zero =>
      simp only [Nat.sub_self, c_zero_right, mul_one, show u + (0 + 1) - 1 = u by omega]
      exact hbase u hu
    | succ v' ihv =>
      have hdiff :
          (∑ r ∈ Finset.range (d + 2), c (d + 1 - r) (u * 3 ^ r - 1) * c r (v' + 1)) -
          (∑ r ∈ Finset.range (d + 2), c (d + 1 - r) (u * 3 ^ r - 1) * c r v') =
          c d (3 * (u + v' + 1)) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']
        simp only [c_zero_left, mul_one, sub_self, add_zero]
        have hterm : ∀ r ∈ Finset.range (d + 1),
            c (d + 1 - (r + 1)) (u * 3 ^ (r + 1) - 1) * c (r + 1) (v' + 1) -
            c (d + 1 - (r + 1)) (u * 3 ^ (r + 1) - 1) * c (r + 1) v' =
            c (d - r) ((3 * u) * 3 ^ r - 1) * c r ((3 * (v' + 1) + 1) - 1) := by
          intro r _
          rw [Nat.succ_sub_succ_eq_sub, ← mul_sub]
          have hst := c_step r v'
          have hsub : c (r + 1) (v' + 1) - c (r + 1) v' = c r (3 * (v' + 1)) := by linarith
          rw [hsub, show u * 3 ^ (r + 1) = 3 * u * 3 ^ r by rw [pow_succ']; ring,
            show 3 * (v' + 1) + 1 - 1 = 3 * (v' + 1) by omega]
        rw [Finset.sum_congr rfl hterm, ihd (3 * u) (3 * (v' + 1) + 1) (by omega) (by omega)]
        congr 1; omega
      have hstep := c_step d (u + v')
      have ihv' := ihv (Nat.succ_pos v')
      have h1 : u + (v' + 1 + 1) - 1 = u + v' + 1 := by omega
      have h2 : u + (v' + 1) - 1 = u + v' := by omega
      simp only [Nat.add_sub_cancel] at ihv' ⊢
      rw [h2] at ihv'
      rw [h1]
      linarith

private noncomputable def T (i j : ℕ) : ℤ :=
  if j ≤ i then c (i - j) (3 ^ j - 1) else 0

private lemma T_pow (m : ℕ) (hm : 1 ≤ m) (i j : ℕ) :
    ltMatPow T m i j = if j ≤ i then c (i - j) (m * 3 ^ j - 1) else 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  induction m' generalizing i j with
  | zero =>
    simp only [ltMatPow, ltMatMul]
    by_cases hji : j ≤ i
    · rw [if_pos hji]
      rw [Finset.sum_eq_single i]
      · simp [T, hji]
      · intro k _ hki; simp [show i ≠ k by omega]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self i)) h
    · rw [if_neg hji]
      rw [Finset.sum_eq_single i]
      · simp [T, hji]
      · intro k _ hki; simp [show i ≠ k by omega]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self i)) h
  | succ m' ih =>
    change ltMatMul (ltMatPow T (m' + 1)) T i j = _
    simp only [ltMatMul]
    by_cases hji : j ≤ i
    · rw [if_pos hji]
      have hsum : ∑ k ∈ Finset.range (i + 1), ltMatPow T (m' + 1) i k * T k j =
          ∑ r ∈ Finset.range (i - j + 1),
            c (i - j - r) ((m' + 1) * 3 ^ (j + r) - 1) * c r (3 ^ j - 1) := by
        have hfilt : ∑ k ∈ Finset.range (i + 1), ltMatPow T (m' + 1) i k * T k j =
            ∑ k ∈ (Finset.range (i + 1)).filter (fun k => j ≤ k), ltMatPow T (m' + 1) i k * T k j := by
          symm
          refine Finset.sum_subset (Finset.filter_subset _ _) fun k hk hnot => ?_
          simp only [Finset.mem_filter, not_and, not_le] at hnot
          have hlt : k < j := hnot hk
          simp [T, show ¬(j ≤ k) by omega]
        rw [hfilt]
        refine Finset.sum_nbij' (fun k => k - j) (fun r => j + r) ?_ ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; omega
        · intro r hr; simp only [Finset.mem_range, Finset.mem_filter] at hr ⊢; omega
        · intro k hk; simp only [Finset.mem_filter] at hk; omega
        · intro r _; omega
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_range] at hk
          rw [ih i k (Nat.succ_pos m'), if_pos (by omega)]
          simp only [T, if_pos hk.2]
          rw [show i - k = i - j - (k - j) by omega, show j + (k - j) = k by omega]
      rw [hsum]
      have hconv := c_conv (i - j) ((m' + 1) * 3 ^ j) (3 ^ j)
        (Nat.one_le_iff_ne_zero.mpr (by positivity)) (Nat.one_le_iff_ne_zero.mpr (by positivity))
      have hrew : ∀ r ∈ Finset.range (i - j + 1),
          c (i - j - r) ((m' + 1) * 3 ^ (j + r) - 1) * c r (3 ^ j - 1) =
          c (i - j - r) (((m' + 1) * 3 ^ j) * 3 ^ r - 1) * c r (3 ^ j - 1) := by
        intro r _
        rw [show (m' + 1) * 3 ^ (j + r) = (m' + 1) * 3 ^ j * 3 ^ r by rw [pow_add]; ring]
      rw [Finset.sum_congr rfl hrew, hconv,
        show (m' + 1) * 3 ^ j + 3 ^ j = (m' + 1 + 1) * 3 ^ j by ring]
    · rw [if_neg hji]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp [T, show ¬(j ≤ k) by omega]

private lemma T_shift (i j : ℕ) : ltMatPow T 3 i j = T (i + 1) (j + 1) := by
  rw [T_pow 3 (by omega) i j]
  simp only [T]
  have hiff : j ≤ i ↔ j + 1 ≤ i + 1 := by omega
  by_cases h : j ≤ i
  · rw [if_pos h, if_pos (hiff.mp h), show i + 1 - (j + 1) = i - j by omega,
      show 3 ^ (j + 1) = 3 * 3 ^ j by rw [pow_succ']]
  · rw [if_neg h, if_neg (mt hiff.mpr h)]

private lemma ltMatPow_agree (M N : ℕ → ℕ → ℤ) (n : ℕ)
    (hMN : ∀ i j, i ≤ n → j ≤ n → M i j = N i j) :
    ∀ m i j, i ≤ n → j ≤ n → ltMatPow M m i j = ltMatPow N m i j := by
  intro m
  induction m with
  | zero => intro i j _ _; rfl
  | succ m ih =>
    intro i j hi hj
    simp only [ltMatPow, ltMatMul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [ih i k hi (by omega), hMN k j (by omega) hj]

private lemma M_eq_T (M : ℕ → ℕ → ℤ)
    (hlt : ∀ i j, i < j → M i j = 0)
    (hcol0 : ∀ i, M i 0 = 1)
    (hshift : ∀ i j, ltMatPow M 3 i j = M (i + 1) (j + 1)) :
    ∀ i j, M i j = T i j := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro j
    cases i with
    | zero =>
      cases j with
      | zero => simp [hcol0 0, T, c_zero_left]
      | succ j => rw [hlt 0 (j + 1) (by omega)]; simp [T]
    | succ i =>
      cases j with
      | zero => simp [hcol0 (i + 1), T, c_zero_right]
      | succ j =>
        by_cases hji : j ≤ i
        · rw [← hshift i j, ← T_shift i j]
          exact ltMatPow_agree M T i (fun a b ha _ => ih a (by omega) b) 3 i j (le_refl i) hji
        · rw [hlt (i + 1) (j + 1) (by omega)]
          simp [T, show ¬(j + 1 ≤ i + 1) by omega]

private theorem main_proved :
    ∀ M : ℕ → ℕ → ℤ,
      (∀ i j, i < j → M i j = 0) →
      (∀ i, M i 0 = 1) →
      (∀ i j, ltMatPow M 3 i j = M (i + 1) (j + 1)) →
      ∀ n : ℕ,
        M (n + 1) 1 = PowerSeries.coeff (2 * 3 ^ n)
          (∏ j ∈ Finset.range (n + 1),
            PowerSeries.mk (fun r => if 3 ^ j ∣ r then (1 : ℤ) else 0)) := by
  intro M hlt hcol0 hshift n
  rw [M_eq_T M hlt hcol0 hshift (n + 1) 1]
  simp only [T, if_pos (by omega : 1 ≤ n + 1), Nat.add_sub_cancel, c, b, prodPow3, invPow3]
  rw [show 3 ^ n * (3 ^ 1 - 1) = 2 * 3 ^ n by ring]

end OMA.P_oeis_a078124

theorem OMA.solution : type_of% @OMA.S_oeis_a078124.main :=
  OMA.P_oeis_a078124.main_proved
