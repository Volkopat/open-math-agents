import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1

/-!
# Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H2.R1.H2.R1

Splits step `H2` of `Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H2.R1` (thin kernel `7933 ∣ n`,
`¬ 8191 ∣ n`, `Y ≤ 5001/5000`, `a ≥ 48`) into three strictly stronger subcases `H1`, `H2`, `H3`.

Tightening the parent weight inequality `masterU` to `a ≥ 48`, `z ≥ 25000` (from `Y ≤ 5001/5000`),
`K'/K ≤ 1 + 1/(125000 * 5000)`, and explicit Mersenne weights at `8191`, `131071`, `524287` (with
tail from `2^31 - 1`, since `2^23 - 1 = 47 * 178481` and `2^29 - 1 = 233 * 2304167` are composite):
1. Every prime in `S` satisfies `z ≥ 25000`, and every simple prime outside
   `{3, 5, 7, 19, 31, 223, 607, 3967, 7933}` is at least `13947`.
2. `node_no19423_no63463`: if `19423` and `63463` are not simple, total `≤ 1.99999213 < 2`.
3. `node_no19423_63463_noM`: if `19423, 131071, 524287` are not simple and `63463` is simple,
   total `≤ 1.99999569 < 2`.
4. `node_no19423_63463_s2only`: if `19423` is not simple, `63463` is simple, and every `z ∈ S`
   has `z % 3 ≠ 1`, then the mod-3 leaf sum drops by half (`sumD_s2only`), total `≤ 1.99996620 < 2`.
5. `node_no19423_63463_no131_524_no104`: if `19423, 131071, 1048573` are not simple and
   `63463, 524287` are simple, total `≤ 1.99999974 < 2`.

Hence every solution in `H2` falls into one of:
- `H1`: `19423 ∣ n` (simple-prime exclusion boosted from `5057` to `49468`),
- `H2`: `¬ 19423 ∣ n`, `63463` and `131071` simple, `∃ z ∈ S, z % 3 = 1` (all-prime exclusion `20699`),
- `H3`: `¬ 19423 ∣ n`, `131071` not simple, `63463, 524287, 1048573` simple, `∃ z ∈ S, z % 3 = 1`
  (all-prime exclusion `18507`).
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1

namespace Erdos1052C18

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C7
  OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C9
  OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C11
  OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C16
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1.Erdos1052C17

-- From ∏ (1 + 5/z) ≤ 5001/5000 every z is at least 25000.
theorem ge_25000 {N : Finset ℕ} (hN0 : ∀ z ∈ N, z ≠ 0)
    (hY5 : ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000) : ∀ z ∈ N, 25000 ≤ z := by
  intro z hz
  have h1 : ∏ w ∈ ({z} : Finset ℕ), (1 + 5 / (w : ℚ)) ≤ ∏ w ∈ N, (1 + 5 / (w : ℚ)) :=
    Finset.prod_le_prod_of_subset_of_one_le (Finset.singleton_subset_iff.mpr hz)
      (fun w _ => by positivity)
      (fun w _ _ => by
        have : (0 : ℚ) ≤ 5 / (w : ℚ) := by positivity
        linarith)
  rw [Finset.prod_singleton] at h1
  by_contra hlt
  have hz' : (z : ℚ) ≤ 24999 := by exact_mod_cast (by omega : z ≤ 24999)
  have hzpos : (0 : ℚ) < z := by exact_mod_cast Nat.pos_of_ne_zero (hN0 z hz)
  have : (5 : ℚ) / 24999 ≤ 5 / (z : ℚ) := div_le_div_of_nonneg_left (by norm_num) hzpos hz'
  linarith

-- Tighter kernel factor bound when every z ∈ N satisfies 25000 ≤ z and ∏ (1 + 5/z) ≤ 5001/5000.
theorem kk_bound_25000 {N : Finset ℕ} (hNb : ∀ z ∈ N, 25000 ≤ z)
    (hY5 : ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000) :
    ∏ z ∈ N, (1 + 1 / (z : ℚ) ^ 2) ≤ 1 + 1 / (125000 * 5000) := by
  have h1 : ∏ z ∈ N, (1 + 1 / (z : ℚ) ^ 2) ≤ ∏ z ∈ N, (1 + 1 / 125000 * (5 / (z : ℚ))) := by
    refine Finset.prod_le_prod (fun z _ => by positivity) (fun z hz => ?_)
    have hq : (25000 : ℚ) ≤ z := by exact_mod_cast hNb z hz
    have hw : 1 / (z : ℚ) ≤ 1 / 25000 := one_div_le_one_div_of_le (by norm_num) hq
    have e1 : 1 / (z : ℚ) ^ 2 = (1 / (z : ℚ)) * (1 / (z : ℚ)) := by ring
    have e2 : (1 : ℚ) / 125000 * (5 / (z : ℚ)) = 1 / 25000 * (1 / (z : ℚ)) := by ring
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_right hw (by positivity : (0 : ℚ) ≤ 1 / (z : ℚ))
    linarith
  have h2 := prod_one_add_mul_le N (fun z => 5 / (z : ℚ)) (1 / 125000) (by norm_num) (by norm_num)
    (fun z _ => by positivity)
  have h3 := h1.trans h2
  nlinarith

-- Tighter smooth-reciprocal product bound for z ≥ 25000 and ∏ (1 + 5/z) ≤ 5001/5000.
theorem prod_recip_25000 {N : Finset ℕ} (hN : ∀ z ∈ N, 25000 ≤ z)
    (hY5 : ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000) :
    ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 1)) ≤ 1 + 1 / 24999 := by
  have hprod : ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 1)) ≤
      ∏ z ∈ N, (1 + 1 / 5 * (25000 / 24999) * (5 / (z : ℚ))) := by
    refine Finset.prod_le_prod (fun z hz => ?_) (fun z hz => ?_)
    · have : (25000 : ℚ) ≤ z := by exact_mod_cast hN z hz
      exact div_nonneg (by linarith) (by linarith)
    · have h : (25000 : ℚ) ≤ z := by exact_mod_cast hN z hz
      have e : (1 : ℚ) / 5 * (25000 / 24999) * (5 / (z : ℚ)) = 25000 / (24999 * (z : ℚ)) := by
        field_simp
      rw [e, div_le_iff₀ (by linarith)]
      have : (1 + 25000 / (24999 * (z : ℚ))) * ((z : ℚ) - 1) = (z : ℚ) - 1 + 25000 / 24999 -
          25000 / (24999 * (z : ℚ)) := by
        field_simp
        ring
      rw [this]
      have : 25000 / (24999 * (z : ℚ)) ≤ 1 / 24999 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith
  have hL2 := prod_one_add_mul_le N (fun z => 5 / (z : ℚ)) (1 / 5 * (25000 / 24999))
    (by norm_num) (by norm_num) (fun z _ => by positivity)
  have hfin := hprod.trans hL2
  have h0 : (0 : ℚ) ≤ 1 / 5 * (25000 / 24999) := by norm_num
  have := mul_le_mul_of_nonneg_left (show ∏ z ∈ N, (1 + 5 / (z : ℚ)) - 1 ≤ 5001 / 5000 - 1 by
    linarith) h0
  linarith

-- Tighter sumD_thin when every z ∈ N is ≥ 25000 and ∏ (1 + 5/z) ≤ 5001/5000.
theorem sumD_thin25 {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 25000 ≤ z)
    (hY5 : ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) :
    ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
      4 / 3 * (75000 / 74996) * (1 / 24999) := by
  have hUge : ∀ u ∈ U, 25000 ≤ u := fun u hu' => by
    obtain ⟨h0, h1, hr⟩ := hU u hu'
    have hmem := hr _ (Nat.minFac_prime h1) (Nat.minFac_dvd u)
    have := (hN _ hmem).2
    have := Nat.minFac_le (Nat.pos_of_ne_zero h0)
    omega
  have hstep : ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
      ∑ u ∈ U, 4 / 3 * (75000 / 74996) * (1 / (u : ℚ)) := by
    refine Finset.sum_le_sum fun u hu' => ?_
    have h := xw_le (c := 25000) (by norm_num) (hUge u hu')
    norm_num at h ⊢
    exact h
  rw [← Finset.mul_sum] at hstep
  have hσ : ∑ u ∈ U, 1 / (u : ℚ) ≤ 1 / 24999 := by
    have h1U : 1 ∉ U := fun h => (hU 1 h).2.1 rfl
    have hs := smooth_recip N (fun z hz => (hN z hz).1) (insert 1 U) (fun u hu' => by
      rcases Finset.mem_insert.mp hu' with rfl | hu'
      · exact ⟨one_ne_zero, fun r hr hd => absurd (Nat.le_of_dvd one_pos hd) (by
          have := hr.two_le; omega)⟩
      · exact ⟨(hU u hu').1, (hU u hu').2.2⟩)
    rw [Finset.sum_insert h1U] at hs
    simp only [Nat.cast_one, div_one] at hs
    have hp := prod_recip_25000 (fun z hz => (hN z hz).2) hY5
    linarith
  have h0 : (0 : ℚ) ≤ 4 / 3 * (75000 / 74996) := by norm_num
  have := mul_le_mul_of_nonneg_left hσ h0
  linarith

-- Elementary Finset inequalities for bounding composite smooth reciprocals.
theorem one_add_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℚ)
    (ha : ∀ x ∈ s, 0 ≤ a x) :
    1 + ∑ x ∈ s, a x ≤ ∏ x ∈ s, (1 + a x) := by
  induction s using Finset.induction with
  | empty => simp
  | insert x t hxt ih =>
    rw [Finset.sum_insert hxt, Finset.prod_insert hxt]
    have hx : 0 ≤ a x := ha x (Finset.mem_insert_self x t)
    have ht : 0 ≤ ∑ y ∈ t, a y := Finset.sum_nonneg fun y hy => ha y (Finset.mem_insert_of_mem hy)
    have iht := ih (fun y hy => ha y (Finset.mem_insert_of_mem hy))
    nlinarith

theorem prod_one_add_le_inv_one_sub {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℚ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (hs : ∑ x ∈ s, a x < 1) :
    ∏ x ∈ s, (1 + a x) ≤ 1 / (1 - ∑ x ∈ s, a x) := by
  induction s using Finset.induction with
  | empty => simp
  | insert x t hxt ih =>
    rw [Finset.sum_insert hxt] at hs ⊢
    rw [Finset.prod_insert hxt]
    have hx : 0 ≤ a x := ha x (Finset.mem_insert_self x t)
    have ht : 0 ≤ ∑ y ∈ t, a y := Finset.sum_nonneg fun y hy => ha y (Finset.mem_insert_of_mem hy)
    have hts : ∑ y ∈ t, a y < 1 := by linarith
    have iht := ih (fun y hy => ha y (Finset.mem_insert_of_mem hy)) hts
    have h1 : (1 + a x) * ∏ y ∈ t, (1 + a y) ≤ (1 + a x) * (1 / (1 - ∑ y ∈ t, a y)) :=
      mul_le_mul_of_nonneg_left iht (by linarith)
    refine h1.trans ?_
    rw [mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

-- Mod-3 leaf bound when NO prime in N has z % 3 = 1: then every u ∈ U with u % 3 = 1 is composite
-- (disjoint from N), so its reciprocal sum is O(1/25000^2) and the total leaf constant drops by half.
theorem sumD_s2only {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 25000 ≤ z)
    (hNo1 : ∀ z ∈ N, z % 3 ≠ 1)
    (hY5 : ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) :
    ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
      2 / 3 * (75000 / 74998) * (1 / 24999) + 4 / 3 * (75000 / 74996) * (1 / 300000000) := by
  have hUge : ∀ u ∈ U, 25000 ≤ u := fun u hu' => by
    obtain ⟨h0, h1, hr⟩ := hU u hu'
    have hmem := hr _ (Nat.minFac_prime h1) (Nat.minFac_dvd u)
    have := (hN _ hmem).2
    have := Nat.minFac_le (Nat.pos_of_ne_zero h0)
    omega
  have hprod : ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 1)) ≤ 1 + 1 / 24999 :=
    prod_recip_25000 (fun z hz => (hN z hz).2) hY5
  have hU_sum : ∑ u ∈ U, 1 / (u : ℚ) ≤ 1 / 24999 := by
    have h1U : 1 ∉ U := fun h => (hU 1 h).2.1 rfl
    have hs := smooth_recip N (fun z hz => (hN z hz).1) (insert 1 U) (fun u hu' => by
      rcases Finset.mem_insert.mp hu' with rfl | hu'
      · exact ⟨one_ne_zero, fun r hr hd => absurd (Nat.le_of_dvd one_pos hd) (by
          have := hr.two_le; omega)⟩
      · exact ⟨(hU u hu').1, (hU u hu').2.2⟩)
    rw [Finset.sum_insert h1U] at hs
    simp only [Nat.cast_one, div_one] at hs
    linarith
  set U1 := U.filter (fun u => u % 3 = 1)
  have hdisj : Disjoint N U1 := Finset.disjoint_left.mpr fun z hzN hzU =>
    hNo1 z hzN (Finset.mem_filter.mp hzU).2
  have h1NU : 1 ∉ N ∪ U1 := by
    intro h1
    rcases Finset.mem_union.mp h1 with h1N | h1U1
    · have := (hN 1 h1N).2; omega
    · exact (hU 1 (Finset.mem_filter.mp h1U1).1).2.1 rfl
  have hsmooth_NU : 1 + ∑ z ∈ N, (1 / (z : ℚ)) + ∑ u ∈ U1, (1 / (u : ℚ)) ≤
      ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 1)) := by
    have hs := smooth_recip N (fun z hz => (hN z hz).1) (insert 1 (N ∪ U1)) (fun u hu' => by
      rcases Finset.mem_insert.mp hu' with rfl | hu'
      · exact ⟨one_ne_zero, fun r hr hd => absurd (Nat.le_of_dvd one_pos hd) (by
          have := hr.two_le; omega)⟩
      · rcases Finset.mem_union.mp hu' with huN | huU1
        · exact ⟨(hN u huN).1.ne_zero, fun r hr hd => by
            rwa [(Nat.prime_dvd_prime_iff_eq hr (hN u huN).1).mp hd]⟩
        · exact ⟨(hU u (Finset.mem_filter.mp huU1).1).1, (hU u (Finset.mem_filter.mp huU1).1).2.2⟩)
    rw [Finset.sum_insert h1NU, Finset.sum_union hdisj] at hs
    simp only [Nat.cast_one, div_one] at hs
    linarith
  have hprod_eq : ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 1)) = ∏ z ∈ N, (1 + 1 / ((z : ℚ) - 1)) := by
    refine Finset.prod_congr rfl fun z hz => ?_
    have hz' : (25000 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
    have hz1 : (z : ℚ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  set s : ℚ := ∑ z ∈ N, (1 / ((z : ℚ) - 1))
  have ha_nn : ∀ z ∈ N, (0 : ℚ) ≤ 1 / ((z : ℚ) - 1) := fun z hz => by
    have hz' : (25000 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
    exact div_nonneg zero_le_one (by linarith)
  have hs_nn : 0 ≤ s := Finset.sum_nonneg ha_nn
  have hs_le : s ≤ 1 / 24999 := by
    have hlow := one_add_sum_le_prod N (fun z => 1 / ((z : ℚ) - 1)) ha_nn
    rw [← hprod_eq] at hlow
    linarith
  have hprod_up : ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 1)) ≤ 1 / (1 - s) := by
    rw [hprod_eq]
    exact prod_one_add_le_inv_one_sub N (fun z => 1 / ((z : ℚ) - 1)) ha_nn (by linarith)
  have hdiff : s - ∑ z ∈ N, (1 / (z : ℚ)) ≤ s / 25000 := by
    have hsub : s - ∑ z ∈ N, (1 / (z : ℚ)) = ∑ z ∈ N, (1 / ((z : ℚ) - 1) - 1 / (z : ℚ)) := by
      rw [Finset.sum_sub_distrib]
    rw [hsub, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_le_sum fun z hz => ?_
    have hz' : (25000 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
    have e : 1 / ((z : ℚ) - 1) - 1 / (z : ℚ) = 1 / ((z : ℚ) - 1) * (1 / (z : ℚ)) := by
      have hz1 : (z : ℚ) - 1 ≠ 0 := by linarith
      have hz0 : (z : ℚ) ≠ 0 := by linarith
      field_simp; ring
    rw [e]
    have h1 : 1 / (z : ℚ) ≤ (25000 : ℚ)⁻¹ := by
      rw [one_div]; exact inv_anti₀ (by norm_num) hz'
    exact mul_le_mul_of_nonneg_left h1 (ha_nn z hz)
  have hU1_sum : ∑ u ∈ U1, (1 / (u : ℚ)) ≤ 1 / 300000000 := by
    have hinv : 1 / (1 - s) - 1 - s = s * s / (1 - s) := by
      have hs1 : (1 : ℚ) - s ≠ 0 := by linarith
      field_simp; ring
    have hss : s * s / (1 - s) ≤ (1 / 24999) * (1 / 24999) / (1 - 1 / 24999) := by
      have hnum : s * s ≤ (1 / 24999) * (1 / 24999) :=
        mul_le_mul hs_le hs_le hs_nn (by norm_num)
      have hden : 1 - (1 : ℚ) / 24999 ≤ 1 - s := by linarith
      exact div_le_div₀ (by positivity) hnum (by norm_num) hden
    have hcomb : ∑ u ∈ U1, (1 / (u : ℚ)) ≤ s * s / (1 - s) + s / 25000 := by linarith
    linarith
  have hsplit := Finset.sum_filter_add_sum_filter_not U (fun u => u % 3 = 1)
    (fun u => if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2))
  have h1part : ∑ u ∈ U1, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
      4 / 3 * (75000 / 74996) * (1 / 300000000) := by
    have hle : ∑ u ∈ U1, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        ∑ u ∈ U1, 4 / 3 * (75000 / 74996) * (1 / (u : ℚ)) := by
      refine Finset.sum_le_sum fun u hu => ?_
      have h := xw_le (c := 25000) (by norm_num) (hUge u (Finset.mem_filter.mp hu).1)
      norm_num at h ⊢
      exact h
    rw [← Finset.mul_sum] at hle
    have := mul_le_mul_of_nonneg_left hU1_sum (by norm_num : (0 : ℚ) ≤ 4 / 3 * (75000 / 74996))
    linarith
  have h2part : ∑ u ∈ U.filter (fun u => ¬ u % 3 = 1),
        (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
      2 / 3 * (75000 / 74998) * (1 / 24999) := by
    have hle : ∑ u ∈ U.filter (fun u => ¬ u % 3 = 1),
          (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        ∑ u ∈ U.filter (fun u => ¬ u % 3 = 1), 2 / 3 * (75000 / 74998) * (1 / (u : ℚ)) := by
      refine Finset.sum_le_sum fun u hu => ?_
      obtain ⟨huU, hne1⟩ := Finset.mem_filter.mp hu
      rw [if_neg hne1]
      have huq : (25000 : ℚ) ≤ u := by exact_mod_cast hUge u huU
      have e : 2 / 3 * (75000 / 74998) * (1 / (u : ℚ)) = 50000 / (74998 * (u : ℚ)) := by
        field_simp; ring
      rw [e, div_le_div_iff₀ (by linarith) (by positivity)]
      nlinarith
    rw [← Finset.mul_sum] at hle
    have hsub : ∑ u ∈ U.filter (fun u => ¬ u % 3 = 1), (1 / (u : ℚ)) ≤ ∑ u ∈ U, (1 / (u : ℚ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun u _ _ => by positivity)
    have htot := hsub.trans hU_sum
    have := mul_le_mul_of_nonneg_left htot (by norm_num : (0 : ℚ) ≤ 2 / 3 * (75000 / 74998))
    linarith
  linarith

-- Helper to kill composite numbers cleanly via explicit factorization.
theorem not_prime_of_mul {p a b : ℕ} (ha : a ≠ 1) (hb : b ≠ 1) (h : p = a * b) : ¬ p.Prime := by
  rw [h]
  exact Nat.not_prime_mul ha hb

-- Mersenne primes below 2^31 - 1 = 2147483647.
theorem mersenne_small19 {q k : ℕ} (hq : q.Prime) (hk : q + 1 = 2 ^ k) (hlt : q < 2147483647) :
    q = 3 ∨ q = 7 ∨ q = 31 ∨ q = 127 ∨ q = 8191 ∨ q = 131071 ∨ q = 524287 := by
  have hk31 : k < 31 := by
    by_contra h
    have : 2 ^ 31 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases h17 : k < 17
  · have hq17 : q < 131071 := by
      have : 2 ^ k ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rcases mersenne_small7 hq hk hq17 with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · have hklo : 17 ≤ k := by omega
    interval_cases k
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 87381) (by norm_num) (by norm_num) (by omega))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 349525) (by norm_num) (by norm_num) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 7) (b := 299593) (by norm_num) (by norm_num) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 1398101) (by norm_num) (by norm_num) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 47) (b := 178481) (by norm_num) (by norm_num) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 5592405) (by norm_num) (by norm_num) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 31) (b := 1082401) (by norm_num) (by norm_num) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 22369621) (by norm_num) (by norm_num) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 7) (b := 19173961) (by norm_num) (by norm_num) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 89478485) (by norm_num) (by norm_num) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 233) (b := 2304167) (by norm_num) (by norm_num) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 357913941) (by norm_num) (by norm_num) (by omega))

-- Mersenne leaves with explicit weights at 8191, 131071, 524287 and tail from 2^31 - 1.
theorem mersenne_bound19 (β : ℕ → ℚ) (L : Finset ℕ) (hLp : ∀ q ∈ L, q.Prime)
    (hLm : ∀ q ∈ L, ∃ k, q + 1 = 2 ^ k)
    (hLβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (h8 : 1 ≤ β 8191) (h17 : 1 ≤ β 131071) (h19 : 1 ≤ β 524287) :
    ∏ q ∈ L, β q ≤
      (β 3 * β 7 * β 31 * β 127) * (β 8191 * β 131071 * β 524287 * (536870912 / 536870911)) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => q < 2147483647) β
  have hsmall : ∏ q ∈ L.filter (fun q => q < 2147483647), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (β 8191 * β 131071 * β 524287) := by
    have hsub : L.filter (fun q => q < 2147483647) ⊆
        ({3, 7, 31, 127, 8191, 131071, 524287} : Finset ℕ) := by
      intro q hq
      obtain ⟨hqL, hlt⟩ := Finset.mem_filter.mp hq
      obtain ⟨k, hk⟩ := hLm q hqL
      have := mersenne_small19 (hLp q hqL) hk hlt
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
      (fun i hi => (hLβ i (Finset.mem_filter.mp hi).1).1.le) (fun i hi _ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1.1
      · exact h1.2.1
      · exact h1.2.2.1
      · exact h1.2.2.2
      · exact h8
      · exact h17
      · exact h19)
    have e : ∏ q ∈ ({3, 7, 31, 127, 8191, 131071, 524287} : Finset ℕ), β q =
        (β 3 * β 7 * β 31 * β 127) * (β 8191 * β 131071 * β 524287) := by
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_singleton]
      ring
    rwa [e] at h
  have hmemT : ∀ q ∈ L.filter (fun q => ¬ q < 2147483647), q ∈ L ∧ 2147483647 ≤ q := fun q hq => by
    obtain ⟨ha, hb⟩ := Finset.mem_filter.mp hq
    exact ⟨ha, by omega⟩
  have htail : ∏ q ∈ L.filter (fun q => ¬ q < 2147483647), β q ≤ 536870912 / 536870911 := by
    have hle : ∏ q ∈ L.filter (fun q => ¬ q < 2147483647), β q ≤
        ∏ q ∈ L.filter (fun q => ¬ q < 2147483647), (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
      Finset.prod_le_prod (fun q hq => (hLβ q (hmemT q hq).1).1.le)
        (fun q hq => (hLβ q (hmemT q hq).1).2)
    have htb := tail_bound _ _ 2147483647 rfl (by norm_num) (fun q hq => (hmemT q hq).2)
      (fun q hq q' hq' hlt => by
        obtain ⟨k, hk⟩ := hLm q (hmemT q hq).1
        obtain ⟨k', hk'⟩ := hLm q' (hmemT q' hq').1
        have hkk : k < k' := by
          by_contra hcon
          have : 2 ^ k' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have : 2 ^ (k + 1) ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        omega)
    refine hle.trans (htb.trans ?_)
    norm_num
  have hnnT : (0 : ℚ) ≤ ∏ q ∈ L.filter (fun q => ¬ q < 2147483647), β q :=
    Finset.prod_nonneg fun q hq => (hLβ q (hmemT q hq).1).1.le
  have hM : (0 : ℚ) ≤ (β 3 * β 7 * β 31 * β 127) * (β 8191 * β 131071 * β 524287) := by
    have h3 : (0 : ℚ) ≤ β 3 := by linarith [h1.1]
    have h7 : (0 : ℚ) ≤ β 7 := by linarith [h1.2.1]
    have h31 : (0 : ℚ) ≤ β 31 := by linarith [h1.2.2.1]
    have h127 : (0 : ℚ) ≤ β 127 := by linarith [h1.2.2.2]
    have h8' : (0 : ℚ) ≤ β 8191 := by linarith
    have h17' : (0 : ℚ) ≤ β 131071 := by linarith
    have h19' : (0 : ℚ) ≤ β 524287 := by linarith
    positivity
  have hmul := mul_le_mul hsmall htail hnnT hM
  rw [hsplit] at hmul
  linarith

-- Tightened master weight inequality for m >= 48, K'/K <= 1 + 1/(125000*5000), and explicit
-- Mersenne weights at 8191, 131071, 524287 with tail 536870912 / 536870911.
theorem masterU_48 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (125000 * 5000))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (D : ℚ) (hD1 : D < 1)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ D)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 48 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5)
    (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (h8 : 1 ≤ β 8191) (h17 : 1 ≤ β 131071) (h19 : 1 ≤ β 524287)
    (hfin : 281474976710657 / 281474976710656 * (β 3 * β 7 * β 31 * β 127) *
      (β 8191 * β 131071 * β 524287 * (536870912 / 536870911)) *
      ((1 + 1 / (125000 * 5000)) * (1 / (1 - D))) < 2) :
    False := by
  obtain ⟨S1, -, S2, -, -, -, -, -⟩ := facts hP hK E
  obtain ⟨g, hg⟩ := exists_child N
  have hK0 : 0 < K := K_pos hN hK
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hβpos : ∀ p ∈ P, 0 < β p := fun p hp => by
    have h0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
    linarith [(hB p hp).1]
  have hg1 : ∀ p ∈ P, g p ∈ P → g p ≠ 1 := fun p _ h h1 => by
    have := (hP _ h).1
    rw [h1] at this
    exact Nat.not_prime_one this
  have hgP : ∀ p ∈ P, g p ≠ 1 → g p ∈ P := fun p hp h =>
    S1 _ ((hg p).2.2.1 h).1 ((hg p).2.2.1 h).2.1 ((hg p).2.2.1 h).2.2 p hp (hg p).1
  have hpath := path_bound g β P.card P rfl hpos
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      have := two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1
      have := hc.1.two_le
      omega)
    (fun p hp p' hp' h he => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      exact S2 _ hc.1 hc.2.1 hc.2.2 p hp p' hp' (hg p).1 (he ▸ (hg p').1))
    (fun p hp => (hB p hp).1)
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      by_cases hsp : β (g p) = (((g p : ℕ) : ℚ) + 1) / (((g p : ℕ) : ℚ) - 1)
      · rw [hsp]
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((g p : ℕ) : ℚ) := by positivity
        exact (mul_le_mul_of_nonneg_left (hB p hp).2 h0).trans
          (B_step hc.1.two_le (two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1))
      · exact h4 p hp (g p) h (hg p).1 (hg p).2.2.2 hsp)
  have hleaf : ∀ q ∈ P.filter (fun q => g q ∉ P),
      ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N := fun q hq => by
    obtain ⟨hqP, hgq⟩ := Finset.mem_filter.mp hq
    by_cases h : g q = 1
    · exact (hg q).2.1 h
    · exact absurd (hgP q hqP h) hgq
  have hLP : ∀ q ∈ P.filter (fun q => g q ∉ P), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hsplit := Finset.prod_filter_mul_prod_filter_not (P.filter (fun q => g q ∉ P))
    (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1) β
  have hzleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      1 / (1 - D) := by
    refine (Finset.prod_le_prod
      (fun q hq => (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le)
      (fun q hq => (hB q (hLP q (Finset.mem_filter.mp hq).1)).2)).trans ?_
    refine nleaf3 (fun z hz => ⟨(hN z hz).1, hNb z hz⟩) D hD1 hD _ (fun q hq => ?_)
    obtain ⟨hqL, hne⟩ := Finset.mem_filter.mp hq
    have hqP := hP q (hLP q hqL)
    have h2 : 2 ∣ q + 1 := by
      rcases hqP.1.eq_two_or_odd with h | h
      · exact absurd h hqP.2
      · omega
    have hn3 : ¬ 3 ∣ q + 1 := fun h3 => by
      have := T3 q (hLP q hqL) h3
      have h3N := hleaf q hqL 3 (by norm_num) (by norm_num) h3
      have := hNb 3 h3N
      omega
    have hq3 : ¬ 3 ∣ q := fun h3 => by
      have hq3' : q = 3 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hqP.1).mp h3).symm
      apply hne
      subst hq3'
      have hd : (3 + 1) / 2 ^ (3 + 1).factorization 2 ∣ 4 := Nat.ordCompl_dvd (3 + 1) 2
      have hodd : ¬ 2 ∣ (3 + 1) / 2 ^ (3 + 1).factorization 2 :=
        Nat.not_dvd_ordCompl Nat.prime_two (by norm_num)
      have hle := Nat.le_of_dvd (by norm_num) hd
      generalize (3 + 1) / 2 ^ (3 + 1).factorization 2 = d at hd hodd hle
      interval_cases d <;> omega
    exact ⟨h2, by omega, hne, hleaf q hqL⟩
  have hmleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => ¬ (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (β 8191 * β 131071 * β 524287 * (536870912 / 536870911)) := by
    refine mersenne_bound19 β _ (fun q hq => (hP q (hLP q (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => ?_)
      (fun q hq => ⟨hβpos q (hLP q (Finset.mem_filter.mp hq).1),
        (hB q (hLP q (Finset.mem_filter.mp hq).1)).2⟩) h1 h8 h17 h19
    obtain ⟨hqL, hzd⟩ := Finset.mem_filter.mp hq
    have h1' : (q + 1) / 2 ^ (q + 1).factorization 2 = 1 := not_not.mp hzd
    have hmul := Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2
    rw [h1', mul_one] at hmul
    exact ⟨(q + 1).factorization 2, hmul.symm⟩
  have hM0 : (0 : ℚ) ≤ (β 3 * β 7 * β 31 * β 127) *
      (β 8191 * β 131071 * β 524287 * (536870912 / 536870911)) := by
    have h3 : (0 : ℚ) ≤ β 3 := by linarith [h1.1]
    have h7 : (0 : ℚ) ≤ β 7 := by linarith [h1.2.1]
    have h31 : (0 : ℚ) ≤ β 31 := by linarith [h1.2.2.1]
    have h127 : (0 : ℚ) ≤ β 127 := by linarith [h1.2.2.2]
    have h8' : (0 : ℚ) ≤ β 8191 := by linarith
    have h17' : (0 : ℚ) ≤ β 131071 := by linarith
    have h19' : (0 : ℚ) ≤ β 524287 := by linarith
    positivity
  have hNL0 : (0 : ℚ) ≤ 1 / (1 - D) := div_nonneg zero_le_one (by linarith)
  have hprodL : ∏ q ∈ P.filter (fun q => g q ∉ P), β q ≤
      (1 / (1 - D)) * ((β 3 * β 7 * β 31 * β 127) *
        (β 8191 * β 131071 * β 524287 * (536870912 / 536870911))) := by
    rw [← hsplit]
    refine mul_le_mul hzleaves hmleaves ?_ hNL0
    exact Finset.prod_nonneg fun q hq =>
      (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hEq : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
    have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
    have hcast : ((2 : ℚ) ^ m + 1) * K' * ∏ p ∈ P, ((p : ℚ) + 1) =
        2 ^ (m + 1) * K * ∏ p ∈ P, (p : ℚ) := by
      have h := congrArg (Nat.cast : ℕ → ℚ) E
      push_cast at h
      exact h
    have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
      field_simp
    have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
    rw [e]
    field_simp
    rw [pow_succ] at hcast
    linarith
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 281474976710657 / 281474976710656 := by
    have h2 : (2 : ℚ) ^ 48 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have hinv : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 48 := one_div_le_one_div_of_le (by positivity) h2
    have h48 : (2 : ℚ) ^ 48 = 281474976710656 := by norm_num
    rw [h48] at hinv
    linarith
  have hP0 : (0 : ℚ) ≤ ∏ p ∈ P, (1 + 1 / (p : ℚ)) := Finset.prod_nonneg fun p _ => by positivity
  have hP_le : ∏ p ∈ P, (1 + 1 / (p : ℚ)) ≤
      (1 / (1 - D)) * ((β 3 * β 7 * β 31 * β 127) *
        (β 8191 * β 131071 * β 524287 * (536870912 / 536870911))) :=
    hpath.trans hprodL
  have hstep1 : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) ≤
      281474976710657 / 281474976710656 * (1 + 1 / (125000 * 5000)) :=
    mul_le_mul hT hKr (div_nonneg (Nat.cast_nonneg _) hKq.le) (by norm_num)
  have hstep2 : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) ≤
      (281474976710657 / 281474976710656 * (1 + 1 / (125000 * 5000))) *
        ((1 / (1 - D)) * ((β 3 * β 7 * β 31 * β 127) *
          (β 8191 * β 131071 * β 524287 * (536870912 / 536870911)))) :=
    mul_le_mul hstep1 hP_le hP0 (by norm_num)
  linarith

-- Prime parent lower bounds under gap >= 13947 (handling allowed cross-primes 607 and 7933).

theorem prime_131071 : Nat.Prime 131071 := by norm_num

theorem T223_13947_m1 {p e : ℕ} (hp : p.Prime) (he : e < 14) (hp_eq : p = 2 * 223 * 2 ^ e - 1)
    (h1783 : p ≠ 1783) : False := by
  subst hp_eq
  interval_cases e
  · exact absurd hp (not_prime_of_mul (a := 5) (b := 89) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 297) (by decide) (by decide) (by decide))
  · exact h1783 (by decide)
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 1189) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 5) (b := 1427) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 4757) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 17) (b := 1679) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 19029) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 5) (b := 22835) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 76117) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 13) (b := 35131) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 304469) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 5) (b := 365363) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 1217877) (by decide) (by decide) (by decide))

theorem T223_13947 {p : ℕ} (hp : p.Prime) (hd : 223 ∣ p + 1) (hsq : ¬ 223 * 223 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 223 ∨ r = 607 ∨ r = 7933 ∨ 13947 ≤ r)
    (h1783 : p ≠ 1783) :
    6220361 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 14 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 14 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    exact T223_13947_m1 hp he (by omega) h1783
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 223 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with rfl | rfl | rfl | h
    · exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · by_cases hk1 : k = 1
      · subst hk1
        have hj' : p + 1 = 2 * 223 * 607 * 2 ^ e := by rw [hj]; ring
        have hlt2 : 2 ^ e < 2 ^ 5 := by generalize 2 ^ e = t at hj'; norm_num; omega
        have he : e < 5 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
        obtain rfl : p = 2 * 223 * 607 * 2 ^ e - 1 := by omega
        clear hj hj' hd hsq hgap hlt hp2 hmo he0 hlt2 hrp hrk hk
        interval_cases e
        · exact absurd hp (not_prime_of_mul (a := 11) (b := 24611) (by decide) (by decide) (by decide))
        · exact absurd hp (not_prime_of_mul (a := 3) (b := 180481) (by decide) (by decide) (by decide))
        · exact absurd hp (not_prime_of_mul (a := 13) (b := 83299) (by decide) (by decide) (by decide))
        · exact absurd hp (not_prime_of_mul (a := 3) (b := 721925) (by decide) (by decide) (by decide))
        · exact absurd hp (not_prime_of_mul (a := 7) (b := 618793) (by decide) (by decide) (by decide))
      · have hko : Odd k := (Nat.odd_mul.mp hmo).2
        obtain ⟨r', k', hr', hr'2, rfl, hk'⟩ := odd_prime_factor hko hk1
        have hr'p : r' ∣ p + 1 := ⟨2 * 223 * 607 * 2 ^ e * k', by rw [hj]; ring⟩
        have hr'le : r' ≤ 2 ^ e * (r' * k') :=
          le_trans (Nat.le_mul_of_pos_right r' hk') (Nat.le_mul_of_pos_left _ he0)
        have hge607 : 607 ≤ r' := by
          rcases hgap r' hr' hr'2 hr'p with rfl | h' | h' | h'
          · exact absurd ⟨2 * 607 * 2 ^ e * k', by rw [hj]; ring⟩ hsq
          · omega
          · omega
          · omega
        have hj' : p + 1 = 2 * 223 * 607 * (2 ^ e * (r' * k')) := by rw [hj]; ring
        have hbig : 607 ≤ 2 ^ e * (r' * k') := le_trans hge607 hr'le
        have hmul : 2 * 223 * 607 * 607 ≤ p + 1 := by
          rw [hj']; exact Nat.mul_le_mul_left _ hbig
        exact hlt (by linarith)
    · by_cases hk1 : k = 1
      · subst hk1
        have hj' : p + 1 = 2 * 223 * 7933 * 2 ^ e := by rw [hj]; ring
        have hlt2 : 2 ^ e < 2 ^ 1 := by generalize 2 ^ e = t at hj'; norm_num; omega
        have he : e = 0 := by
          have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2; omega
        subst he
        obtain rfl : p = 3538117 := by norm_num at hj'; omega
        exact absurd hp (not_prime_of_mul (a := 11) (b := 321647) (by decide) (by decide) (by decide))
      · have hko : Odd k := (Nat.odd_mul.mp hmo).2
        have hk3 : 3 ≤ k := by obtain ⟨j, rfl⟩ := hko; omega
        have hj' : p + 1 = 2 * 223 * 7933 * (2 ^ e * k) := by rw [hj]; ring
        have htk : 3 ≤ 2 ^ e * k := le_trans hk3 (Nat.le_mul_of_pos_left k he0)
        generalize 2 ^ e * k = t at hj' htk; omega
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T607_9630661 {p : ℕ} (hp : p.Prime) (hd : 607 ∣ p + 1) (hsq : ¬ 607 * 607 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 607 ∨ 7933 ≤ r)
    (h1213 : p ≠ 1213) (h19423 : p ≠ 19423) :
    9630661 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 13 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 13 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 607 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e
    · exact h1213 (by norm_num)
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 809) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 971) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 3237) (by norm_num) (by norm_num) (by norm_num))
    · exact h19423 (by norm_num)
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 12949) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 15539) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 51797) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 11) (b := 28253) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 207189) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 248627) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 828757) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 29) (b := 171467) (by norm_num) (by norm_num) (by norm_num))
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 607 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with h | h
    · subst h; exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T607_13947 {p : ℕ} (hp : p.Prime) (hd : 607 ∣ p + 1) (hsq : ¬ 607 * 607 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 607 ∨ 13947 ≤ r)
    (h1213 : p ≠ 1213) (h19423 : p ≠ 19423) :
    16931657 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 14 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 14 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 607 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e
    · exact h1213 (by norm_num)
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 809) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 971) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 3237) (by norm_num) (by norm_num) (by norm_num))
    · exact h19423 (by norm_num)
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 12949) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 15539) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 51797) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 11) (b := 28253) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 207189) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 248627) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 828757) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 29) (b := 171467) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 3315029) (by norm_num) (by norm_num) (by norm_num))
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 607 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with h | h
    · subst h; exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T7933_13947 {p : ℕ} (hp : p.Prime) (hd : 7933 ∣ p + 1) (hsq : ¬ 7933 * 7933 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 7933 ∨ 13947 ≤ r)
    (h63463 : p ≠ 63463) :
    1015423 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 6 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 6 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 7933 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 3173) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 10577) (by norm_num) (by norm_num) (by norm_num))
    · exact h63463 (by norm_num)
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 42309) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 50771) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 169237) (by norm_num) (by norm_num) (by norm_num))
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 7933 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with h | h
    · subst h; exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T63463_13947 {p : ℕ} (hp : p.Prime) (hd : 63463 ∣ p + 1) (hsq : ¬ 63463 * 63463 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 63463 ∨ 13947 ≤ r) :
    1770236921 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 14 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 14 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 63463 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 25385) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 84617) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 7) (b := 72529) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 338469) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 406163) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 1353877) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 17) (b := 477839) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 5415509) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 6498611) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 21662037) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 373) (b := 348451) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 86648149) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 103977779) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 346592597) (by norm_num) (by norm_num) (by norm_num))
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 63463 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with h | h
    · subst h; exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T131071_13947 {p : ℕ} (hp : p.Prime) (hd : 131071 ∣ p + 1) (hsq : ¬ 131071 * 131071 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 131071 ∨ 13947 ≤ r) :
    4194271 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 4 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 4 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 131071 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e
    · exact absurd hp (not_prime_of_mul (a := 11) (b := 23831) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 174761) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 13) (b := 80659) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 699045) (by norm_num) (by norm_num) (by norm_num))
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 131071 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with h | h
    · subst h; exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T524287_no104 {p : ℕ} (hp : p.Prime) (hd : 524287 ∣ p + 1) (hsq : ¬ 524287 * 524287 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 524287 ∨ 13947 ≤ r)
    (h104 : p ≠ 1048573) :
    16777183 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 4 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 4 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 524287 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e
    · exact h104 (by norm_num)
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 699049) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 838859) (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 2796197) (by norm_num) (by norm_num) (by norm_num))
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 524287 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with h | h
    · subst h; exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

-- Shared 9-prime simple gap: every simple prime outside {3, 5, 7, 19, 31, 223, 607, 3967, 7933}
-- is at least 13947.
theorem gap9 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h7933 : 7933 ∈ P) :
    ∀ q ∈ P, q ≠ 3 → q ≠ 5 → q ≠ 7 → q ≠ 19 → q ≠ 31 → q ≠ 223 → q ≠ 607 → q ≠ 3967 →
      q ≠ 7933 → 13947 ≤ q := by
  have hA : ({3, 5, 7, 19, 31, 223, 607, 3967, 7933} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h607
    · exact h3967
    · exact h7933
  intro q hq e3 e5 e7 e19 e31 e223 e607 e3967 e7933
  have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
  rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
  have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933} : Finset ℕ), (p + 1) =
      526861737677291520 := by decide
  have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933} : Finset ℕ), p =
      263449757251770495 := by decide
  rw [e1, e2] at h
  omega

-- Case 1: 19423 ∉ P and 63463 ∉ P (eliminates all four (131071, 524287) subcases at once).
theorem node_no19423_no63463 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hPN : ∀ p ∈ P, p ∉ N)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (125000 * 5000)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hN25 : ∀ z ∈ N, 25000 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        4 / 3 * (75000 / 74996) * (1 / 24999))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 48 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h7933 : 7933 ∈ P)
    (h8191 : 8191 ∉ P) (h19423 : 19423 ∉ P) (h63463 : 63463 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h7933N : 7933 ∉ N := fun h => by have := hN25 7933 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have T3967 : ∀ p ∈ P, 3967 ∣ p + 1 → p = 7933 := fun p hp hd =>
    S2 3967 (by norm_num) (by norm_num) h3967N p hp 7933 h7933 hd (by norm_num)
  have gap := gap9 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h7933
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 7933 ∨ 13947 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hN25 r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3; · exact Or.inl e3
      by_cases e5 : r = 5; · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7; · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19; · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      by_cases e607 : r = 607; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e607))))))
      by_cases e3967 : r = 3967; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e3967)))))))
      by_cases e7933 : r = 7933; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e7933))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e7933)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (9630662 / 9630660)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (9630662 / 9630660))) else
      if p = 19 then 20 / 19 * (608 / 607 * (9630662 / 9630660)) else
      if p = 607 then 608 / 607 * (9630662 / 9630660) else
      if p = 7 then 8 / 7 * (224 / 223 * (6220362 / 6220360)) else
      if p = 223 then 224 / 223 * (6220362 / 6220360) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (7934 / 7933 * (1015424 / 1015422))) else
      if p = 3967 then 3968 / 3967 * (7934 / 7933 * (1015424 / 1015422)) else
      if p = 7933 then 7934 / 7933 * (1015424 / 1015422) else
      if p = 127 then 1 else
      if p = 8191 then 1 else
      if p = 131071 then 131072 / 131071 * (4194272 / 4194270) else
      if p = 524287 then 524288 / 524287 * (1048574 / 1048572) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (9630662 / 9630660)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (9630662 / 9630660))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (9630662 / 9630660)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (9630662 / 9630660) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (6220362 / 6220360)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (6220362 / 6220360) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (7934 / 7933 * (1015424 / 1015422))) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (7934 / 7933 * (1015424 / 1015422)) := by rw [hβ]; norm_num
  have b7933 : β 7933 = 7934 / 7933 * (1015424 / 1015422) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 1 := by rw [hβ]; norm_num
  have b131071 : β 131071 = 131072 / 131071 * (4194272 / 4194270) := by rw [hβ]; norm_num
  have b524287 : β 524287 = 524288 / 524287 * (1048574 / 1048572) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 7933 → c ≠ 127 → c ≠ 8191 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e127 e8191 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e7933, if_neg e127, if_neg e8191, if_neg e131, if_neg e524]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3; · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5; · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19; · subst e19; rw [b19]; norm_num
    by_cases e607 : p = 607; · subst e607; rw [b607]; norm_num
    by_cases e7 : p = 7; · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223; · subst e223; rw [b223]; norm_num
    by_cases e31 : p = 31; · subst e31; rw [b31]; norm_num
    by_cases e3967 : p = 3967; · subst e3967; rw [b3967]; norm_num
    by_cases e7933 : p = 7933; · subst e7933; rw [b7933]; norm_num
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; exact absurd hp h8191
    by_cases e131 : p = 131071; · subst e131; rw [b131071]; norm_num
    by_cases e524 : p = 524287; · subst e524; rw [b524287]; norm_num
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e127 e8191 e131 e524]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU_48 hP hN hK hKr hNb (4 / 3 * (75000 / 74996) * (1 / 24999)) (by norm_num) hD E
    hm T3 β hB ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3; · subst e3; obtain rfl : p = 5 := T3 p hp hd; rw [b3, b5]; norm_num
    by_cases e5 : c = 5; · subst e5; obtain rfl : p = 19 := T5 p hp hd; rw [b5, b19]; norm_num
    by_cases e19 : c = 19; · subst e19; obtain rfl : p = 607 := T19 p hp hd; rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 9630661 ≤ p := T607_9630661 (hP p hp).1 hd
        (S4b 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            by_cases e3967 : r = 3967
            · subst e3967; obtain rfl := T3967 p hp hrd; norm_num at hd
            · omega)
        (fun h => by
          have := gap 1213 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
        (fun h => h19423 (h ▸ hp))
      rw [b607]
      exact step_ge (t := 9630661) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 6220361 ≤ p := T223_13947 (hP p hp).1 hd
        (S4b 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            by_cases e3967 : r = 3967
            · subst e3967; obtain rfl := T3967 p hp hrd; norm_num at hd
            · omega)
        (fun h => by
          have := gap 1783 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
      rw [b223]
      exact step_ge (t := 6220361) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967; · subst e3967; obtain rfl : p = 7933 := T3967 p hp hd; rw [b3967, b7933]; norm_num
    by_cases e7933 : c = 7933
    · subst e7933
      have hge : 1015423 ≤ p := T7933_13947 (hP p hp).1 hd
        (S4b 7933 (by norm_num) (by norm_num) h7933N p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
        (fun h => h63463 (h ▸ hp))
      rw [b7933]
      exact step_ge (t := 1015423) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191; · subst e8191; exact absurd hc h8191
    by_cases e131 : c = 131071
    · subst e131
      have hge : 4194271 ≤ p := T131071_13947 (hP p hp).1 hd
        (S4b 131071 (hP 131071 hc).1 (by norm_num) (hPN 131071 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b131071]
      exact step_ge (t := 4194271) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e524 : c = 524287
    · subst e524
      have hge : 1048573 ≤ p := by
        have := two_mul_le (hP 524287 hc).1 (by norm_num) (hP p hp).1 (hP p hp).2 hd
        omega
      rw [b524287]
      exact step_ge (t := 1048573) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e127 e8191 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]
  · rw [b131071]; norm_num
  · rw [b524287]; norm_num
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num

-- Case 2: 19423 ∉ P, 63463 ∈ P, 131071 ∉ P, 524287 ∉ P.
theorem node_no19423_63463_noM {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hPN : ∀ p ∈ P, p ∉ N)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (125000 * 5000)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hN25 : ∀ z ∈ N, 25000 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        4 / 3 * (75000 / 74996) * (1 / 24999))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 48 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h7933 : 7933 ∈ P)
    (h63463 : 63463 ∈ P) (h8191 : 8191 ∉ P) (h19423 : 19423 ∉ P)
    (h131071 : 131071 ∉ P) (h524287 : 524287 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h7933N : 7933 ∉ N := fun h => by have := hN25 7933 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have T3967 : ∀ p ∈ P, 3967 ∣ p + 1 → p = 7933 := fun p hp hd =>
    S2 3967 (by norm_num) (by norm_num) h3967N p hp 7933 h7933 hd (by norm_num)
  have T7933 : ∀ p ∈ P, 7933 ∣ p + 1 → p = 63463 := fun p hp hd =>
    S2 7933 (by norm_num) (by norm_num) h7933N p hp 63463 h63463 hd (by norm_num)
  have gap := gap9 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h7933
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 7933 ∨ 13947 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hN25 r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3; · exact Or.inl e3
      by_cases e5 : r = 5; · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7; · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19; · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      by_cases e607 : r = 607; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e607))))))
      by_cases e3967 : r = 3967; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e3967)))))))
      by_cases e7933 : r = 7933; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e7933))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e7933)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656))) else
      if p = 19 then 20 / 19 * (608 / 607 * (16931658 / 16931656)) else
      if p = 607 then 608 / 607 * (16931658 / 16931656) else
      if p = 7 then 8 / 7 * (224 / 223 * (6220362 / 6220360)) else
      if p = 223 then 224 / 223 * (6220362 / 6220360) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)))) else
      if p = 3967 then 3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920))) else
      if p = 7933 then 7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)) else
      if p = 63463 then 63464 / 63463 * (1770236922 / 1770236920) else
      if p = 127 then 1 else
      if p = 8191 then 1 else
      if p = 131071 then 1 else
      if p = 524287 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (16931658 / 16931656)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (16931658 / 16931656) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (6220362 / 6220360)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (6220362 / 6220360) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)))) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920))) := by rw [hβ]; norm_num
  have b7933 : β 7933 = 7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)) := by rw [hβ]; norm_num
  have b63463 : β 63463 = 63464 / 63463 * (1770236922 / 1770236920) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 1 := by rw [hβ]; norm_num
  have b131071 : β 131071 = 1 := by rw [hβ]; norm_num
  have b524287 : β 524287 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 7933 → c ≠ 63463 → c ≠ 127 → c ≠ 8191 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e63463 e127 e8191 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e7933, if_neg e63463, if_neg e127, if_neg e8191, if_neg e131,
        if_neg e524]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3; · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5; · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19; · subst e19; rw [b19]; norm_num
    by_cases e607 : p = 607; · subst e607; rw [b607]; norm_num
    by_cases e7 : p = 7; · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223; · subst e223; rw [b223]; norm_num
    by_cases e31 : p = 31; · subst e31; rw [b31]; norm_num
    by_cases e3967 : p = 3967; · subst e3967; rw [b3967]; norm_num
    by_cases e7933 : p = 7933; · subst e7933; rw [b7933]; norm_num
    by_cases e63463 : p = 63463; · subst e63463; rw [b63463]; norm_num
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; exact absurd hp h8191
    by_cases e131 : p = 131071; · subst e131; exact absurd hp h131071
    by_cases e524 : p = 524287; · subst e524; exact absurd hp h524287
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e63463 e127 e8191 e131 e524]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU_48 hP hN hK hKr hNb (4 / 3 * (75000 / 74996) * (1 / 24999)) (by norm_num) hD E
    hm T3 β hB ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3; · subst e3; obtain rfl : p = 5 := T3 p hp hd; rw [b3, b5]; norm_num
    by_cases e5 : c = 5; · subst e5; obtain rfl : p = 19 := T5 p hp hd; rw [b5, b19]; norm_num
    by_cases e19 : c = 19; · subst e19; obtain rfl : p = 607 := T19 p hp hd; rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 16931657 ≤ p := T607_13947 (hP p hp).1 hd
        (S4b 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            by_cases e3967 : r = 3967
            · subst e3967; obtain rfl := T3967 p hp hrd; norm_num at hd
            by_cases e7933 : r = 7933
            · subst e7933; obtain rfl := T7933 p hp hrd; norm_num at hd
            · omega)
        (fun h => by
          have := gap 1213 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
        (fun h => h19423 (h ▸ hp))
      rw [b607]
      exact step_ge (t := 16931657) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 6220361 ≤ p := T223_13947 (hP p hp).1 hd
        (S4b 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            by_cases e3967 : r = 3967
            · subst e3967; obtain rfl := T3967 p hp hrd; norm_num at hd
            · omega)
        (fun h => by
          have := gap 1783 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
      rw [b223]
      exact step_ge (t := 6220361) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967; · subst e3967; obtain rfl : p = 7933 := T3967 p hp hd; rw [b3967, b7933]; norm_num
    by_cases e7933 : c = 7933; · subst e7933; obtain rfl : p = 63463 := T7933 p hp hd; rw [b7933, b63463]; norm_num
    by_cases e63463 : c = 63463
    · subst e63463
      have hge : 1770236921 ≤ p := T63463_13947 (hP p hp).1 hd
        (S4b 63463 (hP 63463 hc).1 (by norm_num) (hPN 63463 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b63463]
      exact step_ge (t := 1770236921) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191; · subst e8191; exact absurd hc h8191
    by_cases e131 : c = 131071; · subst e131; exact absurd hc h131071
    by_cases e524 : c = 524287; · subst e524; exact absurd hc h524287
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e63463 e127 e8191 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]
  · rw [b131071]
  · rw [b524287]
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num

-- Case 3: 19423 ∉ P, 63463 ∈ P, and every z ∈ N has z % 3 ≠ 1 (kills all four (131071, 524287) cases).
theorem node_no19423_63463_s2only {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hPN : ∀ p ∈ P, p ∉ N)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (125000 * 5000)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hN25 : ∀ z ∈ N, 25000 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        2 / 3 * (75000 / 74998) * (1 / 24999) + 4 / 3 * (75000 / 74996) * (1 / 300000000))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 48 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h7933 : 7933 ∈ P)
    (h63463 : 63463 ∈ P) (h8191 : 8191 ∉ P) (h19423 : 19423 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h7933N : 7933 ∉ N := fun h => by have := hN25 7933 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have T3967 : ∀ p ∈ P, 3967 ∣ p + 1 → p = 7933 := fun p hp hd =>
    S2 3967 (by norm_num) (by norm_num) h3967N p hp 7933 h7933 hd (by norm_num)
  have T7933 : ∀ p ∈ P, 7933 ∣ p + 1 → p = 63463 := fun p hp hd =>
    S2 7933 (by norm_num) (by norm_num) h7933N p hp 63463 h63463 hd (by norm_num)
  have gap := gap9 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h7933
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 7933 ∨ 13947 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hN25 r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3; · exact Or.inl e3
      by_cases e5 : r = 5; · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7; · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19; · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      by_cases e607 : r = 607; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e607))))))
      by_cases e3967 : r = 3967; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e3967)))))))
      by_cases e7933 : r = 7933; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e7933))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e7933)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656))) else
      if p = 19 then 20 / 19 * (608 / 607 * (16931658 / 16931656)) else
      if p = 607 then 608 / 607 * (16931658 / 16931656) else
      if p = 7 then 8 / 7 * (224 / 223 * (6220362 / 6220360)) else
      if p = 223 then 224 / 223 * (6220362 / 6220360) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)))) else
      if p = 3967 then 3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920))) else
      if p = 7933 then 7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)) else
      if p = 63463 then 63464 / 63463 * (1770236922 / 1770236920) else
      if p = 127 then 1 else
      if p = 8191 then 1 else
      if p = 131071 then 131072 / 131071 * (4194272 / 4194270) else
      if p = 524287 then 524288 / 524287 * (1048574 / 1048572) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (16931658 / 16931656)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (16931658 / 16931656) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (6220362 / 6220360)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (6220362 / 6220360) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)))) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920))) := by rw [hβ]; norm_num
  have b7933 : β 7933 = 7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)) := by rw [hβ]; norm_num
  have b63463 : β 63463 = 63464 / 63463 * (1770236922 / 1770236920) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 1 := by rw [hβ]; norm_num
  have b131071 : β 131071 = 131072 / 131071 * (4194272 / 4194270) := by rw [hβ]; norm_num
  have b524287 : β 524287 = 524288 / 524287 * (1048574 / 1048572) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 7933 → c ≠ 63463 → c ≠ 127 → c ≠ 8191 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e63463 e127 e8191 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e7933, if_neg e63463, if_neg e127, if_neg e8191, if_neg e131,
        if_neg e524]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3; · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5; · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19; · subst e19; rw [b19]; norm_num
    by_cases e607 : p = 607; · subst e607; rw [b607]; norm_num
    by_cases e7 : p = 7; · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223; · subst e223; rw [b223]; norm_num
    by_cases e31 : p = 31; · subst e31; rw [b31]; norm_num
    by_cases e3967 : p = 3967; · subst e3967; rw [b3967]; norm_num
    by_cases e7933 : p = 7933; · subst e7933; rw [b7933]; norm_num
    by_cases e63463 : p = 63463; · subst e63463; rw [b63463]; norm_num
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; exact absurd hp h8191
    by_cases e131 : p = 131071; · subst e131; rw [b131071]; norm_num
    by_cases e524 : p = 524287; · subst e524; rw [b524287]; norm_num
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e63463 e127 e8191 e131 e524]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU_48 hP hN hK hKr hNb
    (2 / 3 * (75000 / 74998) * (1 / 24999) + 4 / 3 * (75000 / 74996) * (1 / 300000000))
    (by norm_num) hD E hm T3 β hB ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3; · subst e3; obtain rfl : p = 5 := T3 p hp hd; rw [b3, b5]; norm_num
    by_cases e5 : c = 5; · subst e5; obtain rfl : p = 19 := T5 p hp hd; rw [b5, b19]; norm_num
    by_cases e19 : c = 19; · subst e19; obtain rfl : p = 607 := T19 p hp hd; rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 16931657 ≤ p := T607_13947 (hP p hp).1 hd
        (S4b 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            by_cases e3967 : r = 3967
            · subst e3967; obtain rfl := T3967 p hp hrd; norm_num at hd
            by_cases e7933 : r = 7933
            · subst e7933; obtain rfl := T7933 p hp hrd; norm_num at hd
            · omega)
        (fun h => by
          have := gap 1213 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
        (fun h => h19423 (h ▸ hp))
      rw [b607]
      exact step_ge (t := 16931657) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 6220361 ≤ p := T223_13947 (hP p hp).1 hd
        (S4b 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            by_cases e3967 : r = 3967
            · subst e3967; obtain rfl := T3967 p hp hrd; norm_num at hd
            · omega)
        (fun h => by
          have := gap 1783 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
      rw [b223]
      exact step_ge (t := 6220361) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967; · subst e3967; obtain rfl : p = 7933 := T3967 p hp hd; rw [b3967, b7933]; norm_num
    by_cases e7933 : c = 7933; · subst e7933; obtain rfl : p = 63463 := T7933 p hp hd; rw [b7933, b63463]; norm_num
    by_cases e63463 : c = 63463
    · subst e63463
      have hge : 1770236921 ≤ p := T63463_13947 (hP p hp).1 hd
        (S4b 63463 (hP 63463 hc).1 (by norm_num) (hPN 63463 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b63463]
      exact step_ge (t := 1770236921) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191; · subst e8191; exact absurd hc h8191
    by_cases e131 : c = 131071
    · subst e131
      have hge : 4194271 ≤ p := T131071_13947 (hP p hp).1 hd
        (S4b 131071 (hP 131071 hc).1 (by norm_num) (hPN 131071 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b131071]
      exact step_ge (t := 4194271) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e524 : c = 524287
    · subst e524
      have hge : 1048573 ≤ p := by
        have := two_mul_le (hP 524287 hc).1 (by norm_num) (hP p hp).1 (hP p hp).2 hd
        omega
      rw [b524287]
      exact step_ge (t := 1048573) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e63463 e127 e8191 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]
  · rw [b131071]; norm_num
  · rw [b524287]; norm_num
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num

-- Case 4: 19423 ∉ P, 63463 ∈ P, 131071 ∉ P, 524287 ∈ P, 1048573 ∉ P.
theorem node_no19423_63463_no131_524_no104 {m K K' : ℕ} {N P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hPN : ∀ p ∈ P, p ∉ N)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (125000 * 5000)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hN25 : ∀ z ∈ N, 25000 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        4 / 3 * (75000 / 74996) * (1 / 24999))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 48 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h7933 : 7933 ∈ P)
    (h63463 : 63463 ∈ P) (h8191 : 8191 ∉ P) (h19423 : 19423 ∉ P)
    (h131071 : 131071 ∉ P) (h1048573 : 1048573 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h7933N : 7933 ∉ N := fun h => by have := hN25 7933 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have T3967 : ∀ p ∈ P, 3967 ∣ p + 1 → p = 7933 := fun p hp hd =>
    S2 3967 (by norm_num) (by norm_num) h3967N p hp 7933 h7933 hd (by norm_num)
  have T7933 : ∀ p ∈ P, 7933 ∣ p + 1 → p = 63463 := fun p hp hd =>
    S2 7933 (by norm_num) (by norm_num) h7933N p hp 63463 h63463 hd (by norm_num)
  have gap := gap9 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h7933
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 7933 ∨ 13947 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hN25 r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3; · exact Or.inl e3
      by_cases e5 : r = 5; · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7; · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19; · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      by_cases e607 : r = 607; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e607))))))
      by_cases e3967 : r = 3967; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e3967)))))))
      by_cases e7933 : r = 7933; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e7933))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e7933)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656))) else
      if p = 19 then 20 / 19 * (608 / 607 * (16931658 / 16931656)) else
      if p = 607 then 608 / 607 * (16931658 / 16931656) else
      if p = 7 then 8 / 7 * (224 / 223 * (6220362 / 6220360)) else
      if p = 223 then 224 / 223 * (6220362 / 6220360) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)))) else
      if p = 3967 then 3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920))) else
      if p = 7933 then 7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)) else
      if p = 63463 then 63464 / 63463 * (1770236922 / 1770236920) else
      if p = 127 then 1 else
      if p = 8191 then 1 else
      if p = 131071 then 1 else
      if p = 524287 then 524288 / 524287 * (16777184 / 16777182) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (16931658 / 16931656))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (16931658 / 16931656)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (16931658 / 16931656) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (6220362 / 6220360)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (6220362 / 6220360) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)))) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920))) := by rw [hβ]; norm_num
  have b7933 : β 7933 = 7934 / 7933 * (63464 / 63463 * (1770236922 / 1770236920)) := by rw [hβ]; norm_num
  have b63463 : β 63463 = 63464 / 63463 * (1770236922 / 1770236920) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 1 := by rw [hβ]; norm_num
  have b131071 : β 131071 = 1 := by rw [hβ]; norm_num
  have b524287 : β 524287 = 524288 / 524287 * (16777184 / 16777182) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 7933 → c ≠ 63463 → c ≠ 127 → c ≠ 8191 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e63463 e127 e8191 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e7933, if_neg e63463, if_neg e127, if_neg e8191, if_neg e131,
        if_neg e524]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3; · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5; · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19; · subst e19; rw [b19]; norm_num
    by_cases e607 : p = 607; · subst e607; rw [b607]; norm_num
    by_cases e7 : p = 7; · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223; · subst e223; rw [b223]; norm_num
    by_cases e31 : p = 31; · subst e31; rw [b31]; norm_num
    by_cases e3967 : p = 3967; · subst e3967; rw [b3967]; norm_num
    by_cases e7933 : p = 7933; · subst e7933; rw [b7933]; norm_num
    by_cases e63463 : p = 63463; · subst e63463; rw [b63463]; norm_num
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; exact absurd hp h8191
    by_cases e131 : p = 131071; · subst e131; exact absurd hp h131071
    by_cases e524 : p = 524287; · subst e524; rw [b524287]; norm_num
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e63463 e127 e8191 e131 e524]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU_48 hP hN hK hKr hNb (4 / 3 * (75000 / 74996) * (1 / 24999)) (by norm_num) hD E
    hm T3 β hB ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3; · subst e3; obtain rfl : p = 5 := T3 p hp hd; rw [b3, b5]; norm_num
    by_cases e5 : c = 5; · subst e5; obtain rfl : p = 19 := T5 p hp hd; rw [b5, b19]; norm_num
    by_cases e19 : c = 19; · subst e19; obtain rfl : p = 607 := T19 p hp hd; rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 16931657 ≤ p := T607_13947 (hP p hp).1 hd
        (S4b 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            by_cases e3967 : r = 3967
            · subst e3967; obtain rfl := T3967 p hp hrd; norm_num at hd
            by_cases e7933 : r = 7933
            · subst e7933; obtain rfl := T7933 p hp hrd; norm_num at hd
            · omega)
        (fun h => by
          have := gap 1213 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
        (fun h => h19423 (h ▸ hp))
      rw [b607]
      exact step_ge (t := 16931657) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 6220361 ≤ p := T223_13947 (hP p hp).1 hd
        (S4b 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            by_cases e3967 : r = 3967
            · subst e3967; obtain rfl := T3967 p hp hrd; norm_num at hd
            · omega)
        (fun h => by
          have := gap 1783 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
      rw [b223]
      exact step_ge (t := 6220361) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967; · subst e3967; obtain rfl : p = 7933 := T3967 p hp hd; rw [b3967, b7933]; norm_num
    by_cases e7933 : c = 7933; · subst e7933; obtain rfl : p = 63463 := T7933 p hp hd; rw [b7933, b63463]; norm_num
    by_cases e63463 : c = 63463
    · subst e63463
      have hge : 1770236921 ≤ p := T63463_13947 (hP p hp).1 hd
        (S4b 63463 (hP 63463 hc).1 (by norm_num) (hPN 63463 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b63463]
      exact step_ge (t := 1770236921) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191; · subst e8191; exact absurd hc h8191
    by_cases e131 : c = 131071; · subst e131; exact absurd hc h131071
    by_cases e524 : c = 524287
    · subst e524
      have hge : 16777183 ≤ p := T524287_no104 (hP p hp).1 hd
        (S4b 524287 (hP 524287 hc).1 (by norm_num) (hPN 524287 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
        (fun h => h1048573 (h ▸ hp))
      rw [b524287]
      exact step_ge (t := 16777183) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e7933 e63463 e127 e8191 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]
  · rw [b131071]
  · rw [b524287]; norm_num
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num

-- Boosted simple-prime gap in H1 (19423 | n): every simple prime outside the 10-prime set is >= 49468.
theorem gap_H1 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h7933 : 7933 ∈ P) (h19423 : 19423 ∈ P) :
    ∀ q ∈ P, q < 49468 →
      q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 7933 ∨
        q = 19423 := by
  have hA : ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 19423} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h607
    · exact h3967
    · exact h7933
    · exact h19423
  intro q hq hlt
  by_cases hqA : q ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 19423} : Finset ℕ)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hqA; exact hqA
  · exfalso
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 19423} : Finset ℕ), (p + 1) =
        10233762392643710484480 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 19423} : Finset ℕ), p =
        5116984635101138324385 := by decide
    rw [e1, e2] at h
    omega

-- Boosted prime gap in H2 (63463, 131071 simple): every prime of n < 20699 is in the 10-prime set.
theorem gap_H2 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h7933 : 7933 ∈ P)
    (h63463 : 63463 ∈ P) (h131071 : 131071 ∈ P) :
    ∀ q ∈ P, q < 20699 →
      q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 7933 := by
  have hA : ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 63463, 131071} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h607
    · exact h3967
    · exact h7933
    · exact h63463
    · exact h131071
  intro q hq hlt
  by_cases hqA : q ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 63463, 131071} : Finset ℕ)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hqA
    rcases hqA with h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    · omega
    · omega
  · exfalso
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 63463, 131071} : Finset ℕ), (p + 1) =
        4382622131152699919601500160 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 63463, 131071} : Finset ℕ), p =
        2191416935873510837943852135 := by decide
    rw [e1, e2] at h
    omega

-- Boosted prime gap in H3 (63463, 524287 simple): every prime of n < 18507 is in the 10-prime set.
theorem gap_H3 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h7933 : 7933 ∈ P)
    (h63463 : 63463 ∈ P) (h524287 : 524287 ∈ P) :
    ∀ q ∈ P, q < 18507 →
      q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 7933 := by
  have hA : ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 63463, 524287} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h607
    · exact h3967
    · exact h7933
    · exact h63463
    · exact h524287
  intro q hq hlt
  by_cases hqA : q ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 63463, 524287} : Finset ℕ)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hqA
    rcases hqA with h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    · omega
    · omega
  · exfalso
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 63463, 524287} : Finset ℕ), (p + 1) =
        17530488524610799678406000640 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 7933, 63463, 524287} : Finset ℕ), p =
        8765717901429876759108181095 := by decide
    rw [e1, e2] at h
    omega

-- Master classification theorem for H2 (7933 | n, ¬ 8191 | n, thin kernel Y ≤ 5001/5000, a ≥ 48).
theorem thin_7933_split {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h7 : 7 ∣ n) (h19 : 19 ∣ n) (h31 : 31 ∣ n)
    (hl : ∀ q : ℕ, q.Prime → q ∣ n → q < 5057 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967)
    (h223 : 223 ∣ n) (h607 : 607 ∣ n) (h3967 : 3967 ∣ n) (h48 : 48 ≤ padicValNat 2 n)
    (hthin : ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000)
    (hn8191 : ¬ 8191 ∣ n) (h7933 : 7933 ∣ n) :
    (∀ z ∈ S, 25000 ≤ z) ∧
      ((19423 ∣ n ∧
          ∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 49468 →
            q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
              q = 7933 ∨ q = 19423) ∨
        (¬ 19423 ∣ n ∧ 63463 ∣ n ∧ ¬ 63463 ^ 2 ∣ n ∧ (∃ z ∈ S, z % 3 = 1) ∧
          ((131071 ∣ n ∧ ¬ 131071 ^ 2 ∣ n ∧
              ∀ q : ℕ, q.Prime → q ∣ n → q < 20699 →
                q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
                  q = 7933) ∨
            ((131071 ∣ n → 131071 ^ 2 ∣ n) ∧ 524287 ∣ n ∧ ¬ 524287 ^ 2 ∣ n ∧
              1048573 ∣ n ∧ ¬ 1048573 ^ 2 ∣ n ∧
              ∀ q : ℕ, q.Prime → q ∣ n → q < 18507 →
                q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
                  q = 7933)))) := by
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (le_trans (by norm_num) h48)
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z := fun z hz =>
    ⟨((hS z).mp hz).1, hadm1 z hz⟩
  have hNb := adm_ge_2100 hNS hadm2
  have hge := ge_25000 (fun w hw => (hNS w hw).1.ne_zero) hthin
  refine ⟨hge, ?_⟩
  obtain ⟨K, K', P, hP, hK, hKK1, hKr0, E, hmem⟩ := setup7 h hS h2
  have hPN : ∀ p ∈ P, p ∉ S := fun p hp => ((hmem p).mp hp).2.2.2
  have hKr : (K' : ℚ) / K ≤ 1 + 1 / (125000 * 5000) := hKr0.trans (kk_bound_25000 hge hthin)
  obtain ⟨-, -, S2, -, -, -, -, -⟩ := facts hP hK E
  have mem : ∀ q, q.Prime → q ∣ n → q < 25000 → q ≠ 2 → q ∈ P := fun q hq hqn hlt hq2 =>
    (hmem q).mpr ⟨hq, hq2, hqn, fun hx => absurd (hge q hx) (not_le.mpr hlt)⟩
  have m3 := mem 3 (by norm_num) h3 (by norm_num) (by norm_num)
  have m5 := mem 5 (by norm_num) h5 (by norm_num) (by norm_num)
  have m7 := mem 7 (by norm_num) h7 (by norm_num) (by norm_num)
  have m19 := mem 19 (by norm_num) h19 (by norm_num) (by norm_num)
  have m31 := mem 31 (by norm_num) h31 (by norm_num) (by norm_num)
  have m223 := mem 223 (by norm_num) h223 (by norm_num) (by norm_num)
  have m607 := mem 607 (by norm_num) h607 (by norm_num) (by norm_num)
  have m3967 := mem 3967 (by norm_num) h3967 (by norm_num) (by norm_num)
  have m7933 := mem 7933 (by norm_num) h7933 (by norm_num) (by norm_num)
  have T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5 := fun p hp hd =>
    S2 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 5 m5 hd (by norm_num)
  have T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19 := fun p hp hd =>
    S2 5 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 19 m19 hd (by norm_num)
  have hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 := fun q hq hlt => by
    obtain ⟨hqp, hq2, hqn, _⟩ := (hmem q).mp hq
    rcases hl q hqp hqn (lt_trans hlt (by norm_num)) with e | e | e | e | e | e | e | e | e
    · exact absurd e hq2
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
    · exact absurd (e ▸ hlt) (by norm_num)
    · exact absurd (e ▸ hlt) (by norm_num)
    · exact absurd (e ▸ hlt) (by norm_num)
  have n8191 : 8191 ∉ P := fun hx => hn8191 ((hmem 8191).mp hx).2.2.1
  have hD : ∀ U : Finset ℕ,
      (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ S) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        4 / 3 * (75000 / 74996) * (1 / 24999) :=
    fun U hU => sumD_thin25 (fun w hw => ⟨(hNS w hw).1, hge w hw⟩) hthin U hU
  by_cases h19423 : 19423 ∣ n
  · left
    have m19423 := mem 19423 (by norm_num) h19423 (by norm_num) (by norm_num)
    refine ⟨h19423, fun q hqp hqn hnsq hlt => ?_⟩
    by_cases hq2 : q = 2
    · exact Or.inl hq2
    · have hqS : q ∉ S := fun hx => hnsq ((hS q).mp hx).2.2
      have hqP : q ∈ P := (hmem q).mpr ⟨hqp, hq2, hqn, hqS⟩
      exact Or.inr (gap_H1 hP hNS hK hKK1 E m3 m5 m7 m19 m31 m223 m607 m3967 m7933 m19423 q hqP hlt)
  · right
    have n19423 : 19423 ∉ P := fun hx => h19423 ((hmem 19423).mp hx).2.2.1
    have m63463 : 63463 ∈ P := by
      by_contra n63463
      exact node_no19423_no63463 hP hPN hNS hK hKr hKK1 hNb hge hD E h48 T3 T5 hs m3 m5 m7 m19
        m31 m223 m607 m3967 m7933 n8191 n19423 n63463
    have h63463d : 63463 ∣ n := ((hmem 63463).mp m63463).2.2.1
    have h63463nsq : ¬ 63463 ^ 2 ∣ n := fun hsq =>
      ((hmem 63463).mp m63463).2.2.2 ((hS 63463).mpr ⟨((hmem 63463).mp m63463).1, by norm_num, hsq⟩)
    have hex1 : ∃ z ∈ S, z % 3 = 1 := by
      by_contra hno1
      push Not at hno1
      have hDs2 : ∀ U : Finset ℕ,
          (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ S) →
          ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
            2 / 3 * (75000 / 74998) * (1 / 24999) +
              4 / 3 * (75000 / 74996) * (1 / 300000000) :=
        fun U hU => sumD_s2only (fun w hw => ⟨(hNS w hw).1, hge w hw⟩) hno1 hthin U hU
      exact node_no19423_63463_s2only hP hPN hNS hK hKr hKK1 hNb hge hDs2 E h48 T3 T5 hs m3 m5 m7
        m19 m31 m223 m607 m3967 m7933 m63463 n8191 n19423
    refine ⟨h19423, h63463d, h63463nsq, hex1, ?_⟩
    by_cases m131 : 131071 ∈ P
    · left
      have h131d : 131071 ∣ n := ((hmem 131071).mp m131).2.2.1
      have h131nsq : ¬ 131071 ^ 2 ∣ n := fun hsq =>
        ((hmem 131071).mp m131).2.2.2 ((hS 131071).mpr ⟨((hmem 131071).mp m131).1, by norm_num, hsq⟩)
      refine ⟨h131d, h131nsq, fun q hqp hqn hlt => ?_⟩
      by_cases hq2 : q = 2
      · exact Or.inl hq2
      · have hqP : q ∈ P := mem q hqp hqn (lt_trans hlt (by norm_num)) hq2
        exact Or.inr (gap_H2 hP hNS hK hKK1 E m3 m5 m7 m19 m31 m223 m607 m3967 m7933 m63463 m131
          q hqP hlt)
    · right
      have h131imp : 131071 ∣ n → 131071 ^ 2 ∣ n := fun hd => by
        by_contra hnsq
        exact m131 ((hmem 131071).mpr ⟨prime_131071, by norm_num, hd, fun hx =>
          hnsq ((hS 131071).mp hx).2.2⟩)
      have m524 : 524287 ∈ P := by
        by_contra n524
        exact node_no19423_63463_noM hP hPN hNS hK hKr hKK1 hNb hge hD E h48 T3 T5 hs m3 m5 m7
          m19 m31 m223 m607 m3967 m7933 m63463 n8191 n19423 m131 n524
      have m104 : 1048573 ∈ P := by
        by_contra n104
        exact node_no19423_63463_no131_524_no104 hP hPN hNS hK hKr hKK1 hNb hge hD E h48 T3 T5 hs
          m3 m5 m7 m19 m31 m223 m607 m3967 m7933 m63463 n8191 n19423 m131 n104
      have h524d : 524287 ∣ n := ((hmem 524287).mp m524).2.2.1
      have h524nsq : ¬ 524287 ^ 2 ∣ n := fun hsq =>
        ((hmem 524287).mp m524).2.2.2 ((hS 524287).mpr ⟨((hmem 524287).mp m524).1, by norm_num, hsq⟩)
      have h104d : 1048573 ∣ n := ((hmem 1048573).mp m104).2.2.1
      have h104nsq : ¬ 1048573 ^ 2 ∣ n := fun hsq =>
        ((hmem 1048573).mp m104).2.2.2 ((hS 1048573).mpr ⟨((hmem 1048573).mp m104).1, by norm_num, hsq⟩)
      refine ⟨h131imp, h524d, h524nsq, h104d, h104nsq, fun q hqp hqn hlt => ?_⟩
      by_cases hq2 : q = 2
      · exact Or.inl hq2
      · have hqP : q ∈ P := mem q hqp hqn (lt_trans hlt (by norm_num)) hq2
        exact Or.inr (gap_H3 hP hNS hK hKK1 E m3 m5 m7 m19 m31 m223 m607 m3967 m7933 m63463 m524
          q hqP hlt)

end Erdos1052C18

-- Case H1: 19423 | n, with every kernel prime >= 25000 and simple-prime exclusion boosted to 49468.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    ¬ 8191 ∣ n → 7933 ∣ n → 19423 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 49468 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
        q = 7933 ∨ q = 19423) →
    padicValNat 2 n ≤ A

-- Case H2: ¬ 19423 | n, 63463 and 131071 simple, ∃ z ∈ S with z % 3 = 1, prime exclusion 20699.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    ¬ 8191 ∣ n → 7933 ∣ n → ¬ 19423 ∣ n →
    63463 ∣ n → ¬ 63463 ^ 2 ∣ n → 131071 ∣ n → ¬ 131071 ^ 2 ∣ n → (∃ z ∈ S, z % 3 = 1) →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 20699 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 7933) →
    padicValNat 2 n ≤ A

-- Case H3: ¬ 19423 | n, 131071 not simple, 63463, 524287, 1048573 simple, ∃ z ∈ S with z % 3 = 1.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    ¬ 8191 ∣ n → 7933 ∣ n → ¬ 19423 ∣ n →
    63463 ∣ n → ¬ 63463 ^ 2 ∣ n → (131071 ∣ n → 131071 ^ 2 ∣ n) →
    524287 ∣ n → ¬ 524287 ^ 2 ∣ n → 1048573 ∣ n → ¬ 1048573 ^ 2 ∣ n → (∃ z ∈ S, z % 3 = 1) →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 18507 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 7933) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 →
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1.H2 := by
  rintro ⟨A1, hA1⟩ ⟨A2, hA2⟩ ⟨A3, hA3⟩
  refine ⟨max A1 (max A2 A3), fun n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
    h223 h607 h3967 h48 hthin hn8191 h7933 => ?_⟩
  obtain ⟨hge, hcases⟩ := Erdos1052C18.thin_7933_split h hS hadm1 hadm2 h3 h5 h7 h19 h31 hl
    h223 h607 h3967 h48 hthin hn8191 h7933
  rcases hcases with ⟨h19423, hgap1⟩ | ⟨hn19423, h63, h63n, hex1, hbranch⟩
  · exact (hA1 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 h223 h607 h3967 h48
      hthin hge hn8191 h7933 h19423 hgap1).trans (le_max_left _ _)
  · rcases hbranch with ⟨h131, h131n, hgap2⟩ | ⟨h131i, h524, h524n, h104, h104n, hgap3⟩
    · exact (hA2 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 h223 h607 h3967 h48
        hthin hge hn8191 h7933 hn19423 h63 h63n h131 h131n hex1 hgap2).trans
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact (hA3 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 h223 h607 h3967 h48
        hthin hge hn8191 h7933 hn19423 h63 h63n h131i h524 h524n h104 h104n hex1 hgap3).trans
        (le_trans (le_max_right _ _) (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H2_R1
