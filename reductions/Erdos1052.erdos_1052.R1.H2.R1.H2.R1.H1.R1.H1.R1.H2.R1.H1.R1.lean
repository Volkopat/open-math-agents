import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1

/-!
# Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H2.R1.H1.R1

Splits step `H1` of `Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H2.R1` (thin kernel `8191 ∣ n`,
`Y ≤ 5001/5000`, `a ≥ 48`) into three strictly stronger subcases `H1`, `H2`, `H3`.

Using the tightened master inequality `masterU_48` (`a ≥ 48`, `z ≥ 25000`, `K'/K ≤ 1 + 1/(125000*5000)`,
explicit Mersenne weights at `8191, 131071, 524287` with tail from `2^31 - 1`, and the `S1`-empty
leaf bound `sumD_s2only`), we prove unconditionally:
1. Every kernel prime satisfies `z ≥ 25000`, every simple prime outside `{3, 5, 7, 19, 31, 223, 607,
   3967, 8191}` is at least `13215` (in particular `¬ 7933 ∣ n`), and `16381 ∣ n` and `19423 ∣ n`
   are mutually exclusive.
2. When neither `16381` nor `19423` divides `n`, all of the following cases are impossible (`< 2`):
   - `126943 ∉ P` (`node_A`, total `≤ 1.99999909`),
   - `126943 ∈ P, 262111 ∉ P, 9943873 ∉ P` (`node_B_no994`, total `≤ 1.99999994`),
   - `126943 ∈ P, 262111 ∉ P, 9943873 ∈ P` (`node_B_with994`, `β 8191 = 8192/8191`, total `≤ 1.99999628`),
   - `126943, 262111 ∈ P, 131071 ∉ P` (`node_C`, total `≤ 1.99999517`),
   - `126943, 262111, 131071 ∈ P, 524287 ∉ P, 524221 ∉ P` (`node_D1`, total `≤ 1.99999613`),
   - `126943, 262111, 131071 ∈ P, 524287 ∉ P, 524221 ∈ P` (`node_D2`, total `≤ 1.99999994`),
   - `126943, 262111 ∈ P, ∀ z ∈ S, z % 3 ≠ 1` (`node_E`, total `≤ 1.99995805`).

Hence every solution falls into one of:
- `H1`: `16381 ∣ n ∧ ¬ 19423 ∣ n ∧ ¬ 7933 ∣ n` (simple-prime exclusion boosted from `5057` to `68378`),
- `H2`: `¬ 16381 ∣ n ∧ 19423 ∣ n ∧ ¬ 7933 ∣ n` (simple-prime exclusion boosted from `5057` to `41348`),
- `H3`: `¬ 16381 ∣ n ∧ ¬ 19423 ∣ n ∧ ¬ 7933 ∣ n`, all four primes `126943, 262111, 131071, 524287`
  simple, `∃ z ∈ S, z % 3 = 1`, and all-prime exclusion boosted to `18369`.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1

namespace Erdos1052C19

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C7
  OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C9
  OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C11
  OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C16
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1.Erdos1052C17

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

theorem not_prime_of_mul {p a b : ℕ} (ha : a ≠ 1) (hb : b ≠ 1) (h : p = a * b) : ¬ p.Prime := by
  rw [h]
  exact Nat.not_prime_mul ha hb

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
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 87381) (by decide) (by decide) (by omega))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 349525) (by decide) (by decide) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 7) (b := 299593) (by decide) (by decide) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 1398101) (by decide) (by decide) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 47) (b := 178481) (by decide) (by decide) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 5592405) (by decide) (by decide) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 31) (b := 1082401) (by decide) (by decide) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 22369621) (by decide) (by decide) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 7) (b := 19173961) (by decide) (by decide) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 89478485) (by decide) (by decide) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 233) (b := 2304167) (by decide) (by decide) (by omega))
    · exact absurd hq (not_prime_of_mul (a := 3) (b := 357913941) (by decide) (by decide) (by omega))

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

-- Prime parent lower bounds under gap = 13215 (with modular m=1 helpers).

theorem T223_m1 {p e : ℕ} (hp : p.Prime) (he : e < 14) (hp_eq : p = 2 * 223 * 2 ^ e - 1)
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

theorem T223_1769281 {p : ℕ} (hp : p.Prime) (hd : 223 ∣ p + 1) (hsq : ¬ 223 * 223 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 223 ∨ r = 607 ∨ 3967 ≤ r)
    (h1783 : p ≠ 1783) :
    1769281 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 14 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 14 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    exact T223_m1 hp he (by omega) h1783
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 223 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with rfl | rfl | h
    · exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · by_cases hk1 : k = 1
      · subst hk1
        have hj' : p + 1 = 2 * 223 * 607 * 2 ^ e := by rw [hj]; ring
        have hlt2 : 2 ^ e < 2 ^ 3 := by generalize 2 ^ e = t at hj'; norm_num; omega
        have he : e < 3 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
        obtain rfl : p = 2 * 223 * 607 * 2 ^ e - 1 := by omega
        clear hj hj' hd hsq hgap hlt hp2 hmo he0 hlt2 hrp hrk hk
        interval_cases e
        · exact absurd hp (not_prime_of_mul (a := 11) (b := 24611) (by decide) (by decide) (by decide))
        · exact absurd hp (not_prime_of_mul (a := 3) (b := 180481) (by decide) (by decide) (by decide))
        · exact absurd hp (not_prime_of_mul (a := 13) (b := 83299) (by decide) (by decide) (by decide))
      · have hko : Odd k := (Nat.odd_mul.mp hmo).2
        obtain ⟨r', k', hr', hr'2, rfl, hk'⟩ := odd_prime_factor hko hk1
        have hr'p : r' ∣ p + 1 := ⟨2 * 223 * 607 * 2 ^ e * k', by rw [hj]; ring⟩
        have hr'le : r' ≤ 2 ^ e * (r' * k') :=
          le_trans (Nat.le_mul_of_pos_right r' hk') (Nat.le_mul_of_pos_left _ he0)
        have hge607 : 607 ≤ r' := by
          rcases hgap r' hr' hr'2 hr'p with rfl | h' | h'
          · exact absurd ⟨2 * 607 * 2 ^ e * k', by rw [hj]; ring⟩ hsq
          · omega
          · omega
        have hj' : p + 1 = 2 * 223 * 607 * (2 ^ e * (r' * k')) := by rw [hj]; ring
        have hbig : 607 ≤ 2 ^ e * (r' * k') := le_trans hge607 hr'le
        have hmul : 2 * 223 * 607 * 607 ≤ p + 1 := by rw [hj']; exact Nat.mul_le_mul_left _ hbig
        exact hlt (by linarith)
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T223_5893889 {p : ℕ} (hp : p.Prime) (hd : 223 ∣ p + 1) (hsq : ¬ 223 * 223 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 223 ∨ r = 607 ∨ r = 8191 ∨ 13215 ≤ r)
    (h1783 : p ≠ 1783) :
    5893889 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 14 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 14 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    exact T223_m1 hp he (by omega) h1783
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
        have hmul : 2 * 223 * 607 * 607 ≤ p + 1 := by rw [hj']; exact Nat.mul_le_mul_left _ hbig
        exact hlt (by linarith)
    · by_cases hk1 : k = 1
      · subst hk1
        have hj' : p + 1 = 2 * 223 * 8191 * 2 ^ e := by rw [hj]; ring
        have hlt2 : 2 ^ e < 2 ^ 1 := by generalize 2 ^ e = t at hj'; norm_num; omega
        have he : e = 0 := by
          have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2; omega
        subst he
        obtain rfl : p = 3653185 := by norm_num at hj'; omega
        exact absurd hp (not_prime_of_mul (a := 5) (b := 730637) (by decide) (by decide) (by decide))
      · have hko : Odd k := (Nat.odd_mul.mp hmo).2
        have hk3 : 3 ≤ k := by obtain ⟨j, rfl⟩ := hko; omega
        have hj' : p + 1 = 2 * 223 * 8191 * (2 ^ e * k) := by rw [hj]; ring
        have htk : 3 ≤ 2 ^ e * k := le_trans hk3 (Nat.le_mul_of_pos_left k he0)
        have hmul : 2 * 223 * 8191 * 3 ≤ p + 1 := by rw [hj']; exact Nat.mul_le_mul_left _ htk
        exact hlt (by linarith)
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T607_m1 {p e : ℕ} (hp : p.Prime) (he : e < 14) (hp_eq : p = 2 * 607 * 2 ^ e - 1)
    (h1213 : p ≠ 1213) (h19423 : p ≠ 19423) : False := by
  subst hp_eq
  interval_cases e
  · exact h1213 (by decide)
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 809) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 5) (b := 971) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 3237) (by decide) (by decide) (by decide))
  · exact h19423 (by decide)
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 12949) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 5) (b := 15539) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 51797) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 11) (b := 28253) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 207189) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 5) (b := 248627) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 828757) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 29) (b := 171467) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 3315029) (by decide) (by decide) (by decide))

theorem T607_9943873 {p : ℕ} (hp : p.Prime) (hd : 607 ∣ p + 1) (hsq : ¬ 607 * 607 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 607 ∨ r = 3967 ∨ 8191 ≤ r)
    (h1213 : p ≠ 1213) (h19423 : p ≠ 19423) :
    9943873 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 14 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 14 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    exact T607_m1 hp he (by omega) h1213 h19423
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 607 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with rfl | rfl | h
    · exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · by_cases hk1 : k = 1
      · subst hk1
        have hj' : p + 1 = 2 * 607 * 3967 * 2 ^ e := by rw [hj]; ring
        have hlt2 : 2 ^ e < 2 ^ 2 := by generalize 2 ^ e = t at hj'; norm_num; omega
        have he : e < 2 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
        obtain rfl : p = 2 * 607 * 3967 * 2 ^ e - 1 := by omega
        clear hj hj' hd hsq hgap hlt hp2 hmo he0 hlt2 hrp hrk hk
        interval_cases e
        · exact absurd hp (not_prime_of_mul (a := 7) (b := 687991) (by decide) (by decide) (by decide))
        · exact absurd hp (not_prime_of_mul (a := 3) (b := 3210625) (by decide) (by decide) (by decide))
      · have hko : Odd k := (Nat.odd_mul.mp hmo).2
        have hk3 : 3 ≤ k := by obtain ⟨j, rfl⟩ := hko; omega
        have hj' : p + 1 = 2 * 607 * 3967 * (2 ^ e * k) := by rw [hj]; ring
        have htk : 3 ≤ 2 ^ e * k := le_trans hk3 (Nat.le_mul_of_pos_left k he0)
        have hmul : 2 * 607 * 3967 * 3 ≤ p + 1 := by rw [hj']; exact Nat.mul_le_mul_left _ htk
        exact hlt (by linarith)
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T607_16043009 {p : ℕ} (hp : p.Prime) (hd : 607 ∣ p + 1) (hsq : ¬ 607 * 607 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 607 ∨ r = 8191 ∨ 13215 ≤ r)
    (h1213 : p ≠ 1213) (h19423 : p ≠ 19423) (h994 : p ≠ 9943873) :
    16043009 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 14 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 14 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    exact T607_m1 hp he (by omega) h1213 h19423
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 607 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with rfl | rfl | h
    · exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · by_cases hk1 : k = 1
      · subst hk1
        have hj' : p + 1 = 2 * 607 * 8191 * 2 ^ e := by rw [hj]; ring
        have hlt2 : 2 ^ e < 2 ^ 1 := by generalize 2 ^ e = t at hj'; norm_num; omega
        have he : e = 0 := by
          have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2; omega
        subst he
        exact h994 (by norm_num at hj'; omega)
      · have hko : Odd k := (Nat.odd_mul.mp hmo).2
        have hk3 : 3 ≤ k := by obtain ⟨j, rfl⟩ := hko; omega
        have hj' : p + 1 = 2 * 607 * 8191 * (2 ^ e * k) := by rw [hj]; ring
        have htk : 3 ≤ 2 ^ e * k := le_trans hk3 (Nat.le_mul_of_pos_left k he0)
        have hmul : 2 * 607 * 8191 * 3 ≤ p + 1 := by rw [hj']; exact Nat.mul_le_mul_left _ htk
        exact hlt (by linarith)
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T3967_2031103 {p : ℕ} (hp : p.Prime) (hd : 3967 ∣ p + 1) (hsq : ¬ 3967 * 3967 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 3967 ∨ 8191 ≤ r)
    (h7933 : p ≠ 7933) (h126 : p ≠ 126943) :
    2031103 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 8 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 8 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 3967 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e
    · exact h7933 (by decide)
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 5289) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 6347) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 21157) (by decide) (by decide) (by decide))
    · exact h126 (by decide)
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 84629) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 101555) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 338517) (by decide) (by decide) (by decide))
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 3967 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with rfl | h
    · exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T8191_262111 {p : ℕ} (hp : p.Prime) (hd : 8191 ∣ p + 1) (hsq : ¬ 8191 * 8191 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 8191 ∨ 13215 ≤ r)
    (h16 : p ≠ 16381) :
    262111 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 4 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 4 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 8191 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e
    · exact h16 (by decide)
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 10921) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 7) (b := 9361) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 43685) (by decide) (by decide) (by decide))
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 8191 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with rfl | h
    · exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T8191_1048447 {p : ℕ} (hp : p.Prime) (hd : 8191 ∣ p + 1) (hsq : ¬ 8191 * 8191 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 8191 ∨ 13215 ≤ r)
    (h16 : p ≠ 16381) (h262 : p ≠ 262111) :
    1048447 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 6 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 6 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 8191 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e
    · exact h16 (by decide)
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 10921) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 7) (b := 9361) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 43685) (by decide) (by decide) (by decide))
    · exact h262 (by decide)
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 174741) (by decide) (by decide) (by decide))
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 8191 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with rfl | h
    · exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T126943_13215 {p : ℕ} (hp : p.Prime) (hd : 126943 ∣ p + 1) (hsq : ¬ 126943 * 126943 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 126943 ∨ 13215 ≤ r) :
    16248703 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 6 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 6 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 126943 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 50777) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 169257) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 211) (b := 4813) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 677029) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 5) (b := 812435) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 2708117) (by decide) (by decide) (by decide))
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 126943 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with rfl | h
    · exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T131071_13215 {p : ℕ} (hp : p.Prime) (hd : 131071 ∣ p + 1) (hsq : ¬ 131071 * 131071 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 131071 ∨ 13215 ≤ r) :
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
    · exact absurd hp (not_prime_of_mul (a := 11) (b := 23831) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 174761) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 13) (b := 80659) (by decide) (by decide) (by decide))
    · exact absurd hp (not_prime_of_mul (a := 3) (b := 699045) (by decide) (by decide) (by decide))
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 131071 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with rfl | h
    · exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T262111_m1 {p e : ℕ} (hp : p.Prime) (he : e < 14) (hp_eq : p = 2 * 262111 * 2 ^ e - 1)
    (h524 : p ≠ 524221) : False := by
  subst hp_eq
  interval_cases e
  · exact h524 (by decide)
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 349481) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 13) (b := 161299) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 1397925) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 137) (b := 61223) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 5591701) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 761) (b := 44087) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 22366805) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 41) (b := 3273191) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 89467221) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 5197) (b := 103291) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 357868885) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 71) (b := 30242441) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 1431475541) (by decide) (by decide) (by decide))

theorem T262111_no524 {p : ℕ} (hp : p.Prime) (hd : 262111 ∣ p + 1) (hsq : ¬ 262111 * 262111 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 262111 ∨ 13215 ≤ r)
    (h524 : p ≠ 524221) :
    6927593729 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 14 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 14 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    exact T262111_m1 hp he (by omega) h524
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 262111 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with rfl | h
    · exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

theorem T524221_m1 {p e : ℕ} (hp : p.Prime) (he : e < 14) (hp_eq : p = 2 * 524221 * 2 ^ e - 1) :
    False := by
  subst hp_eq
  interval_cases e
  · exact absurd hp (not_prime_of_mul (a := 17) (b := 61673) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 698961) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 41) (b := 102287) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 2795845) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 1447) (b := 11593) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 11183381) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 29) (b := 2313803) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 44733525) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 17) (b := 15788303) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 178934101) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 43) (b := 24967549) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 715736405) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 37) (b := 116065363) (by decide) (by decide) (by decide))
  · exact absurd hp (not_prime_of_mul (a := 3) (b := 2862945621) (by decide) (by decide) (by decide))

theorem T524221_13215 {p : ℕ} (hp : p.Prime) (hd : 524221 ∣ p + 1) (hsq : ¬ 524221 * 524221 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 524221 ∨ 13215 ≤ r) :
    13855161029 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1; rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 14 := by generalize 2 ^ e = t at hj; norm_num; omega
    have he : e < 14 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    exact T524221_m1 hp he (by omega)
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 524221 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with rfl | h
    · exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk; omega

-- Shared 9-prime simple gap for 8191 ∈ P: every other simple prime is at least 13215.
theorem gap9_8191 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P) :
    ∀ q ∈ P, q ≠ 3 → q ≠ 5 → q ≠ 7 → q ≠ 19 → q ≠ 31 → q ≠ 223 → q ≠ 607 → q ≠ 3967 →
      q ≠ 8191 → 13215 ≤ q := by
  have hA : ({3, 5, 7, 19, 31, 223, 607, 3967, 8191} : Finset ℕ) ⊆ P := by
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
    · exact h8191
  intro q hq e3 e5 e7 e19 e31 e223 e607 e3967 e8191
  have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
  rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
  have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191} : Finset ℕ), (p + 1) =
      543994372958453760 := by decide
  have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191} : Finset ℕ), p =
      272017769021713365 := by decide
  rw [e1, e2] at h
  omega

-- Mutual exclusion of 16381 and 19423 when 8191 ∈ P.
theorem excl_16381_19423 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P)
    (h16 : 16381 ∈ P) (h19 : 19423 ∈ P) : False := by
  have hA : ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 16381, 19423} : Finset ℕ) ⊆ P := by
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
    · exact h8191
    · exact h16
    · exact h19
  have h := S_abund hP (K_pos hN hK) hKK1 E hA
  have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 16381, 19423} : Finset ℕ), (p + 1) =
      173101168045051885576519680 := by decide
  have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 16381, 19423} : Finset ℕ), p =
      86547393872996848454598495 := by decide
  rw [e1, e2] at h
  omega

-- Case A: 16381 ∉ P, 19423 ∉ P, 126943 ∉ P (kills all (262111, 131071, 524287) cases at once).
theorem node_A {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
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
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P)
    (h16 : 16381 ∉ P) (h19423 : 19423 ∉ P) (h126 : 126943 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h8191N : 8191 ∉ N := fun h => by have := hN25 8191 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have gap := gap9_8191 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h8191
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 8191 ∨ 13215 ≤ r)) := by
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
      by_cases e8191 : r = 8191; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e8191))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e8191)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (9943874 / 9943872)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (9943874 / 9943872))) else
      if p = 19 then 20 / 19 * (608 / 607 * (9943874 / 9943872)) else
      if p = 607 then 608 / 607 * (9943874 / 9943872) else
      if p = 7 then 8 / 7 * (224 / 223 * (1769282 / 1769280)) else
      if p = 223 then 224 / 223 * (1769282 / 1769280) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (2031104 / 2031102)) else
      if p = 3967 then 3968 / 3967 * (2031104 / 2031102) else
      if p = 127 then 1 else
      if p = 8191 then 8192 / 8191 * (262112 / 262110) else
      if p = 131071 then 131072 / 131071 * (4194272 / 4194270) else
      if p = 524287 then 524288 / 524287 * (1048574 / 1048572) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (9943874 / 9943872)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (9943874 / 9943872))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (9943874 / 9943872)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (9943874 / 9943872) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (1769282 / 1769280)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (1769282 / 1769280) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (2031104 / 2031102)) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (2031104 / 2031102) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (262112 / 262110) := by rw [hβ]; norm_num
  have b131071 : β 131071 = 131072 / 131071 * (4194272 / 4194270) := by rw [hβ]; norm_num
  have b524287 : β 524287 = 524288 / 524287 * (1048574 / 1048572) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 127 → c ≠ 8191 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e127 e8191 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e127, if_neg e8191, if_neg e131, if_neg e524]
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
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; rw [b8191]; norm_num
    by_cases e131 : p = 131071; · subst e131; rw [b131071]; norm_num
    by_cases e524 : p = 524287; · subst e524; rw [b524287]; norm_num
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e127 e8191 e131 e524]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU_48 hP hN hK hKr hNb (4 / 3 * (75000 / 74996) * (1 / 24999)) (by norm_num) hD E
    hm T3 β hB ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3; · subst e3; obtain rfl : p = 5 := T3 p hp hd; rw [b3, b5]; norm_num
    by_cases e5 : c = 5; · subst e5; obtain rfl : p = 19 := T5 p hp hd; rw [b5, b19]; norm_num
    by_cases e19 : c = 19; · subst e19; obtain rfl : p = 607 := T19 p hp hd; rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 9943873 ≤ p := T607_9943873 (hP p hp).1 hd
        (S4b 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
        (fun h => by
          have := gap 1213 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
        (fun h => h19423 (h ▸ hp))
      rw [b607]
      exact step_ge (t := 9943873) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 1769281 ≤ p := T223_1769281 (hP p hp).1 hd
        (S4b 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
        (fun h => by
          have := gap 1783 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
      rw [b223]
      exact step_ge (t := 1769281) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967
    · subst e3967
      have hge : 2031103 ≤ p := T3967_2031103 (hP p hp).1 hd
        (S4b 3967 (by norm_num) (by norm_num) h3967N p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
        (fun h => by
          have := gap 7933 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
        (fun h => h126 (h ▸ hp))
      rw [b3967]
      exact step_ge (t := 2031103) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191
    · subst e8191
      have hge : 262111 ≤ p := T8191_262111 (hP p hp).1 hd
        (S4b 8191 (by norm_num) (by norm_num) h8191N p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
        (fun h => h16 (h ▸ hp))
      rw [b8191]
      exact step_ge (t := 262111) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e131 : c = 131071
    · subst e131
      have hge : 4194271 ≤ p := T131071_13215 (hP p hp).1 hd
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
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e127 e8191 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b131071]; norm_num
  · rw [b524287]; norm_num
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num

-- Case B1: 16381 ∉ P, 19423 ∉ P, 126943 ∈ P, 262111 ∉ P, 9943873 ∉ P.
theorem node_B_no994 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
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
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P)
    (h126 : 126943 ∈ P) (h16 : 16381 ∉ P) (h19423 : 19423 ∉ P)
    (h262 : 262111 ∉ P) (h994 : 9943873 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h8191N : 8191 ∉ N := fun h => by have := hN25 8191 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have T3967 : ∀ p ∈ P, 3967 ∣ p + 1 → p = 126943 := fun p hp hd =>
    S2 3967 (by norm_num) (by norm_num) h3967N p hp 126943 h126 hd (by decide)
  have gap := gap9_8191 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h8191
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 8191 ∨ 13215 ≤ r)) := by
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
      by_cases e8191 : r = 8191; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e8191))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e8191)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) else
      if p = 19 then 20 / 19 * (608 / 607 * (16043010 / 16043008)) else
      if p = 607 then 608 / 607 * (16043010 / 16043008) else
      if p = 7 then 8 / 7 * (224 / 223 * (5893890 / 5893888)) else
      if p = 223 then 224 / 223 * (5893890 / 5893888) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) else
      if p = 3967 then 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) else
      if p = 126943 then 126944 / 126943 * (16248704 / 16248702) else
      if p = 127 then 1 else
      if p = 8191 then 8192 / 8191 * (1048448 / 1048446) else
      if p = 131071 then 131072 / 131071 * (4194272 / 4194270) else
      if p = 524287 then 524288 / 524287 * (1048574 / 1048572) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (16043010 / 16043008)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (16043010 / 16043008) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (5893890 / 5893888)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (5893890 / 5893888) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) := by rw [hβ]; norm_num
  have b126 : β 126943 = 126944 / 126943 * (16248704 / 16248702) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (1048448 / 1048446) := by rw [hβ]; norm_num
  have b131071 : β 131071 = 131072 / 131071 * (4194272 / 4194270) := by rw [hβ]; norm_num
  have b524287 : β 524287 = 524288 / 524287 * (1048574 / 1048572) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 126943 → c ≠ 127 → c ≠ 8191 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e126, if_neg e127, if_neg e8191, if_neg e131, if_neg e524]
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
    by_cases e126 : p = 126943; · subst e126; rw [b126]; norm_num
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; rw [b8191]; norm_num
    by_cases e131 : p = 131071; · subst e131; rw [b131071]; norm_num
    by_cases e524 : p = 524287; · subst e524; rw [b524287]; norm_num
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e131 e524]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU_48 hP hN hK hKr hNb (4 / 3 * (75000 / 74996) * (1 / 24999)) (by norm_num) hD E
    hm T3 β hB ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3; · subst e3; obtain rfl : p = 5 := T3 p hp hd; rw [b3, b5]; norm_num
    by_cases e5 : c = 5; · subst e5; obtain rfl : p = 19 := T5 p hp hd; rw [b5, b19]; norm_num
    by_cases e19 : c = 19; · subst e19; obtain rfl : p = 607 := T19 p hp hd; rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 16043009 ≤ p := T607_16043009 (hP p hp).1 hd
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
        (fun h => h994 (h ▸ hp))
      rw [b607]
      exact step_ge (t := 16043009) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 5893889 ≤ p := T223_5893889 (hP p hp).1 hd
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
      exact step_ge (t := 5893889) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967; · subst e3967; obtain rfl : p = 126943 := T3967 p hp hd; rw [b3967, b126]; norm_num
    by_cases e126 : c = 126943
    · subst e126
      have hge : 16248703 ≤ p := T126943_13215 (hP p hp).1 hd
        (S4b 126943 (hP 126943 hc).1 (by norm_num) (hPN 126943 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b126]
      exact step_ge (t := 16248703) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191
    · subst e8191
      have hge : 1048447 ≤ p := T8191_1048447 (hP p hp).1 hd
        (S4b 8191 (by norm_num) (by norm_num) h8191N p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
        (fun h => h16 (h ▸ hp))
        (fun h => h262 (h ▸ hp))
      rw [b8191]
      exact step_ge (t := 1048447) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e131 : c = 131071
    · subst e131
      have hge : 4194271 ≤ p := T131071_13215 (hP p hp).1 hd
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
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b131071]; norm_num
  · rw [b524287]; norm_num
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num

-- Case B2: 16381 ∉ P, 19423 ∉ P, 126943 ∈ P, 262111 ∉ P, 9943873 ∈ P.
-- Because 9943873 ∈ P and 607 | 9943874, 8191 has NO parent in P with 8191 as minimal odd factor,
-- so β 8191 = 8192 / 8191 is valid and closes the inequality cleanly.
theorem node_B_with994 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
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
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P)
    (h126 : 126943 ∈ P) (h994 : 9943873 ∈ P) (h19423 : 19423 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h8191N : 8191 ∉ N := fun h => by have := hN25 8191 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have T3967 : ∀ p ∈ P, 3967 ∣ p + 1 → p = 126943 := fun p hp hd =>
    S2 3967 (by norm_num) (by norm_num) h3967N p hp 126943 h126 hd (by decide)
  have T8191_994 : ∀ p ∈ P, 8191 ∣ p + 1 → p = 9943873 := fun p hp hd =>
    S2 8191 (by norm_num) (by norm_num) h8191N p hp 9943873 h994 hd (by decide)
  have gap := gap9_8191 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h8191
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 8191 ∨ 13215 ≤ r)) := by
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
      by_cases e8191 : r = 8191; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e8191))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e8191)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (9943874 / 9943872)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (9943874 / 9943872))) else
      if p = 19 then 20 / 19 * (608 / 607 * (9943874 / 9943872)) else
      if p = 607 then 608 / 607 * (9943874 / 9943872) else
      if p = 7 then 8 / 7 * (224 / 223 * (5893890 / 5893888)) else
      if p = 223 then 224 / 223 * (5893890 / 5893888) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) else
      if p = 3967 then 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) else
      if p = 126943 then 126944 / 126943 * (16248704 / 16248702) else
      if p = 127 then 1 else
      if p = 8191 then 8192 / 8191 else
      if p = 131071 then 131072 / 131071 * (4194272 / 4194270) else
      if p = 524287 then 524288 / 524287 * (1048574 / 1048572) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (9943874 / 9943872)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (9943874 / 9943872))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (9943874 / 9943872)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (9943874 / 9943872) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (5893890 / 5893888)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (5893890 / 5893888) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) := by rw [hβ]; norm_num
  have b126 : β 126943 = 126944 / 126943 * (16248704 / 16248702) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 := by rw [hβ]; norm_num
  have b131071 : β 131071 = 131072 / 131071 * (4194272 / 4194270) := by rw [hβ]; norm_num
  have b524287 : β 524287 = 524288 / 524287 * (1048574 / 1048572) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 126943 → c ≠ 127 → c ≠ 8191 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e126, if_neg e127, if_neg e8191, if_neg e131, if_neg e524]
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
    by_cases e126 : p = 126943; · subst e126; rw [b126]; norm_num
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; rw [b8191]; norm_num
    by_cases e131 : p = 131071; · subst e131; rw [b131071]; norm_num
    by_cases e524 : p = 524287; · subst e524; rw [b524287]; norm_num
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e131 e524]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU_48 hP hN hK hKr hNb (4 / 3 * (75000 / 74996) * (1 / 24999)) (by norm_num) hD E
    hm T3 β hB ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3; · subst e3; obtain rfl : p = 5 := T3 p hp hd; rw [b3, b5]; norm_num
    by_cases e5 : c = 5; · subst e5; obtain rfl : p = 19 := T5 p hp hd; rw [b5, b19]; norm_num
    by_cases e19 : c = 19; · subst e19; obtain rfl : p = 607 := T19 p hp hd; rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 9943873 ≤ p := T607_9943873 (hP p hp).1 hd
        (S4b 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
        (fun h => by
          have := gap 1213 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
        (fun h => h19423 (h ▸ hp))
      rw [b607]
      exact step_ge (t := 9943873) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 5893889 ≤ p := T223_5893889 (hP p hp).1 hd
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
      exact step_ge (t := 5893889) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967; · subst e3967; obtain rfl : p = 126943 := T3967 p hp hd; rw [b3967, b126]; norm_num
    by_cases e126 : c = 126943
    · subst e126
      have hge : 16248703 ≤ p := T126943_13215 (hP p hp).1 hd
        (S4b 126943 (hP 126943 hc).1 (by norm_num) (hPN 126943 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b126]
      exact step_ge (t := 16248703) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191
    · subst e8191
      obtain rfl : p = 9943873 := T8191_994 p hp hd
      have h607le := hmin 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) (by decide)
      omega
    by_cases e131 : c = 131071
    · subst e131
      have hge : 4194271 ≤ p := T131071_13215 (hP p hp).1 hd
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
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b131071]; norm_num
  · rw [b524287]; norm_num
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num

-- Case C: 16381 ∉ P, 19423 ∉ P, 126943 ∈ P, 262111 ∈ P, 131071 ∉ P.
theorem node_C {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
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
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P)
    (h126 : 126943 ∈ P) (h262 : 262111 ∈ P) (h19423 : 19423 ∉ P) (h131 : 131071 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h8191N : 8191 ∉ N := fun h => by have := hN25 8191 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have T3967 : ∀ p ∈ P, 3967 ∣ p + 1 → p = 126943 := fun p hp hd =>
    S2 3967 (by norm_num) (by norm_num) h3967N p hp 126943 h126 hd (by decide)
  have T8191 : ∀ p ∈ P, 8191 ∣ p + 1 → p = 262111 := fun p hp hd =>
    S2 8191 (by norm_num) (by norm_num) h8191N p hp 262111 h262 hd (by decide)
  have gap := gap9_8191 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h8191
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 8191 ∨ 13215 ≤ r)) := by
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
      by_cases e8191 : r = 8191; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e8191))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e8191)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) else
      if p = 19 then 20 / 19 * (608 / 607 * (16043010 / 16043008)) else
      if p = 607 then 608 / 607 * (16043010 / 16043008) else
      if p = 7 then 8 / 7 * (224 / 223 * (5893890 / 5893888)) else
      if p = 223 then 224 / 223 * (5893890 / 5893888) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) else
      if p = 3967 then 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) else
      if p = 126943 then 126944 / 126943 * (16248704 / 16248702) else
      if p = 127 then 1 else
      if p = 8191 then 8192 / 8191 * (262112 / 262111 * (524222 / 524220)) else
      if p = 262111 then 262112 / 262111 * (524222 / 524220) else
      if p = 131071 then 1 else
      if p = 524287 then 524288 / 524287 * (1048574 / 1048572) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (16043010 / 16043008)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (16043010 / 16043008) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (5893890 / 5893888)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (5893890 / 5893888) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) := by rw [hβ]; norm_num
  have b126 : β 126943 = 126944 / 126943 * (16248704 / 16248702) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (262112 / 262111 * (524222 / 524220)) := by rw [hβ]; norm_num
  have b262 : β 262111 = 262112 / 262111 * (524222 / 524220) := by rw [hβ]; norm_num
  have b131071 : β 131071 = 1 := by rw [hβ]; norm_num
  have b524287 : β 524287 = 524288 / 524287 * (1048574 / 1048572) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 126943 → c ≠ 127 → c ≠ 8191 → c ≠ 262111 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e126, if_neg e127, if_neg e8191, if_neg e262, if_neg e131,
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
    by_cases e126 : p = 126943; · subst e126; rw [b126]; norm_num
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; rw [b8191]; norm_num
    by_cases e262 : p = 262111; · subst e262; rw [b262]; norm_num
    by_cases e131 : p = 131071; · subst e131; exact absurd hp h131
    by_cases e524 : p = 524287; · subst e524; rw [b524287]; norm_num
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU_48 hP hN hK hKr hNb (4 / 3 * (75000 / 74996) * (1 / 24999)) (by norm_num) hD E
    hm T3 β hB ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3; · subst e3; obtain rfl : p = 5 := T3 p hp hd; rw [b3, b5]; norm_num
    by_cases e5 : c = 5; · subst e5; obtain rfl : p = 19 := T5 p hp hd; rw [b5, b19]; norm_num
    by_cases e19 : c = 19; · subst e19; obtain rfl : p = 607 := T19 p hp hd; rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 16043009 ≤ p := T607_16043009 (hP p hp).1 hd
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
        (fun h => by
          have := T8191 9943873 (h ▸ hp) (by decide)
          omega)
      rw [b607]
      exact step_ge (t := 16043009) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 5893889 ≤ p := T223_5893889 (hP p hp).1 hd
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
      exact step_ge (t := 5893889) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967; · subst e3967; obtain rfl : p = 126943 := T3967 p hp hd; rw [b3967, b126]; norm_num
    by_cases e126 : c = 126943
    · subst e126
      have hge : 16248703 ≤ p := T126943_13215 (hP p hp).1 hd
        (S4b 126943 (hP 126943 hc).1 (by norm_num) (hPN 126943 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b126]
      exact step_ge (t := 16248703) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191; · subst e8191; obtain rfl : p = 262111 := T8191 p hp hd; rw [b8191, b262]; norm_num
    by_cases e262 : c = 262111
    · subst e262
      have hge : 524221 ≤ p := by
        have := two_mul_le (hP 262111 hc).1 (by norm_num) (hP p hp).1 (hP p hp).2 hd
        omega
      rw [b262]
      exact step_ge (t := 524221) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e131 : c = 131071; · subst e131; exact absurd hc h131
    by_cases e524 : c = 524287
    · subst e524
      have hge : 1048573 ≤ p := by
        have := two_mul_le (hP 524287 hc).1 (by norm_num) (hP p hp).1 (hP p hp).2 hd
        omega
      rw [b524287]
      exact step_ge (t := 1048573) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b131071]
  · rw [b524287]; norm_num
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num

-- Case D1: 16381 ∉ P, 19423 ∉ P, 126943 ∈ P, 262111 ∈ P, 131071 ∈ P, 524287 ∉ P, 524221 ∉ P.
theorem node_D1 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
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
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P)
    (h126 : 126943 ∈ P) (h262 : 262111 ∈ P) (h19423 : 19423 ∉ P)
    (h524 : 524287 ∉ P) (h524221 : 524221 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h8191N : 8191 ∉ N := fun h => by have := hN25 8191 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have T3967 : ∀ p ∈ P, 3967 ∣ p + 1 → p = 126943 := fun p hp hd =>
    S2 3967 (by norm_num) (by norm_num) h3967N p hp 126943 h126 hd (by decide)
  have T8191 : ∀ p ∈ P, 8191 ∣ p + 1 → p = 262111 := fun p hp hd =>
    S2 8191 (by norm_num) (by norm_num) h8191N p hp 262111 h262 hd (by decide)
  have gap := gap9_8191 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h8191
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 8191 ∨ 13215 ≤ r)) := by
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
      by_cases e8191 : r = 8191; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e8191))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e8191)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) else
      if p = 19 then 20 / 19 * (608 / 607 * (16043010 / 16043008)) else
      if p = 607 then 608 / 607 * (16043010 / 16043008) else
      if p = 7 then 8 / 7 * (224 / 223 * (5893890 / 5893888)) else
      if p = 223 then 224 / 223 * (5893890 / 5893888) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) else
      if p = 3967 then 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) else
      if p = 126943 then 126944 / 126943 * (16248704 / 16248702) else
      if p = 127 then 1 else
      if p = 8191 then 8192 / 8191 * (262112 / 262111 * (6927593730 / 6927593728)) else
      if p = 262111 then 262112 / 262111 * (6927593730 / 6927593728) else
      if p = 131071 then 131072 / 131071 * (4194272 / 4194270) else
      if p = 524287 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (16043010 / 16043008)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (16043010 / 16043008) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (5893890 / 5893888)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (5893890 / 5893888) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) := by rw [hβ]; norm_num
  have b126 : β 126943 = 126944 / 126943 * (16248704 / 16248702) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (262112 / 262111 * (6927593730 / 6927593728)) := by rw [hβ]; norm_num
  have b262 : β 262111 = 262112 / 262111 * (6927593730 / 6927593728) := by rw [hβ]; norm_num
  have b131071 : β 131071 = 131072 / 131071 * (4194272 / 4194270) := by rw [hβ]; norm_num
  have b524287 : β 524287 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 126943 → c ≠ 127 → c ≠ 8191 → c ≠ 262111 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e126, if_neg e127, if_neg e8191, if_neg e262, if_neg e131,
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
    by_cases e126 : p = 126943; · subst e126; rw [b126]; norm_num
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; rw [b8191]; norm_num
    by_cases e262 : p = 262111; · subst e262; rw [b262]; norm_num
    by_cases e131 : p = 131071; · subst e131; rw [b131071]; norm_num
    by_cases e524 : p = 524287; · subst e524; exact absurd hp h524
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU_48 hP hN hK hKr hNb (4 / 3 * (75000 / 74996) * (1 / 24999)) (by norm_num) hD E
    hm T3 β hB ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3; · subst e3; obtain rfl : p = 5 := T3 p hp hd; rw [b3, b5]; norm_num
    by_cases e5 : c = 5; · subst e5; obtain rfl : p = 19 := T5 p hp hd; rw [b5, b19]; norm_num
    by_cases e19 : c = 19; · subst e19; obtain rfl : p = 607 := T19 p hp hd; rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 16043009 ≤ p := T607_16043009 (hP p hp).1 hd
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
        (fun h => by
          have := T8191 9943873 (h ▸ hp) (by decide)
          omega)
      rw [b607]
      exact step_ge (t := 16043009) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 5893889 ≤ p := T223_5893889 (hP p hp).1 hd
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
      exact step_ge (t := 5893889) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967; · subst e3967; obtain rfl : p = 126943 := T3967 p hp hd; rw [b3967, b126]; norm_num
    by_cases e126 : c = 126943
    · subst e126
      have hge : 16248703 ≤ p := T126943_13215 (hP p hp).1 hd
        (S4b 126943 (hP 126943 hc).1 (by norm_num) (hPN 126943 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b126]
      exact step_ge (t := 16248703) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191; · subst e8191; obtain rfl : p = 262111 := T8191 p hp hd; rw [b8191, b262]; norm_num
    by_cases e262 : c = 262111
    · subst e262
      have hge : 6927593729 ≤ p := T262111_no524 (hP p hp).1 hd
        (S4b 262111 (hP 262111 hc).1 (by norm_num) (hPN 262111 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
        (fun h => h524221 (h ▸ hp))
      rw [b262]
      exact step_ge (t := 6927593729) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e131 : c = 131071
    · subst e131
      have hge : 4194271 ≤ p := T131071_13215 (hP p hp).1 hd
        (S4b 131071 (hP 131071 hc).1 (by norm_num) (hPN 131071 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b131071]
      exact step_ge (t := 4194271) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e524 : c = 524287; · subst e524; exact absurd hc h524
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b131071]; norm_num
  · rw [b524287]
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num

-- Case D2: 16381 ∉ P, 19423 ∉ P, 126943 ∈ P, 262111 ∈ P, 131071 ∈ P, 524287 ∉ P, 524221 ∈ P.
theorem node_D2 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
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
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P)
    (h126 : 126943 ∈ P) (h262 : 262111 ∈ P) (h524221 : 524221 ∈ P)
    (h19423 : 19423 ∉ P) (h524 : 524287 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h8191N : 8191 ∉ N := fun h => by have := hN25 8191 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have T3967 : ∀ p ∈ P, 3967 ∣ p + 1 → p = 126943 := fun p hp hd =>
    S2 3967 (by norm_num) (by norm_num) h3967N p hp 126943 h126 hd (by decide)
  have T8191 : ∀ p ∈ P, 8191 ∣ p + 1 → p = 262111 := fun p hp hd =>
    S2 8191 (by norm_num) (by norm_num) h8191N p hp 262111 h262 hd (by decide)
  have T262 : ∀ p ∈ P, 262111 ∣ p + 1 → p = 524221 := fun p hp hd =>
    S2 262111 (hP 262111 h262).1 (by norm_num) (hPN 262111 h262) p hp 524221 h524221 hd (by decide)
  have gap := gap9_8191 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h8191
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 8191 ∨ 13215 ≤ r)) := by
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
      by_cases e8191 : r = 8191; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e8191))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e8191)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) else
      if p = 19 then 20 / 19 * (608 / 607 * (16043010 / 16043008)) else
      if p = 607 then 608 / 607 * (16043010 / 16043008) else
      if p = 7 then 8 / 7 * (224 / 223 * (5893890 / 5893888)) else
      if p = 223 then 224 / 223 * (5893890 / 5893888) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) else
      if p = 3967 then 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) else
      if p = 126943 then 126944 / 126943 * (16248704 / 16248702) else
      if p = 127 then 1 else
      if p = 8191 then 8192 / 8191 * (262112 / 262111 * (524222 / 524221 * (13855161030 / 13855161028))) else
      if p = 262111 then 262112 / 262111 * (524222 / 524221 * (13855161030 / 13855161028)) else
      if p = 524221 then 524222 / 524221 * (13855161030 / 13855161028) else
      if p = 131071 then 131072 / 131071 * (4194272 / 4194270) else
      if p = 524287 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (16043010 / 16043008)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (16043010 / 16043008) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (5893890 / 5893888)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (5893890 / 5893888) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) := by rw [hβ]; norm_num
  have b126 : β 126943 = 126944 / 126943 * (16248704 / 16248702) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (262112 / 262111 * (524222 / 524221 * (13855161030 / 13855161028))) := by rw [hβ]; norm_num
  have b262 : β 262111 = 262112 / 262111 * (524222 / 524221 * (13855161030 / 13855161028)) := by rw [hβ]; norm_num
  have b524221 : β 524221 = 524222 / 524221 * (13855161030 / 13855161028) := by rw [hβ]; norm_num
  have b131071 : β 131071 = 131072 / 131071 * (4194272 / 4194270) := by rw [hβ]; norm_num
  have b524287 : β 524287 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 126943 → c ≠ 127 → c ≠ 8191 → c ≠ 262111 → c ≠ 524221 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e524221 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e126, if_neg e127, if_neg e8191, if_neg e262, if_neg e524221,
        if_neg e131, if_neg e524]
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
    by_cases e126 : p = 126943; · subst e126; rw [b126]; norm_num
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; rw [b8191]; norm_num
    by_cases e262 : p = 262111; · subst e262; rw [b262]; norm_num
    by_cases e524221 : p = 524221; · subst e524221; rw [b524221]; norm_num
    by_cases e131 : p = 131071; · subst e131; rw [b131071]; norm_num
    by_cases e524 : p = 524287; · subst e524; exact absurd hp h524
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e524221 e131 e524]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU_48 hP hN hK hKr hNb (4 / 3 * (75000 / 74996) * (1 / 24999)) (by norm_num) hD E
    hm T3 β hB ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3; · subst e3; obtain rfl : p = 5 := T3 p hp hd; rw [b3, b5]; norm_num
    by_cases e5 : c = 5; · subst e5; obtain rfl : p = 19 := T5 p hp hd; rw [b5, b19]; norm_num
    by_cases e19 : c = 19; · subst e19; obtain rfl : p = 607 := T19 p hp hd; rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 16043009 ≤ p := T607_16043009 (hP p hp).1 hd
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
        (fun h => by
          have := T8191 9943873 (h ▸ hp) (by decide)
          omega)
      rw [b607]
      exact step_ge (t := 16043009) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 5893889 ≤ p := T223_5893889 (hP p hp).1 hd
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
      exact step_ge (t := 5893889) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967; · subst e3967; obtain rfl : p = 126943 := T3967 p hp hd; rw [b3967, b126]; norm_num
    by_cases e126 : c = 126943
    · subst e126
      have hge : 16248703 ≤ p := T126943_13215 (hP p hp).1 hd
        (S4b 126943 (hP 126943 hc).1 (by norm_num) (hPN 126943 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b126]
      exact step_ge (t := 16248703) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191; · subst e8191; obtain rfl : p = 262111 := T8191 p hp hd; rw [b8191, b262]; norm_num
    by_cases e262 : c = 262111; · subst e262; obtain rfl : p = 524221 := T262 p hp hd; rw [b262, b524221]; norm_num
    by_cases e524221 : c = 524221
    · subst e524221
      have hge : 13855161029 ≤ p := T524221_13215 (hP p hp).1 hd
        (S4b 524221 (hP 524221 hc).1 (by norm_num) (hPN 524221 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b524221]
      exact step_ge (t := 13855161029) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e131 : c = 131071
    · subst e131
      have hge : 4194271 ≤ p := T131071_13215 (hP p hp).1 hd
        (S4b 131071 (hP 131071 hc).1 (by norm_num) (hPN 131071 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b131071]
      exact step_ge (t := 4194271) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e524 : c = 524287; · subst e524; exact absurd hc h524
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e524221 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b131071]; norm_num
  · rw [b524287]
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num

-- Case E: 16381 ∉ P, 19423 ∉ P, 126943 ∈ P, 262111 ∈ P, and every z ∈ N has z % 3 ≠ 1.
theorem node_E {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
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
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P)
    (h126 : 126943 ∈ P) (h262 : 262111 ∈ P) (h19423 : 19423 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h8191N : 8191 ∉ N := fun h => by have := hN25 8191 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have T3967 : ∀ p ∈ P, 3967 ∣ p + 1 → p = 126943 := fun p hp hd =>
    S2 3967 (by norm_num) (by norm_num) h3967N p hp 126943 h126 hd (by decide)
  have T8191 : ∀ p ∈ P, 8191 ∣ p + 1 → p = 262111 := fun p hp hd =>
    S2 8191 (by norm_num) (by norm_num) h8191N p hp 262111 h262 hd (by decide)
  have gap := gap9_8191 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h8191
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 8191 ∨ 13215 ≤ r)) := by
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
      by_cases e8191 : r = 8191; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e8191))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e8191)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) else
      if p = 19 then 20 / 19 * (608 / 607 * (16043010 / 16043008)) else
      if p = 607 then 608 / 607 * (16043010 / 16043008) else
      if p = 7 then 8 / 7 * (224 / 223 * (5893890 / 5893888)) else
      if p = 223 then 224 / 223 * (5893890 / 5893888) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) else
      if p = 3967 then 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) else
      if p = 126943 then 126944 / 126943 * (16248704 / 16248702) else
      if p = 127 then 1 else
      if p = 8191 then 8192 / 8191 * (262112 / 262111 * (524222 / 524220)) else
      if p = 262111 then 262112 / 262111 * (524222 / 524220) else
      if p = 131071 then 131072 / 131071 * (4194272 / 4194270) else
      if p = 524287 then 524288 / 524287 * (1048574 / 1048572) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (16043010 / 16043008)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (16043010 / 16043008) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (5893890 / 5893888)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (5893890 / 5893888) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) := by rw [hβ]; norm_num
  have b126 : β 126943 = 126944 / 126943 * (16248704 / 16248702) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (262112 / 262111 * (524222 / 524220)) := by rw [hβ]; norm_num
  have b262 : β 262111 = 262112 / 262111 * (524222 / 524220) := by rw [hβ]; norm_num
  have b131071 : β 131071 = 131072 / 131071 * (4194272 / 4194270) := by rw [hβ]; norm_num
  have b524287 : β 524287 = 524288 / 524287 * (1048574 / 1048572) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 126943 → c ≠ 127 → c ≠ 8191 → c ≠ 262111 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e126, if_neg e127, if_neg e8191, if_neg e262, if_neg e131,
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
    by_cases e126 : p = 126943; · subst e126; rw [b126]; norm_num
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; rw [b8191]; norm_num
    by_cases e262 : p = 262111; · subst e262; rw [b262]; norm_num
    by_cases e131 : p = 131071; · subst e131; rw [b131071]; norm_num
    by_cases e524 : p = 524287; · subst e524; rw [b524287]; norm_num
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524]
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
      have hge : 16043009 ≤ p := T607_16043009 (hP p hp).1 hd
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
        (fun h => by
          have := T8191 9943873 (h ▸ hp) (by decide)
          omega)
      rw [b607]
      exact step_ge (t := 16043009) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 5893889 ≤ p := T223_5893889 (hP p hp).1 hd
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
      exact step_ge (t := 5893889) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967; · subst e3967; obtain rfl : p = 126943 := T3967 p hp hd; rw [b3967, b126]; norm_num
    by_cases e126 : c = 126943
    · subst e126
      have hge : 16248703 ≤ p := T126943_13215 (hP p hp).1 hd
        (S4b 126943 (hP 126943 hc).1 (by norm_num) (hPN 126943 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b126]
      exact step_ge (t := 16248703) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191; · subst e8191; obtain rfl : p = 262111 := T8191 p hp hd; rw [b8191, b262]; norm_num
    by_cases e262 : c = 262111
    · subst e262
      have hge : 524221 ≤ p := by
        have := two_mul_le (hP 262111 hc).1 (by norm_num) (hP p hp).1 (hP p hp).2 hd
        omega
      rw [b262]
      exact step_ge (t := 524221) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e131 : c = 131071
    · subst e131
      have hge : 4194271 ≤ p := T131071_13215 (hP p hp).1 hd
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
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b131071]; norm_num
  · rw [b524287]; norm_num
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num

-- Boosted prime gaps for H1 (16381 | n), H2 (19423 | n), H3 (126943, 262111, 131071, 524287 simple).
theorem gap_H1_16381 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P) (h16 : 16381 ∈ P) :
    ∀ q ∈ P, q < 68378 →
      q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 8191 ∨
        q = 16381 := by
  have hA : ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 16381} : Finset ℕ) ⊆ P := by
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
    · exact h8191
    · exact h16
  intro q hq hlt
  by_cases hqA : q ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 16381} : Finset ℕ)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hqA; exact hqA
  · exfalso
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 16381} : Finset ℕ), (p + 1) =
        8911715817805389496320 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 16381} : Finset ℕ), p =
        4455923074344686632065 := by decide
    rw [e1, e2] at h
    omega

theorem gap_H2_19423 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P) (h19 : 19423 ∈ P) :
    ∀ q ∈ P, q < 41348 →
      q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 8191 ∨
        q = 19423 := by
  have hA : ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ) ⊆ P := by
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
    · exact h8191
    · exact h19
  intro q hq hlt
  by_cases hqA : q ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hqA; exact hqA
  · exfalso
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ), (p + 1) =
        10566546700345005834240 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 19423} : Finset ℕ), p =
        5283401127708738688395 := by decide
    rw [e1, e2] at h
    omega

theorem gap_H3_four {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P)
    (h126 : 126943 ∈ P) (h262 : 262111 ∈ P) (h131 : 131071 ∈ P) (h524 : 524287 ∈ P) :
    ∀ q ∈ P, q < 18369 →
      q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 8191 := by
  have hA : ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 126943, 262111, 131071, 524287} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h607
    · exact h3967
    · exact h8191
    · exact h126
    · exact h262
    · exact h131
    · exact h524
  intro q hq hlt
  by_cases hqA : q ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 126943, 262111, 131071, 524287} : Finset ℕ)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hqA
    rcases hqA with h | h | h | h | h | h | h | h | h | h | h | h | h
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
    · omega
    · omega
  · exfalso
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 126943, 262111, 131071, 524287} : Finset ℕ), (p + 1) =
        1243865248000019727306182255372748718080 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967, 8191, 126943, 262111, 131071, 524287} : Finset ℕ), p =
        621966482664494855364239486735277606165 := by decide
    rw [e1, e2] at h
    omega

-- Master classification theorem for H1 (8191 | n, thin kernel Y ≤ 5001/5000, a ≥ 48).
theorem thin_8191_split {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h7 : 7 ∣ n) (h19 : 19 ∣ n) (h31 : 31 ∣ n)
    (hl : ∀ q : ℕ, q.Prime → q ∣ n → q < 5057 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967)
    (h223 : 223 ∣ n) (h607 : 607 ∣ n) (h3967 : 3967 ∣ n) (h48 : 48 ≤ padicValNat 2 n)
    (hthin : ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000)
    (h8191 : 8191 ∣ n) :
    (∀ z ∈ S, 25000 ≤ z) ∧ ¬ 7933 ∣ n ∧
      ((16381 ∣ n ∧ ¬ 19423 ∣ n ∧
          ∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 68378 →
            q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
              q = 8191 ∨ q = 16381) ∨
        (¬ 16381 ∣ n ∧ 19423 ∣ n ∧
          ∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 41348 →
            q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
              q = 8191 ∨ q = 19423) ∨
        (¬ 16381 ∣ n ∧ ¬ 19423 ∣ n ∧
          126943 ∣ n ∧ ¬ 126943 ^ 2 ∣ n ∧
          262111 ∣ n ∧ ¬ 262111 ^ 2 ∣ n ∧
          131071 ∣ n ∧ ¬ 131071 ^ 2 ∣ n ∧
          524287 ∣ n ∧ ¬ 524287 ^ 2 ∣ n ∧
          (∃ z ∈ S, z % 3 = 1) ∧
          ∀ q : ℕ, q.Prime → q ∣ n → q < 18369 →
            q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
              q = 8191)) := by
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (le_trans (by norm_num) h48)
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z := fun z hz =>
    ⟨((hS z).mp hz).1, hadm1 z hz⟩
  have hNb := adm_ge_2100 hNS hadm2
  have hge := ge_25000 (fun w hw => (hNS w hw).1.ne_zero) hthin
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
  have m8191 := mem 8191 (by norm_num) h8191 (by norm_num) (by norm_num)
  have hn7933 : ¬ 7933 ∣ n := fun h79 => by
    have m79 := mem 7933 (by norm_num) h79 (by norm_num) (by norm_num)
    have hlt := gap9_8191 hP hNS hK hKK1 E m3 m5 m7 m19 m31 m223 m607 m3967 m8191 7933 m79
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at hlt
  refine ⟨hge, hn7933, ?_⟩
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
  have hD : ∀ U : Finset ℕ,
      (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ S) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        4 / 3 * (75000 / 74996) * (1 / 24999) :=
    fun U hU => sumD_thin25 (fun w hw => ⟨(hNS w hw).1, hge w hw⟩) hthin U hU
  by_cases h16 : 16381 ∣ n
  · left
    have m16 := mem 16381 (by norm_num) h16 (by norm_num) (by norm_num)
    have hn19 : ¬ 19423 ∣ n := fun h19d =>
      excl_16381_19423 hP hNS hK hKK1 E m3 m5 m7 m19 m31 m223 m607 m3967 m8191 m16
        (mem 19423 (by norm_num) h19d (by norm_num) (by norm_num))
    refine ⟨h16, hn19, fun q hqp hqn hnsq hlt => ?_⟩
    by_cases hq2 : q = 2
    · exact Or.inl hq2
    · have hqS : q ∉ S := fun hx => hnsq ((hS q).mp hx).2.2
      have hqP : q ∈ P := (hmem q).mpr ⟨hqp, hq2, hqn, hqS⟩
      exact Or.inr (gap_H1_16381 hP hNS hK hKK1 E m3 m5 m7 m19 m31 m223 m607 m3967 m8191 m16 q hqP hlt)
  · by_cases h19423 : 19423 ∣ n
    · right; left
      have m19423 := mem 19423 (by norm_num) h19423 (by norm_num) (by norm_num)
      refine ⟨h16, h19423, fun q hqp hqn hnsq hlt => ?_⟩
      by_cases hq2 : q = 2
      · exact Or.inl hq2
      · have hqS : q ∉ S := fun hx => hnsq ((hS q).mp hx).2.2
        have hqP : q ∈ P := (hmem q).mpr ⟨hqp, hq2, hqn, hqS⟩
        exact Or.inr (gap_H2_19423 hP hNS hK hKK1 E m3 m5 m7 m19 m31 m223 m607 m3967 m8191 m19423 q hqP hlt)
    · right; right
      have n16 : 16381 ∉ P := fun hx => h16 ((hmem 16381).mp hx).2.2.1
      have n19423 : 19423 ∉ P := fun hx => h19423 ((hmem 19423).mp hx).2.2.1
      have m126 : 126943 ∈ P := by
        by_contra n126
        exact node_A hP hPN hNS hK hKr hKK1 hNb hge hD E h48 T3 T5 hs m3 m5 m7 m19 m31 m223
          m607 m3967 m8191 n16 n19423 n126
      have m262 : 262111 ∈ P := by
        by_contra n262
        by_cases m994 : 9943873 ∈ P
        · exact node_B_with994 hP hPN hNS hK hKr hKK1 hNb hge hD E h48 T3 T5 hs m3 m5 m7 m19 m31
            m223 m607 m3967 m8191 m126 m994 n19423
        · exact node_B_no994 hP hPN hNS hK hKr hKK1 hNb hge hD E h48 T3 T5 hs m3 m5 m7 m19 m31
            m223 m607 m3967 m8191 m126 n16 n19423 n262 m994
      have m131 : 131071 ∈ P := by
        by_contra n131
        exact node_C hP hPN hNS hK hKr hKK1 hNb hge hD E h48 T3 T5 hs m3 m5 m7 m19 m31 m223
          m607 m3967 m8191 m126 m262 n19423 n131
      have m524 : 524287 ∈ P := by
        by_contra n524
        by_cases m524221 : 524221 ∈ P
        · exact node_D2 hP hPN hNS hK hKr hKK1 hNb hge hD E h48 T3 T5 hs m3 m5 m7 m19 m31 m223
            m607 m3967 m8191 m126 m262 m524221 n19423 n524
        · exact node_D1 hP hPN hNS hK hKr hKK1 hNb hge hD E h48 T3 T5 hs m3 m5 m7 m19 m31 m223
            m607 m3967 m8191 m126 m262 n19423 n524 m524221
      have hex1 : ∃ z ∈ S, z % 3 = 1 := by
        by_contra hno1
        push Not at hno1
        have hDs2 : ∀ U : Finset ℕ,
            (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ S) →
            ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
              2 / 3 * (75000 / 74998) * (1 / 24999) +
                4 / 3 * (75000 / 74996) * (1 / 300000000) :=
          fun U hU => sumD_s2only (fun w hw => ⟨(hNS w hw).1, hge w hw⟩) hno1 hthin U hU
        exact node_E hP hPN hNS hK hKr hKK1 hNb hge hDs2 E h48 T3 T5 hs m3 m5 m7 m19 m31 m223
          m607 m3967 m8191 m126 m262 n19423
      have h126d : 126943 ∣ n := ((hmem 126943).mp m126).2.2.1
      have h126nsq : ¬ 126943 ^ 2 ∣ n := fun hsq =>
        ((hmem 126943).mp m126).2.2.2 ((hS 126943).mpr ⟨((hmem 126943).mp m126).1, by norm_num, hsq⟩)
      have h262d : 262111 ∣ n := ((hmem 262111).mp m262).2.2.1
      have h262nsq : ¬ 262111 ^ 2 ∣ n := fun hsq =>
        ((hmem 262111).mp m262).2.2.2 ((hS 262111).mpr ⟨((hmem 262111).mp m262).1, by norm_num, hsq⟩)
      have h131d : 131071 ∣ n := ((hmem 131071).mp m131).2.2.1
      have h131nsq : ¬ 131071 ^ 2 ∣ n := fun hsq =>
        ((hmem 131071).mp m131).2.2.2 ((hS 131071).mpr ⟨((hmem 131071).mp m131).1, by norm_num, hsq⟩)
      have h524d : 524287 ∣ n := ((hmem 524287).mp m524).2.2.1
      have h524nsq : ¬ 524287 ^ 2 ∣ n := fun hsq =>
        ((hmem 524287).mp m524).2.2.2 ((hS 524287).mpr ⟨((hmem 524287).mp m524).1, by norm_num, hsq⟩)
      refine ⟨h16, h19423, h126d, h126nsq, h262d, h262nsq, h131d, h131nsq, h524d, h524nsq, hex1,
        fun q hqp hqn hlt => ?_⟩
      by_cases hq2 : q = 2
      · exact Or.inl hq2
      · have hqP : q ∈ P := mem q hqp hqn (lt_trans hlt (by norm_num)) hq2
        exact Or.inr (gap_H3_four hP hNS hK hKK1 E m3 m5 m7 m19 m31 m223 m607 m3967 m8191 m126
          m262 m131 m524 q hqP hlt)

end Erdos1052C19

-- Case H1: 8191 | n and 16381 | n (with ¬ 7933 | n, ¬ 19423 | n, z >= 25000, simple-prime gap 68378).
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
    8191 ∣ n → ¬ 7933 ∣ n → 16381 ∣ n → ¬ 19423 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 68378 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
        q = 8191 ∨ q = 16381) →
    padicValNat 2 n ≤ A

-- Case H2: 8191 | n and 19423 | n (with ¬ 7933 | n, ¬ 16381 | n, z >= 25000, simple-prime gap 41348).
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
    8191 ∣ n → ¬ 7933 ∣ n → ¬ 16381 ∣ n → 19423 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ^ 2 ∣ n → q < 41348 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨
        q = 8191 ∨ q = 19423) →
    padicValNat 2 n ≤ A

-- Case H3: 8191 | n, neither 16381 nor 19423 divides n; forces all four primes 126943, 262111,
-- 131071, 524287 simple, ∃ z ∈ S with z % 3 = 1, and all-prime exclusion boosted to 18369.
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
    8191 ∣ n → ¬ 7933 ∣ n → ¬ 16381 ∣ n → ¬ 19423 ∣ n →
    126943 ∣ n → ¬ 126943 ^ 2 ∣ n → 262111 ∣ n → ¬ 262111 ^ 2 ∣ n →
    131071 ∣ n → ¬ 131071 ^ 2 ∣ n → 524287 ∣ n → ¬ 524287 ^ 2 ∣ n → (∃ z ∈ S, z % 3 = 1) →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 18369 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 8191) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 →
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1.H1 := by
  rintro ⟨A1, hA1⟩ ⟨A2, hA2⟩ ⟨A3, hA3⟩
  refine ⟨max A1 (max A2 A3), fun n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl
    h223 h607 h3967 h48 hthin h8191 => ?_⟩
  obtain ⟨hge, hn7933, hcases⟩ := Erdos1052C19.thin_8191_split h hS hadm1 hadm2 h3 h5 h7 h19 h31 hl
    h223 h607 h3967 h48 hthin h8191
  rcases hcases with ⟨h16381, hn19, hgap1⟩ | ⟨hn16, h19423, hgap2⟩ |
    ⟨hn16, hn19, h126, h126n, h262, h262n, h131, h131n, h524, h524n, hex1, hgap3⟩
  · exact (hA1 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 h223 h607 h3967 h48
      hthin hge h8191 hn7933 h16381 hn19 hgap1).trans (le_max_left _ _)
  · exact (hA2 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 h223 h607 h3967 h48
      hthin hge h8191 hn7933 hn16 h19423 hgap2).trans
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact (hA3 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 h223 h607 h3967 h48
      hthin hge h8191 hn7933 hn16 hn19 h126 h126n h262 h262n h131 h131n h524 h524n hex1 hgap3).trans
      (le_trans (le_max_right _ _) (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1
