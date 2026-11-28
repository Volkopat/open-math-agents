import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1_H2_R1

open AgohGiuga
open scoped Nat
open OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1 (sum_inv_finset_ap_le_add
  sum_real_gt_k exp_gt_pow_27_10)

private lemma mod_five_of_factor_mod_thirty_eleven {n p : ℕ} (hn : 0 < n)
    (hp : p ∈ n.primeFactors) (hres : p % 30 = 11)
    (hdiv : p * (p - 1) ∣ n / p - 1) : n % 5 = 1 := by
  have hp5 : p % 5 = 1 := by omega
  have hpred : 5 ∣ p - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hq : 5 ∣ n / p - 1 := hpred.trans ((dvd_mul_left (p - 1) p).trans hdiv)
  have hp_dvd := Nat.dvd_of_mem_primeFactors hp
  have hq_pos : 0 < n / p :=
    Nat.div_pos (Nat.le_of_dvd hn hp_dvd) (Nat.prime_of_mem_primeFactors hp).pos
  have hq5 : (n / p) % 5 = 1 := by
    obtain ⟨a, ha⟩ := hq
    omega
  rw [← Nat.div_mul_cancel hp_dvd, Nat.mul_mod, hq5, hp5]

private lemma card_ge_of_three_residue_classes {n k : ℕ} (hn : n ≠ 0)
    (hthree : 3 ∣ n) (hk : 2 ≤ k)
    (hres : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    2500000 ≤ n.primeFactors.card := by
  classical
  by_contra! hsmall
  have hthree_mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hthree, hn⟩
  let S := n.primeFactors.erase 3
  have hS_res : ∀ p ∈ S, p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
    intro p hp
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
    exact (hres p hmem).resolve_left hne
  -- Send the three admissible residues in each block of 30 to 9, 19, and 29.
  let f (p : ℕ) := 30 * (p / 30) + if p % 30 = 17 then 9 else if p % 30 = 23 then 19 else 29
  have hf_inj : Set.InjOn f (↑S : Set ℕ) := by
    intro p hp q hq heq
    rcases hS_res p hp with hp | hp | hp <;>
      rcases hS_res q hq with hq | hq | hq <;>
      simp [f, hp, hq] at heq <;> omega
  have hf_le : ∀ p ∈ S, f p ≤ p := by
    intro p hp
    rcases hS_res p hp with hp | hp | hp <;> simp [f, hp] <;> omega
  let T := S.image f
  have hT_card : T.card ≤ 2500000 := by
    rw [Finset.card_image_of_injOn hf_inj, Finset.card_erase_of_mem hthree_mem]
    omega
  have hT_res : ∀ p ∈ T, 9 ≤ p ∧ p % 10 = 9 % 10 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rcases hS_res q hq with hq | hq | hq <;> simp [f, hq] <;> omega
  have hcompare : (∑ p ∈ S, 1 / (p : ℝ)) ≤ ∑ p ∈ T, 1 / (p : ℝ) := by
    rw [Finset.sum_image hf_inj]
    refine Finset.sum_le_sum fun p hp => ?_
    have hfpos : 0 < f p := by
      have := (hT_res (f p) (Finset.mem_image_of_mem f hp)).1
      omega
    exact one_div_le_one_div_of_le (by exact_mod_cast hfpos) (by exact_mod_cast hf_le p hp)
  have hap := sum_inv_finset_ap_le_add T 9 10 (by decide) (by decide) hT_res
  have hlog : Real.log (((9 + 10 * T.card : ℕ) : ℝ) / 9) < 15 := by
    rw [Real.log_lt_iff_lt_exp (by positivity)]
    have hcard : (T.card : ℝ) ≤ 2500000 := by exact_mod_cast hT_card
    have hpow : (27 / 10 : ℝ) ^ 15 < Real.exp 15 := by
      simpa only [Nat.cast_ofNat] using exp_gt_pow_27_10 15 (by decide)
    calc (((9 + 10 * T.card : ℕ) : ℝ) / 9)
        ≤ (9 + 10 * 2500000 : ℝ) / 9 := by push_cast; linarith
      _ ≤ (27 / 10 : ℝ) ^ 15 := by norm_num
      _ < Real.exp 15 := hpow
  have hsplit := Finset.add_sum_erase n.primeFactors (fun p => 1 / (p : ℝ)) hthree_mem
  have hfull := sum_real_gt_k hn hsum
  have hk_real : (2 : ℝ) ≤ k := by exact_mod_cast hk
  simp only [Nat.cast_ofNat] at hsplit hap
  change 1 / (3 : ℝ) + (∑ p ∈ S, 1 / (p : ℝ)) = _ at hsplit
  linarith only [hcompare, hap, hlog, hsplit, hfull, hk_real]

/-- Without the residue class 11 modulo 30, the reciprocal sum requires at least
2,500,000 prime factors. -/
def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → ¬ (5 ∣ n) →
    n % 36 = 21 →
    2500000 ≤ n.primeFactors.card →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    4 ≤ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∃ k : ℕ, 2 ≤ k ∧ 2 ∣ k ∧
      n.primeFactors.card % 8 = (k + 1) % 8 ∧
      (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = (k + 1) % 4 ∧
      n % 27 = (9 * (k + n.primeFactors.card - 1) + 3) % 27 ∧
      ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) →
    False

/-- A prime factor in the residue class 11 modulo 30 forces the product to be
1 modulo 5. -/
def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → ¬ (5 ∣ n) →
    n % 180 = 21 →
    100000 ≤ n.primeFactors.card →
    (∃ p ∈ n.primeFactors, p % 30 = 11) →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    4 ≤ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∃ k : ℕ, 2 ≤ k ∧ 2 ∣ k ∧
      n.primeFactors.card % 8 = (k + 1) % 8 ∧
      (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = (k + 1) % 4 ∧
      n % 27 = (9 * (k + n.primeFactors.card - 1) + 3) % 27 ∧
      ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) →
    False

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1.H2 := by
  intro h1 h2 n hcomp hsqf hodd hthree hfive h36 hcard hmod4 hr3 hr3min hres hdiv hnormal hk
  by_cases h11 : ∃ p ∈ n.primeFactors, p % 30 = 11
  · obtain ⟨p, hp, hp11⟩ := h11
    have h5 := mod_five_of_factor_mod_thirty_eleven (Nat.pos_of_ne_zero hsqf.ne_zero) hp hp11 (hdiv p hp)
    have h180 : n % 180 = 21 := by omega
    exact h2 n hcomp hsqf hodd hthree hfive h180 hcard ⟨p, hp, hp11⟩
      hmod4 hr3 hr3min hres hdiv hnormal hk
  · have hres' : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
      intro p hp
      rcases hres p hp with h3 | h11' | hother
      · exact Or.inl h3
      · exact (h11 ⟨p, hp, h11'⟩).elim
      · exact Or.inr hother
    obtain ⟨k, hk2, hk_even, hk8, hk4, hk27, hsum⟩ := hk
    have hcard' := card_ge_of_three_residue_classes hsqf.ne_zero hthree hk2 hres' hsum
    exact h1 n hcomp hsqf hodd hthree hfive h36 hcard' hmod4 hr3 hr3min hres' hdiv hnormal
      ⟨k, hk2, hk_even, hk8, hk4, hk27, hsum⟩

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1_H2_R1
