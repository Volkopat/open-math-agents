import OMAStatements.S_oeis_a339210

/-!
Proof of the OEIS A339210 conjecture: for every prime `p > 5`, `a(p) = 2`.

We evaluate `∑_{k=0}^{(p+1)/2} pentCoeff (p * k)` directly:
1. `j ↦ j * (3 * j - 1)` is injective on `ℤ` and whenever `j * (3 * j - 1) = 2 * m` we have
   `-(m : ℤ) ≤ j ≤ m`.
2. For `k ≤ (p + 1) / 2` and `j * (3 * j - 1) = 2 * p * k`, primality of `p` forces either
   `p ∣ j` or `p ∣ (3 * j - 1)`.
   - If `p ∣ j`: either `j = 0` (giving `k = 0`, sign `(-1)^0 = 1`) or `|j| ≥ p`, which yields
     `j * (3 * j - 1) ≥ p * (3 * p - 1) > p * (p + 1) ≥ 2 * p * k`, impossible.
   - If `p ∣ (3 * j - 1)`: write `3 * j - 1 = q * p`. For `|q| ≥ 2` and `p > 5`,
     `j * (3 * j - 1) = q * p * (q * p + 1) / 3 > p * (p + 1) ≥ 2 * p * k`, impossible.
     For `q = 0`, `3 * j = 1`, impossible.
     Thus `q ∈ {1, -1}`, and since `p > 5` is prime, `p % 3 ∈ {1, 2}`, selecting the unique
     `j ∈ ℤ` with `3 * j - 1 = ± p`. In both cases `j` is even (since `p` is odd),
     `k = j * (3 * j - 1) / (2 * p) ≤ (p + 1) / 2`, and `(-1)^|j| = 1`.
3. Summing the two nonzero terms yields `1 + 1 = 2`.
-/

namespace A339210Proof

open Finset

private lemma pent_inj {j₁ j₂ : ℤ} (h : j₁ * (3 * j₁ - 1) = j₂ * (3 * j₂ - 1)) : j₁ = j₂ := by
  have hfac : (j₁ - j₂) * (3 * (j₁ + j₂) - 1) = 0 := by linarith
  rcases mul_eq_zero.mp hfac with h1 | h2
  · omega
  · omega

private lemma pent_abs_le {m : ℕ} {j : ℤ} (h : j * (3 * j - 1) = 2 * (m : ℤ)) :
    -(m : ℤ) ≤ j ∧ j ≤ (m : ℤ) := by
  constructor <;> nlinarith

private lemma pentCoeff_eq_of_eq {m : ℕ} {j₀ : ℤ} (h : j₀ * (3 * j₀ - 1) = 2 * (m : ℤ)) :
    OMA.S_oeis_a339210.pentCoeff m = (-1 : ℤ) ^ j₀.natAbs := by
  unfold OMA.S_oeis_a339210.pentCoeff
  have hmem : j₀ ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := Finset.mem_Icc.mpr (pent_abs_le h)
  rw [Finset.sum_eq_single j₀]
  · simp [h]
  · intro j _ hne
    rw [if_neg]
    intro hj
    exact hne (pent_inj (hj.trans h.symm))
  · intro hnot
    exact (hnot hmem).elim

private lemma pentCoeff_eq_zero_of_forall {m : ℕ}
    (h : ∀ j : ℤ, j * (3 * j - 1) ≠ 2 * (m : ℤ)) :
    OMA.S_oeis_a339210.pentCoeff m = 0 := by
  unfold OMA.S_oeis_a339210.pentCoeff
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (h j)]

private lemma prime_pent_cases {p k : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hk : k ≤ (p + 1) / 2) {j : ℤ} (hj : j * (3 * j - 1) = 2 * ((p * k : ℕ) : ℤ)) :
    (k = 0 ∧ j = 0) ∨
    (p % 3 = 2 ∧ 3 * j - 1 = (p : ℤ) ∧ 6 * k = p + 1) ∨
    (p % 3 = 1 ∧ 3 * j - 1 = -(p : ℤ) ∧ 6 * k = p - 1) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd : (p : ℤ) ∣ j * (3 * j - 1) := ⟨2 * (k : ℤ), by push_cast at hj; linarith⟩
  have h2pk : 2 * ((p * k : ℕ) : ℤ) ≤ (p : ℤ) * ((p : ℤ) + 1) := by
    have hk2 : 2 * k ≤ p + 1 := by omega
    have hk2Z : 2 * (k : ℤ) ≤ (p : ℤ) + 1 := by exact_mod_cast hk2
    push_cast
    nlinarith
  rcases hpZ.dvd_or_dvd hdvd with hdiv_j | hdiv_3j
  · obtain ⟨q, hq⟩ := hdiv_j
    rcases eq_or_ne q 0 with rfl | hq0
    · left
      have hj0 : j = 0 := by simp [hq]
      subst hj0
      simp only [zero_mul] at hj
      have hk0 : k = 0 := by
        have : (p : ℤ) * (k : ℤ) = 0 := by push_cast at hj; linarith
        have hpk0 : p * k = 0 := by exact_mod_cast this
        rcases mul_eq_zero.mp hpk0 with h | h
        · omega
        · exact h
      exact ⟨hk0, rfl⟩
    · exfalso
      have hpZ5 : (5 : ℤ) < (p : ℤ) := by exact_mod_cast hp5
      have hq1 : 1 ≤ q ∨ q ≤ -1 := by omega
      have hle_j : j * (3 * j - 1) ≤ (p : ℤ) * ((p : ℤ) + 1) := hj ▸ h2pk
      rw [hq] at hle_j
      rcases hq1 with hqpos | hqneg
      · have h1 : (p : ℤ) ≤ (p : ℤ) * q := by nlinarith
        have h2 : (p : ℤ) * (3 * (p : ℤ) - 1) ≤ ((p : ℤ) * q) * (3 * ((p : ℤ) * q) - 1) := by
          have ha : (0 : ℤ) ≤ (p : ℤ) * q - (p : ℤ) := by linarith
          have hb : (0 : ℤ) ≤ 3 * ((p : ℤ) * q + (p : ℤ)) - 1 := by linarith
          nlinarith [mul_nonneg ha hb]
        nlinarith
      · have h1 : (p : ℤ) ≤ (p : ℤ) * (-q) := by nlinarith
        have hrew : ((p : ℤ) * q) * (3 * ((p : ℤ) * q) - 1) =
            ((p : ℤ) * (-q)) * (3 * ((p : ℤ) * (-q)) + 1) := by ring
        rw [hrew] at hle_j
        have h2 : (p : ℤ) * (3 * (p : ℤ) + 1) ≤ ((p : ℤ) * (-q)) * (3 * ((p : ℤ) * (-q)) + 1) := by
          have ha : (0 : ℤ) ≤ (p : ℤ) * (-q) - (p : ℤ) := by linarith
          have hb : (0 : ℤ) ≤ 3 * ((p : ℤ) * (-q) + (p : ℤ)) + 1 := by linarith
          nlinarith [mul_nonneg ha hb]
        nlinarith
  · obtain ⟨q, hq⟩ := hdiv_3j
    have hq_bound : q = 1 ∨ q = -1 := by
      by_contra! hnot
      have hpZ5 : (5 : ℤ) < (p : ℤ) := by exact_mod_cast hp5
      have hq0 : q ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hq
        omega
      have hqge2 : 2 ≤ q ∨ q ≤ -2 := by omega
      have h3j : 3 * j = (p : ℤ) * q + 1 := by linarith
      have hmul : 3 * (j * (3 * j - 1)) = (p : ℤ) * q * ((p : ℤ) * q + 1) := by
        have h1 : 3 * (j * (3 * j - 1)) = (3 * j) * (3 * j - 1) := by ring
        rw [h1, hq, h3j]; ring
      have hle : (p : ℤ) * q * ((p : ℤ) * q + 1) ≤ 3 * ((p : ℤ) * ((p : ℤ) + 1)) := by
        linarith
      rcases hqge2 with h2 | hm2
      · have h1 : 2 * (p : ℤ) ≤ (p : ℤ) * q := by nlinarith
        have h2' : (2 * (p : ℤ)) * (2 * (p : ℤ) + 1) ≤ ((p : ℤ) * q) * ((p : ℤ) * q + 1) := by
          have ha : (0 : ℤ) ≤ (p : ℤ) * q - 2 * (p : ℤ) := by linarith
          have hb : (0 : ℤ) ≤ (p : ℤ) * q + 2 * (p : ℤ) + 1 := by linarith
          nlinarith [mul_nonneg ha hb]
        nlinarith
      · have h1 : 2 * (p : ℤ) ≤ (p : ℤ) * (-q) := by nlinarith
        have hrew : (p : ℤ) * q * ((p : ℤ) * q + 1) =
            ((p : ℤ) * (-q)) * ((p : ℤ) * (-q) - 1) := by ring
        rw [hrew] at hle
        have h2' : (2 * (p : ℤ)) * (2 * (p : ℤ) - 1) ≤ ((p : ℤ) * (-q)) * ((p : ℤ) * (-q) - 1) := by
          have ha : (0 : ℤ) ≤ (p : ℤ) * (-q) - 2 * (p : ℤ) := by linarith
          have hb : (0 : ℤ) ≤ (p : ℤ) * (-q) + 2 * (p : ℤ) - 1 := by linarith
          nlinarith [mul_nonneg ha hb]
        nlinarith
    rcases hq_bound with rfl | rfl
    · right; left
      have h3j : 3 * j - 1 = (p : ℤ) := by linarith
      have hmod : p % 3 = 2 := by omega
      have h6k : 6 * k = p + 1 := by
        have h1 : 3 * (2 * ((p * k : ℕ) : ℤ)) = (p : ℤ) * ((p : ℤ) + 1) := by nlinarith
        push_cast at h1
        have h2 : (p : ℤ) * (6 * (k : ℤ) - ((p : ℤ) + 1)) = 0 := by linarith
        rcases mul_eq_zero.mp h2 with h | h
        · omega
        · omega
      exact ⟨hmod, h3j, h6k⟩
    · right; right
      have h3j : 3 * j - 1 = -(p : ℤ) := by linarith
      have hmod : p % 3 = 1 := by omega
      have h6k : 6 * k = p - 1 := by
        have h1 : 3 * (2 * ((p * k : ℕ) : ℤ)) = (p : ℤ) * ((p : ℤ) - 1) := by nlinarith
        push_cast at h1
        have h2 : (p : ℤ) * (6 * (k : ℤ) - ((p : ℤ) - 1)) = 0 := by linarith
        rcases mul_eq_zero.mp h2 with h | h
        · omega
        · omega
      exact ⟨hmod, h3j, h6k⟩

private lemma neg_one_pow_even_natAbs {j : ℤ} (h : 2 ∣ j) : (-1 : ℤ) ^ j.natAbs = 1 := by
  obtain ⟨m, rfl⟩ := h
  have hev : Even (2 * m).natAbs := by
    rw [Int.natAbs_mul]
    exact even_two_mul m.natAbs
  exact hev.neg_one_pow

theorem solve : ∀ p : ℕ, p.Prime → 5 < p → OMA.S_oeis_a339210.a p = 2 := by
  intro p hp hp5
  unfold OMA.S_oeis_a339210.a
  have hp_odd : p % 2 = 1 := by
    have h2 : p ≠ 2 := by omega
    rcases hp.eq_two_or_odd with rfl | hodd
    · exact (h2 rfl).elim
    · exact hodd
  have hp_mod3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : ¬ 3 ∣ p := by
      intro hd
      rcases (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp hd with h
      omega
    omega
  rcases hp_mod3 with hmod1 | hmod2
  · let k₁ : ℕ := (p - 1) / 6
    let j₁ : ℤ := (1 - (p : ℤ)) / 3
    have hk₁_eq : 6 * k₁ = p - 1 := by omega
    have hk₁_pos : 0 < k₁ := by omega
    have hk₁_mem : k₁ ∈ Finset.range ((p + 1) / 2 + 1) := by
      rw [Finset.mem_range]; omega
    have h0_mem : 0 ∈ Finset.range ((p + 1) / 2 + 1) := by
      rw [Finset.mem_range]; omega
    have hj₁_eq : 3 * j₁ = 1 - (p : ℤ) := by omega
    have hj₁_pent : j₁ * (3 * j₁ - 1) = 2 * ((p * k₁ : ℕ) : ℤ) := by
      push_cast
      have hk₁Z : 6 * (k₁ : ℤ) = (p : ℤ) - 1 := by omega
      nlinarith
    have hj₁_even : 2 ∣ j₁ := ⟨-(k₁ : ℤ), by
      have hk₁Z : 6 * (k₁ : ℤ) = (p : ℤ) - 1 := by omega
      omega⟩
    have hsum_split :
        ∑ k ∈ Finset.range ((p + 1) / 2 + 1), OMA.S_oeis_a339210.pentCoeff (p * k) =
        OMA.S_oeis_a339210.pentCoeff (p * 0) + OMA.S_oeis_a339210.pentCoeff (p * k₁) := by
      rw [← Finset.sum_pair (f := fun k => OMA.S_oeis_a339210.pentCoeff (p * k)) (show (0 : ℕ) ≠ k₁ by omega)]
      symm
      apply Finset.sum_subset
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h0_mem
        · exact hk₁_mem
      · intro k hk hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        apply pentCoeff_eq_zero_of_forall
        intro j hj
        have hk_le : k ≤ (p + 1) / 2 := by
          rw [Finset.mem_range] at hk; omega
        rcases prime_pent_cases hp hp5 hk_le hj with ⟨rfl, _⟩ | ⟨h2, _, _⟩ | ⟨_, _, h6k⟩
        · exact hnot.1 rfl
        · omega
        · exact hnot.2 (by omega)
    rw [hsum_split]
    have h0_val : OMA.S_oeis_a339210.pentCoeff (p * 0) = 1 := by
      rw [pentCoeff_eq_of_eq (j₀ := 0) (by simp)]
      simp
    have hk₁_val : OMA.S_oeis_a339210.pentCoeff (p * k₁) = 1 := by
      rw [pentCoeff_eq_of_eq hj₁_pent]
      exact neg_one_pow_even_natAbs hj₁_even
    rw [h0_val, hk₁_val]
    norm_num
  · let k₁ : ℕ := (p + 1) / 6
    let j₁ : ℤ := ((p : ℤ) + 1) / 3
    have hk₁_eq : 6 * k₁ = p + 1 := by omega
    have hk₁_pos : 0 < k₁ := by omega
    have hk₁_mem : k₁ ∈ Finset.range ((p + 1) / 2 + 1) := by
      rw [Finset.mem_range]; omega
    have h0_mem : 0 ∈ Finset.range ((p + 1) / 2 + 1) := by
      rw [Finset.mem_range]; omega
    have hj₁_eq : 3 * j₁ = (p : ℤ) + 1 := by omega
    have hj₁_pent : j₁ * (3 * j₁ - 1) = 2 * ((p * k₁ : ℕ) : ℤ) := by
      push_cast
      have hk₁Z : 6 * (k₁ : ℤ) = (p : ℤ) + 1 := by exact_mod_cast hk₁_eq
      nlinarith
    have hj₁_even : 2 ∣ j₁ := ⟨(k₁ : ℤ), by
      have hk₁Z : 6 * (k₁ : ℤ) = (p : ℤ) + 1 := by exact_mod_cast hk₁_eq
      omega⟩
    have hsum_split :
        ∑ k ∈ Finset.range ((p + 1) / 2 + 1), OMA.S_oeis_a339210.pentCoeff (p * k) =
        OMA.S_oeis_a339210.pentCoeff (p * 0) + OMA.S_oeis_a339210.pentCoeff (p * k₁) := by
      rw [← Finset.sum_pair (f := fun k => OMA.S_oeis_a339210.pentCoeff (p * k)) (show (0 : ℕ) ≠ k₁ by omega)]
      symm
      apply Finset.sum_subset
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h0_mem
        · exact hk₁_mem
      · intro k hk hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        apply pentCoeff_eq_zero_of_forall
        intro j hj
        have hk_le : k ≤ (p + 1) / 2 := by
          rw [Finset.mem_range] at hk; omega
        rcases prime_pent_cases hp hp5 hk_le hj with ⟨rfl, _⟩ | ⟨_, _, h6k⟩ | ⟨h1, _, _⟩
        · exact hnot.1 rfl
        · exact hnot.2 (by omega)
        · omega
    rw [hsum_split]
    have h0_val : OMA.S_oeis_a339210.pentCoeff (p * 0) = 1 := by
      rw [pentCoeff_eq_of_eq (j₀ := 0) (by simp)]
      simp
    have hk₁_val : OMA.S_oeis_a339210.pentCoeff (p * k₁) = 1 := by
      rw [pentCoeff_eq_of_eq hj₁_pent]
      exact neg_one_pow_even_natAbs hj₁_even
    rw [h0_val, hk₁_val]
    norm_num

end A339210Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a339210.main :=
  A339210Proof.solve
