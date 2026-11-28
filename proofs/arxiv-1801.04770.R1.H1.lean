import OMAReductions.R_arxiv_1801_04770_R1

namespace OMA.Proof_arxiv_1801_04770_R1_H1

private lemma sq_mod_four_ne_three (y : ℕ) : y ^ 2 % 4 ≠ 3 := by
  have h : y % 4 < 4 := Nat.mod_lt y (by decide)
  have hdiv : y = 4 * (y / 4) + y % 4 := (Nat.div_add_mod y 4).symm
  have hsq : y ^ 2 = 4 * (4 * (y / 4) ^ 2 + 2 * (y / 4) * (y % 4)) + (y % 4) ^ 2 := by
    conv_lhs => rw [hdiv]
    ring
  rw [hsq, Nat.mul_add_mod]
  generalize y % 4 = r at h ⊢
  interval_cases r <;> decide

private lemma factor_sq_or_two_sq {A : ℕ} (hA : A ≠ 0)
    (heven_odd : ∀ q : ℕ, q.Prime → q ≠ 2 → Even (A.factorization q)) :
    (∃ y : ℕ, A = y ^ 2) ∨ (∃ y : ℕ, A = 2 * y ^ 2) := by
  let y := ∏ p ∈ A.primeFactors, p ^ (A.factorization p / 2)
  have hy_sq : y ^ 2 = ∏ p ∈ A.primeFactors, p ^ (2 * (A.factorization p / 2)) := by
    simp only [y, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, mul_comm]
  have hprod : ∏ p ∈ A.primeFactors, p ^ A.factorization p = A :=
    Nat.factorization_prod_pow_eq_self hA
  rcases Nat.even_or_odd (A.factorization 2) with h2e | h2o
  · left
    refine ⟨y, ?_⟩
    rw [hy_sq]
    conv_lhs => rw [← hprod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpe : Even (A.factorization p) := by
      by_cases hp2 : p = 2
      · subst hp2; exact h2e
      · exact heven_odd p (Nat.prime_of_mem_primeFactors hp) hp2
    obtain ⟨t, ht⟩ := hpe
    rw [ht, show 2 * ((t + t) / 2) = t + t by omega]
  · right
    refine ⟨y, ?_⟩
    have h2mem : 2 ∈ A.primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨Nat.prime_two, ?_, hA⟩
      have hne0 : A.factorization 2 ≠ 0 := by obtain ⟨t, ht⟩ := h2o; omega
      exact Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hA |>.mpr (by omega)
    rw [hy_sq]
    conv_lhs => rw [← hprod]
    rw [← Finset.mul_prod_erase A.primeFactors _ h2mem,
      ← Finset.mul_prod_erase A.primeFactors _ h2mem, ← mul_assoc]
    congr 1
    · obtain ⟨t, ht⟩ := h2o
      rw [ht, show 2 * ((2 * t + 1) / 2) = 2 * t by omega, ← pow_succ']
    · refine Finset.prod_congr rfl fun p hp => ?_
      have hp2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
      have hpmem : p ∈ A.primeFactors := (Finset.mem_erase.mp hp).2
      have hpe : Even (A.factorization p) := heven_odd p (Nat.prime_of_mem_primeFactors hpmem) hp2
      obtain ⟨t, ht⟩ := hpe
      rw [ht, show 2 * ((t + t) / 2) = t + t by omega]

end OMA.Proof_arxiv_1801_04770_R1_H1

theorem OMA.solution : OMA.R_arxiv_1801_04770_R1.H1 := by
  intro a b n x ha hab hn heven heq
  open OMA.Proof_arxiv_1801_04770_R1_H1 in
  obtain ⟨k, rfl⟩ := heven
  have hk : 4 ≤ k := by omega
  have ha3 : 3 ≤ a := by omega
  have hak : 81 ≤ a ^ k := by
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by decide) hk
      _ ≤ a ^ k := Nat.pow_le_pow_left ha3 k
  have hbk : 81 ≤ b ^ k := by
    calc 81 ≤ a ^ k := hak
      _ ≤ b ^ k := Nat.pow_le_pow_left hab.le k
  have ha_pow : a ^ (k + k) = (a ^ k) ^ 2 := by rw [pow_add, sq]
  have hb_pow : b ^ (k + k) = (b ^ k) ^ 2 := by rw [pow_add, sq]
  have ha2 : 4 ≤ a ^ (k + k) := by rw [ha_pow]; nlinarith
  have hb2 : 4 ≤ b ^ (k + k) := by rw [hb_pow]; nlinarith
  set A := a ^ (k + k) - 2
  set B := b ^ (k + k) - 2
  have hA0 : A ≠ 0 := by omega
  have hB0 : B ≠ 0 := by omega
  have hAB : A * B = x ^ 2 := by
    have hz : ((A * B : ℕ) : ℤ) = ((x ^ 2 : ℕ) : ℤ) := by
      have hAz : (A : ℤ) = (a : ℤ) ^ (k + k) - 2 := by
        simp only [A]
        rw [Nat.cast_sub (by omega)]
        push_cast; rfl
      have hBz : (B : ℤ) = (b : ℤ) ^ (k + k) - 2 := by
        simp only [B]
        rw [Nat.cast_sub (by omega)]
        push_cast; rfl
      rw [Nat.cast_mul, hAz, hBz, Nat.cast_pow]
      exact heq
    exact Int.ofNat.inj hz
  have hA_odd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ Odd (A.factorization q) := by
    by_contra hno
    push_neg at hno
    have heven_odd : ∀ q : ℕ, q.Prime → q ≠ 2 → Even (A.factorization q) := by
      intro q hq hq2
      exact Nat.not_odd_iff_even.mp (hno q hq hq2)
    rcases factor_sq_or_two_sq hA0 heven_odd with ⟨y, hy⟩ | ⟨y, hy⟩
    · have hy_lt : y < a ^ k := by
        have : y ^ 2 < (a ^ k) ^ 2 := by
          rw [← hy]; simp only [A, ha_pow]; omega
        nlinarith
      have hy_le : y ≤ a ^ k - 1 := by omega
      have hsq_le : y ^ 2 ≤ (a ^ k - 1) ^ 2 := Nat.pow_le_pow_left hy_le 2
      have hgap : (a ^ k - 1) ^ 2 + 2 < (a ^ k) ^ 2 := by
        obtain ⟨t, ht⟩ : ∃ t, a ^ k = t + 81 := ⟨a ^ k - 81, by omega⟩
        rw [ht]
        simp only [show t + 81 - 1 = t + 80 by omega]
        nlinarith
      have : A + 2 = (a ^ k) ^ 2 := by simp only [A, ha_pow]; omega
      omega
    · have h2A : 2 ∣ A := ⟨y ^ 2, hy⟩
      have h2_apow : 2 ∣ a ^ (k + k) := by
        have hadd : a ^ (k + k) = A + 2 := by omega
        rw [hadd]
        exact Nat.dvd_add h2A dvd_rfl
      have h2a : 2 ∣ a := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2_apow
      obtain ⟨c, rfl⟩ := h2a
      have h8 : 8 ∣ (2 * c) ^ (k + k) := by
        rw [mul_pow]
        have h28 : 8 ∣ 2 ^ (k + k) := by
          rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
          exact Nat.pow_dvd_pow 2 (by omega)
        exact dvd_mul_of_dvd_left h28 _
      obtain ⟨t, ht⟩ := h8
      have ht1 : 1 ≤ t := by omega
      have hy2 : y ^ 2 = 4 * t - 1 := by omega
      have hmod : y ^ 2 % 4 = 3 := by
        rw [hy2]
        obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
        rw [show 4 * (u + 1) - 1 = 4 * u + 3 by omega, Nat.mul_add_mod]
      exact sq_mod_four_ne_three y hmod
  obtain ⟨q, hq, hq2, hoddA⟩ := hA_odd
  refine ⟨q, hq, hq2, hoddA, ?_⟩
  have hfac : A.factorization q + B.factorization q = 2 * x.factorization q := by
    have h1 := congrArg (fun m => m.factorization q) hAB
    rw [Nat.factorization_mul hA0 hB0, Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul] at h1
    exact h1
  rw [Nat.odd_iff] at hoddA ⊢
  omega
