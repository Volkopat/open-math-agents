import OMAStatements.S_oeis_a258903
import Mathlib

namespace OMA.S_oeis_a258903_Proof

open OMA.S_oeis_a258903

private lemma factorial_eq_mul_prod_Icc (a n : ℕ) (han : a ≤ n) :
    n.factorial = a.factorial * ∏ j ∈ Finset.Icc (a + 1) n, j := by
  induction n with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    simp
  | succ m ih =>
    rcases eq_or_lt_of_le han with rfl | hlt
    · have hempty : Finset.Icc (m + 1 + 1) (m + 1) = ∅ := by
        ext x; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      rw [hempty, Finset.prod_empty, mul_one]
    · have ham : a ≤ m := by omega
      have hIcc : Finset.Icc (a + 1) (m + 1) = insert (m + 1) (Finset.Icc (a + 1) m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : m + 1 ∉ Finset.Icc (a + 1) m := by simp
      rw [Nat.factorial_succ, ih ham, hIcc, Finset.prod_insert hnot]
      ring

private lemma dvd_term_of_ge_two {M n d e : ℕ} (hM : 0 < M) (hn : 2 * M + 4 ≤ n)
    (hde : d * e = n) (hd : 2 ≤ d) (he : 2 ≤ e) :
    M ∣ term 2 3 n (d, e) := by
  have hsum_le : 2 * (d + e) ≤ n + 4 := by
    have h0 : 0 ≤ (d - 2) * (e - 2) := Nat.zero_le _
    have h1 : (d - 2) * (e - 2) + 2 * d + 2 * e = d * e + 4 := by
      zify [hd, he]; ring
    omega
  have hgap : d + e + M ≤ n := by omega
  have hde_le : d + e ≤ n := by omega
  have hfac_eq : n.factorial =
      (d.factorial * e.factorial) * ((d + e).choose d * ∏ j ∈ Finset.Icc (d + e + 1) n, j) := by
    rw [factorial_eq_mul_prod_Icc (d + e) n hde_le]
    have hch : (d + e).choose d * d.factorial * e.factorial = (d + e).factorial := by
      have := Nat.choose_mul_factorial_mul_factorial (show d ≤ d + e by omega)
      simpa [Nat.add_sub_cancel_left] using this
    rw [← hch]
    ring
  have hdvd_fac : d.factorial * e.factorial ∣ n.factorial :=
    ⟨(d + e).choose d * ∏ j ∈ Finset.Icc (d + e + 1) n, j, hfac_eq⟩
  have hdiv_eq : n.factorial / (d.factorial * e.factorial) =
      (d + e).choose d * ∏ j ∈ Finset.Icc (d + e + 1) n, j := by
    rw [hfac_eq, Nat.mul_div_cancel_left _ (Nat.mul_pos (Nat.factorial_pos d) (Nat.factorial_pos e))]
  have hterm_eq : term 2 3 n (d, e) =
      2 ^ d * 3 ^ e * ((d + e).choose d * ∏ j ∈ Finset.Icc (d + e + 1) n, j) := by
    unfold term
    rw [Nat.mul_div_assoc _ hdvd_fac, hdiv_eq]
  -- Pick a multiple of M in [d + e + 1, n]
  let j₀ : ℕ := ((d + e) / M + 1) * M
  have hj₀_mem : j₀ ∈ Finset.Icc (d + e + 1) n := by
    simp only [Finset.mem_Icc, j₀]
    have hdm := Nat.div_add_mod (d + e) M
    have hmlt := Nat.mod_lt (d + e) hM
    have hmul : ((d + e) / M + 1) * M = M * ((d + e) / M) + M := by ring
    omega
  have hM_dvd_j₀ : M ∣ j₀ := dvd_mul_left M _
  have hM_dvd_prod : M ∣ ∏ j ∈ Finset.Icc (d + e + 1) n, j :=
    dvd_trans hM_dvd_j₀ (Finset.dvd_prod_of_mem _ hj₀_mem)
  rw [hterm_eq]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hM_dvd_prod _) _

private lemma seq_modEq_two_three {M n : ℕ} (hM : 0 < M) (hn : 2 * M + 4 ≤ n) :
    seq 2 3 n ≡ 2 * 3 ^ n + 3 * 2 ^ n [MOD M] := by
  have hn0 : n ≠ 0 := by omega
  have hn2 : 2 ≤ n := by omega
  unfold seq
  rw [if_neg hn0]
  have h1n : (1, n) ∈ n.divisorsAntidiagonal := by
    rw [Nat.mem_divisorsAntidiagonal]; exact ⟨by omega, hn0⟩
  have hn1 : (n, 1) ∈ n.divisorsAntidiagonal := by
    rw [Nat.mem_divisorsAntidiagonal]; exact ⟨by omega, hn0⟩
  have hne : (1, n) ≠ (n, 1) := by intro h; have := congrArg Prod.fst h; dsimp at this; omega
  let rest := (n.divisorsAntidiagonal.erase (1, n)).erase (n, 1)
  have hsum_split : ∑ de ∈ n.divisorsAntidiagonal, term 2 3 n de =
      term 2 3 n (1, n) + term 2 3 n (n, 1) + ∑ de ∈ rest, term 2 3 n de := by
    have h1 := Finset.add_sum_erase n.divisorsAntidiagonal (term 2 3 n) h1n
    have hn1_in : (n, 1) ∈ n.divisorsAntidiagonal.erase (1, n) :=
      Finset.mem_erase.mpr ⟨hne.symm, hn1⟩
    have h2 := Finset.add_sum_erase (n.divisorsAntidiagonal.erase (1, n)) (term 2 3 n) hn1_in
    dsimp only [rest]
    omega
  have ht1 : term 2 3 n (1, n) = 2 * 3 ^ n := by
    unfold term
    simp only [pow_one, Nat.factorial_one, one_mul]
    exact Nat.mul_div_cancel _ (Nat.factorial_pos n)
  have ht2 : term 2 3 n (n, 1) = 3 * 2 ^ n := by
    unfold term
    simp only [pow_one, Nat.factorial_one, mul_one]
    rw [Nat.mul_div_cancel _ (Nat.factorial_pos n), mul_comm]
  have hrest_dvd : M ∣ ∑ de ∈ rest, term 2 3 n de := by
    refine Finset.dvd_sum fun de hde => ?_
    simp only [rest, Finset.mem_erase, Nat.mem_divisorsAntidiagonal] at hde
    obtain ⟨hne1, hne2, hmul, _⟩ := hde
    have hd_pos : 1 ≤ de.1 := by
      by_contra h0
      have hd0 : de.1 = 0 := by omega
      rw [hd0, zero_mul] at hmul
      omega
    have he_pos : 1 ≤ de.2 := by
      by_contra h0
      have he0 : de.2 = 0 := by omega
      rw [he0, mul_zero] at hmul
      omega
    have hd2 : 2 ≤ de.1 := by
      by_contra hlt
      have hd1 : de.1 = 1 := by omega
      have he_eq : de.2 = n := by rw [hd1, one_mul] at hmul; exact hmul
      exact hne2 (Prod.ext hd1 he_eq)
    have he2 : 2 ≤ de.2 := by
      by_contra hlt
      have he1 : de.2 = 1 := by omega
      have hd_eq : de.1 = n := by rw [he1, mul_one] at hmul; exact hmul
      exact hne1 (Prod.ext hd_eq he1)
    exact dvd_term_of_ge_two hM hn hmul hd2 he2
  rw [hsum_split, ht1, ht2]
  obtain ⟨q, hq⟩ := hrest_dvd
  rw [hq]
  exact Nat.ModEq.add_left _ (by rw [Nat.modEq_zero_iff_dvd]; exact dvd_mul_right M q) |>.trans
    (by simp [Nat.ModEq])

private lemma pow_add_totient_modEq (b M n : ℕ) (hM : 0 < M) (hn : M ≤ n) :
    b ^ (n + M.totient) ≡ b ^ n [MOD M] := by
  let diff : ℤ := (b : ℤ) ^ (n + M.totient) - (b : ℤ) ^ n
  have hpp : ∀ p ∈ M.primeFactors, ((p ^ (M.factorization p) : ℕ) : ℤ) ∣ diff := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpe_dvd : p ^ (M.factorization p) ∣ M := Nat.ordProj_dvd M p
    have he_le : M.factorization p ≤ n := by
      have h1 : p ^ (M.factorization p) ≤ M := Nat.le_of_dvd hM hpe_dvd
      have h2 : M.factorization p < p ^ (M.factorization p) := Nat.lt_pow_self hprime.one_lt
      omega
    have hmod : b ^ (n + M.totient) ≡ b ^ n [MOD p ^ (M.factorization p)] := by
      by_cases hpb : p ∣ b
      · have hd1 : p ^ (M.factorization p) ∣ b ^ n :=
          dvd_trans (pow_dvd_pow_of_dvd hpb _) (pow_dvd_pow b he_le)
        have hd2 : p ^ (M.factorization p) ∣ b ^ (n + M.totient) :=
          dvd_trans (pow_dvd_pow_of_dvd hpb _) (pow_dvd_pow b (by omega))
        exact (Nat.modEq_zero_iff_dvd.mpr hd2).trans (Nat.modEq_zero_iff_dvd.mpr hd1).symm
      · have hcop : Nat.Coprime b (p ^ (M.factorization p)) :=
          (hprime.coprime_iff_not_dvd.mpr hpb).symm.pow_right _
        have heuler : b ^ (p ^ (M.factorization p)).totient ≡ 1 [MOD p ^ (M.factorization p)] :=
          Nat.ModEq.pow_totient hcop
        obtain ⟨q, hq⟩ := Nat.totient_dvd_of_dvd hpe_dvd
        have hphi : b ^ M.totient ≡ 1 [MOD p ^ (M.factorization p)] := by
          rw [hq, pow_mul]
          simpa using heuler.pow q
        rw [pow_add]
        simpa using (Nat.ModEq.refl (b ^ n)).mul hphi
    have := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod.symm)
    simpa [diff] using this
  have hprod : (∏ p ∈ M.primeFactors, ((p ^ (M.factorization p) : ℕ) : ℤ)) ∣ diff := by
    refine Finset.prod_dvd_of_coprime ?_ hpp
    intro p hp q hq hpq
    exact Nat.isCoprime_iff_coprime.mpr
      (((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq).pow _ _)
  have hM_prod : (∏ p ∈ M.primeFactors, p ^ M.factorization p) = M := by
    rw [← Nat.support_factorization]
    exact Nat.prod_factorization_pow_eq_self (by omega : M ≠ 0)
  have hint : (M : ℤ) ∣ diff := by
    rw [← hM_prod, Nat.cast_prod]
    exact hprod
  exact (Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr hint)).symm

theorem main_proof : ∀ M : ℕ, 0 < M → ∃ N : ℕ, ∀ n ≥ N,
    seq 2 3 (n + M.totient) ≡ seq 2 3 n [MOD M] := by
  intro M hM
  refine ⟨2 * M + 4, fun n hn => ?_⟩
  have h1 := seq_modEq_two_three hM (by omega : 2 * M + 4 ≤ n + M.totient)
  have h2 := seq_modEq_two_three hM hn
  have h3 := pow_add_totient_modEq 3 M n hM (by omega)
  have h2pow := pow_add_totient_modEq 2 M n hM (by omega)
  have hcomb : 2 * 3 ^ (n + M.totient) + 3 * 2 ^ (n + M.totient) ≡
      2 * 3 ^ n + 3 * 2 ^ n [MOD M] :=
    (h3.mul_left 2).add (h2pow.mul_left 3)
  exact h1.trans (hcomb.trans h2.symm)

end OMA.S_oeis_a258903_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a258903.main :=
  OMA.S_oeis_a258903_Proof.main_proof
