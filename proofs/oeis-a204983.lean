import OMAStatements.S_oeis_a204983

/-! Following @ceejcake (#27597), retain the minimal-pair and period argument.
Use Mathlib's complementary prime part for the positivity, oddness, and
factorization of the odd part. -/

namespace ProofA204983

open OMA.S_oeis_a204983

private lemma oddPart_pos_and_odd {n : ℕ} (hn : 1 ≤ n) :
    0 < oddPart n ∧ Odd (oddPart n) ∧ n = 2 ^ padicValNat 2 n * oddPart n := by
  have hne : n ≠ 0 := by omega
  simp only [oddPart, ← Nat.factorization_def n Nat.prime_two]
  refine ⟨Nat.ordCompl_pos 2 hne, ?_, (Nat.ordProj_mul_ordCompl_eq_self n 2).symm⟩
  exact Nat.not_even_iff_odd.mp (by
    simpa only [even_iff_two_dvd] using Nat.not_dvd_ordCompl Nat.prime_two hne)

private lemma exists_period {m : ℕ} (hm_pos : 0 < m) (hm_odd : Odd m) :
    ∃ d : ℕ, 0 < d ∧ m ∣ 2 ^ d - 1 := by
  by_cases hm1 : m = 1
  · exact ⟨1, by omega, by simp [hm1]⟩
  · have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm_odd
    refine ⟨Nat.totient m, Nat.totient_pos.mpr hm_pos, ?_⟩
    have heuler : 2 ^ Nat.totient m ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
    have hge : 1 ≤ 2 ^ Nat.totient m := Nat.one_le_pow _ _ (by omega)
    exact (Nat.modEq_iff_dvd' hge).mp heuler.symm

private lemma a007733_mem {n : ℕ} (hn : 1 ≤ n) :
    0 < a007733 n ∧ oddPart n ∣ 2 ^ a007733 n - 1 := by
  have ⟨hpos, hodd, _⟩ := oddPart_pos_and_odd hn
  have hne : {d : ℕ | 0 < d ∧ oddPart n ∣ 2 ^ d - 1}.Nonempty := exists_period hpos hodd
  exact Nat.sInf_mem hne

private lemma a007733_le {n d : ℕ} (hd : 0 < d) (hdvd : oddPart n ∣ 2 ^ d - 1) :
    a007733 n ≤ d :=
  Nat.sInf_le ⟨hd, hdvd⟩

theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = 2 ^ padicValNat 2 n * (2 ^ a007733 n - 1) := by
  intro n hn
  set v := padicValNat 2 n
  set m := oddPart n
  set d := a007733 n
  have ⟨hm_pos, hm_odd, hn_eq⟩ := oddPart_pos_and_odd hn
  have ⟨hd_pos, hd_dvd⟩ := a007733_mem hn
  have hmem : 2 ^ v * (2 ^ d - 1) ∈ {x : ℕ | ∃ j k : ℕ, j < k ∧ x = 2 ^ k - 2 ^ j ∧ n ∣ x} := by
    refine ⟨v, v + d, by omega, ?_, ?_⟩
    · rw [pow_add, Nat.mul_sub_left_distrib, mul_one]
    · rw [hn_eq]
      exact mul_dvd_mul_left (2 ^ v) hd_dvd
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · refine le_csInf ⟨_, hmem⟩ ?_
    rintro x ⟨j, k, hjk, rfl, hndvd⟩
    have hfac : 2 ^ k - 2 ^ j = 2 ^ j * (2 ^ (k - j) - 1) := by
      have hk : k = j + (k - j) := by omega
      conv_lhs => rw [hk, pow_add]
      rw [Nat.mul_sub_left_distrib, mul_one]
    rw [hfac] at hndvd ⊢
    -- 1. Show v ≤ j (since 2^v | 2^j * (2^(k-j) - 1) and 2^(k-j) - 1 is odd)
    have hodd_pow : Odd (2 ^ (k - j) - 1) := by
      have h2 : 2 ∣ 2 ^ (k - j) := dvd_pow_self 2 (by omega)
      have hpos : 1 ≤ 2 ^ (k - j) := Nat.one_le_pow _ _ (by omega)
      rcases h2 with ⟨t, ht⟩
      exact ⟨t - 1, by omega⟩
    have h2v_dvd : 2 ^ v ∣ 2 ^ j * (2 ^ (k - j) - 1) :=
      dvd_trans (by rw [hn_eq]; exact dvd_mul_right _ _) hndvd
    have hcop1 : Nat.Coprime (2 ^ v) (2 ^ (k - j) - 1) :=
      (Nat.coprime_two_left.mpr hodd_pow).pow_left v
    have h2v_dvd_2j : 2 ^ v ∣ 2 ^ j := hcop1.dvd_of_dvd_mul_right h2v_dvd
    have hv_le_j : v ≤ j := (Nat.pow_dvd_pow_iff_le_right (by omega)).mp h2v_dvd_2j
    -- 2. Show d ≤ k - j (since m | 2^j * (2^(k-j) - 1) and gcd(m, 2^j) = 1)
    have hm_dvd : m ∣ 2 ^ j * (2 ^ (k - j) - 1) :=
      dvd_trans (by rw [hn_eq]; exact dvd_mul_left _ _) hndvd
    have hcop2 : Nat.Coprime m (2 ^ j) :=
      (Nat.coprime_two_right.mpr hm_odd).pow_right j
    have hm_dvd_sub : m ∣ 2 ^ (k - j) - 1 := hcop2.dvd_of_dvd_mul_left hm_dvd
    have hd_le : d ≤ k - j := a007733_le (by omega) hm_dvd_sub
    -- 3. Combine inequalities: 2^v * (2^d - 1) ≤ 2^j * (2^(k-j) - 1)
    have h1 : 2 ^ v ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hv_le_j
    have h2 : 2 ^ d - 1 ≤ 2 ^ (k - j) - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) hd_le) 1
    exact Nat.mul_le_mul h1 h2

end ProofA204983

theorem OMA.solution : type_of% @OMA.S_oeis_a204983.main :=
  ProofA204983.main
