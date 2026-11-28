import OMAReductions.R_oeis_a306238_R1

/-!
# Primality of the least odd quotient index in the range `k ≤ 2 * n`

Source: The definition and primality problem are from OEIS A306238
(https://oeis.org/A306238). Formal proof credit: @grp06.
-/

open scoped BigOperators

private theorem prod_positive_factors_dvd_factorial (n : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Icc 1 n) : (∏ i ∈ s, i) ∣ n.factorial := by
  have hfactorial : (∏ i ∈ Finset.Icc 1 n, i) = n.factorial := by
    clear hs
    induction n with
    | zero =>
      rw [Finset.Icc_eq_empty (by decide : ¬ (1 : ℕ) ≤ 0), Finset.prod_empty,
        Nat.factorial_zero]
    | succ n ih =>
      rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), ih,
        Nat.factorial_succ, Nat.mul_comm]
  rw [← hfactorial]
  exact Finset.prod_dvd_prod_of_subset s (Finset.Icc 1 n) (fun i => i) hs

private theorem twice_composite_dvd_factorial {n k : ℕ}
    (hn : 6 ≤ n) (hk : 2 ≤ k) (hbound : k ≤ 2 * n) (hnp : ¬ k.Prime) :
    2 * k ∣ n.factorial := by
  obtain ⟨a, b, ha, hb, hprod⟩ := (Nat.not_prime_iff_exists_mul_eq hk).mp hnp
  have ha2 : 2 ≤ a := by
    by_contra h
    have haSmall : a = 0 ∨ a = 1 := by omega
    rcases haSmall with rfl | rfl <;> simp at hprod <;> omega
  have hb2 : 2 ≤ b := by
    by_contra h
    have hbSmall : b = 0 ∨ b = 1 := by omega
    rcases hbSmall with rfl | rfl <;> simp at hprod <;> omega
  subst k
  have han : a ≤ n := by
    have h := Nat.mul_le_mul_left a hb2
    omega
  have hbn : b ≤ n := by
    have h := Nat.mul_le_mul_right b ha2
    omega
  by_cases hab : a = b
  · subst b
    have hdouble : 2 * a ≤ n := by
      by_cases hlarge : 4 ≤ a
      · have h := Nat.mul_le_mul_right a hlarge
        omega
      · omega
    have hpair := prod_positive_factors_dvd_factorial n {a, 2 * a} (by
      intro x hx
      rw [Finset.mem_Icc]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> omega)
    have hne : a ≠ 2 * a := by omega
    simp only [Finset.prod_insert (show a ∉ ({2 * a} : Finset ℕ) by simpa using hne),
      Finset.prod_singleton] at hpair
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpair
  · obtain ⟨c, hc1, hcn, hca, hcb, heven⟩ :
        ∃ c : ℕ, 1 ≤ c ∧ c ≤ n ∧ c ≠ a ∧ c ≠ b ∧ 2 ∣ c := by
      by_cases htwo : 2 ≠ a ∧ 2 ≠ b
      · exact ⟨2, by decide, by omega, htwo.1, htwo.2, by decide⟩
      by_cases hfour : 4 ≠ a ∧ 4 ≠ b
      · exact ⟨4, by decide, by omega, hfour.1, hfour.2, by decide⟩
      exact ⟨6, by decide, hn, by omega, by omega, by decide⟩
    have htriple := prod_positive_factors_dvd_factorial n {c, a, b} (by
      intro x hx
      rw [Finset.mem_Icc]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> omega)
    have hcNotMem : c ∉ ({a, b} : Finset ℕ) := by simp [hca, hcb]
    have haNotMem : a ∉ ({b} : Finset ℕ) := by simpa using hab
    simp only [Finset.prod_insert hcNotMem, Finset.prod_insert haNotMem,
      Finset.prod_singleton] at htriple
    exact dvd_trans (by simpa only [Nat.mul_comm] using mul_dvd_mul_left (a * b) heven)
      htriple

theorem OMA.solution : OMA.R_oeis_a306238_R1.H1 := by
  intro n k hn hk hbound
  obtain ⟨hkpos, hodd, hleast⟩ := hk
  by_cases hlarge : 6 ≤ n
  · have htwo : 2 ≤ k := by
      by_contra h
      have hk1 : k = 1 := by omega
      subst k
      have hdvd : 2 ∣ n.factorial := Nat.dvd_factorial (by decide) (by omega)
      have heven : Even n.factorial := even_iff_two_dvd.mpr hdvd
      exact Nat.not_odd_iff_even.mpr heven (by simpa only [Nat.div_one] using hodd)
    by_contra hnp
    have hdvd := twice_composite_dvd_factorial hlarge htwo hbound hnp
    have hkDvd : k ∣ n.factorial := dvd_trans (dvd_mul_left k 2) hdvd
    have htwoDvd : 2 ∣ n.factorial / k :=
      (Nat.dvd_div_iff_mul_dvd hkDvd).mpr (by simpa only [Nat.mul_comm] using hdvd)
    exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr htwoDvd) hodd
  · have hnLower : 2 ≤ n := by omega
    have hnUpper : n < 6 := by omega
    interval_cases n using hnLower, hnUpper
    · have hkUpper : k ≤ 2 := hleast 2 (by decide) (by decide)
      interval_cases k <;> first | decide | (exfalso; revert hodd; decide)
    · have hkUpper : k ≤ 2 := hleast 2 (by decide) (by decide)
      interval_cases k <;> first | decide | (exfalso; revert hodd; decide)
    · have hkUpper : k ≤ 7 := hleast 7 (by decide) (by decide)
      interval_cases k <;> first | decide | (exfalso; revert hodd; decide)
    · have hkUpper : k ≤ 7 := hleast 7 (by decide) (by decide)
      interval_cases k <;> first | decide | (exfalso; revert hodd; decide)
