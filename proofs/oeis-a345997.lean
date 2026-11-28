import OMAStatements.S_oeis_a345997

-- Disproof of the conjecture about A344005 (the one A345997 disproves), at n = 60, the first
-- term of A345997. A344005(60) = 15 (60 divides 15 * 16 = 240, and no smaller m works), so
-- gcd(60, 15) = 15 and gcd(60, 16) = 4, while A051119(60) = 60 / 5 = 12.

open OMA.S_oeis_a345997 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a345997.main) := by
  intro h
  have hm : a344005 60 = 15 := by
    unfold a344005
    apply le_antisymm
    · exact Nat.sInf_le (show (15 : ℕ) ∈ {m : ℕ | 0 < m ∧ 60 ∣ m * (m + 1)} from ⟨by norm_num, by norm_num⟩)
    · apply le_csInf (show Set.Nonempty {m : ℕ | 0 < m ∧ 60 ∣ m * (m + 1)} from
        ⟨15, by norm_num, by norm_num⟩)
      rintro m ⟨hm0, hdvd⟩
      by_contra hlt
      push_neg at hlt
      interval_cases m <;> norm_num at hdvd
  have key : ∀ e : ℕ, 60 / 5 ^ e ≠ 15 ∧ 60 / 5 ^ e ≠ 4 := by
    intro e
    rcases e with _ | _ | _ | e
    · norm_num
    · norm_num
    · norm_num
    · have h125 : 60 < 5 ^ (e + 3) :=
        calc 60 < 5 ^ 3 := by norm_num
          _ ≤ 5 ^ (e + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.div_eq_of_lt h125]
      norm_num
  have hg : gpf 60 = 5 := by
    unfold gpf
    apply le_antisymm
    · apply Finset.sup_le
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      obtain ⟨hpp, hpd, -⟩ := hp
      have hp60 : p ≤ 60 := Nat.le_of_dvd (by norm_num) hpd
      interval_cases p <;> (revert hpp hpd; norm_num)
    · have h5 : (5 : ℕ) ∈ (60 : ℕ).primeFactors := by
        rw [Nat.mem_primeFactors]; norm_num
      exact Finset.le_sup (f := id) h5
  have ha : a051119 60 = 60 / 5 ^ (Nat.factorization 60 5) := by
    unfold a051119
    rw [hg]
  have k := key (Nat.factorization 60 5)
  rcases h 60 (by norm_num) with h1 | h1
  · rw [hm, ha] at h1
    norm_num at h1
    exact k.1 h1.symm
  · rw [hm, ha] at h1
    norm_num at h1
    exact k.2 h1.symm
