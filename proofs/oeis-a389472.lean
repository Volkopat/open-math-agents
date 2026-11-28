import OMAStatements.S_oeis_a389472

-- Problem: A389472: G.f. satisfies A(x) = A(x^2 + x^3)/x^2 - 1.
-- Upstream: formal-conjectures statements/oeis-a389472.lean:0 (declaration OMA.S_oeis_a389472.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: strong induction with Lucas' theorem. For N = n + 3, a(N) is a sum of terms
-- a(k) * C(k, j) with j = n + 5 - 2k. If N is odd, j is odd, so C(k, j) is even for even k
-- (Lucas mod 2), odd k >= 3 have a(k) even by induction, and k = 1 gives C(1, j) = 0.
-- If N = 2 mod 3, then j = 1 + k mod 3, so C(k, j) = 0 mod 3 when k = 0 or 1 mod 3 (Lucas
-- mod 3), k = 2 mod 3 with k >= 5 is covered by induction, and k = 2 gives C(2, j) = 0.

open OMA.S_oeis_a389472 in
theorem OMA.solution : type_of% @OMA.S_oeis_a389472.main := by
  have hrec : ∀ n : ℕ, a (n + 3) = ∑ k : Fin (n + 3),
      if 2 * (k : ℕ) ≤ n + 5 then a k * (k : ℕ).choose (n + 5 - 2 * (k : ℕ)) else 0 := by
    intro n
    rw [a]
  have L2 : ∀ k j : ℕ, k % 2 = 0 → j % 2 = 1 → 2 ∣ k.choose j := by
    intro k j hk hj
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := k) (k := j) (p := 2)
    rw [hk, hj] at h
    have h0 : Nat.choose 0 1 = 0 := by decide
    rw [h0, zero_mul] at h
    exact (Nat.modEq_zero_iff_dvd).mp h
  have L3 : ∀ k j : ℕ, (k % 3 = 0 ∧ j % 3 = 1) ∨ (k % 3 = 1 ∧ j % 3 = 2) →
      3 ∣ k.choose j := by
    intro k j hkj
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := k) (k := j) (p := 3)
    have hz : (k % 3).choose (j % 3) = 0 := by
      rcases hkj with ⟨hk, hj⟩ | ⟨hk, hj⟩
      · calc (k % 3).choose (j % 3) = Nat.choose 0 1 := by rw [hk, hj]
          _ = 0 := by decide
      · calc (k % 3).choose (j % 3) = Nat.choose 1 2 := by rw [hk, hj]
          _ = 0 := by decide
    rw [hz, zero_mul] at h
    exact (Nat.modEq_zero_iff_dvd).mp h
  have P1 : ∀ N : ℕ, 3 ≤ N → N % 2 = 1 → 2 ∣ a N := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro hN hodd
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
      rw [hrec n]
      apply Finset.dvd_sum
      intro k _
      have hkl := k.isLt
      split_ifs with hk
      · by_cases he : (k : ℕ) % 2 = 0
        · exact Dvd.dvd.mul_left (L2 _ _ he (by omega)) _
        · by_cases h1 : (k : ℕ) = 1
          · rw [h1, Nat.choose_eq_zero_of_lt (by omega : 1 < n + 5 - 2 * 1), mul_zero]
            exact dvd_zero 2
          · exact Dvd.dvd.mul_right (ih k (by omega) (by omega) (by omega)) _
      · exact dvd_zero 2
  have P2 : ∀ N : ℕ, 5 ≤ N → N % 3 = 2 → 3 ∣ a N := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro hN hmod
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
      rw [hrec n]
      apply Finset.dvd_sum
      intro k _
      have hkl := k.isLt
      split_ifs with hk
      · by_cases h0 : (k : ℕ) % 3 = 0
        · exact Dvd.dvd.mul_left (L3 _ _ (Or.inl ⟨h0, by omega⟩)) _
        · by_cases h1 : (k : ℕ) % 3 = 1
          · exact Dvd.dvd.mul_left (L3 _ _ (Or.inr ⟨h1, by omega⟩)) _
          · by_cases h2 : (k : ℕ) = 2
            · rw [h2, Nat.choose_eq_zero_of_lt (by omega : 2 < n + 5 - 2 * 2), mul_zero]
              exact dvd_zero 3
            · exact Dvd.dvd.mul_right (ih k (by omega) (by omega) (by omega)) _
      · exact dvd_zero 3
  exact ⟨fun n hn => P1 (2 * n - 1) (by omega) (by omega),
    fun n hn => P2 (3 * n - 1) (by omega) (by omega)⟩
