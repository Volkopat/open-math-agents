import OMAStatements.S_oeis_a111018

-- Problem: A111018: Indices of Catalan numbers that are divisible by 3.
-- Upstream: formal-conjectures statements/oeis-a111018.lean:0 (declaration OMA.S_oeis_a111018.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: by Lucas's theorem mod 3, choose(2m, m) is divisible by 3 when m has a ternary
-- digit 2 (L1, by induction on the digits: the last digit 2 gives a factor choose(1, 2) = 0,
-- a last digit 0 or 1 reduces m to m / 3). If n mod 3 is 0 or 1, then (n+1) catalan(n) =
-- choose(2n, n) and 3 does not divide n + 1. If n = 3m + 2, then n + 1 = 3(m+1), so m + 1 has a
-- digit 2; (2n+1) catalan(n) = choose(2n+1, n+1), which is choose(2m+1, m+1) mod 3 by Lucas, and
-- 2 choose(2m+1, m+1) = choose(2m+2, m+1) is divisible by 3 by L1; 3 does not divide 2n + 1.

namespace P1A111018

theorem L1 : ∀ m : ℕ, 2 ∈ Nat.digits 3 m → 3 ∣ Nat.choose (2 * m) m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0] at hm
      simp at hm
    · have hF : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [Nat.digits_def' (b := 3) (by norm_num) hpos] at hm
      have hL := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * m) (k := m) (p := 3)
      have hdiv : 3 ∣ Nat.choose (2 * m % 3) (m % 3) * Nat.choose (2 * m / 3) (m / 3) := by
        by_cases hr : m % 3 = 2
        · have hz : Nat.choose (2 * m % 3) (m % 3) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          rw [hz, zero_mul]
          exact dvd_zero 3
        · rcases List.mem_cons.mp hm with h2 | h2
          · omega
          · have hlt : m / 3 < m := Nat.div_lt_self hpos (by norm_num)
            have ih' := ih (m / 3) hlt h2
            have e2 : 2 * m / 3 = 2 * (m / 3) := by omega
            rw [e2]
            exact Dvd.dvd.mul_left ih' _
      exact (Nat.modEq_zero_iff_dvd).1 (hL.trans ((Nat.modEq_zero_iff_dvd).2 hdiv))

theorem key : ∀ n : ℕ, 2 ∈ Nat.digits 3 n → 2 ∈ Nat.digits 3 (n + 1) → 3 ∣ catalan n := by
  intro n hn hn1
  have hcat := succ_mul_catalan_eq_centralBinom n
  rw [Nat.centralBinom_eq_two_mul_choose] at hcat
  by_cases hr : n % 3 = 2
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 2 := ⟨n / 3, by omega⟩
    have hF : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hm1 : 2 ∈ Nat.digits 3 (m + 1) := by
      rw [show 3 * m + 2 + 1 = 3 * (m + 1) by ring,
        Nat.digits_def' (b := 3) (by norm_num) (show 0 < 3 * (m + 1) by omega)] at hn1
      rw [Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)] at hn1
      rcases List.mem_cons.mp hn1 with h | h
      · omega
      · exact h
    have h1 := L1 (m + 1) hm1
    have hP : Nat.choose (2 * (m + 1)) (m + 1) = 2 * Nat.choose (2 * m + 1) (m + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.choose_succ_succ' (2 * m + 1) m,
        ← Nat.choose_symm_half m]
      ring
    have h2 : 3 ∣ Nat.choose (2 * m + 1) (m + 1) := by
      rw [hP] at h1
      omega
    have hL := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := 2 * (3 * m + 2) + 1) (k := 3 * m + 2 + 1) (p := 3)
    have ea : (2 * (3 * m + 2) + 1) % 3 = 2 := by omega
    have eb : (3 * m + 2 + 1) % 3 = 0 := by omega
    have ec : (2 * (3 * m + 2) + 1) / 3 = 2 * m + 1 := by omega
    have ed : (3 * m + 2 + 1) / 3 = m + 1 := by omega
    rw [ea, eb, ec, ed] at hL
    have h3 : 3 ∣ Nat.choose (2 * (3 * m + 2) + 1) (3 * m + 2 + 1) :=
      (Nat.modEq_zero_iff_dvd).1 (hL.trans ((Nat.modEq_zero_iff_dvd).2 (Dvd.dvd.mul_left h2 _)))
    have hrel : (2 * (3 * m + 2) + 1) * catalan (3 * m + 2) =
        Nat.choose (2 * (3 * m + 2) + 1) (3 * m + 2 + 1) := by
      have hA := Nat.add_one_mul_choose_eq (2 * (3 * m + 2)) (3 * m + 2)
      rw [← hcat] at hA
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 3 * m + 2 + 1 by omega)
      calc (3 * m + 2 + 1) * ((2 * (3 * m + 2) + 1) * catalan (3 * m + 2))
          = (2 * (3 * m + 2) + 1) * ((3 * m + 2 + 1) * catalan (3 * m + 2)) := by ring
        _ = Nat.choose (2 * (3 * m + 2) + 1) (3 * m + 2 + 1) * (3 * m + 2 + 1) := hA
        _ = (3 * m + 2 + 1) * Nat.choose (2 * (3 * m + 2) + 1) (3 * m + 2 + 1) := by ring
    have h4 : 3 ∣ (2 * (3 * m + 2) + 1) * catalan (3 * m + 2) := by
      rw [hrel]
      exact h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h4 with h5 | h5
    · omega
    · exact h5
  · have h1 := L1 n hn
    rw [← hcat] at h1
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h1 with h5 | h5
    · omega
    · exact h5

end P1A111018

theorem OMA.solution : type_of% @OMA.S_oeis_a111018.main := by
  refine ⟨fun n hn hn1 => P1A111018.key n hn hn1, fun n hn hn1 => P1A111018.key n ?_ ?_⟩
  · by_contra h
    exact hn h
  · by_contra h
    exact hn1 h
