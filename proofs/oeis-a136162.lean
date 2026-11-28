import OMAStatements.S_oeis_a136162

-- Problem: A136162: List of prime quadruplets {p, p+2, p+6, p+8}.
-- Upstream: formal-conjectures statements/oeis-a136162.lean:0 (declaration OMA.S_oeis_a136162.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: a prime divisible by 3 is 3. For twin primes q, q+2 with q > 3 we have q = 3t+2, so
-- Q-2 = q*(q+2)-2 = 3*(3t^2+6t+2) > 3 is not prime. For Q = q*r with q < r primes and 3 not
-- dividing Q we have Q >= 10, and one of Q-4, Q-2 is a multiple of 3 larger than 3. If 3 divides
-- Q then q = 3, or r = 3 and q = 2, where Q-2 = 4. For q = 3 the next prime is 5, Q = 15.

namespace H01A136162

open OMA.S_oeis_a136162

theorem quad11 : IsPrimeQuad 11 := by
  unfold IsPrimeQuad
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem three_dvd_prime {n : ℕ} (hn : n.Prime) (h : 3 ∣ n) : n = 3 :=
  ((Nat.Prime.eq_one_or_self_of_dvd hn 3 h).resolve_left (by norm_num)).symm

theorem part1 (q : ℕ) (hq : q.Prime) (hq2 : (q + 2).Prime) :
    IsPrimeQuad (q * (q + 2) - 4) ↔ q = 3 := by
  constructor
  · intro h
    unfold IsPrimeQuad at h
    obtain ⟨-, h2, -, -⟩ := h
    by_contra hne
    have hge : 2 ≤ q := hq.two_le
    have hq3 : q % 3 = 2 := by
      have h0 : q % 3 ≠ 0 := by
        intro h
        exact hne (three_dvd_prime hq (Nat.dvd_of_mod_eq_zero h))
      have h1 : q % 3 ≠ 1 := by
        intro h
        have h' := three_dvd_prime hq2 (by omega)
        omega
      omega
    obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
    have e : (3 * t + 2) * (3 * t + 2 + 2) - 4 + 2 = 3 * (3 * t * t + 6 * t + 2) := by
      have e1 : (3 * t + 2) * (3 * t + 2 + 2) = 3 * (3 * t * t + 6 * t + 2) + 2 := by ring
      omega
    rw [e] at h2
    have h3 := three_dvd_prime h2 (dvd_mul_right 3 _)
    omega
  · rintro rfl
    rw [show 3 * (3 + 2) - 4 = 11 by norm_num]
    exact quad11

theorem part2 (q r : ℕ) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hgap : ∀ m : ℕ, q < m → m < r → ¬ m.Prime) :
    IsPrimeQuad (q * r - 4) ↔ q = 3 := by
  constructor
  · intro h
    unfold IsPrimeQuad at h
    obtain ⟨h1, h2, -, -⟩ := h
    by_contra hne
    have hge : 2 ≤ q := hq.two_le
    by_cases h3 : 3 ∣ q * r
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
      · exact hne (three_dvd_prime hq h)
      · have hr3 := three_dvd_prime hr h
        have hq2 : q = 2 := by omega
        subst hr3
        subst hq2
        norm_num at h2
    · have hr3 : r ≠ 3 := by
        rintro rfl
        exact h3 (dvd_mul_left 3 q)
      have hr4 : r ≠ 4 := by
        rintro rfl
        norm_num at hr
      have hr5 : 5 ≤ r := by omega
      have hQ : 2 * 5 ≤ q * r := Nat.mul_le_mul hge hr5
      have key : 3 ∣ q * r - 4 ∨ 3 ∣ q * r - 4 + 2 := by omega
      rcases key with k | k
      · have h5 := three_dvd_prime h1 k
        omega
      · have h5 := three_dvd_prime h2 k
        omega
  · rintro rfl
    have hr5 : r = 5 := by
      by_contra hne
      rcases Nat.lt_or_ge r 5 with h | h
      · have h4 : r = 4 := by omega
        rw [h4] at hr
        norm_num at hr
      · exact hgap 5 (by norm_num) (by omega) (by norm_num)
    subst hr5
    rw [show 3 * 5 - 4 = 11 by norm_num]
    exact quad11

end H01A136162

open OMA.S_oeis_a136162 H01A136162 in
theorem OMA.solution : type_of% @OMA.S_oeis_a136162.main := by
  exact ⟨fun q hq hq2 => part1 q hq hq2,
    fun q r hq hr hqr hgap => part2 q r hq hr hqr hgap⟩
