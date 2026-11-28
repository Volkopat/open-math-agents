import OMAStatements.S_oeis_a382074

-- Problem: A382074: a(n) is the number of solutions to phi(x) + phi(n-x) = phi(n) where 1 <= x <= floor(n/2).
-- Upstream: formal-conjectures statements/oeis-a382074.lean:0 (declaration OMA.S_oeis_a382074.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Disproof idea: the conjecture a(2*A065381(n)) = 0 for n > 1 fails. 3697 is a prime, and
-- 3697 - 2^k is composite for k = 0, ..., 11 (2^12 > 3697), so 3697 is a term of A065381; its
-- index is count + 1 > 1, where count (the number of terms below 3697) is positive since 2 is a
-- term. But a(2*3697) > 0: x = 959 is a solution, phi(959) + phi(6435) = 816 + 2880 = 3696 =
-- phi(7394), with 959 = 7*137, 6435 = 9*5*11*13 and 7394 = 2*3697.

namespace K01A382074

open OMA.S_oeis_a382074

theorem mem2 : IsA065381 2 := by
  refine ⟨Nat.prime_two, ?_⟩
  intro q k hq heq
  have h1 := hq.two_le
  have h2 : 0 < 2 ^ k := pow_pos (by norm_num) k
  omega

theorem mem3697 : IsA065381 3697 := by
  refine ⟨by norm_num, ?_⟩
  intro q k hq heq
  have hk : k < 12 := by
    by_contra hk
    have h12 : 2 ^ 12 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4096 : (2 : ℕ) ^ 12 = 4096 := by norm_num
    omega
  have hq' : q = 3697 - 2 ^ k := by omega
  subst hq'
  interval_cases k <;> norm_num at hq

theorem idx : ∃ n : ℕ, 1 < n ∧ A065381 n = 3697 := by
  classical
  refine ⟨Nat.count IsA065381 3697 + 1, ?_, ?_⟩
  · have h1 := Nat.count_strict_mono (p := IsA065381) mem2 (show 2 < 3697 by norm_num)
    omega
  · rw [A065381, Nat.add_sub_cancel]
    exact Nat.nth_count (p := IsA065381) mem3697

theorem phi959 : Nat.totient 959 = 816 := by
  have e : Nat.totient (7 * 137) = Nat.totient 7 * Nat.totient 137 :=
    Nat.totient_mul (by decide)
  have h7 : Nat.totient 7 = 6 := Nat.totient_prime (by norm_num)
  have h137 : Nat.totient 137 = 136 := Nat.totient_prime (by norm_num)
  have e2 : (7 * 137 : ℕ) = 959 := by norm_num
  rw [e2, h7, h137] at e
  omega

theorem phi143 : Nat.totient 143 = 120 := by
  have e : Nat.totient (11 * 13) = Nat.totient 11 * Nat.totient 13 :=
    Nat.totient_mul (by decide)
  have h11 : Nat.totient 11 = 10 := Nat.totient_prime (by norm_num)
  have h13 : Nat.totient 13 = 12 := Nat.totient_prime (by norm_num)
  have e2 : (11 * 13 : ℕ) = 143 := by norm_num
  rw [e2, h11, h13] at e
  omega

theorem phi715 : Nat.totient 715 = 480 := by
  have e : Nat.totient (5 * 143) = Nat.totient 5 * Nat.totient 143 :=
    Nat.totient_mul (by decide)
  have h5 : Nat.totient 5 = 4 := Nat.totient_prime (by norm_num)
  have e2 : (5 * 143 : ℕ) = 715 := by norm_num
  rw [e2, h5, phi143] at e
  omega

theorem phi6435 : Nat.totient 6435 = 2880 := by
  have e : Nat.totient (9 * 715) = Nat.totient 9 * Nat.totient 715 :=
    Nat.totient_mul (by decide)
  have h9 : Nat.totient 9 = 6 := by decide
  have e2 : (9 * 715 : ℕ) = 6435 := by norm_num
  rw [e2, h9, phi715] at e
  omega

theorem phi7394 : Nat.totient (2 * 3697) = 3696 := by
  have e : Nat.totient (2 * 3697) = Nat.totient 2 * Nat.totient 3697 :=
    Nat.totient_mul (by decide)
  have h2 : Nat.totient 2 = 1 := Nat.totient_prime Nat.prime_two
  have h3697 : Nat.totient 3697 = 3696 := Nat.totient_prime (by norm_num)
  rw [h2, h3697] at e
  omega

theorem a_pos : 0 < a (2 * 3697) := by
  unfold a
  apply Finset.card_pos.mpr
  refine ⟨959, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, ?_⟩⟩
  show Nat.totient 959 + Nat.totient (2 * 3697 - 959) = Nat.totient (2 * 3697)
  rw [show (2 * 3697 - 959 : ℕ) = 6435 by norm_num]
  have h1 := phi959
  have h2 := phi6435
  have h3 := phi7394
  omega

end K01A382074

open OMA.S_oeis_a382074 K01A382074 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a382074.main) := by
  intro h
  obtain ⟨n, hn, hval⟩ := idx
  have h0 := h.2.2.1 n hn
  rw [hval] at h0
  have h1 := a_pos
  omega
