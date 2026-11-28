import OMAStatements.S_oeis_a117119

-- Problem: A117119: Number of partitions of 2*n into two odd prime powers.
-- Upstream: formal-conjectures statements/oeis-a117119.lean:0 (declaration OMA.S_oeis_a117119.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 164 is a counterexample to a(n) > A002375(n). The odd prime powers below 328 that
-- are not prime are 1, 9, 25, 27, 49, 81, 121, 125, 169, 243, 289, and 328 minus each of them
-- (327, 319, 303, 301, 279, 247, 207, 203, 159, 85, 39) has two distinct prime factors. So every
-- partition of 328 into two odd prime powers is a partition into two odd primes, the first filter
-- is a subset of the second, and a(164) <= A002375(164).

namespace H01A117119

open OMA.S_oeis_a117119

theorem oddpp_odd {m : ℕ} (h : IsOddPrimePow m) : Odd m := by
  unfold IsOddPrimePow at h
  rcases h with h | h
  · rw [h]
    exact odd_one
  · exact h.1

theorem notpp (n p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h1 : p ∣ n)
    (h2 : q ∣ n) : ¬ IsPrimePow n := by
  intro h
  obtain ⟨r, k, hr, -, rfl⟩ := (isPrimePow_nat_iff _).mp h
  have e1 := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h1)
  have e2 := (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow h2)
  exact hpq (e1.trans e2.symm)

theorem nopp (n p q : ℕ) (hn : n ≠ 1) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h1 : p ∣ n) (h2 : q ∣ n) : ¬ IsOddPrimePow n := by
  intro h
  unfold IsOddPrimePow at h
  rcases h with h | h
  · exact hn h
  · exact notpp n p q hp hq hpq h1 h2 h.2

theorem L1 (m : ℕ) (hm : m ≤ 328) (h : IsOddPrimePow m) (hnp : ¬ m.Prime) :
    m = 1 ∨ m = 9 ∨ m = 25 ∨ m = 27 ∨ m = 49 ∨ m = 81 ∨ m = 121 ∨ m = 125 ∨ m = 169 ∨
      m = 243 ∨ m = 289 := by
  unfold IsOddPrimePow at h
  rcases h with h | ⟨hodd, hpp⟩
  · exact Or.inl h
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have hk1 : k = 1 := by omega
      subst hk1
      rw [pow_one] at hnp
      exact hnp hp
    have hp2 : 2 ≤ p := hp.two_le
    have hp3 : 3 ≤ p := by
      by_contra hp3
      have hp2' : p = 2 := by omega
      subst hp2'
      have o1 := Nat.odd_iff.mp hodd
      have o2 := Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, (by omega : k ≠ 0)⟩)
      omega
    have hsq : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk2
    have hp18 : p ≤ 18 := by
      by_contra hp18
      have h19 : 19 * 19 ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
      have e : p ^ 2 = p * p := by ring
      omega
    have hk5 : k ≤ 5 := by
      by_contra hk5
      have h1 : 3 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp3 k
      have h2 : 729 ≤ 3 ^ k :=
        calc 729 = 3 ^ 6 := by norm_num
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    revert hp hm
    interval_cases p <;> interval_cases k <;> norm_num

theorem key (i j : ℕ) (hij : i + j = 328) (hle : i ≤ j) (hi : IsOddPrimePow i)
    (hj : IsOddPrimePow j) : Odd i ∧ i.Prime ∧ Odd j ∧ j.Prime := by
  have hpi : i.Prime := by
    by_contra hpi
    rcases L1 i (by omega) hi hpi with h | h | h | h | h | h | h | h | h | h | h
    · exact nopp 327 3 109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rwa [show j = 327 by omega] at hj)
    · exact nopp 319 11 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rwa [show j = 319 by omega] at hj)
    · exact nopp 303 3 101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rwa [show j = 303 by omega] at hj)
    · exact nopp 301 7 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rwa [show j = 301 by omega] at hj)
    · exact nopp 279 3 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rwa [show j = 279 by omega] at hj)
    · exact nopp 247 13 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rwa [show j = 247 by omega] at hj)
    · exact nopp 207 3 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rwa [show j = 207 by omega] at hj)
    · exact nopp 203 7 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by rwa [show j = 203 by omega] at hj)
    · omega
    · omega
    · omega
  have hpj : j.Prime := by
    by_contra hpj
    rcases L1 j (by omega) hj hpj with h | h | h | h | h | h | h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [show i = 159 by omega] at hpi
      norm_num at hpi
    · rw [show i = 85 by omega] at hpi
      norm_num at hpi
    · rw [show i = 39 by omega] at hpi
      norm_num at hpi
  exact ⟨oddpp_odd hi, hpi, oddpp_odd hj, hpj⟩

theorem a_le : a 164 ≤ A002375 164 := by
  unfold a A002375
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  obtain ⟨hi1, hp, hq⟩ := hi
  have hb := Finset.mem_Icc.mp hi1
  exact ⟨hi1, key i (2 * 164 - i) (by omega) (by omega) hp hq⟩

end H01A117119

open OMA.S_oeis_a117119 H01A117119 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a117119.main) := by
  intro H
  exact absurd (H 164 (by norm_num)).2 (not_lt.mpr a_le)
