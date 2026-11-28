import OMAStatements.S_oeis_a345938

-- Problem: A345938: a(n) = uphi(n) / gcd(n-1, uphi(n)), where uphi is unitary totient (or unitary phi) function, A047994.
-- Upstream: formal-conjectures statements/oeis-a345938.lean:0 (declaration OMA.S_oeis_a345938.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for squarefree n every exponent is 1, so uphi(n) = prod (p - 1) = phi(n), and the
-- numerator of phi(n)/(n-1) is phi(n)/gcd(n-1, phi(n)) = a(n). If phi(n) | n-1 and p^2 | n, then
-- p | phi(p^2) | phi(n) | n-1 and p | n, so p | 1; hence n is squarefree, a(n) = phi(n)/phi(n) = 1,
-- and a squarefree n that is not prime is not a prime power.

namespace N18A345938

open OMA.S_oeis_a345938

theorem uphi_sq (n : ℕ) (hn : n ≠ 0) (hsq : Squarefree n) : uphi n = Nat.totient n := by
  rw [Nat.totient_eq_prod_factorization hn, Finsupp.prod, Nat.support_factorization]
  unfold uphi
  apply Finset.prod_congr rfl
  intro p hp
  have hp1 : n.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hn).mp hsq p
  have hp0 : 0 < n.factorization p := by
    rw [Nat.mem_primeFactors] at hp
    exact Nat.Prime.factorization_pos_of_dvd hp.1 hn hp.2.1
  rw [show n.factorization p = 1 by omega]
  simp

theorem num_eq (t m : ℕ) (hm : 0 < m) :
    ((t : ℚ) / (m : ℚ)).num = ((t / Nat.gcd m t : ℕ) : ℤ) := by
  have h1 : Rat.divInt (t : ℤ) (m : ℤ) = (t : ℚ) / (m : ℚ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast]
  have h2 : Int.sign (m : ℤ) = 1 := Int.sign_eq_one_of_pos (by exact_mod_cast hm)
  rw [← h1, Rat.num_divInt, h2, Int.one_mul, Int.gcd_natCast_natCast, Int.natCast_ediv]

theorem part1 (n : ℕ) (hn : 1 ≤ n) (hsq : Squarefree n) : (a n : ℤ) = A160595 n := by
  rcases Nat.eq_or_lt_of_le hn with h1 | h2
  · subst h1
    have hu : uphi 1 = 1 := by
      unfold uphi
      rw [Nat.primeFactors_one, Finset.prod_empty]
    unfold a A160595
    rw [if_pos (rfl : (1 : ℕ) = 1), hu, Nat.sub_self, Nat.gcd_zero_left, Nat.div_one, Nat.cast_one]
  · have hu := uphi_sq n (by omega) hsq
    have hc : ((n : ℚ) - 1) = ((n - 1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    unfold a A160595
    rw [if_neg (show ¬ n = 1 by omega), hu, hc, num_eq (Nat.totient n) (n - 1) (by omega)]

theorem lehmer_sq (n : ℕ) (hn : 1 < n) (hd : Nat.totient n ∣ n - 1) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpp2 : p ^ 2 ∣ n := by
    rw [pow_two]
    exact hpp
  have h2 : Nat.totient (p ^ 2) = p ^ 1 * (p - 1) := Nat.totient_prime_pow_succ hp 1
  have h3a : p ∣ Nat.totient (p ^ 2) := by
    rw [h2]
    exact dvd_mul_of_dvd_left (dvd_pow_self p one_ne_zero) (p - 1)
  have h3 : p ∣ n - 1 := h3a.trans ((Nat.totient_dvd_of_dvd hpp2).trans hd)
  have h4 : p ∣ n := (dvd_mul_right p p).trans hpp
  have h5 : p ∣ n - (n - 1) := Nat.dvd_sub h4 h3
  rw [show n - (n - 1) = 1 by omega] at h5
  exact hp.one_lt.ne' (Nat.dvd_one.mp h5)

theorem part2 (n : ℕ) (hn : 1 < n) (hnp : ¬ n.Prime) (hd : Nat.totient n ∣ n - 1) :
    a n = 1 ∧ ¬ IsPrimePow n := by
  have hsq := lehmer_sq n hn hd
  have hu := uphi_sq n (by omega) hsq
  have htpos : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
  constructor
  · unfold a
    rw [hu, Nat.gcd_eq_right hd, Nat.div_self htpos]
  · intro hpp
    rw [isPrimePow_nat_iff] at hpp
    obtain ⟨p, k, hp, hk, hpk⟩ := hpp
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      rw [hk1, pow_one] at hpk
      exact hnp (hpk ▸ hp)
    · have hdvd : p * p ∣ n := by
        rw [← hpk, ← pow_two]
        exact pow_dvd_pow p hk2
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq) p hp hdvd

end N18A345938

open OMA.S_oeis_a345938 N18A345938 in
theorem OMA.solution : type_of% @OMA.S_oeis_a345938.main := by
  exact ⟨fun n hn hsq => part1 n hn hsq, fun n hn hnp hd => part2 n hn hnp hd⟩
