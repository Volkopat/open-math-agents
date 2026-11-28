import OMAStatements.S_oeis_a057475
import Mathlib

/-!
Refutation of the OEIS A057475 conjecture (every positive integer is a value of a):
49 is never a value.

* key: for n > 0, primesLE n has at most (a n - 1) + omega(n(n+1)) elements, since every prime
  p <= n not dividing n(n+1) is coprime to n and n+1, and so is 1.
* omega(m) <= log2 m, and 2^n <= (n+1) * lcm(1..n) <= (n+1) * n^(pi n) (Mathlib, Chebyshev).
* n >= 1024: these bounds force a n >= 50.
* 347 <= n < 1024: pi n >= pi 347 = 69 and omega(n(n+1)) <= 20 force a n >= 50.
* n < 347: direct kernel computation.
-/

namespace A057475Refute

theorem key (n : ℕ) (hn : 0 < n) :
    (Nat.primesLE n).card + 1 ≤ OMA.S_oeis_a057475.a n + (n * (n + 1)).primeFactors.card := by
  have hne : n * (n + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hsplit : ((Nat.primesLE n).filter fun p => p ∣ n * (n + 1)).card +
      ((Nat.primesLE n).filter fun p => ¬ p ∣ n * (n + 1)).card = (Nat.primesLE n).card :=
    Finset.card_filter_add_card_filter_not _
  have hU : ((Nat.primesLE n).filter fun p => p ∣ n * (n + 1)).card ≤
      (n * (n + 1)).primeFactors.card := by
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primesLE] at hp
    rw [Nat.mem_primeFactors]
    exact ⟨hp.1.2, hp.2, hne⟩
  have h1 : (1 : ℕ) ∉ (Nat.primesLE n).filter fun p => ¬ p ∣ n * (n + 1) := by
    intro h
    rw [Finset.mem_filter, Nat.mem_primesLE] at h
    exact Nat.not_prime_one h.1.2
  have hT : ((Nat.primesLE n).filter fun p => ¬ p ∣ n * (n + 1)).card + 1 ≤
      OMA.S_oeis_a057475.a n := by
    rw [← Finset.card_insert_of_notMem h1]
    unfold OMA.S_oeis_a057475.a
    apply Finset.card_le_card
    intro k hk
    rw [Finset.mem_insert] at hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    rcases hk with rfl | hk
    · exact ⟨⟨le_refl 1, by omega⟩, Nat.coprime_one_right _, Nat.coprime_one_right _⟩
    · rw [Finset.mem_filter, Nat.mem_primesLE] at hk
      obtain ⟨⟨hkn, hkp⟩, hkd⟩ := hk
      refine ⟨⟨hkp.one_lt.le, hkn⟩, ?_, ?_⟩
      · exact Nat.Coprime.symm
          ((Nat.Prime.coprime_iff_not_dvd hkp).2 (fun h => hkd (Dvd.dvd.mul_right h _)))
      · exact Nat.Coprime.symm
          ((Nat.Prime.coprime_iff_not_dvd hkp).2 (fun h => hkd (Dvd.dvd.mul_left h _)))
  omega

theorem two_pow_omega_le (m : ℕ) (hm : m ≠ 0) : 2 ^ m.primeFactors.card ≤ m :=
  calc 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

theorem cheb (n : ℕ) (hn : n ≠ 0) : 2 ^ n ≤ (n + 1) * n ^ (Nat.primesLE n).card :=
  calc 2 ^ n ≤ (n + 1) * Nat.lcmUpto n := Chebyshev.two_pow_le_mul_lcmUpto n
    _ ≤ (n + 1) * n ^ (Nat.primesLE n).card := by
      refine Nat.mul_le_mul (le_refl _) ?_
      rw [Nat.lcmUpto_eq_prod_pow_log]
      exact Finset.prod_le_pow_card _ _ _ (fun p _ => Nat.pow_log_le_self p hn)

theorem big_aux (L : ℕ) (hL : 10 ≤ L) : (L + 1) * (2 * L + 50) < 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    nlinarith

theorem big (n : ℕ) (hn : 1024 ≤ n) : 50 ≤ OMA.S_oeis_a057475.a n := by
  by_contra hlt
  push_neg at hlt
  have hn0 : n ≠ 0 := by omega
  have hk := key n (by omega)
  have hw := two_pow_omega_le (n * (n + 1)) (Nat.mul_ne_zero hn0 (by omega))
  have hc := cheb n hn0
  have hL1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hL2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hL10 : 10 ≤ Nat.log 2 n := by
    by_contra h
    have h' : 2 ^ (Nat.log 2 n + 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h'' : (2 : ℕ) ^ 10 = 1024 := by norm_num
    have h''' : n < 1024 := lt_of_lt_of_le hL2 (le_trans h' (le_of_eq h''))
    omega
  have hsq : n * (n + 1) < 2 ^ (2 * Nat.log 2 n + 2) := by
    have e1 : n * (n + 1) < (n + 1) * (n + 1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have e2 : (n + 1) * (n + 1) ≤ 2 ^ (Nat.log 2 n + 1) * 2 ^ (Nat.log 2 n + 1) :=
      Nat.mul_le_mul hL2 hL2
    have e3 : 2 ^ (Nat.log 2 n + 1) * 2 ^ (Nat.log 2 n + 1) = 2 ^ (2 * Nat.log 2 n + 2) := by
      rw [← pow_add]
      congr 1
      ring
    rw [← e3]
    exact lt_of_lt_of_le e1 e2
  have hw2 : (n * (n + 1)).primeFactors.card < 2 * Nat.log 2 n + 2 := by
    by_contra h
    push_neg at h
    have h' : 2 ^ (2 * Nat.log 2 n + 2) ≤ 2 ^ (n * (n + 1)).primeFactors.card :=
      Nat.pow_le_pow_right (by norm_num) h
    exact lt_irrefl _ (lt_of_le_of_lt (le_trans h' hw) hsq)
  have hP : (Nat.primesLE n).card ≤ 2 * Nat.log 2 n + 49 := by omega
  have h3 : 2 ^ n ≤ 2 ^ ((Nat.log 2 n + 1) * (2 * Nat.log 2 n + 50)) := by
    calc 2 ^ n ≤ (n + 1) * n ^ (Nat.primesLE n).card := hc
      _ ≤ 2 ^ (Nat.log 2 n + 1) * (2 ^ (Nat.log 2 n + 1)) ^ (2 * Nat.log 2 n + 49) := by
        refine Nat.mul_le_mul hL2 ?_
        calc n ^ (Nat.primesLE n).card ≤ n ^ (2 * Nat.log 2 n + 49) :=
              Nat.pow_le_pow_right (by omega) hP
          _ ≤ (2 ^ (Nat.log 2 n + 1)) ^ (2 * Nat.log 2 n + 49) :=
              Nat.pow_le_pow_left (le_of_lt hL2) _
      _ = 2 ^ ((Nat.log 2 n + 1) * (2 * Nat.log 2 n + 50)) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring
  have h4 : n ≤ (Nat.log 2 n + 1) * (2 * Nat.log 2 n + 50) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  have h5 := big_aux (Nat.log 2 n) hL10
  exact lt_irrefl _ (lt_of_le_of_lt hL1 (lt_of_le_of_lt h4 h5))

theorem pi347 : 69 ≤ (Nat.primesLE 347).card := by decide +kernel

theorem mid (n : ℕ) (h1 : 347 ≤ n) (h2 : n < 1024) : 50 ≤ OMA.S_oeis_a057475.a n := by
  have hk := key n (by omega)
  have hw := two_pow_omega_le (n * (n + 1)) (Nat.mul_ne_zero (by omega) (by omega))
  have hP : (Nat.primesLE 347).card ≤ (Nat.primesLE n).card :=
    Finset.card_mono (Nat.primesLE_mono h1)
  have hw20 : (n * (n + 1)).primeFactors.card ≤ 20 := by
    by_contra h
    push_neg at h
    have h3 : 2 ^ 21 ≤ 2 ^ (n * (n + 1)).primeFactors.card := Nat.pow_le_pow_right (by norm_num) h
    have h4 : n * (n + 1) ≤ 1023 * 1024 := Nat.mul_le_mul (by omega) (by omega)
    have h6 := le_trans h3 (le_trans hw h4)
    norm_num at h6
  have := pi347
  omega

theorem small0 : ∀ n, n < 120 → OMA.S_oeis_a057475.a n ≠ 49 := by decide +kernel

theorem small1 : ∀ n, 120 ≤ n → n < 240 → OMA.S_oeis_a057475.a n ≠ 49 := by decide +kernel

theorem small2 : ∀ n, 240 ≤ n → n < 347 → OMA.S_oeis_a057475.a n ≠ 49 := by decide +kernel

theorem a_ne_49 (n : ℕ) : OMA.S_oeis_a057475.a n ≠ 49 := by
  rcases Nat.lt_or_ge n 120 with h | h
  · exact small0 n h
  rcases Nat.lt_or_ge n 240 with h' | h'
  · exact small1 n h h'
  rcases Nat.lt_or_ge n 347 with h'' | h''
  · exact small2 n h' h''
  rcases Nat.lt_or_ge n 1024 with h''' | h'''
  · have := mid n h'' h'''
    omega
  · have := big n h'''
    omega

end A057475Refute

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a057475.main) := by
  intro h
  obtain ⟨n, -, hn⟩ := h 49 (by norm_num)
  exact A057475Refute.a_ne_49 n hn
