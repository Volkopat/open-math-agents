import OMAReductions.R_mse_468037_R1

/-!
# Proof of `mse-468037.R1.H1`

Proves Euler's theorem on odd perfect numbers: every odd perfect number `N` has the form
`N = q ^ k * m ^ 2` with `q` prime, `q % 4 = 1`, `k % 4 = 1`, and `q.Coprime m`.

Since `N` is perfect and odd, `∑ d ∈ N.divisors, d = 2 * N`, which is divisible by `2` but not
by `4`. Factoring `∑ d ∈ N.divisors, d = ∏ p ∈ N.primeFactors, ∑ j ∈ range (e_p + 1), p ^ j`:
- Each factor `s(p, e) = ∑ j ∈ range (e + 1), p ^ j` for odd prime `p` is odd iff `e` is even.
- When `e` is odd, `s(p, e) ≡ 0 (mod 4)` if `p % 4 = 3` or `e % 4 = 3`, and `s(p, e) ≡ 2 (mod 4)`
  when `p % 4 = 1` and `e % 4 = 1`.
Hence `2 ∥ 2 * N` forces a unique prime `q ∈ N.primeFactors` with odd exponent `k = e_q`,
satisfying `q % 4 = 1` and `k % 4 = 1`, while all other prime factors have even exponents.
-/

namespace Mse468037R1H1Proof

open Finset

private lemma geom_sum_mod_two {p : ℕ} (hp : Odd p) (n : ℕ) :
    (∑ j ∈ range n, p ^ j) % 2 = n % 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have : p ^ n % 2 = 1 := Nat.odd_iff.mp hp.pow
    omega

private lemma geom_sum_mod_four_of_one {p : ℕ} (hp : p % 4 = 1) (n : ℕ) :
    (∑ j ∈ range n, p ^ j) % 4 = n % 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have hpow : p ^ n % 4 = 1 := by
      rw [Nat.pow_mod, hp, one_pow]
      decide
    omega

private lemma geom_sum_mod_four_of_three_even {p : ℕ} (hp : p % 4 = 3) (n : ℕ) :
    (∑ j ∈ range (2 * n), p ^ j) % 4 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : p ^ (2 * n) % 4 = 1 := by
      rw [pow_mul, Nat.pow_mod, show (p ^ 2) % 4 = 1 by rw [Nat.pow_mod, hp], one_pow]
      decide
    have h2 : p ^ (2 * n + 1) % 4 = 3 := by
      rw [pow_succ, Nat.mul_mod, h1, hp]
    omega

private lemma sum_divisors_eq_two_mul_of_perfect {N : ℕ} (hN : Nat.Perfect N) :
    ∑ d ∈ N.divisors, d = 2 * N := by
  have h1 := hN.1
  have hpos := hN.2
  have hsplit : N.divisors = insert N N.properDivisors := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_insert, Nat.mem_properDivisors]
    constructor
    · rintro ⟨hd, _⟩
      rcases eq_or_lt_of_le (Nat.le_of_dvd hpos hd) with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨hd, hlt⟩
    · rintro (rfl | ⟨hd, _⟩)
      · exact ⟨dvd_refl _, hpos.ne'⟩
      · exact ⟨hd, hpos.ne'⟩
  have hnotmem : N ∉ N.properDivisors := by
    simp [Nat.mem_properDivisors]
  rw [hsplit, Finset.sum_insert hnotmem, h1]
  omega

end Mse468037R1H1Proof

theorem OMA.solution : OMA.R_mse_468037_R1.H1 := by
  intro N hodd hperf
  have hpos : 0 < N := hperf.2
  have hN0 : N ≠ 0 := hpos.ne'
  have hsum : ∑ d ∈ N.divisors, d = 2 * N :=
    Mse468037R1H1Proof.sum_divisors_eq_two_mul_of_perfect hperf
  have hprod : 2 * N = ∏ p ∈ N.primeFactors, ∑ j ∈ Finset.range (N.factorization p + 1), p ^ j := by
    rw [← hsum, Nat.sum_divisors hN0]
  have hp_odd : ∀ p ∈ N.primeFactors, Odd p := by
    intro p hp
    have hd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    by_contra hev
    have h2p : 2 ∣ p := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr (dvd_trans h2p hd))
  have hnot4 : ¬ 4 ∣ 2 * N := by
    intro h4
    obtain ⟨t, ht⟩ := h4
    have : 2 ∣ N := ⟨t, by omega⟩
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr this)
  -- There must exist at least one prime factor with odd exponent (otherwise product is odd)
  have hex_odd : ∃ q ∈ N.primeFactors, Odd (N.factorization q) := by
    by_contra hall
    push Not at hall
    have hall_odd : ∀ p ∈ N.primeFactors,
        Odd (∑ j ∈ Finset.range (N.factorization p + 1), p ^ j) := by
      intro p hp
      have hev : Even (N.factorization p) := Nat.not_odd_iff_even.mp (hall p hp)
      rw [Nat.odd_iff, Mse468037R1H1Proof.geom_sum_mod_two (hp_odd p hp)]
      obtain ⟨r, hr⟩ := hev
      omega
    have hprod_odd : Odd (∏ p ∈ N.primeFactors, ∑ j ∈ Finset.range (N.factorization p + 1), p ^ j) := by
      have : ∀ (s : Finset ℕ), (∀ p ∈ s, Odd (∑ j ∈ Finset.range (N.factorization p + 1), p ^ j)) →
          Odd (∏ p ∈ s, ∑ j ∈ Finset.range (N.factorization p + 1), p ^ j) := by
        intro s
        induction s using Finset.induction_on with
        | empty => intro _; simp
        | insert a t ha ih =>
          intro h
          rw [Finset.prod_insert ha]
          exact (h a (Finset.mem_insert_self a t)).mul
            (ih fun p hp => h p (Finset.mem_insert_of_mem hp))
      exact this N.primeFactors hall_odd
    rw [← hprod] at hprod_odd
    exact Nat.not_even_iff_odd.mpr hprod_odd ⟨N, by omega⟩
  obtain ⟨q, hq_mem, hq_odd_exp⟩ := hex_odd
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  set k := N.factorization q
  -- Factor at q is even
  have hq_fac_even : 2 ∣ ∑ j ∈ Finset.range (k + 1), q ^ j := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Mse468037R1H1Proof.geom_sum_mod_two (hp_odd q hq_mem)]
    obtain ⟨r, hr⟩ := hq_odd_exp
    omega
  -- Every other prime factor p ≠ q must have even exponent (else 4 ∣ 2 * N)
  have hother_even : ∀ p ∈ N.primeFactors.erase q, Even (N.factorization p) := by
    intro p hp
    have hp_ne : p ≠ q := (Finset.mem_erase.mp hp).1
    have hp_mem : p ∈ N.primeFactors := (Finset.mem_erase.mp hp).2
    by_contra hnot
    have hp_odd_exp : Odd (N.factorization p) := Nat.not_even_iff_odd.mp hnot
    have hp_fac_even : 2 ∣ ∑ j ∈ Finset.range (N.factorization p + 1), p ^ j := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Mse468037R1H1Proof.geom_sum_mod_two (hp_odd p hp_mem)]
      obtain ⟨r, hr⟩ := hp_odd_exp
      omega
    have hmul_dvd : (∑ j ∈ Finset.range (k + 1), q ^ j) *
        (∑ j ∈ Finset.range (N.factorization p + 1), p ^ j) ∣ 2 * N := by
      rw [hprod, ← Finset.mul_prod_erase N.primeFactors _ hq_mem]
      exact mul_dvd_mul_left _ (Finset.dvd_prod_of_mem _ hp)
    exact hnot4 (dvd_trans (mul_dvd_mul hq_fac_even hp_fac_even) hmul_dvd)
  -- Factor at q is not divisible by 4, forcing q % 4 = 1 and k % 4 = 1
  have hq_not4 : ¬ 4 ∣ ∑ j ∈ Finset.range (k + 1), q ^ j := by
    intro h4
    have hdvd : (∑ j ∈ Finset.range (k + 1), q ^ j) ∣ 2 * N := by
      rw [hprod]
      exact Finset.dvd_prod_of_mem _ hq_mem
    exact hnot4 (dvd_trans h4 hdvd)
  have hq4 : q % 4 = 1 := by
    have hqo : q % 2 = 1 := Nat.odd_iff.mp (hp_odd q hq_mem)
    by_contra hne
    have hq3 : q % 4 = 3 := by omega
    obtain ⟨r, hr⟩ := hq_odd_exp
    have hk1 : k + 1 = 2 * (r + 1) := by omega
    have h4 : 4 ∣ ∑ j ∈ Finset.range (k + 1), q ^ j := by
      apply Nat.dvd_of_mod_eq_zero
      rw [hk1]
      exact Mse468037R1H1Proof.geom_sum_mod_four_of_three_even hq3 (r + 1)
    exact hq_not4 h4
  have hk4 : k % 4 = 1 := by
    have hmod := Mse468037R1H1Proof.geom_sum_mod_four_of_one hq4 (k + 1)
    have hko : k % 2 = 1 := Nat.odd_iff.mp hq_odd_exp
    have hne0 : (∑ j ∈ Finset.range (k + 1), q ^ j) % 4 ≠ 0 := by
      intro h0
      exact hq_not4 (Nat.dvd_of_mod_eq_zero h0)
    omega
  -- Construct m = ∏_{p ∈ N.primeFactors.erase q} p ^ (e_p / 2)
  set m : ℕ := ∏ p ∈ N.primeFactors.erase q, p ^ (N.factorization p / 2)
  have hcop : q.Coprime m := by
    refine Nat.Coprime.prod_right fun p hp => ?_
    have hp_ne : p ≠ q := (Finset.mem_erase.mp hp).1
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2
    exact ((Nat.coprime_primes hq_prime hp_prime).mpr (Ne.symm hp_ne)).pow_right _
  have hNeq : N = q ^ k * m ^ 2 := by
    calc N = ∏ p ∈ N.primeFactors, p ^ (N.factorization p) :=
          (Nat.prod_factorization_pow_eq_self hN0).symm
      _ = q ^ k * ∏ p ∈ N.primeFactors.erase q, p ^ (N.factorization p) :=
          (Finset.mul_prod_erase N.primeFactors (fun p => p ^ (N.factorization p)) hq_mem).symm
      _ = q ^ k * m ^ 2 := by
          congr 1
          rw [sq, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun p hp => ?_
          rw [← pow_add]
          congr 1
          obtain ⟨r, hr⟩ := hother_even p hp
          omega
  exact ⟨q, k, m, hq_prime, hq4, hk4, hcop, hNeq⟩
