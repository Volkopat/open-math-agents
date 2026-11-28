import OMAStatements.S_oeis_a322327

-- Problem: OEIS A322327, Schulte's conjecture that A005361(n) * k^omega(n) is multiplicative
-- Statement: statements/oeis-a322327.lean (declaration OMA.S_oeis_a322327.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. For coprime m and n the primes of m n are the disjoint union of the primes of m and
-- of n, each prime keeps its exponent, and omega(m n) = omega(m) + omega(n). A prime power p^e
-- has the one prime p with exponent e, and omega(p^e) = 1.

namespace OMA.A322327

open Finset ArithmeticFunction OMA.S_oeis_a322327

theorem result (k : ℤ) :
    a k 1 = 1 ∧
    (∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → a k (m * n) = a k m * a k n) ∧
    ∀ p e : ℕ, p.Prime → 0 < e → a k (p ^ e) = k * e := by
  refine ⟨by simp [a], ?_, ?_⟩
  · intro m n hm hn h
    unfold a
    rw [Nat.primeFactors_mul hm.ne' hn.ne', Finset.prod_union h.disjoint_primeFactors,
      cardDistinctFactors_mul h, pow_add]
    have e1 : ∏ p ∈ m.primeFactors, ((m * n).factorization p : ℤ)
        = ∏ p ∈ m.primeFactors, (m.factorization p : ℤ) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpn : ¬ p ∣ n := by
        intro hpn
        have hpp := Nat.prime_of_mem_primeFactors hp
        have := Nat.eq_one_of_dvd_coprimes h (Nat.dvd_of_mem_primeFactors hp) hpn
        exact hpp.one_lt.ne' this
      rw [Nat.factorization_mul_of_coprime h, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpn, add_zero]
    have e2 : ∏ p ∈ n.primeFactors, ((m * n).factorization p : ℤ)
        = ∏ p ∈ n.primeFactors, (n.factorization p : ℤ) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have hpm : ¬ p ∣ m := by
        intro hpm
        have hpp := Nat.prime_of_mem_primeFactors hp
        have := Nat.eq_one_of_dvd_coprimes h hpm (Nat.dvd_of_mem_primeFactors hp)
        exact hpp.one_lt.ne' this
      rw [Nat.factorization_mul_of_coprime h, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpm, zero_add]
    rw [e1, e2]
    ring
  · intro p e hp he
    unfold a
    rw [Nat.primeFactors_prime_pow he.ne' hp, Finset.prod_singleton,
      cardDistinctFactors_apply_prime_pow hp he.ne', hp.factorization_pow]
    simp
    ring

end OMA.A322327

theorem OMA.solution : type_of% @OMA.S_oeis_a322327.main :=
  fun k => OMA.A322327.result k
