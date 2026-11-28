import OMAStatements.S_oeis_a096069
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a096069.main := fun p hp h2 h5 => by
  have h : p.Coprime (10 ^ _) := Nat.Coprime.pow_right (Nat.digits 10 p).length (((Nat.coprime_primes hp Nat.prime_two).2 h2).mul_right ((Nat.coprime_primes hp (by norm_num : Nat.Prime 5)).2 h5))
  obtain ⟨a, ha, hb⟩ := Nat.chineseRemainder h.symm p 1
  obtain ⟨q, -, hq, e⟩ := Nat.forall_exists_prime_gt_and_modEq p (by simp [hp.ne_zero]) (Nat.Coprime.mul_right (by rwa [Nat.Coprime, ha.gcd_eq]) (by rw [Nat.Coprime, hb.gcd_eq]; simp) : a.Coprime (10 ^ (Nat.digits 10 p).length * p))
  exact ⟨q, hq, (e.of_mul_right _).trans ha, (e.of_mul_left _).trans hb⟩
