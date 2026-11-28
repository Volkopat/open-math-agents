import OMAStatements.S_oeis_a014442
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a014442.main := fun p hp h4 => by
  have := Fact.mk hp
  obtain ⟨y, hy⟩ := ZMod.exists_sq_eq_neg_one_iff.2 (by omega : p % 4 ≠ 3)
  have hd : p ∣ y.val ^ 2 + 1 := by rw [← ZMod.natCast_eq_zero_iff]; simp [sq, ← hy]
  have := y.val_lt
  refine ⟨y.val, Nat.pos_of_ne_zero fun h => hp.one_lt.ne' (by simpa [h] using hd), hd, fun q hq => ?_⟩
  by_contra
  have := Nat.le_of_dvd (by positivity) (Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp (Nat.prime_of_mem_primeFactors hq)).2 (by omega)) hd (Nat.dvd_of_mem_primeFactors hq))
  nlinarith
