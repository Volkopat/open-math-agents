import OMAReductions.R_oeis_a109799_R1

-- Step oeis-a109799.R1.H1: hypothesis H1 of reduction oeis-a109799.R1
-- Credit: @luciusacarr
-- H1 := ∀ p : ℕ, p.Prime → 3 ≤ p →   (IsChenPrime (2 ^ p - 1) ↔ (2 ^ p - 1).Prime ∧ ((2 ^ p + 1) / 3).Prime)

/-! For odd `p ≥ 3`, `(2^p - 1) + 2 = 2^p + 1 = 3 m` with `m = (2^p + 1)/3 ≥ 3`. It is not prime
(it is a proper multiple of `3`), and its prime factor list is `3 :: factors m` up to
permutation, which has length `2` exactly when `m` is prime. -/

open OMA.S_oeis_a109799

namespace OMA.S109799H1

theorem len_one_iff {m : ℕ} (hm : 2 ≤ m) : m.primeFactorsList.length = 1 ↔ m.Prime := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h
    have hprod := Nat.prod_primeFactorsList (show m ≠ 0 by omega)
    rw [ha] at hprod
    simp at hprod
    have : a ∈ m.primeFactorsList := by rw [ha]; simp
    rw [← hprod]
    exact Nat.prime_of_mem_primeFactorsList this
  · intro hp
    rw [Nat.primeFactorsList_prime hp]
    rfl

end OMA.S109799H1

theorem OMA.solution : OMA.R_oeis_a109799_R1.H1 := by
  intro p hp hp3
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h8 : 8 ≤ 2 ^ p := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp3
  have h3 : 3 ∣ 2 ^ p + 1 := by
    obtain ⟨k, rfl⟩ := hodd
    have : (2 : ℕ) ^ (2 * k + 1) + 1 = 2 * 4 ^ k + 1 := by
      rw [pow_succ, pow_mul]; ring
    rw [this]
    have hm : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    omega
  obtain ⟨m, hm⟩ := h3
  have hm3 : 3 ≤ m := by omega
  have hdiv : (2 ^ p + 1) / 3 = m := by omega
  have hq2 : 2 ^ p - 1 + 2 = 3 * m := by omega
  have hnotprime : ¬ (3 * m).Prime := by
    intro h
    have := (Nat.prime_mul_iff.mp h)
    rcases this with ⟨_, h1⟩ | ⟨_, h1⟩
    · omega
    · omega
  have hlen : (3 * m).primeFactorsList.length = 1 + m.primeFactorsList.length := by
    have := (Nat.perm_primeFactorsList_mul (by norm_num : (3 : ℕ) ≠ 0) (by omega : m ≠ 0)).length_eq
    rw [this, List.length_append, Nat.primeFactorsList_prime Nat.prime_three]
    rfl
  unfold IsChenPrime
  rw [hq2, hdiv, hlen]
  constructor
  · rintro ⟨hq, h⟩
    refine ⟨hq, ?_⟩
    rcases h with h | h
    · exact absurd h hnotprime
    · exact (OMA.S109799H1.len_one_iff (by omega)).mp (by omega)
  · rintro ⟨hq, h⟩
    refine ⟨hq, Or.inr ?_⟩
    have := (OMA.S109799H1.len_one_iff (by omega)).mpr h
    omega
