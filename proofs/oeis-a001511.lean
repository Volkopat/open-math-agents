import OMAStatements.S_oeis_a001511
import Mathlib

/-!
# A001511: odd-divisor power sums divide even-divisor power sums

Write n = 2^e·m with m odd. The odd divisors of n are exactly the divisors of m, so the odd sum is
σ_k(m). The even and odd sums add up to σ_k(n) = σ_k(2^e)·σ_k(m) by multiplicativity, so the even
sum is (σ_k(2^e) − 1)·σ_k(m), a multiple of σ_k(m).
-/

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a001511.main := by
  intro n hn k
  have hsplit : ∀ d : ℕ, d ^ k * (d % 2 == 0).toNat + d ^ k * (d % 2 == 1).toNat = d ^ k := by
    intro d
    rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [h]
  have hsum : OMA.S_oeis_a001511.evenDivPow n k + OMA.S_oeis_a001511.oddDivPow n k =
      sigma k n := by
    unfold OMA.S_oeis_a001511.evenDivPow OMA.S_oeis_a001511.oddDivPow
    rw [← Finset.sum_add_distrib, sigma_apply]
    exact Finset.sum_congr rfl fun d _ => hsplit d
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hm)
  have hodd : OMA.S_oeis_a001511.oddDivPow (2 ^ e * m) k = sigma k m := by
    unfold OMA.S_oeis_a001511.oddDivPow
    have hterm : ∀ d : ℕ, d ^ k * (d % 2 == 1).toNat = if d % 2 = 1 then d ^ k else 0 := by
      intro d
      rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [h]
    simp only [hterm]
    rw [← Finset.sum_filter, sigma_apply]
    congr 1
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, hdo⟩
      refine ⟨?_, hm0⟩
      have hc : Nat.Coprime d (2 ^ e) :=
        Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hdo))
      exact hc.dvd_of_dvd_mul_left hd
    · rintro ⟨hd, -⟩
      refine ⟨⟨Dvd.dvd.mul_left hd _, by positivity⟩, ?_⟩
      exact Nat.odd_iff.mp (Odd.of_dvd_nat hm hd)
  have hmul : sigma k (2 ^ e * m) = sigma k (2 ^ e) * sigma k m :=
    isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [hodd]
  rw [hodd, hmul] at hsum
  have h1 : 1 ≤ sigma k (2 ^ e) := (sigma_pos_iff).mpr (by positivity)
  obtain ⟨t, ht⟩ : ∃ t, sigma k (2 ^ e) = t + 1 := ⟨sigma k (2 ^ e) - 1, by omega⟩
  rw [ht, add_mul, one_mul] at hsum
  refine ⟨t, ?_⟩
  have := Nat.add_right_cancel hsum
  rw [this]
  ring
