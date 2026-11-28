import OMAStatements.S_oeis_a355448
import Mathlib

open OMA.S_oeis_a355448

namespace P355448

theorem cop (e : ℕ) : Nat.Coprime (2 * e + 1) 6 ↔ e % 3 ≠ 1 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.coprime_mul_iff_right]
  have h2 : Nat.Coprime (2 * e + 1) 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
  have h3 : Nat.Coprime (2 * e + 1) 3 ↔ ¬ 3 ∣ 2 * e + 1 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  rw [h3]
  constructor
  · rintro ⟨-, h⟩; omega
  · intro h; exact ⟨h2, by omega⟩

end P355448

theorem OMA.solution : type_of% @OMA.S_oeis_a355448.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  rw [Nat.card_divisors (pow_ne_zero 2 hn0), Nat.primeFactors_pow n (by norm_num),
    Nat.factorization_pow]
  have hprod : ∏ x ∈ n.primeFactors, ((2 • n.factorization) x + 1) =
      ∏ x ∈ n.primeFactors, (2 * n.factorization x + 1) := by simp
  rw [hprod]
  unfold a307424
  rw [show (∏ p ∈ n.primeFactors, primePowerValue (n.factorization p)).natAbs =
      ∏ p ∈ n.primeFactors, (primePowerValue (n.factorization p)).natAbs from
      map_prod Int.natAbsHom _ _]
  split_ifs with hc
  · rw [Nat.coprime_prod_left_iff] at hc
    symm
    apply Finset.prod_eq_one
    intro p hp
    have := (P355448.cop _).mp (hc p hp)
    unfold primePowerValue
    split_ifs <;> simp_all
  · rw [Nat.coprime_prod_left_iff] at hc
    simp only [not_forall] at hc
    obtain ⟨p, hp, hcp⟩ := hc
    have he : n.factorization p % 3 = 1 := by
      by_contra hne
      exact hcp ((P355448.cop _).mpr hne)
    symm
    apply Finset.prod_eq_zero hp
    unfold primePowerValue
    simp [he]
