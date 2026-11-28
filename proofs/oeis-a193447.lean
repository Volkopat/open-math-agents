import OMAStatements.S_oeis_a193447
import Mathlib

/-! Following @ivillar (#27442), retain the Wilson-theorem characterization.
Use its converse directly; in the prime case, only the two distinct factors
2 and (k-1)/2 are needed for divisibility by k-1. -/

namespace A193447Wilson

theorem mul_dvd_fact (a b : ℕ) (ha : 0 < a) (hab : a < b) : a * b ∣ b.factorial := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [Nat.factorial_succ, mul_comm (c + 1)]
  exact Nat.mul_dvd_mul (Nat.dvd_factorial ha (by omega)) (dvd_refl _)

end A193447Wilson

theorem OMA.solution : type_of% @OMA.S_oeis_a193447.main := by
  intro k hk
  have hkm : ((k - 1 : ℕ) : ZMod k) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), ZMod.natCast_self]
    simp
  have hfac : ((k - 1).factorial : ZMod k) = -((k - 2).factorial : ZMod k) := by
    have he : (k - 1).factorial = (k - 1) * (k - 2).factorial := by
      convert Nat.factorial_succ (k - 2) using 1 <;> congr 1 <;> omega
    rw [he, Nat.cast_mul, hkm, neg_one_mul]
  constructor
  · intro hd
    have hd' : k ∣ (k - 2).factorial + (k - 1) := (dvd_mul_right k (k - 1)).trans hd
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd'
    rw [Nat.cast_add, hkm] at hz
    apply Nat.prime_of_fac_equiv_neg_one _ (by omega)
    rw [hfac]
    linear_combination -hz
  · intro hp
    have : Fact k.Prime := ⟨hp⟩
    have hk1 : k - 1 ∣ (k - 2).factorial + (k - 1) := by
      obtain ⟨a, ha⟩ := hp.odd_of_ne_two (by omega)
      have he : k - 1 = 2 * a := by omega
      have hd := (A193447Wilson.mul_dvd_fact 2 a (by omega) (by omega)).trans
        (Nat.factorial_dvd_factorial (show a ≤ k - 2 by omega))
      rw [← he] at hd
      exact dvd_add hd (dvd_refl _)
    have hkk : k ∣ (k - 2).factorial + (k - 1) := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hkm]
      have hw := ZMod.wilsons_lemma (p := k)
      rw [hfac] at hw
      linear_combination -hw
    exact ((Nat.coprime_self_sub_right (by omega : 1 ≤ k)).mpr
      (Nat.coprime_one_right k)).mul_dvd_of_dvd_of_dvd hkk hk1
