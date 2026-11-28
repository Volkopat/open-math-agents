import OMAReductions.R_OeisA217785_conjecture_3_R1
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Taylor

/-! The prime n+2 case follows from Eisenstein after translation by one. -/

open Polynomial

namespace OMA.PrimeGeometricDerivative

lemma polyS_succ (n : ℕ) :
    OeisA217785.polyS (n + 1) = OeisA217785.polyS n +
      C (n + 2 : ℤ) * X ^ (n + 1) := by
  simp [OeisA217785.polyS, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  ring

lemma coeff_shift (n j : ℕ) :
    ((OeisA217785.polyS n).comp (X + 1)).coeff j =
      (j + 1 : ℤ) * (Nat.choose (n + 2) (j + 2) : ℤ) := by
  induction n with
  | zero =>
    by_cases hj : j = 0
    · subst j; norm_num [OeisA217785.polyS]
    · have hlt : 2 < j + 2 := by omega
      simp [OeisA217785.polyS, coeff_one, hj, Nat.choose_eq_zero_of_lt hlt]
  | succ n ih =>
    rw [polyS_succ, add_comp, coeff_add, ih]
    simp only [mul_comp, C_comp, pow_comp, X_comp, coeff_C_mul, coeff_X_add_one_pow]
    have h := Nat.add_one_mul_choose_eq (n + 1) j
    have hz : (n + 2 : ℤ) * ((n + 1).choose j : ℤ) =
        ((n + 2).choose (j + 1) : ℤ) * (j + 1 : ℤ) := by exact_mod_cast h
    rw [show n + 1 + 2 = (n + 2) + 1 by omega,
      Nat.choose_succ_succ (n + 2) (j + 1)]
    push_cast
    nlinarith [hz]

lemma shifted_degree (n : ℕ) :
    ((OeisA217785.polyS n).comp (X + 1)).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_shift, Nat.choose_eq_zero_of_lt (by omega : n + 2 < j + 2)]
    simp
  · rw [coeff_shift, Nat.choose_self]
    positivity

lemma shifted_leadingCoeff (n : ℕ) :
    ((OeisA217785.polyS n).comp (X + 1)).leadingCoeff = (n + 1 : ℤ) := by
  rw [leadingCoeff, shifted_degree, coeff_shift, Nat.choose_self]
  simp

lemma shifted_primitive (n : ℕ) :
    ((OeisA217785.polyS n).comp (X + 1)).IsPrimitive := by
  intro r hr
  apply isUnit_of_dvd_one
  have he := Polynomial.eval_dvd (x := (-1 : ℤ)) hr
  rw [eval_C, eval_comp] at he
  simpa [OeisA217785.polyS, ← coeff_zero_eq_eval_zero, finsetSum_coeff, coeff_C_mul_X_pow] using he

lemma shifted_irreducible (n : ℕ) (hn : 1 ≤ n) (hp : (n + 2).Prime) :
    Irreducible ((OeisA217785.polyS n).comp (X + 1)) := by
  let P : Ideal ℤ := Ideal.span {((n + 2 : ℕ) : ℤ)}
  have hP : P.IsPrime := by
    change (Ideal.span {((n + 2 : ℕ) : ℤ)}).IsPrime
    rw [Ideal.span_singleton_prime]
    · rw [Int.prime_iff_natAbs_prime, Int.natAbs_natCast]
      exact hp
    · exact_mod_cast (by omega : n + 2 ≠ 0)
  have he : ((OeisA217785.polyS n).comp (X + 1)).IsEisensteinAt P := by
    refine ⟨?_, ?_, ?_⟩
    · rw [shifted_leadingCoeff]
      change ¬ (n + 1 : ℤ) ∈ Ideal.span {((n + 2 : ℕ) : ℤ)}
      rw [Ideal.mem_span_singleton]
      intro h
      have hnat : n + 2 ∣ n + 1 := by exact_mod_cast h
      have := Nat.le_of_dvd (by omega : 0 < n + 1) hnat
      omega
    · intro j hj
      rw [shifted_degree] at hj
      rw [coeff_shift]
      apply Ideal.mem_span_singleton.mpr
      have hc : n + 2 ∣ (n + 2).choose (j + 2) :=
        hp.dvd_choose_self (by omega) (by omega)
      apply dvd_mul_of_dvd_right
      exact_mod_cast hc
    · rw [coeff_shift]
      simp only [Nat.cast_zero, zero_add, one_mul]
      change ¬ ((n + 2).choose 2 : ℤ) ∈
        (Ideal.span {((n + 2 : ℕ) : ℤ)} : Ideal ℤ) ^ 2
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro h
      have hnat : (n + 2) ^ 2 ∣ (n + 2).choose 2 := by exact_mod_cast h
      have hpos : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
      have hlt := Nat.choose_lt_pow (by omega : n + 2 ≠ 0) (by omega : 2 ≤ 2)
      have := Nat.le_of_dvd hpos hnat
      omega
  exact he.irreducible hP (shifted_primitive n) (by rw [shifted_degree]; omega)

lemma original_irreducible (n : ℕ) (hn : 1 ≤ n) (hp : (n + 2).Prime) :
    Irreducible (OeisA217785.polyS n) := by
  apply (MulEquiv.irreducible_iff (taylorEquiv (1 : ℤ))).mp
  change Irreducible ((taylor (1 : ℤ)) (OeisA217785.polyS n))
  rw [taylor_apply, C_1]
  exact shifted_irreducible n hn hp

lemma original_primitive (n : ℕ) : (OeisA217785.polyS n).IsPrimitive := by
  intro r hr
  apply isUnit_of_dvd_one
  have he := Polynomial.eval_dvd (x := (0 : ℤ)) hr
  simpa [OeisA217785.polyS, ← coeff_zero_eq_eval_zero, finsetSum_coeff, coeff_C_mul_X_pow] using he

end OMA.PrimeGeometricDerivative

theorem OMA.solution : OMA.R_OeisA217785_conjecture_3_R1.H1 := by
  intro n hn hp
  exact (OMA.PrimeGeometricDerivative.original_primitive n).irreducible_iff_irreducible_map_fraction_map.mp
    (OMA.PrimeGeometricDerivative.original_irreducible n hn hp)
