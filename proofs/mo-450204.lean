import OMAStatements.S_mo_450204
import Mathlib

-- Retains @caa1982's cyclotomic counterexample from PR #28662.
-- Integral extensions reflect units, replacing the explicit rational-inverse argument.
open OMA.S_mo_450204

open NumberField

lemma three_not_unit : ¬ IsUnit (3 : 𝓞 (CyclotomicField 4 ℚ)) := by
  intro h3
  have h : IsUnit (3 : ℤ) :=
    (isUnit_map_iff (algebraMap ℤ (𝓞 (CyclotomicField 4 ℚ))) 3).mp (by simpa using h3)
  norm_num [Int.isUnit_iff] at h

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_450204.main) := by
  intro h
  have : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    @CyclotomicField.isCyclotomicExtension 4 _ ℚ _ ⟨by norm_num⟩
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ (CyclotomicField 4 ℚ)
  set z : 𝓞 (CyclotomicField 4 ℚ) := hζ.toInteger with hz
  have hzp : IsPrimitiveRoot z 4 := hζ.toInteger_isPrimitiveRoot
  have hz2 : z ^ 2 = -1 := by
    have : IsPrimitiveRoot (z ^ 2) 2 := hzp.pow (by norm_num) (by norm_num)
    exact this.eq_neg_one_of_two_right
  have hu : IsUnit z := hzp.isUnit (by norm_num)
  obtain ⟨P, hPmax, hP3⟩ := Ideal.exists_le_maximal (Ideal.span {(3 : 𝓞 (CyclotomicField 4 ℚ))})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact three_not_unit)
  obtain ⟨n, hn⟩ := h (CyclotomicField 4 ℚ) hu.unit P hPmax
  have h3 : (3 : 𝓞 (CyclotomicField 4 ℚ)) ∈ P := hP3 (Ideal.mem_span_singleton_self _)
  have := hPmax
  have hw2 : (Ideal.Quotient.mk P z) ^ 2 = -1 := by
    rw [← map_pow, hz2, map_neg, map_one]
  have hF3 : (3 : 𝓞 (CyclotomicField 4 ℚ) ⧸ P) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr h3
    rw [map_ofNat] at this
    exact this
  have hF : 1 + (Ideal.Quotient.mk P z) * (n : 𝓞 (CyclotomicField 4 ℚ) ⧸ P) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr hn
    rw [map_add, map_one, map_mul, map_natCast] at this
    exact this
  have hnmod : (n : 𝓞 (CyclotomicField 4 ℚ) ⧸ P) = ((n % 3 : ℕ) : 𝓞 (CyclotomicField 4 ℚ) ⧸ P) := by
    conv_lhs => rw [← Nat.div_add_mod n 3]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hF3, zero_mul, zero_add]
  rw [hnmod] at hF
  set w := Ideal.Quotient.mk P z
  have hr : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h10 : (1 : 𝓞 (CyclotomicField 4 ℚ) ⧸ P) = 0 := by
    interval_cases (n % 3)
    · simp at hF
    · simp only [Nat.cast_one, mul_one] at hF
      linear_combination hF3 - hw2 + (w - 1) * hF
    · simp only [Nat.cast_ofNat] at hF
      linear_combination (1 + w * (w + 1)) * hF3 - hw2 - (w + 1) * hF
  exact one_ne_zero h10
