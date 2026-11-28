import OMAStatements.S_oeis_a003477
import Mathlib

/-!
# Disproof of the stated A003477 identity at n = 4

The first terms are a = 1, 3, 6, 14, 33 and b = 1, 3, 6, 12, 25. At n = 4 the
statement asks 33 = 25 + 2 * a(1) = 31. Arie Bos's conjecture (OEIS A003477,
Nov 29 2019) omits the term a(0) from the sum; the generating functions give
a(n) = b(n) + 2 * (a(0) + ... + a(n-3)) instead, so the stated form is off by 2.
-/

namespace OMA.P_oeis_a003477

open PowerSeries Finset

noncomputable def cm : ℤ⟦X⟧ := (1 - C 2 * X) * (1 + X ^ 2)
noncomputable def f1 : ℤ⟦X⟧ := 1 - X - C 2 * X ^ 3
noncomputable def f2 : ℤ⟦X⟧ := 1 - X
noncomputable def s1 : ℤ⟦X⟧ := invOfUnit (cm * f1) 1
noncomputable def s2 : ℤ⟦X⟧ := invOfUnit (cm * f2) 1

lemma a_eq (n : ℕ) : OMA.S_oeis_a003477.a n = coeff n s1 := rfl
lemma b_eq (n : ℕ) : OMA.S_oeis_a003477.b n = coeff n s2 := rfl

lemma s1_mul : s1 * (cm * f1) = 1 := by
  unfold s1
  apply invOfUnit_mul
  simp [cm, f1]

lemma s2_mul : s2 * (cm * f2) = 1 := by
  unfold s2
  apply invOfUnit_mul
  simp [cm, f2]

lemma vals : coeff 1 s1 = 3 ∧ coeff 4 s1 = 33 ∧ coeff 4 s2 = 25 := by
  have h1 := s1_mul
  have h2 := s2_mul
  simp only [cm, f1, f2, map_ofNat] at h1 h2
  ring_nf at h1 h2
  have g := fun n => And.intro (congrArg (coeff n) h1) (congrArg (coeff n) h2)
  obtain ⟨a0, b0⟩ := g 0
  obtain ⟨a1, b1⟩ := g 1
  obtain ⟨a2, b2⟩ := g 2
  obtain ⟨a3, b3⟩ := g 3
  obtain ⟨a4, b4⟩ := g 4
  simp [coeff_X_pow, coeff_X, ← map_ofNat C, coeff_mul_C, coeff_X_pow_mul',
    coeff_mul_X_pow', -eq_intCast, coeff_one] at a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  refine ⟨?_, ?_, ?_⟩ <;> linarith

end OMA.P_oeis_a003477

open OMA.P_oeis_a003477 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a003477.main) := by
  intro h
  have h4 := h 4 le_rfl
  simp only [a_eq, b_eq, show 4 - 3 = 1 from rfl, Finset.sum_range_one, zero_add] at h4
  obtain ⟨v1, v4, w4⟩ := vals
  rw [v4, w4, v1] at h4
  norm_num at h4
