import OMAReductions.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1_H1_R1_H2_R1
import Mathlib
/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
The quadratic field, integrality, discriminant and real-place lemmas below are adapted
from WangFrankie/QuadraticNumberFields, revision a458ae67e9a10e91355afaebfdd55ecbceebc4bc,
under the Apache 2.0 license. The application to the prime ideals of the order is original.
-/
noncomputable section
section
lemma Squarefree.not_mul_self_dvd_of_not_isUnit {R : Type*} [Monoid R]
    {r p : R} (hr : Squarefree r) (hp : ¬ IsUnit p) : ¬ p * p ∣ r := by
  intro h
  have hp2 : p ^ 2 ∣ r := by simpa [pow_two] using h
  have hsq : Squarefree (p ^ 2) := Squarefree.squarefree_of_dvd hp2 hr
  have hbad : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
    Squarefree.eq_zero_or_one_of_pow_of_not_isUnit hsq hp
  omega
lemma squarefree_int_not_dvd_four (d : ℤ) (hd : Squarefree d) : ¬ (4 : ℤ) ∣ d := by
  intro h
  exact Squarefree.not_mul_self_dvd_of_not_isUnit hd (p := (2 : ℤ))
    (fun hunit => absurd (Int.isUnit_iff.mp hunit) (by omega)) (by simpa using h)
lemma squarefree_int_emod_four (d : ℤ) (hd : Squarefree d) :
    d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
  have hnd : ¬ (4 : ℤ) ∣ d := squarefree_int_not_dvd_four d hd
  omega
lemma eq_one_of_squarefree_isSquare {d : ℤ} (hd : Squarefree d) (hsq : IsSquare d) :
    d = 1 ∨ d = -1 := by
  obtain ⟨z, rfl⟩ := hsq
  have hsqz2 : Squarefree (z ^ 2) := by simpa [pow_two] using hd
  have huz : IsUnit z := by
    by_contra hne
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 hne
    norm_num at h01
  rcases Int.isUnit_iff.mp huz with rfl | rfl <;> simp
end

section
namespace QuadraticAlgebra

section CommSemiring

variable {R : Type*} [CommSemiring R] {a b : R}
theorem leftMulMatrix_eq (x : QuadraticAlgebra R a b) :
    Algebra.leftMulMatrix (basis a b) x = !![x.re, a * x.im; x.im, x.re + b * x.im] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    rw [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
    simp [QuadraticAlgebra.basis]

end CommSemiring
section Int

open Matrix
theorem trace_int (a b : ℤ) (x : QuadraticAlgebra ℤ a b) :
    Algebra.trace ℤ (QuadraticAlgebra ℤ a b) x = 2 * x.re + b * x.im := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b)]
  rw [leftMulMatrix_eq]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring
theorem traceMatrix_basis_int (a b : ℤ) :
    Algebra.traceMatrix ℤ (QuadraticAlgebra.basis a b) =
      !![2, b; b, 2 * a + b ^ 2] := by
  ext i j
  simp only [Algebra.traceMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [trace_int, QuadraticAlgebra.basis, pow_two]
theorem discr_basis_int (a b : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = 4 * a + b ^ 2 := by
  rw [Algebra.discr_def, traceMatrix_basis_int]
  simp [Matrix.det_fin_two]
  ring

end Int

end QuadraticAlgebra
end

section
lemma nat_eq_one_of_squarefree_intcast_of_isSquare (m : ℕ)
    (hsm : Squarefree (m : ℤ)) (hsq : IsSquare (m : ℤ)) : m = 1 := by
  have hmz : (m : ℤ) = 1 ∨ (m : ℤ) = -1 :=
    eq_one_of_squarefree_isSquare hsm hsq
  cases hmz with
  | inl h => exact_mod_cast h
  | inr h => omega
lemma int_dvd_of_ratio_square (d₁ d₂ : ℤ) (hd₂ : d₂ ≠ 0)
    (hsq_d₂ : Squarefree d₂) (hr : IsSquare ((d₁ : ℚ) / (d₂ : ℚ))) : d₂ ∣ d₁ := by
  have hsq_den_nat : IsSquare (((d₁ : ℚ) / (d₂ : ℚ)).den) := (Rat.isSquare_iff.mp hr).2
  have hsq_den_int : IsSquare ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) := by
    rcases hsq_den_nat with ⟨n, hn⟩
    refine ⟨(n : ℤ), by exact_mod_cast hn⟩
  have hden_dvd : ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) ∣ d₂ := by
    simpa [← Rat.divInt_eq_div] using (Rat.den_dvd d₁ d₂)
  have hsqf_den_int : Squarefree ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) :=
    Squarefree.squarefree_of_dvd hden_dvd hsq_d₂
  have hden1_nat : ((d₁ : ℚ) / (d₂ : ℚ)).den = 1 :=
    nat_eq_one_of_squarefree_intcast_of_isSquare _ hsqf_den_int hsq_den_int
  exact (Rat.den_div_intCast_eq_one_iff d₁ d₂ hd₂).1 hden1_nat
end

section
lemma Int.sq_emod_four_of_even (n : ℤ) (h : 2 ∣ n) : n ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ := h
  ring_nf
  omega
lemma Int.sq_emod_four_of_odd (n : ℤ) (h : ¬ 2 ∣ n) : n ^ 2 % 4 = 1 := by
  set k := n / 2
  have hk : n = 2 * k + 1 := by omega
  rw [hk]
  ring_nf
  omega

private lemma div4_iff_mod (a' b' d : ℤ) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ (a' ^ 2 - d * b' ^ 2) % 4 = 0 := by
  omega

private lemma sq_eq_four_mul_div_of_even (n : ℤ) (h : 2 ∣ n) :
    n ^ 2 = 4 * (n ^ 2 / 4) := by
  have hn2 : n ^ 2 % 4 = 0 := Int.sq_emod_four_of_even n h
  omega

private lemma sq_eq_four_mul_div_add_one_of_odd (n : ℤ) (h : ¬ 2 ∣ n) :
    n ^ 2 = 4 * (n ^ 2 / 4) + 1 := by
  have hn2 : n ^ 2 % 4 = 1 := Int.sq_emod_four_of_odd n h
  omega

private lemma odd_eq_two_mul_div_add_one (n : ℤ) (h : ¬ 2 ∣ n) :
    n = 2 * (n / 2) + 1 := by
  omega

private lemma even_odd_impossible_of_mod_eq_zero
    (d a' b' : ℤ) (hd : Squarefree d)
    (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : 2 ∣ a') (hb : ¬ 2 ∣ b') : False := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) := sq_eq_four_mul_div_of_even a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd b' hb
  rw [hb_eq] at hmod'
  ring_nf at hmod'
  have hdvd : (4 : ℤ) ∣ d := by omega
  exact squarefree_int_not_dvd_four d hd hdvd

private lemma odd_even_impossible_of_mod_eq_zero
    (d a' b' : ℤ) (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : ¬ 2 ∣ a') (hb : 2 ∣ b') : False := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) := sq_eq_four_mul_div_of_even b' hb
  rw [ha_eq, hb_eq] at hmod'
  ring_nf at hmod'
  omega

private lemma mod_four_eq_one_of_odd_odd_of_mod_eq_zero
    (d a' b' : ℤ) (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : ¬ 2 ∣ a') (hb : ¬ 2 ∣ b') : d % 4 = 1 := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd b' hb
  rw [ha_eq, hb_eq] at hmod'
  ring_nf at hmod'
  omega
theorem dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one
    (d a' b' : ℤ) (hd : Squarefree d) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔
      (2 ∣ a' ∧ 2 ∣ b') ∨ (¬ 2 ∣ a' ∧ ¬ 2 ∣ b' ∧ d % 4 = 1) := by
  constructor
  · intro hdvd
    have hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0 := (div4_iff_mod a' b' d).1 hdvd
    by_cases ha : 2 ∣ a' <;> by_cases hb : 2 ∣ b'
    · exact Or.inl ⟨ha, hb⟩
    · exact (even_odd_impossible_of_mod_eq_zero d a' b' hd hmod ha hb).elim
    · exact (odd_even_impossible_of_mod_eq_zero d a' b' hmod ha hb).elim
    · exact Or.inr ⟨ha, hb, mod_four_eq_one_of_odd_odd_of_mod_eq_zero d a' b' hmod ha hb⟩
  · intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb, hd1⟩
    · obtain ⟨p, rfl⟩ := ha
      obtain ⟨q, rfl⟩ := hb
      exact ⟨p ^ 2 - d * q ^ 2, by ring⟩
    · have ha_eq : a' = 2 * (a' / 2) + 1 := odd_eq_two_mul_div_add_one a' ha
      have hb_eq : b' = 2 * (b' / 2) + 1 := odd_eq_two_mul_div_add_one b' hb
      rw [ha_eq, hb_eq]
      ring_nf
      have hd_eq : d = 4 * (d / 4) + 1 := by omega
      rw [hd_eq]
      ring_nf
      omega
theorem even_even_of_dvd_four_sub_sq_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (h : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    2 ∣ a' ∧ 2 ∣ b' := by
  rcases (dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd).mp h with
      hab | ⟨_, _, hd1⟩
  · exact hab
  · exact absurd hd1 hd4
theorem dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · exact even_even_of_dvd_four_sub_sq_of_ne_one_mod_four d a' b' hd hd4
  · exact fun h => (dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd).2 (Or.inl h)
end

section
abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0
namespace Qsqrtd

open QuadraticAlgebra

variable {d : ℚ}

@[simp] theorem trace_eq_re_add_re_star (x : Qsqrtd d) :
    Algebra.trace ℚ (Qsqrtd d) x = x.re + (star x).re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis d 0),
    QuadraticAlgebra.leftMulMatrix_eq, Matrix.trace_fin_two_of]
  simp

theorem trace_eq_two_re (x : Qsqrtd d) :
    Algebra.trace ℚ (Qsqrtd d) x = 2 * x.re := by
  rw [trace_eq_re_add_re_star]
  simp
  ring

abbrev norm {d : ℚ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

instance instFact_of_not_isSquare (d : ℚ) [Fact (¬ IsSquare d)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ d + 0 * r) :=
  ⟨by intro r hr; exact (Fact.out : ¬ IsSquare d) ⟨r, by nlinarith [hr]⟩⟩

theorem finrank_ratAlgebra_eq_finrank_quadraticAlgebra (d : ℚ)
    [Fact (¬ IsSquare d)] :
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra) =
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ QuadraticAlgebra.instAlgebra) := by
  symm
  refine @Algebra.finrank_eq_of_equiv_equiv ℚ (Qsqrtd d) _ _
    QuadraticAlgebra.instAlgebra ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra
    (RingEquiv.refl ℚ) (RingEquiv.refl (Qsqrtd d)) ?_
  exact RingHom.ext_rat _ _

section RatAlgebra

local instance ratAlg1140 (d:ℚ) [Fact (¬IsSquare d)] : Algebra ℚ (Qsqrtd d) := DivisionRing.toRatAlgebra

theorem finrank_ratAlgebra_eq_two (d : ℚ) [Fact (¬ IsSquare d)] :
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra) = 2 := by
  rw [finrank_ratAlgebra_eq_finrank_quadraticAlgebra]
  exact QuadraticAlgebra.finrank_eq_two d 0

instance instRatAlgebraIsQuadraticExtension (d : ℚ) [Fact (¬ IsSquare d)] :
    Algebra.IsQuadraticExtension ℚ (Qsqrtd d) where
  finrank_eq_two' := finrank_ratAlgebra_eq_two d

end RatAlgebra
end Qsqrtd

lemma not_isSquare_int_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare d := by
  intro hsq
  rcases eq_one_of_squarefree_isSquare hd hsq with rfl | rfl <;> simp_all

lemma not_isSquare_ratCast_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare ((d : ℤ) : ℚ) := by
  intro hsqQ
  exact not_isSquare_int_of_squarefree_ne_one hd h1 (Rat.isSquare_intCast_iff.mp hsqQ)

instance instFact_not_isSquare_ratCast_of_squarefree_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
  ⟨not_isSquare_ratCast_of_squarefree_ne_one
    (d := d) (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩
end

section

class QuadraticField (K : Type*) [Field K] [Algebra ℚ K] : Prop where

  isQuadratic : Algebra.IsQuadraticExtension ℚ K

instance (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Algebra.IsQuadraticExtension ℚ K :=
  QuadraticField.isQuadratic

namespace QuadraticField

theorem finrank_eq_two (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Module.finrank ℚ K = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two ℚ K

end QuadraticField

instance QuadraticField.instNumberField (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] : NumberField K where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  to_finiteDimensional := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    convert FiniteDimensional.of_finrank_pos (K := ℚ) (V := K) (by
      rw [QuadraticField.finrank_eq_two K]; omega) using 1
    congr 1
    exact Subsingleton.elim _ _

namespace Qsqrtd

instance instQuadraticField (d : ℚ) [Fact (¬ IsSquare d)] :
    QuadraticField (Qsqrtd d) where
  isQuadratic := inferInstance

section RatAlgebra

local instance ratAlgB1140 (d:ℚ) [Fact (¬IsSquare d)] : Algebra ℚ (Qsqrtd d) := DivisionRing.toRatAlgebra

instance instRatAlgebraQuadraticField (d : ℚ) [Fact (¬ IsSquare d)] :
    QuadraticField (Qsqrtd d) where
  isQuadratic := @Qsqrtd.instRatAlgebraIsQuadraticExtension d _

end RatAlgebra

end Qsqrtd
end

section
namespace QuadraticNumberFields

abbrev Zsqrtd (d : ℤ) : Type := QuadraticAlgebra ℤ d 0

namespace Zsqrtd

variable {d : ℤ}
theorem ext {x y : Zsqrtd d} (hre : x.re = y.re) (him : x.im = y.im) : x = y :=
  QuadraticAlgebra.ext hre him

def toQsqrtd (z : Zsqrtd d) : Qsqrtd (d : ℚ) := ⟨(z.re : ℚ), (z.im : ℚ)⟩

def toQsqrtdHom (d : ℤ) : Zsqrtd d →+* Qsqrtd (d : ℚ) where
  toFun := fun z => ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_one' := by
    change ({ re := ((1 : ℤ) : ℚ), im := ((0 : ℤ) : ℚ) } : Qsqrtd (d : ℚ)) = 1
    rfl
  map_mul' := by
    intro x y
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm]
  map_zero' := by
    change ({ re := ((0 : ℤ) : ℚ), im := ((0 : ℤ) : ℚ) } : Qsqrtd (d : ℚ)) = 0
    rfl
  map_add' := by
    intro x y
    ext <;> simp

@[simp] theorem toQsqrtdHom_apply (d : ℤ) (z : Zsqrtd d) :
    toQsqrtdHom d z = toQsqrtd z := rfl

theorem toQsqrtdHom_injective (d : ℤ) : Function.Injective (toQsqrtdHom d) := by
  intro x y hxy
  ext
  · simpa [toQsqrtdHom] using congrArg QuadraticAlgebra.re hxy
  · simpa [toQsqrtdHom] using congrArg QuadraticAlgebra.im hxy

def halfInt (a' b' : ℤ) : Qsqrtd (d : ℚ) :=
  ⟨(a' : ℚ) / 2, (b' : ℚ) / 2⟩

theorem halfInt_mem_range_toQsqrtdHom_iff_even_even (d a' b' : ℤ) :
    (∃ z : Zsqrtd d, toQsqrtdHom d z = halfInt (d := d) a' b') ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · rintro ⟨z, hz⟩
    have hm : (a' : ℚ) / 2 = z.re := by
      simpa [toQsqrtdHom, halfInt] using congrArg QuadraticAlgebra.re hz.symm
    have hn : (b' : ℚ) / 2 = z.im := by
      simpa [toQsqrtdHom, halfInt] using congrArg QuadraticAlgebra.im hz.symm
    refine ⟨?_, ?_⟩
    · refine ⟨z.re, ?_⟩
      have hq : (a' : ℚ) = 2 * z.re := by nlinarith [hm]
      exact_mod_cast hq
    · refine ⟨z.im, ?_⟩
      have hq : (b' : ℚ) = 2 * z.im := by nlinarith [hn]
      exact_mod_cast hq
  · rintro ⟨ha, hb⟩
    rcases ha with ⟨m, hm⟩
    rcases hb with ⟨n, hn⟩
    refine ⟨⟨m, n⟩, ?_⟩
    ext <;> simp [toQsqrtdHom, halfInt, hm, hn]
end Zsqrtd
end QuadraticNumberFields
end

section
namespace QuadraticNumberFields
namespace RingOfIntegers

abbrev halfInt (d : ℤ) (a' b' : ℤ) : Qsqrtd (d : ℚ) :=
  Zsqrtd.halfInt (d := d) a' b'

abbrev omegaHalf (d : ℤ) : Qsqrtd (d : ℚ) := halfInt d 1 1

@[simp] theorem halfInt_re (d a' b' : ℤ) :
    (halfInt d a' b').re = (a' : ℚ) / 2 := rfl

@[simp] theorem halfInt_im (d a' b' : ℤ) :
    (halfInt d a' b').im = (b' : ℚ) / 2 := rfl

theorem norm_halfInt (d a' b' : ℤ) :
    Qsqrtd.norm (halfInt d a' b') = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := by
  simp [halfInt, Qsqrtd.norm, QuadraticAlgebra.norm]
  ring

end RingOfIntegers
end QuadraticNumberFields
end

section
namespace QuadraticNumberFields
namespace RingOfIntegers
namespace TraceNorm

namespace Qsqrtd

theorem add_star_eq_trace_image {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    x + star x =
      algebraMap ℚ (Qsqrtd (d : ℚ)) (Algebra.trace ℚ (Qsqrtd (d : ℚ)) x) := by
  ext
  · simp [Qsqrtd.trace_eq_re_add_re_star, star]
  · simp [star]

theorem norm_image_eq_mul_star {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    algebraMap ℚ (Qsqrtd (d : ℚ)) (Qsqrtd.norm x) = x * star x := by
  simpa [Qsqrtd.norm, mul_comm] using
    (QuadraticAlgebra.algebraMap_norm_eq_mul_star (a := (d : ℚ)) (b := (0 : ℚ)) x)

end Qsqrtd

private lemma isIntegral_star {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (star x) :=
  map_isIntegral_int (starRingEnd (Qsqrtd (d : ℚ))) hx

theorem norm_eq_sqr_minus_d_sqr {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    Qsqrtd.norm x = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := by
  simp [Qsqrtd.norm, QuadraticAlgebra.norm]
  ring

private lemma isIntegral_trace_image {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (algebraMap ℚ (Qsqrtd (d : ℚ)) (Algebra.trace ℚ (Qsqrtd d) x)) := by
  simpa [Qsqrtd.add_star_eq_trace_image x] using hx.add (isIntegral_star hx)

private lemma isIntegral_trace {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (Algebra.trace ℚ (Qsqrtd d) x) :=
  (isIntegral_algHom_iff (algebraMap ℚ (Qsqrtd (d : ℚ))).toIntAlgHom
    (algebraMap ℚ (Qsqrtd (d : ℚ))).injective).1 (isIntegral_trace_image hx)

lemma exists_int_trace {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ a' : ℤ, (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x := by
  obtain ⟨a', ha'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1
    (isIntegral_trace hx)
  exact ⟨a', by simpa using ha'⟩

private lemma isIntegral_norm_image {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (algebraMap ℚ (Qsqrtd (d : ℚ)) (Qsqrtd.norm x)) := by
  simpa [Qsqrtd.norm_image_eq_mul_star x] using hx.mul (isIntegral_star hx)

private lemma isIntegral_norm {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (Qsqrtd.norm x) :=
  (isIntegral_algHom_iff (algebraMap ℚ (Qsqrtd (d : ℚ))).toIntAlgHom
    (algebraMap ℚ (Qsqrtd (d : ℚ))).injective).1 (isIntegral_norm_image hx)

lemma exists_int_norm {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ n' : ℤ, (n' : ℚ) = Qsqrtd.norm x := by
  obtain ⟨n', hn'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1
    (isIntegral_norm hx)
  exact ⟨n', by simpa using hn'⟩

lemma re_eq_half_trace_int {d : ℤ} {x : Qsqrtd (d : ℚ)} {a' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x) :
    x.re = (a' : ℚ) / 2 := by
  nlinarith [show 2 * x.re = (a' : ℚ) by
    calc
      2 * x.re = Algebra.trace ℚ (Qsqrtd d) x := (Qsqrtd.trace_eq_two_re x).symm
      _ = (a' : ℚ) := ha'trace.symm]

lemma isIntegral_of_sq_int {q : ℚ} {k : ℤ} (hq2 : q ^ 2 = (k : ℚ)) :
    IsIntegral ℤ q := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C k,
    Polynomial.monic_X_pow_sub_C (R := ℤ) (n := 2) k (by decide), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp [hq2]

private lemma double_im_sq_mul_eq
    (d : ℤ) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (d : ℚ) * (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) := by
  have hre : x.re = (a' : ℚ) / 2 := re_eq_half_trace_int ha'trace
  have hnorm' :
      (n' : ℚ) = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by
    calc
      (n' : ℚ) = Qsqrtd.norm x := hn'norm
      _ = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := norm_eq_sqr_minus_d_sqr x
      _ = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by simp [hre]
  have haux : (a' : ℚ) ^ 2 - 4 * (n' : ℚ) = 4 * (d : ℚ) * x.im ^ 2 := by
    nlinarith [hnorm']
  have hmcast : ((a' ^ 2 - 4 * n' : ℤ) : ℚ) = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by
    norm_cast
  calc
    (d : ℚ) * (2 * x.im) ^ 2 = 4 * (d : ℚ) * x.im ^ 2 := by ring
    _ = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by linarith [haux]
    _ = (a' ^ 2 - 4 * n' : ℤ) := hmcast.symm

private lemma double_im_sq_eq_ratio
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) := by
  calc
    (2 * x.im) ^ 2 = ((d : ℚ) * (2 * x.im) ^ 2) / (d : ℚ) := by field_simp [hd0Q]
    _ = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) := by
      simp [double_im_sq_mul_eq d ha'trace hn'norm]

private lemma isSquare_trace_norm_ratio
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    IsSquare ((a' ^ 2 - 4 * n' : ℤ) / (d : ℚ)) :=
  ⟨2 * x.im, by simpa [pow_two] using (double_im_sq_eq_ratio d hd0Q ha'trace hn'norm).symm⟩

private lemma dvd_trace_norm_delta
    (d : ℤ) (hd0 : d ≠ 0) (hd_sf : Squarefree d) (hd0Q : (d : ℚ) ≠ 0)
    {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    d ∣ (a' ^ 2 - 4 * n') :=
  int_dvd_of_ratio_square (a' ^ 2 - 4 * n') d hd0 hd_sf
    (isSquare_trace_norm_ratio d hd0Q ha'trace hn'norm)

private lemma double_im_sq_eq_int
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' k : ℤ}
    (hk : a' ^ 2 - 4 * n' = d * k)
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (2 * x.im) ^ 2 = (k : ℚ) := by
  have hmk : ((a' ^ 2 - 4 * n' : ℤ) : ℚ) = (d : ℚ) * k := by
    exact_mod_cast hk
  calc
    (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) :=
      double_im_sq_eq_ratio d hd0Q ha'trace hn'norm
    _ = ((d : ℚ) * k) / (d : ℚ) := by simp [hmk]
    _ = (k : ℚ) := by field_simp [hd0Q]

private lemma exists_int_of_isIntegral_rat {q : ℚ} (hq : IsIntegral ℤ q) :
    ∃ b' : ℤ, (b' : ℚ) = q := by
  obtain ⟨b', hb'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hq
  exact ⟨b', by simpa using hb'⟩

private lemma im_eq_half_of_double_im_eq {d : ℤ} {x : Qsqrtd (d : ℚ)} {b' : ℤ}
    (hb' : (b' : ℚ) = 2 * x.im) :
    x.im = (b' : ℚ) / 2 := by
  nlinarith [hb']

lemma exists_int_double_im
    (d : ℤ) (hd_sf : Squarefree d) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    ∃ b' : ℤ, x.im = (b' : ℚ) / 2 := by
  have hd0 : d ≠ 0 := hd_sf.ne_zero
  have hd0Q : (d : ℚ) ≠ 0 := by
    exact_mod_cast hd0
  rcases dvd_trace_norm_delta d hd0 hd_sf hd0Q ha'trace hn'norm with ⟨k, hk⟩
  rcases exists_int_of_isIntegral_rat
      (isIntegral_of_sq_int (double_im_sq_eq_int d hd0Q hk ha'trace hn'norm)) with
    ⟨b', hb'⟩
  exact ⟨b', im_eq_half_of_double_im_eq hb'⟩

lemma dvd_four_sub_sq_of_norm_eq_int
    (a' b' d n' : ℤ)
    (hnorm :
      (n' : ℚ) = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ))) :
    (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) :=
  (Rat.den_div_intCast_eq_one_iff (a' ^ 2 - d * b' ^ 2) 4 (by norm_num)).1 <| by
    rw [← hnorm]
    simp

end TraceNorm
end RingOfIntegers
end QuadraticNumberFields
end

section
namespace QuadraticNumberFields
namespace RingOfIntegers

open scoped NumberField

section RingOfIntegersEquiv

noncomputable def ringOfIntegers_equiv_of_integralClosure
    (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    𝓞 K ≃+* R :=
  NumberField.RingOfIntegers.equiv (K := K) (R := R)

@[simp]
lemma ringOfIntegers_equiv_of_integralClosure_apply
    {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K]
    (α : 𝓞 K) :
    algebraMap R K (ringOfIntegers_equiv_of_integralClosure K R α) = (algebraMap (𝓞 K) K) α := by
  change algebraMap R K ((IsIntegralClosure.equiv ℤ R K (𝓞 K)).symm α) =
    algebraMap (𝓞 K) K α
  have key := IsIntegralClosure.algebraMap_equiv ℤ R K (𝓞 K)
    ((IsIntegralClosure.equiv ℤ R K (𝓞 K)).symm α)
  rw [(IsIntegralClosure.equiv ℤ R K (𝓞 K)).apply_symm_apply α] at key
  exact key.symm

noncomputable def ringOfIntegers_equiv_of_embedding
    (K : Type*) [Field K]
    (R : Type*) [CommRing R]
    (φ : R →+* K)
    (h_inj : Function.Injective φ)
    (h_exists : ∀ x : K, IsIntegral ℤ x → ∃ z : R, φ z = x)
    (h_integral : ∀ z : R, IsIntegral ℤ (φ z)) :
    𝓞 K ≃+* R :=
  letI : Algebra R K := φ.toAlgebra
  letI : IsIntegralClosure R ℤ K :=
    { algebraMap_injective := by
        exact h_inj
      isIntegral_iff := by
        intro x
        refine ⟨fun hx => ?_, ?_⟩
        · rcases h_exists x hx with ⟨z, hz⟩
          exact ⟨z, hz⟩
        · rintro ⟨z, rfl⟩
          exact h_integral z }
  ringOfIntegers_equiv_of_integralClosure K R

lemma ringOfIntegers_equiv_of_embedding_apply
    {K : Type*} [Field K]
    {R : Type*} [CommRing R]
    (φ : R →+* K)
    (h_inj : Function.Injective φ)
    (h_exists : ∀ x : K, IsIntegral ℤ x → ∃ z : R, φ z = x)
    (h_integral : ∀ z : R, IsIntegral ℤ (φ z))
    (α : 𝓞 K) :
    φ (ringOfIntegers_equiv_of_embedding K R φ h_inj h_exists h_integral α) = (α : K) := by
  letI : Algebra R K := φ.toAlgebra
  letI : IsIntegralClosure R ℤ K :=
    { algebraMap_injective := h_inj
      isIntegral_iff := by
        intro x
        refine ⟨fun hx => ?_, ?_⟩
        · rcases h_exists x hx with ⟨z, hz⟩
          exact ⟨z, hz⟩
        · rintro ⟨z, rfl⟩
          exact h_integral z }
  change algebraMap R K _ = algebraMap (𝓞 K) K α
  exact ringOfIntegers_equiv_of_integralClosure_apply (R := R) α

end RingOfIntegersEquiv

theorem dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔
      ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b' := by
  rw [dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four d a' b' hd hd4,
    (Zsqrtd.halfInt_mem_range_toQsqrtdHom_iff_even_even d a' b').symm]

theorem exists_zsqrtd_image_of_dvd_four_sub_sq_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (hdiv : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b' :=
  (dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four d a' b' hd hd4).1 hdiv
private lemma isIntegral_of_intModel_image
    (R S : Type*) [CommRing R] [CommRing S]
    [Algebra.IsIntegral ℤ R] (φ : R →+* S) (z : R) :
    IsIntegral ℤ (φ z) :=
  map_isIntegral_int φ (Algebra.IsIntegral.isIntegral (R := ℤ) z)

lemma isIntegral_toQsqrtd (d : ℤ) (z : Zsqrtd d) :
    IsIntegral ℤ (Zsqrtd.toQsqrtdHom d z) :=
  isIntegral_of_intModel_image (Zsqrtd d) (Qsqrtd (d : ℚ)) (Zsqrtd.toQsqrtdHom d) z

private lemma eq_halfInt_of_re_im
    (d a' b' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hre : x.re = (a' : ℚ) / 2) (him : x.im = (b' : ℚ) / 2) :
    x = Zsqrtd.halfInt (d := d) a' b' := by
  ext <;> simp [Zsqrtd.halfInt, hre, him]

private lemma int_norm_eq_norm_halfInt
    (d a' b' n' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hxHalf : x = Zsqrtd.halfInt (d := d) a' b')
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (n' : ℚ) = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by
  calc
    (n' : ℚ) = Qsqrtd.norm x := hn'norm
    _ = Qsqrtd.norm (Zsqrtd.halfInt (d := d) a' b') := by simp [hxHalf]
    _ = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := norm_halfInt d a' b'
    _ = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by norm_num

private lemma dvd_four_sub_sq_of_int_norm_halfInt
    (d a' b' n' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hxHalf : x = Zsqrtd.halfInt (d := d) a' b')
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) :=
  TraceNorm.dvd_four_sub_sq_of_norm_eq_int a' b' d n'
    (int_norm_eq_norm_halfInt d a' b' n' hxHalf hn'norm)

lemma exists_halfInt_with_div_four_of_isIntegral
    (d : ℤ) (hd_sf : Squarefree d) (_hd_ne : d ≠ 1)
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ a' b' : ℤ,
      x = Zsqrtd.halfInt (d := d) a' b' ∧
      (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) := by
  obtain ⟨a', ha'trace⟩ := TraceNorm.exists_int_trace hx
  obtain ⟨n', hn'norm⟩ := TraceNorm.exists_int_norm hx
  obtain ⟨b', him⟩ := TraceNorm.exists_int_double_im d hd_sf ha'trace hn'norm
  have hxHalf : x = Zsqrtd.halfInt (d := d) a' b' :=
    eq_halfInt_of_re_im d a' b'
      (TraceNorm.re_eq_half_trace_int ha'trace) him
  exact ⟨a', b', hxHalf, dvd_four_sub_sq_of_int_norm_halfInt d a' b' n' hxHalf hn'norm⟩

private lemma exists_intModel_of_isIntegral
    (d : ℤ) (hd_sf : Squarefree d) (hd_ne : d ≠ 1)
    (R : Type*) [CommRing R]
    (φ : R →+* Qsqrtd (d : ℚ))
    (h_lift :
      ∀ a' b' : ℤ, 4 ∣ (a' ^ 2 - d * b' ^ 2) →
        ∃ z : R, φ z = Zsqrtd.halfInt (d := d) a' b')
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ z : R, φ z = x := by
  rcases exists_halfInt_with_div_four_of_isIntegral d hd_sf hd_ne (x := x) hx with
    ⟨a', b', hxHalf, hdiv⟩
  rcases h_lift a' b' hdiv with ⟨z, hz⟩
  exact ⟨z, by simpa [hxHalf] using hz⟩

lemma exists_zsqrtd_of_isIntegral_of_ne_one_mod_four
    (d : ℤ) (hd_sf : Squarefree d) (hd_ne : d ≠ 1) (hd4 : d % 4 ≠ 1)
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = x :=
  exists_intModel_of_isIntegral d hd_sf hd_ne (Zsqrtd d) (Zsqrtd.toQsqrtdHom d)
    (fun a' b' hdiv =>
      exists_zsqrtd_image_of_dvd_four_sub_sq_of_ne_one_mod_four d a' b' hd_sf hd4 hdiv)
    hx
end RingOfIntegers
end QuadraticNumberFields
end

section
open scoped NumberField

namespace QuadraticNumberFields
namespace RingOfIntegers

section SquarefreeIntegerParameter

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

noncomputable def ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    𝓞 (Qsqrtd (d : ℚ)) ≃+* Zsqrtd d :=
  let hd_sf : Squarefree d := Fact.out
  let hd_ne : d ≠ 1 := Fact.out
  ringOfIntegers_equiv_of_embedding (Qsqrtd (d : ℚ)) (Zsqrtd d)
    (Zsqrtd.toQsqrtdHom d)
    (Zsqrtd.toQsqrtdHom_injective d)
    (fun _ hx => exists_zsqrtd_of_isIntegral_of_ne_one_mod_four d hd_sf hd_ne hd4 hx)
    (fun z => isIntegral_toQsqrtd d z)

end SquarefreeIntegerParameter

end RingOfIntegers
end QuadraticNumberFields
end

section
open scoped NumberField
namespace QuadraticNumberFields.RingOfIntegers

open Module

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

def ringEquivToIntAlgEquiv {R S : Type*} [CommRing R] [Algebra ℤ R]
    [CommRing S] [Algebra ℤ S] (e : R ≃+* S) : R ≃ₐ[ℤ] S :=
  AlgEquiv.ofRingEquiv (f := e) fun n => by
    simp only [eq_intCast, map_intCast]

end QuadraticNumberFields.RingOfIntegers
end
end

/-! The integral basis and descent are adapted from the merged sibling proof
`Erdos1140.erdos_1140.variants.at_most_one_exception.R1.H1.R1.H1`.
A split prime of norm p < t, together with the ideal of norm 2, rules out
class number two. A descent with the unit t + √(t²+1) shows that every absolute
norm below 2t is a square. -/
namespace NearSquareFinite
open NumberField Ideal
open scoped nonZeroDivisors

private def witnesses : List (ℕ × ℕ) :=
  [(7,3), (11,2), (11,4), (13,2), (13,6), (17,3), (17,4), (17,6),
   (19,6), (19,9), (23,3), (29,6), (37,11)]

/-- The additional square tests record both signs of the norm obstruction for
second coordinate one. Since p < t, the natural subtraction here is exact. -/
private def betweenSquares (t v : ℕ) : Bool :=
  (List.range 10).any fun i =>
    let k := t-5+i
    decide (k^2 < v ∧ v < (k+1)^2)

private def squareTests (t p : ℕ) : Bool :=
  let d := t^2+1
  decide (p^2*(2*t+1) < (4*t-p)^2 ∧ d % p ≠ 0) &&
    betweenSquares t (d+p^2) && betweenSquares t (d-p^2)

private def hasFactor (ds : List ℕ) (m : ℕ) : Bool :=
  ds.any fun d => decide (1 < d ∧ d < m ∧ m % d = 0)

private lemma prime_hasFactor {m : ℕ} (hm : m.Prime) (ds : List ℕ) : hasFactor ds m = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨d, _, hd⟩ := List.any_eq_true.mp h
  obtain ⟨lo, hi, div⟩ := of_decide_eq_true hd
  have := hm.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero div)
  omega

private def valid (t : ℕ) : Bool :=
  decide (t ≤ 19 ∨ 3045 < t) || hasFactor [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53] t ||
  witnesses.any (fun (p,r) => decide (p < t ∧ r^2 % p = (t^2+1) % p ∧ squareTests t p = true)) ||
  hasFactor [5,13,17,29,101,113,229] ((t^2+1)/2)

private def checkBlock (lo : ℕ) : ℕ → Bool
  | 0 => valid lo
  | k+1 => checkBlock lo k && checkBlock (lo+2^k) k

private lemma checkBlock_spec (k lo t : ℕ) (ok : checkBlock lo k = true)
    (h₁ : lo ≤ t) (h₂ : t < lo + 2^k) : valid t = true := by
  induction k generalizing lo with
  | zero =>
    have : t = lo := by simp at h₂; omega
    simpa only [this, checkBlock] using ok
  | succ k ih =>
    simp only [checkBlock, Bool.and_eq_true] at ok
    rw [pow_succ] at h₂
    by_cases hm : t < lo+2^k
    · exact ih lo ok.1 h₁ hm
    · exact ih (lo+2^k) ok.2 (by omega) (by omega)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
private lemma checked : checkBlock 0 12 = true := by decide

private lemma split_witness {t n : ℕ} (hl : 19 < t) (hu : t ≤ 3045)
    (ht : t.Prime) (hn : n.Prime) (hs : 2*n = t^2+1) :
    ∃ p : ℕ, 0 < p ∧ p < t ∧ (Nat.sqrt p)^2 ≠ p ∧ (Nat.sqrt (2*p))^2 ≠ 2*p ∧
        ∃ r : ZMod p, r^2 = ((t^2+1 : ℕ) : ZMod p) := by
  have ok := checkBlock_spec 12 0 t checked (Nat.zero_le t) (by norm_num; omega)
  have hn' : ((t^2+1)/2).Prime := by rwa [← hs, Nat.mul_div_cancel_left _ (by decide)]
  simp [valid, Nat.not_le.mpr hl, Nat.not_lt.mpr hu, prime_hasFactor ht, prime_hasFactor hn'] at ok
  obtain ⟨p,r,mem,lt,modEq,_⟩ := ok
  have facts : ∀ u ∈ witnesses, u.1.Prime ∧ u.1 % 2 = 1 ∧ u.2 < u.1 ∧ u.1 ≤ 37 ∧ 0 < u.1 ∧ (Nat.sqrt u.1)^2 ≠ u.1 ∧
      (Nat.sqrt (2*u.1))^2 ≠ 2*u.1 := by decide +kernel
  obtain ⟨_, _, _, _, hp, h₁, h₂⟩ := facts (p,r) mem
  refine ⟨p,hp,lt,h₁,h₂,(r : ZMod p),?_⟩
  simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff' _ _ _).mpr modEq

/-- Descent lowers the second coordinate whenever the absolute norm is below 2t. -/
private lemma small_norm_square {t m : ℕ} (ht : 2 ≤ t) (hm : m < 2*t) (x y : ℤ)
    (h : (x^2 - ((t:ℤ)^2+1)*y^2).natAbs = m) : (Nat.sqrt m)^2 = m := by
  have go : ∀ b a : ℕ, ((a:ℤ)^2-((t:ℤ)^2+1)*(b:ℤ)^2).natAbs = m → (Nat.sqrt m)^2 = m := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro a eq
      by_cases bz : b = 0
      · subst b
        have base : a^2 = m := by simpa [Int.natAbs_pow] using eq
        simp [← base]
      have bpos : (1:ℤ) ≤ b := by omega
      have tpos : (2:ℤ) ≤ t := by omega
      have mlt : (m:ℤ) < 2*t := by exact_mod_cast hm
      have b2 : (1:ℤ) ≤ (b:ℤ)^2 := by nlinarith
      have gap := mul_le_mul_of_nonneg_left b2 (by positivity : (0:ℤ) ≤ t)
      have e : (a:ℤ)^2-((t:ℤ)^2+1)*(b:ℤ)^2 = m ∨
          (a:ℤ)^2-((t:ℤ)^2+1)*(b:ℤ)^2 = -(m:ℤ) := by omega
      have lo : ((t:ℤ)-1)*b < a := by
        by_contra! hh
        have := (sq_le_sq₀ (by positivity : (0:ℤ)≤a)
          (mul_nonneg (by omega) (by positivity) : 0≤((t:ℤ)-1)*b)).mpr hh
        rcases e with e|e <;> nlinarith
      have hi : (a:ℤ) < ((t:ℤ)+1)*b := by
        by_contra! hh
        have := (sq_le_sq₀ (by positivity : (0:ℤ)≤((t:ℤ)+1)*b)
          (by positivity : (0:ℤ)≤a)).mpr hh
        rcases e with e|e <;> nlinarith
      let A : ℤ := ((t:ℤ)^2+1)*b-t*a
      let B : ℤ := t*b-a
      have bsmall : B.natAbs < b := by dsimp [B]; ring_nf at lo hi; omega
      apply ih B.natAbs bsmall A.natAbs
      have E : A^2-((t:ℤ)^2+1)*B^2 = -((a:ℤ)^2-((t:ℤ)^2+1)*(b:ℤ)^2) := by
        dsimp [A,B]; ring
      simpa only [Int.natCast_natAbs,sq_abs] using
        (show (A^2-((t:ℤ)^2+1)*B^2).natAbs = m by rw [E,Int.natAbs_neg,eq])
  exact go y.natAbs x.natAbs (by simpa only [Int.natCast_natAbs,sq_abs] using h)

private lemma split_ideal {K : Type} [Field K] [NumberField K] {d : ℤ}
    (j : QuadraticAlgebra ℤ d 0 ≃ₐ[ℤ] 𝓞 K) {p : ℕ} (hp : 0 < p)
    (r : ZMod p) (hr : r^2 = (d : ZMod p)) :
    ∃ I : (Ideal (𝓞 K))⁰, I.val.absNorm = p := by
  letI : NeZero p := ⟨hp.ne'⟩
  let h : QuadraticAlgebra ℤ d 0 →ₐ[ℤ] ZMod p :=
    QuadraticAlgebra.lift ⟨r, by simpa [← pow_two, zsmul_eq_mul] using hr⟩
  let f := h.toRingHom.comp j.symm.toRingHom
  have sur : Function.Surjective f := fun z => ⟨(z.val : ℕ), by simp⟩
  have size : (RingHom.ker f).absNorm = p :=
    (Nat.card_congr (f.quotientKerEquivOfSurjective sur).toEquiv).trans
      (by simp [Nat.card_eq_fintype_card])
  exact ⟨⟨RingHom.ker f, Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mp (by omega)⟩,size⟩

private lemma principal_norm_square {K : Type} [Field K] [NumberField K] {t : ℕ}
    (ht : 2 ≤ t) {d : ℤ} (form : d=(t:ℤ)^2+1) (j : QuadraticAlgebra ℤ d 0 ≃ₐ[ℤ] 𝓞 K)
    {I : Ideal (𝓞 K)} {m : ℕ} (norm : I.absNorm=m) (hm : m<2*t)
    (princ : I.IsPrincipal) : (Nat.sqrt m)^2 = m := by
  obtain ⟨x,hx⟩ := princ
  obtain ⟨⟨a,b⟩,rfl⟩ := j.surjective x
  rw [submodule_span_eq] at hx
  have coord : Algebra.norm ℤ (j ⟨a,b⟩) = a^2-d*b^2 := by
    rw [Algebra.norm_eq_of_algEquiv j, Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis d 0),
        QuadraticAlgebra.leftMulMatrix_eq, Matrix.det_fin_two]
    simp; ring
  apply small_norm_square ht hm a b
  simpa only [hx,Ideal.absNorm_span_singleton,coord,form] using norm

private lemma classification (n t : ℕ) (pn : n.Prime) (pt : t.Prime) (ot : Odd t)
    (shape : 2*n=t^2+1) (bound : t≤3045)
    (K : Type) [Field K] [NumberField K] (s : K) (hs : s^2=((t^2+1 : ℕ) : K))
    (gen : Algebra.adjoin ℚ ({s}:Set K)=⊤) (cl : NumberField.classNumber K=2) : t≤19 := by
  classical
  by_contra! large
  obtain ⟨p,hp,plt,nsP,ns2P,r,hr⟩ := split_witness large bound pt pn shape
  have oddn : n%2=1 := by
    obtain ⟨u,e⟩ := ot
    rw [e] at shape
    have he : n=2*u^2+2*u+1 := by nlinarith
    omega
  let d : ℤ := 2*n
  have sf : Squarefree (2*n) :=
    (Nat.squarefree_mul (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))).mpr
      ⟨Nat.prime_two.squarefree,pn.squarefree⟩
  letI : Fact (Squarefree d) := ⟨by dsimp [d]; exact_mod_cast (Int.squarefree_natCast.mpr sf)⟩
  letI : Fact (d≠1) := ⟨by dsimp [d]; omega⟩
  have md : d%4≠1 := by dsimp [d]; omega
  have form : d=(t:ℤ)^2+1 := by dsimp [d]; exact_mod_cast shape
  let g : Qsqrtd (d:ℚ) →ₐ[ℚ] K := QuadraticAlgebra.lift ⟨s, by
    simpa [← pow_two, Algebra.smul_def, form] using hs⟩
  have sg : s ∈ g.range := ⟨QuadraticAlgebra.omega, by simp [g, QuadraticAlgebra.lift]⟩
  have onto : Function.Surjective g := by
    have inc : Algebra.adjoin ℚ ({s}:Set K) ≤ g.range := Algebra.adjoin_le (by simpa using sg)
    rw [gen] at inc
    exact fun x => inc (show x∈(⊤ : Subalgebra ℚ K) from trivial)
  let e := RingEquiv.ofBijective g.toRingHom ⟨g.injective,onto⟩
  let q := QuadraticNumberFields.RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d md
  let j : QuadraticAlgebra ℤ d 0 ≃ₐ[ℤ] 𝓞 K := QuadraticNumberFields.RingOfIntegers.ringEquivToIntAlgEquiv
    (q.symm.trans (NumberField.RingOfIntegers.mapRingEquiv e))
  obtain ⟨P,nP⟩ := split_ideal j hp r (by simpa [form] using hr)
  obtain ⟨Q,nQ⟩ := split_ideal j (p:=2) (by decide) 0 (by simp [d, show (2:ZMod 2)=0 from rfl])
  have hcard : Nat.card (ClassGroup (𝓞 K)) = 2 := by rwa [Nat.card_eq_fintype_card]
  obtain ⟨u,_,uniq⟩ := (Nat.card_eq_two_iff' 1).mp hcard
  have hP : ClassGroup.mk0 P ≠ 1 := fun h => nsP (principal_norm_square (by omega) form j nP
    (by omega) ((ClassGroup.mk0_eq_one_iff P.prop).mp h))
  have hQ : ClassGroup.mk0 Q ≠ 1 := by
    intro h
    have := principal_norm_square (by omega) form j nQ (by omega) ((ClassGroup.mk0_eq_one_iff Q.prop).mp h)
    norm_num at this
  have same : ClassGroup.mk0 Q = (ClassGroup.mk0 P)⁻¹ :=
    (uniq _ hQ).trans (uniq _ (by simpa using hP)).symm
  obtain ⟨x,_,hx⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp same
  apply ns2P
  apply principal_norm_square (by omega) form j (I:=Q.val*P.val)
  · rw [map_mul,nQ,nP]
  · omega
  · exact ⟨x,hx⟩

end NearSquareFinite

theorem OMA.solution : OMA.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1_H1_R1_H2_R1.H2 := NearSquareFinite.classification
