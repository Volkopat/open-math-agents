import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R2
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! A modular right inverse is enough for complex surjectivity in the
first rectangular format. Separate the remaining formats by first dimension. -/
open scoped BigOperators
namespace RectangularTensorCertificate

theorem surjective_of_mod_three {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I J ℤ) (B : Matrix J I ℤ)
    (modular : A.map (Int.castRingHom (ZMod 3)) * B.map (Int.castRingHom (ZMod 3)) = 1) :
    Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
  let product := A * B
  have image : product.map (Int.castRingHom (ZMod 3)) = 1 := by
    simpa only [product, Matrix.map_mul] using modular
  have detOne : (Int.castRingHom (ZMod 3)) product.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, image, Matrix.det_one]
  have detInt : product.det ≠ 0 := by
    intro h
    rw [h,map_zero] at detOne
    exact zero_ne_one detOne
  have detComplex : (product.map (Int.castRingHom ℂ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Int.cast_ne_zero.mpr detInt
  have onto : Function.Surjective (product.map (Int.castRingHom ℂ)).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr detComplex))
  intro v
  obtain ⟨w,hw⟩ := onto v
  refine ⟨(B.map (Int.castRingHom ℂ)).mulVec w,?_⟩
  rw [Matrix.mulVec_mulVec,← Matrix.map_mul]
  exact hw

end RectangularTensorCertificate

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R2_H2_R1
open RectangularTensorCertificate

/-- A finite-field right inverse for the tangent matrix in the first rectangular format. -/
def H1 : Prop :=
  ∃ X : Fin 6 → Fin 3 → Fin 121, ∃ Y : Fin 6 → Fin 4 → Fin 121,
  ∃ Z : Fin 6 → Fin 5 → Fin 121,
  ∃ B : Matrix (Fin 6 × (Fin 3 ⊕ Fin 4 ⊕ Fin 5)) (Fin 3 × Fin 4 × Fin 5) (ZMod 3),
    let A : Matrix (Fin 3 × Fin 4 × Fin 5) (Fin 6 × (Fin 3 ⊕ Fin 4 ⊕ Fin 5)) ℤ :=
      fun (i,j,k) (t,s) ↦
        match s with
        | .inl h => if h = i then ((Y t j).val : ℤ) * ((Z t k).val : ℤ) else 0
        | .inr (.inl h) => if h = j then ((X t i).val : ℤ) * ((Z t k).val : ℤ) else 0
        | .inr (.inr h) => if h = k then ((X t i).val : ℤ) * ((Y t j).val : ℤ) else 0
    A.map (Int.castRingHom (ZMod 3)) * B = 1

theorem grid_three_four_five (modular : H1) :
    ∃ x : Fin 6 → Fin 3 → Fin 121, ∃ y : Fin 6 → Fin 4 → Fin 121,
    ∃ z : Fin 6 → Fin 5 → Fin 121, ∀ T : Fin 3 → Fin 4 → Fin 5 → ℂ,
    ∃ u : Fin 6 → Fin 3 → ℂ, ∃ v : Fin 6 → Fin 4 → ℂ, ∃ w : Fin 6 → Fin 5 → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i * (((y t j).val : ℂ) * ((z t k).val : ℂ)) +
        ((x t i).val : ℂ) * (v t j * ((z t k).val : ℂ)) +
        ((x t i).val : ℂ) * (((y t j).val : ℂ) * w t k)) := by
  obtain ⟨X,Y,Z,B,cert⟩ := modular
  let I := Fin 3 × Fin 4 × Fin 5
  let J := Fin 6 × (Fin 3 ⊕ Fin 4 ⊕ Fin 5)
  let A : Matrix I J ℤ := fun (i,j,k) (t,s) ↦
      match s with
      | .inl h => if h = i then ((Y t j).val : ℤ) * ((Z t k).val : ℤ) else 0
      | .inr (.inl h) => if h = j then ((X t i).val : ℤ) * ((Z t k).val : ℤ) else 0
      | .inr (.inr h) => if h = k then ((X t i).val : ℤ) * ((Y t j).val : ℤ) else 0
  change A.map (Int.castRingHom (ZMod 3)) * B = 1 at cert
  let BInt : Matrix J I ℤ := fun j i ↦ ((B j i).val : ℤ)
  have image : BInt.map (Int.castRingHom (ZMod 3)) = B := by
    ext j i
    change (((B j i).val : ℤ) : ZMod 3) = B j i
    rw [Int.cast_natCast,ZMod.natCast_zmod_val]
  have checked : A.map (Int.castRingHom (ZMod 3)) * BInt.map (Int.castRingHom (ZMod 3)) = 1 := by
    rwa [image]
  refine ⟨X,Y,Z,?_⟩
  intro T
  obtain ⟨g,hg⟩ := surjective_of_mod_three A BInt checked (fun (i,j,k) ↦ T i j k)
  refine ⟨fun t i ↦ g (t,.inl i),fun t j ↦ g (t,.inr (.inl j)),
    fun t k ↦ g (t,.inr (.inr k)), ?_⟩
  intro i j k
  have castEntry (p : Prop) [Decidable p] (m n : ℕ) :
      ((if p then (m : ℤ) * (n : ℤ) else 0 : ℤ) : ℂ) =
        if p then (m : ℂ) * (n : ℂ) else 0 := by
    by_cases hp : p <;> simp [hp]
  have complexA : A.map (Int.castRingHom ℂ) =
      (fun (i,j,k) (t,s) ↦
        match s with
        | .inl h => if h = i then ((Y t j).val : ℂ) * ((Z t k).val : ℂ) else 0
        | .inr (.inl h) => if h = j then ((X t i).val : ℂ) * ((Z t k).val : ℂ) else 0
        | .inr (.inr h) => if h = k then ((X t i).val : ℂ) * ((Y t j).val : ℂ) else 0) := by
    apply Matrix.ext
    intro a b
    rcases a with ⟨i,j,k⟩
    rcases b with ⟨t,b⟩
    rcases b with h | b
    · exact castEntry _ _ _
    · rcases b with h | h <;> exact castEntry _ _ _
  have eq := congrFun hg (i,j,k)
  change (∑ q : J, (A.map (Int.castRingHom ℂ)) (i,j,k) q * g q) = T i j k at eq
  rw [complexA,Fintype.sum_prod_type] at eq
  simp [Fintype.sum_sum_type,ite_mul,Finset.sum_ite_eq'] at eq
  simpa only [mul_comm,mul_left_comm,mul_assoc,add_assoc] using eq.symm

/-- Three rows, with the second factor at least five-dimensional. -/
def H2 : Prop := ∀ b c : ℕ, 5 ≤ b → b < c → c < 2*(b-1) →
    let r := 3*b*c ⌈/⌉ (3+b+c-2)
    let D := 2*(3*b*c)+1
    ∃ x : Fin r → Fin 3 → Fin D, ∃ y : Fin r → Fin b → Fin D, ∃ z : Fin r → Fin c → Fin D,
      ∀ T : Fin 3 → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin 3 → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

/-- The first factor has dimension at least four. -/
def H3 : Prop := ∀ a b c : ℕ, 4 ≤ a → a ≤ b → b < c → c < (a-1)*(b-1) →
    let r := a*b*c ⌈/⌉ (a+b+c-2)
    let D := 2*(a*b*c)+1
    ∃ x : Fin r → Fin a → Fin D, ∃ y : Fin r → Fin b → Fin D, ∃ z : Fin r → Fin c → Fin D,
      ∀ T : Fin a → Fin b → Fin c → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin c → ℂ, ∀ i j k,
          T i j k = ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
            ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k))

theorem main : H1 → H2 → H3 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R2.H2 := by
  intro modular three higher a b c ha hab hbc hbound
  by_cases eq : a=3
  · subst a
    by_cases large : 5 ≤ b
    · exact three b c large hbc hbound
    · have b4 : b = 4 := by omega
      subst b
      have c5 : c = 5 := by omega
      subst c
      exact grid_three_four_five modular
  · exact higher a b c (by omega) hab hbc hbound

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R2_H2_R1
