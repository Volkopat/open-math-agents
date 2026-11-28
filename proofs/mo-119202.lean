import OMAStatements.S_mo_119202
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp

/- Source module SquareDescent -/
section
namespace Loeffler

/-- In a finite Galois extension admitting a real place, if a positive power
of x belongs to the base, then x² already belongs to the base. -/
theorem square_descent {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] (v : K →+* ℝ)
    {x : K} {n : ℕ} (hn : n ≠ 0) {a : F} (hp : x ^ n = algebraMap F K a) :
    ∃ b : F, algebraMap F K b = x ^ 2 := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro τ
  have hpow : (τ x) ^ n = x ^ n := by
    rw [← map_pow, hp, τ.commutes]
  have hreal : (v (τ x)) ^ n = (v x) ^ n := by
    simpa using congrArg v hpow
  apply v.injective
  rw [map_pow, map_pow, map_pow]
  apply (pow_left_inj₀ (sq_nonneg _) (sq_nonneg _) hn).mp
  rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, hreal, ← pow_mul, Nat.mul_comm n 2, pow_mul]

end Loeffler
end

/- Source module LoeNoCM -/
section
namespace Loeffler
open NumberField

/-- Restriction of a real embedding excludes all CM subfields. -/
theorem noCM_of_realHom {K : Type*} [Field K] [NumberField K]
    (r : K →+* ℝ) (E : IntermediateField ℚ K) : ¬ IsCMField E := by
  intro h
  let : IsCMField E := h
  let z : E →+* ℂ := Complex.ofRealHom.comp (r.comp E.subtype)
  apply IsTotallyComplex.complexEmbedding_not_isReal z
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp [z]

end Loeffler
end

/- Source module LoefflerEmbeddings -/
section
/-! Duplicate restrictions in a tower of finite separable extensions. -/

namespace LoefflerEmbeddings

variable (F K Ω : Type*) [Field F] [CharZero F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Field Ω] [CharZero Ω] [IsAlgClosed Ω]

private theorem two_extensions (f : F →ₐ[ℚ] Ω) (hd : 2 ≤ Module.finrank F K) :
    ∃ a b : K →+* Ω, a ≠ b ∧
      (∀ x, a (algebraMap F K x) = f x) ∧ (∀ x, b (algebraMap F K x) = f x) := by
  let : Algebra F Ω := f.toRingHom.toAlgebra
  have hn : 1 < Fintype.card (K →ₐ[F] Ω) := by
    rw [AlgHom.card F K Ω]
    exact hd
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hn
  refine ⟨a.toRingHom, b.toRingHom, ?_, fun x => a.commutes x, fun x => b.commutes x⟩
  intro he
  exact hab (AlgHom.ext fun x => DFunLike.congr_fun he x)

theorem four_embeddings [FiniteDimensional ℚ F] (hF : 2 ≤ Module.finrank ℚ F)
    (hK : Module.finrank F K = 2) :
    ∃ σ : Fin 4 ↪ (K →+* Ω),
      (∀ x : F, σ 0 (algebraMap F K x) = σ 1 (algebraMap F K x)) ∧
      (∀ x : F, σ 2 (algebraMap F K x) = σ 3 (algebraMap F K x)) := by
  classical
  have hn : 1 < Fintype.card (F →ₐ[ℚ] Ω) := by
    rw [AlgHom.card ℚ F Ω]
    exact hF
  obtain ⟨f, g, hfg⟩ := Fintype.one_lt_card_iff.mp hn
  obtain ⟨a, b, hab, ha, hb⟩ := two_extensions F K Ω f hK.ge
  obtain ⟨c, d, hcd, hc, hd⟩ := two_extensions F K Ω g hK.ge
  have separate (u v : K →+* Ω)
      (hu : ∀ x, u (algebraMap F K x) = f x)
      (hv : ∀ x, v (algebraMap F K x) = g x) : u ≠ v := by
    rintro rfl
    exact hfg (AlgHom.ext fun x => (hu x).symm.trans (hv x))
  have hac := separate a c ha hc
  have had := separate a d ha hd
  have hbc := separate b c hb hc
  have hbd := separate b d hb hd
  let family : Fin 4 → (K →+* Ω) := ![a,b,c,d]
  have hinj : Function.Injective family := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact False.elim (hab hij)
      | exact False.elim (hab.symm hij)
      | exact False.elim (hac hij)
      | exact False.elim (hac.symm hij)
      | exact False.elim (had hij)
      | exact False.elim (had.symm hij)
      | exact False.elim (hbc hij)
      | exact False.elim (hbc.symm hij)
      | exact False.elim (hbd hij)
      | exact False.elim (hbd.symm hij)
      | exact False.elim (hcd hij)
      | exact False.elim (hcd.symm hij)
  refine ⟨⟨family, hinj⟩, fun x => (ha x).trans (hb x).symm,
    fun x => (hc x).trans (hd x).symm⟩

end LoefflerEmbeddings
end

/- Source module LoeUnits -/
section
open NumberField Module
open scoped Matrix

namespace LoeUnits
noncomputable section
variable {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]

abbrev FreeUnits (E : Type*) [Field E] [NumberField E] :=
  Additive ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E)

instance (E : Type*) [Field E] [NumberField E] : AddCommGroup (FreeUnits E) :=
  inferInstanceAs (AddCommGroup (Additive ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E)))

instance (E : Type*) [Field E] [NumberField E] : Module ℤ (FreeUnits E) :=
  inferInstanceAs (Module ℤ (Additive ((𝓞 E)ˣ ⧸ NumberField.Units.torsion E)))

def mapUnits (f : F →+* K) : (𝓞 F)ˣ →* (𝓞 K)ˣ :=
  _root_.Units.map (RingOfIntegers.mapRingHom f).toMonoidHom

theorem mapUnits_injective (f : F →+* K) : Function.Injective (mapUnits f) := by
  intro x y h
  apply _root_.Units.ext
  apply Subtype.ext
  apply f.injective
  exact congrArg (fun z : (𝓞 K)ˣ => ((z : 𝓞 K) : K)) h

theorem mapUnits_mem_torsion_iff (f : F →+* K) (u : (𝓞 F)ˣ) :
    mapUnits f u ∈ NumberField.Units.torsion K ↔ u ∈ NumberField.Units.torsion F := by
  change IsOfFinOrder (mapUnits f u) ↔ IsOfFinOrder u
  constructor
  · rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
    rintro ⟨n, hn, hu⟩
    exact ⟨n, hn, mapUnits_injective f (by simpa using hu)⟩
  · exact (mapUnits f).isOfFinOrder

def freeMapMul (f : F →+* K) :
    ((𝓞 F)ˣ ⧸ NumberField.Units.torsion F) →* ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) :=
  QuotientGroup.map _ _ (mapUnits f) (fun _ hu => (mapUnits_mem_torsion_iff f _).2 hu)

def freeMap (f : F →+* K) : FreeUnits F →ₗ[ℤ] FreeUnits K :=
  (freeMapMul f).toAdditive.toIntLinearMap

theorem freeMap_injective (f : F →+* K) : Function.Injective (freeMap f) := by
  suffices Function.Injective (freeMapMul f) from this
  apply (MonoidHom.ker_eq_bot_iff _).1
  apply le_antisymm _ bot_le
  intro q hq
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (NumberField.Units.torsion F) q
  apply (Subgroup.mem_bot).2
  apply (QuotientGroup.eq_one_iff u).2
  apply (mapUnits_mem_torsion_iff f u).1
  apply (QuotientGroup.eq_one_iff _).1
  exact hq

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
variable (L : Type*) [Field L] [CharZero L]
variable (f : F →+* K) (bF : Basis ι ℤ (FreeUnits F)) (bK : Basis κ ℤ (FreeUnits K))

def coeff : Matrix κ ι L := fun i j => (bK.equivFun (freeMap f (bF j)) i : ℤ)

theorem coeff_independent :
    LinearIndependent L (fun j i => coeff L f bF bK i j) := by
  let v : ι → κ → ℤ := fun j => bK.equivFun (freeMap f (bF j))
  change LinearIndependent L (fun j => algebraMap ℤ L ∘ v j)
  apply linearIndependent_algebraMap_comp_iff.mpr
  apply bF.linearIndependent.map' (bK.equivFun.toLinearMap.comp (freeMap f))
  apply LinearMap.ker_eq_bot_of_injective
  exact bK.equivFun.injective.comp (freeMap_injective f)

theorem eval_mul_coeff (ev : ν → FreeUnits K →ₗ[ℤ] L) (q : ν) (j : ι) :
    (Matrix.of (fun i k => ev i (bK k)) * coeff L f bF bK) q j =
      ev q (freeMap f (bF j)) := by
  rw [Matrix.mul_apply]
  conv_rhs => rw [← bK.sum_repr (freeMap f (bF j)), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [coeff, zsmul_eq_mul, mul_comm, Matrix.of_apply]

end
end LoeUnits

namespace LoeUnits
noncomputable section
open NumberField
variable {F K L : Type*} [Field F] [Field K] [NumberField F] [NumberField K]
variable [Field L] [CharZero L]

/-- The image of an integral unit under an embedding, viewed in the field's unit group. -/
def embUnit (σ : K →+* L) : (𝓞 K)ˣ →* Lˣ :=
  _root_.Units.map (σ.comp (algebraMap (𝓞 K) K)).toMonoidHom

def charQuot (ℓ : Lˣ →* Multiplicative L) (σ : K →+* L) :
    ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) →* Multiplicative L :=
  QuotientGroup.lift _ (ℓ.comp (embUnit σ)) (by
    intro x hx
    change (ℓ.comp (embUnit σ)) x = 1
    apply (isOfFinOrder_iff_eq_one _).mp
    exact (ℓ.comp (embUnit σ)).isOfFinOrder hx)

def evalChar (ℓ : Lˣ →* Multiplicative L) (σ : K →+* L) : FreeUnits K →ₗ[ℤ] L :=
  (MonoidHom.toAdditiveLeft (charQuot ℓ σ)).toIntLinearMap

@[simp] theorem evalChar_mk (ℓ : Lˣ →* Multiplicative L) (σ : K →+* L) (u : (𝓞 K)ˣ) :
    evalChar ℓ σ (Additive.ofMul ((QuotientGroup.mk u : (𝓞 K)ˣ ⧸ NumberField.Units.torsion K))) =
      (ℓ (embUnit σ u)).toAdd := rfl

theorem evalChar_restrict (ℓ : Lˣ →* Multiplicative L) (σ : K →+* L) (f : F →+* K)
    (x : FreeUnits F) :
    evalChar ℓ σ (freeMap f x) = evalChar ℓ (σ.comp f) x := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (NumberField.Units.torsion F) x.toMul
  have h : Additive.ofMul ((QuotientGroup.mk u : (𝓞 F)ˣ ⧸ NumberField.Units.torsion F)) = x := hu
  subst x
  rfl

end
end LoeUnits
end

/- Source module LoeSmith -/
section
open NumberField Module

namespace LoeUnits
noncomputable section
variable {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]

private abbrev unitClass (u : (𝓞 K)ˣ) : FreeUnits K :=
  Additive.ofMul (QuotientGroup.mk u)

private theorem power_in_image (f : F →+* K) (u : (𝓞 K)ˣ) {m : ℤ} (hm : m ≠ 0)
    (hq : m • unitClass u ∈ LinearMap.range (freeMap f)) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : F, (((u : (𝓞 K)ˣ) : 𝓞 K) : K) ^ n = f a := by
  have hn : (m.natAbs : ℤ) • unitClass u ∈ LinearMap.range (freeMap f) := by
    rw [Int.natCast_natAbs]
    rcases le_total 0 m with h | h
    · simpa only [abs_of_nonneg h] using hq
    · simpa only [abs_of_nonpos h, neg_smul] using (LinearMap.range (freeMap f)).neg_mem hq
  obtain ⟨x, hx⟩ := hn
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (NumberField.Units.torsion F) x.toMul
  have hv' : unitClass v = x := hv
  subst x
  have heq : (QuotientGroup.mk (u ^ m.natAbs) : (𝓞 K)ˣ ⧸ NumberField.Units.torsion K) =
      QuotientGroup.mk (mapUnits f v) := by
    rw [QuotientGroup.mk_pow]
    exact (congrArg Additive.toMul hx).symm
  have ht : IsOfFinOrder ((u ^ m.natAbs) / (mapUnits f v)) :=
    (QuotientGroup.eq_iff_div_mem).mp heq
  obtain ⟨s, hs, hpow⟩ := ht.exists_pow_eq_one
  rw [div_pow, div_eq_one] at hpow
  refine ⟨m.natAbs * s, Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hm) hs.ne', (v : F)^s, ?_⟩
  rw [pow_mul, map_pow]
  simpa [mapUnits] using congrArg (fun z : (𝓞 K)ˣ => ((z : 𝓞 K) : K)) hpow

/-- A fundamental system whose three indicated units have a positive power in the subfield. -/
theorem exists_adapted_units (f : F →+* K) (hr : NumberField.Units.rank F = 3) :
    ∃ (u : Fin (NumberField.Units.rank K) → (𝓞 K)ˣ)
      (b : Basis (Fin (NumberField.Units.rank K)) ℤ (FreeUnits K))
      (e : Fin 3 ↪ Fin (NumberField.Units.rank K)),
      (∀ i, Additive.ofMul (QuotientGroup.mk (u i) : (𝓞 K)ˣ ⧸ NumberField.Units.torsion K) = b i) ∧
      ∀ j, ∃ n : ℕ, n ≠ 0 ∧ ∃ a : F, (((u (e j) : (𝓞 K)ˣ) : 𝓞 K) : K)^n = f a := by
  classical
  obtain ⟨n, S⟩ := (LinearMap.range (freeMap f)).smithNormalForm (NumberField.Units.basisModTorsion K)
  have hdim : n = 3 := by
    have H := Module.finrank_eq_card_basis S.bN
    rw [LinearMap.finrank_range_of_inj (freeMap_injective f), NumberField.Units.finrank_modTorsion,
      Fintype.card_fin, hr] at H
    exact H.symm
  subst n
  let u : Fin (NumberField.Units.rank K) → (𝓞 K)ˣ := fun i => Quotient.out ((S.bM i).toMul :)
  have hu : ∀ i, unitClass (u i) = S.bM i := fun i => by
    apply Additive.toMul.injective
    exact Quotient.out_eq' _
  refine ⟨u, S.bM, S.f, hu, fun j => power_in_image f _ (m := S.a j) ?_ ?_⟩
  · intro hz
    have h := S.snf j
    rw [hz, zero_smul] at h
    exact S.bN.ne_zero j (Subtype.ext h)
  · rw [hu, ← S.snf]
    exact (S.bN j).property

end
end LoeUnits
end

/- Source module LoefflerMinor -/
section
/-! Algebraic certificates for the counterexample to David Loeffler's 2013 question.
The field-theoretic and unit-rank argument is given separately in the research note. -/
namespace LoefflerMinor

/-- The four possible signs of √2 + √3 - 1 in the totally real biquadratic field. -/
theorem signs :
    0 < Real.sqrt 2 + Real.sqrt 3 - 1 ∧
    Real.sqrt 2 - Real.sqrt 3 - 1 < 0 ∧
    -Real.sqrt 2 + Real.sqrt 3 - 1 < 0 ∧
    -Real.sqrt 2 - Real.sqrt 3 - 1 < 0 := by
  have h2 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have H2 : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h3 : 1 < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have H3 : Real.sqrt 3 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The first three columns are the logarithms of subfield units and therefore repeat
in pairs of rows. No restriction on the fourth unit or its logarithms is needed. -/
theorem paired_minor {R : Type*} [CommRing R] (a b c d e f g h i j : R) :
    Matrix.det !![a, b, c, g; a, b, c, h; d, e, f, i; d, e, f, j] = 0 := by
  rw [Matrix.det_succ_column _ 3]
  apply Finset.sum_eq_zero
  intro row _
  apply mul_eq_zero_of_right
  fin_cases row
  · apply Matrix.det_zero_of_row_eq (show (1 : Fin 3) ≠ 2 by decide)
    funext k; fin_cases k <;> rfl
  · apply Matrix.det_zero_of_row_eq (show (1 : Fin 3) ≠ 2 by decide)
    funext k; fin_cases k <;> rfl
  · apply Matrix.det_zero_of_row_eq (show (0 : Fin 3) ≠ 1 by decide)
    funext k; fin_cases k <;> rfl
  · apply Matrix.det_zero_of_row_eq (show (0 : Fin 3) ≠ 1 by decide)
    funext k; fin_cases k <;> rfl

/-- A finite-index change of the unit lattice preserves singularity in characteristic
zero. This form works over any integral domain once the change determinant is nonzero. -/
theorem original_minor {R : Type*} [CommRing R] [IsDomain R]
    (M C : Matrix (Fin 4) (Fin 4) R) (hC : C.det ≠ 0)
    (a b c d e f g h i j : R)
    (hshape : M*C = !![a,b,c,g; a,b,c,h; d,e,f,i; d,e,f,j]) : M.det = 0 := by
  have hz : M.det * C.det = 0 := by
    rw [← Matrix.det_mul, hshape, paired_minor]
  exact (mul_eq_zero.mp hz).resolve_right hC

/-- A three-element selection covers the three columns other than a suitable omitted one. -/
private theorem cover_succAbove : ∀ q : Fin 3 ↪ Fin 4,
    ∃ col : Fin 4, ∀ t : Fin 3, ∃ j, q j = col.succAbove t := by
  intro q
  have cover : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      ∃ col : Fin 4, ∀ t : Fin 3, a = col.succAbove t ∨ b = col.succAbove t ∨ c = col.succAbove t := by
    decide
  obtain ⟨col, hs⟩ := cover (q 0) (q 1) (q 2)
    (q.injective.ne (by decide)) (q.injective.ne (by decide)) (q.injective.ne (by decide))
  refine ⟨col, fun t => ?_⟩
  rcases hs t with ha|hb|hc
  · exact ⟨0,ha⟩
  · exact ⟨1,hb⟩
  · exact ⟨2,hc⟩

/-- Unordered, basis-adapted version of the determinant obstruction. -/
theorem selected_minor {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R)
    (q : Fin 3 ↪ Fin 4) (h01 : ∀ j, M 0 (q j) = M 1 (q j))
    (h23 : ∀ j, M 2 (q j) = M 3 (q j)) : M.det = 0 := by
  obtain ⟨c, hc⟩ := cover_succAbove q
  rw [Matrix.det_succ_column M c]
  apply Finset.sum_eq_zero
  intro row _
  apply mul_eq_zero_of_right
  fin_cases row
  · apply Matrix.det_zero_of_row_eq (show (1 : Fin 3) ≠ 2 by decide)
    funext t
    obtain ⟨j, hj⟩ := hc t
    change M 2 (c.succAbove t) = M 3 (c.succAbove t)
    rw [← hj]; exact h23 j
  · apply Matrix.det_zero_of_row_eq (show (1 : Fin 3) ≠ 2 by decide)
    funext t
    obtain ⟨j, hj⟩ := hc t
    change M 2 (c.succAbove t) = M 3 (c.succAbove t)
    rw [← hj]; exact h23 j
  · apply Matrix.det_zero_of_row_eq (show (0 : Fin 3) ≠ 1 by decide)
    funext t
    obtain ⟨j, hj⟩ := hc t
    change M 0 (c.succAbove t) = M 1 (c.succAbove t)
    rw [← hj]; exact h01 j
  · apply Matrix.det_zero_of_row_eq (show (0 : Fin 3) ≠ 1 by decide)
    funext t
    obtain ⟨j, hj⟩ := hc t
    change M 0 (c.succAbove t) = M 1 (c.succAbove t)
    rw [← hj]; exact h01 j




end LoefflerMinor
end

/- Source module LoeFields -/
section
open Polynomial
noncomputable section
namespace LoeFields

def pZ : ℤ[X] := X ^ 4 + C 12 * X ^ 3 + C 44 * X ^ 2 + C 48 * X ^ 1 - C 2
def p : ℚ[X] := pZ.map (Int.castRingHom ℚ)
theorem pZ_monic : pZ.Monic := by unfold pZ; monicity!
theorem pZ_natDegree : pZ.natDegree = 4 := by unfold pZ; compute_degree!
theorem p_irr : Irreducible p := by
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast pZ_monic.isPrimitive).mp
  apply irreducible_of_eisenstein_criterion (P := Ideal.span ({2} : Set ℤ))
  · exact (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
  · rw [pZ_monic.leadingCoeff, Ideal.mem_span_singleton]
    norm_num
  · intro i hi
    have h := coe_lt_degree.mp hi
    rw [pZ_natDegree] at h
    rw [Ideal.mem_span_singleton]
    interval_cases i <;> norm_num [pZ, coeff_X_pow, coeff_C, coeff_X]
  · rw [← natDegree_pos_iff_degree_pos, pZ_natDegree]
    decide
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [pZ, coeff_X_pow, coeff_C, coeff_X]
  · exact pZ_monic.isPrimitive
instance : Fact (Irreducible p) := ⟨p_irr⟩
abbrev F := AdjoinRoot p
theorem degree_F : Module.finrank ℚ F = 4 := by
  calc
    _ = (AdjoinRoot.powerBasis p_irr.ne_zero).dim := by
      convert! (AdjoinRoot.powerBasis p_irr.ne_zero).finrank
    _ = p.natDegree := AdjoinRoot.powerBasis_dim _
    _ = _ := (natDegree_map_eq_of_injective Int.cast_injective _).trans pZ_natDegree

def qZ : ℤ[X] := X ^ 8 + C 12 * X ^ 6 + C 44 * X ^ 4 + C 48 * X ^ 2 - C 2
def q : ℚ[X] := qZ.map (Int.castRingHom ℚ)
theorem qZ_monic : qZ.Monic := by unfold qZ; monicity!
theorem qZ_natDegree : qZ.natDegree = 8 := by unfold qZ; compute_degree!
theorem q_irr : Irreducible q := by
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast qZ_monic.isPrimitive).mp
  apply irreducible_of_eisenstein_criterion (P := Ideal.span ({2} : Set ℤ))
  · exact (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
  · rw [qZ_monic.leadingCoeff, Ideal.mem_span_singleton]
    norm_num
  · intro i hi
    have h := coe_lt_degree.mp hi
    rw [qZ_natDegree] at h
    rw [Ideal.mem_span_singleton]
    interval_cases i <;> norm_num [qZ, coeff_X_pow, coeff_C, coeff_X]
  · rw [← natDegree_pos_iff_degree_pos, qZ_natDegree]
    decide
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [qZ, coeff_X_pow, coeff_C, coeff_X]
  · exact qZ_monic.isPrimitive
instance : Fact (Irreducible q) := ⟨q_irr⟩
abbrev K := AdjoinRoot q
theorem degree_K : Module.finrank ℚ K = 8 := by
  calc
    _ = (AdjoinRoot.powerBasis q_irr.ne_zero).dim := by
      convert! (AdjoinRoot.powerBasis q_irr.ne_zero).finrank
    _ = q.natDegree := AdjoinRoot.powerBasis_dim _
    _ = _ := (natDegree_map_eq_of_injective Int.cast_injective _).trans qZ_natDegree
theorem aeval_p {E : Type*} [Field E] [Algebra ℚ E] (x : E) :
    aeval x p = x^4 + 12*x^3 + 44*x^2 + 48*x - 2 := by
  simp [p,pZ]
  simp only [show (12 : ℚ[X]) = (12 : ℕ) by rfl, show (44 : ℚ[X]) = (44 : ℕ) by rfl,
    show (48 : ℚ[X]) = (48 : ℕ) by rfl, show (2 : ℚ[X]) = (2 : ℕ) by rfl, aeval_natCast]
  norm_num
theorem aeval_q {E : Type*} [Field E] [Algebra ℚ E] (x : E) :
    aeval x q = x^8 + 12*x^6 + 44*x^4 + 48*x^2 - 2 := by
  simp [q,qZ]
  simp only [show (12 : ℚ[X]) = (12 : ℕ) by rfl, show (44 : ℚ[X]) = (44 : ℕ) by rfl,
    show (48 : ℚ[X]) = (48 : ℕ) by rfl, show (2 : ℚ[X]) = (2 : ℕ) by rfl, aeval_natCast]
  norm_num
theorem aeval_q_sq {E : Type*} [Field E] [Algebra ℚ E] (x : E) :
    aeval x q = aeval (x^2) p := by rw [aeval_p, aeval_q]; ring
def intoK : F →ₐ[ℚ] K :=
  AdjoinRoot.liftAlgHom p (Algebra.ofId ℚ K) (AdjoinRoot.root q ^ 2)
    (by change aeval (AdjoinRoot.root q ^ 2) p = 0; rw [← aeval_q_sq]; convert! AdjoinRoot.eval₂_root q)
instance : Algebra F K := intoK.toRingHom.toAlgebra
instance : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq' intoK.comp_algebraMap.symm
end LoeFields
end
end

/- Source module RealPlacesRoots -/
section
noncomputable section
open Polynomial NumberField NumberField.InfinitePlace
namespace LoeFields

def realHomEquivPlaces (E : Type*) [Field E] :
    (E →+* ℝ) ≃ {w : InfinitePlace E // w.IsReal} :=
  Equiv.trans (β := {φ : E →+* ℂ // ComplexEmbedding.IsReal φ})
    { toFun := fun φ => ⟨Complex.ofRealHom.comp φ, by
        apply ComplexEmbedding.isReal_iff.mpr
        ext1 x
        simp [ComplexEmbedding.conjugate_coe_eq]⟩
      invFun := fun φ => φ.2.embedding
      left_inv := fun φ => by ext1; rfl
      right_inv := fun φ => by
        apply Subtype.ext
        ext1 x
        exact ComplexEmbedding.IsReal.coe_embedding_apply φ.2 x }
    InfinitePlace.mkReal

def realRootEquiv (f : ℚ[X]) :
    (AdjoinRoot f →ₐ[ℚ] ℝ) ≃ {x : ℝ // aeval x f = 0} where
  toFun φ := ⟨φ (AdjoinRoot.root f), AdjoinRoot.aeval_algHom_eq_zero f φ⟩
  invFun x := AdjoinRoot.liftAlgHom f (Algebra.ofId ℚ ℝ) x.val x.2
  left_inv φ := AdjoinRoot.liftAlgHom_eq_algHom f φ
  right_inv _x := Subtype.ext (AdjoinRoot.liftAlgHom_root _ _ _ _)

def placesEquivRoots (f : ℚ[X]) [Fact (Irreducible f)] :
    {w : InfinitePlace (AdjoinRoot f) // w.IsReal} ≃ {x : ℝ // aeval x f = 0} :=
  (realHomEquivPlaces _).symm.trans ((RingHom.equivRatAlgHom _ _).trans (realRootEquiv f))



end LoeFields
end
end

/- Source module LoeRealRoots -/
section
noncomputable section
namespace LoeFields

def curve (x : ℝ) := x^4 + 12*x^3 + 44*x^2 + 48*x - 2
private theorem cont : Continuous curve := by unfold curve; fun_prop

private theorem rising {a b : ℝ} (hab : a ≤ b) (ha : curve a < 0) (hb : 0 < curve b) :
    ∃ x : ℝ, (a < x ∧ x < b) ∧ curve x = 0 :=
  intermediate_value_Ioo hab cont.continuousOn ⟨ha, hb⟩

private theorem falling {a b : ℝ} (hab : a ≤ b) (ha : 0 < curve a) (hb : curve b < 0) :
    ∃ x : ℝ, (a < x ∧ x < b) ∧ curve x = 0 :=
  intermediate_value_Ioo' hab cont.continuousOn ⟨hb, ha⟩

theorem fourQuarticRoots : Nonempty (Fin 4 ↪ {x : ℝ // curve x = 0}) := by
  obtain ⟨a, ha, ea⟩ := falling (a := -7) (b := -6) (by norm_num) (by norm_num [curve]) (by norm_num [curve])
  obtain ⟨b, hb, eb⟩ := rising (a := -4) (b := -3) (by norm_num) (by norm_num [curve]) (by norm_num [curve])
  obtain ⟨c, hc, ec⟩ := falling (a := -3) (b := -2) (by norm_num) (by norm_num [curve]) (by norm_num [curve])
  obtain ⟨d, hd, ed⟩ := rising (a := 0) (b := 1) (by norm_num) (by norm_num [curve]) (by norm_num [curve])
  let f : Fin 4 → {x : ℝ // curve x = 0} := ![⟨a,ea⟩,⟨b,eb⟩,⟨c,ec⟩,⟨d,ed⟩]
  refine ⟨f, fun i j hij ↦ ?_⟩
  have eq := congrArg Subtype.val hij
  fin_cases i <;> fin_cases j <;> norm_num [f] at eq ⊢ <;> linarith [ha.1,ha.2,hb.1,hb.2,hc.1,hc.2,hd.1,hd.2]

private theorem curve_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : curve x < curve y := by
  have h2 := pow_le_pow_left₀ hx hxy.le 2
  have h3 := pow_le_pow_left₀ hx hxy.le 3
  have h4 := pow_le_pow_left₀ hx hxy.le 4
  unfold curve
  linarith

theorem octicRootEquiv : Nonempty (Bool ≃ {x : ℝ // curve (x^2) = 0}) := by
  obtain ⟨d, hd, ed⟩ := rising (a := 0) (b := 1) (by norm_num) (by norm_num [curve]) (by norm_num [curve])
  have hs := Real.sq_sqrt hd.1.le
  have hp := Real.sqrt_pos.2 hd.1
  let f : Bool → {x : ℝ // curve (x^2) = 0}
    | false => ⟨-(Real.sqrt d), by simpa [hs] using ed⟩
    | true => ⟨Real.sqrt d, by simpa [hs] using ed⟩
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro i j hij
    cases i <;> cases j
    · rfl
    · have h : -(Real.sqrt d) = Real.sqrt d := congrArg Subtype.val hij
      linarith
    · have h : Real.sqrt d = -(Real.sqrt d) := congrArg Subtype.val hij
      linarith
    · rfl
  · intro x
    have ex : x.val^2 = d := by
      rcases lt_trichotomy (x.val^2) d with h|h|h
      · have h' := curve_lt (sq_nonneg x.val) h
        exact (h'.ne (x.property.trans ed.symm)).elim
      · exact h
      · have h' := curve_lt hd.1.le h
        exact (h'.ne (ed.trans x.property.symm)).elim
    have dh := mul_self_eq_mul_self_iff.mp (show x.val*x.val = Real.sqrt d * Real.sqrt d by nlinarith only [ex,hs])
    rcases dh with h|h
    · exact ⟨true, Subtype.ext (by simpa [f] using h.symm)⟩
    · exact ⟨false, Subtype.ext (by dsimp [f]; linarith)⟩



end LoeFields
end
end

/- Source module LoeSignature -/
section
open NumberField NumberField.InfinitePlace Polynomial
noncomputable section
namespace LoeFields

def fRealPlaces :
    {w : InfinitePlace F // w.IsReal} ≃ {x : ℝ // curve x = 0} :=
  (placesEquivRoots p).trans (Equiv.subtypeEquivRight (fun x => by rw [aeval_p]; rfl))

def kRealPlaces :
    {w : InfinitePlace K // w.IsReal} ≃ {x : ℝ // curve (x^2) = 0} :=
  (placesEquivRoots q).trans (Equiv.subtypeEquivRight (fun x => by rw [aeval_q_sq, aeval_p]; rfl))

theorem real_F : nrRealPlaces F = 4 := by
  classical
  let e := fourQuarticRoots.some.trans fRealPlaces.symm.toEmbedding
  have h := Fintype.card_le_of_embedding e
  have h' := card_add_two_mul_card_eq_rank F
  rw [degree_F] at h'
  change nrRealPlaces F + 2 * nrComplexPlaces F = 4 at h'
  change Fintype.card (Fin 4) ≤ nrRealPlaces F at h
  simp only [Fintype.card_fin] at h
  omega

theorem real_K : nrRealPlaces K = 2 := by
  classical
  have h := Fintype.card_congr (kRealPlaces.trans octicRootEquiv.some.symm)
  exact h.trans Fintype.card_bool

theorem complex_F : nrComplexPlaces F = 0 := by
  have h := card_add_two_mul_card_eq_rank F
  rw [degree_F, real_F] at h
  omega

theorem complex_K : nrComplexPlaces K = 3 := by
  have h := card_add_two_mul_card_eq_rank K
  rw [degree_K, real_K] at h
  omega

def realEmbeddingK : K →+* ℝ :=
  (realHomEquivPlaces K).symm (kRealPlaces.symm (octicRootEquiv.some true))

theorem relativeDegree : Module.finrank F K = 2 := by
  have h := Module.finrank_mul_finrank ℚ F K
  rw [degree_K, degree_F] at h
  omega
end LoeFields
end
end

/- Source module LoeSolution -/
section
open NumberField OMA.S_mo_119202

namespace Loeffler

theorem logUnit_of_sq {p : ℕ} [Fact p.Prime] {x y : ℂ_[p]} (h : x ^ 2 = y ^ 2) :
    logUnit p x = logUnit p y := by
  simp only [logUnit, h]

/-- For every prime, the counterexample has a genuine basis and four distinct
p-adic embeddings on which its logarithmic regulator minor vanishes. -/
theorem exact_minor {K F : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (real : K →+* ℝ) (hF : Units.rank F = 3) (hK : Units.rank K = 4)
    (hdeg : 2 ≤ Module.finrank ℚ F) (hrel : Module.finrank F K = 2)
    (p : ℕ) [Fact p.Prime] :
    ∃ u : Fin (Units.rank K) → (𝓞 K)ˣ, IsFundamental K u ∧
      ∃ s : Fin (Units.rank K) ↪ (K →+* ℂ_[p]),
        Matrix.det (fun i j => logUnit p (s i (u j : K))) = 0 := by
  classical
  letI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hrel }
  obtain ⟨u,b,e,hu,he⟩ := LoeUnits.exists_adapted_units (algebraMap F K) hF
  obtain ⟨s,s01,s23⟩ := LoefflerEmbeddings.four_embeddings F K ℂ_[p] hdeg hrel
  let r : Fin (Units.rank K) ≃ Fin 4 := finCongr hK
  let t := r.toEmbedding.trans s
  refine ⟨u, ⟨b, hu⟩, t, ?_⟩
  let M : Matrix (Fin 4) (Fin 4) ℂ_[p] := fun i j => logUnit p (s i (u (r.symm j) : K))
  have paired (i i' : Fin 4) (hh : ∀ a : F, s i (algebraMap F K a) = s i' (algebraMap F K a))
      (j : Fin 3) : M i ((e.trans r.toEmbedding) j) = M i' ((e.trans r.toEmbedding) j) := by
    obtain ⟨n,hn,a,ha⟩ := he j
    obtain ⟨c,hc⟩ := square_descent real hn ha
    change logUnit p (s i (u (r.symm (r (e j))) : K)) =
      logUnit p (s i' (u (r.symm (r (e j))) : K))
    simp only [Equiv.symm_apply_apply]
    apply logUnit_of_sq
    rw [← map_pow (s i), ← map_pow (s i'), ← hc]
    exact hh c
  have hz := LoefflerMinor.selected_minor M (e.trans r.toEmbedding) (paired 0 1 s01) (paired 2 3 s23)
  have hmat : (fun (i j : Fin (Units.rank K)) => logUnit p (t i (u j : K))) =
      M.submatrix r r := by
    funext i j
    change _ = logUnit p (s (r i) (u (r.symm (r j)) : K))
    simp [t]
  rw [hmat, Matrix.det_submatrix_equiv_self, hz]

end Loeffler

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_119202.main) := by
  intro hall
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrF : Units.rank LoeFields.F = 3 := by
    rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      LoeFields.real_F, LoeFields.complex_F]
  have hrK : Units.rank LoeFields.K = 4 := by
    rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      LoeFields.real_K, LoeFields.complex_K]
  obtain ⟨u,hu,s,hs⟩ := Loeffler.exact_minor LoeFields.realEmbeddingK hrF hrK
    (by rw [LoeFields.degree_F]; decide) LoeFields.relativeDegree 2
  exact hall LoeFields.K (Loeffler.noCM_of_realHom LoeFields.realEmbeddingK) 2 u hu s hs
end
