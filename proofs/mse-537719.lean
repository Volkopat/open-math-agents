import OMAStatements.S_mse_537719
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Order.Zorn
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic

namespace OMA.Field537719

open Polynomial

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

def Avoids (p : F[X]) (K : IntermediateField F L) : Prop :=
  ∀ x ∈ K, aeval x p ≠ 0

theorem exists_maximal (p : F[X]) (hnone : ∀ x : F, ¬ p.IsRoot x) :
    ∃ K : IntermediateField F L, Maximal (Avoids p) K := by
  classical
  have hbot : Avoids p (⊥ : IntermediateField F L) := by
    intro x hx hr
    obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.mp hx
    apply hnone y
    exact (algebraMap F L).injective (by simpa using hr)
  apply zorn_le₀ {K : IntermediateField F L | Avoids p K}
  intro c hc hchain
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨⊥, hbot, by simp⟩
  refine ⟨sSup c, ?_, fun K hK => le_sSup hK⟩
  change Avoids p (sSup c)
  intro x hx
  have : Nonempty c := hne.to_subtype
  rw [sSup_eq_iSup', ← SetLike.mem_coe,
    IntermediateField.coe_iSup_of_directed hchain.directedOn.directed_val, Set.mem_iUnion] at hx
  obtain ⟨K, hxK⟩ := hx
  exact hc K.property x hxK

theorem irreducible_map_of_avoids {p : F[X]} (hdeg : p.natDegree = 3)
    (K : IntermediateField F L) (hK : Avoids p K) :
    Irreducible (p.map (algebraMap F K)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [hdeg]
  intro x hroot
  apply hK x x.property
  have hmap : ((p.map (algebraMap F K)).map (algebraMap K L)).eval (x : L) = 0 := by
    rw [eval_map]
    change eval₂ (algebraMap K L) (algebraMap K L x) (p.map (algebraMap F K)) = 0
    rw [eval₂_at_apply]
    rw [hroot, map_zero]
  rwa [map_map, ← IsScalarTower.algebraMap_eq F K L, eval_map_algebraMap] at hmap

theorem not_splits_of_unique [CharZero F] {p : F[X]} (hdeg : p.natDegree = 3)
    (hnone : ∀ x : F, ¬ p.IsRoot x)
    (hunique : ∀ x y : L, aeval x p = 0 → aeval y p = 0 → x = y) :
    ¬ (p.map (algebraMap F L)).Splits := by
  classical
  have hirr : Irreducible p :=
    irreducible_of_degree_le_three_of_not_isRoot (by simp [hdeg]) hnone
  let q := p.map (algebraMap F L)
  intro hq
  have hdegree : q.natDegree = 3 := by simpa [q] using hdeg
  have hnodup : q.roots.Nodup := nodup_roots (hirr.separable.map)
  have hcard : q.roots.toFinset.card = 3 := by
    rw [Multiset.toFinset_card_of_nodup hnodup, ← hq.natDegree_eq_card_roots, hdegree]
  have hsub : (q.roots.toFinset : Set L).Subsingleton := by
    intro x hx y hy
    apply hunique x y
    · have hx' : x ∈ q.roots := Multiset.mem_toFinset.mp hx
      simpa [q, ← eval_map_algebraMap, IsRoot] using isRoot_of_mem_roots hx'
    · have hy' : y ∈ q.roots := Multiset.mem_toFinset.mp hy
      simpa [q, ← eval_map_algebraMap, IsRoot] using isRoot_of_mem_roots hy'
  have hle := Finset.card_le_one.mpr hsub
  omega

theorem mem_of_splits {p : F[X]} (hdeg : p.natDegree = 3) (hmonic : p.Monic)
    (hsplit : ¬ (p.map (algebraMap F L)).Splits)
    {K : IntermediateField F L} (hK : Maximal (Avoids p) K)
    {Q : K[X]} (hQ : (Q.map (algebraMap K L)).Splits) {x : L}
    (hx : x ∈ Q.rootSet L) : x ∈ K := by
  let E := IntermediateField.adjoin K (Q.rootSet L)
  have hKE : K ≤ E.restrictScalars F := fun y hy => E.algebraMap_mem (⟨y, hy⟩ : K)
  have hE : Avoids p (E.restrictScalars F) := by
    intro y hy hyroot
    have hyE : y ∈ E := hy
    let z : E := ⟨y, hyE⟩
    let pK := p.map (algebraMap F K)
    have hi : Irreducible pK := irreducible_map_of_avoids hdeg K hK.1
    have hz : aeval z pK = 0 := E.val.injective (by
      change (↑(aeval z pK) : L) = 0
      rw [← IntermediateField.aeval_coe E z pK]
      exact (aeval_eq_aeval_map (IsScalarTower.algebraMap_eq F K L).symm p y).symm.trans hyroot)
    have hp : pK = minpoly K z := minpoly.eq_of_irreducible_of_monic hi hz (hmonic.map _)
    let : Q.IsSplittingField K E := IntermediateField.adjoin_rootSet_isSplittingField hQ
    let hNormal : Normal K E := Normal.of_isSplittingField Q
    have hsplitE : (pK.map (algebraMap K E)).Splits := hp.symm ▸ hNormal.splits z
    apply hsplit
    have hs := hsplitE.map (algebraMap E L)
    rw [map_map, ← IsScalarTower.algebraMap_eq K E L] at hs
    dsimp [pK] at hs
    rwa [map_map, ← IsScalarTower.algebraMap_eq F K L] at hs
  have hEK : E.restrictScalars F ≤ K := hK.2 hE hKE
  exact hEK (IntermediateField.subset_adjoin K _ hx)

end OMA.Field537719

namespace OMA.Cubic537719

open scoped LaurentSeries

theorem ratFunc_no_root (r : RatFunc ℂ) : r ^ 3 - r ^ 2 ≠ RatFunc.X := by
  intro h
  let p : Polynomial (Polynomial ℂ) :=
    Polynomial.X ^ 3 - (Polynomial.X ^ 2 + Polynomial.C Polynomial.X)
  have hp : p.Monic := by
    apply Polynomial.monic_X_pow_sub
    exact (Polynomial.degree_add_le _ _).trans_lt (by norm_num [Polynomial.degree_X_pow])
  have hr : IsIntegral (Polynomial ℂ) r := by
    refine ⟨p, hp, ?_⟩
    simp [p, RatFunc.algebraMap_X]
    linear_combination h
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (K := RatFunc ℂ)).mp hr
  have heq : a ^ 3 - a ^ 2 = Polynomial.X := by
    apply IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)
    rw [map_sub, map_pow, map_pow, RatFunc.algebraMap_X, ha]
    exact h
  have hdeg := congrArg Polynomial.natDegree heq
  by_cases hd : a.natDegree = 0
  · have hb := Polynomial.natDegree_sub_le (a ^ 3) (a ^ 2)
    simp [Polynomial.natDegree_pow, hd] at hb
    simp [hdeg] at hb
  · have hlt : (a ^ 2).natDegree < (a ^ 3).natDegree := by
      simp only [Polynomial.natDegree_pow]
      omega
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt,
      Polynomial.natDegree_pow, Polynomial.natDegree_X] at hdeg
    omega

theorem laurent_root_orders {r : LaurentSeries ℂ}
    (hr : r ^ 3 - r ^ 2 = ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ)) :
    r.order = 0 ∧ (r - 1).order = 1 := by
  have ht : ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) =
      HahnSeries.single (1 : ℤ) (1 : ℂ) := PowerSeries.coe_X
  have ht0 : ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [ht]
    simp
  have hfact : r ^ 2 * (r - 1) =
      ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) := by
    rw [show r ^ 2 * (r - 1) = r ^ 3 - r ^ 2 by ring, hr]
  have hn : r ≠ 0 := by
    intro h
    apply ht0
    simpa [h] using hfact.symm
  have hn1 : r - 1 ≠ 0 := by
    intro h
    apply ht0
    simpa [h] using hfact.symm
  have hord := congrArg HahnSeries.order hfact
  rw [HahnSeries.order_mul (pow_ne_zero _ hn) hn1, HahnSeries.order_pow,
    ht, HahnSeries.order_single one_ne_zero] at hord
  simp only [two_nsmul] at hord
  have ht1 : (1 : LaurentSeries ℂ).orderTop = 0 := HahnSeries.orderTop_one
  have hr0 : r.order = 0 := by
    rcases lt_trichotomy r.order 0 with hneg | hzero | hpos
    · have hlt : r.orderTop < (1 : LaurentSeries ℂ).orderTop := by
        rw [← HahnSeries.order_eq_orderTop_of_ne_zero hn, ht1]
        exact_mod_cast hneg
      have hsub := HahnSeries.orderTop_sub hlt
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hn1,
        ← HahnSeries.order_eq_orderTop_of_ne_zero hn,
        WithTop.coe_eq_coe] at hsub
      omega
    · exact hzero
    · have hlt : (1 : LaurentSeries ℂ).orderTop < r.orderTop := by
        rw [← HahnSeries.order_eq_orderTop_of_ne_zero hn, ht1]
        exact_mod_cast hpos
      have hsub := HahnSeries.orderTop_sub hlt
      rw [← neg_sub r 1, HahnSeries.orderTop_neg, ht1,
        ← HahnSeries.order_eq_orderTop_of_ne_zero hn1] at hsub
      have hzero : (r - 1).order = 0 := by exact_mod_cast hsub
      omega
  exact ⟨hr0, by omega⟩

private theorem coeff_zero_of_root {r : LaurentSeries ℂ}
    (hr : r ^ 3 - r ^ 2 = ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ)) :
    PowerSeries.constantCoeff r.powerSeriesPart = 1 := by
  obtain ⟨h0, h1⟩ := laurent_root_orders hr
  have hcoeff : (r - 1).coeff 0 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_order (h1 ▸ zero_lt_one)
  simpa [← PowerSeries.coeff_zero_eq_constantCoeff, LaurentSeries.powerSeriesPart_coeff,
    h0, HahnSeries.coeff_sub, sub_eq_zero] using hcoeff

theorem laurent_root_unique {r s : LaurentSeries ℂ}
    (hr : r ^ 3 - r ^ 2 = ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ))
    (hs : s ^ 3 - s ^ 2 = ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ)) :
    r = s := by
  have hfactor : (r - s) * (r ^ 2 + r * s + s ^ 2 - r - s) = 0 := by
    linear_combination hr - hs
  have lift_eq (x : LaurentSeries ℂ) (hx : x.order = 0) :
      algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) x.powerSeriesPart = x := by
    simpa [hx, ← HahnSeries.C_apply, LaurentSeries.coe_algebraMap] using
      x.single_order_mul_powerSeriesPart
  have hrMap := lift_eq r (laurent_root_orders hr).1
  have hsMap := lift_eq s (laurent_root_orders hs).1
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · have hmap : algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
          (r.powerSeriesPart ^ 2 + r.powerSeriesPart * s.powerSeriesPart +
            s.powerSeriesPart ^ 2 - r.powerSeriesPart - s.powerSeriesPart) =
          algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) 0 := by
      simpa only [map_add, map_sub, map_mul, map_pow, map_zero, hrMap, hsMap] using h
    have heq := congrArg (PowerSeries.constantCoeff (R := ℂ))
      ((IsFractionRing.injective (PowerSeries ℂ) (LaurentSeries ℂ)) hmap)
    norm_num [map_add, map_sub, map_mul, map_pow, coeff_zero_of_root hr,
      coeff_zero_of_root hs] at heq

end OMA.Cubic537719

open scoped LaurentSeries PowerSeries RatFunc WithZero

namespace OMA.Ring537719

noncomputable section

variable {K : Type} [Field K] (ι : K →+* LaurentSeries ℂ)

abbrev ring : ValuationSubring K :=
  ((Valued.v : Valuation (LaurentSeries ℂ) ℤᵐ⁰).comap ι).valuationSubring

def toLaurentSubring : ring ι →+* LaurentSeries.powerSeries_as_subring ℂ :=
  (ι.comp (ring ι).toSubring.subtype).codRestrict _ (fun x => by
    obtain ⟨f, hf⟩ := (LaurentSeries.val_le_one_iff_eq_coe ℂ (ι x)).mp x.property
    exact ⟨f, trivial, hf⟩)

def toPower : ring ι →+* PowerSeries ℂ :=
  (LaurentSeries.powerSeriesEquivSubring ℂ).symm.toRingHom.comp (toLaurentSubring ι)

theorem toPower_coe (x : ring ι) : (toPower ι x : LaurentSeries ℂ) = ι x :=
  congrArg Subtype.val ((LaurentSeries.powerSeriesEquivSubring ℂ).apply_symm_apply
    (toLaurentSubring ι x))

theorem toPower_injective : Function.Injective (toPower ι) := by
  intro x y h
  apply Subtype.ext
  apply ι.injective
  calc
    ι x = (toPower ι x : LaurentSeries ℂ) := (toPower_coe ι x).symm
    _ = (toPower ι y : LaurentSeries ℂ) :=
      congrArg (fun p : PowerSeries ℂ => (p : LaurentSeries ℂ)) h
    _ = ι y := toPower_coe ι y

def ofPower (f : PowerSeries ℂ) (x : K) (hx : ι x = (f : LaurentSeries ℂ)) : ring ι :=
  ⟨x, (LaurentSeries.val_le_one_iff_eq_coe ℂ (ι x)).mpr ⟨f, hx.symm⟩⟩

@[simp] theorem toPower_ofPower (f : PowerSeries ℂ) (x : K)
    (hx : ι x = (f : LaurentSeries ℂ)) : toPower ι (ofPower ι f x hx) = f := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  exact (toPower_coe ι _).trans hx

def constant : ring ι →+* ℂ := PowerSeries.constantCoeff.comp (toPower ι)

theorem constant_surjective
    (h : ∀ c : ℂ, ∃ x : K, ι x = (PowerSeries.C c : LaurentSeries ℂ)) :
    Function.Surjective (constant ι) := by
  intro c
  obtain ⟨x, hx⟩ := h c
  exact ⟨ofPower ι (PowerSeries.C c) x hx, by simp [constant]⟩

def residueEquiv (h : Function.Surjective (constant ι)) :
    IsLocalRing.ResidueField (ring ι) ≃+* ℂ :=
  (Ideal.quotEquivOfEq (IsLocalRing.ker_eq_maximalIdeal (constant ι) h).symm).trans
    (RingHom.quotientKerEquivOfSurjective h)

@[simp] theorem residueEquiv_residue (h : Function.Surjective (constant ι)) (x : ring ι) :
    residueEquiv ι h (IsLocalRing.residue (ring ι) x) = constant ι x := rfl

def uniformizer (x : K) (hx : ι x = ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ)) :
    ring ι := ofPower ι PowerSeries.X x hx

theorem uniformizer_ne_zero (x : K)
    (hx : ι x = ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ)) :
    uniformizer ι x hx ≠ 0 := by
  intro hzero
  exact (PowerSeries.X_ne_zero (R := ℂ))
    (by simpa [uniformizer] using congrArg (toPower ι) hzero)

theorem uniformizer_residue_zero (h : Function.Surjective (constant ι)) (x : K)
    (hx : ι x = ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ)) :
    IsLocalRing.residue (ring ι) (uniformizer ι x hx) = 0 := by
  apply (residueEquiv ι h).injective
  simp [constant, uniformizer]

section IntermediateField

variable (L : IntermediateField (RatFunc ℂ) (LaurentSeries ℂ))

abbrev fieldEmbedding : L →+* LaurentSeries ℂ := L.subtype

abbrev intRing : ValuationSubring L := ring (fieldEmbedding L)

abbrev baseLift (x : RatFunc ℂ) : L := ⟨x, L.algebraMap_mem x⟩

theorem liftConstant_eq (c : ℂ) :
    fieldEmbedding L (baseLift L (RatFunc.C c)) =
      (PowerSeries.C c : LaurentSeries ℂ) := by
  change ((RatFunc.C c : RatFunc ℂ) : LaurentSeries ℂ) = _
  simpa using (RatFunc.coe_coe (Polynomial.C c)).symm

theorem intRing_constant_surjective : Function.Surjective (constant (fieldEmbedding L)) :=
  constant_surjective _ fun c => ⟨baseLift L (RatFunc.C c), liftConstant_eq L c⟩

abbrev intRing_residueEquiv : IsLocalRing.ResidueField (intRing L) ≃+* ℂ :=
  residueEquiv _ (intRing_constant_surjective L)

theorem liftX_eq :
    fieldEmbedding L (baseLift L RatFunc.X) =
      ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) := by
  change ((RatFunc.X : RatFunc ℂ) : LaurentSeries ℂ) = _
  rw [RatFunc.coe_X, PowerSeries.coe_X]

def parameter : intRing L := uniformizer _ (baseLift L RatFunc.X) (liftX_eq L)

theorem parameter_ne_zero : parameter L ≠ 0 := uniformizer_ne_zero _ _ (liftX_eq L)

theorem parameter_residue_zero : IsLocalRing.residue (intRing L) (parameter L) = 0 :=
  uniformizer_residue_zero _ (intRing_constant_surjective L) _ (liftX_eq L)

theorem parameter_nonunit : ¬ IsUnit (parameter L) := by
  intro h
  have hu := h.map (IsLocalRing.residue (intRing L))
  rw [parameter_residue_zero] at hu
  exact not_isUnit_zero hu

@[simp] theorem parameter_algebraMap :
    algebraMap (intRing L) L (parameter L) = baseLift L RatFunc.X := rfl

instance : Algebra (intRing L) (PowerSeries ℂ) := (toPower (fieldEmbedding L)).toAlgebra

instance : Algebra (intRing L) (LaurentSeries ℂ) :=
  ((fieldEmbedding L).comp (intRing L).toSubring.subtype).toAlgebra

instance : IsScalarTower (intRing L) L (LaurentSeries ℂ) :=
  IsScalarTower.of_algebraMap_eq (R := intRing L) (S := L) (A := LaurentSeries ℂ) fun _ => rfl

instance : IsScalarTower (intRing L) (PowerSeries ℂ) (LaurentSeries ℂ) :=
  IsScalarTower.of_algebraMap_eq fun x => (toPower_coe (fieldEmbedding L) x).symm

instance : IsLocalHom (algebraMap (intRing L) (PowerSeries ℂ)) where
  map_nonunit x hx := by
    by_contra h
    have hm : x ∈ IsLocalRing.maximalIdeal (intRing L) := h
    rw [← IsLocalRing.ker_eq_maximalIdeal (constant (fieldEmbedding L))
      (intRing_constant_surjective L),
      RingHom.mem_ker] at hm
    have hu := hx.map (PowerSeries.constantCoeff (R := ℂ))
    change IsUnit (constant (fieldEmbedding L) x) at hu
    exact not_isUnit_zero (hm ▸ hu)

instance : Module.FaithfullyFlat (intRing L) (PowerSeries ℂ) := by
  have : Module.Flat (intRing L) (PowerSeries ℂ) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    exact Module.isTorsionFree_iff_algebraMap_injective.mpr (toPower_injective (fieldEmbedding L))
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem intRing_intersection (z : PowerSeries ℂ)
    (hz : algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) z ∈
      Set.range (algebraMap L (LaurentSeries ℂ))) :
    z ∈ Set.range (algebraMap (intRing L) (PowerSeries ℂ)) := by
  obtain ⟨x, hx⟩ := hz
  exact ⟨ofPower (fieldEmbedding L) z x hx, toPower_ofPower (fieldEmbedding L) z x hx⟩

end IntermediateField

end

end OMA.Ring537719

namespace OMA.Split537719

universe v

open IsLocalRing
open scoped TensorProduct

private theorem liftToComplete {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallySmooth R S] (I : Ideal R) [IsAdicComplete I R]
    (f : S →ₐ[R] R ⧸ I) : ∃ g : S →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp g = f := by
  classical
  let π (n : ℕ) : R ⧸ I ^ (n + 2) →ₐ[R] R ⧸ I ^ (n + 1) :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  have hs (n : ℕ) : Function.Surjective (π n) :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  have hn (n : ℕ) : IsNilpotent (RingHom.ker (π n).toRingHom) := by
    refine ⟨2, ?_⟩
    change RingHom.ker
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
        I ^ (n + 2) ≤ I ^ (n + 1))) ^ 2 = ⊥
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
    apply le_antisymm _ bot_le
    exact (Ideal.map_mono (Ideal.pow_le_pow_right (by omega))).trans
      (le_of_eq (Ideal.map_quotient_self _))
  let q : (n : ℕ) → S →ₐ[R] R ⧸ I ^ (n + 1) :=
    Nat.rec (motive := fun n => S →ₐ[R] R ⧸ I ^ (n + 1))
      ((Ideal.quotientEquivAlgOfEq R (pow_one I).symm).toAlgHom.comp f)
      (fun n qn => Algebra.FormallySmooth.liftOfSurjective qn (π n) (hs n) (hn n))
  have hstep (n : ℕ) : (π n).comp (q (n + 1)) = q n :=
    Algebra.FormallySmooth.comp_liftOfSurjective (q n) (π n) (hs n) (hn n)
  let g : (n : ℕ) → S →ₐ[R] R ⧸ I ^ n
    | 0 => (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.zero_le 1))).comp (q 0)
    | n + 1 => q n
  have hg {m n : ℕ} (h : m ≤ n) :
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)).comp (g n) = g m := by
    induction n, h using Nat.le_induction with
    | base => simp [Ideal.Quotient.factorₐ_refl]
    | succ n h ih =>
      have hh : (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
          (g (n + 1)) = g n := by
        cases n with
        | zero => rfl
        | succ k => exact hstep k
      rw [← Ideal.Quotient.factorₐ_comp (R₁ := R)
        (hIJ := Ideal.pow_le_pow_right (Nat.le_succ n))
        (hJK := Ideal.pow_le_pow_right h), AlgHom.comp_assoc, hh, ih]
  refine ⟨IsAdicComplete.liftAlgHom I g hg, ?_⟩
  ext x
  have h := DFunLike.congr_fun (IsAdicComplete.mkₐ_comp_liftAlgHom I g hg 1) x
  change Ideal.Quotient.mk (I ^ 1) (IsAdicComplete.liftAlgHom I g hg x) = q 0 x at h
  apply (Ideal.quotientEquivAlgOfEq R (pow_one I).symm).injective
  exact h

private theorem splitFiniteEtale {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsSepClosed (ResidueField R)]
    (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [Algebra.Etale R S] :
    ∃ (ι : Type v) (_ : Fintype ι), Nonempty (S ≃ₐ[R] (ι → R)) := by
  classical
  let I := maximalIdeal R
  let K := R ⧸ I
  let fieldK : Field K := ResidueField.field R
  have hArtK : IsArtinianRing K := @DivisionRing.instIsArtinianRing K fieldK.toDivisionRing
  have hSep : IsSepClosed K := inferInstanceAs (IsSepClosed (ResidueField R))
  let J : Ideal S := I.map (algebraMap R S)
  let T := S ⧸ J
  let algKT : Algebra K T := Ideal.Quotient.algebraQuotientMapQuotient
  let e₀ : T ≃ₐ[K] K ⊗[R] S := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  have hFinite : Module.Finite K T := Module.Finite.of_restrictScalars_finite R K T
  have : IsArtinianRing T := @IsArtinianRing.of_finite K T _ _ _ _ hArtK hFinite
  have hEss : Algebra.EssFiniteType K T := @Algebra.EssFiniteType.of_finiteType K T _ _ algKT
    (@Module.Finite.finiteType K T _ _ algKT hFinite)
  have hEtale : Algebra.FormallyEtale K T := Algebra.FormallyEtale.of_equiv e₀.symm
  let ι := PrimeSpectrum T
  let : Fintype ι := Fintype.ofFinite ι
  let e : T ≃ₐ[K] (ι → K) := @Algebra.FormallyEtale.equivPiOfIsSepClosed K T
    fieldK _ algKT hEss hEtale hSep
  let red : S →ₐ[R] (ι → K) := (e.toAlgHom.restrictScalars R).comp (Ideal.Quotient.mkₐ R J)
  have hred : Function.Surjective red := e.surjective.comp Ideal.Quotient.mk_surjective
  have hlift (i : ι) : ∃ f : S →ₐ[R] R,
      (Ideal.Quotient.mkₐ R I).comp f = (Pi.evalAlgHom R (fun _ : ι => K) i).comp red :=
    liftToComplete I ((Pi.evalAlgHom R (fun _ : ι => K) i).comp red)
  choose f hf using hlift
  let F : S →ₐ[R] (ι → R) := AlgHom.pi f
  have hF (s : S) (i : ι) : Ideal.Quotient.mk I (F s i) = red s i :=
    DFunLike.congr_fun (hf i) s
  have hsF : Function.Surjective F := by
    apply LinearMap.surjective_of_surjective_comp_mkQ F.toLinearMap I
      (by simpa only [Ideal.jacobson_bot] using (ringJacobson_eq_maximalIdeal (R := R)).ge)
    intro q
    obtain ⟨y, rfl⟩ := (I • (⊤ : Submodule R (ι → R))).mkQ_surjective q
    obtain ⟨s, hs⟩ := hred (fun i => Ideal.Quotient.mk I (y i))
    refine ⟨s, ?_⟩
    change Submodule.Quotient.mk (F s) = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq]
    have hcoords (i : ι) : (F s - y) i ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change Ideal.Quotient.mk I (F s i - y i) = 0
      rw [map_sub, hF, congr_fun hs, sub_self]
    have hsum : (∑ i : ι, (F s - y) i • Pi.single i (1 : R)) = F s - y := by
      ext i
      simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hcoords i) Submodule.mem_top
  have : Module.Free R S := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank R S = Module.finrank R (ι → R) := by
    rw [← IsLocalRing.finrank_quotient_map (R := R) (S := S)]
    change Module.finrank K T = Module.finrank R (ι → R)
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card]
  exact ⟨ι, inferInstance,
    ⟨AlgEquiv.ofBijective F (OrzechProperty.bijective_of_surjective_of_finrank_le
      F.toLinearMap hsF hr.le)⟩⟩

theorem finiteEtalePowerSeries (S : Type v) [CommRing S] [Algebra (PowerSeries ℂ) S]
    [Module.Finite (PowerSeries ℂ) S] [Algebra.Etale (PowerSeries ℂ) S] :
    ∃ (ι : Type v) (_ : Fintype ι), Nonempty (S ≃ₐ[PowerSeries ℂ] (ι → PowerSeries ℂ)) := by
  have : IsAdicComplete (maximalIdeal (PowerSeries ℂ)) (PowerSeries ℂ) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have : IsAlgClosed (ResidueField (PowerSeries ℂ)) := IsAlgClosed.of_ringEquiv ℂ _
    (PowerSeries.residueFieldOfPowerSeries (k := ℂ)).symm
  exact splitFiniteEtale S

end OMA.Split537719

namespace OMA.Descend537719

open Polynomial
open scoped TensorProduct

variable (A O : Type*) [CommRing A] [CommRing O] [Algebra A O]
variable {B : Type*} [CommRing B] [Algebra A B]
variable {ι : Type*} [Fintype ι]

private theorem baseChange_lmul (b : B) :
    (Algebra.lmul A B b).baseChange O =
      Algebra.lmul O (O ⊗[A] B) (1 ⊗ₜ[A] b) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o b' =>
    rw [LinearMap.baseChange_tmul]
    change o ⊗ₜ[A] (b * b') = (1 ⊗ₜ[A] b) * (o ⊗ₜ[A] b')
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem charpoly_pi (v : ι → O) :
    (Algebra.lmul O (ι → O) v).charpoly = ∏ i, (X - C (v i)) := by
  classical
  let b := Pi.basisFun O ι
  rw [← LinearMap.charpoly_toMatrix _ b, ← Matrix.charpoly_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  change v i * (Pi.single j 1 : ι → O) i = Matrix.diagonal v i j
  by_cases h : i = j
  · subst j
    simp
  · simp [Pi.single_eq_of_ne h, Matrix.diagonal_apply_ne _ h]

theorem map_charpoly [Module.Free A B] [Module.Finite A B]
    (e : (O ⊗[A] B) ≃ₐ[O] (ι → O)) (b : B) :
    ((Algebra.lmul A B b).charpoly.map (algebraMap A O)) =
      ∏ i, (X - C (e (1 ⊗ₜ[A] b) i)) := by
  rw [← LinearMap.charpoly_baseChange, baseChange_lmul]
  have hc : e.toLinearEquiv.conj (Algebra.lmul O _ (1 ⊗ₜ[A] b)) =
      Algebra.lmul O _ (e (1 ⊗ₜ[A] b)) := by
    apply LinearMap.ext
    intro v
    change e ((1 ⊗ₜ[A] b) * e.symm v) = e (1 ⊗ₜ[A] b) * v
    rw [map_mul, AlgEquiv.apply_symm_apply]
  rw [← e.toLinearEquiv.charpoly_conj, hc, charpoly_pi]

variable (K L : Type*) [Field K] [Field L]
variable [Algebra A K] [Algebra O L] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A O L]

theorem coordinates_in_algebra [Module.Free A B] [Module.Finite A B]
    (hsplit : ∀ (q : K[X]) (x : L), (q.map (algebraMap K L)).Splits →
      x ∈ q.rootSet L → x ∈ Set.range (algebraMap K L))
    (hinter : ∀ z : O, algebraMap O L z ∈ Set.range (algebraMap K L) →
      z ∈ Set.range (algebraMap A O))
    (e : (O ⊗[A] B) ≃ₐ[O] (ι → O)) (b : B) (i : ι) :
    e (1 ⊗ₜ[A] b) i ∈ Set.range (algebraMap A O) := by
  classical
  let qA := (Algebra.lmul A B b).charpoly
  let q := qA.map (algebraMap A K)
  let v := e (1 ⊗ₜ[A] b)
  have hpoly : q.map (algebraMap K L) = ∏ j, (X - C (algebraMap O L (v j))) := by
    dsimp [q]
    rw [map_map, ← IsScalarTower.algebraMap_eq A K L,
      IsScalarTower.algebraMap_eq A O L, ← map_map, map_charpoly A O e b, Polynomial.map_prod]
    simp [v]
  apply hinter
  apply hsplit q
  · rw [hpoly]
    exact Splits.prod fun _ _ => Splits.X_sub_C _
  · apply ((LinearMap.charpoly_monic _).map (algebraMap A K)).mem_rootSet.mpr
    rw [← eval_map_algebraMap, hpoly, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [v])

theorem split_of_coordinates [Module.FaithfullyFlat A O]
    (hinj : Function.Injective (algebraMap A O))
    (e : (O ⊗[A] B) ≃ₐ[O] (ι → O))
    (hcoord : ∀ b : B, ∀ i : ι, e (1 ⊗ₜ[A] b) i ∈ Set.range (algebraMap A O)) :
    Nonempty (B ≃ₐ[A] (ι → A)) := by
  classical
  let j : (ι → A) →ₐ[A] (ι → O) :=
    AlgHom.pi fun i => (Algebra.ofId A O).comp (Pi.evalAlgHom A (fun _ : ι => A) i)
  have hj : Function.Injective j := fun x y h => funext fun i => hinj (congrFun h i)
  let f : B →ₐ[A] (ι → O) := (e.restrictScalars A).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hr (b : B) : f b ∈ j.range := by
    choose w hw using hcoord b
    exact ⟨w, funext hw⟩
  let je := AlgEquiv.ofInjective j hj
  let g : B →ₐ[A] (ι → A) := je.symm.toAlgHom.comp (f.codRestrict j.range hr)
  have hg (b : B) : j (g b) = f b := by
    exact congrArg Subtype.val (je.apply_symm_apply ⟨f b, hr b⟩)
  let gO := Algebra.TensorProduct.map (AlgHom.id O O) g
  let po := Algebra.TensorProduct.piScalarRight A O O ι
  have he : po.toAlgHom.comp gO = e.toAlgHom := by
    apply AlgHom.toLinearMap_injective
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul o b =>
      have h (i : ι) : algebraMap A O (g b i) = e (1 ⊗ₜ[A] b) i := congrFun (hg b) i
      have he' : e (o ⊗ₜ[A] b) = o • e (1 ⊗ₜ[A] b) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change po (gO (o ⊗ₜ[A] b)) = e (o ⊗ₜ[A] b)
      rw [he', Algebra.TensorProduct.map_tmul]
      ext i
      change (g b i) • o = o * e (1 ⊗ₜ[A] b) i
      rw [Algebra.smul_def, h, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hgo : Function.Bijective gO := by
    have hcomp : Function.Bijective (po.toAlgHom.comp gO) := he ▸ e.bijective
    refine ⟨fun _ _ h => hcomp.1 (congrArg po h), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hcomp.2 (po y)
    exact ⟨x, po.injective hx⟩
  have hlin : Function.Bijective (g.toLinearMap.lTensor O) := by
    change Function.Bijective gO at hgo
    convert hgo using 1
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul o b => simp [gO, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact ⟨AlgEquiv.ofBijective g
    ((Module.FaithfullyFlat.lTensor_bijective_iff_bijective A O g.toLinearMap).mp hlin)⟩

end OMA.Descend537719

namespace OMA.Cubic537719

open scoped TensorProduct
open Algebra.TensorProduct

section SimpleRoot

variable {A : Type} [CommRing A] [IsLocalRing A]

theorem notHenselian_of_cubic (t : A) (ht : IsLocalRing.residue A t = 0)
    (hne : ∀ r : A, r ^ 3 - r ^ 2 ≠ t) : ¬ OMA.S_mse_537719.IsHenselianLocal A := by
  intro h
  let p : Polynomial A :=
    Polynomial.X ^ 3 - (Polynomial.X ^ 2 + Polynomial.C t)
  have hp : p.Monic := by
    apply Polynomial.monic_X_pow_sub
    refine (Polynomial.degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · norm_num [Polynomial.degree_X_pow]
    · exact Polynomial.degree_C_le.trans_lt (by norm_num)
  have h0 : IsLocalRing.residue A (p.eval 1) = 0 := by
    simp [p, ht]
  have h1 : IsLocalRing.residue A (p.derivative.eval 1) ≠ 0 := by
    norm_num [p, Polynomial.derivative_pow]
  obtain ⟨r, hr, _⟩ := h p 1 hp h0 h1
  apply hne r
  simp [p] at hr
  linear_combination hr

end SimpleRoot

section Products

variable (A : Type) [CommRing A]

private theorem exists_eval_of_algHom_pi [IsLocalRing A] {ι : Type} [Fintype ι]
    (f : (ι → A) →ₐ[A] A) : ∃ i : ι, ∀ x : ι → A, f x = x i := by
  classical
  let e : ι → (ι → A) := fun i => Pi.single i 1
  have hsum : (∑ i, e i) = 1 := by
    ext j
    simp [e, Finset.sum_apply]
  have hfind : ∃ i, f (e i) ≠ 0 := by
    by_contra! h
    have hf := congrArg f hsum
    simp [map_sum, h] at hf
  obtain ⟨i, hi⟩ := hfind
  have hmul : e i * e i = e i := by
    ext j
    by_cases h : j = i <;> simp [e, h]
  have hidem : f (e i) * f (e i) = f (e i) := by
    rw [← map_mul, hmul]
  have hfi : f (e i) = 1 := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (f (e i)) with hunit | hunit
    · apply hunit.mul_left_cancel
      simpa using hidem
    · exfalso
      apply hi
      apply hunit.mul_right_cancel
      rw [mul_sub, mul_one, hidem, sub_self, zero_mul]
  refine ⟨i, fun x => ?_⟩
  have hx : e i * x = (algebraMap A (ι → A) (x i)) * e i := by
    ext j
    by_cases h : j = i <;> simp [e, h]
  simpa [map_mul, hfi] using congrArg f hx

private def reindex {ι ν : Type} (σ : ν → ι) : (ι → A) →ₐ[A] (ν → A) :=
  AlgHom.pi fun i => Pi.evalAlgHom A (fun _ => A) (σ i)

@[simp] private theorem reindex_apply {ι ν : Type} (σ : ν → ι) (x : ι → A) (j : ν) :
    reindex A σ x j = x (σ j) := rfl

private theorem reindex_bijective [IsLocalRing A] {ι ν : Type} [Fintype ι] :
    Function.Bijective (reindex A : (ν → ι) → ((ι → A) →ₐ[A] (ν → A))) := by
  classical
  constructor
  · intro σ τ h
    funext j
    by_contra hn
    have hval := congrFun (AlgHom.congr_fun h (Pi.single (σ j) (1 : A))) j
    have hn' : τ j ≠ σ j := fun he => hn he.symm
    simp [hn'] at hval
  · intro f
    choose σ hσ using fun j : ν =>
      exists_eval_of_algHom_pi A ((Pi.evalAlgHom A (fun _ => A) j).comp f)
    refine ⟨σ, AlgHom.ext fun x => funext fun j => ?_⟩
    exact (hσ j x).symm

end Products

section BaseChange

variable (A : Type) [CommRing A] [IsLocalRing A]

private abbrev Residue := IsLocalRing.ResidueField A

private noncomputable def changeToPower {B : Type} [CommRing B] [Algebra A B]
    {n : ℕ} (e : B ≃ₐ[A] Fin n → A) : ((Residue A) ⊗[A] B) ≃ₐ[(Residue A)] Fin n → (Residue A) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := (Residue A)) (A₁ := (Residue A))) e).trans
    (Algebra.TensorProduct.piScalarRight A (Residue A) (Residue A) (Fin n))

@[simp] private theorem changeToPower_tmul {B : Type} [CommRing B] [Algebra A B]
    {n : ℕ} (e : B ≃ₐ[A] Fin n → A) (a : (Residue A)) (b : B) (j : Fin n) :
    changeToPower A e (a ⊗ₜ[A] b) j = e b j • a := rfl

private theorem bijective_baseChange_of_split {B₁ B₂ : Type}
    [CommRing B₁] [CommRing B₂] [Algebra A B₁] [Algebra A B₂]
    [Algebra.IsFiniteSplit A B₁] [Algebra.IsFiniteSplit A B₂] :
    Function.Bijective (fun φ : B₁ →ₐ[A] B₂ =>
      Algebra.TensorProduct.map (AlgHom.id (Residue A) (Residue A)) φ) := by
  obtain ⟨n₁, ⟨e₁⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun A B₁
  obtain ⟨n₂, ⟨e₂⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun A B₂
  let u₁ := changeToPower A e₁
  let u₂ := changeToPower A e₂
  let a := (Equiv.ofBijective (reindex A)
    (reindex_bijective A (ι := Fin n₁) (ν := Fin n₂))).trans (AlgEquiv.arrowCongr e₁ e₂).symm
  let b := (Equiv.ofBijective (reindex (Residue A))
    (reindex_bijective (Residue A) (ι := Fin n₁) (ν := Fin n₂))).trans (AlgEquiv.arrowCongr u₁ u₂).symm
  let F := fun φ : B₁ →ₐ[A] B₂ => Algebra.TensorProduct.map (AlgHom.id (Residue A) (Residue A)) φ
  have happ (σ : Fin n₂ → Fin n₁) (x : B₁) (j : Fin n₂) :
      e₂ (a σ x) j = e₁ x (σ j) := by
    simp [a, AlgEquiv.arrowCongr_symm, AlgEquiv.arrowCongr_apply]
  have happ' (σ : Fin n₂ → Fin n₁) (x : (Residue A) ⊗[A] B₁) (j : Fin n₂) :
      u₂ (b σ x) j = u₁ x (σ j) := by
    simp [b, AlgEquiv.arrowCongr_symm, AlgEquiv.arrowCongr_apply]
  have heq : F ∘ a = b := by
    funext σ
    apply AlgHom.ext
    intro x
    apply u₂.injective
    funext j
    rw [happ']
    change u₂ (F (a σ) x) j = u₁ x (σ j)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a' x =>
      simp only [F, map_tmul, AlgHom.id_apply, u₁, u₂, changeToPower_tmul]
      rw [happ]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  apply (a.bijective_comp F).mp
  rw [heq]
  exact b.bijective

theorem baseChangeEquiv_of_split [IsSepClosed (Residue A)]
    (hsplit : ∀ (B : Type) [CommRing B] [Algebra A B],
      Module.Finite A B → Algebra.Etale A B → Algebra.IsFiniteSplit A B) :
    OMA.S_mse_537719.BaseChangeEquiv A := by
  constructor
  · intro C _ _ hfinite hetale
    let _ := hfinite
    let _ := hetale
    obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun (Residue A) C
    refine ⟨Fin n → A, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
    exact (Algebra.TensorProduct.piScalarRight A (Residue A) (Residue A) (Fin n)).trans e.symm
  · intro B₁ B₂ _ _ _ _ hf₁ he₁ hf₂ he₂
    let _ := hsplit B₁ hf₁ he₁
    let _ := hsplit B₂ hf₂ he₂
    exact bijective_baseChange_of_split A

end BaseChange

end OMA.Cubic537719

namespace OMA.Assembly537719

open Polynomial
open scoped RatFunc TensorProduct

private noncomputable def cubic : (RatFunc ℂ)[X] := X ^ 3 - X ^ 2 - C RatFunc.X

private theorem cubic_natDegree : cubic.natDegree = 3 := by
  have hpow : ((X : (RatFunc ℂ)[X]) ^ 2).natDegree <
      ((X : (RatFunc ℂ)[X]) ^ 3).natDegree := by simp
  have hsub : ((X : (RatFunc ℂ)[X]) ^ 3 - X ^ 2).natDegree = 3 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt hpow, natDegree_X_pow]
  unfold cubic
  rw [natDegree_sub_eq_left_of_natDegree_lt (by simp [hsub]), hsub]

private theorem cubic_monic : cubic.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 3 (le_of_eq cubic_natDegree)
  simp [cubic, coeff_X_pow]

private theorem cubic_no_root (r : RatFunc ℂ) : ¬ cubic.IsRoot r := by
  intro hr
  apply Cubic537719.ratFunc_no_root r
  apply sub_eq_zero.mp
  simpa [cubic, IsRoot] using hr

private theorem cubic_not_splits :
    ¬ (cubic.map (algebraMap (RatFunc ℂ) (LaurentSeries ℂ))).Splits := by
  apply Field537719.not_splits_of_unique cubic_natDegree cubic_no_root
  intro x y hx hy
  have ht : algebraMap (RatFunc ℂ) (LaurentSeries ℂ) RatFunc.X =
      ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) := by
    change ((RatFunc.X : RatFunc ℂ) : LaurentSeries ℂ) = _
    rw [RatFunc.coe_X, PowerSeries.coe_X]
  have hx' : x ^ 3 - x ^ 2 = ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) := by
    apply sub_eq_zero.mp
    simpa only [cubic, map_sub, map_pow, aeval_X, aeval_C, ht] using hx
  have hy' : y ^ 3 - y ^ 2 = ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) := by
    apply sub_eq_zero.mp
    simpa only [cubic, map_sub, map_pow, aeval_X, aeval_C, ht] using hy
  exact Cubic537719.laurent_root_unique hx' hy'

theorem exists_required_ring :
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A),
      OMA.S_mse_537719.BaseChangeEquiv A ∧ ¬ OMA.S_mse_537719.IsHenselianLocal A := by
  classical
  obtain ⟨K, hK⟩ := Field537719.exists_maximal (L := LaurentSeries ℂ) cubic cubic_no_root
  let A := Ring537719.intRing K
  let O := PowerSeries ℂ
  have hsplit (q : K[X]) (x : LaurentSeries ℂ)
      (hq : (q.map (algebraMap K (LaurentSeries ℂ))).Splits) (hx : x ∈ q.rootSet (LaurentSeries ℂ)) :
      x ∈ Set.range (algebraMap K (LaurentSeries ℂ)) :=
    ⟨⟨x, Field537719.mem_of_splits cubic_natDegree cubic_monic cubic_not_splits hK hq hx⟩, rfl⟩
  let : IsAlgClosed (IsLocalRing.ResidueField A) :=
    IsAlgClosed.of_ringEquiv ℂ _ (Ring537719.intRing_residueEquiv K).symm
  refine ⟨A, inferInstance, inferInstance, Cubic537719.baseChangeEquiv_of_split A ?_, ?_⟩
  · intro B _ _ hfinite hetale
    let : Module.Finite A B := hfinite
    let : Algebra.Etale A B := hetale
    let : Module.Free A B := Module.free_of_flat_of_isLocalRing
    obtain ⟨ι, _, ⟨e⟩⟩ := Split537719.finiteEtalePowerSeries (O ⊗[A] B)
    have hc : ∀ (b : B) (i : ι), e (1 ⊗ₜ[A] b) i ∈ Set.range (algebraMap A O) :=
      fun b i => Descend537719.coordinates_in_algebra A O K (LaurentSeries ℂ) hsplit
        (Ring537719.intRing_intersection K) e b i
    obtain ⟨g⟩ := Descend537719.split_of_coordinates A O
      (Ring537719.toPower_injective (Ring537719.fieldEmbedding K)) e hc
    exact Algebra.IsFiniteSplit.of_algEquiv g.symm
  · refine Cubic537719.notHenselian_of_cubic (Ring537719.parameter K)
      (Ring537719.parameter_residue_zero K) fun r hr => ?_
    let a : K := algebraMap A K r
    have ha : a ^ 3 - a ^ 2 = Ring537719.baseLift K RatFunc.X := by
      change algebraMap (Ring537719.intRing K) K r ^ 3 -
        algebraMap (Ring537719.intRing K) K r ^ 2 = Ring537719.baseLift K RatFunc.X
      simpa only [a, map_pow, map_sub, Ring537719.parameter_algebraMap] using
        congrArg (algebraMap (Ring537719.intRing K) K) hr
    apply hK.1 (a : LaurentSeries ℂ) a.property
    have hcoef : algebraMap K (LaurentSeries ℂ) (Ring537719.baseLift K RatFunc.X) =
        algebraMap (RatFunc ℂ) (LaurentSeries ℂ) RatFunc.X := rfl
    have hroot : (algebraMap K (LaurentSeries ℂ) a) ^ 3 -
        (algebraMap K (LaurentSeries ℂ) a) ^ 2 = algebraMap (RatFunc ℂ) (LaurentSeries ℂ) RatFunc.X := by
      simpa only [map_pow, map_sub, hcoef] using
        congrArg (algebraMap K (LaurentSeries ℂ)) ha
    change (a : LaurentSeries ℂ) ^ 3 - (a : LaurentSeries ℂ) ^ 2 =
      algebraMap (RatFunc ℂ) (LaurentSeries ℂ) RatFunc.X at hroot
    simpa only [cubic, map_sub, map_pow, aeval_X, aeval_C] using sub_eq_zero.mpr hroot

end OMA.Assembly537719

theorem OMA.solution : type_of% @OMA.S_mse_537719.main :=
  OMA.Assembly537719.exists_required_ring
