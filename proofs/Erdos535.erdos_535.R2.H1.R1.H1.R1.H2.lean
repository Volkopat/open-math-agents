import OMAReductions.R_Erdos535_erdos_535_R2_H1_R1_H1_R1
import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Subadditive
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.Real.Lemmas

-- Step Erdos535.erdos_535.R2.H1.R1.H1.R1.H2. Its statement is word for word step Erdos535.erdos_535.variants.sunflower_strong.R1.H1.R1.H1.R1.H2, whose merged proof
-- (proofs/Erdos535.erdos_535.variants.sunflower_strong.R1.H1.R1.H1.R1.H2.lean) is reused below; only the target namespace changed.
/- Copyright OpenAI. Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6. Apache-2.0; see LICENSE. Conditional consumer only: PlanarPrices remains a hypothesis. -/

-- Source module: OAI.LinearAlgebra.SpectralBooks.Crossing
section

/-!
# Expanding a restriction of a power of a direct sum of wires

A wire is given by the sum of the coordinate basis tensors indexed by its possible
bit strings. Direct sum tags those basis tensors at every site, while tensor power
takes tuples of independently chosen basis tensors. We expand arbitrary local linear
images of these tensors into an ordinary sum of networks with the same output legs.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace Crossing

noncomputable section

variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]

/-- An ordered description of an unoriented wire between distinct sites. -/
structure Wire (I : Type*) where
  left : I
  right : I
  distinct : left ≠ right
  width : ℕ

/-- A local index has one bit per wire bit at an endpoint and no bits elsewhere. -/
abbrev Wire.Leg (e : Wire I) (i : I) :=
  {_t : Fin e.width // i = e.left ∨ i = e.right} → Bool

/-- The two endpoints see the same string. -/
def Wire.basisTerm (e : Wire I) (s : Fin e.width → Bool) (i : I) : e.Leg i :=
  fun t => s t.val

/-- Coefficients of a tensor presented as a finite sum of coordinate basis tensors. -/
def basisTensor {A : I → Type*} {S : Type*} [Fintype S]
    (term : S → ∀ i, A i) (x : ∀ i, A i) : F :=
  ∑ s, if x = term s then 1 else 0

/-- On basis terms, a tensor direct sum tags every site's input by the same summand. -/
def sumBasis {L : Type*} {S : L → Type*} {A : L → I → Type*}
    (term : ∀ l, S l → ∀ i, A l i) (s : Σ l, S l) (i : I) : Σ l, A l i :=
  ⟨s.1, term s.1 s.2 i⟩

/-- A basis term of a grouped power chooses the terms of the factors independently. -/
def powerBasis {S : Type*} {A : I → Type*}
    (term : S → ∀ i, A i) (j : ℕ) (s : Fin j → S) (i : I) : Fin j → A i :=
  fun t => term (s t) i

/-- Direct sum of identical copies, recording the copy index at every site. -/
def copiesBasis {S : Type*} {A : I → Type*}
    (term : S → ∀ i, A i) (K : ℕ) (s : Fin K × S) (i : I) : Fin K × A i :=
  (s.1, term s.2 i)

/-- On the block tagged by one summand, the direct sum has precisely the coefficients
of that summand. At least one site is needed to distinguish the tags. -/
theorem basisTensor_sum_onBlock {L : Type*} [Fintype L] {S : L → Type*}
    [∀ l, Fintype (S l)] {A : L → I → Type*} [Nonempty I]
    (term : ∀ l, S l → ∀ i, A l i) (l : L) (x : ∀ i, A l i) :
    basisTensor (F := F) (sumBasis term) (fun i => ⟨l, x i⟩) = basisTensor (term l) x := by
  classical
  unfold basisTensor
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single l]
  · refine Finset.sum_congr rfl fun s _ => ?_
    have h : (fun i => (⟨l, x i⟩ : Σ l, A l i)) = sumBasis term ⟨l, s⟩ ↔ x = term l s := by
      constructor
      · intro h
        funext i
        exact Sigma.mk.inj_iff.mp (congrFun h i) |>.2 |>.eq
      · rintro rfl
        rfl
    simp [h]
  · intro l' _ hne
    refine Finset.sum_eq_zero fun s _ => if_neg fun h => hne ?_
    let i := Classical.choice (inferInstance : Nonempty I)
    exact (congrArg Sigma.fst (congrFun h i)).symm
  · simp

/-- Mixed tags have zero coefficient in a tensor direct sum. -/
theorem basisTensor_sum_offBlock {L : Type*} [Fintype L] {S : L → Type*}
    [∀ l, Fintype (S l)] {A : L → I → Type*} (term : ∀ l, S l → ∀ i, A l i)
    (x : ∀ i, Σ l, A l i) (h : ¬ ∃ l, ∀ i, (x i).1 = l) :
    basisTensor (F := F) (sumBasis term) x = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  apply if_neg
  rintro rfl
  exact h ⟨s.1, fun _ => rfl⟩

/-- The grouped tensor power has the product of the original coefficients. -/
theorem basisTensor_power {S : Type*} [Fintype S] {A : I → Type*}
    (term : S → ∀ i, A i) (j : ℕ) (x : ∀ i, Fin j → A i) :
    basisTensor (F := F) (powerBasis term j) x =
      ∏ t, basisTensor (F := F) term (fun i => x i t) := by
  classical
  unfold basisTensor
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fintype.prod_boole]
  have h : x = powerBasis term j w ↔ ∀ t, (fun i => x i t) = term (w t) := by
    constructor
    · rintro rfl t
      rfl
    · intro ht
      funext i t
      exact congrFun (ht t) i
  simp [h]

/-- The matrix-coefficient definition of restriction by local linear maps. -/
def IsRestriction {A B : I → Type*} [∀ i, Fintype (A i)]
    (X : (∀ i, B i) → F) (Y : (∀ i, A i) → F) : Prop :=
  ∃ M : ∀ i, B i → A i → F, ∀ x,
    X x = ∑ a, Y a * ∏ i, M i (x i) (a i)

/-- Applying matrices to a sum of basis tensors sums the transformed pure tensors. -/
theorem restriction_basisTensor_iff {A B : I → Type*} [∀ i, Fintype (A i)]
    {S : Type*} [Fintype S] (term : S → ∀ i, A i) (X : (∀ i, B i) → F) :
    IsRestriction X (basisTensor term) ↔
      ∃ M : ∀ i, B i → A i → F, ∀ x, X x = ∑ s, ∏ i, M i (x i) (term s i) := by
  unfold IsRestriction basisTensor
  congr! 3 with M x
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- The leaf matrices of a network may jointly read all strings on incident wires. -/
abbrev LocalTables {B : I → Type*} {j : ℕ} (wires : Fin j → Wire I) (F : Type*) :=
  ∀ i, B i → ((t : Fin j) → (wires t).Leg i) → F

/-- Coefficients of a network, obtained by contracting one shared index for each wire. -/
def network {B : I → Type*} {j : ℕ} (wires : Fin j → Wire I)
    (T : LocalTables (B := B) wires F) (x : ∀ i, B i) : F :=
  ∑ s : (t : Fin j) → (Fin (wires t).width → Bool),
    ∏ i, T i (x i) (fun t => (wires t).basisTerm (s t) i)

/-- Reindex a word of tagged strings by first choosing the word of tags. -/
private def splitTags {J L : Type*} (S : L → Type*) :
    (J → Σ l, S l) ≃ (Σ w : J → L, (t : J) → S (w t)) where
  toFun s := ⟨fun t => (s t).1, fun t => (s t).2⟩
  invFun s t := ⟨s.1 t, s.2 t⟩
  left_inv := by intro s; rfl
  right_inv := by rintro ⟨w, s⟩; rfl

/-- The tensor in the strict comparison step, in the coordinate bases of its direct
sums and grouped tensor powers. -/
def copiesOfWirePower {E : Type*} [Fintype E] (wires : E → Wire I) (K j : ℕ) :=
  basisTensor (F := F) (copiesBasis (powerBasis (sumBasis fun l => (wires l).basisTerm) j) K)

/-- Ordinary local-matrix restriction from the tensor used in strict comparison. -/
def RestrictsWirePower {B : I → Type*} {E : Type*} [Fintype E]
    (X : (∀ i, B i) → F) (wires : E → Wire I) (K j : ℕ) : Prop :=
  IsRestriction X (copiesOfWirePower wires K j)

/-- Restricting the direct sum of `K` copies of `W^⊗j`, where `W` is a direct sum
of `L` wires, gives an ordinary sum indexed by a copy and a word of `j` wire choices. -/
theorem restriction_copiesOfWirePower {B : I → Type*} {E : Type*} [Fintype E] {K j : ℕ}
    (wires : E → Wire I) (X : (∀ i, B i) → F)
    (h : RestrictsWirePower X wires K j) :
    ∃ T : (k : Fin K) → (w : Fin j → E) → LocalTables (B := B) (wires ∘ w) F,
      ∀ x, X x = ∑ k, ∑ w, network (wires ∘ w) (T k w) x := by
  obtain ⟨M, hM⟩ := (restriction_basisTensor_iff _ X).mp h
  refine ⟨fun k w i y a => M i y (k, fun t => ⟨w t, a t⟩), ?_⟩
  intro x
  rw [hM, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  let e := splitTags (J := Fin j) (fun l => Fin (wires l).width → Bool)
  simp only [network]
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- Number of network summands in the expansion. -/
theorem card_networks (K L j : ℕ) :
    Fintype.card (Fin K × (Fin j → Fin L)) = K * L ^ j := by simp

/-- With sites placed in a metric space, supply its distance for `length`. -/
def wireCost (length : I → I → ℝ) (e : Wire I) : ℝ :=
  e.width * length e.left e.right

omit [Fintype I] in
/-- Absorbing arbitrary local matrices does not increase the cost of a word of wires. -/
theorem network_cost_le {E : Type*} {j : ℕ} {bound : ℝ} (length : I → I → ℝ)
    (wires : E → Wire I) (h : ∀ l, wireCost length (wires l) ≤ bound)
    (w : Fin j → E) :
    ∑ t, wireCost length (wires (w t)) ≤ bound * j := by
  simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun t _ => h (w t))

end
end Crossing

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.Restriction
section

/-!
# Composition and reindexing of tensor restrictions
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

open Crossing

variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]
variable {A B C : I → Type*} [∀ i, Fintype (A i)]

/-- Relabeling the coordinate basis at each site gives a restriction. -/
theorem restrict_of_equiv {X : (∀ i, B i) → F} {Y : (∀ i, A i) → F}
    (e : ∀ i, B i ≃ A i) (h : ∀ x, X x = Y (fun i => e i (x i))) :
    IsRestriction X Y := by
  classical
  refine ⟨fun i b a => if a = e i b then 1 else 0, fun x => ?_⟩
  rw [h x]
  simp_rw [Fintype.prod_boole]
  have heq (a : ∀ i, A i) : (∀ i, a i = e i (x i)) ↔ a = fun i => e i (x i) :=
    funext_iff.symm
  simp [heq, mul_ite]

/-- Identity matrices give the reflexive restriction. -/
theorem restrict_refl (X : (∀ i, A i) → F) : IsRestriction X X :=
  restrict_of_equiv (fun i => Equiv.refl (A i)) fun _ => rfl

/-- Local matrix multiplication composes two restrictions. -/
theorem restrict_trans [∀ i, Fintype (B i)] {X : (∀ i, C i) → F}
    {Y : (∀ i, B i) → F} {Z : (∀ i, A i) → F}
    (hXY : IsRestriction X Y) (hYZ : IsRestriction Y Z) : IsRestriction X Z := by
  classical
  obtain ⟨M, hM⟩ := hXY
  obtain ⟨N, hN⟩ := hYZ
  refine ⟨fun i c a => ∑ b, N i b a * M i c b, fun x => ?_⟩
  rw [hM x]
  simp_rw [hN, Finset.sum_mul, Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib,
    mul_assoc]
  exact Finset.sum_comm

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw
section

/-! # Finite coefficient tensors and local restriction

The coordinate type at each site is arbitrary and finite. Keeping the local
types in the format lets the tensor product use pairs of basis indices and the
direct sum use disjoint unions. Mutual restriction identifies changes of basis
and redundant local dimensions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

/-- A finite local format, together with the tensor's coefficients. -/
structure Raw (I : Type u) (K : Type w) where
  Leg : I → Type v
  finiteLeg : ∀ i, Fintype (Leg i)
  coeff : (∀ i, Leg i) → K

instance Raw.instFintypeLeg {I : Type u} {K : Type w} (X : Raw.{v} I K) (i : I) :
    Fintype (X.Leg i) := X.finiteLeg i



namespace Raw

variable {I : Type u} {K : Type w}

noncomputable section
open scoped Classical

/-- Restriction by one matrix at each site, expressed in the chosen bases. -/
abbrev Restricts [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) :=
  Crossing.IsRestriction X.coeff Y.coeff

/-- The equivalence relation used to form the tensor semiring. -/
def Equivalent [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) : Prop :=
  X.Restricts Y ∧ Y.Restricts X

/-- Mutual restriction is a setoid by composition of local matrices. -/
def setoid (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] : Setoid (Raw.{v} I K) where
  r := Equivalent
  iseqv := ⟨fun X => ⟨restrict_refl X.coeff, restrict_refl X.coeff⟩,
    fun h => And.symm h, fun h g => ⟨restrict_trans h.1 g.1, restrict_trans g.2 h.2⟩⟩

/-- Relabeling each coordinate basis by a bijection preserves mutual restriction. -/
theorem reindex_equivalent [Fintype I] [CommSemiring K] {X Y : Raw.{v} I K}
    (e : ∀ i, X.Leg i ≃ Y.Leg i) (h : ∀ x, X.coeff x = Y.coeff (fun i => e i (x i))) :
    X.Equivalent Y := by
  refine ⟨restrict_of_equiv e h, restrict_of_equiv (fun i => (e i).symm) ?_⟩
  intro y
  simpa using (h (fun i => (e i).symm (y i))).symm

/-- The empty local format represents the additive identity. -/
def zero (I : Type u) (K : Type w) [Zero K] : Raw.{v} I K :=
  ⟨fun _ => PEmpty, fun _ => inferInstance, fun _ => 0⟩

/-- The scalar unit has one basis vector at each site. -/
def one (I : Type u) (K : Type w) [One K] : Raw.{v} I K :=
  ⟨fun _ => PUnit, fun _ => inferInstance, fun _ => 1⟩

/-- Tensor multiplication groups the two local factors at each site. -/
def mul [Mul K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => X.Leg i × Y.Leg i, fun _ => inferInstance,
    fun x => X.coeff (fun i => (x i).1) * Y.coeff (fun i => (x i).2)⟩

/-- The common-label diagonal, with one summand per label. -/
def diagonal (I : Type u) (K : Type w) (α : Type v) [Fintype α] [CommSemiring K] : Raw.{v} I K :=
  ⟨fun _ => α, fun _ => inferInstance, fun x => ∑ a : α, if x = fun _ => a then 1 else 0⟩

end
end Raw

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.Product
section

/-!
# Products preserve tensor restriction

The site matrices for two restrictions act on paired basis indices by their
Kronecker products.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

variable {I F : Type*} [Fintype I] [CommSemiring F]
  {A B C D : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

/-- The tensor product of two local restrictions is a local restriction. -/
theorem restrict_product
    {X : (∀ i, A i) → F} {Y : (∀ i, B i) → F}
    {X' : (∀ i, C i) → F} {Y' : (∀ i, D i) → F}
    (hX : Crossing.IsRestriction X' X) (hY : Crossing.IsRestriction Y' Y) :
    Crossing.IsRestriction
      (fun a : ∀ i, C i × D i => X' (fun i => (a i).1) * Y' (fun i => (a i).2))
      (fun a : ∀ i, A i × B i => X (fun i => (a i).1) * Y (fun i => (a i).2)) := by
  classical
  obtain ⟨M, hM⟩ := hX
  obtain ⟨N, hN⟩ := hY
  refine ⟨fun i x a => M i x.1 a.1 * N i x.2 a.2, fun x => ?_⟩
  dsimp
  rw [hM, hN, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow I A B).symm _ _ fun a => ?_
  simp only [Finset.prod_mul_distrib]
  ac_rfl

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.SumDef
section

/-! # Direct sums in coordinates

The direct sum of tensors extends their coefficient functions by zero along the
two summand inclusions at every site and adds the resulting coefficients.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

noncomputable section

variable {X Y Z K : Type*} [Fintype X]

/-- Push coefficients forward by summing on fibers. -/
def pushCoeff [AddCommMonoid K] (f : X → Y) (T : X → K) (y : Y) : K :=
  ∑ x, if f x = y then T x else 0

/-- Successive pushes sum over the fibers of the composite. -/
theorem pushCoeff_comp [AddCommMonoid K] [Fintype Y]
    (g : Y → Z) (f : X → Y) (T : X → K) :
    pushCoeff g (pushCoeff f T) = pushCoeff (g ∘ f) T := by
  funext z
  unfold pushCoeff
  have hs (y : Y) : (if g y = z then ∑ x, if f x = y then T x else 0 else 0) =
      ∑ x, if g y = z then if f x = y then T x else 0 else 0 := by
    by_cases h : g y = z <;> simp [h]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

/-- Fiberwise summation preserves addition. -/
theorem pushCoeff_add [AddCommMonoid K] (f : X → Y) (T U : X → K) :
    pushCoeff f (T + U) = pushCoeff f T + pushCoeff f U := by
  funext y
  simp only [pushCoeff, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp

/-- A bijection transports each coefficient to its new index. -/
theorem pushCoeff_equiv [AddCommMonoid K] (e : X ≃ Y) (T : X → K) (y : Y) :
    pushCoeff e T y = T (e.symm y) := by
  simp [pushCoeff, ← e.eq_symm_apply]

/-- Contracting a pushed tensor pulls the test coefficients back. -/
theorem sum_pushCoeff_mul [Semiring K] [Fintype Y] (f : X → Y) (T : X → K) (g : Y → K) :
    ∑ y, pushCoeff f T y * g y = ∑ x, T x * g (f x) := by
  simp only [pushCoeff, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

variable {I : Type*} [Fintype I] {A B : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [AddCommMonoid K]

/-- Block direct sum, with a copy of the summand label at every site. -/
def sumCoeff (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (y : ∀ i, A i ⊕ B i) : K :=
  pushCoeff (fun x i => Sum.inl (x i)) T y + pushCoeff (fun x i => Sum.inr (x i)) U y

/-- The all-left block carries the first tensor. -/
theorem sumCoeff_inl [Nonempty I] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, A i) : sumCoeff T U (fun i => Sum.inl (x i)) = T x := by
  have hl (y : ∀ i, A i) : (fun i => (Sum.inl (y i) : A i ⊕ B i)) =
      (fun i => Sum.inl (x i)) ↔ y = x := by
    simp [funext_iff]
  have hr (y : ∀ i, B i) : (fun i => (Sum.inr (y i) : A i ⊕ B i)) ≠
      (fun i => Sum.inl (x i)) := by
    intro h
    cases congrFun h (Classical.arbitrary I)
  simp [sumCoeff, pushCoeff, hl, hr]

/-- The all-right block carries the second tensor. -/
theorem sumCoeff_inr [Nonempty I] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, B i) : sumCoeff T U (fun i => Sum.inr (x i)) = U x := by
  have hr (y : ∀ i, B i) : (fun i => (Sum.inr (y i) : A i ⊕ B i)) =
      (fun i => Sum.inr (x i)) ↔ y = x := by
    simp [funext_iff]
  have hl (y : ∀ i, A i) : (fun i => (Sum.inl (y i) : A i ⊕ B i)) ≠
      (fun i => Sum.inr (x i)) := by
    intro h
    cases congrFun h (Classical.arbitrary I)
  simp [sumCoeff, pushCoeff, hl, hr]

/-- Every mixed block has zero coefficient. -/
theorem sumCoeff_mixed (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (y : ∀ i, A i ⊕ B i)
    (hl : ∀ x : ∀ i, A i, (fun i => Sum.inl (x i)) ≠ y)
    (hr : ∀ x : ∀ i, B i, (fun i => Sum.inr (x i)) ≠ y) :
    sumCoeff T U y = 0 := by
  simp [sumCoeff, pushCoeff, hl, hr]

end

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.Ops
section

/-! # Direct sum of finite coefficient tensors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

universe v u w

variable {I : Type u} {K : Type w} [Fintype I]

/-- The direct sum uses a disjoint union at every site. -/
noncomputable def add [AddCommMonoid K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => X.Leg i ⊕ Y.Leg i, fun _ => inferInstance, sumCoeff X.coeff Y.coeff⟩

/-- Tensoring the local restricting maps restricts a product. -/
theorem mul_restricts [CommSemiring K] {X Y U V : Raw.{v} I K}
    (h : X.Restricts Y) (h' : U.Restricts V) : (X.mul U).Restricts (Y.mul V) :=
  restrict_product h h'

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.Quotient
section

/-! # Tensor classes ordered by restriction

Mutual restriction identifies precisely those tensors with the same upper and lower
bounds in the local restriction preorder.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

/-- Finite site tensors up to mutual restriction. -/
def TensorClass (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] :=
  Quotient (Raw.setoid.{v} I K)

variable {I : Type u} {K : Type w} [Fintype I] [CommSemiring K]

/-- Pass a coefficient tensor to its class under mutual restriction. -/
def ofRaw (X : Raw.{v} I K) : TensorClass.{v} I K :=
  Quotient.mk _ X

@[simp] theorem ofRaw_eq_iff {X Y : Raw.{v} I K} :
    ofRaw X = ofRaw Y ↔ X.Equivalent Y := Quotient.eq

instance : LE (TensorClass.{v} I K) where
  le := Quotient.lift₂ Raw.Restricts fun _ _ _ _ hX hY => propext
    ⟨fun h => restrict_trans hX.2 (restrict_trans h hY.1),
     fun h => restrict_trans hX.1 (restrict_trans h hY.2)⟩

@[simp] theorem ofRaw_le_iff {X Y : Raw.{v} I K} :
    ofRaw X ≤ ofRaw Y ↔ X.Restricts Y := Iff.rfl

instance : PartialOrder (TensorClass.{v} I K) where
  le_refl X := Quotient.inductionOn X fun x => restrict_refl x.coeff
  le_trans X Y Z := Quotient.inductionOn₃ X Y Z fun _ _ _ => restrict_trans
  le_antisymm X Y := Quotient.inductionOn₂ X Y fun _ _ h g => Quotient.sound ⟨h, g⟩

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.Sum
section

/-! # Direct sums preserve tensor restrictions -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

open Crossing

variable {I : Type*} [Fintype I] {K : Type*} [CommSemiring K]
variable {A B C D : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, Fintype (C i)] [∀ i, Fintype (D i)]

omit [∀ i, Fintype (C i)] in
/-- Pushing output indices after a restriction sums the rows of each local matrix
over the corresponding fibers. -/
theorem pushCoeff_restriction {X : (∀ i, B i) → K} {T : (∀ i, A i) → K}
    (M : ∀ i, B i → A i → K)
    (hM : ∀ x, X x = ∑ a, T a * ∏ i, M i (x i) (a i))
    (f : ∀ i, B i → C i) (y : ∀ i, C i) :
    pushCoeff (fun x i => f i (x i)) X y =
      ∑ a, T a * ∏ i, ∑ b, if f i b = y i then M i b (a i) else 0 := by
  simp only [Fintype.prod_sum, Finset.mul_sum, Fintype.prod_ite_zero, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  unfold pushCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hM x, funext_iff]
  split <;> simp [*]

/-- Apply the two given restrictions on their respective diagonal blocks. -/
theorem restrict_sum {X : (∀ i, B i) → K} {Y : (∀ i, D i) → K}
    {T : (∀ i, A i) → K} {U : (∀ i, C i) → K}
    (h : IsRestriction X T) (h' : IsRestriction Y U) :
    IsRestriction (sumCoeff X Y) (sumCoeff T U) := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨N, hN⟩ := h'
  let L (i : I) : B i ⊕ D i → A i ⊕ C i → K
    | .inl b, .inl a => M i b a
    | .inr d, .inr c => N i d c
    | _, _ => 0
  refine ⟨L, fun y => ?_⟩
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib, sum_pushCoeff_mul]
  rw [pushCoeff_restriction M hM, pushCoeff_restriction N hN]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => congrArg (T a * ·) ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    cases y i <;> simp [L]
  · refine Finset.sum_congr rfl fun c _ => congrArg (U c * ·) ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    cases y i <;> simp [L]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.AddLaws
section

/-!
# Relabeling laws for direct sums of site tensors
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

variable {I K : Type*} [Fintype I] [AddCommMonoid K]
variable {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]

private theorem pushCoeff_relabel {X Y Z : Type*} [Fintype X]
    (e : Y ≃ Z) (f : X → Y) (g : X → Z) (h : ∀ x, e (f x) = g x)
    (T : X → K) (y : Y) : pushCoeff f T y = pushCoeff g T (e y) := by
  classical
  unfold pushCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← h, e.injective.eq_iff]

private theorem pushCoeff_add_apply {X Y : Type*} [Fintype X]
    (f : X → Y) (T U : X → K) (y : Y) :
    pushCoeff f (fun x => T x + U x) y = pushCoeff f T y + pushCoeff f U y :=
  congrFun (pushCoeff_add f T U) y

/-- Interchanging the two summands interchanges their tags at every site. -/
theorem sumCoeff_comm (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, A i ⊕ B i) :
    sumCoeff T U x = sumCoeff U T (fun i => Equiv.sumComm _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumComm (A i) (B i)
  unfold sumCoeff
  rw [add_comm]
  exact congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) U x)
    (pushCoeff_relabel e _ _ (fun _ => rfl) T x)

/-- Reassociating three direct summands reassociates their tags site by site. -/
theorem sumCoeff_assoc (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (V : (∀ i, C i) → K)
    (x : ∀ i, (A i ⊕ B i) ⊕ C i) :
    sumCoeff (sumCoeff T U) V x =
      sumCoeff T (sumCoeff U V) (fun i => Equiv.sumAssoc _ _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumAssoc (A i) (B i) (C i)
  unfold sumCoeff
  simp_rw [pushCoeff_add_apply, pushCoeff_comp, add_assoc]
  exact congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) T x)
    (congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) U x)
      (pushCoeff_relabel e _ _ (fun _ => rfl) V x))

/-- Adding the tensor with empty local bases on the right preserves coefficients. -/
theorem sumCoeff_zero [∀ i, IsEmpty (B i)] (T : (∀ i, A i) → K) (x : ∀ i, A i ⊕ B i) :
    sumCoeff T (0 : (∀ i, B i) → K) x = T (fun i => Equiv.sumEmpty _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumEmpty (A i) (B i)
  unfold sumCoeff
  rw [pushCoeff_relabel e _ (Equiv.refl _) (fun _ => rfl) T, pushCoeff_equiv]
  simp only [pushCoeff, Pi.zero_apply, ite_self, Finset.sum_const_zero, add_zero]
  rfl

/-- Adding the tensor with empty local bases on the left preserves coefficients. -/
theorem zero_sumCoeff [∀ i, IsEmpty (A i)] (U : (∀ i, B i) → K) (x : ∀ i, A i ⊕ B i) :
    sumCoeff (0 : (∀ i, A i) → K) U x = U (fun i => Equiv.emptySum _ _ (x i)) := by
  rw [sumCoeff_comm, sumCoeff_zero]
  rfl

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.MulLaws
section

/-! # Multiplication laws for finite tensors up to mutual restriction -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

variable {I K : Type*} [Fintype I] [CommSemiring K]

/-- The tensor product is associative after relabeling the paired bases. -/
theorem mul_assoc_equivalent (X Y Z : Raw I K) :
    ((X.mul Y).mul Z).Equivalent (X.mul (Y.mul Z)) := by
  apply reindex_equivalent (fun _ => Equiv.prodAssoc _ _ _)
  intro x
  apply mul_assoc

/-- Swapping the local product factors commutes the tensor product. -/
theorem mul_comm_equivalent (X Y : Raw I K) :
    (X.mul Y).Equivalent (Y.mul X) := by
  apply reindex_equivalent (fun _ => Equiv.prodComm _ _)
  intro x
  apply mul_comm

/-- Dropping the singleton basis index identifies a unit product with its other factor. -/
theorem one_mul_equivalent (X : Raw I K) : ((one I K).mul X).Equivalent X := by
  apply reindex_equivalent (fun _ => Equiv.punitProd _)
  intro x
  apply one_mul

/-- Tensoring with the empty tensor gives an empty basis at each site. -/
theorem zero_mul_equivalent [Nonempty I] (X : Raw I K) :
    ((zero I K).mul X).Equivalent (zero I K) := by
  apply reindex_equivalent (fun _ => Equiv.pemptyProd _)
  intro x
  exact (x (Classical.arbitrary I)).1.elim

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.Distrib
section

/-! # Tensor product distributes over the direct sum

The relabeling at each site sends a paired index with a left (respectively,
right) tag to a left (respectively, right) tagged pair. All sites must choose
the same tag for a coefficient of the direct sum to contribute.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

variable {I K : Type*} [Fintype I] [Nonempty I] [CommSemiring K]
  {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]

/-- Left distributivity of the coefficient tensor product over the direct
sum, up to the canonical relabeling at each site. -/
theorem sumCoeff_product_distrib (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (V : (∀ i, C i) → K) (x : ∀ i, A i × (B i ⊕ C i)) :
    T (fun i => (x i).1) * sumCoeff U V (fun i => (x i).2) =
      sumCoeff (fun y : ∀ i, A i × B i => T (fun i => (y i).1) * U (fun i => (y i).2))
        (fun y : ∀ i, A i × C i => T (fun i => (y i).1) * V (fun i => (y i).2))
        (fun i => Equiv.prodSumDistrib _ _ _ (x i)) := by
  classical
  let u (i : I) := (x i).1
  let v (i : I) := (x i).2
  change T u * sumCoeff U V v = sumCoeff _ _ (fun i => Equiv.prodSumDistrib _ _ _ (u i, v i))
  generalize v = w
  by_cases hl : ∃ y : ∀ i, B i, (fun i => Sum.inl (y i)) = w
  · obtain ⟨y, rfl⟩ := hl
    simp only [Equiv.prodSumDistrib_apply_left, sumCoeff_inl]
  by_cases hr : ∃ y : ∀ i, C i, (fun i => Sum.inr (y i)) = w
  · obtain ⟨y, rfl⟩ := hr
    simp only [Equiv.prodSumDistrib_apply_right, sumCoeff_inr]
  have hleft (z : ∀ i, A i × B i) :
      (fun i => Sum.inl (z i)) ≠ (fun i => Equiv.prodSumDistrib _ _ _ (u i, w i)) := by
    intro eq
    refine hl ⟨fun i => (z i).2, funext fun i => ?_⟩
    have h := congrArg (fun t => ((Equiv.prodSumDistrib (A i) (B i) (C i)).symm t).2)
      (congrFun eq i)
    simpa using h
  have hright (z : ∀ i, A i × C i) :
      (fun i => Sum.inr (z i)) ≠ (fun i => Equiv.prodSumDistrib _ _ _ (u i, w i)) := by
    intro eq
    refine hr ⟨fun i => (z i).2, funext fun i => ?_⟩
    have h := congrArg (fun t => ((Equiv.prodSumDistrib (A i) (B i) (C i)).symm t).2)
      (congrFun eq i)
    simpa using h
  rw [sumCoeff_mixed _ _ _ (not_exists.mp hl) (not_exists.mp hr),
    sumCoeff_mixed _ _ _ hleft hright, mul_zero]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.TensorSemiring
section

/-! # The semiring of tensors up to mutual restriction

The sites, coefficient semiring, and finite coordinate spaces at each site
are arbitrary. Addition is the block direct sum and multiplication is the
tensor product grouped at each site. Both operations preserve local restriction.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

variable {I : Type u} {K : Type w} [Fintype I] [CommSemiring K]

noncomputable section

instance : Add (TensorClass.{v} I K) where
  add := Quotient.map₂ Raw.add fun _ _ h _ _ g =>
    ⟨restrict_sum h.1 g.1, restrict_sum h.2 g.2⟩

instance : Mul (TensorClass.{v} I K) where
  mul := Quotient.map₂ Raw.mul fun _ _ h _ _ g =>
    ⟨Raw.mul_restricts h.1 g.1, Raw.mul_restricts h.2 g.2⟩

instance : Zero (TensorClass.{v} I K) := ⟨ofRaw (Raw.zero I K)⟩
instance : One (TensorClass.{v} I K) := ⟨ofRaw (Raw.one I K)⟩

@[simp] theorem ofRaw_add (X Y : Raw.{v} I K) : ofRaw (X.add Y) = ofRaw X + ofRaw Y := rfl

@[simp] theorem ofRaw_mul (X Y : Raw.{v} I K) : ofRaw (X.mul Y) = ofRaw X * ofRaw Y := rfl

@[simp] theorem ofRaw_zero : ofRaw (Raw.zero.{v} I K) = 0 := rfl

@[simp] theorem ofRaw_one : ofRaw (Raw.one.{v} I K) = 1 := rfl

private theorem class_add_comm (X Y : TensorClass.{v} I K) : X + Y = Y + X :=
  Quotient.inductionOn₂ X Y fun x y => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.sumComm _ _) (sumCoeff_comm x.coeff y.coeff)

private theorem class_zero_add (X : TensorClass.{v} I K) : 0 + X = X := by
  let (i : I) : IsEmpty ((Raw.zero.{v} I K).Leg i) := inferInstanceAs (IsEmpty PEmpty)
  exact
  Quotient.inductionOn X fun x => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.emptySum _ _) (zero_sumCoeff x.coeff)

private theorem class_mul_comm (X Y : TensorClass.{v} I K) : X * Y = Y * X :=
  Quotient.inductionOn₂ X Y fun x y => Quotient.sound (x.mul_comm_equivalent y)

private theorem class_one_mul (X : TensorClass.{v} I K) : 1 * X = X :=
  Quotient.inductionOn X fun x => Quotient.sound (x.one_mul_equivalent)

variable [Nonempty I]

private theorem class_zero_mul (X : TensorClass.{v} I K) : 0 * X = 0 :=
  Quotient.inductionOn X fun x => Quotient.sound (x.zero_mul_equivalent)

private theorem class_left_distrib (X Y Z : TensorClass.{v} I K) :
    X * (Y + Z) = X * Y + X * Z :=
  Quotient.inductionOn₃ X Y Z fun x y z => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.prodSumDistrib _ _ _)
      (sumCoeff_product_distrib x.coeff y.coeff z.coeff)

/-- The restriction classes form the tensor semiring of the manuscript. -/
instance : CommSemiring (TensorClass.{v} I K) where
  add_assoc X Y Z := Quotient.inductionOn₃ X Y Z fun x y z => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.sumAssoc _ _ _) (sumCoeff_assoc x.coeff y.coeff z.coeff)
  add_comm := class_add_comm
  zero_add := class_zero_add
  add_zero X := (class_add_comm X 0).trans (class_zero_add X)
  nsmul := nsmulRec
  mul_assoc X Y Z := Quotient.inductionOn₃ X Y Z fun x y z =>
    Quotient.sound (x.mul_assoc_equivalent y z)
  mul_comm := class_mul_comm
  one_mul := class_one_mul
  mul_one X := (class_mul_comm X 1).trans (class_one_mul X)
  zero_mul := class_zero_mul
  mul_zero X := (class_mul_comm X 0).trans (class_zero_mul X)
  left_distrib := class_left_distrib
  right_distrib X Y Z := by rw [class_mul_comm, class_left_distrib, class_mul_comm Z X, class_mul_comm Z Y]

omit [Nonempty I] in
/-- Both arguments of block direct sum are monotone under restriction. -/
theorem add_mono {X Y U V : TensorClass.{v} I K} (h : X ≤ Y) (g : U ≤ V) :
    X + U ≤ Y + V := by
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  induction U using Quotient.inductionOn
  induction V using Quotient.inductionOn
  exact restrict_sum h g

omit [Nonempty I] in
/-- Both arguments of tensor product are monotone under restriction. -/
theorem mul_mono {X Y U V : TensorClass.{v} I K} (h : X ≤ Y) (g : U ≤ V) :
    X * U ≤ Y * V := by
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  induction U using Quotient.inductionOn
  induction V using Quotient.inductionOn
  exact Raw.mul_restricts h g

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.MaskDiagonal
section

/-! # Common-label diagonals in a fixed space of sites

On the support a local basis index is a label. Off the support the local
space has one basis index. The type of functions from the membership
proposition implements both cases in one coordinate format.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

open scoped Classical

variable {I : Type*} [Fintype I]

abbrev MaskLeg (S : Finset I) (α : Type) (i : I) := i ∈ S → α

/-- A partial diagonal in the ambient site set `I`. -/
noncomputable def Raw.maskDiagonal (K : Type*) [Field K] (S : Finset I) (α : Type) [Fintype α] :
    Raw.{0} I K :=
  ⟨MaskLeg S α, fun _ ↦ Fintype.ofFinite _, Crossing.basisTensor (fun (a : α) i (_ : i ∈ S) ↦ a)⟩

/-- Pairing independent terms in two basis presentations is multiplication
in the tensor semiring, up to the indicated local changes of coordinates. -/
theorem basisTensor_paired_eq_mul {K : Type*} [Field K]
    {A B C : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]
    {J L : Type} [Fintype J] [Fintype L] (a : J → ∀ i, A i) (b : L → ∀ i, B i)
    (c : J × L → ∀ i, C i) (e : ∀ i, C i ≃ A i × B i)
    (h : ∀ s t i, e i (c (s,t) i) = (a s i, b t i)) :
    ofRaw (I := I) (K := K) ⟨C, inferInstance, Crossing.basisTensor c⟩ =
      ofRaw (I := I) (K := K) ⟨A, inferInstance, Crossing.basisTensor a⟩ *
        ofRaw (I := I) (K := K) ⟨B, inferInstance, Crossing.basisTensor b⟩ := by
  classical
  rw [← ofRaw_mul]
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent e
  intro x
  change Crossing.basisTensor c x = Crossing.basisTensor a (fun i ↦ (e i (x i)).1) *
    Crossing.basisTensor b (fun i ↦ (e i (x i)).2)
  simp only [Crossing.basisTensor, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  have heq : x = c (s, t) ↔ ((fun i ↦ (e i (x i)).1) = a s ∧
      (fun i ↦ (e i (x i)).2) = b t) := by
    constructor
    · rintro rfl
      exact ⟨funext fun i ↦ congrArg Prod.fst (h s t i), funext fun i ↦ congrArg Prod.snd (h s t i)⟩
    · rintro ⟨ha,hb⟩
      funext i
      exact (e i).injective ((Prod.ext (congrFun ha i) (congrFun hb i)).trans (h s t i).symm)
  by_cases ha : (fun i ↦ (e i (x i)).1) = a s <;> simp [heq, ha]

/-- A basis presentation with two independent labels factors into the partial
diagonals on the supports where the labels are read. -/
theorem basisTensor_eq_maskDiagonal_mul {K : Type*} [Field K]
    {C : I → Type} [∀ i, Fintype (C i)] {J L : Type} [Fintype J] [Fintype L]
    (S T : Finset I) (c : J × L → ∀ i, C i)
    (e : ∀ i, C i ≃ MaskLeg S J i × MaskLeg T L i)
    (h : ∀ s t i, e i (c (s,t) i) = (fun _ ↦ s, fun _ ↦ t)) :
    ofRaw (I := I) (K := K) ⟨C, inferInstance, Crossing.basisTensor c⟩ =
      ofRaw (Raw.maskDiagonal K S J) * ofRaw (Raw.maskDiagonal K T L) := by
  let (i : I) : Fintype (MaskLeg S J i) := (Raw.maskDiagonal K S J).finiteLeg i
  let (i : I) : Fintype (MaskLeg T L i) := (Raw.maskDiagonal K T L).finiteLeg i
  exact basisTensor_paired_eq_mul (K := K) (A := MaskLeg S J) (B := MaskLeg T L)
    (fun a _ _ ↦ a) (fun b _ _ ↦ b) c e h

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.PolynomialOverhead
section

/-! # Removing polynomial overheads from tensor-power inequalities -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter
open scoped Topology NNReal

/-- A fixed polynomial overhead in a comparison of all positive powers
disappears at the level of exponential growth rates. -/
theorem le_of_pow_le_polynomial_mul_pow {x y : ℝ} (hy : 0 ≤ y) (L : ℕ)
    (h : ∀ m : ℕ, 1 ≤ m → x ^ m ≤ ((m : ℝ) + 1) ^ L * y ^ m) : x ≤ y := by
  by_contra! hxy
  have hx := hy.trans_lt hxy
  have hr := tendsto_pow_const_mul_const_pow_of_lt_one L (div_nonneg hy hx.le)
    ((div_lt_one hx).2 hxy)
  have hlim : Tendsto (fun m : ℕ => (2 : ℝ) ^ L * ((m : ℝ) ^ L * (y / x) ^ m))
      atTop (𝓝 0) := by simpa using hr.const_mul ((2 : ℝ) ^ L)
  have hone : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hp : ((m : ℝ) + 1) ^ L ≤ (2 * (m : ℝ)) ^ L :=
      pow_le_pow_left₀ (by positivity) (by linarith) L
    rw [div_pow, ← mul_div_assoc, ← mul_div_assoc, le_div_iff₀ (pow_pos hx _), one_mul,
      ← mul_assoc, ← mul_pow]
    exact (h m hm).trans (mul_le_mul_of_nonneg_right hp (pow_nonneg hy _)))
  norm_num at hone

/-- The growth-rate comparison in nonnegative reals. -/
theorem nnreal_le_of_pow_le_polynomial_mul_pow {x y : ℝ≥0} (L : ℕ)
    (h : ∀ m : ℕ, 1 ≤ m → x ^ m ≤ ((m : ℝ≥0) + 1) ^ L * y ^ m) : x ≤ y := by
  apply NNReal.coe_le_coe.mp
  apply le_of_pow_le_polynomial_mul_pow y.2 L
  intro m hm
  exact_mod_cast h m hm

/-- A uniformly bounded error between all natural multiples forces equality. -/
theorem eq_of_nat_mul_close {a b C : ℝ}
    (h : ∀ m : ℕ, |(m : ℝ) * (a - b)| ≤ C) : a = b := by
  by_contra hab
  obtain ⟨m, hm⟩ := exists_lt_nsmul (abs_pos.mpr (sub_ne_zero.mpr hab)) C
  rw [nsmul_eq_mul] at hm
  have hbound := h m
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)] at hbound
  exact hm.not_ge hbound

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.DimensionLaw
section

/-! # Logarithmic dependence on wire dimension

Restricting a wire to fewer labels is monotone, and tensoring wires multiplies
the number of labels. Comparing powers with consecutive powers of two then
determines every positive-dimensional value from the binary wire.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- Every nondecreasing wire price that adds on products of positive dimensions
equals its binary price times the logarithm of the dimension. -/
theorem dimension_price_eq_logb {p : ℕ → ℝ} (hmono : ∀ i j, 0 < i → i ≤ j → p i ≤ p j)
    (hone : p 1 = 0) (hmul : ∀ i j, 0 < i → 0 < j → p (i * j) = p i + p j)
    {q : ℕ} (hq : 0 < q) : p q = p 2 * Real.logb 2 q := by
  have hp (i : ℕ) (hi : 0 < i) (n : ℕ) : p (i ^ n) = n * p i := by
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, hmul _ _ (pow_pos hi _) hi, ih, Nat.cast_succ, add_mul, one_mul]
  have hp2 : 0 ≤ p 2 := by simpa [hone] using hmono 1 2 (by decide) (by decide)
  have happrox (k : ℕ) : k * p q ≤ k * (p 2 * Real.logb 2 q) + p 2 ∧
      k * (p 2 * Real.logb 2 q) ≤ k * p q + p 2 := by
    let b := Nat.log 2 (q ^ k)
    have hlo : 2 ^ b ≤ q ^ k := Nat.pow_log_le_self _ (pow_pos hq _).ne'
    have hhi : q ^ k ≤ 2 ^ (b + 1) := (Nat.lt_pow_succ_log_self (by decide) _).le
    have hplo := hmono _ _ (pow_pos (by decide : 0 < 2) _) hlo
    have hphi := hmono _ _ (pow_pos hq _) hhi
    rw [hp _ (by decide) _, hp _ hq _] at hplo
    rw [hp _ hq _, hp _ (by decide) _, Nat.cast_add_one] at hphi
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (2 : ℝ) ^ b) (by exact_mod_cast hlo : (2 : ℝ)^b ≤ (q : ℝ)^k)
    have hu := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (q : ℝ)^k) (by exact_mod_cast hhi : (q : ℝ)^k ≤ (2 : ℝ)^(b+1))
    simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      Nat.cast_add_one, mul_one] at hl hu
    constructor <;> nlinarith only [hphi, hplo, mul_le_mul_of_nonneg_left hl hp2,
      mul_le_mul_of_nonneg_left hu hp2]
  apply eq_of_nat_mul_close (C := p 2)
  intro k
  rw [abs_le, mul_sub]
  obtain ⟨hu, hl⟩ := happrox k
  constructor <;> linarith

/-- Its multiplicative form applies to the normalized spectral value of a wire,
or of square matrix multiplication as a function of its order. -/
theorem dimension_value_eq_rpow {v : ℕ → ℝ} (hmono : Monotone v) (hone : v 1 = 1)
    (hmul : ∀ m n, v (m * n) = v m * v n) {q : ℕ} (hq : 0 < q) :
    v q = (q : ℝ) ^ (Real.logb 2 (v 2)) := by
  have hpos (n : ℕ) (hn : 0 < n) : 0 < v n := by
    have h := hmono (show 1 ≤ n from hn)
    linarith
  have h := dimension_price_eq_logb (p := fun n => Real.logb 2 (v n))
    (fun i j hi hij => Real.logb_le_logb_of_le (by norm_num) (hpos i hi) (hmono hij))
    (by simp [hone]) (fun i j hi hj => by rw [hmul, Real.logb_mul (hpos _ hi).ne' (hpos _ hj).ne']) hq
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hr := Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (hpos q hq)
  have hR := Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    (Real.rpow_pos_of_pos hq' (Real.logb 2 (v 2)))
  rw [Real.logb_rpow_eq_mul_logb_of_pos hq', ← h] at hR
  exact hr.symm.trans hR

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.NatSpectralExponent
section

/-! # Natural diagonal evaluations

Monotonicity on positive integer diagonals and multiplicativity force their
evaluation to be a single power, determined by the binary diagonal.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Real
open scoped NNReal

variable {A : Type*} [Semiring A] (v : A →* ℝ≥0)
  (hmono : ∀ {a b : ℕ}, 0 < a → a ≤ b → v (a : A) ≤ v (b : A))

include hmono in
theorem spectral_natCast_one_le (n : ℕ) (hn : 0 < n) : 1 ≤ v (n : A) := by
  simpa using hmono (a := 1) (b := n) (by decide) hn

include hmono in
/-- Positive integer diagonals have a nonnegative logarithmic price. -/
theorem spectral_natCast_logb_nonneg (n : ℕ) (hn : 0 < n) : 0 ≤ logb 2 (v (n : A)) :=
  logb_nonneg (by norm_num) (by exact_mod_cast spectral_natCast_one_le v hmono n hn)

include hmono in
private theorem spectral_natCast_logb_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    logb 2 (v (a : A)) ≤ logb 2 (v (b : A)) :=
  logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast zero_lt_one.trans_le (spectral_natCast_one_le v hmono a ha))
    (by exact_mod_cast hmono ha hab)

include hmono in
/-- The logarithmic price of the `n`-diagonal is the binary price times
`log₂ n`. -/
theorem spectral_natCast_logb (n : ℕ) (hn : 0 < n) :
    logb 2 (v (n : A)) = logb 2 (v (2 : A)) * logb 2 n := by
  refine dimension_price_eq_logb (p := fun i => logb 2 (v (i : A)))
    (fun _ _ => spectral_natCast_logb_mono v hmono) (by simp) ?_ hn
  intro i j hi hj
  have hpos {k : ℕ} (hk : 0 < k) : (v (k : A) : ℝ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (spectral_natCast_one_le v hmono k hk)).ne'
  rw [Nat.cast_mul, map_mul, NNReal.coe_mul, logb_mul (hpos hi) (hpos hj)]

include hmono in
/-- The diagonal exponent is `log₂(v 2)` over every semiring carrying a
monotone multiplicative evaluation on positive integer diagonals. -/
theorem spectral_natCast_eq_rpow (n : ℕ) (hn : 0 < n) :
    v (n : A) = (n : ℝ≥0) ^ logb 2 (v (2 : A)) := by
  apply NNReal.eq
  rw [NNReal.coe_rpow, NNReal.coe_natCast]
  have hv : 0 < (v (n : A) : ℝ) := by
    exact_mod_cast zero_lt_one.trans_le (spectral_natCast_one_le v hmono n hn)
  apply (Real.strictMonoOn_logb (by norm_num : (1 : ℝ) < 2)).injOn
      (show 0 < (v (n : A) : ℝ) from hv) (Real.rpow_pos_of_pos (by exact_mod_cast hn : 0 < (n : ℝ)) _)
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]
  exact spectral_natCast_logb v hmono n hn

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.Doubling
section

/-!
# Selecting a single spectral price

This is the compactness and separation argument in the proof of the doubling
theorem. Nonzero tensors modulo mutual restriction form a commutative monoid
under tensor product. We use additive notation for that monoid, so `n • t`
means a tensor power and a log spectral evaluation is an additive map.

The submonoid `G` is generated by the private tensors and the binary diagonal
on their union. The finite comparison hypothesis applies only to targets of
the form `Δ + x` with `x ∈ G`. Thus the separating construction keeps a
positive power of the diagonal in every target.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Finset Set

/-- Clear denominators in a strict comparison of two nonnegative ratios. -/
private theorem exists_integral_cut {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hd : 0 < d) (hab : a / b < c / d) :
    ∃ m n : ℕ, (n : ℝ) * a < m * b ∧ (m : ℝ) * d < n * c := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hab)
  let n := k + 1
  have hn : (0 : ℝ) < n := by dsimp [n]; positivity
  have hgap : 1 < (c / d - a / b) * n := by
    apply (div_lt_iff₀ hn).mp
    simpa [n] using hk
  let m := ⌊a / b * n⌋₊ + 1
  have hm₁ : a / b * n < m := by simpa [m] using Nat.lt_floor_add_one (a / b * n)
  have hm₂ : (m : ℝ) < c / d * n := by
    have hfloor := Nat.floor_le (mul_nonneg (div_nonneg ha hb.le) hn.le : 0 ≤ a / b * n)
    dsimp [m]
    push_cast
    linarith only [hfloor, hgap]
  refine ⟨m, n, ?_, ?_⟩
  · calc
      (n : ℝ) * a = (a / b * n) * b := by field_simp
      _ < m * b := mul_lt_mul_of_pos_right hm₁ hb
  · calc
      (m : ℝ) * d < (c / d * n) * d := mul_lt_mul_of_pos_right hm₂ hd
      _ = n * c := by field_simp

variable {T : Type*} [AddCommMonoid T]

/-- At a single normalized point, failure of every rescaling yields two actual
tensor products in opposite strict order. The more expensive product for
`h` belongs to the submonoid generated by the equality requirements. -/
private theorem local_price_separator
    (F h : T →+ ℝ) (G : AddSubmonoid T) {u : T} (hu : u ∈ G)
    (hU : 0 < h u) (hF : ∀ t, 0 ≤ F t) (hh : ∀ t, 0 ≤ h t)
    (hfull : ∃ t, 0 < F t)
    (hfail : ¬ ∃ c : ℝ, 0 < c ∧ (∀ t, c * F t ≤ h t) ∧
      ∀ t ∈ G, c * F t = h t) :
    ∃ x ∈ G, ∃ y : T, F x < F y ∧ h y < h x := by
  by_cases hzero : F u = 0
  · obtain ⟨y, hpos⟩ := hfull
    obtain ⟨n, hn⟩ := exists_nat_gt (h y / h u)
    refine ⟨n • u, G.nsmul_mem hu n, y, ?_, ?_⟩
    · simpa [hzero] using hpos
    · simpa [nsmul_eq_mul] using (div_lt_iff₀ hU).mp hn
  have hFu : 0 < F u := lt_of_le_of_ne (hF u) (Ne.symm hzero)
  by_cases hover : ∃ t, h t / h u < F t / F u
  · obtain ⟨t, ht⟩ := hover
    obtain ⟨m, n, h₁, h₂⟩ := exists_integral_cut (hh t) hU hFu ht
    refine ⟨m • u, G.nsmul_mem hu m, n • t, ?_, ?_⟩
    · simpa [nsmul_eq_mul] using h₂
    · simpa [nsmul_eq_mul] using h₁
  by_cases hunder : ∃ t ∈ G, F t / F u < h t / h u
  · obtain ⟨t, htG, ht⟩ := hunder
    obtain ⟨m, n, h₁, h₂⟩ := exists_integral_cut (hF t) hFu hU ht
    refine ⟨n • t, G.nsmul_mem htG n, m • u, ?_, ?_⟩
    · simpa [nsmul_eq_mul] using h₁
    · simpa [nsmul_eq_mul] using h₂
  push Not at hover hunder
  exfalso
  apply hfail
  refine ⟨h u / F u, div_pos hU hFu, ?_, ?_⟩
  · intro t
    have hle := (div_le_div_iff₀ hFu hU).mp (hover t)
    rw [div_mul_eq_mul_div, div_le_iff₀ hFu]
    linarith
  · intro t ht
    have heq := (div_eq_div_iff hFu.ne' hU.ne').mp
      (le_antisymm (hover t) (hunder t ht))
    rw [div_mul_eq_mul_div, div_eq_iff hFu.ne']
    linarith

/-- Given finite strict spectral comparison for stretched targets, a single
rescaled point is bounded above by `h` everywhere and attains `h` on `G`.

Take `G` to be the submonoid generated by the private tensors and `Δ`.
In the doubling theorem `h = λ a + b + c` and `u` is the binary diagonal
on the first private set. The estimate turning an ordinary sum into the
finite comparison hypothesis is a separate input to this theorem. -/
theorem select_spectral_price_of_finite_comparison
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [Nonempty S]
    (F : S → T →+ ℝ) (h : T →+ ℝ) (G : AddSubmonoid T) (Δ u : T)
    (hcont : ∀ t, Continuous (fun s => F s t)) (hF : ∀ s t, 0 ≤ F s t)
    (hh : ∀ t, 0 ≤ h t) (hu : u ∈ G) (hU : 0 < h u)
    (hfull : ∀ s, ∃ t, 0 < F s t)
    (hcompare : ∀ (x : T), x ∈ G → ∀ (j : ℕ) (y : Fin j → T),
      (∀ s, ∃ i, F s (Δ + x) < F s (y i)) → ∃ i, h (Δ + x) ≤ h (y i)) :
    ∃ (s : S) (c : ℝ), 0 < c ∧ (∀ t, c * F s t ≤ h t) ∧
      ∀ t ∈ G, c * F s t = h t := by
  classical
  by_contra hnone
  have hlocal (s : S) := local_price_separator (F s) h G hu hU (hF s) hh (hfull s)
    (fun he => hnone ⟨s, he⟩)
  choose x hx y hxy hyx using hlocal
  let U (s : S) := {q : S | F q (x s) < F q (y s)}
  have hcover : (univ : Set S) ⊆ ⋃ s, U s := fun q _ => mem_iUnion.mpr ⟨q, hxy q⟩
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover U
    (fun s => isOpen_lt (hcont _) (hcont _)) hcover
  let E := Fintype.equivFin ↥J
  let X := ∑ s ∈ J, x s
  let Y (s : S) := Δ + (∑ q ∈ J.erase s, x q) + y s
  have hX : X ∈ G := G.sum_mem fun s _ => hx s
  have hrewrite (s : ↥J) : X = (∑ q ∈ J.erase s.val, x q) + x s :=
    (Finset.sum_erase_add J x s.property).symm
  have hdominates (q : S) : ∃ i, F q (Δ + X) < F q (Y ((E.symm i).val)) := by
    obtain ⟨s, hs⟩ := mem_iUnion.mp (hJ (mem_univ q))
    obtain ⟨hsJ, hqs⟩ := mem_iUnion.mp hs
    let i : ↥J := ⟨s, hsJ⟩
    refine ⟨E i, ?_⟩
    rw [Equiv.symm_apply_apply, hrewrite i]
    simpa [Y, i, add_assoc] using
      add_lt_add_left (show F q (x s) < F q (y s) from hqs)
        (F q Δ + F q (∑ a ∈ J.erase s, x a))
  obtain ⟨i, hi⟩ := hcompare X hX _ (fun i => Y (E.symm i).val) hdominates
  rw [hrewrite (E.symm i)] at hi
  exact (not_le.mpr (hyx (E.symm i).val)) (by simpa only [Y, map_add, ← add_assoc, add_le_add_iff_left] using hi)

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.Spectrum
section

/-!
# Compactness of the normalized spectrum

The direct sum and tensor product of restriction classes give a semiring. It suffices here that
each class is a restriction of a natural number, represented by a diagonal tensor. We view a
point as a function into the nonnegative reals with the topology of pointwise convergence.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set NNReal

variable {S : Type*} [Semiring S]

/-- Normalized restriction-monotone semiring homomorphisms, as their pointwise evaluations. -/
def normalizedSpectrum (restricts : S → S → Prop) : Set (S → ℝ≥0) :=
  {f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, f (x * y) = f x * f y) ∧ ∀ x y, restricts x y → f x ≤ f y}

/-- A spectral point preserves the semiring operations. -/
def normalizedSpectrum.toRingHom {restricts : S → S → Prop}
    (f : normalizedSpectrum restricts) : S →+* ℝ≥0 where
  toFun := f.1
  map_zero' := f.2.1
  map_one' := f.2.2.1
  map_add' := f.2.2.2.1
  map_mul' := f.2.2.2.2.1

/-- Pointwise limits preserve all the spectral axioms, including every restriction comparison. -/
theorem isClosed_normalizedSpectrum (restricts : S → S → Prop) :
    IsClosed (normalizedSpectrum restricts) := by
  have hmono : IsClosed {f : S → ℝ≥0 | ∀ x y, restricts x y → f x ≤ f y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_iInter fun _ ↦
      isClosed_le (continuous_apply x) (continuous_apply y)
  exact (isClosed_setOfPred_map_zero S ℝ≥0).inter <|
    (isClosed_setOfPred_map_one S ℝ≥0).inter <|
    (isClosed_setOfPred_map_add S ℝ≥0).inter ((isClosed_setOfPred_map_mul S ℝ≥0).inter hmono)

/-- Finite tensor rank bounds every coordinate of the normalized spectrum. -/
theorem isCompact_normalizedSpectrum (restricts : S → S → Prop)
    (hfinite : ∀ x : S, ∃ r : ℕ, restricts x r) : IsCompact (normalizedSpectrum restricts) := by
  choose r hr using hfinite
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun x ↦ isCompact_Icc (a := (0 : ℝ≥0)) (b := (r x : ℝ≥0))))
    (isClosed_normalizedSpectrum restricts)
  intro f hf x _
  have hle := hf.2.2.2.2 x _ (hr x)
  have hcast : f (r x : S) = (r x : ℝ≥0) := map_natCast (normalizedSpectrum.toRingHom ⟨f, hf⟩) _
  exact ⟨bot_le, hle.trans_eq hcast⟩

/-- On any tensor admitting a restriction to the unit, normalized logarithmic price is
continuous on the entire spectrum. -/
theorem continuous_log_price {restricts : S → S → Prop} {x : S} (hx : restricts 1 x) :
    Continuous (fun f : normalizedSpectrum restricts ↦ Real.logb 2 (f.val x : ℝ)) := by
  apply (continuous_subtype_val.comp ((continuous_apply x).comp continuous_subtype_val)).logb
  intro f
  have hone := f.2.2.2.2.2 1 x hx
  rw [f.2.2.1] at hone
  change (f.val x : ℝ) ≠ 0
  exact_mod_cast (zero_lt_one.trans_le hone).ne'

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.StrictComparison
section

/-!
# Selecting a summand by amplified strict comparison

In this file addition in `T` denotes tensor product of nonzero tensors, so a
logarithmic price is an additive homomorphism. Ordinary sums and restrictions
remain separate relations. We use the consequence of strict comparison obtained
by expanding a restriction of `K` direct copies of a tensor power and dropping
the zero images. The constant `K` may vary with the initial power `k`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

variable {T : Type*} [AddCommMonoid T]

/-- The expanded conclusion of strict spectral comparison for a finite direct sum.
Every nonzero summand in the target is the image of a word of length `n` in the
sources. Its price will be bounded using restriction monotonicity. -/
def ExpandedStrictComparison (spectrum : Set (T →+ ℝ))
    (restricts : T → T → Prop) (ordinarySum : T → (L : ℕ) → (Fin L → T) → Prop) : Prop :=
  ∀ {J : ℕ} (X : T) (Y : Fin J → T), 0 < J →
    (∀ f ∈ spectrum, ∃ i, f X < f (Y i)) →
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      ∃ L : ℕ, 0 < L ∧ L ≤ K * J ^ n ∧ ∃ Z : Fin L → T,
        ordinarySum (n • X) L Z ∧
        ∀ l, ∃ w : Fin n → Fin J, restricts (Z l) (∑ t, Y (w t))

private theorem remove_constant {a b c : ℝ}
    (h : ∀ n : ℕ, 0 < n → (n : ℝ) * a ≤ c + n * b) : a ≤ b := by
  by_contra! hab
  obtain ⟨m, hm⟩ := exists_lt_nsmul (sub_pos.mpr hab) c
  have hh := h (m + 1) (Nat.succ_pos _)
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hm hh
  linarith

/-- The finite alternative used in the proof of doubling. If each normalized
point prefers some `Y i` to `X`, a monotone price satisfying the ordinary-sum
estimate on all positive powers of `X` weakly prefers some `Y i` as well.
The two amplifications absorb first the constant number of direct copies and
then the cost of choosing one of the `J` sources. -/
theorem finite_comparison_of_ordinary_sum
    {spectrum : Set (T →+ ℝ)} {restricts : T → T → Prop}
    {ordinarySum : T → (L : ℕ) → (Fin L → T) → Prop}
    (compare : ExpandedStrictComparison spectrum restricts ordinarySum)
    (h : T →+ ℝ) (mono : ∀ {x y}, restricts x y → h x ≤ h y)
    {C : ℝ} (hC : 0 ≤ C) {X : T}
    (stretch : ∀ (m L : ℕ) (Z : Fin L → T), 0 < m →
      ordinarySum (m • X) L Z → ∃ l, h (m • X) ≤ h (Z l) + C * Real.logb 2 L)
    {J : ℕ} (hJ : 0 < J) (Y : Fin J → T)
    (cover : ∀ f ∈ spectrum, ∃ i, f X < f (Y i)) : ∃ i, h X ≤ h (Y i) := by
  classical
  have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  obtain ⟨i, _, hmax⟩ := Finset.univ.exists_max_image (fun j => h (Y j)) Finset.univ_nonempty
  refine ⟨i, remove_constant (c := C * Real.logb 2 J) fun k hk => ?_⟩
  have hlarge (f : T →+ ℝ) (hf : f ∈ spectrum) : ∃ j, f (k • X) < f (k • Y j) := by
    obtain ⟨j, hj⟩ := cover f hf
    refine ⟨j, ?_⟩
    simpa only [map_nsmul, nsmul_eq_mul] using
      mul_lt_mul_of_pos_left hj (show (0 : ℝ) < k by exact_mod_cast hk)
  obtain ⟨K, hK, decompose⟩ := compare (k • X) (fun j => k • Y j) hJ hlarge
  apply remove_constant (c := C * Real.logb 2 K)
  intro n hn
  obtain ⟨L, hL, hcount, Z, hZ, hword⟩ := decompose n hn
  have hsum : ordinarySum ((n * k) • X) L Z := by rwa [Nat.mul_comm, mul_nsmul]
  obtain ⟨l, hprice⟩ := stretch (n * k) L Z (Nat.mul_pos hn hk) hsum
  obtain ⟨w, hw⟩ := hword l
  have hfactor : h (Z l) ≤ n * (k * h (Y i)) := calc
    h (Z l) ≤ h (∑ t, k • Y (w t)) := mono hw
    _ = ∑ t, k * h (Y (w t)) := by simp
    _ ≤ ∑ _t : Fin n, k * h (Y i) := Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (hmax (w t) (Finset.mem_univ _)) (Nat.cast_nonneg _)
    _ = n * (k * h (Y i)) := by simp
  have hlog : Real.logb 2 L ≤ Real.logb 2 K + n * Real.logb 2 J := calc
    Real.logb 2 L ≤ Real.logb 2 ((K * J ^ n : ℕ) : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hL) (by exact_mod_cast hcount)
    _ = _ := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.logb_mul (by positivity) (by positivity), Real.logb_pow]
  simp only [map_nsmul, nsmul_eq_mul, Nat.cast_mul] at hprice
  linarith only [hprice, hfactor, mul_le_mul_of_nonneg_left hlog hC]

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.PriceSelection
section

/-!
# Doubling via the normalized spectrum

The rank bound makes the space of normalized spectral points compact. On the
multiplicative monoid of nonzero tensors, taking logarithms gives additive
real-valued maps. The subsequent selection argument uses the restriction
expansion from strict comparison and the permutation-stretch estimate.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section
open scoped NNReal

variable {A : Type*} [CommSemiring A] {res : A → A → Prop} {P : Submonoid A}

/-- The log price is nonnegative because every nonzero tensor restricts to the unit. -/
theorem one_le_spectral_value (f : normalizedSpectrum res) {t : A} (ht : res 1 t) :
    1 ≤ f.val t := by
  simpa only [f.property.2.1] using f.property.2.2.2.2 1 t ht

/-- The nonzero tensor classes use tensor product as their additive operation.
The logarithm is base two, as in the manuscript. -/
def spectralLogHom (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res) :
    Additive P →+ ℝ where
  toFun x := Real.logb 2 (f.val x.toMul.val : ℝ)
  map_zero' := by simp [f.property.2.1]
  map_add' x y := by
    have hpos (t : P) : (f.val t.val : ℝ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le (one_le_spectral_value f (hunit t))).ne'
    simp only [toMul_add, Submonoid.coe_mul, f.property.2.2.2.1, NNReal.coe_mul]
    exact Real.logb_mul (hpos x.toMul) (hpos y.toMul)

theorem spectralLogHom_nonneg (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res)
    (x : Additive P) : 0 ≤ spectralLogHom hunit f x := by
  apply Real.logb_nonneg (by norm_num)
  exact_mod_cast one_le_spectral_value f (hunit x.toMul)

theorem continuous_spectralLogHom (hunit : ∀ t : P, res 1 t) (x : Additive P) :
    Continuous (fun f : normalizedSpectrum res => spectralLogHom hunit f x) :=
  continuous_log_price (hunit x.toMul)

/-- Every normalized point assigns log price one to the full binary diagonal. -/
theorem spectralLogHom_two (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res)
    (h₂ : (2 : A) ∈ P) :
    spectralLogHom hunit f (Additive.ofMul (⟨2, h₂⟩ : P)) = 1 := by
  change Real.logb 2 (f.val 2 : ℝ) = 1
  have htwo : f.val 2 = (2 : ℝ≥0) := map_ofNat (normalizedSpectrum.toRingHom f) 2
  rw [htwo]
  exact Real.logb_self_eq_one (by norm_num)

/-- A spectral price is a common positive multiple of a normalized log
evaluation, or the zero price of a collapsed placement. -/
def IsSpectralPrice (hunit : ∀ t : P, res 1 t) (g : Additive P →+ ℝ) : Prop :=
  g = 0 ∨ ∃ (f : normalizedSpectrum res) (c : ℝ), 0 < c ∧ g = c • spectralLogHom hunit f

theorem IsSpectralPrice.nonneg {hunit : ∀ t : P, res 1 t} {g : Additive P →+ ℝ}
    (hg : IsSpectralPrice hunit g) (t : Additive P) : 0 ≤ g t := by
  rcases hg with rfl | ⟨f, c, hc, rfl⟩
  · rfl
  · exact mul_nonneg hc.le (spectralLogHom_nonneg hunit f t)

theorem IsSpectralPrice.mono {hunit : ∀ t : P, res 1 t} {g : Additive P →+ ℝ}
    (hg : IsSpectralPrice hunit g) {x y : Additive P} (hxy : res x.toMul.val y.toMul.val) :
    g x ≤ g y := by
  rcases hg with rfl | ⟨f, c, hc, rfl⟩
  · rfl
  · apply mul_le_mul_of_nonneg_left _ hc.le
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact_mod_cast zero_lt_one.trans_le (one_le_spectral_value f (hunit x.toMul))
    · exact_mod_cast f.property.2.2.2.2 _ _ hxy

/-- The price selected from the actual normalized spectrum. The inputs from
tensor theory are finite rank, strict comparison and the ordinary-sum estimate
on positive powers of a diagonal times private products; all numerical
amplification, denominator clearing and compactness arguments are proved. -/
theorem spectral_price_of_permutation_stretch
    (hunit : ∀ t : P, res 1 t) (h₂ : (2 : A) ∈ P)
    (hfinite : ∀ t : A, ∃ n : ℕ, res t n)
    (hne : (normalizedSpectrum res).Nonempty)
    (ordinarySum : Additive P → (L : ℕ) → (Fin L → Additive P) → Prop)
    (compare : ExpandedStrictComparison (Set.range (spectralLogHom hunit))
      (fun x y => res x.toMul.val y.toMul.val) ordinarySum)
    (G : AddSubmonoid (Additive P)) (Δ u : Additive P) (hu : u ∈ G)
    (a b c : Additive P →+ ℝ) (ha : IsSpectralPrice hunit a)
    (hb : IsSpectralPrice hunit b) (hc : IsSpectralPrice hunit c)
    (lam C : ℝ) (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (hU : 0 < (lam • a + b + c) u)
    (stretch : ∀ x ∈ G, ∀ (m L : ℕ) (Z : Fin L → Additive P), 0 < m →
      ordinarySum (m • (Δ + x)) L Z → ∃ l,
        (lam • a + b + c) (m • (Δ + x)) ≤
          (lam • a + b + c) (Z l) + C * Real.logb 2 L) :
    ∃ g : Additive P →+ ℝ, IsSpectralPrice hunit g ∧
      (∀ t, g t ≤ (lam • a + b + c) t) ∧ ∀ t ∈ G, g t = (lam • a + b + c) t := by
  classical
  let h := lam • a + b + c
  let : CompactSpace (normalizedSpectrum res) :=
    isCompact_iff_compactSpace.mp (isCompact_normalizedSpectrum res hfinite)
  let : Nonempty (normalizedSpectrum res) := hne.to_subtype
  have hh (t : Additive P) : 0 ≤ h t :=
    add_nonneg (add_nonneg (mul_nonneg hlam (ha.nonneg t)) (hb.nonneg t)) (hc.nonneg t)
  have hmono {x y : Additive P} (hxy : res x.toMul.val y.toMul.val) : h x ≤ h y :=
    add_le_add (add_le_add (mul_le_mul_of_nonneg_left (ha.mono hxy) hlam) (hb.mono hxy))
      (hc.mono hxy)
  have hfull (f : normalizedSpectrum res) : ∃ t, 0 < spectralLogHom hunit f t := by
    refine ⟨Additive.ofMul (⟨2,h₂⟩ : P), ?_⟩
    rw [spectralLogHom_two]
    norm_num
  obtain ⟨f, d, hd, hle, heq⟩ := select_spectral_price_of_finite_comparison
    (spectralLogHom hunit) h G Δ u (continuous_spectralLogHom hunit)
    (spectralLogHom_nonneg hunit) hh hu hU hfull (by
      intro x hx J Y hcover
      obtain ⟨i₀, _⟩ := hcover (Classical.choice inferInstance)
      apply finite_comparison_of_ordinary_sum compare h hmono hC (stretch x hx) (Fin.pos i₀) Y
      rintro _ ⟨q, rfl⟩
      exact hcover q)
  exact ⟨d • spectralLogHom hunit f, Or.inr ⟨f, d, hd, rfl⟩, hle, heq⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteSpectrum
section

/-!
# Finite-party diagonal bounds and simultaneous extension constraints

Each coordinate tensor is a restriction of the full diagonal indexed by its
coordinate positions. Conversely a nonzero coefficient supplies a restriction
to the scalar unit. The resulting bounds give compactness for spectral
evaluations, which lets the old tensor prices in a site extension be prescribed
simultaneously once every finite list can be matched.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical NNReal
noncomputable section

section

namespace Crossing

variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable {B : I → Type*} [∀ i, Fintype (B i)]

/-- Expand a tensor in the local coordinate bases. A common diagonal label
selects the entire coordinate tuple. A distinguished site supplies its coefficient. -/
theorem restricts_from_coordinate_diagonal_equiv {L : Type*} [Fintype L]
    (e : L ≃ (∀ i, B i)) (T : (∀ i, B i) → K) :
    IsRestriction T (basisTensor (I := I) (fun (l : L) _ ↦ l)) := by
  classical
  let o : I := Classical.choice inferInstance
  let M (i : I) (b : B i) (a : ∀ i, B i) : K :=
    (if b = a i then 1 else 0) * (if i = o then T a else 1)
  apply (restriction_basisTensor_iff _ _).mpr
  refine ⟨fun i b l ↦ M i b (e l), fun b ↦ ?_⟩
  have hprod (a : ∀ i, B i) :
      (∏ i, M i (b i) a) = if b = a then T a else 0 := by
    simp only [M, Finset.prod_mul_distrib, Fintype.prod_boole, ← funext_iff]
    simp
  rw [e.sum_comp (fun a ↦ ∏ i, M i (b i) a)]
  simp [hprod]

/-- A single nonzero coefficient makes the scalar unit a local linear image. -/
theorem unit_restricts_of_nonzero {T : (∀ i, B i) → K} (h : T ≠ 0) :
    IsRestriction (fun _ : I → PUnit ↦ (1 : K)) T := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, T a ≠ 0 := by
    by_contra! hn
    exact h (funext hn)
  let o : I := Classical.choice inferInstance
  let M (i : I) (_ : PUnit) (b : B i) : K :=
    (if b = a i then 1 else 0) * (if i = o then (T a)⁻¹ else 1)
  refine ⟨M, fun _ ↦ ?_⟩
  have hprod (b : ∀ i, B i) :
      (∏ i, M i PUnit.unit (b i)) = if b = a then (T a)⁻¹ else 0 := by
    simp only [M, Finset.prod_mul_distrib, Fintype.prod_boole, ← funext_iff]
    simp
  simp [hprod, mul_ite, ha]

end Crossing

namespace SiteTensor.Raw

universe v

/-- A concrete diagonal of finite size supplies every coefficient array,
even if the coordinate spaces and the set of sites use different universes. -/
theorem restricts_diagonal (I : Type*) [Fintype I] [Nonempty I]
    {K : Type*} [Field K] (X : Raw.{v} I K) :
    X.Restricts (diagonal I K (ULift.{v} (Fin (Fintype.card (∀ i, X.Leg i))))) := by
  classical
  let e : ULift.{v} (Fin (Fintype.card (∀ i, X.Leg i))) ≃ (∀ i, X.Leg i) :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  have h := Crossing.restricts_from_coordinate_diagonal_equiv e X.coeff
  unfold Crossing.basisTensor at h
  convert! h using 1
  funext x
  simp only [diagonal]
  congr 1
  funext a
  split_ifs <;> simp_all

/-- Conversely the multiplicative unit is a restriction of every nonzero tensor. -/
theorem one_restricts_of_nonzero {I : Type*} [Fintype I] [Nonempty I]
    {K : Type*} [Field K] (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    (one I K).Restricts X :=
  Crossing.unit_restricts_of_nonzero h

end SiteTensor.Raw

/-- On the enlarged site set, finite compatibility gives agreement on all
old evaluations and retains any closed wire-distance constraint. This also
allows prescribed values on uncountably many old tensors. -/
theorem exists_matching_spectral_point {S A : Type*} [Semiring S]
    (restricts : S → S → Prop) (hrank : ∀ x, ∃ n : ℕ, restricts x n)
    (tensor : A → S) (target : A → ℝ≥0)
    (wire : Set (normalizedSpectrum restricts)) (hclosed : IsClosed wire)
    (hfinite : ∀ a : Finset A, ∃ f ∈ wire, ∀ i ∈ a, f.val (tensor i) = target i) :
    ∃ f ∈ wire, ∀ i, f.val (tensor i) = target i := by
  classical
  let : CompactSpace (normalizedSpectrum restricts) :=
    isCompact_iff_compactSpace.mp (isCompact_normalizedSpectrum restricts hrank)
  let C (a : A) : Set (normalizedSpectrum restricts) := {f | f.val (tensor a) = target a}
  have hc (a : A) : IsClosed (C a) :=
    isClosed_eq ((continuous_apply (tensor a)).comp continuous_subtype_val) continuous_const
  have hp : (wire ∩ ⋂ a, C a).Nonempty :=
    hclosed.isCompact.inter_iInter_nonempty _ hc (fun a ↦ by
      obtain ⟨f, hf, ha⟩ := hfinite a
      exact ⟨f, hf, Set.mem_iInter₂.mpr ha⟩)
  obtain ⟨f, hf, h⟩ := hp
  exact ⟨f, hf, Set.mem_iInter.mp h⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.Nonzero
section

/-! # Nonzero tensors up to restriction -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

variable {I : Type u} [Fintype I] {K : Type w}

section Semiring

variable [CommSemiring K]

/-- The zero tensor is a restriction of every tensor. -/
theorem zero_le_tensor [Nonempty I] (X : TensorClass.{v} I K) : 0 ≤ X := by
  induction X using Quotient.inductionOn with
  | h x =>
    change (Raw.zero I K).Restricts x
    refine ⟨fun _ _ _ => 0, fun y => ?_⟩
    exact (y (Classical.arbitrary I)).elim

/-- A tensor represents zero precisely when every coefficient vanishes. -/
theorem ofRaw_eq_zero_iff (X : Raw.{v} I K) : ofRaw X = 0 ↔ X.coeff = 0 := by
  change ofRaw X = ofRaw (Raw.zero I K) ↔ _
  rw [ofRaw_eq_iff]
  constructor
  · rintro ⟨⟨M, hM⟩, _⟩
    funext x
    simpa [Raw.zero] using hM x
  · intro h
    constructor
    · refine ⟨fun _ _ _ => 0, fun x => ?_⟩
      simp [Raw.zero, h]
    · refine ⟨fun _ _ _ => 0, fun y => ?_⟩
      simp [Raw.zero, h]

instance [Nonempty I] [Nontrivial K] : Nontrivial (TensorClass.{v} I K) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h' := (ofRaw_eq_zero_iff (Raw.one.{v} I K)).mp h
  exact one_ne_zero (congrFun h' (fun _ => PUnit.unit))

instance [Nonempty I] [NoZeroDivisors K] : NoZeroDivisors (TensorClass.{v} I K) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} := by
    induction a using Quotient.inductionOn with | h X =>
    induction b using Quotient.inductionOn with | h Y =>
    change ofRaw (X.mul Y) = 0 → ofRaw X = 0 ∨ ofRaw Y = 0
    simp only [ofRaw_eq_zero_iff]
    intro h
    by_cases hX : X.coeff = 0
    · exact Or.inl hX
    · apply Or.inr
      obtain ⟨x, hx⟩ : ∃ x, X.coeff x ≠ 0 := by
        by_contra! h0
        exact hX (funext h0)
      funext y
      exact (mul_eq_zero.mp (congrFun h (fun i => (x i, y i)))).resolve_left hx

end Semiring

/-- A nonzero class dominates the unit, by contracting onto a nonzero coefficient. -/
theorem one_le_of_ne_zero [Nonempty I] [Field K] {X : TensorClass.{v} I K}
    (h : X ≠ 0) : 1 ≤ X := by
  induction X using Quotient.inductionOn with
  | h x =>
    exact x.one_restricts_of_nonzero (fun h0 => h ((ofRaw_eq_zero_iff x).mpr h0))

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.RawLogPrice
section

/-!
# Scaled logarithmic prices on finite-site tensor classes

A nonzero field tensor restricts to the scalar unit, so every normalized point takes
values in `{0} ∪ [1,∞)`. Lean's convention `log 0 = 0` therefore extends a log
price monotonically to the zero tensor.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open scoped NNReal

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → _))

/-- The price of a raw tensor at a normalized spectral point and a common scale. -/
def rawLogPrice (c : ℝ) (X : Raw.{v} I K) : ℝ :=
  c * Real.logb 2 (φ.val (ofRaw X) : ℝ)

/-- The positivity needed when taking the logarithm of a nonzero tensor. -/
theorem one_le_raw_spectralValue (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    1 ≤ φ.val (ofRaw X) :=
  one_le_spectral_value φ (X.one_restricts_of_nonzero h)

/-- The zero tensor has price zero. -/
theorem rawLogPrice_zero (c : ℝ) (X : Raw.{v} I K) (h : X.coeff = 0) :
    rawLogPrice φ c X = 0 := by
  simp [rawLogPrice, (ofRaw_eq_zero_iff X).mpr h, φ.property.1]

/-- At a nonnegative scale every tensor has nonnegative price. -/
theorem rawLogPrice_nonneg {c : ℝ} (hc : 0 ≤ c) (X : Raw.{v} I K) :
    0 ≤ rawLogPrice φ c X := by
  by_cases h : X.coeff = 0
  · rw [rawLogPrice_zero φ c X h]
  · apply mul_nonneg hc (Real.logb_nonneg (by norm_num) _)
    exact_mod_cast one_le_raw_spectralValue φ X h

/-- Scaled log price respects the actual local-matrix restriction preorder,
including when a restriction annihilates the input. -/
theorem rawLogPrice_mono {c : ℝ} (hc : 0 ≤ c) {X Y : Raw.{v} I K}
    (h : X.Restricts Y) : rawLogPrice φ c X ≤ rawLogPrice φ c Y := by
  by_cases hX : X.coeff = 0
  · rw [rawLogPrice_zero φ c X hX]
    exact rawLogPrice_nonneg φ hc _
  · apply mul_le_mul_of_nonneg_left _ hc
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ X hX)
    · exact_mod_cast φ.property.2.2.2.2 (ofRaw X) (ofRaw Y) h

/-- Multiplicativity of a normalized point gives additivity of price on nonzero
tensor factors. -/
theorem rawLogPrice_mul (c : ℝ) (X Y : Raw.{v} I K)
    (hX : X.coeff ≠ 0) (hY : Y.coeff ≠ 0) :
    rawLogPrice φ c (X.mul Y) = rawLogPrice φ c X + rawLogPrice φ c Y := by
  have pos (T : Raw.{v} I K) (h : T.coeff ≠ 0) : (φ.val (ofRaw T) : ℝ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (one_le_raw_spectralValue φ T h)).ne'
  simp only [rawLogPrice, ofRaw_mul, φ.property.2.2.2.1, NNReal.coe_mul,
    Real.logb_mul (pos X hX) (pos Y hY), mul_add]

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.MaskDiagonalPrice
section

/-! # Prices of partial diagonals on a fixed set of sites

The same spectral point evaluates all the partial diagonals. Their positive
label dimensions form a monotone multiplicative family, so its entire
logarithmic price law is determined by the binary label.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SiteTensor

open scoped Classical NNReal

variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

/-- A partial diagonal coefficient tests consistency with any specified occupied site. -/
theorem Raw.maskDiagonal_coeff_at (S : Finset I) {i₀ : I} (hi₀ : i₀ ∈ S)
    {α : Type} [Fintype α] (x : ∀ i, MaskLeg S α i) :
    (Raw.maskDiagonal K S α).coeff x = if ∀ (i : I) (hi : i ∈ S), x i hi = x i₀ hi₀ then 1 else 0 := by
  unfold Raw.maskDiagonal Crossing.basisTensor
  dsimp only
  rw [Finset.sum_eq_single (x i₀ hi₀)]
  · simp only [funext_iff]
  · intro a _ hne
    exact if_neg fun ha ↦ hne (congrFun (congrFun ha i₀) hi₀).symm
  · simp

omit [DecidableEq I] in
/-- Selecting one input coefficient at each output basis index is a local restriction. -/
theorem Raw.restrict_by_read {X Y : Raw.{0} I K} (g : ∀ i, X.Leg i → Y.Leg i)
    (hcoeff : ∀ x, X.coeff x = Y.coeff (fun i ↦ g i (x i))) : X.Restricts Y := by
  classical
  refine ⟨fun i x y ↦ if y = g i x then 1 else 0, fun x ↦ ?_⟩
  rw [hcoeff x]
  simp_rw [Fintype.prod_boole]
  have heq (y : ∀ i, Y.Leg i) : (∀ i, y i = g i (x i)) ↔ y = fun i ↦ g i (x i) :=
    funext_iff.symm
  simp [heq, mul_ite]

/-- Projecting the labels at all occupied sites realizes embeddings of label sets. -/
theorem Raw.maskDiagonal_restricts_of_embedding (S : Finset I) (hS : S.Nonempty)
    {α β : Type} [Fintype α] [Fintype β] (e : α ↪ β) :
    (Raw.maskDiagonal K S α).Restricts (Raw.maskDiagonal K S β) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hS
  let g (i : I) (x : MaskLeg S α i) : MaskLeg S β i := fun hi ↦ e (x hi)
  apply Raw.restrict_by_read (X := Raw.maskDiagonal K S α) (Y := Raw.maskDiagonal K S β) g
  intro x
  calc
    _ = _ := Raw.maskDiagonal_coeff_at (K := K) S hi₀ x
    _ = _ := ?_
    _ = _ := (Raw.maskDiagonal_coeff_at (K := K) S hi₀ (fun i ↦ g i (x i))).symm
  simp [g]


theorem ofRaw_maskDiagonal_equiv (S : Finset I) (hS : S.Nonempty)
    {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) :
    ofRaw (Raw.maskDiagonal K S α) = ofRaw (Raw.maskDiagonal K S β) :=
  ofRaw_eq_iff.mpr ⟨Raw.maskDiagonal_restricts_of_embedding S hS e.toEmbedding,
    Raw.maskDiagonal_restricts_of_embedding S hS e.symm.toEmbedding⟩

omit [DecidableEq I] in
/-- Multiplicativity in the dimension, using independent pairs of labels. -/
theorem ofRaw_maskDiagonal_prod (S : Finset I) (α β : Type) [Fintype α] [Fintype β] :
    ofRaw (Raw.maskDiagonal K S (α × β)) =
      ofRaw (Raw.maskDiagonal K S α) * ofRaw (Raw.maskDiagonal K S β) := by
  let a (x : α) (i : I) (_ : i ∈ S) := x
  let b (x : β) (i : I) (_ : i ∈ S) := x
  let c (x : α × β) (i : I) (_ : i ∈ S) := x
  let e (i : I) : MaskLeg S (α × β) i ≃ MaskLeg S α i × MaskLeg S β i :=
    { toFun := fun f ↦ (fun j ↦ (f j).1, fun j ↦ (f j).2)
      invFun := fun f j ↦ (f.1 j, f.2 j)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let : ∀ i, Fintype (MaskLeg S α i) := (Raw.maskDiagonal K S α).finiteLeg
  let : ∀ i, Fintype (MaskLeg S β i) := (Raw.maskDiagonal K S β).finiteLeg
  let : ∀ i, Fintype (MaskLeg S (α × β) i) := (Raw.maskDiagonal K S (α × β)).finiteLeg
  exact basisTensor_paired_eq_mul (K := K) (A := MaskLeg S α) (B := MaskLeg S β)
    (C := MaskLeg S (α × β)) a b c e (fun _ _ _ ↦ rfl)

variable [Nonempty I]

/-- The natural label dimensions as a monoid homomorphism into tensor classes. -/
def maskDiagonalHom (K : Type*) [Field K] (S : Finset I) (hS : S.Nonempty) :
    ℕ →* TensorClass.{0} I K where
  toFun n := ofRaw (Raw.maskDiagonal K S (Fin n))
  map_one' := by
    obtain ⟨i, hi⟩ := hS
    apply ofRaw_eq_iff.mpr
    apply Raw.reindex_equivalent (X := Raw.maskDiagonal K S (Fin 1)) (Y := Raw.one I K)
      (fun j ↦ Equiv.ofUnique (MaskLeg S (Fin 1) j) PUnit)
    intro x
    calc
      _ = _ := Raw.maskDiagonal_coeff_at (K := K) S hi x
      _ = _ := if_pos (fun _ _ ↦ Subsingleton.elim (α := Fin 1) _ _)
  map_mul' n m := (ofRaw_maskDiagonal_equiv S hS finProdFinEquiv.symm).trans
    (ofRaw_maskDiagonal_prod S (Fin n) (Fin m))

/-- Increasing dimension gives a restriction comparison inside the fixed ambient format. -/
theorem maskDiagonalHom_mono (S : Finset I) (hS : S.Nonempty) : Monotone (maskDiagonalHom K S hS) :=
  fun _ _ h ↦ Raw.maskDiagonal_restricts_of_embedding S hS (Fin.castLEEmb h)

/-- Exact base-two price of a common label on a nonempty support. -/
theorem maskDiagonal_log_price
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
    (S : Finset I) (hS : S.Nonempty) {q : ℕ} (hq : 0 < q) :
    Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K S (Fin q))) : ℝ) =
      Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K S (Fin 2))) : ℝ) * Real.logb 2 q := by
  let v := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (maskDiagonalHom K S hS)
  apply spectral_natCast_logb (A := ℕ) (v := v) _ q hq
  intro a b _ hab
  exact φ.property.2.2.2.2 _ _ (maskDiagonalHom_mono S hS hab)

omit [Nonempty I] in
/-- A partial diagonal on a nonempty support with at least one label is nonzero. -/
theorem Raw.maskDiagonal_ne_zero (S : Finset I) (hS : S.Nonempty)
    (α : Type) [Fintype α] [Nonempty α] : (Raw.maskDiagonal K S α).coeff ≠ 0 := by
  obtain ⟨i, hi⟩ := hS
  let a : α := Classical.choice inferInstance
  intro hzero
  have h := congrFun hzero (fun _ _ ↦ a)
  change (Raw.maskDiagonal K S α).coeff (fun _ _ ↦ a) = 0 at h
  exact one_ne_zero (by simpa only [Raw.maskDiagonal_coeff_at (K := K) S hi (fun _ _ ↦ a),
    implies_true, ite_true] using h)

omit [Nonempty I] in
/-- Deleting occurrences of the common label is a local restriction. -/
theorem Raw.maskDiagonal_restricts_of_subset {S T : Finset I} (h : S ⊆ T)
    (α : Type) [Fintype α] :
    (Raw.maskDiagonal K S α).Restricts (Raw.maskDiagonal K T α) := by
  let c (a : α) (i : I) (_ : i ∈ T) := a
  let : ∀ i, Fintype (MaskLeg T α i) := (Raw.maskDiagonal K T α).finiteLeg
  apply (Crossing.restriction_basisTensor_iff (F := K) (A := MaskLeg T α) (B := MaskLeg S α)
    c (Raw.maskDiagonal K S α).coeff).mpr
  refine ⟨fun i x y ↦ if x = (fun hi ↦ y (h hi)) then 1 else 0, fun x ↦ ?_⟩
  simp only [Raw.maskDiagonal, Crossing.basisTensor, Fintype.prod_boole, c, funext_iff]

/-- One site's diagonal is the tensor class of the scalar unit. -/
theorem ofRaw_maskDiagonal_singleton (i : I) (α : Type) [Fintype α] [Nonempty α] :
    ofRaw (Raw.maskDiagonal K {i} α) = 1 := by
  apply ofRaw_eq_iff.mpr
  refine ⟨Raw.restrict_by_read (Y := Raw.one I K) (fun _ _ ↦ PUnit.unit) ?_,
    Raw.one_restricts_of_nonzero _ (Raw.maskDiagonal_ne_zero _ (Finset.singleton_nonempty i) α)⟩
  intro x
  calc
    _ = _ := Raw.maskDiagonal_coeff_at (K := K) {i} (Finset.mem_singleton_self i) x
    _ = _ := if_pos (fun j hj ↦ by obtain rfl := Finset.mem_singleton.mp hj; rfl)

omit [Nonempty I] in
/-- Equating the common labels where two nonempty diagonals overlap supplies
the diagonal on their union. -/
theorem Raw.maskDiagonal_union_restricts_mul (A B : Finset I) (hI : (A ∩ B).Nonempty)
    (α : Type) [Fintype α] :
    (Raw.maskDiagonal K (A ∪ B) α).Restricts
      ((Raw.maskDiagonal K A α).mul (Raw.maskDiagonal K B α)) := by
  obtain ⟨i₀, hi₀⟩ := hI
  obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hi₀
  let g₁ (i : I) (x : MaskLeg (A ∪ B) α i) (hi : i ∈ A) := x (Finset.mem_union_left _ hi)
  let g₂ (i : I) (x : MaskLeg (A ∪ B) α i) (hi : i ∈ B) := x (Finset.mem_union_right _ hi)
  apply Raw.restrict_by_read (fun i x ↦ (g₁ i x, g₂ i x))
  intro x
  change (maskDiagonal K (A ∪ B) α).coeff x =
    (maskDiagonal K A α).coeff (fun i ↦ g₁ i (x i)) *
      (maskDiagonal K B α).coeff (fun i ↦ g₂ i (x i))
  rw [Raw.maskDiagonal_coeff_at (K := K) (A ∪ B) (Finset.mem_union_left _ ha) x,
    Raw.maskDiagonal_coeff_at (K := K) A ha (fun i ↦ g₁ i (x i)),
    Raw.maskDiagonal_coeff_at (K := K) B hb (fun i ↦ g₂ i (x i))]
  let v := x i₀ (Finset.mem_union_left B ha)
  have heq : (∀ (i : I) (hi : i ∈ A ∪ B), x i hi = v) ↔
      (∀ (i : I) (hi : i ∈ A), g₁ i (x i) hi = v) ∧
      ∀ (i : I) (hi : i ∈ B), g₂ i (x i) hi = v := by
    constructor
    · intro H
      exact ⟨fun _ _ ↦ H _ _, fun _ _ ↦ H _ _⟩
    · rintro ⟨H₁, H₂⟩ i hi
      rcases Finset.mem_union.mp hi with h | h
      · exact H₁ i h
      · exact H₂ i h
  change (if ∀ (i : I) (hi : i ∈ A ∪ B), x i hi = v then (1 : K) else 0) =
    (if ∀ (i : I) (hi : i ∈ A), g₁ i (x i) hi = v then 1 else 0) *
      (if ∀ (i : I) (hi : i ∈ B), g₂ i (x i) hi = v then 1 else 0)
  split_ifs <;> simp_all

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))

/-- The common binary label price at the chosen sites, evaluated at a single
ambient spectral point and scale. -/
def maskDiagonalPrice (c : ℝ) (S : Finset I) : ℝ := rawLogPrice φ c (Raw.maskDiagonal K S (Fin 2))

theorem rawLogPrice_maskDiagonal (c : ℝ) (S : Finset I) (hS : S.Nonempty) {q : ℕ} (hq : 0 < q) :
    rawLogPrice φ c (Raw.maskDiagonal K S (Fin q)) = maskDiagonalPrice φ c S * Real.logb 2 q := by
  unfold maskDiagonalPrice rawLogPrice
  rw [maskDiagonal_log_price φ S hS hq, mul_assoc]

theorem maskDiagonalPrice_mono {c : ℝ} (hc : 0 ≤ c) : Monotone (maskDiagonalPrice φ c) :=
  fun _ _ h ↦ rawLogPrice_mono φ hc (Raw.maskDiagonal_restricts_of_subset h (Fin 2))

omit [DecidableEq I] in
theorem maskDiagonalPrice_nonneg {c : ℝ} (hc : 0 ≤ c) (S : Finset I) :
    0 ≤ maskDiagonalPrice φ c S := rawLogPrice_nonneg φ hc _

theorem maskDiagonalPrice_singleton (c : ℝ) (i : I) : maskDiagonalPrice φ c {i} = 0 := by
  simp [maskDiagonalPrice, rawLogPrice, ofRaw_maskDiagonal_singleton, φ.property.2.1]

/-- Sending the independent labels on overlapping sets can supply one common
label on their union. -/
theorem maskDiagonalPrice_union_le {c : ℝ} (hc : 0 ≤ c) (A B : Finset I) (hAB : (A ∩ B).Nonempty) :
    maskDiagonalPrice φ c (A ∪ B) ≤ maskDiagonalPrice φ c A + maskDiagonalPrice φ c B := by
  have hm := rawLogPrice_mono φ hc (Raw.maskDiagonal_union_restricts_mul A B hAB (Fin 2))
  rwa [rawLogPrice_mul φ c _ _
    (Raw.maskDiagonal_ne_zero A (hAB.mono Finset.inter_subset_left) (Fin 2))
    (Raw.maskDiagonal_ne_zero B (hAB.mono Finset.inter_subset_right) (Fin 2))] at hm

/-- A wire from any occupied site suffices to append a common label at another site. -/
theorem maskDiagonalPrice_insert_le_wire {c : ℝ} (hc : 0 ≤ c) (A : Finset I) {x : I}
    (hx : x ∈ A) (z : I) :
    maskDiagonalPrice φ c (insert z A) ≤ maskDiagonalPrice φ c A + maskDiagonalPrice φ c {x, z} := by
  have hunion : A ∪ {x,z} = insert z A := by ext w; simp; grind
  rw [← hunion]
  apply maskDiagonalPrice_union_le φ hc
  exact ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_insert_self _ _⟩⟩

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.DiagonalRaw
section

/-! # Diagonal tensors and their direct sums -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor.Raw

universe v
variable (I K : Type*) [Fintype I] [CommSemiring K]

/-- The common-label diagonal only depends on the label type up to equivalence. -/
theorem diagonal_equiv {α β : Type v} [Fintype α] [Fintype β] (e : α ≃ β) :
    (diagonal I K α).Equivalent (diagonal I K β) := by
  classical
  apply reindex_equivalent (fun _ => e)
  intro (x : I → α)
  simp only [diagonal]
  refine Fintype.sum_equiv e _ _ fun a => ?_
  have h : (fun i => e (x i)) = (fun _ => e a) ↔ x = (fun _ => a) := by
    simp [funext_iff]
  congr! 1
  exact h.symm

/-- The empty diagonal is the zero tensor. -/
theorem diagonal_empty_equivalent :
    (diagonal I K PEmpty.{v + 1}).Equivalent (zero I K) := by
  classical
  apply reindex_equivalent (fun _ => Equiv.refl _)
  intro x
  simp [diagonal]

/-- The one-label diagonal is the scalar unit. -/
theorem diagonal_unit_equivalent :
    (diagonal I K PUnit.{v + 1}).Equivalent (one I K) := by
  classical
  apply reindex_equivalent (X := diagonal I K _) (Y := one I K) (fun _ => Equiv.refl _)
  intro (x : I → PUnit.{v + 1})
  simp [diagonal, one, Subsingleton.elim x (fun _ => PUnit.unit)]

private theorem push_constant_labels (α : Type v) [Fintype α] {Y : Type*}
    (f : (I → α) → Y) (y : Y) :
    pushCoeff f (diagonal I K α).coeff y =
      ∑ a : α, if f (fun _ => a) = y then 1 else 0 := by
  classical
  let c (a : α) : I → α := fun _ => a
  have hc : (diagonal I K α).coeff = pushCoeff c (fun _ => 1) := by
    funext x
    apply Finset.sum_congr rfl
    intro a _
    change (if x = c a then (1 : K) else 0) = (if c a = x then 1 else 0)
    congr! 1
    exact eq_comm
  rw [hc, pushCoeff_comp]
  rfl

/-- A direct sum of diagonals has all the labels of the disjoint union. -/
theorem diagonal_sum_equivalent (α β : Type v) [Fintype α] [Fintype β] :
    ((diagonal I K α).add (diagonal I K β)).Equivalent (diagonal I K (α ⊕ β)) := by
  classical
  apply reindex_equivalent (X := (diagonal I K α).add (diagonal I K β))
    (Y := diagonal I K (α ⊕ β)) (fun _ => Equiv.refl _)
  intro (x : I → α ⊕ β)
  let f (y : I → α) (i : I) : α ⊕ β := Sum.inl (y i)
  let g (y : I → β) (i : I) : α ⊕ β := Sum.inr (y i)
  change pushCoeff f (diagonal I K α).coeff x +
    pushCoeff g (diagonal I K β).coeff x = (diagonal I K (α ⊕ β)).coeff x
  rw [push_constant_labels I K α, push_constant_labels I K β]
  simp only [diagonal, Fintype.sum_sum_type]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro a _ <;>
    congr! 1 <;> exact eq_comm

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
section

/-! # Natural numbers in the tensor semiring -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v
variable (I K : Type*) [Fintype I] [Nonempty I] [CommSemiring K]

/-- A natural number in the tensor semiring is the class of the common-label
diagonal of that size. -/
@[simp] theorem ofRaw_diagonal_eq_natCast (α : Type v) [Fintype α] :
    ofRaw (Raw.diagonal I K α) = (Fintype.card α : TensorClass.{v} I K) := by
  classical
  refine Fintype.induction_empty_option (P := fun β _ =>
    ofRaw (Raw.diagonal I K β) = (Fintype.card β : TensorClass.{v} I K)) ?_ ?_ ?_ α
  · intro β γ _ e ih
    let := Fintype.ofEquiv γ e.symm
    rw [← Fintype.card_congr e, ← ih]
    exact ofRaw_eq_iff.mpr (Raw.diagonal_equiv I K e.symm)
  · rw [Fintype.card_pempty, Nat.cast_zero, ← ofRaw_zero]
    exact ofRaw_eq_iff.mpr (Raw.diagonal_empty_equivalent I K)
  · intro β _ ih
    rw [Fintype.card_option, Nat.cast_add, Nat.cast_one, ← ih, ← ofRaw_one]
    have h := Raw.diagonal_equiv I K (Equiv.optionEquivSumPUnit.{v} β)
    rw [ofRaw_eq_iff.mpr h, ← ofRaw_eq_iff.mpr (Raw.diagonal_sum_equivalent I K β PUnit.{v + 1}),
      ofRaw_add, ofRaw_eq_iff.mpr (Raw.diagonal_unit_equivalent I K)]

@[simp] theorem ofRaw_diagonal_fin_eq_natCast (n : ℕ) :
    ofRaw (Raw.diagonal I K (Fin n)) = (n : TensorClass.{0} I K) := by
  simpa only [Fintype.card_fin] using ofRaw_diagonal_eq_natCast I K (Fin n)

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Tensor
section

/-!
# Coefficient calculus for simultaneous local maps

A local matrix is indexed by its output basis followed by its input basis.
The coefficient formulas retain the matrices, which allows each site to choose
its matrix as a function of a control.
-/

open scoped BigOperators Classical
open OAI.LinearAlgebra.SpectralBooks
open OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

noncomputable section

variable {S K : Type*} [Fintype S]
variable {A B C D : S → Type*}

/-- Apply one local matrix at each site to a coefficient tensor. -/
def contract [CommSemiring K] [∀ i, Fintype (A i)]
    (M : ∀ i, B i → A i → K) (T : (∀ i, A i) → K) (x : ∀ i, B i) : K :=
  ∑ a, T a * ∏ i, M i (x i) (a i)

theorem restrict_iff_contract [CommSemiring K] [∀ i, Fintype (A i)]
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    Crossing.IsRestriction U T ↔ ∃ M : ∀ i, B i → A i → K, U = contract M T :=
  exists_congr fun _ => funext_iff.symm

/-- Expand a tensor given as a sum of coordinate basis tensors before applying local matrices. -/
theorem contract_basisTensor [CommSemiring K] [∀ i, Fintype (A i)]
    {L : Type*} [Fintype L] (M : ∀ i, B i → A i → K) (f : L → ∀ i, A i) (x : ∀ i, B i) :
    contract M (Crossing.basisTensor f) x =
      ∑ l, ∏ i, M i (x i) (f l i) := by
  unfold contract Crossing.basisTensor
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- A common label is summed once, also when only a subset of the sites holds it. -/
theorem contract_maskDiagonal [Field K] (P : Finset S) (L : Type) [Fintype L]
    (M : ∀ i, B i → (Raw.maskDiagonal K P L).Leg i → K) (x : ∀ i, B i) :
    contract M (Raw.maskDiagonal K P L).coeff x =
      ∑ l : L, ∏ i, M i (x i) (fun _ => l) :=
  contract_basisTensor M (fun (l : L) _ _ => l) x

/-- The contraction of a basis label is a product of sitewise matrix entries. -/
theorem contract_basis [CommSemiring K] [∀ i, Fintype (A i)]
    (M : ∀ i, B i → A i → K) (a : ∀ i, A i) (x : ∀ i, B i) :
    contract M (fun y => if y = a then 1 else 0) x = ∏ i, M i (x i) (a i) := by
  simp [contract, ite_mul]

/-- Successive restrictions multiply the local matrices. -/
theorem contract_comp [CommSemiring K] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (N : ∀ i, C i → B i → K) (M : ∀ i, B i → A i → K) (T : (∀ i, A i) → K) :
    contract N (contract M T) = contract (fun i c a => ∑ b, M i b a * N i c b) T := by
  funext x
  unfold contract
  simp_rw [Finset.sum_mul, Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib,
    mul_assoc]
  exact Finset.sum_comm

/-- Independent resources transform under the Kronecker products of their local matrices. -/
theorem contract_mul [CommSemiring K] [∀ i, Fintype (A i)] [∀ i, Fintype (C i)]
    (M : ∀ i, B i → A i → K) (N : ∀ i, D i → C i → K)
    (T : (∀ i, A i) → K) (U : (∀ i, C i) → K) (x : ∀ i, B i × D i) :
    contract (fun i (v : B i × D i) (a : A i × C i) => M i v.1 a.1 * N i v.2 a.2)
        (fun a => T (fun i => (a i).1) * U (fun i => (a i).2)) x =
      contract M T (fun i => (x i).1) * contract N U (fun i => (x i).2) := by
  unfold contract
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow S A C) _ _ fun a => ?_
  simp only [Finset.prod_mul_distrib]
  ac_rfl

/-- Map each diagonal block into the same target and add its image. -/
theorem contract_addBlocks [CommSemiring K] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (M : ∀ i, C i → A i → K) (N : ∀ i, C i → B i → K)
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    contract (fun i c => Sum.elim (M i c) (N i c)) (sumCoeff T U) =
      contract M T + contract N U := by
  funext x
  simp only [contract, sumCoeff, add_mul, Finset.sum_add_distrib, sum_pushCoeff_mul,
    Pi.add_apply, Sum.elim_inl, Sum.elim_inr]

/-- Multiplying a single site's matrix by a scalar scales the output. -/
theorem contract_scaleAt [CommSemiring K] [∀ i, Fintype (A i)]
    (j : S) (z : K) (M : ∀ i, B i → A i → K) (T : (∀ i, A i) → K) (x : ∀ i, B i) :
    contract (fun i b a => (if i = j then z else 1) * M i b a) T x = z * contract M T x := by
  simp only [contract, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
    ite_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ac_rfl

/-- Subtract the second block by changing the sign at one site. -/
theorem contract_subBlocks [CommRing K] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (j : S) (M : ∀ i, C i → A i → K) (N : ∀ i, C i → B i → K)
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (x : ∀ i, C i) :
    contract (fun i c => Sum.elim (M i c) (fun b => (if i = j then -1 else 1) * N i c b))
        (sumCoeff T U) x =
      contract M T x - contract N U x := by
  rw [contract_addBlocks, Pi.add_apply, contract_scaleAt]
  ring

end

end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Control
section

/-! A local matrix may be chosen by a symbol at the same site. A symbol carried
as a basis index can itself select such a matrix while being retained. -/

open scoped BigOperators Classical
open OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Control

noncomputable section

variable {I : Type*} {C D A B E : I → Type*}

/-- Local matrices indexed by classical controls, with output rows first. -/
abbrev Map (C A B : I → Type*) := ∀ i, C i → B i → A i → ℂ

/-- The coefficient obtained by applying the chosen local matrices. -/
def eval [Fintype I] [∀ i, Fintype (A i)] (M : Map C A B)
    (c : ∀ i, C i) (X : (∀ i, A i) → ℂ) (b : ∀ i, B i) : ℂ :=
  contract (fun i => M i (c i)) X b

/-- Apply a function to each control before reading it. -/
def pre (f : ∀ i, D i → C i) (M : Map C A B) : Map D A B :=
  fun i d => M i (f i d)

@[simp] theorem eval_pre [Fintype I] [∀ i, Fintype (A i)]
    (f : ∀ i, D i → C i) (M : Map C A B) (d : ∀ i, D i)
    (X : (∀ i, A i) → ℂ) (b : ∀ i, B i) :
    eval (pre f M) d X b = eval M (fun i => f i (d i)) X b := rfl

/-- The identity acts on every branch of the external control. -/
def idMap {C A : I → Type*} : Map C A A :=
  fun _ _ b a => if a = b then 1 else 0

@[simp] theorem eval_idMap [Fintype I] [∀ i, Fintype (A i)]
    (c : ∀ i, C i) (X : (∀ i, A i) → ℂ) (b : ∀ i, A i) :
    eval idMap c X b = X b := by
  simp [eval, contract, idMap, Fintype.prod_boole, ← funext_iff, mul_ite]

/-- Only the selected rows influence an output coefficient. -/
theorem eval_congr_at [Fintype I] [∀ i, Fintype (A i)]
    {M : Map C A B} {N : Map D A B} {c : ∀ i, C i} {d : ∀ i, D i}
    (X : (∀ i, A i) → ℂ) {b : ∀ i, B i}
    (h : ∀ i a, M i (c i) (b i) a = N i (d i) (b i) a) :
    eval M c X b = eval N d X b := by
  simp only [eval, contract, h]

/-- The output control index selects a block. Within each block the auxiliary
matrix can use both the external control and the retained basis label. -/
def retainMap (M : Map (fun i => D i × C i) A B) :
    Map D (fun i => C i × A i) (fun i => C i × B i) :=
  fun i d y x => if x.1 = y.1 then M i (d, y.1) y.2 x.2 else 0

/-- A block diagonal matrix acts on each slice with precisely its own controls.
The input tensor may correlate the retained labels with the auxiliary indices. -/
theorem eval_retainMap [Fintype I] [∀ i, Fintype (A i)] [∀ i, Fintype (C i)]
    (M : Map (fun i => D i × C i) A B) (d : ∀ i, D i)
    (X : (∀ i, C i × A i) → ℂ) (y : ∀ i, C i × B i) :
    eval (retainMap M) d X y =
      eval M (fun i => (d i, (y i).1))
        (fun a => X (fun i => ((y i).1, a i))) (fun i => (y i).2) := by
  classical
  change (∑ x, X x * ∏ i, (if (x i).1 = (y i).1 then M i (d i, (y i).1) (y i).2 (x i).2 else 0)) = _
  let e := Equiv.arrowProdEquivProdArrow I C A
  calc
    _ = ∑ p : (∀ i, C i) × (∀ i, A i),
        X (fun i => (p.1 i,p.2 i)) *
          ∏ i, (if p.1 i = (y i).1 then M i (d i,(y i).1) (y i).2 (p.2 i) else 0) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp_rw [Fintype.prod_ite_zero, ← funext_iff, mul_ite, mul_zero]
      simp [eval, contract]

/-- Tensoring independent factors with the same controls. -/
def prodMap {A' B' : I → Type*} (M : Map C A B) (N : Map C A' B') :
    Map C (fun i => A i × A' i) (fun i => B i × B' i) :=
  fun i c y x => M i c y.1 x.1 * N i c y.2 x.2

theorem eval_prodMap [Fintype I] {A' B' : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (A' i)]
    (M : Map C A B) (N : Map C A' B') (c : ∀ i, C i)
    (X : (∀ i, A i) → ℂ) (Y : (∀ i, A' i) → ℂ) (b : ∀ i, B i × B' i) :
    eval (prodMap M N) c (fun a => X (fun i => (a i).1) * Y (fun i => (a i).2)) b =
      eval M c X (fun i => (b i).1) * eval N c Y (fun i => (b i).2) :=
  contract_mul (fun i => M i (c i)) (fun i => N i (c i)) X Y b

/-- Compose two local maps chosen by the same external control. -/
def compMap [∀ i, Fintype (B i)] (N : Map C B E) (M : Map C A B) : Map C A E :=
  fun i c e a => ∑ b, M i c b a * N i c e b

theorem eval_compMap [Fintype I] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (N : Map C B E) (M : Map C A B) (c : ∀ i, C i) (X : (∀ i, A i) → ℂ) (e : ∀ i, E i) :
    eval (compMap N M) c X e = eval N c (eval M c X) e :=
  congrFun (contract_comp (fun i => N i (c i)) (fun i => M i (c i)) X).symm e

/-- Local assembly of two block maps into a common output format. -/
def sumMap {A' : I → Type*} (M : Map C A B) (N : Map C A' B) :
    Map C (fun i => A i ⊕ A' i) B :=
  fun i c b => Sum.elim (M i c b) (N i c b)

theorem eval_sumMap [Fintype I] {A' : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (A' i)]
    (M : Map C A B) (N : Map C A' B) (c : ∀ i, C i)
    (X : (∀ i, A i) → ℂ) (Y : (∀ i, A' i) → ℂ) (b : ∀ i, B i) :
    eval (sumMap M N) c (sumCoeff X Y) b = eval M c X b + eval N c Y b :=
  congrFun (contract_addBlocks (fun i => M i (c i)) (fun i => N i (c i)) X Y) b

/-- The distinguished site's sign changes the second summand to its negative. -/
def diffMap {A' : I → Type*} (j : I) (M : Map C A B) (N : Map C A' B) :
    Map C (fun i => A i ⊕ A' i) B :=
  fun i c b => Sum.elim (M i c b) (fun a => (if i = j then -1 else 1) * N i c b a)

theorem eval_diffMap [Fintype I] {A' : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (A' i)]
    (j : I) (M : Map C A B) (N : Map C A' B) (c : ∀ i, C i)
    (X : (∀ i, A i) → ℂ) (Y : (∀ i, A' i) → ℂ) (b : ∀ i, B i) :
    eval (diffMap j M N) c (sumCoeff X Y) b = eval M c X b - eval N c Y b :=
  contract_subBlocks j (fun i => M i (c i)) (fun i => N i (c i)) X Y b

/-- Fixed controls give an ordinary restriction of the input tensor. -/
theorem restricts_eval [Fintype I] {R Q : Raw I ℂ} (M : Map C R.Leg Q.Leg)
    (c : ∀ i, C i) (h : ∀ b, eval M c R.coeff b = Q.coeff b) : Q.Restricts R :=
  ⟨fun i => M i (c i), fun b => (h b).symm⟩

end
end Control
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Basic
section

/-! # Sunflowers in set families and in word families -/

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {ι I α β : Type*}

/-- Every entry of the tuple has the same value. This includes the empty tuple. -/
def IsConstant (f : ι → β) : Prop :=
  ∀ i j, f i = f j

/-- One coordinate of a sunflower has either a common symbol or pairwise distinct symbols. -/
def Admissible (f : ι → β) : Prop :=
  IsConstant f ∨ Function.Injective f

/-- Each coordinate of the tuple of words is admissible. -/
def WordAdmissible (w : ι → I → β) : Prop :=
  ∀ c, Admissible (fun i => w i c)

/-- Every admissible ordered tuple of words in the family repeats one word. -/
def WordFree (r : ℕ) (W : Finset (I → β)) : Prop :=
  ∀ w : Fin r → I → β, (∀ i, w i ∈ W) → WordAdmissible w → IsConstant w

theorem WordAdmissible.isConstant_of_repeat {w : ι → I → β} (h : WordAdmissible w)
    {i j : ι} (hne : i ≠ j) (hw : w i = w j) : IsConstant w := by
  intro a b
  funext c
  rcases h c with hc | hc
  · exact hc a b
  · exact (hne (hc (congrFun hw c))).elim

theorem WordAdmissible.injective_of_not_isConstant {w : ι → I → β}
    (h : WordAdmissible w) (hn : ¬ IsConstant w) : Function.Injective w := by
  intro i j heq
  by_contra hne
  exact hn (h.isConstant_of_repeat hne heq)

/-- A family contains a subfamily of size `r` whose distinct members intersect in one
fixed core. The core can be empty. -/
def HasSunflower [DecidableEq α] (r : ℕ) (F : Finset (Finset α)) : Prop :=
  ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K

theorem hasSunflower_of_indexed [DecidableEq α] {r : ℕ} {F : Finset (Finset α)}
    {w : Fin r → Finset α} (hmem : ∀ i, w i ∈ F) (hinj : Function.Injective w)
    {K : Finset α} (hcore : ∀ i j, i ≠ j → w i ∩ w j = K) : HasSunflower r F := by
  let e : Fin r ↪ Finset α := ⟨w, hinj⟩
  refine ⟨Finset.univ.map e, ?_, by simp, K, ?_⟩
  · intro A hA
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hA
    exact hmem i
  · intro A hA B hB hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hB
    exact hcore i j (fun heq => hne (congrArg e heq))

theorem hasSunflower_iff_indexed [DecidableEq α] {r : ℕ} {F : Finset (Finset α)} :
    HasSunflower r F ↔ ∃ w : Fin r → Finset α, (∀ i, w i ∈ F) ∧
      Function.Injective w ∧ ∃ K : Finset α, ∀ i j, i ≠ j → w i ∩ w j = K := by
  constructor
  · rintro ⟨G, hG, hcard, K, hK⟩
    let e := (G.equivFinOfCardEq hcard).symm
    have hinj : Function.Injective (fun i => (e i).val) :=
      Subtype.val_injective.comp e.injective
    exact ⟨_, fun i => hG (e i).property, hinj, K, fun i j hij =>
      hK _ (e i).property _ (e j).property (fun heq => hij (hinj heq))⟩
  · rintro ⟨w, hmem, hinj, K, hcore⟩
    exact hasSunflower_of_indexed hmem hinj hcore

/-- A zero-uniform family of distinct finite sets has at most one member. -/
theorem zero_uniform_card_le_one {F : Finset (Finset α)} (hF : ∀ A ∈ F, A.card = 0) :
    F.card ≤ 1 :=
  Finset.card_le_one.mpr fun A hA B hB =>
    (Finset.card_eq_zero.mp (hF A hA)).trans (Finset.card_eq_zero.mp (hF B hB)).symm

end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Rules
section

/-! # The two-anchor implication system -/

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {G I α : Type*}

/-- Equality of the symbols on the two antecedents obliges the target to agree. -/
structure Rule (G : Type*) where
  left : G
  right : G
  target : G
  deriving DecidableEq, Fintype

def Rule.Holds (q : Rule G) (f : G → α) : Prop :=
  f q.left = f q.right → f q.left = f q.target

theorem Rule.not_holds_iff (q : Rule G) (f : G → α) :
    ¬ q.Holds f ↔ f q.left = f q.right ∧ f q.left ≠ f q.target := by
  classical
  simp [Rule.Holds]

/-- In the fourth rule each unordered pair of satellites occurs once. -/
inductive IsAnchorRule [LT G] (A B : G) : Rule G → Prop where
  | anchors (i : G) (hiA : i ≠ A) (hiB : i ≠ B) :
      IsAnchorRule A B ⟨A, B, i⟩
  | left (i : G) (hiA : i ≠ A) (hiB : i ≠ B) :
      IsAnchorRule A B ⟨A, i, B⟩
  | right (i : G) (hiA : i ≠ A) (hiB : i ≠ B) :
      IsAnchorRule A B ⟨B, i, A⟩
  | satellites (i j : G) (hiA : i ≠ A) (hiB : i ≠ B) (hjA : j ≠ A) (hjB : j ≠ B)
      (hij : i < j) : IsAnchorRule A B ⟨i, j, A⟩

theorem IsAnchorRule.distinct [Preorder G] {A B : G} {q : Rule G}
    (hq : IsAnchorRule A B q) (hAB : A ≠ B) :
    q.left ≠ q.right ∧ q.left ≠ q.target ∧ q.right ≠ q.target := by
  cases hq with
  | anchors i hiA hiB => exact ⟨hAB, hiA.symm, hiB.symm⟩
  | left i hiA hiB => exact ⟨hiA.symm, hAB, hiB⟩
  | right i hiA hiB => exact ⟨hiB.symm, hAB.symm, hiA⟩
  | satellites i j hiA _ hjA _ hij => exact ⟨ne_of_lt hij, hiA, hjA⟩

noncomputable def anchorRules [Fintype G] [LT G] (A B : G) : Finset (Rule G) := by
  classical
  exact Finset.univ.filter (IsAnchorRule A B)

@[simp] theorem mem_anchorRules [Fintype G] [LT G] {A B : G} {q : Rule G} :
    q ∈ anchorRules A B ↔ IsAnchorRule A B q := by
  classical
  simp [anchorRules]

/-- With groups numbered by `Fin (n+2)`, the four geometric constructions
suffice to discharge a property of every rule. -/
theorem anchorRules_fin_cases {n : ℕ} {P : Rule (Fin (n + 2)) → Prop}
    (ab : ∀ i : Fin n, P ⟨0, 1, i.succ.succ⟩)
    (az : ∀ i : Fin n, P ⟨0, i.succ.succ, 1⟩)
    (bz : ∀ i : Fin n, P ⟨1, i.succ.succ, 0⟩)
    (zz : ∀ i j : Fin n, i < j → P ⟨i.succ.succ, j.succ.succ, 0⟩)
    {q : Rule (Fin (n + 2))} (hq : q ∈ anchorRules 0 1) : P q := by
  have satellite (i : Fin (n + 2)) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
      ∃ j : Fin n, j.succ.succ = i := by
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
    have hj : j ≠ 0 := fun h => hi1 (h ▸ Fin.succ_zero_eq_one)
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
    exact ⟨j', rfl⟩
  cases mem_anchorRules.mp hq with
  | anchors i hiA hiB =>
    obtain ⟨i, rfl⟩ := satellite i hiA hiB
    exact ab i
  | left i hiA hiB =>
    obtain ⟨i, rfl⟩ := satellite i hiA hiB
    exact az i
  | right i hiA hiB =>
    obtain ⟨i, rfl⟩ := satellite i hiA hiB
    exact bz i
  | satellites i j hiA hiB hjA hjB hij =>
    obtain ⟨i, rfl⟩ := satellite i hiA hiB
    obtain ⟨j, rfl⟩ := satellite j hjA hjB
    exact zz i j (by simpa using hij)

/-- For unequal anchor symbols, every remaining group has a symbol different from either
anchor, and the satellite-pair rules make these remaining symbols pairwise different. -/
theorem admissible_of_isAnchorRule [LinearOrder G] {A B : G} (f : G → α)
    (hr : ∀ q, IsAnchorRule A B q → q.Holds f) : Admissible f := by
  classical
  by_cases hab : f A = f B
  · left
    have hall (i : G) : f A = f i := by
      by_cases hiA : i = A
      · rw [hiA]
      by_cases hiB : i = B
      · simpa only [hiB] using hab
      exact hr _ (.anchors i hiA hiB) hab
    exact fun i j => (hall i).symm.trans (hall j)
  · right
    have left_ne {i : G} (hiA : i ≠ A) : f A ≠ f i := by
      by_cases hiB : i = B
      · simpa only [hiB] using hab
      exact fun h => hab (hr _ (.left i hiA hiB) h)
    have right_ne {i : G} (hiB : i ≠ B) : f B ≠ f i := by
      by_cases hiA : i = A
      · simpa only [hiA] using (Ne.symm hab)
      exact fun h => hab (hr _ (.right i hiA hiB) h).symm
    intro i j hij
    by_contra hne
    by_cases hiA : i = A
    · subst i
      exact left_ne (Ne.symm hne) hij
    by_cases hjA : j = A
    · subst j
      exact left_ne hne hij.symm
    by_cases hiB : i = B
    · subst i
      exact right_ne (Ne.symm hne) hij
    by_cases hjB : j = B
    · subst j
      exact right_ne hne hij.symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact left_ne hiA (hr _ (.satellites i j hiA hiB hjA hjB hlt) hij).symm
    · exact left_ne hjA (hr _ (.satellites j i hjA hjB hiA hiB hgt) hij.symm).symm

theorem admissible_of_anchorRules [Fintype G] [LinearOrder G] {A B : G} (_hAB : A ≠ B)
    (f : G → α) (h : ∀ q ∈ anchorRules A B, q.Holds f) : Admissible f :=
  admissible_of_isAnchorRule f fun q hq => h q (mem_anchorRules.mpr hq)

/-- A nonconstant assignment of words from a free family must violate some rule at some
coordinate. This gives the zero factor in the expansion of the controlled restriction. -/
theorem exists_violated_anchorRule {r : ℕ} {W : Finset (I → α)} (hfree : WordFree r W)
    {A B : Fin r} (hAB : A ≠ B) (w : Fin r → I → α) (hmem : ∀ i, w i ∈ W)
    (h : ¬ IsConstant w) :
    ∃ c q, q ∈ anchorRules A B ∧ ¬ q.Holds (fun i => w i c) := by
  classical
  by_contra hn
  apply h
  apply hfree w hmem
  intro c
  apply admissible_of_anchorRules hAB
  intro q hq
  by_contra hv
  exact hn ⟨c, q, hq, hv⟩

end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Comparison
section

/-! # Comparing a word family with the full diagonal

The input word indices agree inside each group of sites. Keeping these
indices while applying the local tests leaves exactly the full diagonal.
-/

noncomputable section
open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Comparison

variable {S G : Type*} [Fintype S]

/-- The sites labeled by one group. -/
def fiber (group : S → G) (j : G) : Finset S :=
  Finset.univ.filter fun s => group s = j

@[simp] theorem mem_fiber {group : S → G} {j : G} {s : S} :
    s ∈ fiber group j ↔ group s = j := by simp [fiber]

theorem fiber_nonempty {group : S → G} (h : Function.Surjective group) (j : G) :
    (fiber group j).Nonempty := by
  obtain ⟨s, hs⟩ := h j
  exact ⟨s, mem_fiber.mpr hs⟩

/-- Coefficient predicate for independent word indices on the selected groups. -/
def Compatible (group : S → G) (J : Finset G) {L : Type*} (x : S → L) : Prop :=
  ∀ s t, group s ∈ J → group s = group t → x s = x t

def groupTensor (group : S → G) (J : Finset G) (L : Type) [Fintype L] : Raw.{0} S ℂ :=
  ⟨fun _ => L, fun _ => inferInstance, fun x => if Compatible group J x then 1 else 0⟩

omit [Fintype S] in
theorem groupTensor_ne_zero (group : S → G) (J : Finset G)
    (L : Type) [Fintype L] [Nonempty L] : (groupTensor group J L).coeff ≠ 0 := by
  classical
  let l : L := Classical.choice inferInstance
  intro h
  have H := congrFun h (fun _ => l)
  change (if Compatible group J (fun _ => l) then (1 : ℂ) else 0) = 0 at H
  simp [Compatible] at H

theorem groupTensor_insert_restricts_mul [DecidableEq S] [DecidableEq G]
    (group : S → G) (hsur : Function.Surjective group) (j : G) (J : Finset G)
    (L : Type) [Fintype L] :
    (groupTensor group (insert j J) L).Restricts
      ((groupTensor group J L).mul (Raw.maskDiagonal ℂ (fiber group j) L)) := by
  classical
  obtain ⟨s₀, hs₀⟩ := fiber_nonempty hsur j
  apply Raw.restrict_by_read (fun s x => (x, fun _ => x))
  intro (x : S → L)
  change (if Compatible group (insert j J) x then (1 : ℂ) else 0) =
    (if Compatible group J x then 1 else 0) *
      (Raw.maskDiagonal ℂ (fiber group j) L).coeff (fun s _ => x s)
  rw [Raw.maskDiagonal_coeff_at (K := ℂ) (α := L) _ hs₀ (fun s _ => x s)]
  have hh : Compatible group (insert j J) x ↔ Compatible group J x ∧
      ∀ s, s ∈ fiber group j → x s = x s₀ := by
    constructor
    · intro H
      exact ⟨fun s t hs hst => H s t (Finset.mem_insert_of_mem hs) hst,
        fun s hs => H s s₀ (by simp [mem_fiber.mp hs])
          ((mem_fiber.mp hs).trans (mem_fiber.mp hs₀).symm)⟩
    · rintro ⟨H, Hj⟩ s t hs hst
      rcases Finset.mem_insert.mp hs with he | he
      · exact (Hj s (mem_fiber.mpr he)).trans (Hj t (mem_fiber.mpr (hst.symm.trans he))).symm
      · exact H s t he hst
  split_ifs <;> simp_all

theorem groupTensor_price_le [DecidableEq S] [Nonempty S] [DecidableEq G]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} S ℂ → _ → Prop))
    (group : S → G) (hsur : Function.Surjective group) (J : Finset G)
    (L : Type) [Fintype L] [Nonempty L] :
    rawLogPrice φ 1 (groupTensor group J L) ≤
      ∑ j ∈ J, rawLogPrice φ 1 (Raw.maskDiagonal ℂ (fiber group j) L) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    have h : (groupTensor group ∅ L).Restricts (Raw.one S ℂ) := by
      apply Raw.restrict_by_read (fun _ _ => PUnit.unit)
      intro x
      simp [groupTensor, Compatible, Raw.one]
    simpa [rawLogPrice, ofRaw_one, φ.property.2.1] using
      rawLogPrice_mono φ (by norm_num : (0 : ℝ) ≤ 1) h
  | @insert j J hj ih =>
    have h := rawLogPrice_mono φ (by norm_num : (0 : ℝ) ≤ 1)
      (groupTensor_insert_restricts_mul group hsur j J L)
    rw [rawLogPrice_mul φ 1 _ _ (groupTensor_ne_zero _ _ _)
      (Raw.maskDiagonal_ne_zero _ (fiber_nonempty hsur j) L)] at h
    rw [Finset.sum_insert hj, add_comm]
    exact h.trans (add_le_add_left ih _)


/-- A fixed resource and return tensor with a local matrix for every control value. -/
structure Device (S C : Type*) where
  R : Raw.{0} S ℂ
  Q : Raw.{0} S ℂ
  R_ne : R.coeff ≠ 0
  Q_ne : Q.coeff ≠ 0
  M : ∀ s, C → Q.Leg s → R.Leg s → ℂ

variable {C : Type*}

def Device.out (D : Device S C) (c : S → C) : (∀ s, D.Q.Leg s) → ℂ :=
  contract (fun s => D.M s (c s)) D.R.coeff

variable [Nonempty S]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} S ℂ → _ → Prop))

def Device.cost (D : Device S C) : ℝ := rawLogPrice φ 1 D.R - rawLogPrice φ 1 D.Q

omit [Fintype S] [Nonempty S] in
private theorem raw_mul_nonzero (X Y : Raw.{0} S ℂ)
    (hX : X.coeff ≠ 0) (hY : Y.coeff ≠ 0) : (X.mul Y).coeff ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hX
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hY
  exact Function.ne_iff.mpr ⟨fun i => (a i, b i), mul_ne_zero ha hb⟩

def Device.parallel (D E : Device S C) : Device S C where
  R := D.R.mul E.R
  Q := D.Q.mul E.Q
  R_ne := raw_mul_nonzero _ _ D.R_ne E.R_ne
  Q_ne := raw_mul_nonzero _ _ D.Q_ne E.Q_ne
  M s c b a := D.M s c b.1 a.1 * E.M s c b.2 a.2

omit [Nonempty S] in
theorem Device.out_parallel (D E : Device S C) (c : S → C)
    (b : ∀ s, D.Q.Leg s × E.Q.Leg s) :
    (D.parallel E).out c b = D.out c (fun s => (b s).1) * E.out c (fun s => (b s).2) :=
  contract_mul _ _ _ _ _

theorem Device.cost_parallel (D E : Device S C) :
    (D.parallel E).cost φ = D.cost φ + E.cost φ := by
  unfold Device.cost
  change rawLogPrice _ _ (D.R.mul E.R) - rawLogPrice _ _ (D.Q.mul E.Q) = _
  rw [rawLogPrice_mul _ _ _ _ D.R_ne E.R_ne, rawLogPrice_mul _ _ _ _ D.Q_ne E.Q_ne]
  ring

def Device.unit (S C : Type*) : Device S C where
  R := Raw.one S ℂ
  Q := Raw.one S ℂ
  R_ne := fun h => one_ne_zero (congrFun h (fun _ => PUnit.unit))
  Q_ne := fun h => one_ne_zero (congrFun h (fun _ => PUnit.unit))
  M _ _ _ _ := 1

omit [Nonempty S] in
theorem Device.out_unit (c : S → C) : (Device.unit S C).out c = (Raw.one S ℂ).coeff := by
  funext b
  change (∑ _ : S → PUnit, (1 : ℂ) * ∏ _ : S, (1 : ℂ)) = 1
  simp

/-- Parallel execution of the tests preserves the return tensor on all good
controls. A single failed test annihilates the entire output. -/
theorem parallel_tests {J : Type*} (ids : Finset J)
    (D : J → Device S C) (good : (S → C) → Prop) (bad : J → (S → C) → Prop)
    (hgood : ∀ j ∈ ids, ∀ c, good c → (D j).out c = (D j).Q.coeff)
    (hbad : ∀ j ∈ ids, ∀ c, bad j c → (D j).out c = 0) :
    ∃ T : Device S C, T.cost φ = ∑ j ∈ ids, (D j).cost φ ∧
      (∀ c, good c → T.out c = T.Q.coeff) ∧
      ∀ j ∈ ids, ∀ c, bad j c → T.out c = 0 := by
  classical
  induction ids using Finset.induction_on with
  | empty =>
    exact ⟨Device.unit S C, by simp [Device.cost, Device.unit],
      fun c _ => Device.out_unit c, by simp⟩
  | @insert j ids hj ih =>
    obtain ⟨T, hcost, hpres, hkill⟩ := ih
      (fun k hk => hgood k (Finset.mem_insert_of_mem hk))
      (fun k hk => hbad k (Finset.mem_insert_of_mem hk))
    refine ⟨(D j).parallel T, by rw [Device.cost_parallel, hcost, Finset.sum_insert hj], ?_, ?_⟩
    · intro c hc
      funext b
      rw [Device.out_parallel (D j) T c b, hgood j (Finset.mem_insert_self ..) c hc, hpres c hc]
      rfl
    · intro k hk c hc
      funext b
      rw [Device.out_parallel (D j) T c b]
      rcases Finset.mem_insert.mp hk with rfl | hk
      · rw [hbad k (Finset.mem_insert_self ..) c hc]
        simp
      · rw [hkill k hk c hc]
        simp

omit [Fintype S] in
private theorem diagonal_coeff (L : Type) [Fintype L] (x : S → L) :
    (Raw.diagonal S ℂ L).coeff x = if IsConstant x then 1 else 0 := by
  classical
  let s : S := Classical.choice inferInstance
  simp only [Raw.diagonal]
  rw [Finset.sum_eq_single (x s)]
  · have he : x = (fun _ => x s) ↔ IsConstant x :=
      ⟨fun h i j => (congrFun h i).trans (congrFun h j).symm, fun h => funext fun i => h i s⟩
    simp [he]
  · intro b _ hbs
    exact if_neg (fun h => (hbs (congrFun h s).symm).elim)
  · simp

/-- The retained word indices give an ordinary local restriction. A coefficient
of the input already vanishes if its indices disagree within a group. On all
remaining nonconstant indices at least one local test gives zero. -/
theorem diagonal_restricts_filtered [Fintype G] (group : S → G)
    {L : Type} [Fintype L] (D : Device S L)
    (hpres : ∀ c, IsConstant c → D.out c = D.Q.coeff)
    (hkill : ∀ c, Compatible group Finset.univ c → ¬ IsConstant c → D.out c = 0) :
    ((Raw.diagonal S ℂ L).mul D.Q).Restricts ((groupTensor group Finset.univ L).mul D.R) := by
  classical
  let N : Control.Map (fun _ : S => Unit × L) D.R.Leg D.Q.Leg := fun i p => D.M i p.2
  refine ⟨fun s => Control.retainMap N s (), ?_⟩
  intro (y : ∀ s, L × D.Q.Leg s)
  let c : S → L := fun s => (y s).1
  let b : ∀ s, D.Q.Leg s := fun s => (y s).2
  change (Raw.diagonal S ℂ L).coeff c * D.Q.coeff b =
    Control.eval (Control.retainMap N) (fun _ => ())
      ((groupTensor group Finset.univ L).mul D.R).coeff y
  rw [Control.eval_retainMap N (fun _ => ()) ((groupTensor group Finset.univ L).mul D.R).coeff y]
  change _ = ∑ a, ((if Compatible group Finset.univ c then (1 : ℂ) else 0) * D.R.coeff a) *
    ∏ s, D.M s (c s) (b s) (a s)
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  change _ = (if Compatible group Finset.univ c then (1 : ℂ) else 0) * D.out c b
  rw [diagonal_coeff]
  by_cases he : IsConstant c
  · have hm : Compatible group Finset.univ c := fun s t _ _ => he s t
    simp [he, hm, hpres c he]
  · by_cases hm : Compatible group Finset.univ c
    · simp [he, hm, hkill c hm he]
    · simp [he, hm]

/-- Monotonicity of the spectral point applied to the restriction, followed by
the log-price laws for word labels and independent resources. -/
theorem diagonal_price_bound [Fintype G] [DecidableEq S] [DecidableEq G]
    (group : S → G) (hsur : Function.Surjective group)
    {L : Type} [Fintype L] [Nonempty L] (D : Device S L)
    (hpres : ∀ c, IsConstant c → D.out c = D.Q.coeff)
    (hkill : ∀ c, Compatible group Finset.univ c → ¬ IsConstant c → D.out c = 0) :
    (1 - ∑ j, maskDiagonalPrice φ 1 (fiber group j)) * Real.logb 2 (Fintype.card L) ≤
      D.cost φ := by
  classical
  have h := rawLogPrice_mono φ (by norm_num : (0 : ℝ) ≤ 1)
    (diagonal_restricts_filtered group D hpres hkill)
  have dne : (Raw.diagonal S ℂ L).coeff ≠ 0 := by
    let l : L := Classical.choice inferInstance
    intro hz
    have H := congrFun hz (fun _ => l)
    change (Raw.diagonal S ℂ L).coeff (fun _ => l) = 0 at H
    rw [diagonal_coeff] at H
    simp [IsConstant] at H
  rw [rawLogPrice_mul φ 1 _ _ dne D.Q_ne, rawLogPrice_mul φ 1 _ _
    (groupTensor_ne_zero group Finset.univ L) D.R_ne] at h
  have hdf : rawLogPrice φ 1 (Raw.diagonal S ℂ L) = Real.logb 2 (Fintype.card L) := by
    have hv := map_natCast (normalizedSpectrum.toRingHom φ) (Fintype.card L)
    change φ.val (Fintype.card L : TensorClass.{0} S ℂ) = (Fintype.card L : NNReal) at hv
    simp [rawLogPrice, ofRaw_diagonal_eq_natCast, hv]
  rw [hdf] at h
  have hm := groupTensor_price_le φ group hsur Finset.univ L
  have price (j : G) : rawLogPrice φ 1 (Raw.maskDiagonal ℂ (fiber group j) L) =
      maskDiagonalPrice φ 1 (fiber group j) * Real.logb 2 (Fintype.card L) := by
    have hh := ofRaw_maskDiagonal_equiv (K := ℂ) (fiber group j) (fiber_nonempty hsur j)
      (Fintype.equivFin L)
    calc
      _ = rawLogPrice φ 1 (Raw.maskDiagonal ℂ (fiber group j) (Fin (Fintype.card L))) :=
        congrArg (fun x => (1 : ℝ) * Real.logb 2 (φ.val x : ℝ)) hh
      _ = _ := rawLogPrice_maskDiagonal φ 1 _ (fiber_nonempty hsur j) Fintype.card_pos
  simp_rw [price] at hm
  rw [← Finset.sum_mul] at hm
  unfold Device.cost
  linarith


/-- Read a specified function of the local word index as the control. -/
def Device.pre {B : Type*} (D : Device S C) (f : B → C) : Device S B where
  R := D.R
  Q := D.Q
  R_ne := D.R_ne
  Q_ne := D.Q_ne
  M s b := D.M s (f b)

/-- Proposition 2.1 for the two-anchor forcing rules. One fixed device for
each rule is used once at each coordinate. The index type for the diagonal
is small even when the coordinate alphabet lies in a higher universe. -/
theorem wordComparison [DecidableEq S] {r k : ℕ} {α : Type*}
    (group : S → Fin r) (hsur : Function.Surjective group)
    (A B : Fin r) (hAB : A ≠ B) (W : Finset (Fin k → α))
    (hW : W.Nonempty) (hfree : WordFree r W) (cost : Rule (Fin r) → ℝ)
    (tests : ∀ q ∈ anchorRules A B, ∃ D : Device S α, D.cost φ ≤ cost q ∧
      (∀ x, D.out (fun _ => x) = D.Q.coeff) ∧
      ∀ f : Fin r → α, ¬ q.Holds f → D.out (f ∘ group) = 0) :
    (1 - ∑ j, maskDiagonalPrice φ 1 (fiber group j)) * Real.logb 2 W.card ≤
      (k : ℝ) * ∑ q ∈ anchorRules A B, cost q := by
  classical
  let Q := ↥(anchorRules A B)
  let L := Fin W.card
  let : Nonempty L := Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hW)
  let e : L ≃ W := W.equivFin.symm
  let word (i : L) : Fin k → α := (e i).val
  have inj : Function.Injective word := Subtype.val_injective.comp e.injective
  have hw (i : L) : word i ∈ W := (e i).property
  choose D hcost hpres hkill using fun q : Q => tests q.val q.property
  let test (z : Fin k × Q) : Device S L := (D z.2).pre (fun a => word a z.1)
  let bad (z : Fin k × Q) (c : S → L) := ∃ v : Fin r → L,
      c = v ∘ group ∧ ¬ z.2.val.Holds (fun i => word (v i) z.1)
  have hg (z : Fin k × Q) (c : S → L) (hc : IsConstant c) :
      (test z).out c = (test z).Q.coeff := by
    let s₀ : S := Classical.choice inferInstance
    change (D z.2).out (fun s => word (c s) z.1) = (D z.2).Q.coeff
    have he : (fun s => word (c s) z.1) = (fun _ => word (c s₀) z.1) :=
      funext fun s => congrArg (fun x => word x z.1) (hc s s₀)
    rw [he, hpres]
  have hb (z : Fin k × Q) (c : S → L) (hc : bad z c) : (test z).out c = 0 := by
    obtain ⟨v, rfl, hv⟩ := hc
    exact hkill z.2 (fun i => word (v i) z.1) hv
  obtain ⟨T, hprice, hpass, hfail⟩ := parallel_tests φ Finset.univ test IsConstant bad
    (fun z _ => hg z) (fun z _ => hb z)
  have hd (c : S → L) (hm : Compatible group Finset.univ c) (hc : ¬ IsConstant c) :
      T.out c = 0 := by
    choose rep hrep using hsur
    let v : Fin r → L := c ∘ rep
    have he : c = v ∘ group := funext fun s =>
      hm s (rep (group s)) (Finset.mem_univ _) (hrep _).symm
    have hnc : ¬ IsConstant (fun i => word (v i)) := by
      intro hconstant
      apply hc
      intro s t
      rw [congrFun he s, congrFun he t]
      exact inj (hconstant (group s) (group t))
    obtain ⟨i, q, hq, hqv⟩ := exists_violated_anchorRule hfree hAB (fun g => word (v g))
      (fun g => hw (v g)) hnc
    exact hfail (i, ⟨q, hq⟩) (Finset.mem_univ _) c ⟨v, he, hqv⟩
  have hdiag := diagonal_price_bound φ group hsur T hpass hd
  rw [hprice] at hdiag
  have hcst : ∑ z : Fin k × Q, (test z).cost φ ≤ (k : ℝ) * ∑ q ∈ anchorRules A B, cost q := by
    calc
      _ ≤ ∑ z : Fin k × Q, cost z.2.val := Finset.sum_le_sum fun z _ => hcost z.2
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp [Q, Finset.sum_attach]
  exact (by simpa [L] using hdiag.trans hcst)

end Comparison
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Copy
section

/-! The single-target convex-hull copying construction. A shared binary string indexed
by the alphabet supplies a sign at each possible label. Deleting the control position
at each source leaves a shared string just one bit shorter. -/

noncomputable section
open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks
open OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Copy

abbrev Bits (n : ℕ) := Fin n → Bool

private def sign (b : Bool) : ℂ := if b then -1 else 1

private theorem sign_average {n : ℕ} (i j : Fin (n + 1)) (v : Bits n) :
    (∑ b : Bool, sign b / 2 * sign ((i.insertNth (α := fun _ ↦ Bool) b v) j)) =
      if i = j then 1 else 0 := by
  cases j using i.succAboveCases with
  | x => norm_num [Fintype.sum_bool, sign]
  | p j =>
    simp only [Fin.insertNth_apply_succAbove, Fin.ne_succAbove, ite_false, Fintype.sum_bool]
    cases v j <;> norm_num [sign]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Input and returned resource for copying one label to site `z` from the sources `P`. -/
abbrev input (P : Finset I) (z : I) (n : ℕ) : Raw.{0} I ℂ :=
  Raw.maskDiagonal ℂ (insert z P) (Bits (n + 1))

abbrev returned (P : Finset I) (n : ℕ) : Raw.{0} I ℂ :=
  Raw.maskDiagonal ℂ P (Bits n)

/-- Each local matrix reads its own control. At the target `z`, the control is the
desired output index of the copied vector, or the symbol to compare against. -/
def matrix (P : Finset I) (z s₀ : I) (n : ℕ) (s : I) (label : Fin (n + 1))
    (x : (returned P n).Leg s) (y : (input P z n).Leg s) : ℂ :=
  let t : Bits (n+1) := if h : s ∈ insert z P then y h else fun _ ↦ false
  (if (∀ h : s ∈ P, x h = label.removeNth t) then 1 else 0) *
    (if s = s₀ then sign (t label) / 2 else 1) *
    (if s = z then sign (t label) else 1)

private theorem basis_product {P : Finset I} {z s₀ : I} (h₀ : s₀ ∈ P)
    {n : ℕ} (control : I → Fin (n+1)) (i : Fin (n+1)) (hc : ∀ s ∈ P, control s = i)
    (x : ∀ s, (returned P n).Leg s) (t : Bits (n+1)) :
    (∏ s, matrix P z s₀ n s (control s) (x s) (fun _ ↦ t)) =
      (if x = (fun _ _ ↦ i.removeNth t) then 1 else 0) *
      (sign (t i) / 2) * sign (t (control z)) := by
  classical
  have hlocal (s : I) :
      matrix P z s₀ n s (control s) (x s) (fun _ ↦ t) =
        (if (∀ h : s ∈ P, x s h = i.removeNth t) then 1 else 0) *
        (if s = s₀ then sign (t i) / 2 else 1) *
        (if s = z then sign (t (control z)) else 1) := by
    by_cases h : s ∈ P
    · have hi := hc s h
      have h' : s ∈ insert z P := Finset.mem_insert_of_mem h
      by_cases hz : s = z
      · subst s; simp [matrix, hi, h']
      · simp [matrix, hi, h', hz]
    · have hne : s ≠ s₀ := fun he ↦ h (he ▸ h₀)
      by_cases hz : s = z
      · subst s; simp [matrix, h, hne]
      · simp [matrix, h, hne, hz]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_boole]
  have hh : (∀ s (h : s ∈ P), x s h = i.removeNth t) ↔ x = (fun _ _ ↦ i.removeNth t) :=
    ⟨fun H ↦ funext fun s ↦ funext fun h ↦ H s h, fun H ↦ by rw [H]; simp⟩
  simp [hh]

private theorem sum_delete {n : ℕ} (i j : Fin (n+1)) (u : Bits n → ℂ) :
    (∑ t : Bits (n+1), u (i.removeNth t) * (sign (t i) / 2) * sign (t j)) =
      (if i = j then 1 else 0) * ∑ v, u v := by
  classical
  let term (t : Bits (n+1)) := u (i.removeNth t) * (sign (t i) / 2) * sign (t j)
  let e := Fin.insertNthEquiv (fun _ : Fin (n+1) ↦ Bool) i
  calc
    _ = ∑ bv : Bool × Bits n, term (e bv) := (e.sum_comp term).symm
    _ = ∑ v : Bits n, ∑ b : Bool, term (e (b,v)) :=
      (Fintype.sum_prod_type _).trans Finset.sum_comm
    _ = ∑ v : Bits n, u v * (if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      calc
        _ = ∑ b : Bool, u v * (sign b / 2 * sign ((i.insertNth (α := fun _ ↦ Bool) b v) j)) := by
          apply Finset.sum_congr rfl
          intro b _
          change u (i.removeNth (i.insertNth (α := fun _ ↦ Bool) b v)) *
            (sign ((i.insertNth (α := fun _ ↦ Bool) b v) i) / 2) * _ = _
          simp only [Fin.removeNth_insertNth, Fin.insertNth_apply_same, mul_assoc]
          rfl
        _ = _ := by rw [← Finset.mul_sum, sign_average]
    _ = _ := (Finset.sum_mul _ _ _).symm.trans (mul_comm _ _)

private theorem deleted_sum {P : Finset I} {z s₀ : I} (h₀ : s₀ ∈ P) {n : ℕ}
    (control : I → Fin (n+1)) (i : Fin (n+1)) (hc : ∀ s ∈ P, control s = i)
    (x : ∀ s, (returned P n).Leg s) :
    (∑ t : Bits (n+1), ∏ s, matrix P z s₀ n s (control s) (x s) (fun _ ↦ t)) =
      (if i = control z then 1 else 0) * (returned P n).coeff x := by
  classical
  calc
    _ = ∑ t : Bits (n+1), (if x = (fun _ _ ↦ i.removeNth t) then 1 else 0) *
        (sign (t i) / 2) * sign (t (control z)) :=
      Finset.sum_congr rfl (fun t _ ↦ basis_product h₀ control i hc x t)
    _ = _ := by
      simp only [returned, Raw.maskDiagonal, Crossing.basisTensor]
      convert sum_delete i (control z)
        (fun v ↦ if x = (fun (s : I) (_ : s ∈ P) ↦ v) then 1 else 0) using 1
      all_goals congr 1
      apply Finset.sum_congr
      · ext t
        simp
      · intro t _
        split_ifs with h₁ h₂ h₂
        · rfl
        · exact (h₂ (h₁.trans (by funext s h; rfl))).elim
        · exact (h₁ (h₂.trans (by funext s h; rfl))).elim
        · rfl

/-- The coefficient identity for the controlled conversion. It gives a basis vector
at the target, tensored with the returned partial diagonal, on the common-source promise. -/
theorem matrix_apply {P : Finset I} {z s₀ : I} (h₀ : s₀ ∈ P) {n : ℕ}
    (control : I → Fin (n+1)) (i : Fin (n+1)) (hc : ∀ s ∈ P, control s = i)
    (x : ∀ s, (returned P n).Leg s) :
    contract (fun s ↦ matrix P z s₀ n s (control s)) (input P z n).coeff x =
      (if i = control z then 1 else 0) * (returned P n).coeff x := by
  classical
  exact (contract_maskDiagonal (K := ℂ) (B := fun s ↦ (returned P n).Leg s)
    (insert z P) (Bits (n+1)) (fun s ↦ matrix P z s₀ n s (control s)) x).trans
      (deleted_sum h₀ control i hc x)

/-- A basis label at the target site, padded with scalar factors elsewhere. -/
def labelAt (z : I) {n : ℕ} (i : Fin (n+1)) : Raw.{0} I ℂ :=
  ⟨MaskLeg {z} (Fin (n+1)), fun _ ↦ Fintype.ofFinite _,
    fun x ↦ if i = x z (Finset.mem_singleton_self z) then 1 else 0⟩

/-- The copying matrix emits the chosen label at the target. Unlike the test matrix,
its target row supplies the label being tested. -/
def copyMatrix (P : Finset I) (z s₀ : I) (n : ℕ) (s : I) (label : Fin (n+1))
    (x : (returned P n).Leg s × MaskLeg {z} (Fin (n+1)) s) (y : (input P z n).Leg s) : ℂ :=
  matrix P z s₀ n s (if h : s = z then x.2 (Finset.mem_singleton.mpr h) else label) x.1 y

/-- On the common-source promise the same local matrices for every `i` copy
the source label as an output basis vector and return the fixed resource. -/
theorem copyMatrix_apply {P : Finset I} {z s₀ : I} (h₀ : s₀ ∈ P) (hz : z ∉ P)
    {n : ℕ} (control : I → Fin (n+1)) (i : Fin (n+1)) (hc : ∀ s ∈ P, control s = i)
    (x : ∀ s, (returned P n).Leg s × MaskLeg {z} (Fin (n+1)) s) :
    contract (fun s ↦ copyMatrix P z s₀ n s (control s)) (input P z n).coeff x =
      ((returned P n).mul (labelAt z i)).coeff x := by
  let u (s : I) := if h : s = z then (x s).2 (Finset.mem_singleton.mpr h) else control s
  have hu (s : I) (hs : s ∈ P) : u s = i := by
    have hsz : s ≠ z := fun e ↦ hz (e ▸ hs)
    simp [u, hsz, hc s hs]
  calc
    _ = contract (fun s ↦ matrix P z s₀ n s (u s)) (input P z n).coeff
      (fun s ↦ (x s).1) := rfl
    _ = _ := by
      rw [matrix_apply h₀ u i hu]
      change (if i = u z then 1 else 0) * _ =
        _ * (if i = (x z).2 (Finset.mem_singleton_self z) then 1 else 0)
      rw [mul_comm]
      simp [u]

variable [Nonempty I]

private theorem price_bits (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (c : ℝ) {P : Finset I} (hP : P.Nonempty) (n : ℕ) :
    rawLogPrice φ c (Raw.maskDiagonal ℂ P (Fin n → Bool)) = maskDiagonalPrice φ c P * n := by
  classical
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  let e : (Fin n → Bool) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq hcard
  have hp : rawLogPrice φ c (Raw.maskDiagonal ℂ P (Fin n → Bool)) =
      rawLogPrice φ c (Raw.maskDiagonal ℂ P (Fin (2 ^ n))) :=
    congrArg (fun x ↦ c * Real.logb 2 (φ.val x : ℝ)) (ofRaw_maskDiagonal_equiv P hP e)
  rw [hp, rawLogPrice_maskDiagonal φ c P hP (by positivity)]
  simp [Real.logb_pow]

/-- When adjoining the target preserves the diagonal price, testing an alphabet
of any size costs exactly the price of one extra source bit. -/
theorem cost_eq {P : Finset I} {z : I}
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop)) (hP : P.Nonempty)
    (c : ℝ) (h : maskDiagonalPrice φ c (insert z P) = maskDiagonalPrice φ c P) (n : ℕ) :
    rawLogPrice φ c (input P z n) - rawLogPrice φ c (returned P n) = maskDiagonalPrice φ c P := by
  unfold input returned
  rw [price_bits φ c (Finset.insert_nonempty z P), price_bits φ c hP, h]
  push_cast
  ring

end Copy
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Placement.Sites
section

/-! Sites, groups, and fibers for the planar sunflower placement. -/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Placement

/-- Each anchor has an endpoint at each extreme height and one site at each satellite
height. Each satellite group consists of a single site. -/
abbrev Site (n : ℕ) := Fin (n + 2) ⊕ (Fin (n + 2) ⊕ Fin n)

variable {n : ℕ}

def a (j : Fin (n + 2)) : Site n := Sum.inl j
def b (j : Fin (n + 2)) : Site n := Sum.inr (Sum.inl j)
def z (i : Fin n) : Site n := Sum.inr (Sum.inr i)

/-- The index of the anchor site at the height of satellite `i`. -/
def interior (i : Fin n) : Fin (n + 2) := i.succ.castSucc

@[simp] theorem interior_val (i : Fin n) : (interior i).val = i.val + 1 := rfl

theorem interior_pos (i : Fin n) : 0 < interior i := by
  change 0 < i.val + 1
  omega

theorem interior_lt_last (i : Fin n) : interior i < Fin.last (n + 1) := by
  change i.val + 1 < n + 1
  omega

/-- Group 0 is the first anchor, group 1 the second, and group `i+2` a satellite. -/
def group : Site n → Fin (n + 2)
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr i) => i.succ.succ

@[simp] theorem group_a (j : Fin (n + 2)) : group (a j) = 0 := rfl
@[simp] theorem group_b (j : Fin (n + 2)) : group (b j) = 1 := rfl
@[simp] theorem group_z (i : Fin n) : group (z i) = i.succ.succ := rfl

private theorem zero_ne_one : (0 : Fin (n + 2)) ≠ 1 := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'

private theorem sat_ne_zero (i : Fin n) : i.succ.succ ≠ (0 : Fin (n + 2)) := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'

private theorem sat_ne_one (i : Fin n) : i.succ.succ ≠ (1 : Fin (n + 2)) := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'

def fiber (g : Fin (n + 2)) : Finset (Site n) := Finset.univ.filter (group · = g)

@[simp] theorem mem_fiber {s : Site n} {g : Fin (n + 2)} : s ∈ fiber g ↔ group s = g := by
  simp [fiber]

theorem fiber_zero : fiber (0 : Fin (n + 2)) = Finset.univ.image a := by
  ext s
  rcases s with j | (j | i)
  · exact iff_of_true (mem_fiber.mpr (group_a j)) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  · simp [group, a, zero_ne_one.symm]
  · simp [group, a]

theorem fiber_one : fiber (1 : Fin (n + 2)) = Finset.univ.image b := by
  ext s
  rcases s with j | (j | i)
  · simp [group, b]
  · exact iff_of_true (mem_fiber.mpr (group_b j)) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  · simp [group, b, sat_ne_one]

@[simp] theorem fiber_satellite (i : Fin n) : fiber i.succ.succ = {z i} := by
  ext s
  rcases s with j | (j | k)
  · simp [group, z, (sat_ne_zero i).symm]
  · simp [group, z, (sat_ne_one i).symm]
  · simp [group, z]

theorem fiber_nonempty (g : Fin (n + 2)) : (fiber g).Nonempty := by
  refine Fin.cases ?_ (fun g' => ?_) g
  · exact ⟨a 0, mem_fiber.mpr rfl⟩
  refine Fin.cases ?_ (fun i => ?_) g'
  · exact ⟨b 0, mem_fiber.mpr rfl⟩
  · exact ⟨z i, mem_fiber.mpr rfl⟩

theorem group_surjective : Function.Surjective (@group n) :=
  fun g => let ⟨s, hs⟩ := fiber_nonempty g; ⟨s, mem_fiber.mp hs⟩

/-- Every group other than the anchors is uniquely indexed by its satellite. -/
theorem exists_satellite_index {g : Fin (n + 2)} (h0 : g ≠ 0) (h1 : g ≠ 1) :
    ∃ i : Fin n, g = i.succ.succ := by
  revert h0 h1
  refine Fin.cases (by simp) (fun j => ?_) g
  refine Fin.cases (by simp) (fun i _ _ => ⟨i, rfl⟩) j

/-- Satellites are singletons, so only the two anchor terms contribute to any sum of
group prices that vanishes on singletons. -/
theorem sum_fibers_eq_add_of_zero_satellites {M : Type*} [AddCommMonoid M]
    (v : Finset (Site n) → M) (hz : ∀ i : Fin n, v {z i} = 0) :
    ∑ g : Fin (n + 2), v (fiber g) = v (fiber 0) + v (fiber 1) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [hz]

end Placement
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Placement.RuleSites
section

/-! # Source and target sites of an anchor rule -/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Placement

variable {n : ℕ} {q : Rule (Fin (n + 2))}

/-- The three groups of locally readable sites for one ordered rule. -/
structure RuleSites {n : ℕ} (q : Rule (Fin (n + 2))) where
  L : Finset (Site n)
  R : Finset (Site n)
  T : Finset (Site n)
  hL : L.Nonempty
  hR : R.Nonempty
  hT : T.Nonempty
  left_sub : L ⊆ fiber q.left
  right_sub : R ⊆ fiber q.right
  target_sub : T ⊆ fiber q.target

namespace RuleSites

variable (d : RuleSites q)

/-- An equality filter at positive gap or a width-preserving copy to one target. -/
def Works (w : Finset (Site n) → ℝ) : Prop :=
  0 < w (d.L ∪ d.R) + w d.T - w ((d.L ∪ d.R) ∪ d.T) ∨
    ∃ s, d.T = {s} ∧ w (insert s (d.L ∪ d.R)) = w (d.L ∪ d.R)

theorem disjoint (hlt : q.left ≠ q.target) (hrt : q.right ≠ q.target) :
    Disjoint (d.L ∪ d.R) d.T := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx ht
  have he := mem_fiber.mp (d.target_sub ht)
  rcases Finset.mem_union.mp hx with h | h
  · exact hlt ((mem_fiber.mp (d.left_sub h)).symm.trans he)
  · exact hrt ((mem_fiber.mp (d.right_sub h)).symm.trans he)

theorem antecedent_const {α : Type*} (f : Fin (n + 2) → α) (h : f q.left = f q.right) :
    ∀ s ∈ d.L ∪ d.R, f (group s) = f q.left := by
  intro s hs
  rcases Finset.mem_union.mp hs with hL | hR
  · rw [mem_fiber.mp (d.left_sub hL)]
  · rw [mem_fiber.mp (d.right_sub hR), h]

theorem target_const {α : Type*} (f : Fin (n + 2) → α) :
    ∀ s ∈ d.T, f (group s) = f q.target :=
  fun _ hs => congrArg f (mem_fiber.mp (d.target_sub hs))

theorem works_normalize {w v : Finset (Site n) → ℝ} {D : ℝ} (hD : 0 < D)
    (h : ∀ s : Finset (Site n), s.Nonempty → v s = w s / D)
    (hw : d.Works w) : d.Works v := by
  have hp := d.hL.mono (Finset.subset_union_left (s₂ := d.R))
  rcases hw with hg | ⟨s, hs, he⟩
  · left
    rw [h _ hp, h _ d.hT, h _ (hp.mono Finset.subset_union_left), ← add_div, ← sub_div]
    exact div_pos hg hD
  · right
    exact ⟨s, hs, by rw [h _ (Finset.insert_nonempty ..), he, h _ hp]⟩

end RuleSites

end Placement
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.Width
section

/-!
# Mean width of a finite Euclidean configuration

We use the Gaussian normalization of the manuscript. The first variation when a
site leaves the origin is an integral over the directions supported at the origin.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace Classical

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Support function of a finite nonempty set of sites. -/
def support (S : Finset E) (hS : S.Nonempty) (u : E) : ℝ :=
  S.sup' hS (fun x ↦ ⟪u, x⟫)

theorem support_insert (S : Finset E) (hS : S.Nonempty) (v u : E) :
    support (insert v S) (Finset.insert_nonempty v S) u =
      max ⟪u, v⟫ (support S hS u) :=
  Finset.sup'_insert hS _

theorem support_smul (S : Finset E) (hS : S.Nonempty) (u : E) {a : ℝ} (ha : 0 ≤ a) :
    support (S.image (a • ·)) (hS.image _) u = a * support S hS u := by
  unfold support
  rw [Finset.sup'_image]
  simpa only [Function.comp_apply, real_inner_smul_right] using
    (Finset.apply_sup'_eq_sup'_comp hS (a * ·)
      (fun b c ↦ mul_max_of_nonneg b c ha) (f := fun x ↦ ⟪u, x⟫)).symm

theorem support_nonneg_of_zero_mem {S : Finset E} (h0 : 0 ∈ S) (u : E) :
    0 ≤ support S ⟨0, h0⟩ u := by
  simpa only [support, inner_zero_right] using S.le_sup' (fun x ↦ ⟪u, x⟫) h0

/-- Directions at which the origin supports the given configuration. -/
def normalConeAtZero (S : Finset E) : Set E :=
  {u | ∀ x ∈ S, ⟪u, x⟫ ≤ 0}

theorem mem_normalConeAtZero_iff {S : Finset E} (h0 : 0 ∈ S) (u : E) :
    u ∈ normalConeAtZero S ↔ support S ⟨0, h0⟩ u = 0 := by
  change (∀ x ∈ S, ⟪u, x⟫ ≤ 0) ↔ _
  rw [← Finset.sup'_le_iff ⟨0, h0⟩ (fun x ↦ ⟪u, x⟫)]
  exact ⟨(le_antisymm · (support_nonneg_of_zero_mem h0 u)), Eq.le⟩

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
theorem measurableSet_normalConeAtZero (S : Finset E) : MeasurableSet (normalConeAtZero S) := by
  have heq : normalConeAtZero S = ⋂ x ∈ (S : Set E), {u : E | ⟪u, x⟫ ≤ 0} := by
    ext
    simp [normalConeAtZero]
  rw [heq]
  exact .biInter S.countable_toSet fun x _ ↦
    measurableSet_le (f := fun u : E ↦ ⟪u, x⟫) (by fun_prop) measurable_const

/-- Gaussian mean width, normalized to give a segment its Euclidean length. -/
def meanWidth (S : Finset E) (hS : S.Nonempty) : ℝ :=
  Real.sqrt (2 * Real.pi) * ∫ u, support S hS u ∂stdGaussian E

theorem integrable_support (S : Finset E) (hS : S.Nonempty) :
    Integrable (support S hS) (stdGaussian E) := by
  have heq : support S hS = S.sup' hS (fun x u ↦ ⟪u, x⟫) := by
    funext u
    exact (Finset.sup'_apply hS (fun (x u : E) ↦ ⟪u, x⟫) u).symm
  rw [heq]
  refine Finset.sup'_induction hS _ (p := fun f : E → ℝ ↦ Integrable f (stdGaussian E))
    (fun _ hf _ hg ↦ hf.sup hg) (fun x _ ↦ ?_)
  exact (IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const x

omit [BorelSpace E] in
theorem meanWidth_smul (S : Finset E) (hS : S.Nonempty) {a : ℝ} (ha : 0 ≤ a) :
    meanWidth (S.image (a • ·)) (hS.image _) = a * meanWidth S hS := by
  simp only [meanWidth, support_smul S hS _ ha, integral_const_mul, ← mul_assoc]
  rw [mul_comm (Real.sqrt _)]

/-- The exact width increment upon adjoining a site to a dilation. -/
theorem meanWidth_insert_smul_sub (S : Finset E) (hS : S.Nonempty) (v : E)
    {a : ℝ} (ha : 0 ≤ a) :
    meanWidth (insert v (S.image (a • ·))) (Finset.insert_nonempty _ _) -
      meanWidth (S.image (a • ·)) (hS.image _) =
    Real.sqrt (2 * Real.pi) *
      ∫ u, max (⟪u, v⟫ - a * support S hS u) 0 ∂stdGaussian E := by
  unfold meanWidth
  rw [← mul_sub, ← integral_sub (integrable_support _ _) (integrable_support _ _)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
  simp only [support_insert _ (hS.image _), support_smul S hS u ha]
  rcases le_total ⟪u, v⟫ (a * support S hS u) with h | h
  · simp [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]
  · simp [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]

private theorem tendsto_max_sub_mul (b : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun a : ℝ ↦ max (b - a * s) 0) atTop
      (𝓝 (if s = 0 then max b 0 else 0)) := by
  by_cases h : s = 0
  · simp [h]
  · simp only [h, ite_false]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (b / s)] with a ha
    exact (max_eq_right (sub_nonpos.mpr ((div_le_iff₀ (lt_of_le_of_ne hs (Ne.symm h))).mp ha))).symm

/-- The large-dilation limit in the width-marginal formula, using the equivalent
Gaussian integral of the support function. -/
theorem tendsto_meanWidth_insert_smul_sub {S : Finset E} (h0 : 0 ∈ S) (v : E) :
    Tendsto (fun a : ℝ ↦
      meanWidth (insert v (S.image (a • ·))) (Finset.insert_nonempty _ _) -
        meanWidth (S.image (a • ·)) (Finset.Nonempty.image ⟨0, h0⟩ _)) atTop
      (𝓝 (Real.sqrt (2 * Real.pi) *
        ∫ u in normalConeAtZero S, max ⟪u, v⟫ 0 ∂stdGaussian E)) := by
  have hS : S.Nonempty := ⟨0, h0⟩
  have hv : Integrable (fun u : E ↦ ⟪u, v⟫) (stdGaussian E) :=
    (IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const v
  rw [← integral_indicator (measurableSet_normalConeAtZero S)]
  apply Filter.Tendsto.congr' _ (tendsto_const_nhds.mul
    (tendsto_integral_filter_of_dominated_convergence (fun u : E ↦ max ⟪u, v⟫ 0)
      (μ := stdGaussian E) (F := fun (a : ℝ) u ↦ max (⟪u, v⟫ - a * support S hS u) 0)
      ?_ ?_ (hv.sup (integrable_const 0)) ?_))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    exact (meanWidth_insert_smul_sub S hS v ha).symm
  · exact .of_forall fun a ↦
      ((hv.sub ((integrable_support S hS).const_mul a)).sup (integrable_const 0)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    refine ae_of_all _ fun u ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (sub_le_self _ (mul_nonneg ha (support_nonneg_of_zero_mem h0 u))) le_rfl
  · refine ae_of_all _ fun u ↦ ?_
    simpa only [Set.indicator_apply, mem_normalConeAtZero_iff h0] using
      tendsto_max_sub_mul ⟪u, v⟫ (support_nonneg_of_zero_mem h0 u)

/-- Right derivative at the instant when the added site separates from the origin. -/
theorem hasDerivWithinAt_meanWidth_insert {S : Finset E} (h0 : 0 ∈ S) (v : E) :
    HasDerivWithinAt
      (fun h : ℝ ↦ meanWidth (insert (h • v) S) (Finset.insert_nonempty _ _))
      (Real.sqrt (2 * Real.pi) *
        ∫ u in normalConeAtZero S, max ⟪u, v⟫ 0 ∂stdGaussian E) (Set.Ioi 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' Set.self_notMem_Ioi]
  apply ((tendsto_meanWidth_insert_smul_sub h0 v).comp tendsto_inv_nhdsGT_zero).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : (0 : ℝ) < h := hh
  have hS : S.Nonempty := ⟨0, h0⟩
  have hmove := meanWidth_smul (insert (h • v) S) (Finset.insert_nonempty _ _)
    (inv_nonneg.mpr hp.le)
  simp only [Finset.image_insert, inv_smul_smul₀ hp.ne'] at hmove
  simp only [Function.comp_apply, slope_def_field, zero_smul, Finset.insert_eq_of_mem h0,
    sub_zero, hmove, meanWidth_smul S hS (inv_nonneg.mpr hp.le)]
  ring

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.MinkowskiSupport
section

/-! # Support functions of Minkowski sums and continuity of Gaussian mean width -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Metric Filter
open scoped RealInnerProductSpace Pointwise Classical

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Support functions add under Minkowski addition of finite configurations. -/
theorem support_add (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) (u : E) :
    support (S + T) (hS.add hT) u = support S hS u + support T hT u := by
  unfold support
  apply le_antisymm
  · apply Finset.sup'_le
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    rw [inner_add_right]
    exact add_le_add (S.le_sup' (fun v ↦ ⟪u, v⟫) hx) (T.le_sup' (fun v ↦ ⟪u, v⟫) hy)
  · obtain ⟨x, hx, ex⟩ := Finset.exists_mem_eq_sup' hS (fun v ↦ ⟪u, v⟫)
    obtain ⟨y, hy, ey⟩ := Finset.exists_mem_eq_sup' hT (fun v ↦ ⟪u, v⟫)
    rw [ex, ey, ← inner_add_right]
    exact (S + T).le_sup' (fun v ↦ ⟪u, v⟫) (Finset.add_mem_add hx hy)

/-- Support function restricted to the unit sphere, with its uniform topology. -/
def sphereSupport (S : Finset E) (hS : S.Nonempty) : C(sphere (0 : E) 1, ℝ) where
  toFun u := support S hS u
  continuous_toFun := Continuous.finset_sup'_apply hS (fun _ _ ↦
    continuous_subtype_val.inner continuous_const)

/-- The continuous functions generating the triangle approximation space. -/
def triangleSupports (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Set C(sphere (0 : E) 1, ℝ) :=
  {f | ∃ a b c : E, f = sphereSupport {a, b, c} (Finset.insert_nonempty _ _)}

theorem sphereSupport_add (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) :
    sphereSupport (S + T) (hS.add hT) = sphereSupport S hS + sphereSupport T hT := by
  ext u
  exact support_add S T hS hT u

theorem sphereSupport_zero : sphereSupport ({0} : Finset E) (Finset.singleton_nonempty _) = 0 := by
  ext u
  simp [sphereSupport, support]

theorem support_smul_direction (S : Finset E) (hS : S.Nonempty) (u : E) {a : ℝ} (ha : 0 ≤ a) :
    support S hS (a • u) = a * support S hS u := by
  unfold support
  simpa only [real_inner_smul_left, Function.comp_def] using
    (Finset.apply_sup'_eq_sup'_comp hS (a * ·)
      (fun b c ↦ mul_max_of_nonneg b c ha) (f := fun x ↦ ⟪u, x⟫)).symm

/-- Adjoining sites in the convex hull preserves the support function. -/
theorem support_union_of_subset_convexHull {S T : Finset E} (hS : S.Nonempty)
    (hT : (T : Set E) ⊆ convexHull ℝ (S : Set E)) (u : E) :
    support (S ∪ T) (hS.mono Finset.subset_union_left) u = support S hS u := by
  have hc : Convex ℝ {v : E | ⟪u, v⟫ ≤ support S hS u} :=
    convex_halfSpace_le (innerSL ℝ u).toLinearMap.isLinear _
  have hbound : (S : Set E) ⊆ {v : E | ⟪u, v⟫ ≤ support S hS u} :=
    fun _ hx ↦ Finset.le_sup' (fun w : E ↦ ⟪u, w⟫) hx
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hbound h
    · exact convexHull_min hbound hc (hT h)
  · apply Finset.sup'_le
    intro x hx
    exact Finset.le_sup' _ (Finset.mem_union_left T hx)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
/-- Adjoining finitely many points in the convex hull preserves mean width. -/
theorem meanWidth_union_of_subset_convexHull {S T : Finset E} (hS : S.Nonempty)
    (hT : (T : Set E) ⊆ convexHull ℝ (S : Set E)) :
    meanWidth (S ∪ T) (hS.mono Finset.subset_union_left) = meanWidth S hS := by
  simp only [meanWidth, funext (support_union_of_subset_convexHull hS hT)]

theorem meanWidth_add (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) :
    meanWidth (S + T) (hS.add hT) = meanWidth S hS + meanWidth T hT := by
  simp only [meanWidth, support_add S T hS hT, integral_add (integrable_support S hS) (integrable_support T hT),
    mul_add]

/-- Uniform error on unit directions bounds the error in Gaussian mean width. -/
theorem abs_meanWidth_sub_le (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) {ε : ℝ}
    (hclose : ∀ u ∈ sphere (0 : E) 1, |support S hS u - support T hT u| ≤ ε) :
    |meanWidth S hS - meanWidth T hT| ≤
      (Real.sqrt (2 * Real.pi) * ∫ u : E, ‖u‖ ∂stdGaussian E) * ε := by
  have pointwise (u : E) : |support S hS u - support T hT u| ≤ ε * ‖u‖ := by
    by_cases hu : u = 0
    · simp [hu, support]
    let w := NormedSpace.normalize u
    have hw : w ∈ sphere (0 : E) 1 := by simp [w, NormedSpace.norm_normalize hu]
    have heq : ‖u‖ • w = u := NormedSpace.norm_smul_normalize u
    calc
      _ = ‖u‖ * |support S hS w - support T hT w| := by
        conv_lhs => rw [← heq]
        rw [support_smul_direction _ _ _ (norm_nonneg u), support_smul_direction _ _ _ (norm_nonneg u),
          ← mul_sub, abs_mul, abs_norm]
      _ ≤ ε * ‖u‖ := (mul_le_mul_of_nonneg_left (hclose w hw) (norm_nonneg u)).trans_eq (mul_comm _ _)
  have integralBound := norm_integral_le_of_norm_le
    (f := fun u ↦ support S hS u - support T hT u)
    ((IsGaussian.integrable_fun_id (μ := stdGaussian E)).norm.const_mul ε)
    (Eventually.of_forall pointwise)
  simp only [Real.norm_eq_abs, integral_const_mul] at integralBound
  rw [meanWidth, meanWidth, ← mul_sub, ← integral_sub (integrable_support S hS) (integrable_support T hT),
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left integralBound (Real.sqrt_nonneg _)).trans_eq (by ring)

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.GaussianAbsolute
section

/-! # Absolute first moment of the standard Gaussian -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory Real Set

section

/-- The Gaussian normalization used for the mean width gives a segment of length two
when its endpoints are the two unit vectors on the real line. -/
theorem normalized_integral_abs_gaussianReal :
    √(2 * π) * (∫ x : ℝ, |x| ∂(gaussianReal 0 1)) = 2 := by
  have hpos : (∫ x : ℝ in Ioi 0, x * exp (-(1 / 2) * x ^ 2)) = 1 := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [Real.Gamma_one] at h
    simpa only [neg_mul] using h
  have hfull : (∫ x : ℝ, |x| * exp (-(1 / 2) * x ^ 2)) = 2 := by
    have h := integral_comp_abs (f := fun x : ℝ ↦ x * exp (-(1 / 2) * x ^ 2))
    change (∫ x : ℝ, |x| * exp (-(1 / 2) * |x| ^ 2)) =
      2 * ∫ x : ℝ in Ioi 0, x * exp (-(1 / 2) * x ^ 2) at h
    simpa only [sq_abs, hpos, mul_one] using h
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_const_mul]
  convert hfull using 1
  congr 1
  ext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, mul_comm]
  congr 2
  ring

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.TriangleWidth
section

/-! # Gaussian mean width of segments and triangles -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem normalized_integral_abs_inner (x : E) :
    Real.sqrt (2 * Real.pi) * ∫ u, |⟪u, x⟫| ∂(stdGaussian E) = 2 * ‖x‖ := by
  let L := innerSL ℝ x
  have hmap : (stdGaussian E).map L = (gaussianReal 0 1).map (‖x‖ * ·) := by
    rw [IsGaussian.map_eq_gaussianReal, gaussianReal_map_const_mul,
      integral_strongDual_stdGaussian, variance_dual_stdGaussian]
    simp [L, Real.toNNReal_of_nonneg (sq_nonneg ‖x‖)]
  have hi : (∫ u, |⟪u, x⟫| ∂(stdGaussian E)) =
      ‖x‖ * ∫ t : ℝ, |t| ∂(gaussianReal 0 1) := by
    calc
      _ = ∫ t : ℝ, |t| ∂((stdGaussian E).map L) := by
        rw [integral_map L.continuous.aemeasurable (by fun_prop)]
        simp only [L, innerSL_apply_apply, real_inner_comm x]
      _ = ∫ t : ℝ, |‖x‖ * t| ∂(gaussianReal 0 1) := by
        rw [hmap, integral_map (by fun_prop) (by fun_prop)]
      _ = _ := by simp [abs_mul, integral_const_mul]
  rw [hi, mul_left_comm, normalized_integral_abs_gaussianReal, mul_comm]

private theorem twice_range_of_three (a b c : ℝ) :
    2 * (max a (max b c) + max (-a) (max (-b) (-c))) =
      |a - b| + |b - c| + |c - a| := by
  grind [abs_eq_max_neg]

private theorem integral_precomp_neg (f : E → ℝ) (hf : AEStronglyMeasurable f (stdGaussian E)) :
    (∫ u, f (-u) ∂(stdGaussian E)) = ∫ u, f u ∂(stdGaussian E) := by
  let e : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have he := stdGaussian_map e
  calc
    _ = ∫ u, f u ∂((stdGaussian E).map e) :=
      (integral_map e.continuous.aemeasurable (by simpa only [he] using hf)).symm
    _ = _ := by rw [he]

/-- The Gaussian mean width of three vertices equals their half-perimeter, allowing
repeated or collinear vertices. -/
theorem meanWidth_triangle [DecidableEq E] (a b c : E) :
    meanWidth {a, b, c} (Finset.insert_nonempty _ _) =
      (dist a b + dist b c + dist c a) / 2 := by
  let f (u : E) := max ⟪u, a⟫ (max ⟪u, b⟫ ⟪u, c⟫)
  have hproj (v : E) : Integrable (fun u : E ↦ ⟪u, v⟫) (stdGaussian E) :=
    (IsGaussian.integrable_fun_id (μ := stdGaussian E)).inner_const v
  have hf : Integrable f (stdGaussian E) := (hproj a).sup ((hproj b).sup (hproj c))
  have hf' : Integrable (fun u ↦ f (-u)) (stdGaussian E) := by
    simp only [f, inner_neg_left]
    exact (hproj a).neg.sup ((hproj b).neg.sup (hproj c).neg)
  have hwidth (u : E) :
      2 * (f u + f (-u)) = |⟪u, a - b⟫| + |⟪u, b - c⟫| + |⟪u, c - a⟫| := by
    simpa only [f, inner_neg_left, inner_sub_right] using
      twice_range_of_three ⟪u, a⟫ ⟪u, b⟫ ⟪u, c⟫
  have heq := congrArg (fun g : E → ℝ ↦ ∫ u, g u ∂(stdGaussian E)) (funext hwidth)
  rw [integral_const_mul, integral_add hf hf', integral_precomp_neg f hf.aestronglyMeasurable,
    integral_add ((hproj (a - b)).abs.fun_add (hproj (b - c)).abs) (hproj (c - a)).abs,
    integral_add (hproj (a - b)).abs (hproj (b - c)).abs] at heq
  have hs : support {a, b, c} (Finset.insert_nonempty _ _) = f := by
    funext u
    simp only [support, Finset.sup'_insert (Finset.insert_nonempty _ _),
      Finset.sup'_insert (Finset.singleton_nonempty _), Finset.sup'_singleton, f]
  unfold meanWidth
  rw [hs]
  simp only [dist_eq_norm]
  linarith only [congrArg (Real.sqrt (2 * Real.pi) * ·) heq,
    normalized_integral_abs_inner (a - b), normalized_integral_abs_inner (b - c),
    normalized_integral_abs_inner (c - a)]

/-- A segment has normalized mean width equal to its length. -/
theorem meanWidth_pair [DecidableEq E] (a b : E) :
    meanWidth {a, b} (Finset.insert_nonempty _ _) = dist a b := by
  simpa [dist_comm b a] using meanWidth_triangle a b b

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Planar
section

/-! The finite planar configurations used for the anchor and satellite rules. -/

noncomputable section
open scoped Classical Pointwise
open OAI.LinearAlgebra.SpectralBooks

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Planar

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def xy (x y : ℝ) : Plane := WithLp.toLp 2 ![x,y]

@[simp] theorem xy_zero (x y : ℝ) : xy x y 0 = x := rfl
@[simp] theorem xy_one (x y : ℝ) : xy x y 1 = y := rfl

@[simp] theorem xy_eq_iff {x y x' y' : ℝ} : xy x y = xy x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    exact ⟨congrArg (fun p : Plane ↦ p 0) h, congrArg (fun p : Plane ↦ p 1) h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem xy_add (x y u v : ℝ) : xy x y + xy u v = xy (x+u) (y+v) := by
  ext i
  fin_cases i <;> rfl

theorem dist_xy (x y u v : ℝ) :
    dist (xy x y) (xy u v) = Real.sqrt ((x-u)^2 + (y-v)^2) := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq]

@[simp] theorem dist_xy_horiz (x u y : ℝ) : dist (xy x y) (xy u y) = |x-u| := by
  simp [dist_xy, Real.sqrt_sq_eq_abs]

@[simp] theorem dist_xy_vert (x y v : ℝ) : dist (xy x y) (xy x v) = |y-v| := by
  simp [dist_xy, Real.sqrt_sq_eq_abs]

def rectangle (a b c d : ℝ) : Finset Plane := {xy a c, xy a d, xy b c, xy b d}

theorem rectangle_nonempty (a b c d : ℝ) : (rectangle a b c d).Nonempty :=
  Finset.insert_nonempty _ _

theorem meanWidth_congr {S T : Finset Plane} (h : S = T) (hS : S.Nonempty) (hT : T.Nonempty) :
    meanWidth S hS = meanWidth T hT := by subst T; rfl

theorem meanWidth_rectangle (a b c d : ℝ) :
    meanWidth (rectangle a b c d) (rectangle_nonempty ..) = |a-b| + |c-d| := by
  let : DecidableEq Plane := Classical.decEq _
  let H : Finset Plane := {xy a 0,xy b 0}
  let V : Finset Plane := {xy 0 c,xy 0 d}
  have he : H + V = rectangle a b c d := by
    ext z
    simp only [H,V,rectangle,Finset.mem_add,Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨x, (rfl|rfl), y, (rfl|rfl), rfl⟩ <;> simp [xy_add]
    · rintro (rfl|rfl|rfl|rfl)
      · exact ⟨_,Or.inl rfl,_,Or.inl rfl, by simp [xy_add]⟩
      · exact ⟨_,Or.inl rfl,_,Or.inr rfl, by simp [xy_add]⟩
      · exact ⟨_,Or.inr rfl,_,Or.inl rfl, by simp [xy_add]⟩
      · exact ⟨_,Or.inr rfl,_,Or.inr rfl, by simp [xy_add]⟩
  have h := meanWidth_add H V (Finset.insert_nonempty _ _) (Finset.insert_nonempty _ _)
  have hH : H.Nonempty := Finset.insert_nonempty _ _
  have hV : V.Nonempty := Finset.insert_nonempty _ _
  refine (meanWidth_congr he.symm _ (hH.add hV)).trans ?_
  simpa only [H,V,meanWidth_pair,dist_xy_horiz,dist_xy_vert] using h

private theorem vertical_mem_of_convex {C : Set Plane} (hC : Convex ℝ C) {x a y b : ℝ}
    (ha : a ≤ y) (hb : y ≤ b) (h1 : xy x a ∈ C) (h2 : xy x b ∈ C) : xy x y ∈ C := by
  have hseg : y ∈ segment ℝ a b := by rw [segment_eq_Icc (ha.trans hb)]; exact ⟨ha,hb⟩
  obtain ⟨s,t,hs,ht,hst,hy⟩ := hseg
  have h := hC h1 h2 hs ht hst
  have he : s • xy x a + t • xy x b = xy x y := by
    ext i
    fin_cases i
    · change s*x+t*x = x
      rw [← add_mul,hst,one_mul]
    · exact hy
  rwa [he] at h

private theorem horizontal_mem_of_convex {C : Set Plane} (hC : Convex ℝ C) {a x b y : ℝ}
    (ha : a ≤ x) (hb : x ≤ b) (h1 : xy a y ∈ C) (h2 : xy b y ∈ C) : xy x y ∈ C := by
  have hseg : x ∈ segment ℝ a b := by rw [segment_eq_Icc (ha.trans hb)]; exact ⟨ha,hb⟩
  obtain ⟨s,t,hs,ht,hst,hx⟩ := hseg
  have h := hC h1 h2 hs ht hst
  have he : s • xy a y + t • xy b y = xy x y := by
    ext i
    fin_cases i
    · exact hx
    · change s*y+t*y = y
      rw [← add_mul,hst,one_mul]
  rwa [he] at h

theorem xy_mem_hull_vpair (x : ℝ) {a y b : ℝ} (ha : a ≤ y) (hb : y ≤ b) :
    xy x y ∈ convexHull ℝ (↑({xy x a, xy x b} : Finset Plane) : Set Plane) :=
  vertical_mem_of_convex (convex_convexHull ℝ _) ha hb
    (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))

theorem xy_mem_hull_hpair {a x b : ℝ} (y : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    xy x y ∈ convexHull ℝ (↑({xy a y, xy b y} : Finset Plane) : Set Plane) :=
  horizontal_mem_of_convex (convex_convexHull ℝ _) ha hb
    (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))

theorem xy_mem_hull_rectangle {a x b c y d : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (hc : c ≤ y) (hd : y ≤ d) :
    xy x y ∈ convexHull ℝ (rectangle a b c d : Set Plane) := by
  apply horizontal_mem_of_convex (convex_convexHull ℝ _) ha hb
  all_goals
    apply vertical_mem_of_convex (convex_convexHull ℝ _) hc hd <;>
      apply subset_convexHull ℝ _ <;> simp [rectangle]

private theorem vertical_offset_cost {y t h : ℝ} (hy : y ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hh : t ≤ |h|) :
    y + t^2/4 ≤ Real.sqrt (h^2 + y^2) := by
  apply Real.le_sqrt_of_sq_le
  have hth : t^2 ≤ h^2 := by simpa only [sq_abs] using (sq_le_sq₀ ht0 (abs_nonneg h)).2 hh
  have htt : t^2 ≤ 1 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hy),
    mul_nonneg (sq_nonneg t) (sub_nonneg.mpr htt)]

theorem meanWidth_triangle_vertical_lower {a z y t : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hz : t ≤ |a-z|) :
    1+t^2/4 ≤ meanWidth {xy a 0,xy a 1,xy z y} (Finset.insert_nonempty _ _) := by
  rw [meanWidth_triangle, dist_xy_vert, dist_xy, dist_comm (xy z y), dist_xy]
  have h₁ := vertical_offset_cost (h := a-z) (y := 1-y) (by linarith) ht0 ht1 hz
  have h₂ := vertical_offset_cost (h := a-z) hy1 ht0 ht1 hz
  simp only [zero_sub, neg_sq, abs_neg, abs_one]
  linarith

end Planar
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Placement
section

/-! # The planar anchor and satellite placement

The anchor lines are one unit tall and slightly more than one unit apart.
The satellites have evenly spaced heights.  The perturbation of the right
anchor is quadratic in the distance from the left anchor to the satellites. -/

noncomputable section
open scoped Classical
open OAI.LinearAlgebra.SpectralBooks OAI.Combinatorics.Sunflower.Planar

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Placement

variable {n : ℕ}

/-- Horizontal distance of the satellites from the left anchor. -/
def offset (n : ℕ) : ℝ := 1 / (4 * ((n : ℝ)+1))

/-- Distance between the two anchor lines. -/
def spanX (n : ℕ) : ℝ := 1 + (offset n)^2/8

def height (j : Fin (n+2)) : ℝ := (j.val : ℝ) / ((n : ℝ)+1)

@[simp] theorem height_zero : height (0 : Fin (n+2)) = 0 := by simp [height]

@[simp] theorem height_top : height (Fin.last (n+1)) = 1 := by
  simp [height, show (n : ℝ) + 1 ≠ 0 by positivity]

theorem height_nonneg (j : Fin (n+2)) : 0 ≤ height j := by unfold height; positivity

theorem height_le_one (j : Fin (n+2)) : height j ≤ 1 := by
  rw [height, div_le_one (by positivity)]
  exact_mod_cast Nat.le_of_lt_succ j.isLt

theorem height_injective : Function.Injective (@height n) := by
  intro i j h
  apply Fin.ext
  have h' := (div_left_inj' (by positivity : (n : ℝ)+1 ≠ 0)).mp h
  exact_mod_cast h'

theorem interior_injective : Function.Injective (@interior n) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [interior] using this

theorem offset_pos (n : ℕ) : 0 < offset n := by unfold offset; positivity

theorem offset_le_quarter (n : ℕ) : offset n ≤ 1/4 := by
  rw [offset, div_le_div_iff₀ (by positivity) (by norm_num)]
  have hn : (0:ℝ) ≤ n := by positivity
  linarith

theorem one_lt_spanX (n : ℕ) : 1 < spanX n := by
  have h := sq_pos_of_pos (offset_pos n)
  unfold spanX
  linarith

theorem offset_lt_spanX (n : ℕ) : offset n < spanX n := by
  linarith [offset_le_quarter n, one_lt_spanX n]

theorem row_spacing {i j : Fin n} (hij : i < j) :
    offset n < height (interior j) - height (interior i) := by
  have h : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
  simp only [offset, height, interior, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  have d : 0 < (n:ℝ)+1 := by positivity
  field_simp
  linarith

def position : Site n → Plane
  | .inl j => xy 0 (height j)
  | .inr (.inl j) => xy (spanX n) (height j)
  | .inr (.inr i) => xy (offset n) (height (interior i))

@[simp] theorem position_a (j : Fin (n+2)) : position (a j) = xy 0 (height j) := rfl
@[simp] theorem position_b (j : Fin (n+2)) : position (b j) = xy (spanX n) (height j) := rfl
@[simp] theorem position_z (i : Fin n) : position (z i) = xy (offset n) (height (interior i)) := rfl

theorem position_injective : Function.Injective (@position n) := by
  have hs : spanX n ≠ 0 := ne_of_gt (by linarith [one_lt_spanX n])
  have ht := (offset_pos n).ne'
  have hts := (offset_lt_spanX n).ne
  rintro (j|j|i) (k|k|l) h <;>
    simp only [position, xy_eq_iff] at h <;>
    first | exact congrArg _ (height_injective h.2)
          | exact congrArg (fun i ↦ Sum.inr (Sum.inr i)) (interior_injective (height_injective h.2))
          | exact congrArg (fun j ↦ Sum.inr (Sum.inl j)) (height_injective h.2)
          | exact (hs h.1).elim | exact (hs h.1.symm).elim
          | exact (ht h.1).elim | exact (ht h.1.symm).elim
          | exact (hts h.1).elim | exact (hts h.1.symm).elim

def embedding (n : ℕ) : Site n ↪ Plane := ⟨position, position_injective⟩

@[simp] theorem coe_embedding (n : ℕ) : ⇑(embedding n) = position := rfl

/-- The unnormalized semiperimeter of a group of sites. -/
def width (S : Finset (Site n)) : ℝ :=
  if h : S.Nonempty then meanWidth (S.map (embedding n)) h.map else 0

theorem width_eq (S : Finset (Site n)) (h : S.Nonempty) :
    width S = meanWidth (S.map (embedding n)) h.map := by simp [width, h]

private theorem width_of_hull {S : Finset (Site n)} {V : Finset Plane} (hV : V.Nonempty)
    (hVS : V ⊆ S.map (embedding n))
    (hh : (↑(S.map (embedding n)) : Set Plane) ⊆ convexHull ℝ (V : Set Plane)) :
    width S = meanWidth V hV := by
  have hs : S.Nonempty := Finset.map_nonempty.mp (hV.mono hVS)
  rw [width_eq _ hs]
  have h := meanWidth_union_of_subset_convexHull hV hh
  refine (meanWidth_congr ?_ _ _).trans h
  ext p
  simp only [Finset.mem_union]
  exact ⟨Or.inr, fun hp ↦ hp.elim (fun hv ↦ hVS hv) id⟩

def endsA (n : ℕ) : Finset (Site n) := {a 0, a (Fin.last (n+1))}
def endsB (n : ℕ) : Finset (Site n) := {b 0, b (Fin.last (n+1))}
def triA (i : Fin n) : Finset (Site n) := insert (z i) (endsA n)
def triB (i : Fin n) : Finset (Site n) := insert (z i) (endsB n)
def bracket (i : Fin n) : Finset (Site n) := {a (interior i), b (interior i)}
def satPair (i j : Fin n) : Finset (Site n) := {z i, z j}
def matchPair (i j : Fin n) : Finset (Site n) := {a (interior i), a (interior j)}

@[simp] theorem image_endsA (n : ℕ) : (endsA n).map (embedding n) = {xy 0 0, xy 0 1} := by
  simp [endsA]
@[simp] theorem image_endsB (n : ℕ) :
    (endsB n).map (embedding n) = {xy (spanX n) 0, xy (spanX n) 1} := by simp [endsB]

@[simp] theorem width_endsA (n : ℕ) : width (endsA n) = 1 := by
  rw [width_eq (endsA n) (Finset.insert_nonempty _ _)]
  simp [meanWidth_pair]
@[simp] theorem width_endsB (n : ℕ) : width (endsB n) = 1 := by
  rw [width_eq (endsB n) (Finset.insert_nonempty _ _)]
  simp [meanWidth_pair]

private theorem position_in_rect (s : Site n) :
    position s ∈ convexHull ℝ (rectangle 0 (spanX n) 0 1 : Set Plane) := by
  have h := (offset_lt_spanX n).le
  have h' := (offset_pos n).le
  rcases s with j | j | i <;> apply xy_mem_hull_rectangle <;>
    first | exact height_nonneg _ | exact height_le_one _ | linarith

private theorem rectangle_eq_ends (n : ℕ) :
    rectangle 0 (spanX n) 0 1 = ((endsA n ∪ endsB n).map (embedding n)) := by
  ext p
  simp only [rectangle, Finset.map_union, image_endsA, image_endsB, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union]
  tauto

theorem width_of_corners {S : Finset (Site n)} (h : endsA n ∪ endsB n ⊆ S) :
    width S = 1 + spanX n := by
  have hsub : rectangle 0 (spanX n) 0 1 ⊆ S.map (embedding n) := by
    rw [rectangle_eq_ends]
    exact Finset.map_subset_map.mpr h
  have hh : (↑(S.map (embedding n)) : Set Plane) ⊆
      convexHull ℝ (rectangle 0 (spanX n) 0 1 : Set Plane) := by
    intro p hp
    obtain ⟨s, -, rfl⟩ := Finset.mem_map.mp hp
    exact position_in_rect s
  rw [width_of_hull (rectangle_nonempty ..) hsub hh, meanWidth_rectangle]
  simp [abs_of_pos (by linarith [one_lt_spanX n] : 0 < spanX n), add_comm]

@[simp] theorem width_univ (n : ℕ) : width (Finset.univ : Finset (Site n)) = 1 + spanX n :=
  width_of_corners (Finset.subset_univ _)


private theorem width_fiber_of_anchor (u : Fin (n+2) → Site n) (x : ℝ)
    (hu : ∀ j, position (u j) = xy x (height j)) :
    width (Finset.univ.image u) = 1 := by
  have he (j : Fin (n+2)) : xy x (height j) ∈ (Finset.univ.image u).map (embedding n) :=
    Finset.mem_map.mpr ⟨u j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hu _⟩
  have hsub : {xy x 0,xy x 1} ⊆ (Finset.univ.image u).map (embedding n) := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa only [height_zero] using he 0
    · obtain rfl := Finset.mem_singleton.mp hp
      simpa only [height_top] using he (Fin.last (n+1))
  have hh : (↑((Finset.univ.image u).map (embedding n)) : Set Plane) ⊆
      convexHull ℝ (↑({xy x 0,xy x 1} : Finset Plane) : Set Plane) := by
    intro p hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hs
    change position (u j) ∈ _
    rw [hu]
    exact xy_mem_hull_vpair x (height_nonneg _) (height_le_one _)
  rw [width_of_hull (Finset.insert_nonempty _ _) hsub hh, meanWidth_pair]
  simp

@[simp] theorem width_fiber_zero (n : ℕ) : width (fiber (0 : Fin (n+2))) = 1 := by
  rw [fiber_zero]
  exact width_fiber_of_anchor a 0 position_a

@[simp] theorem width_fiber_one (n : ℕ) : width (fiber (1 : Fin (n+2))) = 1 := by
  rw [fiber_one]
  exact width_fiber_of_anchor b (spanX n) position_b

@[simp] theorem width_singleton (s : Site n) : width {s} = 0 := by
  rw [width_eq _ (Finset.singleton_nonempty _)]
  simpa using meanWidth_pair (position s) (position s)

theorem width_groups_sum (n : ℕ) : ∑ g : Fin (n+2), width (fiber g) = 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  norm_num

theorem deficit_pos (n : ℕ) :
    0 < width (Finset.univ : Finset (Site n)) - ∑ g : Fin (n+2), width (fiber g) := by
  rw [width_univ, width_groups_sum]
  linarith [one_lt_spanX n]

theorem bracket_copy (i : Fin n) :
    width (bracket i ∪ {z i}) = width (bracket i) := by
  let V := (bracket i).map (embedding n)
  have hb : (bracket i).Nonempty := Finset.insert_nonempty _ _
  have hV : V.Nonempty := hb.map
  have hV' : V =
      {xy 0 (height (interior i)), xy (spanX n) (height (interior i))} := by simp [V,bracket]
  have hh : (↑(({z i} : Finset _).map (embedding n)) : Set Plane) ⊆
      convexHull ℝ (V : Set Plane) := by
    intro p hp
    have hp' : p = position (z i) := by simpa using hp
    rw [hp', position_z, hV']
    exact xy_mem_hull_hpair _ (offset_pos n).le (offset_lt_spanX n).le
  have hh' := meanWidth_union_of_subset_convexHull hV hh
  rw [width_eq _ (hb.mono Finset.subset_union_left), width_eq _ hb]
  refine (meanWidth_congr ?_ _ _).trans hh'
  ext p
  simp [V]

private theorem triangle_bound (u : Fin (n+2) → Site n) (x : ℝ) (i : Fin n)
    (hu : ∀ j, position (u j) = xy x (height j)) (hx : offset n ≤ |x-offset n|) :
    1 + (offset n)^2/4 ≤ width {z i, u 0, u (Fin.last (n+1))} := by
  rw [width_eq _ (Finset.insert_nonempty _ _)]
  have h := meanWidth_triangle_vertical_lower (a := x) (z := offset n)
    (height_nonneg (interior i)) (height_le_one _)
    (offset_pos n).le (by linarith [offset_le_quarter n]) hx
  refine h.trans_eq (meanWidth_congr ?_ _ _)
  ext p
  simp only [Finset.map_insert,Finset.map_singleton,coe_embedding,hu,height_zero,height_top,
    position_z,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem gap_left (i : Fin n) :
    0 < width (triA i) + width (endsB n) - width (triA i ∪ endsB n) := by
  have hh : endsA n ∪ endsB n ⊆ triA i ∪ endsB n :=
    Finset.union_subset_union (Finset.subset_insert _ _) (Finset.Subset.refl _)
  rw [width_of_corners hh, width_endsB]
  have h := triangle_bound a 0 i position_a (by simpa using (le_abs_self (offset n)))
  change 1 + (offset n)^2/4 ≤ width (triA i) at h
  unfold spanX
  nlinarith [sq_pos_of_pos (offset_pos n)]

theorem gap_right (i : Fin n) :
    0 < width (triB i) + width (endsA n) - width (triB i ∪ endsA n) := by
  have hh : endsA n ∪ endsB n ⊆ triB i ∪ endsA n := by
    rw [Finset.union_comm]
    exact Finset.union_subset_union (Finset.subset_insert _ _) (Finset.Subset.refl _)
  rw [width_of_corners hh, width_endsA]
  have hx : offset n ≤ |spanX n - offset n| := by
    rw [abs_of_pos (sub_pos.mpr (offset_lt_spanX n))]
    linarith [one_lt_spanX n, offset_le_quarter n]
  have h := triangle_bound b (spanX n) i position_b hx
  change 1 + (offset n)^2/4 ≤ width (triB i) at h
  unfold spanX
  nlinarith [sq_pos_of_pos (offset_pos n)]

theorem gap_satellites {i j : Fin n} (hij : i < j) :
    0 < width (satPair i j) + width (matchPair i j) -
      width (satPair i j ∪ matchPair i j) := by
  have S : (satPair i j).Nonempty := Finset.insert_nonempty _ _
  have M : (matchPair i j).Nonempty := Finset.insert_nonempty _ _
  have hrect : (satPair i j ∪ matchPair i j).map (embedding n) =
      rectangle (offset n) 0 (height (interior i)) (height (interior j)) := by
    ext p
    simp only [satPair,matchPair,rectangle,Finset.map_union,Finset.map_insert,Finset.map_singleton,
      coe_embedding,position_z,position_a,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  rw [width_eq _ S, width_eq _ M, width_eq _ (S.mono Finset.subset_union_left)]
  have he := meanWidth_rectangle (offset n) 0 (height (interior i)) (height (interior j))
  rw [(meanWidth_congr hrect _ (rectangle_nonempty ..)).trans he]
  simp only [satPair,matchPair,Finset.map_insert,Finset.map_singleton,
    coe_embedding,position_z,position_a,meanWidth_pair,dist_xy_vert,
    sub_zero,abs_of_pos (offset_pos n)]
  rw [abs_of_neg (by linarith [row_spacing hij,offset_pos n] :
    height (interior i) - height (interior j) < 0)]
  linarith [row_spacing hij]

end Placement
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Placement.Rules
section

/-! The finite planar placement realizes the geometric condition for every anchor rule
and has a positive global comparison deficit, all in one complex spectral point. -/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Placement

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

variable {n : ℕ}

private theorem endsA_subset_fiber (n : ℕ) : endsA n ⊆ fiber 0 := by
  simp [endsA, Finset.insert_subset_iff]

private theorem endsB_subset_fiber (n : ℕ) : endsB n ⊆ fiber 1 := by
  simp [endsB, Finset.insert_subset_iff]

theorem exists_rule_sites (q : Rule (Fin (n + 2))) (hq : q ∈ anchorRules 0 1) :
    ∃ d : RuleSites q, d.Works width := by
  apply anchorRules_fin_cases (P := fun q => ∃ d : RuleSites q, d.Works width) _ _ _ _ hq
  · intro i
    refine ⟨⟨{a (interior i)}, {b (interior i)}, {z i}, by simp, by simp, by simp,
        by simp, by simp, by simp⟩, Or.inr ⟨z i, rfl, ?_⟩⟩
    change width (insert (z i) ({a (interior i)} ∪ {b (interior i)})) =
      width ({a (interior i)} ∪ {b (interior i)})
    rw [Finset.singleton_union]
    simpa only [bracket, Finset.union_singleton] using bracket_copy i
  · intro i
    refine ⟨⟨endsA n, {z i}, endsB n, by simp [endsA], by simp, by simp [endsB],
        endsA_subset_fiber n, by simp, endsB_subset_fiber n⟩, Or.inl ?_⟩
    simpa [triA, Finset.union_singleton] using gap_left i
  · intro i
    refine ⟨⟨endsB n, {z i}, endsA n, by simp [endsB], by simp, by simp [endsA],
        endsB_subset_fiber n, by simp, endsA_subset_fiber n⟩, Or.inl ?_⟩
    simpa [triB, Finset.union_singleton] using gap_right i
  · intro i j hij
    refine ⟨⟨{z i}, {z j}, matchPair i j, by simp, by simp, by simp [matchPair],
        by simp, by simp, by simp [matchPair, Finset.insert_subset_iff]⟩, Or.inl ?_⟩
    simpa [satPair] using gap_satellites hij

/-- A fixed complex point and placement for the `n+2` groups, chosen before the
alphabet or word length. -/
theorem priced_placement (n : ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Site n) ℂ → _ → Prop))
    (hD' : 0 < width (Finset.univ : Finset (Site n)))
    (price : ∀ (s : Finset (Site n)), s.Nonempty →
      maskDiagonalPrice φ 1 s = width s / width (Finset.univ : Finset (Site n))) :
    0 < 1 - ∑ g : Fin (n + 2), maskDiagonalPrice φ 1 (fiber g) ∧
      ∀ q ∈ anchorRules (0 : Fin (n + 2)) 1,
        ∃ d : RuleSites q, d.Works (maskDiagonalPrice φ 1) := by
  classical
  constructor
  · simp_rw [fun g => price (fiber g) (fiber_nonempty g)]
    rw [← Finset.sum_div, sub_pos, div_lt_one hD']
    exact sub_pos.mp (deficit_pos n)
  · intro q hq
    obtain ⟨d, hd⟩ := exists_rule_sites q hq
    exact ⟨d, d.works_normalize hD' price hd⟩

end Placement
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Binary
section

/-! # Pair names for the binary equality filter

For a nonzero direction, eliminate one pivot coordinate by adding a multiple of the
direction. Deleting this coordinate then names the coset of the two-element subgroup.
-/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Binary

abbrev Word (b : ℕ) := Fin b → ZMod 2
abbrev Direction (b : ℕ) := {p : Word b // p ≠ 0}

@[simp] theorem card_word (b : ℕ) : Fintype.card (Word b) = 2 ^ b := by
  simp [Word, ZMod.card]

@[simp] theorem card_direction (b : ℕ) : Fintype.card (Direction b) = 2 ^ b - 1 := by
  classical
  rw [show Fintype.card (Direction b) = _ from Fintype.card_subtype_compl (· = (0 : Word b))]
  simp

instance {b : ℕ} : Nonempty (Direction (b + 1)) :=
  ⟨⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0)⟩⟩

private theorem has_pivot {b : ℕ} (p : Direction b) : ∃ i, p.val i = 1 := by
  by_contra! h
  exact p.property (funext fun i =>
    (show ∀ a : ZMod 2, a ≠ 1 → a = 0 by decide) _ (h i))

noncomputable def pivot {b : ℕ} (p : Direction b) : Fin b :=
  Classical.choose (has_pivot p)

@[simp] theorem pivot_bit {b : ℕ} (p : Direction b) : p.val (pivot p) = 1 :=
  Classical.choose_spec (has_pivot p)

/-- The smaller alphabet names each unordered pair in direction `p`. -/
noncomputable def pairName {b : ℕ} (p : Direction (b + 1)) (x : Word (b + 1)) : Word b :=
  fun i => x ((pivot p).succAbove i) + x (pivot p) * p.val ((pivot p).succAbove i)

theorem pairName_eq_iff {b : ℕ} (p : Direction (b + 1)) (x y : Word (b + 1)) :
    pairName p x = pairName p y ↔ x = y ∨ p.val = x + y := by
  constructor
  · intro he
    have hn (i) : x i + x (pivot p) * p.val i = y i + y (pivot p) * p.val i := by
      rcases (pivot p).eq_self_or_eq_succAbove i with rfl | ⟨j, rfl⟩
      · rw [pivot_bit]
        exact (show ∀ a b : ZMod 2, a + a * 1 = b + b * 1 by decide) _ _
      · exact congrFun he j
    by_cases hs : x (pivot p) = y (pivot p)
    · exact Or.inl (funext fun i => add_right_cancel ((hs ▸ hn i) : _))
    · exact Or.inr (funext fun i =>
        (show ∀ a b c d e : ZMod 2, a ≠ b → c + a * e = d + b * e → e = c + d by decide)
          _ _ _ _ _ hs (hn i))
  · rintro (rfl | he)
    · rfl
    · have hp : 1 = x (pivot p) + y (pivot p) := (pivot_bit p).symm.trans (congrFun he _)
      funext i
      simp only [pairName, he, Pi.add_apply]
      exact (show ∀ a b c d : ZMod 2, 1 = a + b →
        c + a * (c + d) = d + b * (c + d) by decide) _ _ _ _ hp

@[simp] theorem word_add_self {b : ℕ} (x : Word b) : x + x = 0 :=
  funext fun i => (show ∀ a : ZMod 2, a + a = 0 by decide) (x i)

/-- Adding the same binary word twice recovers the other summand. -/
@[simp] theorem word_add_cancel_right {b : ℕ} (x y : Word b) : x + y + y = x := by
  rw [add_assoc, word_add_self, add_zero]

/-- The unique direction pairing two different words. -/
def difference {b : ℕ} (x y : Word b) (h : x ≠ y) : Direction b :=
  ⟨x + y, fun hz => h (funext fun i =>
    (show ∀ a b : ZMod 2, a + b = 0 → a = b by decide) _ _ (congrFun hz i))⟩

@[simp] theorem difference_val {b : ℕ} (x y : Word b) (h : x ≠ y) :
    (difference x y h).val = x + y := rfl

theorem pairName_eq_iff_direction {b : ℕ} (p : Direction (b + 1)) (x y : Word (b + 1))
    (h : x ≠ y) : pairName p x = pairName p y ↔ p = difference x y h := by
  rw [pairName_eq_iff, or_iff_right h, Subtype.ext_iff]
  rfl

/-- Summing any coefficient over the directions whose pair names match keeps all
directions on equal inputs and exactly the difference direction on unequal inputs. -/
theorem matchingSum {b : ℕ} {M : Type*} [AddCommMonoid M] (x y : Word (b + 1))
    (f : Direction (b + 1) → M) :
    (∑ p, if pairName p x = pairName p y then f p else 0) =
      if h : x = y then ∑ p, f p else f (difference x y h) := by
  classical
  by_cases h : x = y
  · simp [h]
  · simp [h, pairName_eq_iff_direction _ _ _ h]

end Binary
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.CorrectionSpec
section

/-! # Local maps for correcting the binary equality test -/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

noncomputable section

open Binary Control

variable {I : Type*} [Fintype I]

/-- The correction block emits the shared difference when the promised labels disagree. -/
def CorrectionMaps (P T : Finset I) (b : ℕ) (U V : Raw.{0} I ℂ) : Prop :=
  ∃ M : Map (fun _ : I => Word (b+1)) U.Leg
      (V.mul (Raw.maskDiagonal ℂ (P ∪ T) (Direction (b+1)))).Leg,
    ∀ x y (c : I → Word (b+1)), (∀ i ∈ P, c i = x) → (∀ i ∈ T, c i = y) →
      ∀ o, eval M c U.coeff o = V.coeff (fun i => (o i).1) *
        ∑ p : Direction (b+1), if p.val = x + y then
          (if (fun i => (o i).2) = (fun _ _ => p) then 1 else 0) else 0

end

end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Filter
section

/-! # One recursive step of the binary equality filter

The first input block preserves a shared direction and runs the smaller filter on the
pair names in that direction. The second block removes the direction left by a mismatch.
-/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

noncomputable section

open Binary Control

variable {I : Type*} [Fintype I]

/-- A promised equality test need only specify its values on controls constant on
each of its two designated sets of sites. -/
def EqualityMaps (P T : Finset I) (A : Type) (R Q : Raw.{0} I ℂ) : Prop :=
  ∃ M : Map (fun _ : I => A) R.Leg Q.Leg, ∀ x y (c : I → A),
    (∀ i ∈ P, c i = x) → (∀ i ∈ T, c i = y) → ∀ o,
      eval M c R.coeff o = if x = y then Q.coeff o else 0

private def readDir {K : Finset I} {b : ℕ} (i : I)
    (a : MaskLeg K (Direction (b+1)) i) : Direction (b+1) :=
  if h : i ∈ K then a h else Classical.choice inferInstance

private def matchMap (K : Finset I) {b : ℕ} {R Q : Raw.{0} I ℂ}
    (V : Raw.{0} I ℂ) (M : Map (fun _ : I => Word b) R.Leg Q.Leg) :
    let D := Raw.maskDiagonal ℂ K (Direction (b+1))
    Map (fun _ : I => Word (b+1)) (R.mul (V.mul D)).Leg (Q.mul (V.mul D)).Leg :=
  fun i c o a => M i (pairName (readDir i o.2.2) c) o.1 a.1 *
    (if a.2 = o.2 then 1 else 0)

private theorem matchMap_eval {P T : Finset I} {b : ℕ} {R Q : Raw.{0} I ℂ}
    (V : Raw.{0} I ℂ) (M : Map (fun _ : I => Word b) R.Leg Q.Leg)
    (hM : ∀ x y (c : I → Word b), (∀ i ∈ P, c i = x) → (∀ i ∈ T, c i = y) → ∀ o,
      eval M c R.coeff o = if x = y then Q.coeff o else 0)
    (x y : Word (b+1)) (c : I → Word (b+1))
    (hcP : ∀ i ∈ P, c i = x) (hcT : ∀ i ∈ T, c i = y) :
    let K := P ∪ T
    let D := Raw.maskDiagonal ℂ K (Direction (b+1))
    ∀ o : ∀ i, (Q.mul (V.mul D)).Leg i,
      eval (matchMap K V M) c (R.mul (V.mul D)).coeff o =
        Q.coeff (fun i => (o i).1) * V.coeff (fun i => (o i).2.1) *
        ∑ p : Direction (b+1), if pairName p x = pairName p y then
          (if (fun i => (o i).2.2) = (fun _ _ => p) then 1 else 0) else 0 := by
  classical
  intro K D o
  let dir (i : I) := readDir (K := K) i (o i).2.2
  let names (i : I) := pairName (dir i) (c i)
  let N := pre (fun i w => pairName (dir i) w) M
  have h :
      eval (matchMap K V M) c (R.mul (V.mul D)).coeff o =
        eval M names R.coeff (fun i => (o i).1) *
          (V.coeff (fun i => (o i).2.1) * D.coeff (fun i => (o i).2.2)) := by
    calc
      _ = eval (prodMap N idMap) c (R.mul (V.mul D)).coeff o := by
        apply eval_congr_at
        intros
        rfl
      _ = _ := by
        change eval (prodMap N idMap) c
          (fun a => R.coeff (fun i => (a i).1) * (V.mul D).coeff (fun i => (a i).2)) o = _
        erw [eval_prodMap N idMap c R.coeff (V.mul D).coeff o, eval_idMap]
        rfl
  rw [h]
  dsimp only [D, Raw.maskDiagonal, Crossing.basisTensor]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : (fun i => (o i).2.2) = (fun _ _ => p)
  · have hd (i) (hi : i ∈ K) : dir i = p := by
      simp [dir, readDir, hi, congrFun hp i]
    have hP (i) (hi : i ∈ P) : names i = pairName p x := by
      simp [names, hd i (Finset.mem_union_left T hi), hcP i hi]
    have hT (i) (hi : i ∈ T) : names i = pairName p y := by
      simp [names, hd i (Finset.mem_union_right P hi), hcT i hi]
    rw [hM _ _ names hP hT]
    by_cases hxy : pairName p x = pairName p y <;> simp [hp, hxy]
  · by_cases hn : pairName p x = pairName p y
    all_goals simp only [hn, ↓reduceIte]
    all_goals repeat' split
    all_goals first | contradiction | simp
    exact Or.inr (if_neg hp)

/-- Zero-bit labels are all equal, so the scalar identity is the starting filter. -/
theorem equalityMaps_one (P T : Finset I) :
    EqualityMaps P T (Word 0) (Raw.one I ℂ) (Raw.one I ℂ) := by
  refine ⟨idMap, fun x y c _ _ o => ?_⟩
  simp [Subsingleton.elim x y]

/-- A direct sum runs the smaller filter in each matching direction and
subtracts its unique erroneous output on unequal inputs. -/
theorem filter_step_maps (j : I) {P T : Finset I} {b : ℕ} {R Q U V : Raw.{0} I ℂ}
    (hM : EqualityMaps P T (Word b) R Q) (hC : CorrectionMaps P T b U V) :
    let D := Raw.maskDiagonal ℂ (P ∪ T) (Direction (b+1))
    EqualityMaps P T (Word (b+1)) ((R.mul (V.mul D)).add (Q.mul U)) (Q.mul (V.mul D)) := by
  classical
  intro D
  obtain ⟨M, hM⟩ := hM
  obtain ⟨C, hC⟩ := hC
  let L := matchMap (P ∪ T) V M
  let N := prodMap (idMap (A := Q.Leg)) C
  refine ⟨diffMap j L N, fun x y c hcP hcT o => ?_⟩
  erw [eval_diffMap j L N c (R.mul (V.mul D)).coeff (Q.mul U).coeff o]
  rw [show eval L c (R.mul (V.mul D)).coeff o = _ from
    matchMap_eval V M (fun a d e h1 h2 z => by
      have h := hM a d e h1 h2 z
      by_cases h' : a = d <;> simpa [h'] using h) x y c hcP hcT o]
  change _ - eval (prodMap (idMap (A := Q.Leg)) C) c
    (fun a => Q.coeff (fun i => (a i).1) * U.coeff (fun i => (a i).2)) o = _
  erw [eval_prodMap (idMap (A := Q.Leg)) C c Q.coeff U.coeff o, eval_idMap, hC x y c hcP hcT]
  by_cases he : x = y
  · subst y
    have hn (p : Direction (b+1)) : p.val ≠ 0 := p.property
    simp only [word_add_self, hn, ↓reduceIte, Finset.sum_const_zero, mul_zero, sub_zero]
    dsimp only [Raw.mul, D, Raw.maskDiagonal, Crossing.basisTensor]
    rw [← mul_assoc]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    split
    · exact if_pos ‹_›
    · exact if_neg ‹_›

  · simp only [pairName_eq_iff, he, false_or, ite_false]
    ring

end
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
section

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation

abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def rankOne (a : X → K) (b : Y → K) (c : Z → K) : Tensor K X Y Z :=
  fun x y z => a x * b y * c z

def RankAtMost (T : Tensor K X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    T = fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z

def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

def contract (T : Tensor K X Y Z) [Fintype X] [Fintype Y]
    (a : X → K) (b : Y → K) : Z → K :=
  fun z => ∑ x, ∑ y, T x y z * a x * b y

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def power (T : Tensor K X Y Z) (n : ℕ) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

@[simp] theorem directSum_matching {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (i : ι) (x : X) (y : Y) (z : Z) :
    directSum T (i, x) (i, y) (i, z) = T i x y z := by
  simp [directSum]

theorem directSum_zero_of_left_ne {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (x : ι × X) (y : ι × Y) (z : ι × Z)
    (h : x.1 ≠ y.1) : directSum T x y z = 0 := by
  simp [directSum, h]

@[simp] theorem rankAtMost_zero : RankAtMost (0 : Tensor K X Y Z) 0 := by
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  funext x y z
  simp

theorem rankOne_rankAtMost (a : X → K) (b : Y → K) (c : Z → K) :
    RankAtMost (rankOne a b c) 1 := by
  refine ⟨fun _ => a, fun _ => b, fun _ => c, ?_⟩
  funext x y z
  simp

theorem RankAtMost.map {L : Type*} [CommSemiring L]
    (f : K →+* L) {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost T r) :
    RankAtMost (fun x y z => f (T x y z)) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => f (a i x), fun i y => f (b i y), fun i z => f (c i z), ?_⟩
  funext x y z
  simp [rankOne]

theorem RankAtMost.scale {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (u : K) :
    RankAtMost (fun x y z => u * T x y z) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => u * a i x, b, c, ?_⟩
  funext x y z
  simp [rankOne, Finset.mul_sum, mul_assoc]

theorem rankAtMost_sum_rankOne {ι : Type*} [Fintype ι]
    (a : ι → X → K) (b : ι → Y → K) (c : ι → Z → K) :
    RankAtMost (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (Fintype.card ι) := by
  classical
  refine ⟨fun i => a ((Fintype.equivFin ι).symm i),
    fun i => b ((Fintype.equivFin ι).symm i),
    fun i => c ((Fintype.equivFin ι).symm i), ?_⟩
  funext x y z
  exact ((Fintype.equivFin ι).symm.sum_comp
    (fun i => rankOne (a i) (b i) (c i) x y z)).symm

theorem RankAtMost.product {U V W : Type*}
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost T r) (hS : RankAtMost S s) :
    RankAtMost (Tensor.product T S) (r * s) := by
  rcases hT with ⟨a, b, c, rfl⟩
  rcases hS with ⟨d, e, f, rfl⟩
  let aa : (Fin r × Fin s) → (X × U) → K := fun i x => a i.1 x.1 * d i.2 x.2
  let bb : (Fin r × Fin s) → (Y × V) → K := fun i y => b i.1 y.1 * e i.2 y.2
  let cc : (Fin r × Fin s) → (Z × W) → K := fun i z => c i.1 z.1 * f i.2 z.2
  have heq : Tensor.product
      (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (fun u v w => ∑ j, rankOne (d j) (e j) (f j) u v w) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    simp only [Tensor.product, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [rankOne, aa, bb, cc]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

theorem RankAtMost.power {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (n : ℕ) : RankAtMost (Tensor.power T n) (r ^ n) := by
  rcases h with ⟨a, b, c, rfl⟩
  let aa : (Fin n → Fin r) → (Fin n → X) → K := fun f x => ∏ i, a (f i) (x i)
  let bb : (Fin n → Fin r) → (Fin n → Y) → K := fun f y => ∏ i, b (f i) (y i)
  let cc : (Fin n → Fin r) → (Fin n → Z) → K := fun f z => ∏ i, c (f i) (z i)
  have heq : Tensor.power (fun x y z => ∑ j, rankOne (a j) (b j) (c j) x y z) n =
      fun x y z => ∑ f, rankOne (aa f) (bb f) (cc f) x y z := by
    funext x y z
    simp only [Tensor.power, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [rankOne, aa, bb, cc, Finset.prod_mul_distrib]
  rw [heq]
  simpa only [Fintype.card_pi_const, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_rankOne (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (a : X → K) (b : Y → K) (c : Z → K) :
    restrict A B C (rankOne a b c) =
      rankOne (fun x' => ∑ x, A x' x * a x)
        (fun y' => ∑ y, B y' y * b y)
        (fun z' => ∑ z, C z' z * c z) := by
  funext x' y' z'
  simp only [restrict, rankOne]
  conv_rhs => rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem restrict_sum {ι : Type*} [Fintype ι]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : ι → Tensor K X Y Z) :
    restrict A B C (fun x y z => ∑ i, T i x y z) =
      fun x' y' z' => ∑ i, restrict A B C (T i) x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  calc
    (∑ x, ∑ y, ∑ z, ∑ i, A x' x * B y' y * C z' z * T i x y z) =
        ∑ x, ∑ y, ∑ i, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z :=
      Finset.sum_comm

theorem RankAtMost.restrict {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : RankAtMost (Tensor.restrict A B C T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x' => ∑ x, A x' x * a i x,
    fun i y' => ∑ y, B y' y * b i y,
    fun i z' => ∑ z, C z' z * c i z, ?_⟩
  rw [restrict_sum]
  funext x' y' z'
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (congrFun (congrFun (restrict_rankOne A B C (a i) (b i) (c i)) x') y') z'

end Algebra

section Pullback
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict
      (fun x' x => if x = fx x' then 1 else 0)
      (fun y' y => if y = fy y' then 1 else 0)
      (fun z' z => if z = fz z' then 1 else 0) T := by
  classical
  funext x y z
  simp [pullback, restrict, ite_mul, mul_ite]

theorem RankAtMost.pullback {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (pullback fx fy fz T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => a i (fx x), fun i y => b i (fy y),
    fun i z => c i (fz z), rfl⟩

end Pullback

section ComplexTopology

variable {X Y Z X' Y' Z' : Type*}

def BorderRankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (r : ℕ) : Prop :=
  T ∈ closure {S | RankAtMost S r}

def restrictionOrbit [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : Set (Tensor ℂ X' Y' Z') :=
  {U | ∃ (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ),
    U = restrict A B C T}

def DegeneratesTo [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor ℂ X Y Z) (U : Tensor ℂ X' Y' Z') : Prop :=
  U ∈ closure (restrictionOrbit T)

theorem RankAtMost.borderRankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : RankAtMost T r) :
    BorderRankAtMost T r := subset_closure h

theorem continuous_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    Continuous (Tensor.restrict A B C) := by
  unfold restrict
  fun_prop

theorem BorderRankAtMost.restrict [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : BorderRankAtMost T r)
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    BorderRankAtMost (Tensor.restrict A B C T) r := by
  have hclosed : IsClosed {S : Tensor ℂ X Y Z |
      BorderRankAtMost (Tensor.restrict A B C S) r} :=
    isClosed_closure.preimage (continuous_restrict A B C)
  have hsubset : {S : Tensor ℂ X Y Z | RankAtMost S r} ⊆
      {S | BorderRankAtMost (Tensor.restrict A B C S) r} := by
    intro S hS
    exact (hS.restrict A B C).borderRankAtMost
  exact closure_minimal hsubset hclosed h

theorem continuous_product_left {U V W : Type*} (S : Tensor ℂ U V W) :
    Continuous (fun T : Tensor ℂ X Y Z => Tensor.product T S) := by
  unfold product
  fun_prop

theorem continuous_product_right {U V W : Type*} (T : Tensor ℂ X Y Z) :
    Continuous (fun S : Tensor ℂ U V W => Tensor.product T S) := by
  unfold product
  fun_prop

theorem BorderRankAtMost.product {U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor ℂ X Y Z} {S : Tensor ℂ U V W} {r s : ℕ}
    (hT : BorderRankAtMost T r) (hS : BorderRankAtMost S s) :
    BorderRankAtMost (Tensor.product T S) (r * s) := by
  have hexact : ∀ T' : Tensor ℂ X Y Z, RankAtMost T' r →
      BorderRankAtMost (Tensor.product T' S) (r * s) := by
    intro T' hT'
    have hclosed : IsClosed {S' : Tensor ℂ U V W |
        BorderRankAtMost (Tensor.product T' S') (r * s)} :=
      isClosed_closure.preimage (continuous_product_right T')
    have hsubset : {S' : Tensor ℂ U V W | RankAtMost S' s} ⊆
        {S' | BorderRankAtMost (Tensor.product T' S') (r * s)} := by
      intro S' hS'
      exact (hT'.product hS').borderRankAtMost
    exact closure_minimal hsubset hclosed hS
  have hclosed : IsClosed {T' : Tensor ℂ X Y Z |
      BorderRankAtMost (Tensor.product T' S) (r * s)} :=
    isClosed_closure.preimage (continuous_product_left S)
  exact closure_minimal hexact hclosed hT

theorem BorderRankAtMost.of_degeneration [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} {r : ℕ}
    (hT : BorderRankAtMost T r) (hTU : DegeneratesTo T U) :
    BorderRankAtMost U r := by
  have hsubset : restrictionOrbit T ⊆
      {S : Tensor ℂ X' Y' Z' | BorderRankAtMost S r} := by
    rintro S ⟨A, B, C, rfl⟩
    exact hT.restrict A B C
  exact closure_minimal hsubset isClosed_closure hTU

end ComplexTopology

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

-- Source module: OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Complexity
section

namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation

namespace Arithmetic

inductive Gate (Input Register : Type*) where
  | constant : ℂ → Gate Input Register
  | input : Input → Gate Input Register
  | add : Register → Register → Gate Input Register
  | sub : Register → Register → Gate Input Register
  | mul : Register → Register → Gate Input Register

namespace Gate

variable {Input Register : Type*}

def eval (inputs : Input → ℂ) (registers : Register → ℂ) : Gate Input Register → ℂ
  | .constant z => z
  | .input i => inputs i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

def cost : Gate Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

end Gate

inductive Program (Input : Type*) : ℕ → Type _ where
  | nil : Program Input 0
  | step {r : ℕ} : Program Input r → Gate Input (Fin r) → Program Input (r + 1)

namespace Program

variable {Input : Type*}

def eval : {r : ℕ} → Program Input r → (Input → ℂ) → Fin r → ℂ
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p g, inputs =>
    Fin.cases (g.eval inputs (p.eval inputs)) (p.eval inputs)

def cost : {r : ℕ} → Program Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

@[simp] theorem eval_step_zero {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

@[simp] theorem eval_step_succ {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

@[simp] theorem cost_step {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

abbrev MatrixInput (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

def matrixInputs {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : MatrixInput n → ℂ
  | .inl (i, j) => A i j
  | .inr (j, k) => B j k

structure MatrixAlgorithm (n : ℕ) where
  registers : ℕ
  program : Program (MatrixInput n) registers
  output : Fin n → Fin n → Fin registers

namespace MatrixAlgorithm

def eval {n : ℕ} (P : MatrixAlgorithm n)
    (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i k => P.program.eval (matrixInputs A B) (P.output i k)

def Correct {n : ℕ} (P : MatrixAlgorithm n) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℂ, P.eval A B = A * B

def cost {n : ℕ} (P : MatrixAlgorithm n) : ℕ := P.program.cost

theorem correct_iff_entries {n : ℕ} (P : MatrixAlgorithm n) :
    P.Correct ↔ ∀ (A B : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k := by
  constructor
  · intro h A B i k
    exact congrFun (congrFun (h A B) i) k
  · intro h A B
    funext i k
    exact h A B i k

end MatrixAlgorithm

def scalarAlgorithm : MatrixAlgorithm 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

theorem scalarAlgorithm_correct : scalarAlgorithm.Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

@[simp] theorem scalarAlgorithm_cost : scalarAlgorithm.cost = 1 := rfl

def AdmissibleExponent (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

noncomputable def omega : ℝ := sInf {τ : ℝ | AdmissibleExponent τ}

end Arithmetic

namespace Tensor

def matrixMultiplication (a b c : ℕ) :
    Tensor ℂ (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

@[simp] theorem matrixMultiplication_matching (a b c : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    matrixMultiplication a b c (i, j) (j, k) (k, i) = 1 := by
  simp [matrixMultiplication]

end Tensor
end MatrixMultiplication.Foundation

end

end OAI
end

-- Source module: OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorBatching
section

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

def diagonal (ι : Type*) [DecidableEq ι] : Tensor K ι ι ι :=
  fun i j k => if i = j ∧ i = k then 1 else 0

theorem diagonal_rankAtMost (ι : Type*) [Fintype ι] [DecidableEq ι] :
    RankAtMost (diagonal (K := K) ι) (Fintype.card ι) := by
  let a : ι → ι → K := fun i j => if i = j then 1 else 0
  have heq : diagonal (K := K) ι =
      fun x y z => ∑ i, rankOne (a i) (a i) (a i) x y z := by
    funext x y z
    simp [diagonal, rankOne, a, mul_ite, ite_and]
    split_ifs <;> simp_all
  rw [heq]
  exact rankAtMost_sum_rankOne a a a

theorem RankAtMost.repeat_batch {S : Tensor K U V W} {k r R B : ℕ}
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hfit : R ≤ B * k) :
    RankAtMost (directSum (fun _ : Fin R => S)) (B * r) := by
  classical
  let f : Fin R → Fin B × Fin k := fun i => finProdFinEquiv.symm (Fin.castLE hfit i)
  have hf : Function.Injective f := finProdFinEquiv.symm.injective.comp (Fin.castLE_injective hfit)
  have hbig := (diagonal_rankAtMost (K := K) (Fin B)).product hbatch
  simp only [Fintype.card_fin] at hbig
  rcases hbig with ⟨a, b, c, heq⟩
  let liftU : (Fin R × U) → Fin B × (Fin k × U) := fun x => ((f x.1).1, (f x.1).2, x.2)
  let liftV : (Fin R × V) → Fin B × (Fin k × V) := fun y => ((f y.1).1, (f y.1).2, y.2)
  let liftW : (Fin R × W) → Fin B × (Fin k × W) := fun z => ((f z.1).1, (f z.1).2, z.2)
  refine ⟨fun i x => a i (liftU x), fun i y => b i (liftV y),
    fun i z => c i (liftW z), ?_⟩
  funext x y z
  change directSum (fun _ : Fin R => S) x y z =
    ∑ i, rankOne (a i) (b i) (c i) (liftU x) (liftV y) (liftW z)
  have hentry := congrFun (congrFun (congrFun heq (liftU x)) (liftV y)) (liftW z)
  rw [← hentry]
  by_cases hxy : x.1 = y.1
  · by_cases hxz : x.1 = z.1
    · have hyz : y.1 = z.1 := hxy.symm.trans hxz
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hyz]
    · have hn : f x.1 ≠ f z.1 := fun h => hxz (hf h)
      have hs : (f x.1).1 ≠ (f z.1).1 ∨ (f x.1).2 ≠ (f z.1).2 := by
        by_cases hfirst : (f x.1).1 = (f z.1).1
        · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
        · exact Or.inl hfirst
      rcases hs with hs | hs <;>
        simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxz, hs]
  · have hn : f x.1 ≠ f y.1 := fun h => hxy (hf h)
    have hs : (f x.1).1 ≠ (f y.1).1 ∨ (f x.1).2 ≠ (f y.1).2 := by
      by_cases hfirst : (f x.1).1 = (f y.1).1
      · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
      · exact Or.inl hfirst
    rcases hs with hs | hs <;>
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hs]

theorem RankAtMost.batch_substitute [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r b : ℕ}
    (hT : RankAtMost T r)
    (hbatch : RankAtMost (directSum (fun _ : Fin r => S)) b) :
    RankAtMost (Tensor.product T S) b := by
  classical
  rcases hT with ⟨a, c, e, rfl⟩
  let A : (X × U) → (Fin r × U) → K :=
    fun x i => if x.2 = i.2 then a i.1 x.1 else 0
  let B : (Y × V) → (Fin r × V) → K :=
    fun y i => if y.2 = i.2 then c i.1 y.1 else 0
  let C : (Z × W) → (Fin r × W) → K :=
    fun z i => if z.2 = i.2 then e i.1 z.1 else 0
  have heq : Tensor.restrict A B C (directSum (fun _ : Fin r => S)) =
      Tensor.product (fun x y z => ∑ i, rankOne (a i) (c i) (e i) x y z) S := by
    funext x y z
    simp [Tensor.restrict, directSum, Tensor.product, rankOne, A, B, C,
      Fintype.sum_prod_type, ite_and, ite_mul, mul_ite, Finset.sum_mul]
  rw [← heq]
  exact hbatch.restrict A B C

theorem RankAtMost.batch_product [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {R k r B : ℕ}
    (hT : RankAtMost T R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r)
    (hfit : R ≤ B * k) : RankAtMost (Tensor.product T S) (B * r) :=
  hT.batch_substitute (hbatch.repeat_batch hfit)

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

-- Source module: OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
section

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

def matrixCoefficients (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K (A × B) (B × C) (C × A) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

theorem matrixMultiplication_eq_matrixCoefficients (a b c : ℕ) :
    matrixMultiplication a b c = matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c) := rfl

theorem contract_matrixCoefficients [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (left : A × B → K) (right : B × C → K) (i : A) (k : C) :
    contract (matrixCoefficients A B C) left right (k, i) =
      ∑ j, left (i, j) * right (j, k) := by
  simp [contract, matrixCoefficients, Fintype.sum_prod_type, ite_and, ite_mul]

theorem matrixCoefficients_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (x : (A × D) × (B × E)) (y : (B × E) × (C × F)) (z : (C × F) × (A × D)) :
    product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)
      ((x.1.1, x.2.1), (x.1.2, x.2.2))
      ((y.1.1, y.2.1), (y.1.2, y.2.2))
      ((z.1.1, z.2.1), (z.1.2, z.2.2)) =
      matrixCoefficients (A × D) (B × E) (C × F) x y z := by
  simp only [product, matrixCoefficients, Prod.ext_iff]
  split_ifs <;> simp_all

theorem matrixCoefficients_cyclic [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (x : B × C) (y : C × A) (z : A × B) :
    matrixCoefficients (K := K) A B C z x y = matrixCoefficients B C A x y z := by
  have h : (z.2 = x.1 ∧ x.2 = y.1 ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩
  simp only [matrixCoefficients, h]

theorem matrixCoefficients_rank_of_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r : ℕ}
    (hproduct : RankAtMost (product (matrixCoefficients (K := K) A B C)
      (matrixCoefficients D E F)) r) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) r := by
  have h := hproduct.pullback
    (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
  have heq : pullback
      (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
      (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      (product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)) =
      matrixCoefficients (K := K) (A × D) (B × E) (C × F) := by
    funext x y z
    exact matrixCoefficients_product x y z
  rw [heq] at h
  exact h

theorem matrixCoefficients_product_rank [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r s : ℕ}
    (hT : RankAtMost (matrixCoefficients (K := K) A B C) r)
    (hS : RankAtMost (matrixCoefficients (K := K) D E F) s) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) (r * s) :=
  matrixCoefficients_rank_of_product (hT.product hS)

theorem matrixCoefficients_batch_rank [DecidableEq A] [DecidableEq B] [Fintype B]
    {R k r batches : ℕ}
    (houter : RankAtMost (matrixCoefficients (K := K) A A A) R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => matrixCoefficients (K := K) B B B)) r)
    (hfit : R ≤ batches * k) :
    RankAtMost (matrixCoefficients (K := K) (A × B) (A × B) (A × B)) (batches * r) :=
  matrixCoefficients_rank_of_product (houter.batch_product hbatch hfit)

theorem matrixCoefficients_power [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (n : ℕ) (x : (Fin n → A) × (Fin n → B))
    (y : (Fin n → B) × (Fin n → C)) (z : (Fin n → C) × (Fin n → A)) :
    Tensor.power (matrixCoefficients (K := K) A B C) n
      (fun i => (x.1 i, x.2 i)) (fun i => (y.1 i, y.2 i)) (fun i => (z.1 i, z.2 i)) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) x y z := by
  simp only [Tensor.power, matrixCoefficients, Fintype.prod_boole, forall_and, ← funext_iff]

theorem matrixCoefficients_cyclic_rank [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {r : ℕ} (h : RankAtMost (matrixCoefficients (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K) B C A) r := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨b, c, a, ?_⟩
  funext x y z
  rw [← matrixCoefficients_cyclic (K := K) x y z]
  rw [congrFun (congrFun (congrFun heq z) x) y]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

-- Source module: OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening
section

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z : Type*} [Field K]

theorem RankAtMost.card_le_of_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι K) := by
    funext i j
    change (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = if i = j then 1 else 0
    calc
      (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = T (x i) (y i) (z j) :=
        (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm
      _ = _ := hidentity i j
  have hle : (1 : Matrix ι ι K).rank ≤ r := by
    rw [← hmul]
    exact (Matrix.rank_mul_le_left L R).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width L)
  simpa only [Matrix.rank_one] using hle

theorem directSum_matrixCoefficients_rank_lower
    {Label A B C : Type*} [Fintype Label] [Fintype A] [Fintype C]
    [DecidableEq Label] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty B] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : Label => matrixCoefficients (K := K) A B C)) r) :
    Fintype.card Label * (Fintype.card C * Fintype.card A) ≤ r := by
  classical
  let b₀ : B := Classical.choice inferInstance
  have hminor : ∀ i j : Label × (C × A),
      directSum (fun _ : Label => matrixCoefficients (K := K) A B C)
        (i.1, (i.2.2, b₀)) (i.1, (b₀, i.2.1)) j = if i = j then 1 else 0 := by
    intro i j
    simp only [directSum, matrixCoefficients]
    split_ifs <;> simp_all [Prod.ext_iff]
  have hlower := h.card_le_of_identity
    (fun i : Label × (C × A) => (i.1, (i.2.2, b₀)))
    (fun i : Label × (C × A) => (i.1, (b₀, i.2.1)))
    (fun i : Label × (C × A) => i) hminor
  simpa only [Fintype.card_prod] using hlower

theorem directSum_square_rank_lower (k n r : ℕ) (hn : 0 < n)
    (h : RankAtMost (directSum (fun _ : Fin k =>
      matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))) r) :
    k * n ^ 2 ≤ r := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin, pow_two] using directSum_matrixCoefficients_rank_lower h

end Tensor
end MatrixMultiplication.Foundation

end

end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.Tensor
section

/-!
# Rectangular matrix multiplication over a field

We use the finite coefficient tensors and Kronecker powers from the matrix
multiplication library. The dimensions are the shared wire sizes, in the
paper's order `12, 23, 31`. The first site's coordinates are consequently
indexed by `Fin n31 × Fin n12`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

section

section Rank

variable {F X Y Z : Type*} [Field F] [Fintype X] [Fintype Y]

/-- Expanding in the coordinate bases of the first two sites gives a finite
decomposition into simple tensors. -/
theorem exists_rankAtMost (T : Tensor F X Y Z) : ∃ r, Tensor.RankAtMost T r := by
  classical
  let a : X × Y → X → F := fun p x => if p.1 = x then 1 else 0
  let b : X × Y → Y → F := fun p y => if p.2 = y then 1 else 0
  let c : X × Y → Z → F := fun p => T p.1 p.2
  refine ⟨Fintype.card (X × Y), ?_⟩
  have h : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, ite_mul, mul_ite]
  rw [h]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- The least number of simple tensors in a decomposition over the ground field. -/
def tensorRank (T : Tensor F X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_rankAtMost T)

theorem rankAtMost_tensorRank (T : Tensor F X Y Z) : Tensor.RankAtMost T (tensorRank T) := by
  classical
  exact Nat.find_spec (exists_rankAtMost T)

theorem tensorRank_le_of_rankAtMost {T : Tensor F X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost T r) : tensorRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_rankAtMost T) h

/-- The infimum of the positive tensor-power rank roots. -/
def asymptoticRank (T : Tensor F X Y Z) : ℝ :=
  ⨅ n : ℕ, (tensorRank (Tensor.power T (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹)

theorem asymptoticRank_nonneg (T : Tensor F X Y Z) : 0 ≤ asymptoticRank T :=
  le_ciInf (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem asymptoticRank_le_tensorRank (T : Tensor F X Y Z) :
    asymptoticRank T ≤ tensorRank T := by
  have hu := ciInf_le ⟨(0 : ℝ), by rintro _ ⟨n, rfl⟩; positivity⟩ (0 : ℕ)
    (f := fun n : ℕ => (tensorRank (Tensor.power T (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹))
  have h₁ := tensorRank_le_of_rankAtMost ((rankAtMost_tensorRank T).power 1)
  simp only [pow_one] at h₁
  apply le_trans _ (Nat.cast_le (α := ℝ) |>.mpr h₁)
  simpa [asymptoticRank] using hu

end Rank

/-- The coefficient of the cyclic pattern `e_{ki} ⊗ e_{ij} ⊗ e_{jk}` is one. -/
abbrev matrixTensor (F : Type*) [Field F] (n12 n23 n31 : ℕ) :=
  Tensor.matrixCoefficients (K := F) (Fin n31) (Fin n12) (Fin n23)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SpectralPoint
section

/-! # Spectral evaluation and tensor rank

We record the properties of a normalized spectral point needed for a rank lower
bound. All local maps act on actual three-site coefficient tensors. The
comparison with asymptotic rank follows by applying the exact rank comparison
to every positive tensor power.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped NNReal

section

/-- The normalized, multiplicative, restriction-monotone evaluation underlying a
three-site spectral point. Only its laws used in the rank comparison are required. -/
structure RankFunctional (F : Type*) [Field F] where
  value {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] : Tensor F X Y Z → ℝ≥0
  diagonal (r : ℕ) : value (Tensor.diagonal (K := F) (Fin r)) = r
  product {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
      [Fintype U] [Fintype V] [Fintype W] (T : Tensor F X Y Z) (S : Tensor F U V W) :
    value (Tensor.product T S) = value T * value S
  restrict_le {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
      [Fintype U] [Fintype V] [Fintype W] (T : Tensor F X Y Z)
      (A : U → X → F) (B : V → Y → F) (C : W → Z → F) :
    value (Tensor.restrict A B C T) ≤ value T

namespace RankFunctional

variable {F : Type*} [Field F] (φ : RankFunctional F)
variable {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype U] [Fintype V] [Fintype W]

theorem pullback_le (T : Tensor F X Y Z) (a : U → X) (b : V → Y) (c : W → Z) :
    φ.value (Tensor.pullback a b c T) ≤ φ.value T := by
  classical
  convert φ.restrict_le T
      (fun u x => if x = a u then 1 else 0)
      (fun v y => if y = b v then 1 else 0)
      (fun w z => if z = c w then 1 else 0) using 2
  funext u v w
  simp [Tensor.pullback, Tensor.restrict, ite_mul, mul_ite]

theorem pullback_equiv (T : Tensor F X Y Z) (a : U ≃ X) (b : V ≃ Y) (c : W ≃ Z) :
    φ.value (Tensor.pullback a b c T) = φ.value T := by
  refine le_antisymm (φ.pullback_le T a b c) ?_
  have h := φ.pullback_le (Tensor.pullback a b c T) a.symm b.symm c.symm
  have heq : Tensor.pullback a.symm b.symm c.symm (Tensor.pullback a b c T) = T := by
    funext x y z
    simp [Tensor.pullback]
  rwa [heq] at h

theorem le_of_rankAtMost {T : Tensor F X Y Z} {r : ℕ} (hr : Tensor.RankAtMost T r) :
    φ.value T ≤ r := by
  obtain ⟨a,b,c,ht⟩ := hr
  have heq : Tensor.restrict (fun x i => a i x) (fun y j => b j y)
      (fun z k => c k z) (Tensor.diagonal (K := F) (Fin r)) = T := by
    rw [ht]
    funext x y z
    simp [Tensor.restrict, Tensor.diagonal, Tensor.rankOne, mul_ite, ite_and]
  rw [← φ.diagonal, ← heq]
  apply φ.restrict_le

theorem le_tensorRank (T : Tensor F X Y Z) : φ.value T ≤ tensorRank T :=
  φ.le_of_rankAtMost (rankAtMost_tensorRank T)

/-- An entry equal to one supplies the one-dimensional unit tensor. -/
theorem one_le_of_entry_one {T : Tensor F X Y Z} {x : X} {y : Y} {z : Z}
    (h : T x y z = 1) : 1 ≤ φ.value T := by
  have heq : Tensor.pullback (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) (fun _ : Fin 1 => z) T =
      Tensor.diagonal (K := F) (Fin 1) := by
    funext i j k
    simp [Tensor.pullback, Tensor.diagonal, h, Subsingleton.elim i j, Subsingleton.elim j k]
  have hh := φ.pullback_le T (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) (fun _ : Fin 1 => z)
  simpa only [heq, φ.diagonal, Nat.cast_one] using hh

private def uncons {A : Type} (n : ℕ) : (Fin (n + 1) → A) ≃ A × (Fin n → A) where
  toFun f := (f 0, fun i => f i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv f := by funext i; induction i using Fin.cases <;> simp
  right_inv x := by ext <;> simp

theorem power_succ (T : Tensor F X Y Z) (n : ℕ) :
    φ.value (Tensor.power T (n + 1)) = φ.value T ^ (n + 1) := by
  induction n with
  | zero =>
    let e (A : Type) : (Fin 1 → A) ≃ A := Equiv.funUnique (Fin 1) A
    have ht : Tensor.power T 1 = Tensor.pullback (e X) (e Y) (e Z) T := by
      funext x y z
      simp [Tensor.power, Tensor.pullback, e, Equiv.funUnique, Subsingleton.elim (default : Fin 1) 0]
    rw [ht, φ.pullback_equiv, pow_one]
  | succ n ih =>
    have ht : Tensor.power T (n + 1 + 1) =
        Tensor.pullback (uncons (n + 1)) (uncons (n + 1)) (uncons (n + 1))
          (Tensor.product T (Tensor.power T (n + 1))) := by
      funext x y z
      exact Fin.prod_univ_succ _
    rw [ht, φ.pullback_equiv, φ.product, ih, pow_succ' _ (n + 1)]

/-- A normalized spectral evaluation is bounded by the infimum of the
positive power rank roots, in the ground field. -/
theorem le_asymptoticRank (T : Tensor F X Y Z) : (φ.value T : ℝ) ≤ asymptoticRank T := by
  apply le_ciInf
  intro n
  have h := φ.le_tensorRank (Tensor.power T (n + 1))
  rw [φ.power_succ] at h
  have hr : (φ.value T : ℝ) ^ (n + 1) ≤ tensorRank (Tensor.power T (n + 1)) := by
    exact_mod_cast h
  have hroot := Real.rpow_le_rpow (by positivity) hr (by positivity : 0 ≤ ((n + 1 : ℝ)⁻¹))
  rwa [← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _), Nat.cast_succ,
    mul_inv_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), Real.rpow_one] at hroot

end RankFunctional
end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteRankFunctional
section

/-! # Evaluating three-site tensors at a finite-site spectral point

The site-indexed coefficient convention and the curried convention used by
matrix multiplication describe the same three-index arrays. In particular,
their products, diagonals, and three local restricting maps agree after
relabeling coordinates.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor

open MatrixMultiplication.Foundation
open scoped BigOperators Classical NNReal
noncomputable section

private def tuple {A : Fin 3 → Type*} (x : A 0) (y : A 1) (z : A 2) : ∀ i, A i :=
  Fin.cons x (Fin.cons y (Fin.cons z (fun i => i.elim0)))

private def coords (A : Fin 3 → Type*) : (∀ i, A i) ≃ A 0 × A 1 × A 2 :=
  (Fin.consEquiv A).symm.trans ((Equiv.refl _).prodCongr (piFinTwoEquiv _))

variable {F : Type*} [CommSemiring F] {X Y Z U V W : Type}
  [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]

/-- Regard a matrix-multiplication coefficient array as a tensor on three sites. -/
def ofThree (T : Tensor F X Y Z) : Raw (Fin 3) F where
  Leg := ![X, Y, Z]
  finiteLeg := tuple (inferInstanceAs (Fintype X)) (inferInstanceAs (Fintype Y)) (inferInstanceAs (Fintype Z))
  coeff := fun x => T (x 0) (x 1) (x 2)

/-- Local restriction agrees in the curried and site-indexed conventions. -/
theorem ofThree_restrict (T : Tensor F X Y Z) (A : U → X → F) (B : V → Y → F) (C : W → Z → F) :
    (ofThree (Tensor.restrict A B C T)).Restricts (ofThree T) := by
  let : DecidableEq (Fin 3) := fun i j => Classical.propDecidable (i = j)
  let M : ∀ i, (ofThree (Tensor.restrict A B C T)).Leg i → (ofThree T).Leg i → F := tuple A B C
  refine ⟨M, fun p => ?_⟩
  change (∑ x, ∑ y, ∑ z, A (p 0) x * B (p 1) y * C (p 2) z * T x y z) =
    ∑ q : (i : Fin 3) → (ofThree T).Leg i, T (q 0) (q 1) (q 2) * ∏ i, M i (p i) (q i)
  let e := coords (ofThree T).Leg
  calc
    _ = ∑ q : X × Y × Z, A (p 0) q.1 * B (p 1) q.2.1 * C (p 2) q.2.2 * T q.1 q.2.1 q.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = _ := by
      apply Fintype.sum_equiv e.symm
      intro q
      simp only [Fin.prod_univ_three]
      change A (p 0) q.1 * B (p 1) q.2.1 * C (p 2) q.2.2 * T q.1 q.2.1 q.2.2 =
        T q.1 q.2.1 q.2.2 * (A (p 0) q.1 * B (p 1) q.2.1 * C (p 2) q.2.2)
      ac_rfl

/-- The grouped tensor product in both coordinate conventions pairs the same three indices. -/
theorem ofThree_product (T : Tensor F X Y Z) (S : Tensor F U V W) :
    (ofThree (Tensor.product T S)).Equivalent ((ofThree T).mul (ofThree S)) := by
  let e : ∀ i, (ofThree (Tensor.product T S)).Leg i ≃ ((ofThree T).mul (ofThree S)).Leg i :=
    tuple (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
  apply Raw.reindex_equivalent e
  intro p
  rfl

private theorem diagonal_eq_sum {α : Type} [Fintype α] [DecidableEq α] (q : Fin 3 → α) :
    (if q 0 = q 1 ∧ q 0 = q 2 then (1 : F) else 0) =
      ∑ a : α, @ite F (q = fun _ => a) (Classical.propDecidable _) 1 0 := by
  have eq (a : α) : q = (fun _ => a) ↔ q 0 = a ∧ q 1 = a ∧ q 2 = a := by
    simp [funext_iff, Fin.forall_fin_succ]
  simp_rw [eq]
  rw [Finset.sum_eq_single (q 0)]
  · simp [eq_comm]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- The full diagonal in the rank model is the common-label site diagonal. -/
theorem ofThree_diagonal (α : Type) [Fintype α] [DecidableEq α] :
    (ofThree (Tensor.diagonal (K := F) α)).Equivalent (Raw.diagonal (Fin 3) F α) := by
  let e : ∀ i, (ofThree (Tensor.diagonal (K := F) α)).Leg i ≃ α :=
    tuple (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
  apply Raw.reindex_equivalent e
  intro x
  exact diagonal_eq_sum (F := F) (fun i => e i (x i))

/-- Evaluation at a normalized three-site spectral point gives the multiplicative,
restriction-monotone functional used for the rectangular rank bounds. -/
def rankFunctionalOfSpectrum {K : Type*} [Field K]
    (f : normalizedSpectrum (fun x y : TensorClass.{0} (Fin 3) K => x ≤ y)) : RankFunctional K where
  value T := f.1 (ofRaw (ofThree T))
  diagonal r := by
    rw [ofRaw_eq_iff.mpr (ofThree_diagonal (F := K) (Fin r)), ofRaw_diagonal_fin_eq_natCast]
    exact map_natCast (normalizedSpectrum.toRingHom f) r
  product T S := by
    rw [ofRaw_eq_iff.mpr (ofThree_product T S), ofRaw_mul]
    exact f.2.2.2.2.1 _ _
  restrict_le T A B C := f.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr (ofThree_restrict T A B C))

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.WireProduct
section

/-! # Matrix multiplication as a product of wires

Each shared wire is an identity matrix at its two endpoints and has a
one-dimensional slot at the remaining site. After grouping the two nontrivial
legs at each site in cyclic order, the three wires give the coefficient tensor
of rectangular matrix multiplication.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation

section

/-- The identity wire between sites one and two. -/
def wire12 (F : Type*) [Zero F] [One F] (n : ℕ) : Tensor F (Fin n) (Fin n) Unit :=
  fun i j _ ↦ if i = j then 1 else 0

/-- The identity wire between sites two and three. -/
def wire23 (F : Type*) [Zero F] [One F] (n : ℕ) : Tensor F Unit (Fin n) (Fin n) :=
  fun _ i j ↦ if i = j then 1 else 0

/-- The identity wire between sites three and one. -/
def wire31 (F : Type*) [Zero F] [One F] (n : ℕ) : Tensor F (Fin n) Unit (Fin n) :=
  fun i _ j ↦ if j = i then 1 else 0

/-- Group the two incident wire legs at the first site. -/
def wireSite1Equiv (n12 n31 : ℕ) :
    Fin n31 × Fin n12 ≃ (Fin n12 × Unit) × Fin n31 where
  toFun x := ((x.2, ()), x.1)
  invFun x := (x.2, x.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group the two incident wire legs at the second site. -/
def wireSite2Equiv (n12 n23 : ℕ) :
    Fin n12 × Fin n23 ≃ (Fin n12 × Fin n23) × Unit where
  toFun x := (x, ())
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group the two incident wire legs at the third site. -/
def wireSite3Equiv (n23 n31 : ℕ) :
    Fin n23 × Fin n31 ≃ (Unit × Fin n23) × Fin n31 where
  toFun x := (((), x.1), x.2)
  invFun x := (x.1.2, x.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Matrix multiplication is the product of its three two-site diagonals,
up to local bijections of the coordinate bases. -/
theorem matrixTensor_eq_wireProduct (F : Type*) [Field F] (n12 n23 n31 : ℕ) :
    matrixTensor F n12 n23 n31 =
      Tensor.pullback (wireSite1Equiv n12 n31) (wireSite2Equiv n12 n23) (wireSite3Equiv n23 n31)
        (Tensor.product (Tensor.product (wire12 F n12) (wire23 F n23)) (wire31 F n31)) := by
  funext x y z
  simp only [matrixTensor, Tensor.matrixCoefficients, Tensor.pullback, Tensor.product,
    wire12, wire23, wire31, wireSite1Equiv, wireSite2Equiv, wireSite3Equiv,
    Equiv.coe_fn_mk]
  by_cases h12 : x.2 = y.1 <;> by_cases h23 : y.2 = z.1 <;>
    by_cases h31 : z.2 = x.1 <;> simp [h12, h23, h31]

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteWireClasses
section

/-! # Three-site wire classes as partial diagonals -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor

open scoped Classical

private def occupiedLeg {α : Type} {p : Prop} (h : p) : α ≃ (p → α) where
  toFun a _ := a
  invFun f := f h
  left_inv _ := rfl
  right_inv _ := rfl

private def emptyLeg {α : Type} {p : Prop} (h : ¬ p) : Unit ≃ (p → α) where
  toFun _ hp := (h hp).elim
  invFun _ := ()
  left_inv _ := rfl
  right_inv _ := funext fun hp ↦ (h hp).elim

private def threeLegs {A : Fin 3 → Type*} (x : A 0) (y : A 1) (z : A 2) : ∀ i, A i :=
  Fin.cons x (Fin.cons y (Fin.cons z (fun i ↦ i.elim0)))

variable (F : Type*) [Field F]

private theorem coeff_pair {I α : Type} [Fintype I] [DecidableEq I] [Fintype α]
    (i j : I) (x : ∀ k, MaskLeg {i, j} α k) :
    (Raw.maskDiagonal F {i, j} α).coeff x =
      if x i (by simp) = x j (by simp) then 1 else 0 := by
  classical
  rw [Raw.maskDiagonal_coeff_at (K := F) {i, j} (Finset.mem_insert_self _ _) x]
  congr 1
  apply propext
  constructor
  · intro h
    exact (h j (by simp)).symm
  · intro h k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · rfl
    · obtain rfl := Finset.mem_singleton.mp hk
      exact h.symm

/-- The first two factors of the curried wire carry its common label. -/
theorem ofRaw_ofThree_wire12 (n : ℕ) :
    ofRaw (ofThree (wire12 F n)) = ofRaw (Raw.maskDiagonal F ({0, 1} : Finset (Fin 3)) (Fin n)) := by
  let S : Finset (Fin 3) := {0, 1}
  let e : ∀ i, (ofThree (wire12 F n)).Leg i ≃ MaskLeg S (Fin n) i :=
    threeLegs (occupiedLeg (by decide)) (occupiedLeg (by decide)) (emptyLeg (by decide))
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  refine Eq.trans ?_ (coeff_pair F (0 : Fin 3) 1 (fun i ↦ e i (x i))).symm
  simp only [ofThree, wire12]
  split_ifs <;> first | rfl | contradiction

/-- The last two factors of the curried wire carry its common label. -/
theorem ofRaw_ofThree_wire23 (n : ℕ) :
    ofRaw (ofThree (wire23 F n)) = ofRaw (Raw.maskDiagonal F ({1, 2} : Finset (Fin 3)) (Fin n)) := by
  let S : Finset (Fin 3) := {1, 2}
  let e : ∀ i, (ofThree (wire23 F n)).Leg i ≃ MaskLeg S (Fin n) i :=
    threeLegs (emptyLeg (by decide)) (occupiedLeg (by decide)) (occupiedLeg (by decide))
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  refine Eq.trans ?_ (coeff_pair F (1 : Fin 3) 2 (fun i ↦ e i (x i))).symm
  simp only [ofThree, wire23]
  split_ifs <;> first | rfl | contradiction

/-- The third and first factors of the curried wire carry its common label. -/
theorem ofRaw_ofThree_wire31 (n : ℕ) :
    ofRaw (ofThree (wire31 F n)) = ofRaw (Raw.maskDiagonal F ({2, 0} : Finset (Fin 3)) (Fin n)) := by
  let S : Finset (Fin 3) := {2, 0}
  let e : ∀ i, (ofThree (wire31 F n)).Leg i ≃ MaskLeg S (Fin n) i :=
    threeLegs (occupiedLeg (by decide)) (emptyLeg (by decide)) (occupiedLeg (by decide))
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  refine Eq.trans ?_ (coeff_pair F (2 : Fin 3) 0 (fun i ↦ e i (x i))).symm
  simp only [ofThree, wire31]
  split_ifs <;> first | rfl | contradiction

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.Rank
section

/-! # The height and radical tests for rectangular matrix multiplication

The load at a site is the sum of its incident logarithmic wire dimensions.
This file proves the equivalence of the two numerical tests in the rectangular
rank theorem, including the cases of zero loads and saturated flattenings.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter
open scoped BigOperators Topology
noncomputable section

/-- The three site loads for the cyclically ordered wires. -/
def loads (w12 w23 w31 : ℝ) : Fin 3 → ℝ := ![w31 + w12, w12 + w23, w23 + w31]

/-- Inequality (height-bound), tested at independently chosen positive heights. -/
def HeightTest (m : Fin 3 → ℝ) (L : ℝ) : Prop :=
  ∀ a : Fin 3 → ℝ, (∀ i, 0 < a i) →
    ∑ i, a i * m i ≤ L * (∑ i, Real.sqrt (1 + a i ^ 2) - 1)

/-- The flattening and radical inequalities of the rectangular rank theorem. -/
def RadicalTest (m : Fin 3 → ℝ) (L : ℝ) : Prop :=
  (∀ i, m i ≤ L) ∧ L ≤ ∑ i, Real.sqrt (L ^ 2 - m i ^ 2)

/-- The diagonal-price upper bound is positive for every triple of heights. -/
theorem heightDenom_pos (a : Fin 3 → ℝ) : 0 < ∑ i, Real.sqrt (1 + a i ^ 2) - 1 := by
  have h i : 1 ≤ Real.sqrt (1 + a i ^ 2) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg (a i)])
  rw [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem HeightTest.mono {m : Fin 3 → ℝ} {L U : ℝ} (h : HeightTest m L) (hLU : L ≤ U) :
    HeightTest m U := by
  intro a ha
  exact (h a ha).trans (mul_le_mul_of_nonneg_right hLU (heightDenom_pos a).le)

private theorem le_at_right_endpoint {f g : ℝ → ℝ} {x : ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ y, x < y → f y ≤ g y) : f x ≤ g x := by
  apply le_of_tendsto_of_tendsto (b := 𝓝[>] x) hf.continuousAt.continuousWithinAt
    hg.continuousAt.continuousWithinAt
  filter_upwards [self_mem_nhdsWithin] with y hy using h y hy

/-- Zero-height sites are obtained by approaching from positive heights. -/
theorem HeightTest.nonnegHeights {m : Fin 3 → ℝ} {L : ℝ} (h : HeightTest m L)
    (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, a i * m i ≤ L * (∑ i, Real.sqrt (1 + a i ^ 2) - 1) := by
  let f (t : ℝ) := ∑ i, (a i + t) * m i
  let g (t : ℝ) := L * (∑ i, Real.sqrt (1 + (a i + t) ^ 2) - 1)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have bound : f 0 ≤ g 0 := le_at_right_endpoint hf hg
    (fun t ht => h (fun i => a i + t) (fun i => add_pos_of_nonneg_of_pos (ha i) ht))
  simpa [f, g] using bound

theorem HeightTest.nonneg {m : Fin 3 → ℝ} {L : ℝ} (h : HeightTest m L) : 0 ≤ L := by
  have hzero := h.nonnegHeights (fun _ => 0) (fun _ => le_rfl)
  norm_num [Fin.sum_univ_three] at hzero
  linarith

/-- Sending one height to infinity gives the corresponding flattening inequality. -/
theorem HeightTest.load_le {m : Fin 3 → ℝ} {L : ℝ} (h : HeightTest m L) (i : Fin 3) :
    m i ≤ L := by
  by_contra! hsmall
  let x := (2 * L + 1) / (m i - L)
  have hx : 0 < x := div_pos (by linarith [h.nonneg]) (sub_pos.mpr hsmall)
  have hax := h.nonnegHeights (fun j => if j = i then x else 0)
    (fun j => by split <;> positivity)
  have hbound : x * m i ≤ L * (Real.sqrt (1 + x ^ 2) + 1) := by
    fin_cases i <;> simp [Fin.sum_univ_three] at hax ⊢ <;> linarith
  have hs : Real.sqrt (1 + x ^ 2) ≤ 1 + x := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  have hden : x * (m i - L) = 2 * L + 1 := div_mul_cancel₀ _ (sub_ne_zero.mpr hsmall.ne')
  nlinarith [mul_le_mul_of_nonneg_left hs h.nonneg]

private theorem minimizing_height {p b : ℝ} (hb : 0 ≤ b) (hbp : b < p) :
    let r := Real.sqrt (p ^ 2 - b ^ 2)
    p * Real.sqrt (1 + (b / r) ^ 2) - (b / r) * b = r := by
  dsimp only
  let r := Real.sqrt (p ^ 2 - b ^ 2)
  have hdiff : 0 < p ^ 2 - b ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hbp) (show 0 < p + b by linarith)]
  have hr : 0 < r := Real.sqrt_pos.2 hdiff
  have hrsq : r ^ 2 = p ^ 2 - b ^ 2 := Real.sq_sqrt hdiff.le
  have hs : Real.sqrt (1 + (b / r) ^ 2) = p / r := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (hb.trans hbp.le) hr.le)).mpr
    field_simp
    nlinarith
  change p * Real.sqrt (1 + (b / r) ^ 2) - (b / r) * b = r
  rw [hs]
  field_simp
  nlinarith

/-- Minimize each summand after increasing the rank parameter, then let it decrease to
its original value. This also handles sites with load equal to that parameter. -/
theorem HeightTest.radicalTest {m : Fin 3 → ℝ} {L : ℝ} (h : HeightTest m L)
    (hm : ∀ i, 0 ≤ m i) : RadicalTest m L := by
  refine ⟨h.load_le, ?_⟩
  apply le_at_right_endpoint (f := id) (g := fun p => ∑ i, Real.sqrt (p ^ 2 - m i ^ 2))
    continuous_id (by fun_prop)
  intro p hp
  let a i := m i / Real.sqrt (p ^ 2 - m i ^ 2)
  have htest := (h.mono hp.le).nonnegHeights a (fun i => div_nonneg (hm i) (Real.sqrt_nonneg _))
  have hmin : ∀ i, p * Real.sqrt (1 + a i ^ 2) - a i * m i = Real.sqrt (p ^ 2 - m i ^ 2) :=
    fun i => minimizing_height (hm i) (lt_of_le_of_lt (h.load_le i) hp)
  change p ≤ _
  simp only [← hmin, Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith

/-- The converse variational inequality follows from the two-dimensional Cauchy inequality. -/
theorem RadicalTest.heightTest {m : Fin 3 → ℝ} {L : ℝ} (h : RadicalTest m L)
    (hm : ∀ i, 0 ≤ m i) : HeightTest m L := by
  intro a ha
  have hL := (hm 0).trans (h.1 0)
  have hterm (i) : a i * m i + Real.sqrt (L ^ 2 - m i ^ 2) ≤
      L * Real.sqrt (1 + a i ^ 2) := by
    let r := Real.sqrt (L ^ 2 - m i ^ 2)
    have hr : r ^ 2 = L ^ 2 - m i ^ 2 := Real.sq_sqrt (by
      nlinarith [mul_nonneg (sub_nonneg.mpr (h.1 i)) (add_nonneg hL (hm i))])
    have hs : Real.sqrt (1 + a i ^ 2) ^ 2 = 1 + a i ^ 2 := Real.sq_sqrt (by positivity)
    change a i * m i + r ≤ _
    apply le_of_sq_le_sq _ (mul_nonneg hL (Real.sqrt_nonneg _))
    calc
      (a i * m i + r) ^ 2 ≤ (a i * m i + r) ^ 2 + (a i * r - m i) ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
      _ = (a i ^ 2 + 1) * (m i ^ 2 + r ^ 2) := by ring
      _ = _ := by rw [hr, mul_pow, hs]; ring
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  linarith [h.2]

theorem heightTest_iff_radicalTest {m : Fin 3 → ℝ} {L : ℝ} (hm : ∀ i, 0 ≤ m i) :
    HeightTest m L ↔ RadicalTest m L := ⟨(·.radicalTest hm), (·.heightTest hm)⟩

/-- Replacing log asymptotic rank by the logarithm of a larger rank measure
preserves both inequalities. -/
theorem RadicalTest.mono {m : Fin 3 → ℝ} {L U : ℝ} (h : RadicalTest m L)
    (hm : ∀ i, 0 ≤ m i) (hLU : L ≤ U) : RadicalTest m U :=
  ((h.heightTest hm).mono hLU).radicalTest hm

/-- For three equal loads of size two the radical inequality gives the
superquadratic exponent constant. -/
theorem square_lower_bound {L : ℝ} (h : RadicalTest (fun _ => 2) L) :
    3 / Real.sqrt 2 ≤ L := by
  have hL : 2 ≤ L := h.1 0
  have hrad := h.2
  simp only [Fin.sum_univ_three] at hrad
  have hsq := Real.sq_sqrt (show 0 ≤ L ^ 2 - 2 ^ 2 by nlinarith [sq_nonneg (L - 2)])
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply (div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))).mpr
  apply le_of_sq_le_sq _ (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
  rw [mul_pow, h2]
  nlinarith [sq_le_sq' (by linarith [Real.sqrt_nonneg (L ^ 2 - 2 ^ 2)] :
    -(3 * Real.sqrt (L ^ 2 - 2 ^ 2)) ≤ L) (by linarith : L ≤ 3 * Real.sqrt (L ^ 2 - 2 ^ 2))]

theorem loads_nonneg {w12 w23 w31 : ℝ} (h12 : 0 ≤ w12) (h23 : 0 ≤ w23)
    (h31 : 0 ≤ w31) (i : Fin 3) : 0 ≤ loads w12 w23 w31 i := by
  fin_cases i <;> dsimp [loads] <;> positivity

/-- The sum of the three wire weights always passes the radical test. -/
theorem radicalTest_of_totalWireLoad_le {w12 w23 w31 L : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) (htotal : w12 + w23 + w31 ≤ L) :
    RadicalTest (loads w12 w23 w31) L := by
  let m := loads w12 w23 w31
  have hbound (i : Fin 3) : m i ≤ L := by fin_cases i <;> dsimp [m, loads] <;> linarith
  have hterm (i : Fin 3) : L - m i ≤ Real.sqrt (L ^ 2 - m i ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    have hprod : 0 ≤ m i * (L - m i) :=
      mul_nonneg (loads_nonneg h12 h23 h31 i) (sub_nonneg.mpr (hbound i))
    nlinarith
  refine ⟨hbound, ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simp only [Fin.sum_univ_three] at hsum ⊢
  dsimp [m, loads] at hsum ⊢
  linarith

/-- At square order the log-rank bound is proportional to the base-two
logarithm of the order, including order one. -/
theorem square_log_lower_bound {b L : ℝ} (h : HeightTest (loads b b b) L) :
    3 / Real.sqrt 2 * b ≤ L := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hden : Real.sqrt (1 + (2 * Real.sqrt 2) ^ 2) = 3 := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by norm_num)).mpr
    nlinarith
  have hh := h (fun _ => 2 * Real.sqrt 2) (fun _ => by positivity)
  simp only [Fin.sum_univ_three, loads, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, hden] at hh
  change 2 * Real.sqrt 2 * (b + b) + 2 * Real.sqrt 2 * (b + b) +
    2 * Real.sqrt 2 * (b + b) ≤ L * (3 + 3 + 3 - 1) at hh
  have heq : 3 / Real.sqrt 2 = 3 * Real.sqrt 2 / 2 := by
    field_simp
    nlinarith
  rw [heq]
  linarith

/-- A square tensor with the finite height bound at rank measure r has
rank measure at least the stated power of its order. -/
theorem square_rpow_lower_bound {n r : ℝ} (hn : 0 < n) (hr : 0 < r)
    (h : let b := Real.logb 2 n; HeightTest (loads b b b) (Real.logb 2 r)) :
    n ^ (3 / Real.sqrt 2) ≤ r := by
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (Real.rpow_pos_of_pos hn _) hr).mp
  rw [Real.logb_rpow_eq_mul_logb_of_pos hn]
  exact square_log_lower_bound h

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.Scaling
section

/-! # Logarithmic scaling of rectangular wire dimensions -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter
open scoped Topology

noncomputable section

/-- The integer wire dimension at scale `N` and weight `w`. -/
def wireDimension (N : ℕ) (w : ℝ) : ℕ := ⌈(N : ℝ) ^ w⌉₊

theorem wireDimension_pos {N : ℕ} (hN : 0 < N) (w : ℝ) : 0 < wireDimension N w := by
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hN) _)

theorem wireDimension_log_ge {N : ℕ} (hN : 0 < N) (w : ℝ) :
    w * Real.logb 2 N ≤ Real.logb 2 (wireDimension N w) := by
  have h : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [← Real.logb_rpow_eq_mul_logb_of_pos h]
  exact Real.logb_le_logb_of_le (by norm_num) (Real.rpow_pos_of_pos h w) (Nat.le_ceil _)

theorem dyadic_wireDimension_log_ge (k : ℕ) (w : ℝ) :
    (k : ℝ) * w ≤ Real.logb 2 (wireDimension (2 ^ k) w) := by
  have h := wireDimension_log_ge (N := 2 ^ k) (by positivity) w
  push_cast at h
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, mul_comm] at h
  exact h

/-- For positive scales and nonnegative weights, rounding costs a factor of at most two. -/
theorem wireDimension_le {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw : 0 ≤ w) :
    (wireDimension N w : ℝ) ≤ 2 * (N : ℝ) ^ w := by
  have hp : 1 ≤ (N : ℝ) ^ w := Real.one_le_rpow (by exact_mod_cast hN) hw
  unfold wireDimension
  linarith [Nat.ceil_lt_add_one (zero_le_one.trans hp)]

/-- Rounding a wire dimension up adds at most one bit for nonnegative weights. -/
theorem wireDimension_log_le {N : ℕ} (hN : 0 < N) {w : ℝ} (hw : 0 ≤ w) :
    Real.logb 2 (wireDimension N w) ≤ 1 + w * Real.logb 2 N := by
  calc
    _ ≤ Real.logb 2 (2 * (N : ℝ) ^ w) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast wireDimension_pos hN w) (wireDimension_le hN hw)
    _ = _ := by rw [Real.logb_mul (by norm_num) (by positivity),
      Real.logb_self_eq_one (by norm_num), Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]

/-- The normalized logarithmic dimension converges to the wire weight. -/
theorem tendsto_log_wireDimension_div {w : ℝ} (hw : 0 ≤ w) :
    Tendsto (fun N : ℕ ↦ Real.logb 2 (wireDimension N w) / Real.logb 2 N) atTop (𝓝 w) := by
  have ht : Tendsto (fun N : ℕ ↦ (Real.logb 2 N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((Real.tendsto_logb_atTop (by norm_num)).comp
      tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun N : ℕ ↦ (Real.logb 2 N)⁻¹ + w) atTop (𝓝 w) by
      simpa using ht.add_const w)
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hd := Real.logb_pos (b := 2) (by norm_num) (x := (N : ℝ)) (by exact_mod_cast hN)
    exact (le_div_iff₀ hd).mpr (wireDimension_log_ge (by omega) w)
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hd := Real.logb_pos (b := 2) (by norm_num) (x := (N : ℝ)) (by exact_mod_cast hN)
    apply (div_le_iff₀ hd).mpr
    rw [add_mul, inv_mul_cancel₀ hd.ne']
    exact wireDimension_log_le (by omega) hw

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.Asymptotic
section

/-! # From finite height bounds to arithmetic exponents

Evaluate the finite bound at base sizes `2 ^ k`. Rounding each dimension
up only increases its logarithmic load. The logarithm of a constant in
a polynomial cost bound contributes a fixed additive term, which disappears
when the inequality holds at every dyadic scale.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

noncomputable section

/-- Logarithmic site loads at the three rounded wire dimensions of base size `N`. -/
def scaledLoads (N : ℕ) (w12 w23 w31 : ℝ) : Fin 3 → ℝ :=
  loads (Real.logb 2 (wireDimension N w12)) (Real.logb 2 (wireDimension N w23))
    (Real.logb 2 (wireDimension N w31))

/-- The dyadic loads dominate the real weights multiplied by the scale exponent. -/
theorem dyadic_load_le (k : ℕ) (w12 w23 w31 : ℝ) (i : Fin 3) :
    (k : ℝ) * loads w12 w23 w31 i ≤ scaledLoads (2 ^ k) w12 w23 w31 i := by
  fin_cases i <;> dsimp [scaledLoads, loads] <;> rw [mul_add] <;>
    exact add_le_add (dyadic_wireDimension_log_ge _ _) (dyadic_wireDimension_log_ge _ _)

/-- A uniform polynomial bound at dyadic scales forces the growth exponent
to dominate the slope, independently of the multiplicative constant. -/
theorem le_of_dyadic_log_bound {u τ : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      (k : ℝ) * u ≤ Real.logb 2 (C * ((2 ^ k : ℕ) : ℝ) ^ (τ + ε))) : u ≤ τ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨C, hC, hk⟩ := h ε hε
  by_contra! hlt
  obtain ⟨k, hlarge⟩ := exists_lt_nsmul (sub_pos.mpr hlt) (Real.logb 2 C)
  rw [nsmul_eq_mul] at hlarge
  have hbound := hk k
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_mul hC.ne' (by positivity),
    Real.logb_rpow_eq_mul_logb_of_pos (by positivity), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one] at hbound
  nlinarith only [hlarge, hbound]

/-- A polynomial upper bound on the finite height-test parameter implies
the corresponding test on exponent loads, with all positive slack removed. -/
theorem heightTest_of_polynomial_bound {w12 w23 w31 τ : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      HeightTest (scaledLoads N w12 w23 w31) (Real.logb 2 (C * (N : ℝ) ^ (τ + ε)))) :
    HeightTest (loads w12 w23 w31) τ := by
  intro a ha
  let M := ∑ i, a i * loads w12 w23 w31 i
  let D := ∑ i, Real.sqrt (1 + a i ^ 2) - 1
  have hD : 0 < D := heightDenom_pos a
  change M ≤ τ * D
  apply (div_le_iff₀ hD).mp
  apply le_of_dyadic_log_bound
  intro ε hε
  obtain ⟨C, hC, hN⟩ := h ε hε
  refine ⟨C, hC, fun k => ?_⟩
  rw [← mul_div_assoc, div_le_iff₀ hD]
  have hstep : (k : ℝ) * M ≤ ∑ i, a i * scaledLoads (2 ^ k) w12 w23 w31 i := by
    dsimp only [M]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (dyadic_load_le k _ _ _ i) (ha i).le
  exact hstep.trans (hN (2 ^ k) (Nat.one_le_pow _ _ (by decide)) a ha)

/-- Height tests pass to the infimum of any nonempty set of admissible exponents. -/
theorem heightTest_sInf {m : Fin 3 → ℝ} {S : Set ℝ} (hS : S.Nonempty)
    (h : ∀ τ ∈ S, HeightTest m τ) : HeightTest m (sInf S) := by
  intro a ha
  have hD := heightDenom_pos a
  apply (div_le_iff₀ hD).mp
  exact le_csInf hS fun τ hτ => (div_le_iff₀ hD).mpr (h τ hτ a ha)

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.MatrixMultiplication.Model
section

namespace OAI

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

inductive Gate (F Input Register : Type*) where
  | constant : F → Gate F Input Register
  | input : Input → Gate F Input Register
  | add : Register → Register → Gate F Input Register
  | sub : Register → Register → Gate F Input Register
  | mul : Register → Register → Gate F Input Register

namespace Gate

variable {F Input Register : Type*}

def cost : Gate F Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

def eval [Field F] (inputs : Input → F) (registers : Register → F) :
    Gate F Input Register → F
  | .constant z => z
  | .input i => inputs i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

abbrev eval.match_1 := @cost.match_1

end Gate

inductive Program (F Input : Type*) : ℕ → Type _ where
  | nil : Program F Input 0
  | step {r : ℕ} : Program F Input r → Gate F Input (Fin r) → Program F Input (r + 1)

namespace Program

variable {F Input : Type*}

def eval [Field F] : {r : ℕ} → Program F Input r → (Input → F) → Fin r → F
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p g, inputs =>
    Fin.cases (g.eval inputs (p.eval inputs)) (p.eval inputs)

def cost : {r : ℕ} → Program F Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

end Program

abbrev MatrixInput (a b c : ℕ) := (Fin a × Fin b) ⊕ (Fin b × Fin c)

def matrixInputs {F : Type*} {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    MatrixInput a b c → F
  | .inl (i, j) => A i j
  | .inr (j, k) => B j k

structure MatrixAlgorithm (F : Type*) (a b c : ℕ) where
  registers : ℕ
  program : Program F (MatrixInput a b c) registers
  output : Fin a → Fin c → Fin registers

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

def eval (P : MatrixAlgorithm F a b c)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    Matrix (Fin a) (Fin c) F :=
  fun i k => P.program.eval (matrixInputs A B) (P.output i k)

def Correct (P : MatrixAlgorithm F a b c) : Prop :=
  ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F), P.eval A B = A * B

def cost (P : MatrixAlgorithm F a b c) : ℕ := P.program.cost

end MatrixAlgorithm

/-- Positive slack, one uniform constant, and a correct program at every size. -/
def AdmissibleExponent (F : Type*) [Field F] (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n n n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

def omega (F : Type*) [Field F] : ℝ := sInf {τ : ℝ | AdmissibleExponent F τ}

/-- The inner dimension of an `n × n^k` by `n^k × n` multiplication. -/
def innerSize (n : ℕ) (k : ℝ) : ℕ := ⌈(n : ℝ) ^ k⌉₊

def RectangularAdmissibleExponent (F : Type*) [Field F] (k τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

def rectangularOmega (F : Type*) [Field F] (k : ℝ) : ℝ :=
  sInf {τ : ℝ | RectangularAdmissibleExponent F k τ}

/-- The dual exponent is a supremum of exact exponent-two rectangular shapes. -/
def complexAlpha : ℝ :=
  sSup {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2}

end MatrixMultiplication.Arithmetic

end

end OAI
end

-- Source module: OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Complexity
section

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace Gate

variable {F Input Register : Type*}

end Gate

namespace Program

variable {F Input : Type*}

@[simp] theorem eval_step_zero [Field F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

@[simp] theorem eval_step_succ [Field F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

@[simp] theorem cost_step {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

theorem correct_iff_entries (P : MatrixAlgorithm F a b c) :
    P.Correct ↔ ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F)
      (i : Fin a) (k : Fin c),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k := by
  constructor
  · intro h A B i k
    exact congrFun (congrFun (h A B) i) k
  · intro h A B
    funext i k
    exact h A B i k

end MatrixAlgorithm

def scalarAlgorithm (F : Type*) [Field F] : MatrixAlgorithm F 1 1 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

theorem scalarAlgorithm_correct (F : Type*) [Field F] : (scalarAlgorithm F).Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

@[simp] theorem scalarAlgorithm_cost (F : Type*) [Field F] : (scalarAlgorithm F).cost = 1 := rfl

theorem one_le_innerSize {n : ℕ} (hn : 1 ≤ n) (k : ℝ) : 1 ≤ innerSize n k := by
  apply Nat.one_le_ceil_iff.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)) k

@[simp] theorem innerSize_zero (n : ℕ) : innerSize n 0 = 1 := by
  simp [innerSize]

@[simp] theorem innerSize_one (n : ℕ) : innerSize n 1 = n := by
  simp [innerSize]

theorem innerSize_mono {n : ℕ} (hn : 1 ≤ n) {k l : ℝ} (hkl : k ≤ l) :
    innerSize n k ≤ innerSize n l := by
  exact Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hkl)

theorem innerSize_le_pow {a b n t : ℕ} {k : ℝ} (hk : 0 ≤ k)
    (hn : n ≤ a ^ t) (hab : (a : ℝ) ^ k ≤ b) : innerSize n k ≤ b ^ t := by
  apply Nat.ceil_le.mpr
  calc
    (n : ℝ) ^ k ≤ ((a ^ t : ℕ) : ℝ) ^ k :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hk
    _ = ((a : ℝ) ^ k) ^ t := by
      rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg a)]
    _ ≤ (b : ℝ) ^ t := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
    _ = ((b ^ t : ℕ) : ℝ) := by rw [Nat.cast_pow]

theorem innerSize_cast_le {n : ℕ} (hn : 1 ≤ n) {k : ℝ} (hk : 0 ≤ k) :
    (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ k := by
  have hpow : 1 ≤ (n : ℝ) ^ k := Real.one_le_rpow (by exact_mod_cast hn) hk
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) k)).le
  change (⌈(n : ℝ) ^ k⌉₊ : ℝ) ≤ _
  linarith

end MatrixMultiplication.Arithmetic

end

end OAI
end

-- Source module: OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Programs
section

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.Arithmetic

namespace Gate

variable {F : Type*} [Field F] {Input R S : Type*}

def mapRegister (f : R → S) : Gate F Input R → Gate F Input S
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add (f i) (f j)
  | .sub i j => .sub (f i) (f j)
  | .mul i j => .mul (f i) (f j)

theorem eval_mapRegister (g : Gate F Input R) (f : R → S)
    (inputs : Input → F) (registers : S → F) :
    (g.mapRegister f).eval inputs registers = g.eval inputs (fun i => registers (f i)) := by
  cases g <;> rfl

omit [Field F] in
@[simp] theorem cost_mapRegister (g : Gate F Input R) (f : R → S) :
    (g.mapRegister f).cost = g.cost := by
  cases g <;> rfl

end Gate

namespace Program

variable {F : Type*} [Field F] {Input : Type*}

def oldIndex (r s : ℕ) (i : Fin r) : Fin (r + s) := ⟨s + i.val, by omega⟩

def newIndex (r s : ℕ) (i : Fin s) : Fin (r + s) := ⟨i.val, by omega⟩

@[simp] theorem oldIndex_zero (r : ℕ) (i : Fin r) : oldIndex r 0 i = i := by
  apply Fin.ext
  simp [oldIndex]

@[simp] theorem oldIndex_succ (r s : ℕ) (i : Fin r) :
    oldIndex r (s + 1) i = (oldIndex r s i).succ := by
  apply Fin.ext
  simp only [oldIndex, Fin.val_succ]
  omega

@[simp] theorem newIndex_zero (r s : ℕ) : newIndex r (s + 1) 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem newIndex_succ (r s : ℕ) (i : Fin s) :
    newIndex r (s + 1) i.succ = (newIndex r s i).succ := by
  apply Fin.ext
  rfl

def append {r : ℕ} (p : Program F Input r) : {s : ℕ} → Program F Input s → Program F Input (r + s)
  | 0, .nil => p
  | s + 1, .step q g => (p.append q).step (g.mapRegister (newIndex r s))

theorem eval_append_new {r s : ℕ} (p : Program F Input r) (q : Program F Input s)
    (inputs : Input → F) :
    ∀ i : Fin s, (p.append q).eval inputs (newIndex r s i) = q.eval inputs i := by
  induction q with
  | nil => intro i; exact Fin.elim0 i
  | @step s q g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [append, newIndex_zero, eval_step_zero, Gate.eval_mapRegister]
      rw [funext ih]
    · simpa only [append, newIndex_succ, eval_step_succ] using ih j

theorem eval_append_old {r s : ℕ} (p : Program F Input r) (q : Program F Input s)
    (inputs : Input → F) :
    ∀ i : Fin r, (p.append q).eval inputs (oldIndex r s i) = p.eval inputs i := by
  induction q with
  | nil => intro i; simp [append]
  | @step s q g ih =>
    intro i
    simpa only [append, oldIndex_succ, eval_step_succ] using ih i

omit [Field F] in
@[simp] theorem cost_append {r s : ℕ} (p : Program F Input r) (q : Program F Input s) :
    (p.append q).cost = p.cost + q.cost := by
  induction q with
  | nil => simp [append, cost]
  | @step s q g ih => simp [append, ih, Nat.add_assoc]

end Program

inductive Expression (F Input : Type*) where
  | constant : F → Expression F Input
  | input : Input → Expression F Input
  | add : Expression F Input → Expression F Input → Expression F Input
  | sub : Expression F Input → Expression F Input → Expression F Input
  | mul : Expression F Input → Expression F Input → Expression F Input

namespace Expression

variable {F : Type*} [Field F] {Input : Type*}

def cost : Expression F Input → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add e f => e.cost + f.cost + 1
  | .sub e f => e.cost + f.cost + 1
  | .mul e f => e.cost + f.cost + 1

def eval (inputs : Input → F) : Expression F Input → F
  | .constant z => z
  | .input i => inputs i
  | .add e f => e.eval inputs + f.eval inputs
  | .sub e f => e.eval inputs - f.eval inputs
  | .mul e f => e.eval inputs * f.eval inputs

-- Keep the matcher name referenced by existing compiled modules.
abbrev eval.match_1 := @cost.match_1

structure Compiled (e : Expression F Input) where
  registers : ℕ
  program : Program F Input registers
  output : Fin registers
  correct : ∀ inputs, program.eval inputs output = e.eval inputs
  cost_eq : program.cost = e.cost

def compile : (e : Expression F Input) → Compiled e
  | .constant z =>
    { registers := 1
      program := Program.nil.step (.constant z)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .input i =>
    { registers := 1
      program := Program.nil.step (.input i)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .add e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.add (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .sub e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.sub (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .mul e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.mul (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }

end Expression
end MatrixMultiplication.Arithmetic

namespace LinearAlgebra.SpectralBooks

open MatrixMultiplication.Arithmetic MvPolynomial

variable {F I : Type*} [Field F]

/-- The formal polynomial represented by an arithmetic expression. Kept with `Expression.cost`
so Lean compiles the two recursions with the same matcher as the ArithmeticHierarchy challenge. -/
def expressionPolynomial : Expression F I → MvPolynomial I F
  | .constant z => C z
  | .input i => X i
  | .add e f => expressionPolynomial e + expressionPolynomial f
  | .sub e f => expressionPolynomial e - expressionPolynomial f
  | .mul e f => expressionPolynomial e * expressionPolynomial f

end LinearAlgebra.SpectralBooks

end

end OAI
end

-- Source module: OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ExpressionFamily
section

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic.Expression

variable {F : Type*} [Field F]

variable {Input Output : Type*}

structure CompiledFamily [Fintype Output] (expressions : Output → Expression F Input) where
  registers : ℕ
  program : Program F Input registers
  output : Output → Fin registers
  correct : ∀ inputs i, program.eval inputs (output i) = (expressions i).eval inputs
  cost_eq : program.cost = ∑ i, (expressions i).cost

def compileFinFamily : (n : ℕ) → (expressions : Fin n → Expression F Input) →
    CompiledFamily expressions
  | 0, _ =>
    { registers := 0
      program := Program.nil
      output := Fin.elim0
      correct := by
        intro inputs i
        exact Fin.elim0 i
      cost_eq := by simp [Program.cost] }
  | n + 1, expressions =>
    let p := compile (expressions 0)
    let q := compileFinFamily n (fun i => expressions i.succ)
    { registers := p.registers + q.registers
      program := p.program.append q.program
      output := Fin.cases (Program.oldIndex _ _ p.output)
        (fun i => Program.newIndex _ _ (q.output i))
      correct := by
        intro inputs i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (Program.eval_append_old p.program q.program inputs p.output).trans
            (p.correct inputs)
        · exact (Program.eval_append_new p.program q.program inputs (q.output j)).trans
            (q.correct inputs j)
      cost_eq := by
        rw [Program.cost_append, p.cost_eq, q.cost_eq, Fin.sum_univ_succ] }

def compileFamily [Fintype Output] (expressions : Output → Expression F Input) :
    CompiledFamily expressions :=
  let e := Fintype.equivFin Output
  let p := compileFinFamily (Fintype.card Output) (fun i => expressions (e.symm i))
  { registers := p.registers
    program := p.program
    output := fun i => p.output (e i)
    correct := by
      intro inputs i
      simpa only [Equiv.symm_apply_apply] using p.correct inputs (e i)
    cost_eq := by
      rw [p.cost_eq]
      exact e.symm.sum_comp (fun i => (expressions i).cost) }

end MatrixMultiplication.Arithmetic.Expression

end

end OAI
end

-- Source module: OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm
section

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Expression

variable {Input : Type*}

def sumFin : {n : ℕ} → (Fin n → Expression F Input) → Expression F Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin (fun i : Fin n => f i.succ))

theorem sumFin_eval {n : ℕ} (f : Fin n → Expression F Input) (inputs : Input → F) :
    (sumFin f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, eval]
  | succ n ih => simp [sumFin, eval, ih, Fin.sum_univ_succ]

theorem sumFin_cost {n : ℕ} (f : Fin n → Expression F Input) :
    (sumFin f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, cost]
  | succ n ih =>
    simp only [sumFin, cost, ih, Fin.sum_univ_succ]
    omega

end Expression

def naiveEntry {a b c : ℕ} (i : Fin a) (k : Fin c) : Expression F (MatrixInput a b c) :=
  Expression.sumFin fun j : Fin b =>
    .mul (.input (.inl (i, j))) (.input (.inr (j, k)))

theorem naiveEntry_eval {a b c : ℕ} (i : Fin a) (k : Fin c)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    (naiveEntry i k).eval (matrixInputs A B) = ∑ j, A i j * B j k := by
  simp [naiveEntry, Expression.sumFin_eval, Expression.eval, matrixInputs]

@[simp] theorem naiveEntry_cost {a b c : ℕ} (i : Fin a) (k : Fin c) :
    (naiveEntry (F := F) (b := b) i k).cost = 2 * b := by
  simp [naiveEntry, Expression.sumFin_cost, Expression.cost, two_mul]

def naiveAlgorithm (a b c : ℕ) : MatrixAlgorithm F a b c :=
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (b := b) ik.1 ik.2)
  { registers := p.registers
    program := p.program
    output := fun i k => p.output (i, k) }

theorem naiveAlgorithm_correct (a b c : ℕ) : (naiveAlgorithm (F := F) a b c).Correct := by
  apply (MatrixAlgorithm.correct_iff_entries _).2
  intro A B i k
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.eval (matrixInputs A B) (p.output (i, k)) = _
  rw [p.correct]
  exact naiveEntry_eval i k A B

@[simp] theorem naiveAlgorithm_cost (a b c : ℕ) :
    (naiveAlgorithm (F := F) a b c).cost = 2 * a * b * c := by
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.cost = _
  rw [p.cost_eq]
  simp only [naiveEntry_cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem naiveAlgorithm_cost_le (a b c : ℕ) :
    (naiveAlgorithm (F := F) a b c).cost ≤ 2 * a * b * c :=
  (naiveAlgorithm_cost a b c).le

theorem admissibleExponent_three : AdmissibleExponent F 3 := by
  intro ε hε
  refine ⟨2, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveAlgorithm n n n, naiveAlgorithm_correct n n n, ?_⟩
  rw [naiveAlgorithm_cost]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ (3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR (le_add_of_nonneg_right hε.le)
  calc
    ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℝ) := by
      calc
        ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℕ) := by
          push_cast
          ring
        _ = 2 * (n : ℝ) ^ (3 : ℝ) :=
          congrArg (fun t : ℝ => 2 * t) (Real.rpow_natCast (n : ℝ) 3).symm
    _ ≤ 2 * (n : ℝ) ^ (3 + ε) := mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem admissibleExponent_nonempty : Set.Nonempty {τ : ℝ | AdmissibleExponent F τ} :=
  ⟨3, admissibleExponent_three⟩

end MatrixMultiplication.Arithmetic

end

end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.FormalCircuit
section

/-! # Formal polynomial semantics for division-free arithmetic circuits

Registers in the repository's straight-line programs can be interpreted in the
polynomial ring on the inputs. This distinguishes formal identities over a finite
field from equality of polynomial functions on its rational points.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial
open scoped BigOperators
noncomputable section

variable {F I R : Type*} [CommRing F]

/-- The polynomial produced at one gate from the polynomials in its registers. -/
def gatePolynomial (g : Gate F I R) (v : R → MvPolynomial I F) : MvPolynomial I F :=
  g.casesOn (fun c => C c) (fun i => X i)
    (fun i j => v i + v j) (fun i j => v i - v j) (fun i j => v i * v j)

/-- Formal polynomial in each register of a straight-line program. -/
def registerPolynomial : {r : ℕ} → Program F I r → Fin r → MvPolynomial I F
  | _, .nil => Fin.elim0
  | _, .step p g => Fin.cases (gatePolynomial g (registerPolynomial p)) (registerPolynomial p)

@[simp] theorem registerPolynomial_zero {r : ℕ} (p : Program F I r) (g : Gate F I (Fin r)) :
    registerPolynomial (p.step g) 0 = gatePolynomial g (registerPolynomial p) := rfl

@[simp] theorem registerPolynomial_succ {r : ℕ} (p : Program F I r) (g : Gate F I (Fin r))
    (i : Fin r) : registerPolynomial (p.step g) i.succ = registerPolynomial p i := rfl

/-- Formal correctness in the paper, including over a finite ground field. -/
def FormalCorrect {a b c : ℕ} (P : MatrixAlgorithm F a b c) : Prop :=
  ∀ i k, registerPolynomial P.program (P.output i k) =
    ∑ j : Fin b, X (Sum.inl (i, j)) * X (Sum.inr (j, k))

private theorem gatePolynomial_mapRegister {S : Type*} (f : R → S)
    (v : S → MvPolynomial I F) (g : Gate F I R) :
    gatePolynomial (g.mapRegister f) v = gatePolynomial g (v ∘ f) := by
  cases g <;> rfl

theorem registerPolynomial_append_new {r s : ℕ} (p : Program F I r)
    (q : Program F I s) (i : Fin s) :
    registerPolynomial (p.append q) (Program.newIndex r s i) = registerPolynomial q i := by
  induction q with
  | nil => exact i.elim0
  | @step s q g ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Program.append, Program.newIndex_zero, registerPolynomial_zero,
        gatePolynomial_mapRegister]
      congr 1
      exact funext ih
    · simpa only [Program.append, Program.newIndex_succ, registerPolynomial_succ] using ih j

theorem registerPolynomial_append_old {r s : ℕ} (p : Program F I r)
    (q : Program F I s) (i : Fin r) :
    registerPolynomial (p.append q) (Program.oldIndex r s i) = registerPolynomial p i := by
  induction q with
  | nil => simp [Program.append]
  | @step s q g ih =>
    simpa only [Program.append, Program.oldIndex_succ, registerPolynomial_succ] using ih

end

noncomputable section

variable {F I : Type*} [Field F]

-- Keep the matcher name exported by earlier builds of this module.
abbrev expressionPolynomial.match_1 := @Expression.cost.match_1

theorem registerPolynomial_compile (e : Expression F I) :
    registerPolynomial e.compile.program e.compile.output = expressionPolynomial e := by
  induction e <;> simp_all [Expression.compile, expressionPolynomial, gatePolynomial,
    registerPolynomial_append_old, registerPolynomial_append_new]

private theorem registerPolynomial_compileFinFamily (n : ℕ) (f : Fin n → Expression F I)
    (i : Fin n) :
    registerPolynomial (Expression.compileFinFamily n f).program
      ((Expression.compileFinFamily n f).output i) = expressionPolynomial (f i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Expression.compileFinFamily, registerPolynomial_append_old, registerPolynomial_compile]
    · simp [Expression.compileFinFamily, registerPolynomial_append_new, ih]

theorem registerPolynomial_compileFamily {O : Type*} [Fintype O]
    (f : O → Expression F I) (i : O) :
    registerPolynomial (Expression.compileFamily f).program ((Expression.compileFamily f).output i)
      = expressionPolynomial (f i) := by
  simp [Expression.compileFamily, registerPolynomial_compileFinFamily]

theorem expressionPolynomial_sumFin {n : ℕ} (f : Fin n → Expression F I) :
    expressionPolynomial (Expression.sumFin f) = ∑ i, expressionPolynomial (f i) := by
  induction n with
  | zero => simp [Expression.sumFin, expressionPolynomial]
  | succ n ih => simp [Expression.sumFin, expressionPolynomial, ih, Fin.sum_univ_succ]

/-- The usual entrywise algorithm computes the formal matrix product over every field. -/
theorem formalCorrect_naiveAlgorithm (F : Type*) [Field F] (a b c : ℕ) :
    FormalCorrect (naiveAlgorithm (F := F) a b c) := by
  intro i k
  simp [naiveAlgorithm, registerPolynomial_compileFamily, naiveEntry, expressionPolynomial_sumFin,
    expressionPolynomial]

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.Circuit
section

/-! # From formal scalar circuits to tensor rank

At a product gate only two new products of linear forms enter the bidegree
`(1,1)` component. We maintain one shared list of these products across *all*
registers, so fan-out and multiple matrix entries incur no additional cost.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic Foundation MvPolynomial
open scoped BigOperators
noncomputable section

variable {F A B I R : Type*} [Field F]

/-- Number of scalar multiplication gates. Register loads, additions and
subtractions contribute zero. -/
def multiplicationCount : {r : ℕ} → Program F I r → ℕ
  | _, .nil => 0
  | _, .step p (.mul _ _) => multiplicationCount p + 1
  | _, .step p _ => multiplicationCount p

omit [Field F] in
theorem multiplicationCount_le_cost {r : ℕ} (p : Program F I r) :
    multiplicationCount p ≤ p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => cases g <;> simp [multiplicationCount, Gate.cost] <;> omega

private abbrev InputPoly (F A B : Type*) [Field F] := MvPolynomial (A ⊕ B) F

/-- The coefficient of the squarefree monomial indexed by a left and a right input. -/
def mixedPart (p : InputPoly F A B) (x : A) (y : B) : F :=
  constantCoeff (pderiv (Sum.inr y) (pderiv (Sum.inl x) p))

private def leftPart (p : InputPoly F A B) (x : A) : F :=
  constantCoeff (pderiv (Sum.inl x) p)

private def rightPart (p : InputPoly F A B) (y : B) : F :=
  constantCoeff (pderiv (Sum.inr y) p)

private theorem mixedPart_mul (p q : InputPoly F A B) (x : A) (y : B) :
    mixedPart (p * q) x y =
      constantCoeff q * mixedPart p x y + constantCoeff p * mixedPart q x y +
        leftPart p x * rightPart q y + leftPart q x * rightPart p y := by
  simp only [mixedPart, leftPart, rightPart, pderiv_mul, map_add, map_mul]
  ring

private theorem mixedPart_X (s : A ⊕ B) (x : A) (y : B) :
    mixedPart (X s : InputPoly F A B) x y = 0 := by
  classical
  by_cases h : s = Sum.inl x
  · subst s
    simp [mixedPart]
  · simp [mixedPart, pderiv_X_of_ne h]

/-- A common collection of products can be linearly recombined to give this register. -/
private def InProductSpan {r : ℕ} (a : Fin r → A → F) (b : Fin r → B → F)
    (p : InputPoly F A B) : Prop :=
  ∃ c : Fin r → F, ∀ x y, mixedPart p x y = ∑ t, a t x * b t y * c t

private theorem inProductSpan_add {r : ℕ} {a : Fin r → A → F} {b : Fin r → B → F}
    {p q : InputPoly F A B} (hp : InProductSpan a b p) (hq : InProductSpan a b q) :
    InProductSpan a b (p + q) := by
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  refine ⟨c + d, fun x y => ?_⟩
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ← hc, ← hd, mixedPart, map_add]

private theorem inProductSpan_sub {r : ℕ} {a : Fin r → A → F} {b : Fin r → B → F}
    {p q : InputPoly F A B} (hp : InProductSpan a b p) (hq : InProductSpan a b q) :
    InProductSpan a b (p - q) := by
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  refine ⟨c - d, fun x y => ?_⟩
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, ← hc, ← hd, mixedPart, map_sub]

private theorem inProductSpan_insert {r : ℕ} {a : Fin r → A → F} {b : Fin r → B → F}
    {p : InputPoly F A B} (hp : InProductSpan a b p) (u : A → F) (v : B → F) :
    InProductSpan (Fin.cons u a) (Fin.cons v b) p := by
  obtain ⟨c, hc⟩ := hp
  refine ⟨Fin.cons 0 c, fun x y => ?_⟩
  simp [Fin.sum_univ_succ, hc]

private theorem inProductSpan_mul {r : ℕ} {a : Fin r → A → F} {b : Fin r → B → F}
    {p q : InputPoly F A B} (hp : InProductSpan a b p) (hq : InProductSpan a b q) :
    InProductSpan (Fin.cons (leftPart p) (Fin.cons (leftPart q) a))
      (Fin.cons (rightPart q) (Fin.cons (rightPart p) b)) (p * q) := by
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  refine ⟨Fin.cons 1 (Fin.cons 1 (fun t => constantCoeff q * c t + constantCoeff p * d t)),
    fun x y => ?_⟩
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_one, mixedPart_mul,
    hc, hd, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  ring_nf

private theorem registerProducts {r : ℕ} (p : Program F (A ⊕ B) r) :
    ∃ (a : Fin (2 * multiplicationCount p) → A → F) (b : Fin (2 * multiplicationCount p) → B → F),
      ∀ i, InProductSpan a b (registerPolynomial p i) := by
  induction p with
  | nil => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0⟩
  | step p g ih =>
    obtain ⟨a, b, hab⟩ := ih
    cases g with
    | constant z =>
      refine ⟨a, b, Fin.cases ?_ hab⟩
      refine ⟨0, fun x y => ?_⟩
      simp [gatePolynomial, mixedPart]
    | input s =>
      refine ⟨a, b, Fin.cases ?_ hab⟩
      refine ⟨0, fun x y => ?_⟩
      simp [gatePolynomial, mixedPart_X]
    | add i j => exact ⟨a, b, Fin.cases (inProductSpan_add (hab i) (hab j)) hab⟩
    | sub i j => exact ⟨a, b, Fin.cases (inProductSpan_sub (hab i) (hab j)) hab⟩
    | mul i j =>
      simp only [multiplicationCount]
      refine ⟨_, _, Fin.cases (inProductSpan_mul (hab i) (hab j)) (fun k => ?_)⟩
      exact inProductSpan_insert (inProductSpan_insert (hab k) _ _) _ _

private theorem matrixEntry_mixedPart {a b c : ℕ} (i : Fin a) (k : Fin c)
    (x : Fin a × Fin b) (y : Fin b × Fin c) :
    mixedPart (∑ j : Fin b, X (Sum.inl (i,j)) * X (Sum.inr (j,k)) : InputPoly F _ _) x y =
      matrixTensor F b c a x y (k, i) := by
  classical
  rcases x with ⟨u, v⟩
  rcases y with ⟨w, z⟩
  simp [mixedPart, map_sum, pderiv_X, Pi.single_apply, apply_ite,
    Tensor.matrixCoefficients, Prod.ext_iff, ite_and, eq_comm]
  split_ifs <;> simp_all

/-- A formal division-free rectangular matrix multiplication circuit with `s`
products gives an exact rank decomposition with at most `2s` simple tensors. -/
theorem matrixTensor_rank_le_twice_multiplicationCount {a b c : ℕ} {P : MatrixAlgorithm F a b c}
    (h : FormalCorrect P) : tensorRank (matrixTensor F b c a) ≤ 2 * multiplicationCount P.program := by
  classical
  obtain ⟨u, v, huv⟩ := registerProducts P.program
  choose w hw using huv
  apply tensorRank_le_of_rankAtMost
  refine ⟨u, v, fun t z => w (P.output z.2 z.1) t, ?_⟩
  funext x y z
  rw [← matrixEntry_mixedPart, ← h z.2 z.1]
  exact hw _ _ _

/-- The total number of operations also bounds the rank, with the same factor two. -/
theorem matrixTensor_rank_le_twice_cost {a b c : ℕ} {P : MatrixAlgorithm F a b c}
    (h : FormalCorrect P) : tensorRank (matrixTensor F b c a) ≤ 2 * P.cost :=
  (matrixTensor_rank_le_twice_multiplicationCount h).trans
    (Nat.mul_le_mul_left 2 (multiplicationCount_le_cost _))

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.MatrixMinors
section

/-! # Identity minors of the matrix multiplication tensor

Fixing the wire opposite a site selects a square submatrix of its flattening
with one row for every local index. The matching-wire rule makes this
submatrix the identity, independently of the scalar characteristic.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation.Tensor

variable {K A B C : Type*} [CommSemiring K] [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- Fix the third wire and read off both indices of the first site. -/
theorem matrixMinor₁ (k : C) :
    Matrix.of (fun x x' : A × B =>
      matrixCoefficients (K := K) A B C x (x'.2, k) (k, x'.1)) = 1 := by
  ext x x'
  simp only [Matrix.of_apply, matrixCoefficients, Matrix.one_apply, Prod.ext_iff]
  by_cases ha : x.1 = x'.1 <;> by_cases hb : x.2 = x'.2 <;> simp_all [eq_comm]

/-- Fix the first wire and read off both indices of the second site. -/
theorem matrixMinor₂ (i : A) :
    Matrix.of (fun y y' : B × C =>
      matrixCoefficients (K := K) A B C (i, y'.1) y (y'.2, i)) = 1 := by
  ext y y'
  simp only [Matrix.of_apply, matrixCoefficients, Matrix.one_apply, Prod.ext_iff]
  by_cases hb : y.1 = y'.1 <;> by_cases hc : y.2 = y'.2 <;> simp_all [eq_comm]

/-- Fix the second wire and read off both indices of the third site. -/
theorem matrixMinor₃ (j : B) :
    Matrix.of (fun z z' : C × A =>
      matrixCoefficients (K := K) A B C (z'.2, j) (j, z'.1) z) = 1 := by
  ext z z'
  simp only [Matrix.of_apply, matrixCoefficients, Matrix.one_apply, Prod.ext_iff]
  by_cases hc : z.1 = z'.1 <;> by_cases ha : z.2 = z'.2 <;> simp_all [eq_comm]

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.Flattening
section

/-! # Flattening lower bounds in finite rectangular formats

Each flattening contains an identity minor. Applying the argument to powers,
whose wire indices are tuples, preserves the lower bound on taking roots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section

open MatrixMultiplication.Foundation

section Finite

variable {F A B C : Type*} [Field F] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

omit [Fintype B] in
private theorem card_last_le_rank {r : ℕ} (b : B)
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) A B C) r) :
    Fintype.card C * Fintype.card A ≤ r := by
  rw [← Fintype.card_prod]
  apply h.card_le_of_identity (fun i : C × A => (i.2, b)) (fun i => (b, i.1)) id
  intro i j
  have hh := congrFun (congrFun (matrixMinor₃ (K := F) (A := A) (C := C) b) j) i
  simpa [Matrix.one_apply, eq_comm] using hh

/-- A rank decomposition bounds the cardinalities of all three local bases. -/
theorem matrixCoefficients_flattenings {r : ℕ} (a : A) (b : B) (c : C)
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) A B C) r) :
    max (Fintype.card A * Fintype.card B)
      (max (Fintype.card B * Fintype.card C) (Fintype.card C * Fintype.card A)) ≤ r := by
  exact max_le (card_last_le_rank c (Tensor.matrixCoefficients_cyclic_rank h))
    (max_le (card_last_le_rank a
      (Tensor.matrixCoefficients_cyclic_rank (Tensor.matrixCoefficients_cyclic_rank h)))
      (card_last_le_rank b h))

end Finite

variable (F : Type*) [Field F] {n12 n23 n31 : ℕ}

/-- Reindexing the three sites of a tensor power by tuples of wire indices
turns it into a single larger matrix multiplication tensor. -/
theorem matrix_power_rankAtMost (s : ℕ) :
    Tensor.RankAtMost (Tensor.matrixCoefficients (K := F)
      (Fin s → Fin n31) (Fin s → Fin n12) (Fin s → Fin n23))
      (tensorRank (Tensor.power (matrixTensor F n12 n23 n31) s)) := by
  have h := (rankAtMost_tensorRank (Tensor.power (matrixTensor F n12 n23 n31) s)).pullback
    (fun x : (Fin s → Fin n31) × (Fin s → Fin n12) => fun i => (x.1 i, x.2 i))
    (fun y : (Fin s → Fin n12) × (Fin s → Fin n23) => fun i => (y.1 i, y.2 i))
    (fun z : (Fin s → Fin n23) × (Fin s → Fin n31) => fun i => (z.1 i, z.2 i))
  convert h using 1
  funext x y z
  exact (Tensor.matrixCoefficients_power s x y z).symm

/-- The largest local dimension bounds ordinary rank from below. -/
theorem matrix_flattening_le_tensorRank (h12 : 0 < n12) (h23 : 0 < n23) (h31 : 0 < n31) :
    max (n31 * n12) (max (n12 * n23) (n23 * n31)) ≤
      tensorRank (matrixTensor F n12 n23 n31) := by
  simpa using matrixCoefficients_flattenings
    (F := F) (⟨0, h31⟩ : Fin n31) (⟨0, h12⟩ : Fin n12) (⟨0, h23⟩ : Fin n23)
    (rankAtMost_tensorRank (matrixTensor F n12 n23 n31))

/-- The largest local dimension bounds asymptotic rank from below over every field. -/
theorem matrix_flattening_le_asymptoticRank (h12 : 0 < n12) (h23 : 0 < n23) (h31 : 0 < n31) :
    (max (n31 * n12) (max (n12 * n23) (n23 * n31)) : ℕ) ≤
      asymptoticRank (matrixTensor F n12 n23 n31) := by
  apply le_ciInf
  intro s
  have h := matrixCoefficients_flattenings
    (fun _ => (⟨0, h31⟩ : Fin n31)) (fun _ => (⟨0, h12⟩ : Fin n12))
    (fun _ => (⟨0, h23⟩ : Fin n23)) (matrix_power_rankAtMost F (s + 1))
  simp only [Fintype.card_pi_const, Fintype.card_fin, ← mul_pow] at h
  apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (show 0 < (s : ℝ) + 1 by positivity)).mpr
  rw [← Nat.cast_succ, Real.rpow_natCast]
  have hm (a b : ℕ) : max a b ^ (s+1) = max (a ^ (s+1)) (b ^ (s+1)) :=
    (pow_left_mono (n := s+1)).map_max
  have hh : max (n31 * n12) (max (n12 * n23) (n23 * n31)) ^ (s+1) ≤
      tensorRank (Tensor.power (matrixTensor F n12 n23 n31) (s+1)) := by
    simpa only [hm] using h
  exact_mod_cast hh

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.ArithmeticExponent
section

/-! # Rectangular arithmetic exponents over a field

The wire order is (12,23,31), so the product has dimensions
`(n31 × n12) × (n12 × n23)`. Correctness means polynomial identity over
the ground field, including when that field is finite.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Arithmetic

noncomputable section

/-- Admissible exponents for the rounded rectangular formats, with positive slack. -/
def FormalAdmissibleExponent (F : Type*) [Field F] (w12 w23 w31 τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    ∃ P : MatrixAlgorithm F (wireDimension N w31) (wireDimension N w12) (wireDimension N w23),
      FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (N : ℝ) ^ (τ + ε)

/-- The arithmetic exponent in base size `N` at three prescribed wire weights. -/
def formalOmega (F : Type*) [Field F] (w12 w23 w31 : ℝ) : ℝ :=
  sInf {τ : ℝ | FormalAdmissibleExponent F w12 w23 w31 τ}

/-- The entrywise algorithm gives an admissible exponent in every weighted format. -/
theorem formalAdmissibleExponent_naive (F : Type*) [Field F] {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) :
    FormalAdmissibleExponent F w12 w23 w31 (w12 + w23 + w31) := by
  intro ε hε
  refine ⟨16, by norm_num, ?_⟩
  intro N hN
  refine ⟨Arithmetic.naiveAlgorithm _ _ _, formalCorrect_naiveAlgorithm F _ _ _, ?_⟩
  rw [Arithmetic.naiveAlgorithm_cost]
  push_cast
  have h : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  calc
    _ ≤ 2 * (2 * (N : ℝ) ^ w31) * (2 * (N : ℝ) ^ w12) * (2 * (N : ℝ) ^ w23) := by
      gcongr <;> apply wireDimension_le hN <;> assumption
    _ = 16 * (N : ℝ) ^ (w12 + w23 + w31) := by
      rw [Real.rpow_add (zero_lt_one.trans_le h), Real.rpow_add (zero_lt_one.trans_le h)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le h (le_add_of_nonneg_right hε.le)) (by norm_num)

/-- Positive slack allows the infimum itself as an admissible exponent. -/
theorem formalOmega_admissible (F : Type*) [Field F] {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) :
    FormalAdmissibleExponent F w12 w23 w31 (formalOmega F w12 w23 w31) := by
  intro ε hε
  let S := {τ : ℝ | FormalAdmissibleExponent F w12 w23 w31 τ}
  have hS : S.Nonempty := ⟨_, formalAdmissibleExponent_naive F h12 h23 h31⟩
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt hS
    (lt_add_of_pos_right (sInf S) (half_pos hε))
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) (half_pos hε)
  refine ⟨C, hC, fun N hN => ?_⟩
  obtain ⟨P, hP, hcost⟩ := hbound N hN
  refine ⟨P, hP, hcost.trans (mul_le_mul_of_nonneg_left ?_ hC.le)⟩
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  change τ + ε / 2 ≤ sInf S + ε
  linarith

/-- A formal arithmetic cost bound also controls ordinary rank in each rounded format. -/
theorem FormalAdmissibleExponent.rank_growth {F : Type*} [Field F] {w12 w23 w31 τ : ℝ}
    (hτ : FormalAdmissibleExponent F w12 w23 w31 τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (tensorRank (matrixTensor F (wireDimension N w12) (wireDimension N w23)
        (wireDimension N w31)) : ℝ) ≤ C * (N : ℝ) ^ (τ + ε) := by
  obtain ⟨C, hC, hc⟩ := hτ ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN
  obtain ⟨P, hP, hcost⟩ := hc N hN
  calc
    _ ≤ (2 : ℝ) * P.cost := by exact_mod_cast matrixTensor_rank_le_twice_cost hP
    _ ≤ 2 * (C * (N : ℝ) ^ (τ + ε)) := by linarith only [hcost]
    _ = _ := by ring

theorem matrixTensor_rank_pos (F : Type*) [Field F] {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 0 < tensorRank (matrixTensor F x y z) :=
  (Nat.mul_pos hz hx).trans_le ((le_max_left _ _).trans (matrix_flattening_le_tensorRank F hx hy hz))

/-- Each logarithmic site load is a lower bound on the ordinary log-rank. -/
theorem matrix_load_le_log_tensorRank (F : Type*) [Field F] {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (i : Fin 3) :
    loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z) i ≤
      Real.logb 2 (tensorRank (matrixTensor F x y z)) := by
  let r := tensorRank (matrixTensor F x y z)
  have hlog {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hprod : a * b ≤ r) :
      Real.logb 2 a + Real.logb 2 b ≤ Real.logb 2 r := by
    rw [← Real.logb_mul (by positivity : (a : ℝ) ≠ 0) (by positivity : (b : ℝ) ≠ 0)]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    exact_mod_cast hprod
  obtain ⟨h₁, h₂, h₃⟩ := (max_le_iff.mp (matrix_flattening_le_tensorRank F hx hy hz)).imp_right
    max_le_iff.mp
  fin_cases i
  · exact hlog hz hx h₁
  · exact hlog hx hy h₂
  · exact hlog hy hz h₃

/-- Every formal rectangular arithmetic exponent dominates each local dimension exponent. -/
theorem FormalAdmissibleExponent.load_le {F : Type*} [Field F] {w12 w23 w31 τ : ℝ}
    (hτ : FormalAdmissibleExponent F w12 w23 w31 τ) (i : Fin 3) : loads w12 w23 w31 i ≤ τ := by
  apply le_of_dyadic_log_bound
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ.rank_growth ε hε
  refine ⟨C, hC, fun k => ?_⟩
  have hdim (w : ℝ) := wireDimension_pos (N := 2 ^ k) (by positivity) w
  apply (dyadic_load_le k _ _ _ i).trans
  apply (matrix_load_le_log_tensorRank F (hdim w12) (hdim w23) (hdim w31) i).trans
  exact Real.logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast matrixTensor_rank_pos F (hdim w12) (hdim w23) (hdim w31))
    (hbound _ (Nat.one_le_pow _ _ (by decide)))

theorem load_le_formalOmega (F : Type*) [Field F] {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) (i : Fin 3) :
    loads w12 w23 w31 i ≤ formalOmega F w12 w23 w31 :=
  (formalOmega_admissible F h12 h23 h31).load_le i

@[simp] theorem unit_weight_loads : loads 1 1 1 = fun _ => 2 := by
  funext i
  fin_cases i <;> norm_num [loads]

private theorem loads_nonnegative {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    ∀ i, 0 ≤ loads u v w i := by
  intro i
  fin_cases i <;> dsimp [loads] <;> positivity

section RankBound

variable {F : Type*} [Field F]
variable (hfinite : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
  RadicalTest (loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z))
    (Real.logb 2 (tensorRank (matrixTensor F x y z))))

include hfinite

private theorem heightTest_of_matrix_rank_growth {w12 w23 w31 τ : ℝ}
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (tensorRank (matrixTensor F (wireDimension N w12) (wireDimension N w23)
        (wireDimension N w31)) : ℝ) ≤ C * (N : ℝ) ^ (τ + ε)) :
    HeightTest (loads w12 w23 w31) τ := by
  apply heightTest_of_polynomial_bound
  intro ε hε
  obtain ⟨C, hC, hc⟩ := hgrowth ε hε
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hdim (w : ℝ) := wireDimension_pos (N := N) (by omega) w
  have hlog (w : ℝ) : 0 ≤ Real.logb 2 (wireDimension N w) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hdim w)
  have htest := (hfinite _ _ _ (hdim w12) (hdim w23) (hdim w31)).heightTest
    (loads_nonnegative (hlog _) (hlog _) (hlog _))
  apply htest.mono
  exact Real.logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast matrixTensor_rank_pos F (hdim w12) (hdim w23) (hdim w31)) (hc N hN)

/-- Take the infimum over all polynomial growth bounds supplied by a circuit model.
The rank may be measured over a common extension of its field of constants. -/
theorem radicalTest_sInf_of_matrix_rank_growth {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) {S : Set ℝ} (hS : S.Nonempty)
    (hgrowth : ∀ τ ∈ S, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (tensorRank (matrixTensor F (wireDimension N w12) (wireDimension N w23)
        (wireDimension N w31)) : ℝ) ≤ C * (N : ℝ) ^ (τ + ε)) :
    RadicalTest (loads w12 w23 w31) (sInf S) :=
  (heightTest_sInf hS fun τ hτ => heightTest_of_matrix_rank_growth hfinite (hgrowth τ hτ)).radicalTest
    (loads_nonnegative h12 h23 h31)

/-- The finite ordinary-rank inequality gives the rectangular arithmetic exponent inequality. -/
theorem formalOmega_radicalTest_of_rank_bound {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) :
    RadicalTest (loads w12 w23 w31) (formalOmega F w12 w23 w31) := by
  apply radicalTest_sInf_of_matrix_rank_growth hfinite h12 h23 h31
    (S := {τ | FormalAdmissibleExponent F w12 w23 w31 τ}) ⟨_, formalAdmissibleExponent_naive F h12 h23 h31⟩
  exact fun _ hτ => hτ.rank_growth

/-- The square exponent consequence of the finite ordinary-rank inequality. -/
theorem formalOmega_square_lower_bound_of_rank_bound :
    3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 := by
  apply square_lower_bound
  simpa only [unit_weight_loads] using formalOmega_radicalTest_of_rank_bound hfinite
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)

end RankBound
end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.Increment
section

/-!
# Intersecting submodularity of diagonal prices

The proof of Lemma `lem:submod` in the manuscript uses two integer weight
specializations to obtain a one-site inequality. We verify the weights on
their specified supports and the telescoping argument for finite sets.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Finset

section Increments

variable {α : Type*} [DecidableEq α] (δ : Finset α → ℝ)

/-- The one-site inequality (equation `eq:width-increment`). -/
def DiminishingIncrements : Prop :=
  ∀ ⦃I A : Finset α⦄ ⦃z : α⦄, I.Nonempty → I ⊆ A → z ∉ A →
    δ (insert z A) - δ A ≤ δ (insert z I) - δ I

/-- The price inequality for finite sets with nonempty intersection. -/
def IntersectingSubmodular : Prop :=
  ∀ ⦃A B : Finset α⦄, (A ∩ B).Nonempty → δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B

variable {δ}

/-- Adjoin a finite family of new sites successively to both sets. -/
theorem diminishingIncrements_union (h : DiminishingIncrements δ)
    {I A : Finset α} (hne : I.Nonempty) (hIA : I ⊆ A)
    (S : Finset α) (hdis : Disjoint S A) :
    δ (A ∪ S) - δ A ≤ δ (I ∪ S) - δ I := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert z S hz ih =>
    obtain ⟨hzA, hSA⟩ := Finset.disjoint_insert_left.mp hdis
    have step := h (I := I ∪ S) (A := A ∪ S) (z := z) (hne.mono (Finset.subset_union_left (s₂ := S)))
      (Finset.union_subset_union hIA (Finset.Subset.refl S))
      (by simpa only [Finset.mem_union, not_or] using And.intro hzA hz)
    rw [Finset.union_insert, Finset.union_insert]
    linarith [ih hSA]

/-- Intersecting submodularity is equivalent to the one-site increment inequality. -/
theorem intersectingSubmodular_iff_diminishingIncrements :
    IntersectingSubmodular δ ↔ DiminishingIncrements δ := by
  constructor
  · intro h I A z hI hIA hz
    have hinter : A ∩ insert z I = I := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      grind
    have hunion : A ∪ insert z I = insert z A := by
      rw [Finset.union_insert, Finset.union_eq_left.mpr hIA]
    have h' := h (A := A) (B := insert z I) (by simpa only [hinter] using hI)
    rw [hinter, hunion] at h'
    linarith
  · intro h A B hAB
    have h' := diminishingIncrements_union h hAB Finset.inter_subset_left
      (B \ A) Finset.sdiff_disjoint
    have heq : (A ∩ B) ∪ (B \ A) = B := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      grind
    rw [heq, Finset.union_sdiff_self_eq_union] at h'
    linarith

end Increments

section IntegerWeights

variable {ι : Type*} [Fintype ι]

/-- On the support selected by coefficient extraction, the first local
weights sum to `(g - h)²`. Here `ι` indexes the sites other than site 1. -/
theorem firstWeight_eq_sq (g h v₁ : ℤ) (v : ι → ℤ)
    (hs : g = h + ∑ j, v j - Fintype.card ι * v₁) :
    g ^ 2 + (-h ^ 2 + 2 * h * (Fintype.card ι * v₁)) +
      ∑ j, -(2 * h * v j) = (g - h) ^ 2 := by
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hs]
  ring

/-- The first specialization retains precisely `g = h`. -/
theorem firstWeight_eq_zero_iff (g h v₁ : ℤ) (v : ι → ℤ)
    (hs : g = h + ∑ j, v j - Fintype.card ι * v₁) :
    g ^ 2 + (-h ^ 2 + 2 * h * (Fintype.card ι * v₁)) +
      ∑ j, -(2 * h * v j) = 0 ↔ g = h := by
  rw [firstWeight_eq_sq g h v₁ v hs]
  simp [sub_eq_zero]

/-- On the remaining support, the second local weights also sum to a
sum of squares in the integers. -/
theorem secondWeight_eq_sum_sq (v₁ : ℤ) (v : ι → ℤ)
    (hs : ∑ j, v j = Fintype.card ι * v₁) :
    ∑ j, v j ^ 2 - Fintype.card ι * v₁ ^ 2 = ∑ j, (v j - v₁) ^ 2 := by
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_right_comm (2 : ℤ) _ v₁]
  rw [← Finset.mul_sum, hs]
  simp
  ring

/-- The second specialization retains precisely the common choices of all labels. -/
theorem secondWeight_eq_zero_iff (v₁ : ℤ) (v : ι → ℤ)
    (hs : ∑ j, v j = Fintype.card ι * v₁) :
    ∑ j, v j ^ 2 - Fintype.card ι * v₁ ^ 2 = 0 ↔ ∀ j, v j = v₁ := by
  rw [secondWeight_eq_sum_sq v₁ v hs, Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j - v₁))]
  simp [sub_eq_zero]

end IntegerWeights

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SpineConditioning
section

/-!
# Conditioning a finite family of tips on a spine

These are the finite, deterministic inequalities used before taking
expectations in the proof of Theorem `thm:student`. Tips may coincide with each other or
with points of the spine.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {α ι : Type*} [DecidableEq α] {δ : Finset α → ℝ}

/-- The price of adding all the tips to the spine is bounded by the
sum of their individual increments at the spine. -/
theorem conditioning_union_image_le_of_nonempty
    (hmono : ∀ ⦃S T : Finset α⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hsub : IntersectingSubmodular δ) {B : Finset α} (hB : B.Nonempty)
    (s : Finset ι) (tip : ι → α) :
    δ (B ∪ s.image tip) ≤ δ B + ∑ i ∈ s, (δ (insert (tip i) B) - δ B) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.image_insert, Finset.union_insert, Finset.sum_insert hi]
    by_cases hx : tip i ∈ B ∪ s.image tip
    · rw [Finset.insert_eq_of_mem hx]
      have hinc : δ B ≤ δ (insert (tip i) B) := hmono hB (Finset.subset_insert _ _)
      linarith
    · have hinc := intersectingSubmodular_iff_diminishingIncrements.mp hsub
          (I := B) (A := B ∪ s.image tip) hB Finset.subset_union_left hx
      linarith

/-- Conditioning with monotonicity on all finite sets. -/
theorem conditioning_union_image_le (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ) {B : Finset α} (hB : B.Nonempty)
    (s : Finset ι) (tip : ι → α) :
    δ (B ∪ s.image tip) ≤ δ B + ∑ i ∈ s, (δ (insert (tip i) B) - δ B) :=
  conditioning_union_image_le_of_nonempty (fun _ _ _ h => hmono h) hsub hB s tip

/-- The conditioning bound for the tips alone, including repeated tips. -/
theorem conditioning_image_le (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ) {B : Finset α} (hB : B.Nonempty)
    (s : Finset ι) (tip : ι → α) :
    δ (s.image tip) ≤ δ B + ∑ i ∈ s, (δ (insert (tip i) B) - δ B) :=
  (hmono Finset.subset_union_right).trans (conditioning_union_image_le hmono hsub hB s tip)

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.Book
section

/-!
# The metric of the three-page book

The positive coordinate axes in three-dimensional ℓ¹ realize the metric
tripod. Taking its Euclidean metric product with the spine identifies the
three copies of the spine. We compute the distances used for the three tips
and the two base points in the finite-rank argument.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open WithLp
open scoped NNReal

/-- The three positive coordinate rays, with their common origin and path metric. -/
abbrev Tripod :=
  {x : PiLp 1 (fun _ : Fin 3 => ℝ) // ∃ (i : Fin 3) (r : ℝ≥0), x = PiLp.single (β := fun _ : Fin 3 => ℝ) 1 i (r : ℝ)}

/-- The point at height `r` on arm `i`. -/
def tripodPoint (i : Fin 3) (r : ℝ≥0) : Tripod :=
  ⟨PiLp.single (β := fun _ : Fin 3 => ℝ) 1 i (r : ℝ), i, r, rfl⟩

theorem tripodPoint_zero (i j : Fin 3) : tripodPoint i 0 = tripodPoint j 0 := by
  apply Subtype.ext
  change PiLp.single (β := fun _ : Fin 3 => ℝ) 1 i (0 : ℝ) = PiLp.single (β := fun _ : Fin 3 => ℝ) 1 j (0 : ℝ)
  apply PiLp.ext
  intro k
  simp [PiLp.single_apply]

theorem tripod_dist_same (i : Fin 3) (r s : ℝ≥0) :
    dist (tripodPoint i r) (tripodPoint i s) = |(r : ℝ) - s| := by
  exact PiLp.dist_single_same 1 (fun _ : Fin 3 => ℝ) i (r : ℝ) (s : ℝ)

theorem tripod_dist_of_ne {i j : Fin 3} (hij : i ≠ j) (r s : ℝ≥0) :
    dist (tripodPoint i r) (tripodPoint j s) = (r : ℝ) + s := by
  change dist (PiLp.single (β := fun _ : Fin 3 => ℝ) 1 i (r : ℝ) : PiLp 1 (fun _ : Fin 3 => ℝ))
    (PiLp.single (β := fun _ : Fin 3 => ℝ) 1 j (s : ℝ)) = _
  rw [PiLp.dist_eq_of_L1]
  have h (k : Fin 3) : dist (PiLp.single (β := fun _ : Fin 3 => ℝ) 1 i (r : ℝ) k) (PiLp.single (β := fun _ : Fin 3 => ℝ) 1 j (s : ℝ) k) =
      (if k = i then (r : ℝ) else 0) + (if k = j then (s : ℝ) else 0) := by
    by_cases hi : k = i
    · subst k
      simp [hij]
    · by_cases hj : k = j
      · subst k
        simp [hi, Real.dist_eq]
      · simp [hi, hj]
  simp_rw [h]
  simp [Finset.sum_add_distrib]

/-- The book with spine `E`. For Euclidean `E` this has the Euclidean product metric. -/
abbrev Book (E : Type*) := WithLp 2 (Tripod × E)

/-- Page coordinates. Height zero gives the same point in every page. -/
def bookPoint {E : Type*} (i : Fin 3) (r : ℝ≥0) (p : E) : Book E :=
  toLp 2 (tripodPoint i r, p)

theorem bookPoint_zero {E : Type*} (i j : Fin 3) (p : E) :
    bookPoint i 0 p = bookPoint j 0 p := by
  simp only [bookPoint, tripodPoint_zero i j]

theorem book_dist {E : Type*} [PseudoMetricSpace E] (i j : Fin 3) (r s : ℝ≥0) (p q : E) :
    dist (bookPoint i r p) (bookPoint j s q) =
      Real.sqrt ((if i = j then |(r : ℝ) - s| else (r : ℝ) + s) ^ 2 + dist p q ^ 2) := by
  rw [WithLp.prod_dist_eq_add (by norm_num : 0 < (2 : ENNReal).toReal)]
  change (dist (tripodPoint i r) (tripodPoint j s) ^ (2 : ENNReal).toReal +
      dist p q ^ (2 : ENNReal).toReal) ^ (1 / (2 : ENNReal).toReal) = _
  rw [Real.sqrt_eq_rpow]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  by_cases h : i = j
  · subst j
    simp [tripod_dist_same]
  · simp [h, tripod_dist_of_ne h]

theorem book_dist_distinct_tips {E : Type*} [PseudoMetricSpace E] {i j : Fin 3}
    (hij : i ≠ j) (r s : ℝ≥0) (p : E) :
    dist (bookPoint i r p) (bookPoint j s p) = (r : ℝ) + s := by
  rw [book_dist]
  simp only [ite_eq_right_iff.mpr (fun h => (hij h).elim), dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  exact Real.sqrt_sq (add_nonneg r.2 s.2)

/-- The Euclidean triangle with spine endpoints at ±1 and a tip of height `r`
has half-perimeter `1 + √(1 + r²)`. -/
theorem book_triangle_half_perimeter (i : Fin 3) (r : ℝ≥0) :
    (dist (bookPoint i 0 (-1 : ℝ)) (bookPoint i 0 1) +
      dist (bookPoint i 0 (1 : ℝ)) (bookPoint i r 0) +
      dist (bookPoint i r (0 : ℝ)) (bookPoint i 0 (-1))) / 2 =
      1 + Real.sqrt (1 + (r : ℝ) ^ 2) := by
  simp only [book_dist, ite_true, eq_self, NNReal.coe_zero, sub_zero, zero_sub, abs_neg,
    NNReal.abs_eq, Real.dist_eq]
  norm_num [add_comm]
  ring

/-- The signed-height chart through pages `i` and `j`. Nonnegative heights
belong to page `i`, and negative heights belong to page `j`. -/
def bookPlane {E : Type*} (i j : Fin 3) (x : WithLp 2 (E × ℝ)) : Book E :=
  if 0 ≤ x.snd then bookPoint i x.snd.toNNReal x.fst
  else bookPoint j (-x.snd).toNNReal x.fst

theorem bookPlane_nonneg {E : Type*} (i j : Fin 3) (p : E) (r : ℝ≥0) :
    bookPlane i j (toLp 2 (p, (r : ℝ))) = bookPoint i r p := by
  change (if 0 ≤ (r : ℝ) then _ else _) = _
  simp

theorem bookPlane_isometry {E : Type*} [SeminormedAddCommGroup E] {i j : Fin 3} (hij : i ≠ j) :
    Isometry (bookPlane (E := E) i j) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [WithLp.prod_dist_eq_of_L2 x y, add_comm]
  unfold bookPlane
  split_ifs with hx hy hy <;> rw [book_dist]
  · simp [Real.toNNReal_of_nonneg hx, Real.toNNReal_of_nonneg hy, Real.dist_eq]
  · have hny : 0 ≤ -y.snd := by linarith
    simp [hij, Real.toNNReal_of_nonneg hx, Real.toNNReal_of_nonneg hny,
      Real.dist_eq, sq_abs, sub_eq_add_neg]
  · have hnx : 0 ≤ -x.snd := by linarith
    simp only [hij.symm, ite_false, Real.toNNReal_of_nonneg hy, Real.toNNReal_of_nonneg hnx,
      Real.dist_eq, sq_abs, NNReal.coe_mk]
    congr 2
    ring
  · have hnx : 0 ≤ -x.snd := by linarith
    have hny : 0 ≤ -y.snd := by linarith
    simp only [eq_self, ite_true, Real.toNNReal_of_nonneg hnx, Real.toNNReal_of_nonneg hny,
      Real.dist_eq, sq_abs, NNReal.coe_mk]
    congr 2
    ring

/-- A point on the spine of the two-dimensional book. -/
def bookSpine (p : ℝ) : Book ℝ := bookPoint 0 0 p

/-- The two points at coordinates ±1 on the spine. -/
def bookBase : Finset (Book ℝ) := {bookSpine (-1), bookSpine 1}

/-- The tip belonging to party `i` in the rectangular rank test. -/
def bookTip (r : Fin 3 → ℝ≥0) (i : Fin 3) : Book ℝ := bookPoint i (r i) 0

theorem bookTip_dist (r : Fin 3 → ℝ≥0) {i j : Fin 3} (hij : i ≠ j) :
    dist (bookTip r i) (bookTip r j) = (r i : ℝ) + r j :=
  book_dist_distinct_tips hij _ _ _

theorem bookSpine_dist : dist (bookSpine (-1)) (bookSpine 1) = 2 := by
  norm_num [bookSpine, book_dist, Real.dist_eq]

/-- The diagonal price bound of the planar book test, from its metric and
the planar half-perimeter law for each of the three triangles. -/
theorem bookTip_price_le_of_triangle_le {δ : Finset (Book ℝ) → ℝ} (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ) (r : Fin 3 → ℝ≥0) (hbase : δ bookBase = 2)
    (htri : ∀ i, δ (insert (bookTip r i) bookBase) ≤
      (dist (bookSpine (-1)) (bookSpine 1) + dist (bookSpine 1) (bookTip r i) +
        dist (bookTip r i) (bookSpine (-1))) / 2) :
    δ (Finset.univ.image (bookTip r)) ≤ ∑ i, Real.sqrt (1 + (r i : ℝ) ^ 2) - 1 := by
  have hB : bookBase.Nonempty := ⟨bookSpine (-1), by simp [bookBase]⟩
  have h := conditioning_image_le hmono hsub hB Finset.univ (bookTip r)
  have htriangle (i : Fin 3) : δ (insert (bookTip r i) bookBase) ≤
      1 + Real.sqrt (1 + (r i : ℝ) ^ 2) := by
    apply (htri i).trans_eq
    simpa only [bookSpine, bookTip, bookPoint_zero i 0] using book_triangle_half_perimeter i (r i)
  simp only [hbase, Fin.sum_univ_three] at h ⊢
  linarith [htriangle 0, htriangle 1, htriangle 2]

theorem bookTip_price_le {δ : Finset (Book ℝ) → ℝ} (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ) (r : Fin 3 → ℝ≥0) (hbase : δ bookBase = 2)
    (htri : ∀ i, δ (insert (bookTip r i) bookBase) =
      (dist (bookSpine (-1)) (bookSpine 1) + dist (bookSpine 1) (bookTip r i) +
        dist (bookTip r i) (bookSpine (-1))) / 2) :
    δ (Finset.univ.image (bookTip r)) ≤ ∑ i, Real.sqrt (1 + (r i : ℝ) ^ 2) - 1 :=
  bookTip_price_le_of_triangle_le hmono hsub r hbase (fun i => (htri i).le)

private theorem sqrt_scaled_sum_sq (a b c : ℝ) (ha : 0 ≤ a) :
    Real.sqrt ((a * b) ^ 2 + (a * c) ^ 2) = a * Real.sqrt (b ^ 2 + c ^ 2) := by
  rw [show (a * b) ^ 2 + (a * c) ^ 2 = a ^ 2 * (b ^ 2 + c ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

/-- Reflect one tip across the common facet. The Euclidean segment from the
reflected tip to the other tip crosses the facet at a point between the feet.
Only distances in each individual page enter this upper bound. -/
theorem dist_le_reflected_path {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace X] {x y : X} {p q : E} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (facet : E → X)
    (hx : ∀ z ∈ segment ℝ p q, dist x (facet z) = Real.sqrt (dist p z ^ 2 + r ^ 2))
    (hy : ∀ z ∈ segment ℝ p q, dist (facet z) y = Real.sqrt (dist z q ^ 2 + s ^ 2)) :
    dist x y ≤ Real.sqrt (dist p q ^ 2 + (r + s) ^ 2) := by
  let t := r / (r + s)
  have ht : 0 ≤ t := div_nonneg hr (add_nonneg hr hs)
  have ht₁ : t ≤ 1 := by
    rcases (add_nonneg hr hs).eq_or_lt with h | h
    · simp [t, ← h]
    · exact (div_le_one h).mpr (by linarith)
  have hr' : t * (r + s) = r := by
    rcases (add_nonneg hr hs).eq_or_lt with h | h
    · rw [← h, mul_zero]
      linarith
    · exact div_mul_cancel₀ r h.ne'
  have hs' : (1 - t) * (r + s) = s := by linarith
  let z := AffineMap.lineMap p q t
  have hz : z ∈ segment ℝ p q := lineMap_mem_segment ℝ p q ⟨ht, ht₁⟩
  have hx' : dist x (facet z) = t * Real.sqrt (dist p q ^ 2 + (r + s) ^ 2) := by
    rw [hx z hz, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht]
    conv_lhs => rw [← hr']
    exact sqrt_scaled_sum_sq _ _ _ ht
  have hy' : dist (facet z) y = (1 - t) * Real.sqrt (dist p q ^ 2 + (r + s) ^ 2) := by
    rw [hy z hz, dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht₁)]
    conv_lhs => rw [← hs']
    exact sqrt_scaled_sum_sq _ _ _ (sub_nonneg.mpr ht₁)
  calc
    dist x y ≤ dist x (facet z) + dist (facet z) y := dist_triangle _ _ _
    _ = _ := by rw [hx', hy']; ring

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.BorderRank
section

/-! # Geometric border rank

We use equations of the affine Zariski closure in a fixed tensor format. Both
the polynomials and the rank decompositions tested by their equations are
taken over the algebraic closure of the ground field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

noncomputable section

variable {F X Y Z : Type*} [Field F]

/-- The scalar extension of a tensor, entry by entry. -/
def toAlgebraicClosure (T : Tensor F X Y Z) : Tensor (AlgebraicClosure F) X Y Z :=
  fun x y z => algebraMap F (AlgebraicClosure F) (T x y z)

/-- Evaluate a polynomial in the tensor entries. -/
def tensorEval (T : Tensor F X Y Z) : MvPolynomial (X × Y × Z) F →+* F :=
  MvPolynomial.eval (fun p => T p.1 p.2.1 p.2.2)

/-- Membership in the Zariski closure of the rank-at-most-`r` locus after scalar extension. -/
def GeometricBorderRankAtMost (T : Tensor F X Y Z) (r : ℕ) : Prop :=
  ∀ p : MvPolynomial (X × Y × Z) (AlgebraicClosure F),
    (∀ S : Tensor (AlgebraicClosure F) X Y Z, S.RankAtMost r → tensorEval S p = 0) →
      tensorEval (toAlgebraicClosure T) p = 0

theorem geometricBorderRankAtMost_of_rankAtMost {T : Tensor F X Y Z} {r : ℕ}
    (h : T.RankAtMost r) : GeometricBorderRankAtMost T r := by
  exact fun p hp => hp _ (h.map (algebraMap F (AlgebraicClosure F)))

/-- A determinant of coordinate entries is a polynomial in the tensor. -/
private theorem eval_minor {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (S : Tensor K X Y Z) (entry : I → I → X × Y × Z) :
    tensorEval S (Matrix.of (fun i j =>
      MvPolynomial.X (entry i j) : I → I → MvPolynomial (X × Y × Z) K)).det =
    (Matrix.of fun i j => S (entry i j).1 (entry i j).2.1 (entry i j).2.2).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [tensorEval]

variable [Fintype X] [Fintype Y]

private theorem exists_geometricBorderRankAtMost (T : Tensor F X Y Z) :
    ∃ r, GeometricBorderRankAtMost T r :=
  ⟨_, geometricBorderRankAtMost_of_rankAtMost (rankAtMost_tensorRank T)⟩

/-- The least rank whose locus has the scalar-extended tensor in its Zariski closure. -/
def geometricBorderRank (T : Tensor F X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_geometricBorderRankAtMost T)

theorem geometricBorderRankAtMost_geometricBorderRank (T : Tensor F X Y Z) :
    GeometricBorderRankAtMost T (geometricBorderRank T) := by
  classical
  exact Nat.find_spec (exists_geometricBorderRankAtMost T)

theorem geometricBorderRank_le_of_atMost {T : Tensor F X Y Z} {r : ℕ}
    (h : GeometricBorderRankAtMost T r) : geometricBorderRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_geometricBorderRankAtMost T) h

theorem geometricBorderRank_le_tensorRank (T : Tensor F X Y Z) :
    geometricBorderRank T ≤ tensorRank T :=
  geometricBorderRank_le_of_atMost (geometricBorderRankAtMost_of_rankAtMost (rankAtMost_tensorRank T))

/-- A nonzero minor whose determinant vanishes on tensors of insufficient
rank supplies a lower bound on geometric border rank. -/
theorem card_le_geometricBorderRank_of_minor {I : Type*} [Fintype I] [DecidableEq I]
    (T : Tensor F X Y Z) (entry : I → I → X × Y × Z)
    (hne : (Matrix.of fun i j => T (entry i j).1 (entry i j).2.1 (entry i j).2.2).det ≠ 0)
    (hvanish : ∀ (S : Tensor (AlgebraicClosure F) X Y Z) (r : ℕ), S.RankAtMost r →
      r < Fintype.card I →
      (Matrix.of fun i j => S (entry i j).1 (entry i j).2.1 (entry i j).2.2).det = 0) :
    Fintype.card I ≤ geometricBorderRank T := by
  by_contra! hlt
  let p := (Matrix.of (fun i j => MvPolynomial.X (entry i j) :
    I → I → MvPolynomial (X × Y × Z) (AlgebraicClosure F))).det
  have he := geometricBorderRankAtMost_geometricBorderRank T p (fun S hS => by
    rw [show tensorEval S p = _ from eval_minor S entry]
    exact hvanish S _ hS hlt)
  rw [show tensorEval (toAlgebraicClosure T) p = _ from eval_minor _ entry] at he
  let A : Matrix I I F := Matrix.of fun i j => T (entry i j).1 (entry i j).2.1 (entry i j).2.2
  change ((algebraMap F (AlgebraicClosure F)).mapMatrix A).det = 0 at he
  rw [← RingHom.map_det] at he
  exact hne ((map_eq_zero _).mp he)

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.PowerClosure
section

/-! # Closure of the tensor-power span

Every linear equation on a tensor power pulls back to a polynomial equation
on the original tensor. Thus membership in a fixed linear span extends to the
Zariski closure of a rank locus.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

variable {K X Y Z : Type*} [Field K] [Fintype X] [Fintype Y] [Fintype Z]

private theorem power_dual_is_polynomial (n : ℕ)
    (f : Module.Dual K (Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z))) :
    ∃ p : MvPolynomial (X × Y × Z) K, ∀ S : Tensor K X Y Z,
      tensorEval S p = f (Tensor.power S n) := by
  classical
  let e (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
      Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
    fun x' y' z' => if x = x' ∧ y = y' ∧ z = z' then 1 else 0
  refine ⟨∑ x, ∑ y, ∑ z, MvPolynomial.C (f (e x y z)) *
    ∏ i : Fin n, MvPolynomial.X (x i, y i, z i), ?_⟩
  intro S
  have he : Tensor.power S n =
      ∑ x, ∑ y, ∑ z, (Tensor.power S n x y z) • e x y z := by
    funext x' y' z'
    simp [e, Finset.sum_apply, Pi.smul_apply, ite_and]
  rw [he]
  simp [tensorEval, Tensor.power, mul_comm]

/-- A linear span containing all powers of tensors of rank at most `r`
contains the powers of tensors in the Zariski closure of that rank locus. -/
theorem power_mem_span_of_closure {ι : Type*} {r n : ℕ} {T : Tensor K X Y Z}
    (hT : ∀ p : MvPolynomial (X × Y × Z) K,
      (∀ S : Tensor K X Y Z, S.RankAtMost r → tensorEval S p = 0) → tensorEval T p = 0)
    (W : ι → Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z))
    (hW : ∀ S : Tensor K X Y Z, S.RankAtMost r →
      Tensor.power S n ∈ Submodule.span K (Set.range W)) :
    Tensor.power T n ∈ Submodule.span K (Set.range W) := by
  by_contra hn
  obtain ⟨f, hf, hker⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨p, hp⟩ := power_dual_is_polynomial n f
  apply hf
  rw [← hp]
  apply hT
  intro S hS
  rw [hp, ← Submodule.mem_bot K, ← hker]
  exact ⟨_, hW S hS, rfl⟩

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.RankLimit
section

/-! # The limit defining asymptotic tensor rank

Splitting Kronecker powers gives a submultiplicative sequence of natural
ranks. Applying Fekete's lemma to their logarithms identifies the manuscript's
limit with the infimum of the positive-index rank roots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open Filter MatrixMultiplication.Foundation
open scoped Topology

section

/-- The positive-index root infimum is the limit for a natural-valued
submultiplicative sequence, including sequences with a zero term. -/
theorem tendsto_root_of_submultiplicative (r : ℕ → ℕ)
    (hmul : ∀ m n, r (m + n) ≤ r m * r n) :
    Tendsto (fun n : ℕ => (r (n + 1) : ℝ) ^ ((n + 1 : ℝ)⁻¹)) atTop
      (𝓝 (⨅ n : ℕ, (r (n + 1) : ℝ) ^ ((n + 1 : ℝ)⁻¹))) := by
  let root (n : ℕ) := (r (n + 1) : ℝ) ^ ((n + 1 : ℝ)⁻¹)
  change Tendsto root atTop (𝓝 (⨅ n, root n))
  have hnonneg n : 0 ≤ root n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbdd : BddBelow (Set.range root) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hnonneg n
  by_cases hz : ∃ k, r k = 0
  · obtain ⟨k, hk⟩ := hz
    have heq (n : ℕ) (hn : k ≤ n) : root n = 0 := by
      have h := hmul k (n + 1 - k)
      rw [show k + (n + 1 - k) = n + 1 by omega, hk, zero_mul, Nat.le_zero] at h
      simp [root, h, Real.zero_rpow (by positivity : ((n + 1 : ℝ)⁻¹) ≠ 0)]
    have hinf : (⨅ n, root n) = 0 :=
      le_antisymm ((ciInf_le hbdd k).trans_eq (heq k le_rfl)) (le_ciInf hnonneg)
    rw [hinf]
    exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨k, fun n hn => (heq n hn).symm⟩)
  · push Not at hz
    have hpos (n : ℕ) : (0 : ℝ) < r n := by exact_mod_cast Nat.pos_of_ne_zero (hz n)
    let u (n : ℕ) := Real.log (r n)
    have hsub : Subadditive u := by
      intro m n
      dsimp [u]
      rw [← Real.log_mul (hpos m).ne' (hpos n).ne']
      apply Real.log_le_log (hpos _)
      exact_mod_cast hmul m n
    have hu : BddBelow (Set.range fun n : ℕ => u n / n) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero (hz n))) (Nat.cast_nonneg _)
    have hroot n : root n = Real.exp (u (n + 1) / (n + 1)) := by
      dsimp only [root]
      rw [Real.rpow_def_of_pos (hpos _)]
      rfl
    have hlim : Tendsto root atTop (𝓝 (Real.exp hsub.lim)) := by
      have h := (Real.continuous_exp.continuousAt.tendsto.comp
        ((hsub.tendsto_lim hu).comp (tendsto_add_atTop_nat 1)))
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, ← hroot] using h
    have hinf : (⨅ n, root n) = Real.exp hsub.lim := by
      refine le_antisymm (ge_of_tendsto' hlim (ciInf_le hbdd)) (le_ciInf fun n => ?_)
      rw [hroot, Real.exp_le_exp]
      simpa only [Nat.cast_succ] using
        hsub.lim_le_div hu (Nat.succ_ne_zero n)
    rwa [hinf]

variable {F X Y Z : Type*} [Field F] [Fintype X] [Fintype Y]

private def splitPowerWord {A : Type*} (m n : ℕ) (x : Fin (m + n) → A) :
    (Fin m → A) × (Fin n → A) :=
  (x ∘ Fin.castAdd n, x ∘ Fin.natAdd m)

/-- Splitting each site's words into a prefix and suffix shows that the
rank of Kronecker powers is submultiplicative. -/
theorem tensorRank_power_add_le (T : Tensor F X Y Z) (m n : ℕ) :
    tensorRank (Tensor.power T (m + n)) ≤
      tensorRank (Tensor.power T m) * tensorRank (Tensor.power T n) := by
  have h := ((rankAtMost_tensorRank (Tensor.power T m)).product
    (rankAtMost_tensorRank (Tensor.power T n))).pullback
    (splitPowerWord m n) (splitPowerWord m n) (splitPowerWord m n)
  apply tensorRank_le_of_rankAtMost
  have heq : Tensor.power T (m + n) = Tensor.pullback
      (splitPowerWord m n) (splitPowerWord m n) (splitPowerWord m n)
      (Tensor.product (Tensor.power T m) (Tensor.power T n)) := by
    funext x y z
    exact Fin.prod_univ_add (fun i => T (x i) (y i) (z i))
  rw [heq]
  exact h

/-- The tensor-power rank roots converge to asymptotic rank. -/
theorem tendsto_tensorRank_power_root (T : Tensor F X Y Z) :
    Tendsto (fun n : ℕ => (tensorRank (Tensor.power T n) : ℝ) ^ ((n : ℝ)⁻¹)) atTop
      (𝓝 (asymptoticRank T)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one, asymptoticRank] using
    tendsto_root_of_submultiplicative (fun n => tensorRank (Tensor.power T n))
      (tensorRank_power_add_le T)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.RankGrowth
section

/-! # Polynomial factors in tensor-power rank bounds -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open Filter MatrixMultiplication.Foundation
open scoped Topology

section

variable {F X Y Z : Type*} [Field F] [Fintype X] [Fintype Y]

/-- A polynomial overhead in a uniform tensor-power algorithm disappears
on taking the asymptotic rank. -/
theorem asymptoticRank_le_of_polynomial_power_bound (T : Tensor F X Y Z) (r D : ℕ)
    (h : ∀ n : ℕ, tensorRank (Tensor.power T n) ≤ (n + 1)^D * r^n) :
    asymptoticRank T ≤ r := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa [Function.comp_def] using (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hpoly : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) / n)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using
      (tendsto_rpow_div_mul_add D 1 (-1) zero_ne_one).comp hbase
  have hlim := hpoly.mul_const (r : ℝ)
  rw [one_mul] at hlim
  apply le_of_tendsto_of_tendsto (tendsto_tensorRank_power_root T) hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hcast : (tensorRank (Tensor.power T n) : ℝ) ≤ ((n : ℝ) + 1)^D * (r : ℝ)^n := by
    exact_mod_cast h n
  calc
    _ ≤ (((n : ℝ) + 1)^D * (r : ℝ)^n) ^ (n : ℝ)⁻¹ :=
      Real.rpow_le_rpow (by positivity) hcast (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.pow_rpow_inv_natCast (by positivity) hn.ne',
        ← Real.rpow_natCast_mul (by positivity), div_eq_mul_inv]

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.RankProfileHistogram
section

/-! # Histograms of the factor indices of a tensor power -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

/-- Counts the positions bearing each pair of a summand index and a basis index. -/
noncomputable def rankProfileHistogram {n r : ℕ} {X : Type*}
    (s : Fin n → Fin r) (x : Fin n → X) (p : Fin r × X) : Fin (n + 1) := by
  classical
  refine ⟨(Finset.univ.filter fun k => (s k, x k) = p).card, Nat.lt_succ_of_le ?_⟩
  simpa using Finset.card_filter_le Finset.univ (fun k => (s k, x k) = p)

/-- The monomial with exponent vector given by the joint histogram. -/
def rankProfileWeight {F X : Type*} [CommMonoid F] [Fintype X] {r n : ℕ}
    (L : Fin r → X → F) (a : Fin r × X → Fin (n + 1)) : F :=
  ∏ p, L p.1 p.2 ^ (a p : ℕ)

/-- Grouping the factors in a tensor-power term by their pair of indices gives its weight. -/
theorem rankProfileWeight_histogram {F X : Type*} [CommMonoid F] [Fintype X] {r n : ℕ}
    (L : Fin r → X → F) (s : Fin n → Fin r) (x : Fin n → X) :
    rankProfileWeight L (rankProfileHistogram s x) = ∏ k, L (s k) (x k) := by
  classical
  simpa only [rankProfileWeight, rankProfileHistogram, Finset.prod_const] using
    Finset.prod_fiberwise' Finset.univ (fun k => (s k, x k)) (fun p => L p.1 p.2)

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.RankProfiles
section

/-!
# Type-count expansion of bounded-rank tensors

In the expansion of a tensor power, the product of the first-site factors depends
only on the histogram of rank summands and first-site letters. Grouping all three
sites by their histograms gives a fixed spanning family over the ground field.
Each member is itself a sum indexed by the words of rank summands.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

section

noncomputable section

variable {F X Y Z : Type*} [Field F] {r n : ℕ}

/-- Joint multiplicities of a rank summand and a letter in a word of length `n`. -/
abbrev RankProfile (r n : ℕ) (X : Type*) := Fin r × X → Fin (n + 1)

/-- One local histogram at each site of a three-tensor. -/
abbrev TripleRankProfile (r n : ℕ) (X Y Z : Type*) :=
  RankProfile r n X × RankProfile r n Y × RankProfile r n Z

/-- An indicator vector for words of a prescribed joint histogram with `s`. -/
def rankProfileIndicator (s : Fin n → Fin r) (a : RankProfile r n X) (x : Fin n → X) : F := by
  classical
  exact if rankProfileHistogram s x = a then 1 else 0

/-- The tensor counting all rank-summand words with the given three site histograms. -/
def rankProfileTensor (a : RankProfile r n X) (b : RankProfile r n Y) (c : RankProfile r n Z) :
    Tensor F (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∑ s : Fin n → Fin r, Tensor.rankOne
    (rankProfileIndicator s a) (rankProfileIndicator s b) (rankProfileIndicator s c) x y z

theorem rankProfileTensor_rankAtMost (a : RankProfile r n X) (b : RankProfile r n Y)
    (c : RankProfile r n Z) : Tensor.RankAtMost (rankProfileTensor (F := F) a b c) (r ^ n) := by
  unfold rankProfileTensor
  simpa only [rankProfileTensor, Fintype.card_pi_const, Fintype.card_fin] using Tensor.rankAtMost_sum_rankOne
    (fun s => rankProfileIndicator (F := F) s a) (fun s => rankProfileIndicator s b)
    (fun s => rankProfileIndicator s c)

variable [Fintype X] [Fintype Y] [Fintype Z]

/-- The expansion of a rank formula as a linear combination of the profile tensors. -/
theorem power_eq_sum_rankProfileTensors (n : ℕ) (L : Fin r → X → F) (M : Fin r → Y → F)
    (N : Fin r → Z → F) :
    Tensor.power (fun x y z => ∑ i, Tensor.rankOne (L i) (M i) (N i) x y z) n =
      ∑ p : TripleRankProfile r n X Y Z,
        (rankProfileWeight L p.1 * rankProfileWeight M p.2.1 * rankProfileWeight N p.2.2) •
          rankProfileTensor p.1 p.2.1 p.2.2 := by
  classical
  funext x y z
  simp only [Tensor.power, Fintype.prod_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    rankProfileTensor, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun (p : TripleRankProfile r n X Y Z) (s : Fin n → Fin r) => _)]
  apply Finset.sum_congr rfl
  intro s _
  let p : TripleRankProfile r n X Y Z :=
    (rankProfileHistogram s x, rankProfileHistogram s y, rankProfileHistogram s z)
  rw [Finset.sum_eq_single p]
  · simp [p, rankProfileWeight_histogram, Tensor.rankOne, rankProfileIndicator,
      Finset.prod_mul_distrib]
  · rintro ⟨a, b, c⟩ _ hne
    by_cases ha : rankProfileHistogram s x = a <;> by_cases hb : rankProfileHistogram s y = b
    · have hc : rankProfileHistogram s z ≠ c := fun hc => hne (by simp [p, ha, hb, hc])
      simp [Tensor.rankOne, rankProfileIndicator, hc]
    all_goals simp [Tensor.rankOne, rankProfileIndicator, *]
  · simp

/-- Powers of all tensors of rank at most `r` lie in the same profile span. -/
theorem power_mem_span_rankProfileTensors {U : Tensor F X Y Z} {r : ℕ}
    (hU : Tensor.RankAtMost U r) (n : ℕ) : Tensor.power U n ∈ Submodule.span F
      (Set.range (fun p : TripleRankProfile r n X Y Z =>
        rankProfileTensor (F := F) p.1 p.2.1 p.2.2)) := by
  classical
  rcases hU with ⟨L, M, N, rfl⟩
  rw [power_eq_sum_rankProfileTensors]
  exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.RankSpan
section

/-! # Rank of tensors in a finitely generated span -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

/-- A linear combination of a finite family of tensors of rank at most
`s` has rank at most `s` times the size of the family. -/
theorem rankAtMost_of_mem_span {F X Y Z I : Type*} [CommSemiring F] [Fintype I]
    (W : I → Tensor F X Y Z) {s : ℕ} (hW : ∀ i, (W i).RankAtMost s)
    {T : Tensor F X Y Z} (hT : T ∈ Submodule.span F (Set.range W)) :
    T.RankAtMost (Fintype.card I * s) := by
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hT
  choose a b c h using fun i => (hW i).scale (d i)
  let A (p : I × Fin s) := a p.1 p.2
  let B (p : I × Fin s) := b p.1 p.2
  let C (p : I × Fin s) := c p.1 p.2
  have heq : ∑ i, d i • W i = fun x y z =>
      ∑ p, Tensor.rankOne (A p) (B p) (C p) x y z := by
    funext x y z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => congrFun (congrFun (congrFun (h i) x) y) z)
  rw [heq]
  simpa using Tensor.rankAtMost_sum_rankOne A B C

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SpanDescent
section

/-! # Descent of a linear span in a fixed tensor format

A linear retraction from the algebraic closure onto the ground field recovers
a ground-field expansion from a linear combination of scalar-extended tensors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

variable {F X Y Z I : Type*} [Field F] [Fintype I]

/-- A linear dependence expressing a ground tensor in the span of ground
tensors descends from the algebraic closure. -/
theorem mem_span_of_toAlgebraicClosure_mem_span (T : Tensor F X Y Z)
    (W : I → Tensor F X Y Z)
    (h : toAlgebraicClosure T ∈
      Submodule.span (AlgebraicClosure F) (Set.range (fun i => toAlgebraicClosure (W i)))) :
    T ∈ Submodule.span F (Set.range W) := by
  obtain ⟨l, hl⟩ := (Algebra.linearMap F (AlgebraicClosure F)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F (AlgebraicClosure F)).injective)
  have retract (t : F) : l (algebraMap F (AlgebraicClosure F) t) = t :=
    LinearMap.congr_fun hl t
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h
  refine (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨fun i => l (a i), ?_⟩
  funext x y z
  have ha' := congrArg (fun S : Tensor (AlgebraicClosure F) X Y Z => S x y z) ha
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toAlgebraicClosure] at ha' ⊢
  obtain he := congrArg l ha'
  rw [map_sum, retract] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (a i), ← Algebra.smul_def, l.map_smul]
  exact mul_comm _ _

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.BorderComparison
section

/-! # Asymptotic rank is bounded by geometric border rank over every field

For a fixed rank bound, tensor powers of the rank locus lie in the span of a
polynomial number of histogram tensors. Each histogram tensor is defined
over the ground field. A polynomial vanishing argument extends power-span
membership to the closure, and linear descent gives the same expansion over
the ground field. The polynomial factor disappears when taking power roots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

variable {F X Y Z : Type*} [Field F]

private theorem scalarExtension_rankProfileTensor {n r : ℕ}
    (a : RankProfile r n X) (b : RankProfile r n Y) (c : RankProfile r n Z) :
    toAlgebraicClosure (rankProfileTensor (F := F) a b c) =
      rankProfileTensor (F := AlgebraicClosure F) a b c := by
  classical
  funext x y z
  simp [toAlgebraicClosure, rankProfileTensor, Tensor.rankOne, rankProfileIndicator,
    apply_ite (algebraMap F (AlgebraicClosure F))]

private theorem scalarExtension_power (T : Tensor F X Y Z) (n : ℕ) :
    toAlgebraicClosure (Tensor.power T n) = Tensor.power (toAlgebraicClosure T) n := by
  funext x y z
  simp [toAlgebraicClosure, Tensor.power]

variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Uniform rank bound for powers of a tensor in the geometric rank-`r` closure. -/
theorem tensorRank_power_le_of_geometricBorderRankAtMost {T : Tensor F X Y Z} {r : ℕ}
    (hT : GeometricBorderRankAtMost T r) (n : ℕ) :
    tensorRank (Tensor.power T n) ≤
      (n + 1) ^ (r * Fintype.card X + r * Fintype.card Y + r * Fintype.card Z) * r ^ n := by
  classical
  let W := fun p : TripleRankProfile r n X Y Z => rankProfileTensor (F := F) p.1 p.2.1 p.2.2
  have hW : Tensor.power T n ∈ Submodule.span F (Set.range W) := by
    apply mem_span_of_toAlgebraicClosure_mem_span
    simp only [W, scalarExtension_power, scalarExtension_rankProfileTensor]
    exact power_mem_span_of_closure hT _ (fun _ hS => power_mem_span_rankProfileTensors hS n)
  have hbound := tensorRank_le_of_rankAtMost (rankAtMost_of_mem_span W
    (fun p => rankProfileTensor_rankAtMost p.1 p.2.1 p.2.2) hW)
  simpa only [TripleRankProfile, RankProfile, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, pow_add, Nat.mul_assoc] using hbound

/-- The middle inequality of the paper's rank comparison, including finite ground fields. -/
theorem asymptoticRank_le_geometricBorderRank (T : Tensor F X Y Z) :
    asymptoticRank T ≤ geometricBorderRank T :=
  asymptoticRank_le_of_polynomial_power_bound T (geometricBorderRank T) _
    (tensorRank_power_le_of_geometricBorderRankAtMost (geometricBorderRankAtMost_geometricBorderRank T))

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.BookRank
section

/-! # The finite rank theorem from a spectral book

The input to the reduction is price data on the *metric* book. It consists
of a monotone, intersecting-submodular diagonal price, the half-perimeter upper bound for each page triangle, and normalized tensor
evaluations pricing the three wires by their lengths. Constructing these
data over a field is the geometric part of the manuscript.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped NNReal

section

/-- The wire evaluations of a spectral point in a placement of three sites.
The factor `d` is the price of the common binary diagonal at the three sites. -/
structure PlacedWires (F : Type*) [Field F] {X : Type*} [PseudoMetricSpace X]
    (p : Fin 3 → X) (d : ℝ) where
  point : RankFunctional F
  nonneg : 0 ≤ d
  price12 (n : ℕ) (hn : 0 < n) :
    d * Real.logb 2 (point.value (wire12 F n)) = dist (p 0) (p 1) * Real.logb 2 n
  price23 (n : ℕ) (hn : 0 < n) :
    d * Real.logb 2 (point.value (wire23 F n)) = dist (p 1) (p 2) * Real.logb 2 n
  price31 (n : ℕ) (hn : 0 < n) :
    d * Real.logb 2 (point.value (wire31 F n)) = dist (p 2) (p 0) * Real.logb 2 n

/-- Multiplying the wires and comparing their evaluation to asymptotic
rank gives the rank bound at any placement. -/
theorem PlacedWires.wireSum_le {F : Type*} [Field F] {X : Type*} [PseudoMetricSpace X]
    {p : Fin 3 → X} {d : ℝ} (w : PlacedWires F p d)
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    dist (p 0) (p 1) * Real.logb 2 x + dist (p 1) (p 2) * Real.logb 2 y +
        dist (p 2) (p 0) * Real.logb 2 z ≤
      d * Real.logb 2 (asymptoticRank (matrixTensor F x y z)) := by
  let φ := w.point
  let T := matrixTensor F x y z
  have e : φ.value T = φ.value (wire12 F x) * φ.value (wire23 F y) * φ.value (wire31 F z) := by
    dsimp only [T]
    rw [matrixTensor_eq_wireProduct, φ.pullback_equiv, φ.product, φ.product]
  have hreal {a : ℝ≥0} (h : 1 ≤ a) : 0 < (a : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one h)
  have h12 : 0 < (φ.value (wire12 F x) : ℝ) := hreal (φ.one_le_of_entry_one
    (x := (⟨0,hx⟩ : Fin x)) (y := ⟨0,hx⟩) (z := ()) (by simp [wire12]))
  have h23 : 0 < (φ.value (wire23 F y) : ℝ) := hreal (φ.one_le_of_entry_one
    (x := ()) (y := (⟨0,hy⟩ : Fin y)) (z := ⟨0,hy⟩) (by simp [wire23]))
  have h31 : 0 < (φ.value (wire31 F z) : ℝ) := hreal (φ.one_le_of_entry_one
    (x := (⟨0,hz⟩ : Fin z)) (y := ()) (z := ⟨0,hz⟩) (by simp [wire31]))
  have hT : 0 < (φ.value T : ℝ) := by rw [e]; push_cast; positivity
  have h := mul_le_mul_of_nonneg_left
    (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hT (φ.le_asymptoticRank T)) w.nonneg
  rw [e, NNReal.coe_mul, NNReal.coe_mul, Real.logb_mul (mul_pos h12 h23).ne' h31.ne',
    Real.logb_mul h12.ne' h23.ne', mul_add, mul_add] at h
  exact (show _ from (w.price12 x hx ▸ w.price23 y hy ▸ w.price31 z hz ▸ h))

/-- The geometric data used from the spectral book and its pages in the
finite rectangular theorem. The quantified evaluations act on tensors over
the specified ground field. -/
structure PlanarBookPrices (F : Type*) [Field F] where
  diagonal : Finset (Book ℝ) → ℝ
  monotone : Monotone diagonal
  submodular : IntersectingSubmodular diagonal
  base : diagonal bookBase = 2
  triangle (r : Fin 3 → ℝ≥0) (i : Fin 3) : diagonal (insert (bookTip r i) bookBase) ≤
    (dist (bookSpine (-1)) (bookSpine 1) + dist (bookSpine 1) (bookTip r i) +
      dist (bookTip r i) (bookSpine (-1))) / 2
  wires (r : Fin 3 → ℝ≥0) (hr : ∀ i, 0 < r i) :
    PlacedWires F (bookTip r) (diagonal (Finset.univ.image (bookTip r)))

variable {F : Type*} [Field F]

/-- Inequality (height-bound) for the actual asymptotic tensor rank. -/
theorem PlanarBookPrices.heightTest (B : PlanarBookPrices F) {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    HeightTest (loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z))
      (Real.logb 2 (asymptoticRank (matrixTensor F x y z))) := by
  classical
  intro a ha
  let r (i : Fin 3) : ℝ≥0 := ⟨a i, (ha i).le⟩
  let w := B.wires r (fun i => ha i)
  have h := w.wireSum_le hx hy hz
  rw [bookTip_dist r (by decide : (0 : Fin 3) ≠ 1),
    bookTip_dist r (by decide : (1 : Fin 3) ≠ 2),
    bookTip_dist r (by decide : (2 : Fin 3) ≠ 0)] at h
  have hb := bookTip_price_le_of_triangle_le B.monotone B.submodular r B.base (B.triangle r)
  have hflat := matrix_flattening_le_asymptoticRank F hx hy hz
  have hone : 1 ≤ max (z * x) (max (x * y) (y * z)) :=
    le_trans (Nat.mul_pos hz hx) (le_max_left _ _)
  have hL := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    ((Nat.one_le_cast.mpr hone).trans hflat)
  calc
    _ = ((r 0 : ℝ) + r 1) * Real.logb 2 x + ((r 1 : ℝ) + r 2) * Real.logb 2 y +
          ((r 2 : ℝ) + r 0) * Real.logb 2 z := by
      change _ = (a 0 + a 1) * Real.logb 2 x + (a 1 + a 2) * Real.logb 2 y +
        (a 2 + a 0) * Real.logb 2 z
      simp [Fin.sum_univ_three, loads]
      ring
    _ ≤ _ := h
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hb hL

/-- The conclusion of the paper's rectangular rank theorem over a fixed field. -/
def RectangularRankBound (F : Type*) [Field F] : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z →
    let T := matrixTensor F x y z
    let m := loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z)
    RadicalTest m (Real.logb 2 (asymptoticRank T)) ∧
      RadicalTest m (Real.logb 2 (geometricBorderRank T)) ∧
      RadicalTest m (Real.logb 2 (tensorRank T))

theorem PlanarBookPrices.rectangularRankBound (B : PlanarBookPrices F) : RectangularRankBound F := by
  intro x y z hx hy hz
  dsimp only
  have h := B.heightTest hx hy hz
  have hlog (q : ℕ) (hq : 0 < q) := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    (Nat.one_le_cast.mpr hq)
  have hm := loads_nonneg (hlog x hx) (hlog y hy) (hlog z hz)
  have hl := matrix_flattening_le_asymptoticRank F hx hy hz
  have hn : 0 < max (z * x) (max (x * y) (y * z)) :=
    lt_of_lt_of_le (Nat.mul_pos hz hx) (le_max_left _ _)
  have hpos := lt_of_lt_of_le (Nat.cast_pos.mpr hn) hl
  have cmp := asymptoticRank_le_geometricBorderRank (matrixTensor F x y z)
  have hborder := h.mono (Real.logb_le_logb_of_le (by norm_num) hpos cmp)
  exact ⟨h.radicalTest hm, hborder.radicalTest hm, (hborder.mono
    (Real.logb_le_logb_of_le (by norm_num) (hpos.trans_le cmp)
      (Nat.cast_le.mpr (geometricBorderRank_le_tensorRank _)))).radicalTest hm⟩

/-- The stated square arithmetic bound follows over a field admitting the
price data. All circuit equalities in `formalOmega` are formal identities. -/
theorem PlanarBookPrices.square_exponent (B : PlanarBookPrices F) :
    3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 :=
  formalOmega_square_lower_bound_of_rank_bound
    (fun x y z hx hy hz => (B.rectangularRankBound x y z hx hy hz).2.2)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.WireEvaluation
section

/-! # The price of each matrix multiplication wire

A normalized spectral evaluation on three sites gives a monotone multiplicative
function of the dimension on each of the three wires. Hence its logarithmic
wire price is its binary wire price times the logarithm of the dimension.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open MatrixMultiplication.Foundation
open scoped NNReal
namespace RankFunctional

variable {F : Type*} [Field F] (φ : RankFunctional F)

/-- The normalized values of the three wires in cyclic order. -/
def wireValue (e : Fin 3) (n : ℕ) : ℝ≥0 :=
  ![φ.value (wire12 F n), φ.value (wire23 F n), φ.value (wire31 F n)] e

theorem wireValue_mono (e : Fin 3) : Monotone (φ.wireValue e) := by
  intro m n h
  let f := Fin.castLE h
  have hf : Function.Injective f := Fin.castLE_injective h
  fin_cases e
  · have hp : Tensor.pullback f f id (wire12 F n) = wire12 F m := by
      funext i j k
      simp [Tensor.pullback, wire12, hf.eq_iff]
    change φ.value (wire12 F m) ≤ _
    rw [← hp]
    exact φ.pullback_le _ _ _ _
  · have hp : Tensor.pullback id f f (wire23 F n) = wire23 F m := by
      funext i j k
      simp [Tensor.pullback, wire23, hf.eq_iff]
    change φ.value (wire23 F m) ≤ _
    rw [← hp]
    exact φ.pullback_le _ _ _ _
  · have hp : Tensor.pullback f id f (wire31 F n) = wire31 F m := by
      funext i j k
      simp [Tensor.pullback, wire31, hf.eq_iff]
    change φ.value (wire31 F m) ≤ _
    rw [← hp]
    exact φ.pullback_le _ _ _ _

theorem wireValue_one (e : Fin 3) : φ.wireValue e 1 = 1 := by
  let f : Unit ≃ Fin 1 := Equiv.ofUnique _ _
  let D := Tensor.diagonal (K := F) (Fin 1)
  fin_cases e
  · have hp : Tensor.pullback (Equiv.refl (Fin 1)) (Equiv.refl (Fin 1)) f D = wire12 F 1 := by
      funext i j k
      have heq : ∀ u v : Fin 1, u = v := fun _ _ => Subsingleton.elim _ _
      simp [Tensor.pullback, wire12, D, Tensor.diagonal]
      grind
    change φ.value (wire12 F 1) = 1
    rw [← hp, φ.pullback_equiv, φ.diagonal, Nat.cast_one]
  · have hp : Tensor.pullback f (Equiv.refl (Fin 1)) (Equiv.refl (Fin 1)) D = wire23 F 1 := by
      funext i j k
      have heq : ∀ u v : Fin 1, u = v := fun _ _ => Subsingleton.elim _ _
      simp [Tensor.pullback, wire23, D, Tensor.diagonal]
      grind
    change φ.value (wire23 F 1) = 1
    rw [← hp, φ.pullback_equiv, φ.diagonal, Nat.cast_one]
  · have hp : Tensor.pullback (Equiv.refl (Fin 1)) f (Equiv.refl (Fin 1)) D = wire31 F 1 := by
      funext i j k
      have heq : ∀ u v : Fin 1, u = v := fun _ _ => Subsingleton.elim _ _
      simp [Tensor.pullback, wire31, D, Tensor.diagonal]
      grind
    change φ.value (wire31 F 1) = 1
    rw [← hp, φ.pullback_equiv, φ.diagonal, Nat.cast_one]

theorem wireValue_mul (e : Fin 3) (m n : ℕ) :
    φ.wireValue e (m * n) = φ.wireValue e m * φ.wireValue e n := by
  let f : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  let u : Unit × Unit ≃ Unit := Equiv.prodUnique Unit Unit
  fin_cases e
  · have hp : Tensor.pullback f f u (wire12 F (m * n)) =
        Tensor.product (wire12 F m) (wire12 F n) := by
      funext i j k
      simp [Tensor.pullback, Tensor.product, wire12, Prod.ext_iff, ite_and, mul_ite]
      grind
    change φ.value (wire12 F (m * n)) = φ.value (wire12 F m) * φ.value (wire12 F n)
    rw [← φ.product, ← hp, φ.pullback_equiv]
  · have hp : Tensor.pullback u f f (wire23 F (m * n)) =
        Tensor.product (wire23 F m) (wire23 F n) := by
      funext i j k
      simp [Tensor.pullback, Tensor.product, wire23, Prod.ext_iff, ite_and, mul_ite]
      grind
    change φ.value (wire23 F (m * n)) = φ.value (wire23 F m) * φ.value (wire23 F n)
    rw [← φ.product, ← hp, φ.pullback_equiv]
  · have hp : Tensor.pullback f u f (wire31 F (m * n)) =
        Tensor.product (wire31 F m) (wire31 F n) := by
      funext i j k
      simp [Tensor.pullback, Tensor.product, wire31, Prod.ext_iff, ite_and, mul_ite]
      grind
    change φ.value (wire31 F (m * n)) = φ.value (wire31 F m) * φ.value (wire31 F n)
    rw [← φ.product, ← hp, φ.pullback_equiv]

/-- The value of a wire of arbitrary positive order is determined by its
binary value at the same placement. -/
theorem wireValue_eq_rpow (e : Fin 3) {n : ℕ} (hn : 0 < n) :
    (φ.wireValue e n : ℝ) = (n : ℝ) ^ Real.logb 2 (φ.wireValue e 2) := by
  exact dimension_value_eq_rpow (v := fun q => (φ.wireValue e q : ℝ))
    (fun _ _ hij => by exact_mod_cast φ.wireValue_mono e hij)
    (by simp [φ.wireValue_one]) (fun m q => by simp [φ.wireValue_mul]) hn

/-- Formula for the logarithmic price of a wire on any of the three edges. -/
theorem logb_wireValue (e : Fin 3) {n : ℕ} (hn : 0 < n) :
    Real.logb 2 (φ.wireValue e n) = Real.logb 2 (φ.wireValue e 2) * Real.logb 2 n := by
  rw [φ.wireValue_eq_rpow e hn, Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]

end RankFunctional

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.BinaryWirePlacement
section

/-! # Recovering placed wires from binary distances

The metric is specified by the price of a binary wire. The dimension law
extends each of these identities to all positive wire dimensions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
section

/-- It suffices to identify the three binary wire prices with the three
distances in a placement. -/
def PlacedWires.ofBinary {F : Type*} [Field F] {X : Type*} [PseudoMetricSpace X]
    {p : Fin 3 → X} {d : ℝ} (φ : RankFunctional F) (hd : 0 ≤ d)
    (h12 : d * Real.logb 2 (φ.value (wire12 F 2)) = dist (p 0) (p 1))
    (h23 : d * Real.logb 2 (φ.value (wire23 F 2)) = dist (p 1) (p 2))
    (h31 : d * Real.logb 2 (φ.value (wire31 F 2)) = dist (p 2) (p 0)) :
    PlacedWires F p d where
  point := φ
  nonneg := hd
  price12 n hn := by
    have h := φ.logb_wireValue 0 hn
    change Real.logb 2 (φ.value (wire12 F n)) = Real.logb 2 (φ.value (wire12 F 2)) * _ at h
    rw [h, ← mul_assoc, h12]
  price23 n hn := by
    have h := φ.logb_wireValue 1 hn
    change Real.logb 2 (φ.value (wire23 F n)) = Real.logb 2 (φ.value (wire23 F 2)) * _ at h
    rw [h, ← mul_assoc, h23]
  price31 n hn := by
    have h := φ.logb_wireValue 2 hn
    change Real.logb 2 (φ.value (wire31 F n)) = Real.logb 2 (φ.value (wire31 F 2)) * _ at h
    rw [h, ← mul_assoc, h31]

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SpectralSpace
section

/-! # Prices of tensors placed in a metric space

Each tensor has one finite-dimensional coordinate space per index. A map of the
indices groups all factors in each fiber at one site, including the scalar slot
of an empty fiber. Thus prices indexed by arbitrary lists of sites also handle
collisions, relabelings and insertion of trivial slots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
section

namespace SiteTensor.Raw

variable {I J K : Type*} [Fintype I]

/-- Group the local coordinates over the fibers of a placement. -/
def group (T : SiteTensor.Raw I K) (σ : I → J) : SiteTensor.Raw J K where
  Leg := fun j => (i : {i : I // σ i = j}) → T.Leg i.1
  finiteLeg := fun _ => inferInstance
  coeff := fun x => T.coeff (fun i => x (σ i) ⟨i, rfl⟩)

/-- Grouping sites preserves the underlying array of coefficients up to a bijection. -/
theorem group_ne_zero_iff [Zero K] (T : SiteTensor.Raw I K) (σ : I → J) :
    (T.group σ).coeff ≠ 0 ↔ T.coeff ≠ 0 := by
  constructor
  · intro h hzero
    exact h (funext fun x => congrFun hzero _)
  · intro h hzero
    apply h
    exact funext fun x => congrFun hzero (fun _ i => x i.1)

end SiteTensor.Raw

open SiteTensor

/-- Prices of finite nonzero placed tensors over a fixed field, with the price at
the zero tensor extended by zero. The normalization is the price of the binary
diagonal on the occupied sites. The transport and diameter bounds are the
corresponding estimates in the manuscript's preliminaries. -/
structure SpectralPlacementPrices (K : Type*) [Field K] (X : Type*) [PseudoMetricSpace X] where
  price {I : Type} [Fintype I] (T : Raw.{0} I K) (x : I → X) : ℝ
  zero_tensor {I : Type} [Fintype I] (T : Raw.{0} I K) (h : T.coeff = 0) (x : I → X) :
    price T x = 0
  collapsed {I : Type} [Fintype I] (T : Raw.{0} I K) (p : X) : price T (fun _ => p) = 0
  group {I J : Type} [Fintype I] [Fintype J] (T : Raw.{0} I K) (σ : I → J) (x : J → X) :
    price T (x ∘ σ) = price (T.group σ) x
  wire (x : Fin 2 → X) : price (Raw.diagonal (Fin 2) K (Fin 2)) x = dist (x 0) (x 1)
  transport {I : Type} [Fintype I] (T : Raw.{0} I K) (x y : I → X) :
    dist (price T x) (price T y) ≤ ∑ i, dist (x i) (y i) * Real.logb 2 (Fintype.card (T.Leg i))
  dist_le_diagonal {I : Type} [Fintype I] (x : I → X) (i j : I) :
    dist (x i) (x j) ≤ price (Raw.diagonal I K (Fin 2)) x
  normalized {I : Type} [Fintype I] [Nontrivial I] (x : I ↪ X) :
    ∃ φ : normalizedSpectrum (fun a b : TensorClass.{0} I K => a ≤ b), ∀ T : Raw.{0} I K,
      T.coeff ≠ 0 → price T x =
        price (Raw.diagonal I K (Fin 2)) x * Real.logb 2 (φ.val (ofRaw T) : ℝ)

namespace SpectralPlacementPrices

variable {K X : Type*} [Field K] [PseudoMetricSpace X]

/-- Restrict all tensor prices to an isometrically embedded metric subspace. -/
def pullback {Y : Type*} [MetricSpace Y] (P : SpectralPlacementPrices K X) (f : Y → X)
    (hf : Isometry f) : SpectralPlacementPrices K Y where
  price T x := P.price T (f ∘ x)
  zero_tensor T h x := P.zero_tensor T h (f ∘ x)
  collapsed T p := P.collapsed T (f p)
  group T σ x := P.group T σ (f ∘ x)
  wire x := (P.wire (f ∘ x)).trans (hf.dist_eq (x 0) (x 1))
  transport T x y := by simpa only [Function.comp_apply, hf.dist_eq] using P.transport T (f ∘ x) (f ∘ y)
  dist_le_diagonal x i j := by simpa only [Function.comp_apply, hf.dist_eq] using P.dist_le_diagonal (f ∘ x) i j
  normalized x := P.normalized (x.trans ⟨f, hf.injective⟩)

/-- On an injective placement with at least two sites the diagonal normalization
is strictly positive. -/
theorem diagonal_pos {Y : Type*} [MetricSpace Y] (P : SpectralPlacementPrices K Y)
    {I : Type} [Fintype I] [Nontrivial I] (x : I ↪ Y) :
    0 < P.price (Raw.diagonal I K (Fin 2)) x := by
  obtain ⟨i, j, hne⟩ := exists_pair_ne I
  exact (dist_pos.mpr (x.injective.ne hne)).trans_le (P.dist_le_diagonal x i j)

/-- For any map to a fixed finite set of distinct sites, a single spectral
point computes the prices of every tensor after its indices are grouped at
those sites. The number of tensor indices and their multiplicities can vary. -/
theorem normalized_group {Y : Type*} [MetricSpace Y] (P : SpectralPlacementPrices K Y)
    {J : Type} [Fintype J] [Nontrivial J] (y : J ↪ Y) :
    ∃ φ : normalizedSpectrum (fun a b : TensorClass.{0} J K => a ≤ b),
      0 < P.price (Raw.diagonal J K (Fin 2)) y ∧
      ∀ {I : Type} [Fintype I] (σ : I → J) (T : Raw.{0} I K), T.coeff ≠ 0 →
        P.price T (y ∘ σ) = P.price (Raw.diagonal J K (Fin 2)) y *
          Real.logb 2 (φ.val (ofRaw (T.group σ)) : ℝ) := by
  obtain ⟨φ, hφ⟩ := P.normalized y
  refine ⟨φ, P.diagonal_pos y, ?_⟩
  intro I _ σ T hT
  exact (P.group T σ y).trans (hφ _ ((T.group_ne_zero_iff σ).2 hT))

end SpectralPlacementPrices

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.TensorGroupRaw
section

/-! # Grouping local indices along a placement

A matrix acting at an occupied site is the tensor product of the matrices
on its preimages. This makes grouping monotone for arbitrary placements.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

open scoped Classical

/-- Regrouping a coordinate tuple over the fibers of a placement is a bijection. -/
def groupIndexEquiv {I J : Type*} (σ : I → J) (A : I → Type*) :
    (∀ i, A i) ≃ (∀ j, (t : {i // σ i = j}) → A t.1) :=
  Equiv.piCongrFiberwise (fun _ => Equiv.refl _)

@[simp] theorem groupIndexEquiv_apply {I J : Type*} (σ : I → J) (A : I → Type*)
    (a : ∀ i, A i) (j : J) (t : {i // σ i = j}) : groupIndexEquiv σ A a j t = a t.1 := rfl

@[simp] theorem groupIndexEquiv_symm_apply {I J : Type*} (σ : I → J) (A : I → Type*)
    (a : ∀ j, (t : {i // σ i = j}) → A t.1) (i : I) :
    (groupIndexEquiv σ A).symm a i = a (σ i) ⟨i, rfl⟩ := rfl

namespace Raw

variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]

/-- Grouped matrices are Kronecker products inside each fiber of the placement. -/
theorem group_restricts (σ : I → J) {X Y : Raw I K} (h : X.Restricts Y) :
    (X.group σ).Restricts (Y.group σ) := by
  classical
  obtain ⟨M, hM⟩ := h
  refine ⟨fun j b a => ∏ i : {i // σ i = j}, M i.1 (b i) (a i), fun x => ?_⟩
  change X.coeff ((groupIndexEquiv σ X.Leg).symm x) = _
  rw [hM]
  refine Fintype.sum_equiv (groupIndexEquiv σ Y.Leg) _ _ fun a => ?_
  apply congrArg (Y.coeff a * ·)
  let w (p : Σ j, {i // σ i = j}) := M p.2.1 (x p.1 p.2) (a p.2.1)
  calc
    _ = ∏ p, w p := Fintype.prod_equiv (Equiv.sigmaFiberEquiv σ).symm _ _ (fun i => rfl)
    _ = _ := Fintype.prod_sigma w

/-- Grouping commutes with the tensor product by collecting first and second coordinates. -/
theorem group_mul_equivalent (σ : I → J) (X Y : Raw I K) :
    ((X.mul Y).group σ).Equivalent ((X.group σ).mul (Y.group σ)) := by
  apply reindex_equivalent (fun j =>
    Equiv.arrowProdEquivProdArrow {i // σ i = j} (fun i => X.Leg i.1) (fun i => Y.Leg i.1))
  intro x
  rfl

/-- A grouped product of singleton bases still represents the scalar unit. -/
theorem group_one_equivalent (σ : I → J) :
    ((one I K).group σ).Equivalent (one J K) := by
  let (j : J) : Unique (((one I K).group σ).Leg j) := inferInstanceAs (Unique (∀ _ : {i // σ i = j}, PUnit))
  apply reindex_equivalent (fun _ => Equiv.equivPUnit _)
  intro x
  rfl

/-- A nonempty fiber contains an empty factor when every original leg is empty. -/
theorem group_zero_equivalent (σ : I → J) (hs : Function.Surjective σ) :
    ((zero I K).group σ).Equivalent (zero J K) := by
  classical
  have (j : J) : IsEmpty (((zero I K).group σ).Leg j) := by
    obtain ⟨i, hi⟩ := hs j
    exact ⟨fun x => (x ⟨i, hi⟩).elim⟩
  apply reindex_equivalent (fun _ => Equiv.equivPEmpty _)
  intro x
  rfl

end Raw
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.Push
section

/-! # Padding the local coordinate spaces with zeros -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

open Crossing

variable {I K : Type*} [Fintype I] [CommSemiring K]
variable {A B : I → Type*} [∀ i, Fintype (A i)]

/-- Pushing the coefficients along local functions is a restriction, with each
basis vector sent to the basis vector indexed by its image. -/
theorem pushCoeff_restricts (f : ∀ i, A i → B i) (X : (∀ i, A i) → K) :
    IsRestriction (pushCoeff (fun x i => f i (x i)) X) X := by
  refine ⟨fun i b a => if f i a = b then 1 else 0, fun x => ?_⟩
  simp only [pushCoeff, Fintype.prod_boole, ← funext_iff, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

/-- An injection of basis indices at each site pads a tensor with zeros.
The coordinate projections restrict the padded tensor back to the original. -/
theorem equivalent_pushCoeff [∀ i, Fintype (B i)] (f : ∀ i, A i ↪ B i)
    (X : (∀ i, A i) → K) :
    IsRestriction X (pushCoeff (fun x i => f i (x i)) X) ∧
    IsRestriction (pushCoeff (fun x i => f i (x i)) X) X := by
  refine ⟨?_, pushCoeff_restricts (fun i => f i) X⟩
  refine ⟨fun i a b => if b = f i a then 1 else 0, fun x => ?_⟩
  rw [sum_pushCoeff_mul]
  simp [Fintype.prod_boole, ← funext_iff, mul_ite]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.TensorGroupAdd
section

/-! # Grouping a direct sum over occupied sites -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Classical

namespace SiteTensor.Raw

universe v

variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]

/-- Grouping sends uniform summand tags to uniform tags at every old site in a fiber.
Surjectivity ensures at least one old site is available to distinguish the tags. -/
private def groupedTags (σ : I → J) (hs : Function.Surjective σ) (A B : I → Type v) (j : J) :
    ((∀ t : {i // σ i = j}, A t.1) ⊕ (∀ t : {i // σ i = j}, B t.1)) ↪
      (∀ t : {i // σ i = j}, A t.1 ⊕ B t.1) where
  toFun := Sum.elim (fun a t => Sum.inl (a t)) (fun b t => Sum.inr (b t))
  inj' := by
    obtain ⟨i, hi⟩ := hs j
    intro a b h
    cases a <;> cases b
    · congr 1
      funext t
      exact Sum.inl.inj (congrFun h t)
    · cases congrFun h ⟨i, hi⟩
    · cases congrFun h ⟨i, hi⟩
    · congr 1
      funext t
      exact Sum.inr.inj (congrFun h t)

omit [Fintype J] in
private theorem group_eq_push (σ : I → J) (X : Raw.{v} I K) :
    (X.group σ).coeff = pushCoeff (groupIndexEquiv σ X.Leg) X.coeff := by
  funext x
  exact (pushCoeff_equiv (groupIndexEquiv σ X.Leg) X.coeff x).symm

/-- Grouping sites along a surjection preserves direct sums up to local restriction. -/
theorem group_add_equivalent (σ : I → J) (hs : Function.Surjective σ) (X Y : Raw.{v} I K) :
    ((X.add Y).group σ).Equivalent ((X.group σ).add (Y.group σ)) := by
  let g := groupedTags σ hs X.Leg Y.Leg
  let e := groupIndexEquiv σ (fun i => X.Leg i ⊕ Y.Leg i)
  let S := (X.group σ).add (Y.group σ)
  have h : ((X.add Y).group σ).coeff = pushCoeff (fun x j => g j (x j)) S.coeff := by
    rw [group_eq_push]
    change pushCoeff e (pushCoeff (fun x i => Sum.inl (x i)) X.coeff +
      pushCoeff (fun y i => Sum.inr (y i)) Y.coeff) =
      pushCoeff (fun (x : ∀ j, (X.group σ).Leg j ⊕ (Y.group σ).Leg j) j => g j (x j)) (pushCoeff (fun x j => Sum.inl (x j)) (X.group σ).coeff +
        pushCoeff (fun y j => Sum.inr (y j)) (Y.group σ).coeff)
    rw [group_eq_push, group_eq_push, pushCoeff_add, pushCoeff_add]
    congr 1 <;> (erw [pushCoeff_comp, pushCoeff_comp, pushCoeff_comp]) <;> rfl
  have hg := equivalent_pushCoeff g S.coeff
  unfold Equivalent Restricts
  rw [h]
  exact ⟨hg.2, hg.1⟩

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.DiagonalEmbedding
section

/-! # Embedding the labels of a diagonal tensor -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor.Raw

universe u v w

variable (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [CommSemiring K]
variable {α β : Type v} [Fintype α] [Fintype β]

/-- Coordinate projections at every site restrict a diagonal to an embedded label set. -/
theorem diagonal_restricts_of_embedding (e : α ↪ β) :
    (diagonal I K α).Restricts (diagonal I K β) := by
  classical
  unfold Restricts diagonal
  refine ⟨fun _ a b => if b = e a then 1 else 0, fun x => ?_⟩
  simp_rw [Fintype.prod_boole]
  have heq (y : I → β) : (∀ i, y i = e (x i)) ↔ y = fun i => e (x i) :=
    funext_iff.symm
  simp only [heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  let i₀ : I := Classical.choice inferInstance
  rw [Finset.sum_eq_single (x i₀), Finset.sum_eq_single (e (x i₀))]
  · simp [funext_iff]
  · intro b _ hb
    exact if_neg fun h => (hb (congrFun h i₀).symm).elim
  · simp
  · intro a _ ha
    exact if_neg fun h => (ha (congrFun h i₀).symm).elim
  · simp

/-- A larger diagonal restricts to every diagonal with at most as many labels. -/
theorem diagonal_restricts_of_card_le (h : Fintype.card α ≤ Fintype.card β) :
    (diagonal I K α).Restricts (diagonal I K β) := by
  apply diagonal_restricts_of_embedding
  exact (Fintype.equivFin α).toEmbedding.trans
    ((Fin.castLEEmb h).trans (Fintype.equivFin β).symm.toEmbedding)

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping
section

/-! # Grouping placed tensors on restriction classes

Even with unoccupied sites, grouping commutes with tensor products and is
monotone for restriction. Applied to a diagonal of arbitrary label dimension,
any normalized spectral point therefore evaluates a power of that dimension.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

noncomputable section
open scoped NNReal

universe v u u' w
variable {I : Type u} {J : Type u'} {K : Type w} [Fintype I] [Fintype J] [CommSemiring K]

/-- Group local indices over the fibers of a placement at the level of tensor classes. -/
def groupClass (σ : I → J) : TensorClass.{v} I K → TensorClass.{max u v} J K :=
  Quotient.map (fun X => X.group σ) fun _ _ h =>
    ⟨Raw.group_restricts σ h.1, Raw.group_restricts σ h.2⟩

@[simp] theorem groupClass_ofRaw (σ : I → J) (X : Raw.{v} I K) :
    groupClass σ (ofRaw X) = ofRaw (X.group σ) := rfl

theorem groupClass_mono (σ : I → J) : Monotone (groupClass (K := K) σ) :=
  fun X Y => Quotient.inductionOn₂ X Y fun _ _ => Raw.group_restricts σ

/-- Arbitrary (possibly colliding) placements preserve products and the scalar unit. -/
def groupMulHom [Nonempty I] [Nonempty J] (σ : I → J) :
    TensorClass.{v} I K →* TensorClass.{max u v} J K where
  toFun := groupClass σ
  map_one' := ofRaw_eq_iff.mpr (Raw.group_one_equivalent σ)
  map_mul' X Y := Quotient.inductionOn₂ X Y fun x y =>
    ofRaw_eq_iff.mpr (Raw.group_mul_equivalent σ x y)

/-- Grouping along a surjection also preserves direct sums, because each grouped
site can distinguish the two uniform tags. -/
def groupRingHom [Nonempty I] [Nonempty J] (σ : I → J) (hs : Function.Surjective σ) :
    TensorClass.{v} I K →+* TensorClass.{max u v} J K where
  __ := groupMulHom σ
  map_zero' := ofRaw_eq_iff.mpr (Raw.group_zero_equivalent σ hs)
  map_add' X Y := Quotient.inductionOn₂ X Y fun x y =>
    ofRaw_eq_iff.mpr (Raw.group_add_equivalent σ hs x y)

/-- Pull back a normalized spectral point when sites have been identified. -/
def groupSpectralPoint [Nonempty I] [Nonempty J] (σ : I → J) (hs : Function.Surjective σ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{max u v} J K → _ → Prop)) :
    normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop) := by
  let ψ := (normalizedSpectrum.toRingHom φ).comp (groupRingHom σ hs)
  exact ⟨ψ, ψ.map_zero, ψ.map_one, ψ.map_add, ψ.map_mul,
    fun x y h => φ.property.2.2.2.2 _ _ (groupClass_mono σ h)⟩

section Logarithms

variable {A B : Type} {F : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Field F]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} B F → _ → Prop))

/-- A grouped diagonal, including a wire with arbitrary endpoints, has log price
equal to its binary price times the base-two logarithm of its dimension. -/
theorem rawLogPrice_group_diagonal (σ : A → B) (c : ℝ) {α : Type} [Fintype α] [Nonempty α] :
    rawLogPrice φ c ((Raw.diagonal A F α).group σ) =
      rawLogPrice φ c ((Raw.diagonal A F (Fin 2)).group σ) * Real.logb 2 (Fintype.card α) := by
  let v : TensorClass.{0} A F →* ℝ≥0 := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (groupMulHom σ)
  have hv : ∀ {m n : ℕ}, 0 < m → m ≤ n → v m ≤ v n := by
    intro m n _ h
    apply φ.property.2.2.2.2
    apply groupClass_mono σ
    rw [← ofRaw_diagonal_fin_eq_natCast A F m, ← ofRaw_diagonal_fin_eq_natCast A F n]
    exact Raw.diagonal_restricts_of_embedding A F (Fin.castLEEmb h)
  have h := spectral_natCast_logb v hv (Fintype.card α) Fintype.card_pos
  have eval (β : Type) [Fintype β] : φ.val (ofRaw ((Raw.diagonal A F β).group σ)) =
      v (Fintype.card β : TensorClass.{0} A F) := by
    rw [← ofRaw_diagonal_eq_natCast A F β]
    rfl
  rw [rawLogPrice, rawLogPrice, eval α, eval (Fin 2), Fintype.card_fin, Nat.cast_ofNat, h, mul_assoc]

end Logarithms
end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.SpectralDiagonal
section

/-! # The binary diagonal price on occupied sites

A finite site set is enumerated by `Fin S.card` to allow arbitrary ambient
universes. Grouping repeated labels onto their occupied sites preserves its
binary diagonal class because surjective grouping is a semiring homomorphism.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace SpectralPlacementPrices

open SiteTensor

variable {K X : Type*} [Field K] [PseudoMetricSpace X] (P : SpectralPlacementPrices K X)

/-- The binary diagonal price of the finite set of occupied sites, extended by zero
on the empty set. -/
def diagonal (S : Finset X) : ℝ :=
  if S.Nonempty then P.price (Raw.diagonal (Fin S.card) K (Fin 2))
    (fun i ↦ (S.equivFin.symm i).val) else 0

@[simp] theorem diagonal_empty : P.diagonal ∅ = 0 := by simp [diagonal]

/-- On an injective placement equivalent nonzero tensors have equal prices. -/
theorem price_eq_of_class_eq {I : Type} [Fintype I] [Nonempty I] (p : I ↪ X)
    {T V : Raw.{0} I K} (he : ofRaw T = ofRaw V) : P.price T p = P.price V p := by
  cases subsingleton_or_nontrivial I with
  | inl hs =>
    let i : I := Classical.choice inferInstance
    have e : (p : I → X) = fun _ ↦ p i := funext (fun j ↦ congrArg p (Subsingleton.elim j i))
    rw [e, P.collapsed, P.collapsed]
  | inr ht =>
    by_cases hT : T.coeff = 0
    · have hV := (ofRaw_eq_zero_iff V).mp (he.symm.trans ((ofRaw_eq_zero_iff T).mpr hT))
      rw [P.zero_tensor T hT, P.zero_tensor V hV]
    · have hV : V.coeff ≠ 0 := fun h ↦ hT ((ofRaw_eq_zero_iff T).mp
        (he.trans ((ofRaw_eq_zero_iff V).mpr h)))
      obtain ⟨φ, hφ⟩ := P.normalized p
      rw [hφ T hT, hφ V hV, he]

/-- The price of the binary full diagonal on any nonempty list of labels
depends only on the occupied set. This includes all collisions. -/
theorem price_binaryDiagonal_eq {I : Type} [Fintype I] [Nonempty I] (p : I → X) :
    P.price (Raw.diagonal I K (Fin 2)) p = P.diagonal (Finset.univ.image p) := by
  let S := Finset.univ.image p
  have hS : S.Nonempty := Finset.univ_nonempty.image p
  let x : Fin S.card ↪ X := S.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
  let σ (i : I) := S.equivFin ⟨p i, Finset.mem_image_of_mem p (Finset.mem_univ i)⟩
  have hσ : Function.Surjective σ := by
    intro j
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (S.equivFin.symm j).property
    refine ⟨i, S.equivFin.symm.injective ?_⟩
    exact Subtype.ext (by simpa only [σ, Equiv.symm_apply_apply] using hi)
  have hp : p = x ∘ σ := funext (fun i ↦ by simp [x, σ])
  have : Nonempty (Fin S.card) := ⟨σ (Classical.choice inferInstance)⟩
  change P.price _ p = P.diagonal S
  rw [diagonal, if_pos hS, hp, P.group]
  apply P.price_eq_of_class_eq x
  change groupClass σ (ofRaw (Raw.diagonal I K (Fin 2))) = _
  rw [ofRaw_diagonal_fin_eq_natCast, ofRaw_diagonal_fin_eq_natCast]
  exact map_natCast (groupRingHom σ hσ) 2

@[simp] theorem diagonal_singleton (x : X) : P.diagonal {x} = 0 := by
  have h := P.price_binaryDiagonal_eq (fun _ : Unit ↦ x)
  rw [P.collapsed, Finset.image_const Finset.univ_nonempty] at h
  exact h.symm

theorem diagonal_pair (x y : X) : P.diagonal {x, y} = dist x y := by
  have h := P.price_binaryDiagonal_eq ![x, y]
  rw [P.wire] at h
  simpa [Finset.univ_fin2] using h.symm

/-- The binary diagonal pays at most one unit of price per unit displacement
of each index, including collisions at either endpoint. -/
theorem diagonal_transport {I : Type} [Fintype I] (p q : I → X) :
    dist (P.diagonal (Finset.univ.image p)) (P.diagonal (Finset.univ.image q)) ≤
      ∑ i, dist (p i) (q i) := by
  cases isEmpty_or_nonempty I with
  | inl => simp
  | inr =>
    rw [← P.price_binaryDiagonal_eq, ← P.price_binaryDiagonal_eq]
    have h := P.transport (Raw.diagonal I K (Fin 2)) p q
    simpa [Raw.diagonal, Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))] using h

/-- Restricting tensor prices along an isometry restricts their finite-set
diagonal to the isometric image. -/
theorem diagonal_pullback {Y : Type*} [MetricSpace Y] (f : Y → X) (hf : Isometry f) (S : Finset Y) :
    (P.pullback f hf).diagonal S = P.diagonal (S.image f) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  let z (i : Fin S.card) := (S.equivFin.symm i).val
  have : Nonempty (Fin S.card) := Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hS)
  have himage : Finset.univ.image (f ∘ z) = S.image f := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, (S.equivFin.symm i).prop, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨S.equivFin ⟨y,hy⟩, by simp [z]⟩
  rw [← himage, ← P.price_binaryDiagonal_eq, diagonal, if_pos hS]
  rfl

end SpectralPlacementPrices

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.PlacementDiagonal
section

/-! # Partial diagonals at a finite placement

Grouping a diagonal along an injection assigns a single label at each site
of its image and a trivial slot elsewhere. Hence the prices of all subsets of
one finite placement can be read from its single normalized spectral point.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

section

open SiteTensor

namespace SiteTensor.Raw

/-- Grouping by an injection produces the common diagonal on its image. -/
theorem ofRaw_group_diagonal_eq_mask {J I : Type} {K : Type*} [Fintype I] [Nonempty I]
    [Fintype J] [Field K] (σ : J ↪ I) (S : Finset I)
    (hS : ∀ i, i ∈ S ↔ ∃ j, σ j = i) (α : Type) [Fintype α] :
    ofRaw ((diagonal J K α).group σ) = ofRaw (maskDiagonal K S α) := by
  classical
  let fiber (i : I) (h : i ∈ S) : {j : J // σ j = i} :=
    ⟨((hS i).mp h).choose, ((hS i).mp h).choose_spec⟩
  have unique (i : I) (a b : {j : J // σ j = i}) : a = b :=
    Subtype.ext (σ.injective (a.property.trans b.property.symm))
  let e (i : I) : ((j : {j : J // σ j = i}) → α) ≃ (i ∈ S → α) :=
    { toFun := fun x h ↦ x (fiber i h)
      invFun := fun x j ↦ x ((hS i).mpr ⟨j, j.property⟩)
      left_inv := fun x ↦ funext fun j ↦ congrArg x (unique i _ j)
      right_inv := fun _ ↦ rfl }
  apply ofRaw_eq_iff.mpr (reindex_equivalent e ?_)
  intro x
  simp only [Raw.group, Raw.diagonal, Raw.maskDiagonal, Crossing.basisTensor]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply propext
  constructor
  · intro hx
    funext i hi
    change x i (fiber i hi) = a
    obtain ⟨j, hj⟩ := fiber i hi
    subst i
    exact congrFun hx j
  · intro hx
    funext j
    have hj : σ j ∈ S := (hS _).mpr ⟨j,rfl⟩
    exact (congrArg (x _) (unique _ _ (fiber _ hj))).trans (congrFun (congrFun hx _) hj)

end SiteTensor.Raw

namespace SpectralPlacementPrices

variable {K X : Type*} [Field K] [PseudoMetricSpace X]

theorem diagonal_nonneg (P : SpectralPlacementPrices K X) (S : Finset X) : 0 ≤ P.diagonal S := by
  classical
  by_cases h : S.Nonempty
  · simp only [diagonal, h, ite_true]
    let i : Fin S.card := ⟨0, Finset.card_pos.mpr h⟩
    simpa only [dist_self] using P.dist_le_diagonal
      (fun j : Fin S.card ↦ (S.equivFin.symm j).val) i i
  · simp [diagonal, h]

/-- At an injective placement one point evaluates the prices of all of its
nonempty subsets. -/
theorem exists_point_diagonal_map (P : SpectralPlacementPrices K X) {I : Type}
    [Fintype I] [Nontrivial I] (x : I ↪ X) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop),
      ∃ c : ℝ, 0 ≤ c ∧ ∀ (S : Finset I), S.Nonempty →
        P.diagonal (S.map x) =
          c * Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K S (Fin 2))) : ℝ) := by
  classical
  obtain ⟨φ, hφ⟩ := P.normalized x
  let c := P.price (Raw.diagonal I K (Fin 2)) x
  have hc : 0 ≤ c := by
    let i := Classical.arbitrary I
    simpa only [dist_self] using P.dist_le_diagonal x i i
  refine ⟨φ, c, hc, ?_⟩
  intro S hS
  let σ : S ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hs (i : I) : i ∈ S ↔ ∃ j, σ j = i := by
    constructor
    · intro hi
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.property
  have hocc : Finset.univ.image (x ∘ σ) = S.map x := by
    ext y
    simp [σ, Function.comp_def]
  let _ : Nonempty S := hS.to_subtype
  have hd : (Raw.diagonal S K (Fin 2)).coeff ≠ 0 := by
    obtain ⟨s,hs'⟩ := hS
    intro hz
    have he (a : Fin 2) : ((fun _ : S ↦ (0 : Fin 2)) = fun _ ↦ a) ↔ a = 0 :=
      ⟨fun h ↦ (congrFun h ⟨s,hs'⟩).symm, by rintro rfl; rfl⟩
    have h : (Raw.diagonal S K (Fin 2)).coeff (fun _ ↦ (0 : Fin 2)) = 0 :=
      congrFun hz _
    simp [Raw.diagonal, he] at h
  rw [← hocc, ← P.price_binaryDiagonal_eq, P.group, hφ _ ((Raw.group_ne_zero_iff _ _).mpr hd),
    Raw.ofRaw_group_diagonal_eq_mask σ S hs]

end SpectralPlacementPrices

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.LinearAlgebra.SpectralBooks.PlacedSpectralWires
section

/-! # Matrix multiplication wires at an injective placement

All three edge prices and the full diagonal price are evaluated at the same
three-site spectral point. This converts the binary metric-price law of a
spectral space into wire evaluations in every positive dimension.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped Classical NNReal
noncomputable section

section

open SiteTensor

/-- When every site is occupied, the masked diagonal is the full diagonal. -/
theorem SiteTensor.ofRaw_maskDiagonal_univ {I F : Type*} [Fintype I] [Field F]
    (α : Type) [Fintype α] :
    ofRaw (Raw.maskDiagonal F (Finset.univ : Finset I) α) = ofRaw (Raw.diagonal I F α) := by
  let e (i : I) : MaskLeg Finset.univ α i ≃ α :=
    { toFun := fun g => g (Finset.mem_univ i)
      invFun := fun a _ => a
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  simp only [Raw.maskDiagonal, Crossing.basisTensor, Raw.diagonal]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  apply propext
  constructor
  · rintro rfl
    rfl
  · exact fun h => funext (fun i => funext (fun _ => congrFun h i))

section
variable {F X : Type*} [Field F] [PseudoMetricSpace X]

private theorem wire_scale {P : SpectralPlacementPrices F X} {e : Fin 3 ↪ X}
    {φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) F → _ → Prop)} {c : ℝ}
    (hm : ∀ S : Finset (Fin 3), S.Nonempty → P.diagonal (S.map e) =
      c * Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal F S (Fin 2))) : ℝ)) :
    P.diagonal (Finset.univ.image e) = c := by
  have h := hm Finset.univ Finset.univ_nonempty
  have he := map_natCast (normalizedSpectrum.toRingHom φ) 2
  change φ.val (2 : TensorClass.{0} (Fin 3) F) = 2 at he
  rw [ofRaw_maskDiagonal_univ, ofRaw_diagonal_fin_eq_natCast] at h
  simpa [Finset.map_eq_image, he, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

/-- The three binary wire distances in a spectral placement provide the
normalized functional for all positive matrix multiplication wire sizes. -/
def SpectralPlacementPrices.placedWires (P : SpectralPlacementPrices F X) (e : Fin 3 ↪ X) :
    PlacedWires F e (P.diagonal (Finset.univ.image e)) := by
  apply Classical.choice
  let d := P.diagonal (Finset.univ.image e)
  obtain ⟨φ, c, _, hm⟩ := P.exists_point_diagonal_map e
  have hdc : d = c := wire_scale hm
  have hpair (i j : Fin 3) : d * Real.logb 2
      (φ.val (ofRaw (Raw.maskDiagonal F {i,j} (Fin 2))) : ℝ) = dist (e i) (e j) := by
    rw [hdc, ← hm {i,j} (by simp), Finset.map_insert, Finset.map_singleton, P.diagonal_pair]
  refine ⟨PlacedWires.ofBinary (rankFunctionalOfSpectrum φ) (P.diagonal_nonneg _) ?_ ?_ ?_⟩
  · change d * Real.logb 2 (φ.val (ofRaw (ofThree (wire12 F 2))) : ℝ) = _
    rw [ofRaw_ofThree_wire12]
    exact hpair 0 1
  · change d * Real.logb 2 (φ.val (ofRaw (ofThree (wire23 F 2))) : ℝ) = _
    rw [ofRaw_ofThree_wire23]
    exact hpair 1 2
  · change d * Real.logb 2 (φ.val (ofRaw (ofThree (wire31 F 2))) : ℝ) = _
    rw [ofRaw_ofThree_wire31]
    exact hpair 2 0

end
end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Prices
section

/-! # Diagonal prices and the equality-filter cost recurrence -/

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

noncomputable section

variable {I F : Type*} [Fintype I] [Nonempty I] [Field F]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I F → _ → Prop))

/-- Naming the labels by any finite nonempty alphabet preserves the price formula. -/
theorem rawLogPrice_maskDiagonal_card (c : ℝ) (S : Finset I) (hS : S.Nonempty)
    (α : Type) [Fintype α] [Nonempty α] :
    rawLogPrice φ c (Raw.maskDiagonal F S α) =
      maskDiagonalPrice φ c S * Real.logb 2 (Fintype.card α) := by
  classical
  have he := ofRaw_maskDiagonal_equiv (K := F) S hS (Fintype.equivFin α)
  calc
    _ = rawLogPrice φ c (Raw.maskDiagonal F S (Fin (Fintype.card α))) :=
      congrArg (fun z ↦ c * Real.logb 2 (φ.val z : ℝ)) he
    _ = _ := rawLogPrice_maskDiagonal φ c S hS Fintype.card_pos

/-- The value before taking logarithms, for an arbitrary finite alphabet. -/
theorem spectralValue_maskDiagonal_card (S : Finset I) (hS : S.Nonempty)
    (α : Type) [Fintype α] [Nonempty α] :
    (φ.val (ofRaw (Raw.maskDiagonal F S α)) : ℝ) =
      (Fintype.card α : ℝ) ^ maskDiagonalPrice φ 1 S := by
  classical
  have hp : 0 < (φ.val (ofRaw (Raw.maskDiagonal F S α)) : ℝ) := by
    exact_mod_cast zero_lt_one.trans_le
      (one_le_raw_spectralValue φ _ (Raw.maskDiagonal_ne_zero S hS α))
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (Real.strictMonoOn_logb (by norm_num : (1 : ℝ) < 2)).injOn hp
    (Real.rpow_pos_of_pos hc _)
  rw [Real.logb_rpow_eq_mul_logb_of_pos hc]
  simpa only [rawLogPrice, one_mul] using rawLogPrice_maskDiagonal_card φ 1 S hS α

/-- The full support costs one unit per shared bit at every normalized point. -/
@[simp] theorem maskDiagonalPrice_univ (c : ℝ) :
    maskDiagonalPrice φ c (Finset.univ : Finset I) = c := by
  have hv := map_natCast (normalizedSpectrum.toRingHom φ) 2
  change φ.val (2 : TensorClass.{0} I F) = 2 at hv
  simp [maskDiagonalPrice, rawLogPrice, ofRaw_maskDiagonal_univ, hv]

theorem maskDiagonalPrice_le_one (S : Finset I) : maskDiagonalPrice φ 1 S ≤ 1 := by
  classical
  simpa only [maskDiagonalPrice_univ] using
    maskDiagonalPrice_mono φ (zero_le_one : (0 : ℝ) ≤ 1) (Finset.subset_univ S)

/-- Value of a raw tensor as a real number. -/
abbrev spectralValue (X : Raw.{0} I F) : ℝ := (φ.val (ofRaw X) : ℝ)

theorem spectralValue_pos {X : Raw.{0} I F} (h : X.coeff ≠ 0) : 0 < spectralValue φ X := by
  exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ X h)

@[simp] theorem spectralValue_mul (X Y : Raw.{0} I F) :
    spectralValue φ (X.mul Y) = spectralValue φ X * spectralValue φ Y := by
  simp only [spectralValue, ofRaw_mul, φ.property.2.2.2.1, NNReal.coe_mul]

@[simp] theorem spectralValue_add (X Y : Raw.{0} I F) :
    spectralValue φ (X.add Y) = spectralValue φ X + spectralValue φ Y := by
  simp only [spectralValue, ofRaw_add, φ.property.2.2.1, NNReal.coe_add]

theorem logb_spectralValue_div {U V : Raw.{0} I F} (hU : U.coeff ≠ 0)
    (hV : V.coeff ≠ 0) :
    Real.logb 2 (spectralValue φ U / spectralValue φ V) =
      rawLogPrice φ 1 U - rawLogPrice φ 1 V := by
  rw [Real.logb_div (spectralValue_pos φ hU).ne' (spectralValue_pos φ hV).ne']
  simp only [rawLogPrice, spectralValue, one_mul]

/-- A correction of known logarithmic cost, discounted by the matching labels. -/
theorem spectralRatio_div_maskDiagonal_le {U V : Raw.{0} I F} (hU : U.coeff ≠ 0)
    (hV : V.coeff ≠ 0) (S : Finset I) (hS : S.Nonempty)
    (α : Type) [Fintype α] [Nonempty α] {c : ℝ}
    (hc : rawLogPrice φ 1 U - rawLogPrice φ 1 V ≤ c) :
    spectralValue φ U / (spectralValue φ V * spectralValue φ (Raw.maskDiagonal F S α)) ≤
      (2 : ℝ) ^ (c - maskDiagonalPrice φ 1 S * Real.logb 2 (Fintype.card α)) := by
  classical
  have hD := spectralValue_pos φ (Raw.maskDiagonal_ne_zero (K := F) S hS α)
  rw [← div_div]
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (div_pos (div_pos (spectralValue_pos φ hU) (spectralValue_pos φ hV)) hD)).mp
  rw [Real.logb_div (div_pos (spectralValue_pos φ hU) (spectralValue_pos φ hV)).ne' hD.ne',
    logb_spectralValue_div φ hU hV]
  have hprice := rawLogPrice_maskDiagonal_card φ 1 S hS α
  simp only [rawLogPrice, one_mul] at hprice
  rw [show Real.logb 2 (spectralValue φ (Raw.maskDiagonal F S α)) = _ from hprice]
  exact sub_le_sub_right hc _

/-- The exact ratio recurrence for one equality-filter step, with `D` the
diagonal bearing the nonzero matching index. The direct sum is taken on the
whole set of sites, so the denominator retains the ambient price of `D`. -/
theorem spectralRatio_filter_step (R Q U V D : Raw.{0} I F)
    (hQ : Q.coeff ≠ 0) (hV : V.coeff ≠ 0) (hD : D.coeff ≠ 0) :
    spectralValue φ ((R.mul (V.mul D)).add (Q.mul U)) /
        spectralValue φ (Q.mul (V.mul D)) =
      spectralValue φ R / spectralValue φ Q +
        spectralValue φ U / (spectralValue φ V * spectralValue φ D) := by
  simp only [spectralValue_add, spectralValue_mul]
  field_simp [(spectralValue_pos φ hQ).ne', (spectralValue_pos φ hV).ne',
    (spectralValue_pos φ hD).ne']

end
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Summability
section

/-! # Summing the costs of recursive equality tests -/

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- Each increment uses up at most the difference between two successive
terms of a geometrically decreasing reserve. -/
theorem filterRatio_bounded_of_affine {f : ℕ → ℝ} {A d : ℝ} (hd : 0 < d)
    (hstep : ∀ b : ℕ, f (b + 1) ≤ f b + (2 : ℝ) ^ (A - d * (b : ℝ))) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ b, f b ≤ M := by
  let q := (2 : ℝ) ^ (-d)
  have hq : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hd)
  have hq₀ : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  let reserve := (2 : ℝ) ^ A / (1 - q)
  have hr : reserve * (1 - q) = (2 : ℝ) ^ A := by
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hq.ne')
  have hr₀ : 0 ≤ reserve := div_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_nonneg.mpr hq.le)
  have budget (b : ℕ) : f b + reserve * q ^ b ≤ f 0 + reserve := by
    induction b with
    | zero => simp
    | succ b ih =>
      have h := hstep b
      rw [show A - d * (b : ℝ) = A + -d * (b : ℝ) by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_mul_natCast (by norm_num)] at h
      change f (b + 1) ≤ f b + (2 : ℝ) ^ A * q ^ b at h
      rw [← hr] at h
      rw [pow_succ]
      linarith only [h, ih]
  refine ⟨max 1 (f 0 + reserve), le_max_left .., fun b => ?_⟩
  exact (le_add_of_nonneg_right (mul_nonneg hr₀ (pow_nonneg hq₀ _))).trans
    ((budget b).trans (le_max_right ..))

/-- There are at least `2^b` nonzero matching indices on `b+1` bits. -/
theorem matchingIndex_log_lower (b : ℕ) :
    (b : ℝ) ≤ Real.logb 2 ((2 ^ (b + 1) - 1 : ℕ) : ℝ) := by
  have h : 2 ^ b ≤ 2 ^ (b + 1) - 1 := by
    have hp : 0 < 2 ^ b := pow_pos (by decide) _
    rw [pow_succ]
    omega
  have h' : (2 : ℝ) ^ b ≤ ((2 ^ (b + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast h
  have hp : 0 < ((2 ^ (b + 1) - 1 : ℕ) : ℝ) := (pow_pos (by norm_num) _).trans_le h'
  apply (Real.le_logb_iff_rpow_le (by norm_num) hp).2
  simpa using h'

/-- Dividing a correction by the price of all nonzero matching indices
leaves an exponentially decaying increment. The correction cost is measured
in base-two logarithms. -/
theorem filterIncrement_le_of_cost (b : ℕ) {u v θ d B : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hθ : 0 ≤ θ)
    (hc : Real.logb 2 u - Real.logb 2 v ≤ (θ - d) * ((b : ℝ) + 1) + B) :
    u / (v * ((2 ^ (b + 1) - 1 : ℕ) : ℝ) ^ θ) ≤
      (2 : ℝ) ^ ((B + θ - d) - d * (b : ℝ)) := by
  have hl : 0 < ((2 ^ (b + 1) - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega : b + 1 ≠ 0))
  have hpow := Real.rpow_pos_of_pos hl θ
  apply (Real.logb_le_iff_le_rpow (by norm_num) (div_pos hu (mul_pos hv hpow))).1
  rw [Real.logb_div hu.ne' (mul_pos hv hpow).ne', Real.logb_mul hv.ne' hpow.ne',
    Real.logb_rpow_eq_mul_logb_of_pos hl]
  linarith only [hc, mul_le_mul_of_nonneg_left (matchingIndex_log_lower b) hθ]

/-- For any strictly positive gap a single integral coding parameter makes
the two broadcast overhead slopes strictly smaller than half the gap. -/
theorem exists_broadcastParameter {θ g : ℝ} (hg : 0 < g) :
    ∃ h : ℕ, 1 ≤ h ∧ (12 / (h : ℝ)) * θ < g / 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (24 * θ / g)
  refine ⟨n + 1, by omega, ?_⟩
  have hn' : 24 * θ < (n : ℝ) * g := (div_lt_iff₀ hg).mp hn
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (↑(n + 1) : ℝ))).mpr
  push_cast
  linarith

end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Alphabet
section

/-! # Transporting an arbitrary finite alphabet to binary words -/

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {I α β : Type*}

/-- Relabel all coordinates of a word by the same alphabet embedding. -/
def wordEmbedding (e : α ↪ β) : (I → α) ↪ (I → β) where
  toFun w c := e (w c)
  inj' _ _ h := funext fun c => e.injective (congrFun h c)

theorem admissible_relabel_iff {ι : Type*} (e : α ↪ β) {f : ι → α} :
    Admissible (fun i => e (f i)) ↔ Admissible f := by
  constructor
  · rintro (h | h)
    · exact Or.inl fun i j => e.injective (h i j)
    · exact Or.inr fun _ _ he => h (congrArg e he)
  · rintro (h | h)
    · exact Or.inl fun i j => congrArg e (h i j)
    · exact Or.inr (e.injective.comp h)

theorem wordFree_map_iff {r : ℕ} (e : α ↪ β) (W : Finset (I → α)) :
    WordFree r (W.map (wordEmbedding e)) ↔ WordFree r W := by
  constructor
  · intro h w hw hadm i j
    apply (wordEmbedding e).injective
    apply h (fun t => wordEmbedding e (w t))
    · exact fun t => Finset.mem_map.mpr ⟨_, hw t, rfl⟩
    · exact fun c => (admissible_relabel_iff e).mpr (hadm c)
  · intro h w hw hadm i j
    choose v hv heq using fun t => Finset.mem_map.mp (hw t)
    have hword : WordAdmissible v := by
      intro c
      apply (admissible_relabel_iff e).mp
      change Admissible (fun i => wordEmbedding e (v i) c)
      simpa only [heq] using hadm c
    rw [← heq i, ← heq j, h v hv hword i j]

/-- A one-hot encoding into `n` bits works for every cardinal, including zero. -/
def Binary.alphabetEmbedding (n : ℕ) : Fin n ↪ Binary.Word n where
  toFun x i := if x = i then 1 else 0
  inj' x y h := by
    by_contra hne
    exact hne (show y = x by simpa using congrFun h x).symm

/-- Passing to a binary-word alphabet preserves both the cardinality and sunflower-freeness. -/
theorem exists_binary_word_family {r n : ℕ} {W : Finset (I → Fin n)} (h : WordFree r W) :
    ∃ B : Finset (I → Binary.Word n), B.card = W.card ∧ WordFree r B :=
  ⟨_, Finset.card_map _, (wordFree_map_iff (Binary.alphabetEmbedding n) W).mpr h⟩

end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.FilterBound
section

/-! # A uniform price for testing equality

The resource ratio at each step increases by the cost of one correction divided
by the value of the diagonal of all nonzero directions. A strictly positive
gap makes the resulting increments summable independently of the alphabet.
-/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

noncomputable section

open Binary Control

variable {I : Type*} [Fintype I] [Nonempty I]

private theorem coeff_ne_zero_of_value_pos
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    {X : Raw.{0} I ℂ} (hX : 0 < spectralValue φ X) : X.coeff ≠ 0 := by
  intro h
  simp [spectralValue, (ofRaw_eq_zero_iff X).mpr h, φ.property.1] at hX

omit [Nonempty I] in
/-- A filter remains correct after restricting its controls to an embedded alphabet. -/
theorem EqualityMaps.precompose {P T : Finset I} {R Q : Raw.{0} I ℂ}
    {A B : Type} (e : B ↪ A) (h : EqualityMaps P T A R Q) :
    EqualityMaps P T B R Q := by
  obtain ⟨M, hM⟩ := h
  refine ⟨pre (fun _ => e) M, ?_⟩
  intro x y c hc₁ hc₂ o
  rw [eval_pre, hM (e x) (e y) (fun i => e (c i))
    (fun i hi => congrArg e (hc₁ i hi)) (fun i hi => congrArg e (hc₂ i hi))]
  simp

private theorem bounded_filter_induction
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (P T : Finset I) (hK : (P ∪ T).Nonempty) {d B : ℝ} (hd : 0 < d)
    (hbase : EqualityMaps P T (Word 0) (Raw.one I ℂ) (Raw.one I ℂ))
    (hstep : ∀ (b : ℕ) (R Q : Raw.{0} I ℂ), EqualityMaps P T (Word b) R Q →
      ∃ U V : Raw.{0} I ℂ, U.coeff ≠ 0 ∧ V.coeff ≠ 0 ∧
        rawLogPrice φ 1 U - rawLogPrice φ 1 V ≤
          (maskDiagonalPrice φ 1 (P ∪ T) - d) * ((b : ℝ) + 1) + B ∧
        let D := Raw.maskDiagonal ℂ (P ∪ T) (Direction (b + 1))
        EqualityMaps P T (Word (b + 1))
          ((R.mul (V.mul D)).add (Q.mul U)) (Q.mul (V.mul D))) :
    ∃ C : ℝ, ∀ n : ℕ, ∃ R Q : Raw.{0} I ℂ, R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧
      rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤ C ∧ EqualityMaps P T (Fin n) R Q := by
  classical
  let θ := maskDiagonalPrice φ 1 (P ∪ T)
  let f : ℕ → ℝ := Nat.rec 1 (fun b f => f + (2 : ℝ) ^ ((B + θ - d) - d * (b : ℝ)))
  have hf (b : ℕ) : f (b + 1) = f b + (2 : ℝ) ^ ((B + θ - d) - d * (b : ℝ)) := rfl
  obtain ⟨M, hM, hbound⟩ := filterRatio_bounded_of_affine hd (fun b => (hf b).le)
  have hlevels (b : ℕ) : ∃ R Q : Raw.{0} I ℂ, R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧
      spectralValue φ R / spectralValue φ Q ≤ f b ∧ EqualityMaps P T (Word b) R Q := by
    induction b with
    | zero =>
      have hn : (Raw.one.{0} I ℂ).coeff ≠ 0 := by
        exact fun he => one_ne_zero (congrFun he (fun _ => PUnit.unit))
      refine ⟨_, _, hn, hn, ?_, hbase⟩
      simp [f, (spectralValue_pos φ hn).ne']
    | succ b ih =>
      obtain ⟨R, Q, hR, hQ, hratio, hmaps⟩ := ih
      obtain ⟨U, V, hU, hV, hc, hnext⟩ := hstep b R Q hmaps
      let D := Raw.maskDiagonal ℂ (P ∪ T) (Direction (b+1))
      have hD : D.coeff ≠ 0 := Raw.maskDiagonal_ne_zero _ hK _
      have hvalD : spectralValue φ D = ((2 ^ (b+1) - 1 : ℕ) : ℝ) ^ θ := by
        simpa [D, θ] using spectralValue_maskDiagonal_card φ (P ∪ T) hK (Direction (b+1))
      have hinc := filterIncrement_le_of_cost b (d := d) (B := B) (spectralValue_pos φ hU)
        (spectralValue_pos φ hV) (maskDiagonalPrice_nonneg φ zero_le_one (P ∪ T))
        (by simpa [rawLogPrice, spectralValue] using hc)
      have hR' : 0 < spectralValue φ ((R.mul (V.mul D)).add (Q.mul U)) := by
        simp only [spectralValue_add, spectralValue_mul]
        exact add_pos (mul_pos (spectralValue_pos φ hR)
          (mul_pos (spectralValue_pos φ hV) (spectralValue_pos φ hD)))
          (mul_pos (spectralValue_pos φ hQ) (spectralValue_pos φ hU))
      have hQ' : 0 < spectralValue φ (Q.mul (V.mul D)) := by
        simp only [spectralValue_mul]
        exact mul_pos (spectralValue_pos φ hQ)
          (mul_pos (spectralValue_pos φ hV) (spectralValue_pos φ hD))
      refine ⟨_, _, coeff_ne_zero_of_value_pos φ hR', coeff_ne_zero_of_value_pos φ hQ', ?_, hnext⟩
      rw [spectralRatio_filter_step φ R Q U V D hQ hV hD, hvalD, hf]
      exact add_le_add hratio hinc
  refine ⟨Real.logb 2 M, fun n => ?_⟩
  obtain ⟨R, Q, hR, hQ, hratio, hmaps⟩ := hlevels n
  refine ⟨R, Q, hR, hQ, ?_, hmaps.precompose (alphabetEmbedding n)⟩
  have hposR := spectralValue_pos φ hR
  have hposQ := spectralValue_pos φ hQ
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (div_pos hposR hposQ) (hratio.trans (hbound n))
  simpa [rawLogPrice, spectralValue, Real.logb_div hposR.ne' hposQ.ne'] using hl

/-- Corrections with a strictly smaller slope than the price of the direction
diagonal yield bounded-cost equality filters for every finite alphabet. -/
theorem exists_equality_filter_of_corrections
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (P T : Finset I) (hK : (P ∪ T).Nonempty) {d B : ℝ} (hd : 0 < d)
    (hcorr : ∀ b : ℕ, ∃ U V : Raw.{0} I ℂ, U.coeff ≠ 0 ∧ V.coeff ≠ 0 ∧
      rawLogPrice φ 1 U - rawLogPrice φ 1 V ≤
        (maskDiagonalPrice φ 1 (P ∪ T) - d) * ((b : ℝ) + 1) + B ∧
      CorrectionMaps P T b U V) :
    ∃ C : ℝ, ∀ n : ℕ, ∃ R Q : Raw.{0} I ℂ, R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧
      rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤ C ∧ EqualityMaps P T (Fin n) R Q := by
  apply bounded_filter_induction φ P T hK hd (B := B)
  · exact equalityMaps_one P T
  · intro b R Q hmaps
    obtain ⟨U, V, hU, hV, hc, hC⟩ := hcorr b
    exact ⟨U, V, hU, hV, hc, filter_step_maps (Classical.choice inferInstance) hmaps hC⟩

end
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Fourier
section

/-! # Character matrices for a shared-label resource

A mask diagonal with the character group as labels implements a zero-sum
constraint. Each matrix can depend on a local control and a local output index.
-/

namespace OAI
namespace Combinatorics
namespace Sunflower

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators Classical

noncomputable section

variable {I : Type*} [Fintype I]

/-- Contracting matrices with a partial diagonal only sums over its shared label. -/
theorem maskDiagonal_apply {α : Type} [Fintype α] (K : Finset I)
    (M : ∀ i, MaskLeg K α i → ℂ) :
    (∑ a : ∀ i, (Raw.maskDiagonal ℂ K α).Leg i,
      (Raw.maskDiagonal ℂ K α).coeff a * ∏ i, M i (a i)) =
      ∑ t : α, ∏ i, M i (fun _ ↦ t) :=
  contract_maskDiagonal (K := ℂ) (B := fun _ ↦ Unit) K α (fun i _ ↦ M i) (fun _ ↦ ())

variable {Γ : Type} [AddCommGroup Γ] [Fintype Γ] {C B : I → Type*}

/-- The matrix at each site evaluates the shared character on its local
contribution. A designated site supplies the single normalization factor. -/
def fourierMatrix (K : Finset I) (i₀ : I) (phase : ∀ i, C i → B i → Γ)
    (i : I) (c : C i) (x : B i) (a : MaskLeg K (AddChar Γ ℂ) i) : ℂ :=
  (if i = i₀ then (Fintype.card Γ : ℂ)⁻¹ else 1) *
  if h : i ∈ K then a h (phase i c x) else 1

omit [Fintype Γ] in
private theorem char_sum {ι : Type*} (s : Finset ι) (f : ι → Γ) (χ : AddChar Γ ℂ) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, AddChar.map_add_eq_mul, ih]

/-- Fourier contraction implements the indicator that the sum of the local
contributions in the mask vanishes. -/
theorem fourierMatrix_apply (K : Finset I) (i₀ : I) (phase : ∀ i, C i → B i → Γ)
    (c : ∀ i, C i) (x : ∀ i, B i) :
    (∑ a : ∀ i, (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).Leg i,
      (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).coeff a *
        ∏ i, fourierMatrix K i₀ phase i (c i) (x i) (a i)) =
      if (∑ i ∈ K, phase i (c i) (x i)) = 0 then (1 : ℂ) else 0 := by
  classical
  rw [maskDiagonal_apply]
  have hterm (χ : AddChar Γ ℂ) :
      (∏ i, fourierMatrix K i₀ phase i (c i) (x i) (fun _ ↦ χ)) =
        (Fintype.card Γ : ℂ)⁻¹ * χ (∑ i ∈ K, phase i (c i) (x i)) := by
    simp only [fourierMatrix, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
      ite_true, char_sum]
    congr 1
    simp [Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [hterm]
  rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite]
  split_ifs <;> simp [Fintype.card_ne_zero]

/-- The controlled-map form used for composing the zero-sum predicate with
other restrictions. -/
theorem eval_fourierMatrix (K : Finset I) (i₀ : I) (phase : ∀ i, C i → B i → Γ)
    (c : ∀ i, C i) (x : ∀ i, B i) :
    @Control.eval I C (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).Leg B _
        (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).finiteLeg
        (fourierMatrix K i₀ phase) c (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).coeff x =
      if (∑ i ∈ K, phase i (c i) (x i)) = 0 then (1 : ℂ) else 0 :=
  fourierMatrix_apply K i₀ phase c x

/-- The zero-sum predicate for fixed local controls is an ordinary tensor
restriction of the character-labeled partial diagonal. -/
theorem zeroSum_restricts (K : Finset I) (i₀ : I)
    (phase : ∀ i, C i → B i → Γ) (c : ∀ i, C i) :
    Crossing.IsRestriction
      (fun x : ∀ i, B i ↦ if (∑ i ∈ K, phase i (c i) (x i)) = 0 then (1 : ℂ) else 0)
      (Raw.maskDiagonal ℂ K (AddChar Γ ℂ)).coeff :=
  ⟨fun i ↦ fourierMatrix K i₀ phase i (c i), fun x ↦ (fourierMatrix_apply K i₀ phase c x).symm⟩

end

end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.BroadcastCode
section

/-! # Finite codes for broadcasting a common label -/

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- A code for broadcasting a shared label. Each control point lies on the same
sphere. For a fixed control point the source indices lie on another sphere,
in a hyperplane perpendicular to that control. -/
structure BroadcastCode (m q N : ℕ) where
  H : Fin N ↪ (Fin m → Fin q)
  V : Fin N → Fin N ↪ (Fin m → Fin q)
  H_norm : ∀ x y, (∑ j, (H x j : ℕ) ^ 2) = ∑ j, (H y j : ℕ) ^ 2
  V_norm : ∀ x y z, (∑ j, (V x y j : ℕ) ^ 2) = ∑ j, (V x z j : ℕ) ^ 2
  dot_eq : ∀ x y z, (∑ j, (H x j : ℕ) * (V x y j : ℕ)) =
                      ∑ j, (H x j : ℕ) * (V x z j : ℕ)

namespace BroadcastCode

private theorem exists_constant_embedding {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] {N : ℕ} (f : α → β)
    (h : Fintype.card β * N ≤ Fintype.card α) :
    ∃ e : Fin N ↪ α, ∀ x y, f (e x) = f (e y) := by
  classical
  obtain ⟨v, hv⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f h
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin N) (by simpa using hv)
  have hf (x : Fin N) : f (e x) = v := by
    simpa using he (Set.mem_range_self x)
  exact ⟨e, fun x y => (hf x).trans (hf y).symm⟩

private def dot {m q : ℕ} (a b : Fin m → Fin q) : ℕ :=
  ∑ j, (a j : ℕ) * (b j : ℕ)

private theorem dot_le {m q : ℕ} (a b : Fin m → Fin q) :
    dot a b ≤ m * (q - 1) ^ 2 := by
  have hab (j : Fin m) : (a j : ℕ) * (b j : ℕ) ≤ (q - 1) ^ 2 := by
    have ha := (a j).isLt
    have hb := (b j).isLt
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  calc
    _ ≤ ∑ _j : Fin m, (q - 1) ^ 2 := Finset.sum_le_sum fun j _ => hab j
    _ = _ := by simp

/-- Squared norms and inner products take at most `1 + m * (q-1)^2`
values each. The product bound guarantees enough labels even when both are
prescribed by a common fiber. -/
theorem nonempty_of_card {m q N : ℕ}
    (h : (1 + m * (q - 1) ^ 2) ^ 2 * N ≤ q ^ m) :
    Nonempty (BroadcastCode m q N) := by
  let B := 1 + m * (q - 1) ^ 2
  have hB : 0 < B := by dsimp [B]; omega
  let : NeZero B := ⟨Nat.ne_of_gt hB⟩
  let val (a b : Fin m → Fin q) : Fin B := ⟨dot a b, by
    have := dot_le a b
    dsimp [B]
    omega⟩
  let radius (b : Fin m → Fin q) := val b b
  have h₂ : Fintype.card (Fin B × Fin B) * N ≤ Fintype.card (Fin m → Fin q) := by
    simpa [B, pow_two] using h
  obtain ⟨H, hH⟩ := exists_constant_embedding
    (fun b : Fin m → Fin q => (radius b, radius b)) h₂
  have hV (x : Fin N) := exists_constant_embedding
    (fun b : Fin m → Fin q => (radius b, val (H x) b)) h₂
  choose V hV using hV
  refine ⟨⟨H, V, ?_, ?_, ?_⟩⟩
  · intro x y
    simpa [radius, val, dot, pow_two] using
      congrArg (fun z : Fin B × Fin B => z.1.val) (hH x y)
  · intro x y z
    simpa [radius, val, dot, pow_two] using
      congrArg (fun p : Fin B × Fin B => p.1.val) (hV x y z)
  · intro x y z
    exact congrArg (fun p : Fin B × Fin B => p.2.val) (hV x y z)

end BroadcastCode
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.BroadcastParameters
section

/-!
# Parameter bounds for broadcasting a shared label

For the qualitative sunflower theorem, the broadcast slope may exceed one by
any prescribed positive amount.  Fix the box dimension `h + 6` in advance,
then increase its side length with the number of bits.  This gives slope
`1 + 6 / h` with an additive constant independent of the alphabet.
-/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace BroadcastParameters

/-- The dimension of the integer box. Six coordinates pay for two pigeonhole losses. -/
def dim (h : ℕ) : ℕ := h + 6

/-- Bit depth of each coordinate. -/
def depth (h b : ℕ) : ℕ := b / h + dim h + 2

def side (h b : ℕ) : ℕ := 2 ^ depth h b

/-- Every coordinate of either side of the broadcast relation lies below this modulus. -/
def modulus (h b sites : ℕ) : ℕ := 2 ^ (depth h b + sites)

def bits (h b sites : ℕ) : ℕ := (depth h b + sites) * dim h

theorem modulus_pos (h b sites : ℕ) : 0 < modulus h b sites := by
  unfold modulus
  positivity

theorem side_pos (h b : ℕ) : 0 < side h b := by
  unfold side
  positivity

theorem modulus_pow_dim (h b sites : ℕ) :
    modulus h b sites ^ dim h = 2 ^ bits h b sites := by
  rw [modulus, bits, pow_mul]

theorem no_wrap (h b sites : ℕ) :
    sites * (side h b - 1) < modulus h b sites := by
  rw [modulus, pow_add, mul_comm (2 ^ depth h b)]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le (side h b) 1))
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_two_pow_self (n := sites)) (side_pos h b))

private theorem box_bucket_bound (h b : ℕ) :
    1 + dim h * (side h b - 1)^2 ≤ (side h b)^3 := by
  let m := dim h
  let q := side h b
  have hmq : m + 1 ≤ q := by
    have hmd : m ≤ depth h b :=
      (Nat.le_add_left m (b / h)).trans (Nat.le_add_right _ 2)
    have hd := Nat.lt_two_pow_self (n := depth h b)
    exact Nat.succ_le_of_lt (lt_of_le_of_lt hmd hd)
  have hq : 0 < q := side_pos h b
  have sq : 1 ≤ q^2 := Nat.succ_le_of_lt (pow_pos hq 2)
  calc
    1 + m * (q - 1)^2 ≤ q^2 + m * q^2 := by
      gcongr
      exact Nat.sub_le _ _
    _ = (m + 1) * q^2 := by ring
    _ ≤ q * q^2 := Nat.mul_le_mul_right _ hmq
    _ = q^3 := by ring

theorem code_capacity {h : ℕ} (hh : 0 < h) (b : ℕ) :
    (1 + dim h * (side h b - 1)^2)^2 * 2^b ≤ side h b ^ dim h := by
  have hb : b ≤ depth h b * h := by
    have hr := Nat.mod_lt b hh
    have hdiv := Nat.div_add_mod b h
    unfold depth
    rw [Nat.add_mul, Nat.add_mul, mul_comm (b / h)]
    omega
  have hcap : 2^b ≤ side h b ^ h := by
    rw [side, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) hb
  calc
    _ ≤ ((side h b)^3)^2 * side h b ^ h := by
      gcongr
      exact box_bucket_bound h b
    _ = side h b ^ (h + 6) := by rw [← pow_mul, pow_add, mul_comm]

/-- A size bound on the exponent of the diagonal resource. The overhead is
independent of the bit length once the slope parameter and sites are fixed. -/
theorem bits_le {h : ℕ} (hh : 0 < h) (b sites : ℕ) :
    (bits h b sites : ℝ) ≤ (1 + 6 / (h : ℝ)) * b +
      (dim h : ℝ) * ((dim h : ℝ) + 2 + sites) := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hdiv : ((b / h : ℕ) : ℝ) ≤ b / h := Nat.cast_div_le
  unfold bits depth
  push_cast
  calc
    _ ≤ ((b : ℝ) / h + dim h + 2 + sites) * dim h := by gcongr
    _ = _ := by
      unfold dim
      push_cast
      field_simp
      ring

end BroadcastParameters
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Rigidity
section

/-! Rigidity of the integer relation used to broadcast a shared label. -/
namespace OAI
namespace Combinatorics
namespace Sunflower

open Finset

private theorem sphere_rigidity_int {D Z : Type*} [Fintype D] [Fintype Z]
    (u : D → ℤ) (w : Z → D → ℤ)
    (hn : ∀ z, ∑ i, (w z i)^2 = ∑ i, (u i)^2)
    (hd : ∑ z, ∑ i, u i * w z i = Fintype.card Z * ∑ i, (u i)^2) :
    ∀ z, w z = u := by
  classical
  have hdist (z : Z) :
      ∑ i, (w z i - u i)^2 = 2 * ((∑ i, (u i)^2) - ∑ i, u i * w z i) := by
    calc
      _ = ∑ i, ((w z i)^2 + (u i)^2 - 2 * (u i * w z i)) :=
        sum_congr rfl fun i _ => by ring
      _ = _ := by rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, hn]; ring
  have hz : ∑ z, ∑ i, (w z i - u i)^2 = 0 := by
    simp_rw [hdist]
    rw [← mul_sum, sum_sub_distrib, hd, sum_const, card_univ, nsmul_eq_mul]
    ring
  intro z
  have hz' := (sum_eq_zero_iff_of_nonneg (fun z _ => sum_nonneg
    fun i _ => sq_nonneg (w z i - u i))).mp hz z (mem_univ _)
  funext i
  have hi := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (w z i - u i))).mp
    hz' i (mem_univ _)
  exact sub_eq_zero.mp ((sq_eq_zero_iff).mp hi)

private theorem sphere_rigidity {D Z : Type*} [Fintype D] [Fintype Z]
    (u : D → ℕ) (w : Z → D → ℕ)
    (hn : ∀ z, ∑ i, (w z i)^2 = ∑ i, (u i)^2)
    (hd : ∑ z, ∑ i, u i * w z i = Fintype.card Z * ∑ i, (u i)^2) :
    ∀ z, w z = u := by
  classical
  have he := sphere_rigidity_int (fun i => (u i : ℤ)) (fun z i => (w z i : ℤ))
    (fun z => by exact_mod_cast hn z) (by exact_mod_cast hd)
  intro z
  funext i
  exact_mod_cast congrFun (he z) i

private theorem dot_sum {D Z : Type*} [Fintype D] [Fintype Z]
    (u : D → ℕ) (w : Z → D → ℕ) :
    ∑ i, u i * (∑ z, w z i) = ∑ z, ∑ i, u i * w z i := by
  simp_rw [mul_sum]
  exact sum_comm

private theorem dot_multiple {D : Type*} [Fintype D]
    (u v : D → ℕ) (c : ℕ) :
    ∑ i, u i * (c * v i) = c * ∑ i, u i * v i := by
  rw [mul_sum]
  exact sum_congr rfl fun i _ => Nat.mul_left_comm _ _ _

/-- On a common sphere for targets and a common spherical slice for sources,
the integer broadcast relation picks out the desired diagonal exactly.
The distinguished source has value `v₀` and the other sources are indexed by `J`. -/
theorem broadcast_relation_iff {D Z J : Type*} [Fintype D] [Fintype Z] [Fintype J]
    (u v₀ : D → ℕ) (g : Z → D → ℕ) (v : J → D → ℕ)
    (hg : ∀ z, ∑ i, (g z i)^2 = ∑ i, (u i)^2)
    (hv : ∀ j, ∑ i, (v j i)^2 = ∑ i, (v₀ i)^2)
    (huv : ∀ j, ∑ i, u i * v j i = ∑ i, u i * v₀ i) :
    (∀ i, (∑ z, g z i) + Fintype.card J * v₀ i = Fintype.card Z * u i + ∑ j, v j i) ↔
      (∀ z, g z = u) ∧ ∀ j, v j = v₀ := by
  classical
  constructor
  · intro h
    have hpair := sum_congr (s₁ := (univ : Finset D)) rfl
      (fun i _ => congrArg (u i * ·) (h i))
    simp only [Nat.mul_add, sum_add_distrib, dot_sum, dot_multiple] at hpair
    simp_rw [huv] at hpair
    simp only [sum_const, card_univ, nsmul_eq_mul] at hpair
    have htarget : ∀ z, g z = u := by
      apply sphere_rigidity u g hg
      simpa only [sq, Nat.cast_id, Nat.add_right_cancel_iff] using hpair
    have hsource (i : D) : (∑ j, v j i) = Fintype.card J * v₀ i := by
      simpa only [htarget, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, Nat.add_left_cancel_iff]
        using (h i).symm
    refine ⟨htarget, sphere_rigidity v₀ v hv ?_⟩
    simp_rw [sq]
    rw [← dot_sum, ← dot_multiple]
    simp_rw [hsource]
  · rintro ⟨ht, hs⟩ i
    simp [ht, hs]

private theorem sum_box_le {q : ℕ} {I : Type*} [Fintype I] (f : I → ℕ) (hf : ∀ x, f x ≤ q - 1) :
    ∑ x, f x ≤ Fintype.card I * (q - 1) := by
  simpa [nsmul_eq_mul] using sum_le_sum (s := (univ : Finset I))
    (g := fun _ => q - 1) (fun x _ => hf x)

/-- The same test inside a product of cyclic groups. The modulus exceeds
both sides of the coordinatewise integer equation. -/
theorem broadcast_mod_relation_iff {D Z J : Type*} [Fintype D] [Fintype Z] [Fintype J]
    {q L : ℕ} (hL : (Fintype.card Z + Fintype.card J) * (q - 1) < L)
    (u v₀ : D → ℕ) (g : Z → D → ℕ) (v : J → D → ℕ)
    (bu : ∀ i, u i ≤ q - 1) (bv₀ : ∀ i, v₀ i ≤ q - 1)
    (bg : ∀ z i, g z i ≤ q - 1) (bv : ∀ j i, v j i ≤ q - 1)
    (hg : ∀ z, ∑ i, (g z i)^2 = ∑ i, (u i)^2)
    (hv : ∀ j, ∑ i, (v j i)^2 = ∑ i, (v₀ i)^2)
    (huv : ∀ j, ∑ i, u i * v j i = ∑ i, u i * v₀ i) :
    ((∑ z, fun i => (g z i : ZMod L)) + Fintype.card J • (fun i => (v₀ i : ZMod L)) =
       Fintype.card Z • (fun i => (u i : ZMod L)) + ∑ j, fun i => (v j i : ZMod L)) ↔
      (∀ z, g z = u) ∧ ∀ j, v j = v₀ := by
  classical
  rw [← broadcast_relation_iff u v₀ g v hg hv huv]
  rw [add_mul] at hL
  constructor
  · intro h i
    have h₁ := lt_of_le_of_lt (Nat.add_le_add (sum_box_le (g · i) (bg · i))
      (Nat.mul_le_mul_left _ (bv₀ i))) hL
    have h₂ := lt_of_le_of_lt (Nat.add_le_add (Nat.mul_le_mul_left _ (bu i))
      (sum_box_le (v · i) (bv · i))) hL
    have e : (((∑ z, g z i) + Fintype.card J * v₀ i : ℕ) : ZMod L) =
        ((Fintype.card Z * u i + ∑ j, v j i : ℕ) : ZMod L) := by
      simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul,
        Pi.mul_apply, Pi.natCast_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_sum] using congrFun h i
    simpa only [ZMod.val_natCast_of_lt h₁, ZMod.val_natCast_of_lt h₂] using
      congrArg ZMod.val e
  · intro h
    funext i
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul,
      Pi.mul_apply, Pi.natCast_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_sum] using
      congrArg (Nat.cast (R := ZMod L)) (h i)

end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Broadcast
section

/-! # Controlled broadcasting by character orthogonality -/

namespace OAI
namespace Combinatorics
namespace Sunflower

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators Classical

noncomputable section

variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]

/-- A restriction controlled at its source sites that reproduces the common
source label at the target sites while returning a fixed resource. -/
def Broadcasts (P T : Finset I) (A : Type) (R Q : Raw.{0} I ℂ) : Prop :=
  ∃ M : Control.Map (fun _ : I => A) R.Leg (fun i => Q.Leg i × MaskLeg T A i),
    ∀ (a : A) (c : I → A), (∀ i ∈ P, c i = a) →
      ∀ y, Control.eval M c R.coeff y = Q.coeff (fun i => (y i).1) *
        (if (fun i => (y i).2) = (fun _ _ => a) then 1 else 0)

/-- The distinguished source contributes both the control and the reference
source index. Other source indices enter with negative sign. -/
private def phase {Γ : Type} [AddCommGroup Γ] (P T : Finset I) (s : I)
    (H : A → Γ) (V : A → A → Γ) (i : I) (c : A)
    (y : MaskLeg P A i × MaskLeg T A i) : Γ :=
  if hp : i ∈ P then
    if i = s then (P.erase s).card • V c (y.1 hp) - T.card • H c
    else -V c (y.1 hp)
  else if ht : i ∈ T then H (y.2 ht) else 0

omit [Fintype I] [Fintype A] in
private theorem sum_phase {Γ : Type} [AddCommGroup Γ] (P T : Finset I)
    (hPT : Disjoint P T) (s : I) (hs : s ∈ P)
    (H : A → Γ) (V : A → A → Γ) (a : A) (c : I → A)
    (hc : ∀ i ∈ P, c i = a) (y : ∀ i, MaskLeg P A i × MaskLeg T A i) :
    (∑ i ∈ P ∪ T, phase P T s H V i (c i) (y i)) = 0 ↔
      (∑ z : T, H ((y z).2 z.property)) + (P.erase s).card • V a ((y s).1 hs) =
        T.card • H a + ∑ j : P.erase s, V a ((y j).1 (Finset.mem_of_mem_erase j.property)) := by
  classical
  let f (i : I) := phase P T s H V i (c i) (y i)
  have hex : (∑ i ∈ P.erase s, f i) =
      -(∑ j : P.erase s, V a ((y j).1 (Finset.mem_of_mem_erase j.property))) := by
    rw [← Finset.sum_coe_sort, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have h := Finset.mem_erase.mp j.property
    simp [f, phase, h.1, h.2, hc j h.2]
  have htar : (∑ i ∈ T, f i) = ∑ z : T, H ((y z).2 z.property) := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro z _
    have hz : (z : I) ∉ P := fun hp => Finset.disjoint_left.mp hPT hp z.property
    simp [f, phase, hz, z.property]
  have hsrc : f s = (P.erase s).card • V a ((y s).1 hs) - T.card • H a := by
    simp [f, phase, hs, hc s hs]
  change (∑ i ∈ P ∪ T, f i) = 0 ↔ _
  rw [Finset.sum_union hPT, ← Finset.sum_erase_add P f hs, hex, hsrc, htar]
  constructor
  · intro h
    apply sub_eq_zero.mp
    convert h using 1; abel
  · intro h
    convert sub_eq_zero.mpr h using 1; abel

omit [Fintype I] [Fintype A] in
private theorem zero_sum_agrees {m q N L : ℕ} (d : BroadcastCode m q N) (e : A ≃ Fin N)
    (P T : Finset I) (hPT : Disjoint P T) (s : I) (hs : s ∈ P)
    (hL : (T.card + (P.erase s).card) * (q-1) < L)
    (a : A) (c : I → A) (hc : ∀ i ∈ P, c i = a)
    (y : ∀ i, MaskLeg P A i × MaskLeg T A i) :
    (∑ i ∈ P ∪ T, phase P T s
      (fun x j => ((d.H (e x) j : ℕ) : ZMod L))
      (fun x t j => ((d.V (e x) (e t) j : ℕ) : ZMod L)) i (c i) (y i)) = 0 ↔
      (∀ i (hi : i ∈ P), (y i).1 hi = (y s).1 hs) ∧
      ((fun i => (y i).2) = (fun _ _ => a)) := by
  classical
  rw [sum_phase P T hPT s hs _ _ a c hc]
  let h (x : A) (i : Fin m) : ℕ := d.H (e x) i
  let v (x : A) (i : Fin m) : ℕ := d.V (e a) (e x) i
  let idx (j : P.erase s) := (y j).1 (Finset.mem_of_mem_erase j.property)
  let tar (z : T) := (y z).2 z.property
  let t₀ := (y s).1 hs
  have hinj : Function.Injective h := by
    intro x z he
    exact e.injective (d.H.injective (funext fun i => Fin.ext (congrFun he i)))
  have vinj : Function.Injective v := by
    intro x z he
    exact e.injective ((d.V (e a)).injective (funext fun i => Fin.ext (congrFun he i)))
  have hb (x : Fin q) : x.val ≤ q - 1 := by have := x.isLt; omega
  have rel := broadcast_mod_relation_iff (D := Fin m) (Z := T) (J := P.erase s)
    (q := q) (L := L) (by simpa using hL) (h a) (v t₀)
    (fun z => h (tar z)) (fun j => v (idx j))
    (fun i => hb _) (fun i => hb _) (fun z i => hb _) (fun j i => hb _)
    (fun z => d.H_norm _ _) (fun j => d.V_norm _ _ _) (fun j => d.dot_eq _ _ _)
  simp only [Fintype.card_coe] at rel
  refine rel.trans ?_
  constructor
  · rintro ⟨ht,hp⟩
    constructor
    · intro i hi
      by_cases hsame : i = s
      · subst i; rfl
      · exact vinj (hp ⟨i, Finset.mem_erase.mpr ⟨hsame, hi⟩⟩)
    · funext i hi
      exact hinj (ht ⟨i, hi⟩)
  · rintro ⟨hp, ht⟩
    exact ⟨fun z => congrArg h (congrFun (congrFun ht z) z.property),
      fun j => congrArg v (hp j (Finset.mem_of_mem_erase j.property))⟩

private theorem broadcasts_code {m q N L : ℕ} [NeZero L]
    (d : BroadcastCode m q N) (e : A ≃ Fin N) (P T : Finset I) (hPT : Disjoint P T)
    (s : I) (hs : s ∈ P) (hL : (T.card + (P.erase s).card) * (q-1) < L) :
    Broadcasts P T A (Raw.maskDiagonal ℂ (P ∪ T) (AddChar (Fin m → ZMod L) ℂ))
      (Raw.maskDiagonal ℂ P A) := by
  classical
  let H (x : A) (j : Fin m) : ZMod L := (d.H (e x) j : ℕ)
  let V (x t : A) (j : Fin m) : ZMod L := (d.V (e x) (e t) j : ℕ)
  refine ⟨fourierMatrix (P ∪ T) s (phase P T s H V), ?_⟩
  intro a c hc y
  change ∀ i, MaskLeg P A i × MaskLeg T A i at y
  refine (eval_fourierMatrix (P ∪ T) s (phase P T s H V) c y).trans ?_
  rw [Raw.maskDiagonal_coeff_at (K := ℂ) P hs (fun i => (y i).1)]
  have hz : (∑ i ∈ P ∪ T, phase P T s H V i (c i) (y i)) = 0 ↔ _ :=
    zero_sum_agrees d e P T hPT s hs hL a c hc y
  rw [hz]
  split_ifs <;> simp_all

/-- The alphabet-independent additive cost paid for a chosen broadcast slope. -/
def broadcastOverhead (sites h : ℕ) : ℝ :=
  (BroadcastParameters.dim h : ℝ) * ((BroadcastParameters.dim h : ℝ) + 2 + sites)

/-- On a shared control, broadcast its label to every target and recover a
fixed tensor at the sources. Increasing the fixed parameter h makes the excess
slope arbitrarily small, uniformly in b. -/
theorem exists_broadcast [Nonempty I] [Nonempty A]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (P T : Finset I) (hP : P.Nonempty) (_hT : T.Nonempty) (hPT : Disjoint P T)
    {h : ℕ} (hh : 0 < h) (b : ℕ) (hA : Fintype.card A = 2^b) :
    ∃ R Q : Raw.{0} I ℂ, R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧ Broadcasts P T A R Q ∧
      rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤
        (maskDiagonalPrice φ 1 (P ∪ T) - maskDiagonalPrice φ 1 P + 6/(h:ℝ)) * b +
          broadcastOverhead (Fintype.card I) h := by
  classical
  obtain ⟨s, hs⟩ := hP
  let sites := Fintype.card I
  let L := BroadcastParameters.modulus h b sites
  let m := BroadcastParameters.dim h
  let q := BroadcastParameters.side h b
  let : NeZero L := ⟨(BroadcastParameters.modulus_pos _ _ _).ne'⟩
  obtain ⟨code⟩ := BroadcastCode.nonempty_of_card (BroadcastParameters.code_capacity hh b)
  let e : A ≃ Fin (2^b) := Fintype.equivOfCardEq (by simpa using hA)
  have hcard : T.card + (P.erase s).card ≤ sites := by
    have hle := (P ∪ T).card_le_univ
    rw [Finset.card_union_of_disjoint hPT] at hle
    have he := Finset.card_erase_le (s := P) (a := s)
    omega
  have hn : (T.card + (P.erase s).card) * (q-1) < L :=
    (Nat.mul_le_mul_right _ hcard).trans_lt (BroadcastParameters.no_wrap h b sites)
  let D := AddChar (Fin m → ZMod L) ℂ
  have hk : (P ∪ T).Nonempty := ⟨s, Finset.mem_union_left _ hs⟩
  refine ⟨Raw.maskDiagonal ℂ (P ∪ T) D, Raw.maskDiagonal ℂ P A,
    Raw.maskDiagonal_ne_zero _ hk _, Raw.maskDiagonal_ne_zero _ ⟨s,hs⟩ _,
    broadcasts_code code e P T hPT s hs hn, ?_⟩
  have dcard : Fintype.card D = 2 ^ BroadcastParameters.bits h b sites := by
    simp [D, AddChar.card_eq, ZMod.card, L, m, BroadcastParameters.modulus_pow_dim]
  rw [rawLogPrice_maskDiagonal_card φ 1 _ hk D,
    rawLogPrice_maskDiagonal_card φ 1 _ ⟨s, hs⟩ A, dcard, hA]
  push_cast
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : 1 < (2:ℝ)), mul_one]
  have wpos := maskDiagonalPrice_nonneg φ (by norm_num : 0 ≤ (1:ℝ)) (P ∪ T)
  have wle := maskDiagonalPrice_le_one φ (P ∪ T)
  have hbits := BroadcastParameters.bits_le hh b sites
  change _ ≤ _ + broadcastOverhead sites h
  have costnn : 0 ≤ broadcastOverhead sites h := by unfold broadcastOverhead; positivity
  have hover : 0 ≤ 6 / (h : ℝ) * (b : ℝ) + broadcastOverhead sites h := by positivity
  have hu := mul_le_mul_of_nonneg_left hbits wpos
  have hv := mul_le_mul_of_nonneg_right wle hover
  unfold broadcastOverhead at *
  linarith only [hu, hv]

end
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Correction
section

/-! The error correction in one equality-test step. A row of the output contains
a proposed direction at each site. At a target this row and the external symbol
determine the row to read from the first broadcast, and its direction selects
the local map of the return broadcast. -/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

noncomputable section

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {I : Type*} [Fintype I] {A D : Type}

/-- A nonzero direction survives exactly when all its local labels agree with
the announced difference. -/
private theorem sum_label_eq_indicator [Fintype D]
    (K : Finset I) (hK : K.Nonempty) (code : D → A) (hc : Function.Injective code)
    (q : ∀ i, MaskLeg K D i) (z : A) :
    (∑ d : D, if code d = z then (if q = (fun _ _ => d) then (1 : ℂ) else 0) else 0) =
      if ∀ i (h : i ∈ K), code (q i h) = z then 1 else 0 := by
  classical
  obtain ⟨j,hj⟩ := hK
  by_cases ha : ∀ i (h : i ∈ K), code (q i h) = z
  · let d := q j hj
    have hd : code d = z := ha j hj
    have hq : q = fun _ _ => d := by
      funext i hi
      exact hc ((ha i hi).trans hd.symm)
    rw [if_pos ha]
    rw [Finset.sum_eq_single d]
    · simp [hd, hq]
    · intro e _ he
      exact if_neg (fun h => he (hc (h.trans hd.symm)))
    · simp
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro d _
    by_cases hd : code d = z
    · have hn : q ≠ (fun _ _ => d) := by
        intro h
        apply ha
        intro i hi
        simpa [h] using hd
      simp [hd, hn]
    · simp [hd]

/-- Two common-label broadcasts implement the nonzero correction term.
The label decoder may omit a symbol, as it does for the omitted zero direction
in a binary matching. -/
theorem correction_maps_general [Fintype D]
    (P T : Finset I) (hT : T.Nonempty)
    (code : D → A) (hc : Function.Injective code)
    (decode : D → A → A) (delta : A → A → A)
    (hdecode : ∀ p x y, decode p y = x ↔ code p = delta x y)
    (R₁ Q₁ R₂ Q₂ : Raw.{0} I ℂ)
    (M : Control.Map (fun _ : I => A) R₁.Leg (fun i => Q₁.Leg i × MaskLeg T A i))
    (N : Control.Map (fun _ : I => A) R₂.Leg (fun i => Q₂.Leg i × MaskLeg P A i))
    (hM : ∀ x c, (∀ i ∈ P, c i = x) → ∀ o,
      Control.eval M c R₁.coeff o =
        Q₁.coeff (fun i => (o i).1) * (if (fun i => (o i).2) = (fun _ _ => x) then 1 else 0))
    (hN : ∀ x c, (∀ i ∈ T, c i = x) → ∀ o,
      Control.eval N c R₂.coeff o =
        Q₂.coeff (fun i => (o i).1) * (if (fun i => (o i).2) = (fun _ _ => x) then 1 else 0)) :
    ∃ W : Control.Map (fun _ : I => A) (R₁.mul R₂).Leg
      (fun i => (Q₁.mul Q₂).Leg i × MaskLeg (P ∪ T) D i),
      ∀ x y c, (∀ i ∈ P, c i = x) → (∀ i ∈ T, c i = y) → ∀ o,
        Control.eval W c (R₁.mul R₂).coeff o =
          (Q₁.mul Q₂).coeff (fun i => (o i).1) *
          ∑ p : D, if code p = delta x y then
            (if (fun i => (o i).2) = (fun _ _ => p) then 1 else 0) else 0 := by
  classical
  let left (i : I) (c : A) (q : MaskLeg (P ∪ T) D i) : MaskLeg T A i :=
    fun hi => decode (q (Finset.mem_union_right P hi)) c
  let right (i : I) (q : MaskLeg (P ∪ T) D i) : MaskLeg P A i :=
    fun hi => code (q (Finset.mem_union_left T hi))
  let control (i : I) (c : A) (q : MaskLeg (P ∪ T) D i) :=
    if hi : i ∈ T then code (q (Finset.mem_union_right P hi)) else c
  refine ⟨fun i c o a =>
    M i c (o.1.1, left i c o.2) a.1 *
      N i (control i c o.2) (o.1.2, right i o.2) a.2, ?_⟩
  intro x y c hP hT' o
  let q (i : I) := (o i).2
  let a₁ (i : I) := ((o i).1.1, left i (c i) (q i))
  let a₂ (i : I) := ((o i).1.2, right i (q i))
  let c₂ (i : I) := control i (c i) (q i)
  have hfac :
      Control.eval (fun i c o a =>
        M i c (o.1.1, left i c o.2) a.1 *
        N i (control i c o.2) (o.1.2, right i o.2) a.2) c (R₁.mul R₂).coeff o =
        Control.eval M c R₁.coeff a₁ * Control.eval N c₂ R₂.coeff a₂ := by
    exact contract_mul (fun i => M i (c i)) (fun i => N i (c₂ i))
      R₁.coeff R₂.coeff (fun i => (a₁ i, a₂ i))
  rw [hfac, hM x c hP]
  rw [sum_label_eq_indicator (P ∪ T) (hT.mono (Finset.subset_union_right)) code hc q]
  let z := delta x y
  have ht : ((fun i => (a₁ i).2) = fun _ _ => x) ↔
      ∀ i (hi : i ∈ T), code (q i (Finset.mem_union_right P hi)) = z := by
    constructor
    · intro hh i hi
      apply (hdecode _ x y).1
      rw [← hT' i hi]
      exact congrFun (congrFun hh i) hi
    · intro hh
      funext i hi
      change decode _ (c i) = x
      rw [hT' i hi]
      exact (hdecode _ x y).2 (hh i hi)
  have hp : ((fun i => (a₂ i).2) = fun _ _ => z) ↔
      ∀ i (hi : i ∈ P), code (q i (Finset.mem_union_left T hi)) = z := by
    constructor
    · exact fun hh i hi => congrFun (congrFun hh i) hi
    · exact fun hh => funext fun i => funext (hh i)
  have hu : (∀ i (hi : i ∈ P ∪ T), code (q i hi) = z) ↔
      ((∀ i (hi : i ∈ P), code (q i (Finset.mem_union_left T hi)) = z) ∧
        (∀ i (hi : i ∈ T), code (q i (Finset.mem_union_right P hi)) = z)) := by
    constructor
    · exact fun h => ⟨fun i hi => h i _, fun i hi => h i _⟩
    · rintro ⟨p,t⟩ i hi
      rcases Finset.mem_union.1 hi with hip | hit
      · exact p i hip
      · exact t i hit
  rw [if_congr ht rfl rfl]
  by_cases h : ∀ i (hi : i ∈ T), code (q i (Finset.mem_union_right P hi)) = z
  · have hc₂ : ∀ i ∈ T, c₂ i = z := by
      intro i hi
      simpa [c₂, control, hi] using h i hi
    rw [if_pos h, hN z c₂ hc₂, if_congr hp rfl rfl]
    change _ = _ * (if ∀ i (hi : i ∈ P ∪ T), code (q i hi) = z then 1 else 0)
    rw [if_congr hu rfl rfl]
    rw [if_congr (and_iff_left h) rfl rfl]
    simp only [mul_one, mul_assoc, Raw.mul, a₁, a₂]
  · have hn : ¬ ∀ i (hi : i ∈ P ∪ T), code (q i hi) = z := fun H => h (hu.1 H).2
    rw [if_neg h, if_neg hn]
    simp only [mul_zero, zero_mul]

private theorem binary_decode {b : ℕ} (p : Binary.Direction b) (x y : Binary.Word b) :
    p.val + y = x ↔ p.val = x + y := by
  have bit : ∀ a v w : ZMod 2, a + w = v ↔ a = v + w := by decide
  exact ⟨fun h => funext fun i => (bit _ _ _).mp (congrFun h i),
    fun h => funext fun i => (bit _ _ _).mpr (congrFun h i)⟩

/-- Pairing the forward and return broadcasts produces the binary correction. -/
theorem correction_maps {J : Type} [Fintype J] [DecidableEq J] {b : ℕ}
    (P T : Finset J) (hT : T.Nonempty)
    (R₁ Q₁ R₂ Q₂ : Raw.{0} J ℂ)
    (h₁ : Broadcasts P T (Binary.Word (b+1)) R₁ Q₁)
    (h₂ : Broadcasts T P (Binary.Word (b+1)) R₂ Q₂) :
    CorrectionMaps P T b (R₁.mul R₂) (Q₁.mul Q₂) := by
  classical
  obtain ⟨M,hM⟩ := h₁
  obtain ⟨N,hN⟩ := h₂
  obtain ⟨W,hW⟩ := correction_maps_general (A := Binary.Word (b+1)) (D := Binary.Direction (b+1))
    P T hT Subtype.val Subtype.val_injective
    (fun p y => p.val + y) (· + ·) (binary_decode (b := b+1)) R₁ Q₁ R₂ Q₂ M N
    (fun x c hc o => by
      rw [hM x c hc o]
      split_ifs <;> rfl)
    (fun x c hc o => by
      rw [hN x c hc o]
      split_ifs <;> rfl)
  refine ⟨W, ?_⟩
  intro x y c hp ht o
  refine (hW x y c hp ht o).trans ?_
  apply congrArg (_ * ·)
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> try rfl
  all_goals
    rename_i h₁ h₂
    first | exact False.elim (h₂ h₁) | exact False.elim (h₁ h₂)

private theorem nonzero_product {J : Type} [Fintype J] [Nonempty J] (X Y : Raw.{0} J ℂ)
    (hX : X.coeff ≠ 0) (hY : Y.coeff ≠ 0) : (X.mul Y).coeff ≠ 0 := by
  apply (ofRaw_eq_zero_iff _).not.mp
  rw [ofRaw_mul]
  exact mul_ne_zero ((ofRaw_eq_zero_iff _).not.mpr hX) ((ofRaw_eq_zero_iff _).not.mpr hY)

/-- The positive gap reduces the cost slope of the two broadcasts below the
price of the shared correction index once the fixed parameter is large enough. -/
theorem exists_correction {J : Type} [Fintype J] [Nonempty J] [DecidableEq J]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J ℂ → _ → Prop))
    (P T : Finset J) (hP : P.Nonempty) (hT : T.Nonempty) (hPT : Disjoint P T)
    {h : ℕ} (hh : 0 < h) (b : ℕ) :
    ∃ U V : Raw.{0} J ℂ, U.coeff ≠ 0 ∧ V.coeff ≠ 0 ∧ CorrectionMaps P T b U V ∧
      rawLogPrice φ 1 U - rawLogPrice φ 1 V ≤
        (maskDiagonalPrice φ 1 (P ∪ T) -
          (maskDiagonalPrice φ 1 P + maskDiagonalPrice φ 1 T - maskDiagonalPrice φ 1 (P ∪ T)) +
          12 / (h : ℝ)) * (b+1 : ℕ) + 2 * broadcastOverhead (Fintype.card J) h := by
  classical
  obtain ⟨R₁,Q₁,hR₁,hQ₁,hB₁,e₁⟩ :=
    exists_broadcast (A := Binary.Word (b+1)) φ P T hP hT hPT hh _ (Binary.card_word _)
  obtain ⟨R₂,Q₂,hR₂,hQ₂,hB₂,e₂⟩ :=
    exists_broadcast (A := Binary.Word (b+1)) φ T P hT hP hPT.symm hh _ (Binary.card_word _)
  refine ⟨_, _, nonzero_product _ _ hR₁ hR₂, nonzero_product _ _ hQ₁ hQ₂,
    correction_maps P T hT R₁ Q₁ R₂ Q₂ hB₁ hB₂, ?_⟩
  rw [rawLogPrice_mul φ 1 _ _ hR₁ hR₂, rawLogPrice_mul φ 1 _ _ hQ₁ hQ₂]
  rw [Finset.union_comm T P] at e₂
  linear_combination e₁ + e₂

end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.PositiveFilter
section

/-! # Alphabet-uniform filtering at a positive diagonal gap -/

open scoped Classical
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- A positive partial-diagonal gap admits equality tests at a common bounded
price for all finite alphabets. Each local matrix uses only its own control. -/
theorem exists_equality_filter {I : Type} [Fintype I] [Nonempty I] [dec : DecidableEq I]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (P T : Finset I) (hP : P.Nonempty) (hT : T.Nonempty) (hPT : Disjoint P T)
    (hg : 0 < maskDiagonalPrice φ 1 P + maskDiagonalPrice φ 1 T - maskDiagonalPrice φ 1 (P ∪ T)) :
    ∃ C : ℝ, ∀ n : ℕ, ∃ R Q : Raw.{0} I ℂ, R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧
      rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤ C ∧ EqualityMaps P T (Fin n) R Q := by
  have hdec := Subsingleton.elim dec (Classical.decEq I)
  subst dec
  let g := maskDiagonalPrice φ 1 P + maskDiagonalPrice φ 1 T - maskDiagonalPrice φ 1 (P ∪ T)
  have hpos : 0 < g := hg
  obtain ⟨h, hh, he⟩ := exists_broadcastParameter (θ := 1) hpos
  rw [mul_one] at he
  apply exists_equality_filter_of_corrections φ P T
    (hP.mono Finset.subset_union_left) (half_pos hpos)
    (B := 2 * broadcastOverhead (Fintype.card I) h)
  intro b
  obtain ⟨U,V,hU,hV,hcor,hcost⟩ := exists_correction φ P T hP hT hPT (by omega : 0 < h) b
  refine ⟨U,V,hU,hV,hcost.trans ?_,hcor⟩
  push_cast
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  dsimp [g] at he ⊢
  linarith only [he]

end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.RuleDevices
section

/-! # Uniform controlled tests for the planar anchor rules

The local matrices read the control at their own site. Under a violated implication
the selected antecedent sites have one common symbol and the target sites another.
The same device preserves its return tensor when all controls agree.
-/

open scoped Classical
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace RuleDevices

open Comparison Placement

noncomputable section

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

/-- A width-preserving copy to a single target gives an equality test. The extra
unused symbol lets every finite alphabet, including the empty one, embed in the
positive-sized label set of the copying construction. -/
private theorem copyFilter
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} S ℂ → _ → Prop))
    (P : Finset S) (s : S) (hP : P.Nonempty)
    (hw : maskDiagonalPrice φ 1 (insert s P) = maskDiagonalPrice φ 1 P) :
    ∃ B : ℝ, ∀ m : ℕ, ∃ R Q : Raw.{0} S ℂ,
      R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧ rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤ B ∧
      EqualityMaps P {s} (Fin m) R Q := by
  obtain ⟨t, ht⟩ := hP
  refine ⟨maskDiagonalPrice φ 1 P, fun m =>
    ⟨Copy.input P s m, Copy.returned P m,
      Raw.maskDiagonal_ne_zero _ (Finset.insert_nonempty ..) _,
      Raw.maskDiagonal_ne_zero _ ⟨t, ht⟩ _,
      (Copy.cost_eq φ ⟨t, ht⟩ 1 hw m).le, ?_⟩⟩
  refine ⟨fun j u => Copy.matrix P s t m j u.castSucc, ?_⟩
  intro x y c hL hT o
  have hc : c s = y := hT s (Finset.mem_singleton_self s)
  have h := Copy.matrix_apply (z := s) ht (fun j => (c j).castSucc) x.castSucc
    (fun j hj => congrArg Fin.castSucc (hL j hj)) o
  refine h.trans ?_
  by_cases he : x = y <;> simp [hc, he]

variable {n : ℕ} {q : Rule (Fin (n+2))}
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Site n) ℂ → _ → Prop))

/-- Uniform price and behavior of a single implication test. -/
def UniformRule (q : Rule (Fin (n+2))) : Prop :=
  ∃ B : ℝ, ∀ m : ℕ, ∃ D : Comparison.Device (Site n) (Fin m), D.cost φ ≤ B ∧
    (∀ u, D.out (fun _ => u) = D.Q.coeff) ∧
    ∀ f : Fin (n+2) → Fin m, ¬ q.Holds f → D.out (f ∘ group) = 0

theorem exists_rule_device (hq : q ∈ anchorRules 0 1) (d : RuleSites q)
    (hw : d.Works (maskDiagonalPrice φ 1)) : UniformRule φ q := by
  classical
  have hP := d.hL.mono (Finset.subset_union_left (s₂ := d.R))
  have hd := (mem_anchorRules.mp hq).distinct (Fin.zero_ne_one : (0 : Fin (n+2)) ≠ 1)
  have hex : ∃ B : ℝ, ∀ m : ℕ, ∃ R Q : Raw.{0} (Site n) ℂ,
      R.coeff ≠ 0 ∧ Q.coeff ≠ 0 ∧ rawLogPrice φ 1 R - rawLogPrice φ 1 Q ≤ B ∧
      EqualityMaps (d.L ∪ d.R) d.T (Fin m) R Q := by
    rcases hw with hgap | ⟨s, hT, he⟩
    · exact exists_equality_filter φ _ _ hP d.hT (d.disjoint hd.2.1 hd.2.2) hgap
    · rw [hT]
      exact copyFilter φ _ _ hP he
  obtain ⟨B, hB⟩ := hex
  refine ⟨B, fun m => ?_⟩
  obtain ⟨R, Q, hR, hQ, hcost, M, hM⟩ := hB m
  let D : Comparison.Device (Site n) (Fin m) := ⟨R, Q, hR, hQ, M⟩
  refine ⟨D, hcost, ?_, ?_⟩
  · intro u
    funext o
    exact (hM u u (fun _ => u) (fun _ _ => rfl) (fun _ _ => rfl) o).trans (by simp [D])
  · intro f hv
    obtain ⟨he, hne⟩ := (q.not_holds_iff f).mp hv
    funext o
    exact (hM _ _ (f ∘ group) (d.antecedent_const f he) (d.target_const f) o).trans
      (by simp [hne])

/-- One spectral point supplies positive group deficit and all rule tests with
bounds chosen before the alphabet size. -/
theorem devices_of_prices (n : ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Site n) ℂ → _ → Prop))
    (hD : 0 < width (Finset.univ : Finset (Site n)))
    (price : ∀ (s : Finset (Site n)), s.Nonempty →
      maskDiagonalPrice φ 1 s = width s / width (Finset.univ : Finset (Site n))) :
    0 < 1 - ∑ g, maskDiagonalPrice φ 1 (Placement.fiber g) ∧
        ∀ q ∈ anchorRules (0 : Fin (n+2)) 1, UniformRule φ q := by
  obtain ⟨hdef, hgeo⟩ := priced_placement n φ hD price
  refine ⟨hdef, fun q hq => ?_⟩
  obtain ⟨d, hw⟩ := hgeo q hq
  exact exists_rule_device φ hq d hw

end

end RuleDevices
end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Rounding
section

/-! # Exponential bounds for coloring and word comparisons -/

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- A uniformly random coloring with `k` colors is rainbow on a fixed `k`-set
with probability at least `3⁻ᵏ`. -/
theorem pow_self_le_three_pow_mul_factorial (k : ℕ) :
    k ^ k ≤ 3 ^ k * k.factorial := by
  have hk : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hExp : Real.exp k ≤ (3 : ℝ) ^ k := by
    calc
      Real.exp k = (Real.exp 1) ^ k := by simp
      _ ≤ 3 ^ k := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have h := (div_le_iff₀ hk).mp ((Real.pow_div_factorial_le_exp k (Nat.cast_nonneg k) k).trans hExp)
  exact_mod_cast h

/-- A positive coefficient of `log₂ N` in a uniform word comparison gives a
single natural base for every word length and alphabet. -/
theorem exists_natBase_of_logb_bound {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ k N : ℕ,
      (0 < N → ρ * Real.logb 2 N ≤ (k : ℝ) * c) → N ≤ D ^ k := by
  obtain ⟨D, hD⟩ := exists_nat_gt ((2 : ℝ) ^ (c / ρ))
  have hpos : 0 < (D : ℝ) := (Real.rpow_pos_of_pos (by norm_num) _).trans hD
  have hD' : 0 < D := by exact_mod_cast hpos
  refine ⟨D, hD', ?_⟩
  intro k N h
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Nat.zero_le _
  have hlog : Real.logb 2 N ≤ (c / ρ) * k := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
    simpa only [mul_comm] using h hN
  have hcard := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hN)).mp hlog
  rw [Real.rpow_mul_natCast (by norm_num)] at hcard
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hD.le k
  exact_mod_cast hcard.trans hpow

end Sunflower
end Combinatorics
end OAI
end

-- Source module: OAI.Combinatorics.Sunflower.Bound
section

/-! # The fixed-base Erdős–Rado sunflower theorem -/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

/-- For each number of petals, the planar configuration gives one base for all
word lengths and all finite alphabets. -/
theorem bound_of_prices (n : ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Placement.Site n) ℂ → _ → Prop))
    (hd : 0 < Placement.width (Finset.univ : Finset (Placement.Site n)))
    (hp : ∀ (s : Finset (Placement.Site n)), s.Nonempty →
      maskDiagonalPrice φ 1 s = Placement.width s / Placement.width (Finset.univ : Finset (Placement.Site n))) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (k m : ℕ) (W : Finset (Fin k → Fin m)),
      WordFree (n+2) W → W.card ≤ D ^ k := by
  classical
  obtain ⟨hgap, htests⟩ := RuleDevices.devices_of_prices n φ hd hp
  let rules := anchorRules (0 : Fin (n + 2)) 1
  let cost (q : Rule (Fin (n + 2))) : ℝ :=
    if h : q ∈ rules then (htests q h).choose else 0
  let ρ := 1 - ∑ j, maskDiagonalPrice φ 1 (Placement.fiber j)
  obtain ⟨D, hD, hbound⟩ := exists_natBase_of_logb_bound (ρ := ρ) hgap (∑ q ∈ rules, cost q)
  refine ⟨D, hD, fun k m W hfree => hbound k W.card (fun hpos => ?_)⟩
  have hfiber (j : Fin (n + 2)) :
      Comparison.fiber Placement.group j = Placement.fiber j := by
    ext s
    simp only [Comparison.mem_fiber, Placement.mem_fiber]
  have hc := Comparison.wordComparison φ Placement.group Placement.group_surjective 0 1
    Fin.zero_ne_one W (Finset.card_pos.mp hpos) hfree cost (by
      intro q hq
      simpa only [cost, dif_pos (show q ∈ rules from hq)] using (htests q hq).choose_spec m)
  simpa only [ρ, rules, hfiber] using hc

end Sunflower
end Combinatorics
end OAI
end


/- Coordinate adapter adapted from TheWaler (Theorem / Grok Bot), open-math-agents PR 4572, commit 5589df772152438e2b768fcd02053dc78d1bda47. The word estimate below uses the separate OpenAI bound_of_prices consumer. -/
section
namespace OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open OAI.Combinatorics.Sunflower

abbrev T (I : Type) := Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ

section
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Reading one coordinate at each site against Kronecker deltas. -/
theorem sum_read {A : I → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (F : (∀ i, A i) → ℂ) (g : ∀ i, A i) :
    ∑ z, F z * ∏ i, (if g i = z i then (1 : ℂ) else 0) = F g := by
  classical
  rw [Finset.sum_eq_single g]
  · simp
  · intro b _ hb
    obtain ⟨i, hi⟩ : ∃ i, g i ≠ b i := by
      by_contra h
      push Not at h
      exact hb (funext fun i => (h i).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), mul_zero]
  · simp

variable (Φ : T I → ℝ)
variable (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X)
include hmono

/-- Reading coordinates through maps: the smaller tensor is a restriction. -/
theorem read_le {X S : T I} (g : ∀ i, Fin (X.1 i) → Fin (S.1 i))
    (h : ∀ x, X.2 x = S.2 (fun i => g i (x i))) : Φ X ≤ Φ S := by
  apply hmono S X
  refine ⟨fun i p q => if g i p = q then 1 else 0, fun y => ?_⟩
  rw [h y, ← sum_read S.2 (fun i => g i (y i))]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

/-- The coordinate presentation of a raw tensor. -/
noncomputable def toSig (X : Raw.{0} I ℂ) : T I :=
  ⟨fun i => Fintype.card (X.Leg i), fun z => X.coeff (fun i => (Fintype.equivFin (X.Leg i)).symm (z i))⟩

omit hmono [Fintype I] [DecidableEq I] in
@[simp] theorem toSig_snd (X : Raw.{0} I ℂ) (z) :
    (toSig X).2 z = X.coeff (fun i => (Fintype.equivFin (X.Leg i)).symm (z i)) := rfl

theorem raw_read_le {X : Raw.{0} I ℂ} {S : T I} (g : ∀ i, X.Leg i → Fin (S.1 i))
    (h : ∀ x, X.coeff x = S.2 (fun i => g i (x i))) : Φ (toSig X) ≤ Φ S :=
  read_le Φ hmono (X := toSig X) (fun i p => g i ((Fintype.equivFin (X.Leg i)).symm p))
    (fun x => h _)

theorem read_raw_le {X : Raw.{0} I ℂ} {S : T I} (g : ∀ i, Fin (S.1 i) → X.Leg i)
    (h : ∀ z, S.2 z = X.coeff (fun i => g i (z i))) : Φ S ≤ Φ (toSig X) :=
  read_le Φ hmono (X := S) (S := toSig X) (fun i p => Fintype.equivFin (X.Leg i) (g i p))
    (fun z => by rw [h z]; show _ = X.coeff _; simp)

theorem raw_eq {X : Raw.{0} I ℂ} {S : T I} (e : ∀ i, X.Leg i ≃ Fin (S.1 i))
    (h : ∀ x, X.coeff x = S.2 (fun i => e i (x i))) : Φ (toSig X) = Φ S :=
  le_antisymm (raw_read_le Φ hmono (fun i => e i) h)
    (read_raw_le Φ hmono (fun i => (e i).symm) fun z => by simp [h])

theorem raw_mono {X Y : Raw.{0} I ℂ} (h : X.Restricts Y) : Φ (toSig X) ≤ Φ (toSig Y) := by
  obtain ⟨M, hM⟩ := h
  apply hmono (toSig Y) (toSig X)
  refine ⟨fun i p q => M i ((Fintype.equivFin _).symm p) ((Fintype.equivFin _).symm q),
    fun y => ?_⟩
  simp only [toSig_snd]
  rw [hM]
  have key := Fintype.sum_equiv (Equiv.piCongrRight fun i => (Fintype.equivFin (Y.Leg i))).symm
    (fun z => (∏ i, M i ((Fintype.equivFin (X.Leg i)).symm (y i))
      ((Fintype.equivFin (Y.Leg i)).symm (z i))) *
        Y.coeff (fun i => (Fintype.equivFin (Y.Leg i)).symm (z i)))
    (fun a => Y.coeff a * ∏ i, M i ((Fintype.equivFin (X.Leg i)).symm (y i)) (a i))
    (fun z => by rw [mul_comm]; rfl)
  refine Eq.trans ?_ (Eq.trans key.symm ?_)
  · convert rfl
  · rfl

end


section ops
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The coordinate direct sum, as in the target statement. -/
def sigAdd (X Y : T I) : T I :=
  ⟨fun i => X.1 i + Y.1 i, fun z =>
          if h : ∀ i, (z i : ℕ) < X.1 i then X.2 (fun i => ⟨z i, h i⟩)
          else if h' : ∀ i, X.1 i ≤ z i then
            Y.2 (fun i => ⟨z i - X.1 i, by have h2 : (z i : ℕ) < X.1 i + Y.1 i := (z i).2; have := h' i; omega⟩)
          else 0⟩

/-- The coordinate tensor product, as in the target statement. -/
def sigMul (X Y : T I) : T I :=
  ⟨fun i => X.1 i * Y.1 i, fun z => X.2 (fun i => (finProdFinEquiv.symm (z i)).1) *
          Y.2 (fun i => (finProdFinEquiv.symm (z i)).2)⟩

/-- The one-bit partial diagonal on `S`, as in the target statement. -/
def maskSig (S : Finset I) : T I :=
  ⟨fun i => if i ∈ S then 2 else 1,
          fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩

noncomputable def addEquiv (X Y : Raw.{0} I ℂ) (i : I) :
    X.Leg i ⊕ Y.Leg i ≃ Fin (Fintype.card (X.Leg i) + Fintype.card (Y.Leg i)) :=
  (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finSumFinEquiv

noncomputable def mulEquiv (X Y : Raw.{0} I ℂ) (i : I) :
    X.Leg i × Y.Leg i ≃ Fin (Fintype.card (X.Leg i) * Fintype.card (Y.Leg i)) :=
  (Equiv.prodCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finProdFinEquiv

theorem mulEquiv_symm (X Y : Raw.{0} I ℂ) (i : I) (p : X.Leg i × Y.Leg i) :
    finProdFinEquiv.symm (mulEquiv X Y i p) =
      (Fintype.equivFin _ p.1, Fintype.equivFin _ p.2) := by
  rw [mulEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]; rfl

theorem addEquiv_inl (X Y : Raw.{0} I ℂ) (i : I) (a : X.Leg i) :
    ((addEquiv X Y i (Sum.inl a) : Fin _) : ℕ) = (Fintype.equivFin _ a : ℕ) := by
  rw [addEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Fin.coe_castAdd]

theorem addEquiv_inr (X Y : Raw.{0} I ℂ) (i : I) (b : Y.Leg i) :
    ((addEquiv X Y i (Sum.inr b) : Fin _) : ℕ) = Fintype.card (X.Leg i) + (Fintype.equivFin _ b : ℕ) := by
  rw [addEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right, Fin.coe_natAdd]

theorem mul_coeff (X Y : Raw.{0} I ℂ) (x : ∀ i, X.Leg i × Y.Leg i) :
    (X.mul Y).coeff x = (sigMul (toSig X) (toSig Y)).2 (fun i => mulEquiv X Y i (x i)) := by
  dsimp only [sigMul, toSig, Raw.mul]
  simp only [mulEquiv_symm, Equiv.symm_apply_apply]

theorem add_coeff [Nonempty I] (X Y : Raw.{0} I ℂ) (x : ∀ i, X.Leg i ⊕ Y.Leg i) :
    (X.add Y).coeff x = (sigAdd (toSig X) (toSig Y)).2 (fun i => addEquiv X Y i (x i)) := by
  classical
  show sumCoeff X.coeff Y.coeff x = _
  dsimp only [sigAdd, toSig]
  by_cases hL : ∀ i, ∃ a, x i = Sum.inl a
  · choose a ha using hL
    obtain rfl : x = fun i => Sum.inl (a i) := funext ha
    rw [sumCoeff_inl]
    have hlt : ∀ i, ((addEquiv X Y i (Sum.inl (a i)) : Fin _) : ℕ) < Fintype.card (X.Leg i) := by
      intro i; rw [addEquiv_inl]; exact (Fintype.equivFin _ (a i)).isLt
    rw [dif_pos hlt]
    congr 1
    funext i
    apply (Fintype.equivFin _).injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (addEquiv_inl X Y i (a i)).symm
  · by_cases hR : ∀ i, ∃ b, x i = Sum.inr b
    · choose b hb using hR
      obtain rfl : x = fun i => Sum.inr (b i) := funext hb
      rw [sumCoeff_inr]
      obtain ⟨i₀⟩ := ‹Nonempty I›
      have hnlt : ¬ ∀ i, ((addEquiv X Y i (Sum.inr (b i)) : Fin _) : ℕ) < Fintype.card (X.Leg i) := by
        intro h; have := h i₀; rw [addEquiv_inr] at this
        omega
      have hge : ∀ i, Fintype.card (X.Leg i) ≤ ((addEquiv X Y i (Sum.inr (b i)) : Fin _) : ℕ) := by
        intro i; rw [addEquiv_inr]; exact Nat.le_add_right _ _
      rw [dif_neg hnlt, dif_pos hge]
      congr 1
      funext i
      apply (Fintype.equivFin _).injective
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      simp only [addEquiv_inr]
      omega
    · push Not at hL hR
      obtain ⟨i, hi⟩ := hL
      obtain ⟨j, hj⟩ := hR
      rw [sumCoeff_mixed]
      · obtain ⟨b, hb⟩ : ∃ b, x i = Sum.inr b := by
          rcases h : x i with a | b
          · exact absurd h (hi a)
          · exact ⟨b, rfl⟩
        obtain ⟨a, ha⟩ : ∃ a, x j = Sum.inl a := by
          rcases h : x j with a | b
          · exact ⟨a, rfl⟩
          · exact absurd h (hj b)
        have h1 : ¬ ∀ k, ((addEquiv X Y k (x k) : Fin _) : ℕ) < Fintype.card (X.Leg k) := by
          intro h; have := h i; rw [hb, addEquiv_inr] at this
          omega
        have h2 : ¬ ∀ k, Fintype.card (X.Leg k) ≤ ((addEquiv X Y k (x k) : Fin _) : ℕ) := by
          intro h; have := h j; rw [ha, addEquiv_inl] at this
          have := (Fintype.equivFin _ a).isLt
          omega
        rw [dif_neg h1, dif_neg h2]
      · intro a h; exact hi (a i) (congrFun h i).symm
      · intro b h; exact hj (b j) (congrFun h j).symm

end ops


section mask
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Reading a mask leg as a coordinate. -/
def maskTo (S : Finset I) (i : I) (f : MaskLeg S (Fin 2) i) : Fin (if i ∈ S then 2 else 1) :=
  ⟨if h : i ∈ S then (f h : ℕ) else 0, by
    split_ifs with h
    · exact (f h).isLt
    · exact Nat.zero_lt_one⟩

/-- Reading a coordinate as a mask leg. -/
def maskFrom (S : Finset I) (i : I) (z : Fin (if i ∈ S then 2 else 1)) : MaskLeg S (Fin 2) i :=
  fun h => ⟨z, by have := z.isLt; simp only [h, if_true] at this; exact this⟩

theorem maskTo_val (S : Finset I) (i : I) (hi : i ∈ S) (f : MaskLeg S (Fin 2) i) :
    ((maskTo S i f : Fin _) : ℕ) = (f hi : ℕ) := by
  simp [maskTo, hi]

theorem mask_le (Φ : T I → ℝ) (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X)
    (S : Finset I) (hS : S.Nonempty) :
    Φ (toSig (Raw.maskDiagonal ℂ S (Fin 2))) = Φ (maskSig S) := by
  obtain ⟨i₀, hi₀⟩ := hS
  apply le_antisymm
  · refine raw_read_le Φ hmono (S := maskSig S) (fun i f => maskTo S i f) (fun x => ?_)
    refine (Raw.maskDiagonal_coeff_at S hi₀ x).trans ?_
    show _ = if ∀ i ∈ S, ∀ j ∈ S, ((maskTo S i (x i) : Fin _) : ℕ) = maskTo S j (x j) then 1 else 0
    by_cases hc : ∀ (i : I) (hi : i ∈ S), x i hi = x i₀ hi₀
    · rw [if_pos hc, if_pos]
      intro i hi j hj
      exact (maskTo_val S i hi (x i)).trans ((congrArg Fin.val (hc i hi)).trans
        ((congrArg Fin.val (hc j hj)).symm.trans (maskTo_val S j hj (x j)).symm))
    · rw [if_neg hc, if_neg]
      intro hall
      apply hc
      intro i hi
      apply Fin.ext
      have := hall i hi i₀ hi₀
      exact (maskTo_val S i hi (x i)).symm.trans (this.trans (maskTo_val S i₀ hi₀ (x i₀)))
  · refine read_raw_le Φ hmono (X := Raw.maskDiagonal ℂ S (Fin 2)) (S := maskSig S)
      (fun i z => maskFrom S i z) (fun z => ?_)
    refine Eq.trans ?_ (Raw.maskDiagonal_coeff_at S hi₀ (fun i => maskFrom S i (z i))).symm
    show (if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then (1 : ℂ) else 0) = _
    by_cases hc : ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j
    · rw [if_pos hc, if_pos]
      intro i hi
      exact Fin.ext (hc i hi i₀ hi₀)
    · rw [if_neg hc, if_neg]
      intro hall
      apply hc
      intro i hi j hj
      have h1 := congrArg Fin.val (hall i hi)
      have h2 := congrArg Fin.val (hall j hj)
      exact h1.trans h2.symm

end mask


section spec
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The spectral point on tensor classes induced by a coordinate spectral point. -/
noncomputable def phiClass (Φ : T I → ℝ) (h0 : ∀ X, 0 ≤ Φ X) (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X) :
    TensorClass.{0} I ℂ → NNReal :=
  Quotient.lift (s := Raw.setoid.{0} I ℂ) (fun X => ⟨Φ (toSig X), h0 _⟩)
    (fun _ _ h => Subtype.ext (le_antisymm (raw_mono Φ hmono h.1) (raw_mono Φ hmono h.2)))

theorem phiClass_mem [Nonempty I] (Φ : T I → ℝ) (h0 : ∀ X, 0 ≤ Φ X)
    (h1 : Φ ⟨fun _ => 1, fun _ => 1⟩ = 1)
    (hz : ∀ X : T I, (∀ z, X.2 z = 0) → Φ X = 0)
    (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X)
    (hmul : ∀ X Y : T I, Φ (sigMul X Y) = Φ X * Φ Y)
    (hadd : ∀ X Y : T I, Φ (sigAdd X Y) = Φ X + Φ Y) :
    phiClass Φ h0 hmono ∈ normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show Φ (toSig (Raw.zero I ℂ)) = 0
    exact hz _ (fun _ => rfl)
  · apply Subtype.ext
    show Φ (toSig (Raw.one I ℂ)) = 1
    rw [raw_eq Φ hmono (S := ⟨fun _ => 1, fun _ => 1⟩) (fun _ => ⟨fun _ => 0, fun _ => PUnit.unit, fun _ => rfl,
        fun _ => Subsingleton.elim _ _⟩)
      (fun _ => rfl)]
    exact h1
  · intro x y
    refine Quotient.inductionOn₂ (s₁ := Raw.setoid.{0} I ℂ) (s₂ := Raw.setoid.{0} I ℂ) x y
      fun X Y => ?_
    apply Subtype.ext
    show Φ (toSig (X.add Y)) = Φ (toSig X) + Φ (toSig Y)
    rw [raw_eq Φ hmono (S := sigAdd (toSig X) (toSig Y)) (addEquiv X Y) (add_coeff X Y)]
    exact hadd _ _
  · intro x y
    refine Quotient.inductionOn₂ (s₁ := Raw.setoid.{0} I ℂ) (s₂ := Raw.setoid.{0} I ℂ) x y
      fun X Y => ?_
    apply Subtype.ext
    show Φ (toSig (X.mul Y)) = Φ (toSig X) * Φ (toSig Y)
    rw [raw_eq Φ hmono (S := sigMul (toSig X) (toSig Y)) (mulEquiv X Y) (mul_coeff X Y)]
    exact hmul _ _
  · intro x y
    refine Quotient.inductionOn₂ (s₁ := Raw.setoid.{0} I ℂ) (s₂ := Raw.setoid.{0} I ℂ) x y
      fun X Y h => ?_
    exact raw_mono Φ hmono h

end spec

end OMAPort
end

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open OAI.Combinatorics.Sunflower OMAPort
open scoped Classical
theorem OMA.solution : OMA.R_Erdos535_erdos_535_R2_H1_R1_H1_R1.H2 := by
  intro r hr
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  let _ : Nontrivial (Placement.Site n) := ⟨⟨Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inl_ne_inr⟩⟩
  refine ⟨Placement.Site n, inferInstance, inferInstance, inferInstance, Placement.embedding n, ?_⟩
  rintro Φ ⟨h0, h1, hz, hmono, hmul, hadd, hprice⟩
  let φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Placement.Site n) ℂ → _ → Prop) :=
    ⟨phiClass Φ h0 hmono, phiClass_mem Φ h0 h1 hz hmono hmul hadd⟩
  apply bound_of_prices n φ
  · rw [Placement.width_univ]
    linarith [Placement.one_lt_spanX n]
  · intro S hS
    unfold maskDiagonalPrice rawLogPrice
    rw [one_mul]
    change Real.logb 2 (Φ (toSig (Raw.maskDiagonal ℂ S (Fin 2)))) = _
    rw [mask_le Φ hmono S hS]
    refine (hprice S hS).trans ?_
    rw [Placement.width_eq S hS,
      Placement.width_eq _ Finset.univ_nonempty]
    simp only [meanWidth, support, Finset.sup'_map]
    rw [mul_div_mul_left _ _ (Real.sqrt_pos.mpr (by positivity)).ne']
    all_goals rfl
