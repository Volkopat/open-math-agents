import FormalConjectures.ErdosProblems.«535»
import Mathlib

-- Credit: @MrSeizy

/-!
The arithmetic sunflower bound from planar wire realizability.

The tensor comparison, adapted from OpenAI math at 3344da59991ed94f9ba711217b29c1d760badfa6
(Apache-2.0), uses the local port for the sunflower word bound. The planar placement
uses a tiling bound on the sum of parallelogram price deficits and a common translate
for the anchor rectangle and adjacent triangles. The triangle upper bound is proved
by restricting a product of three wires to the diagonal indexed by progressions
with differences in a Behrend set.

The arithmetic transfer and the rainbow color-coding transfer use the merged
sunflower_strong.R1, R1.H2, and R1.H1.R1.H2 proofs by JamesSlash.
-/





/- Reduction of the fixed-base word sunflower bound to planar spectral prices. -/

/-
Adapted from OpenAI math, commit 3344da59991ed94f9ba711217b29c1d760badfa6,
licensed under Apache 2.0 as reproduced in LICENSE.OpenAI. Source paths are relative to lean/OAI.
This port inlines the tensor and sunflower argument under Lean 4.33.1,
makes its mathematical definitions private, and proves the finite planar formulas
by translation, tiling, and a half-turn selection of satellite rows.
The merged sibling R1.H1.R1.H2 ports the later rainbow-coloring transfer from
the same revision. The coloring transfer applies after the word estimate.
-/

/- Ported from LinearAlgebra/SpectralBooks/Crossing.lean -/
section
/-
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
private structure Wire (I : Type*) where
  left : I
  right : I
  distinct : left ≠ right
  width : ℕ

/-- A local index has one bit per wire bit at an endpoint and no bits elsewhere. -/
private abbrev Wire.Leg (e : Wire I) (i : I) :=
  {_t : Fin e.width // i = e.left ∨ i = e.right} → Bool
/-- The two endpoints see the same string. -/
private def Wire.basisTerm (e : Wire I) (s : Fin e.width → Bool) (i : I) : e.Leg i :=
  fun t => s t.val

/-- Coefficients of a tensor presented as a finite sum of coordinate basis tensors. -/
private def basisTensor {A : I → Type*} {S : Type*} [Fintype S]
    (term : S → ∀ i, A i) (x : ∀ i, A i) : F :=
  ∑ s, if x = term s then 1 else 0
/-- On basis terms, a tensor direct sum tags every site's input by the same summand. -/
private def sumBasis {L : Type*} {S : L → Type*} {A : L → I → Type*}
    (term : ∀ l, S l → ∀ i, A l i) (s : Σ l, S l) (i : I) : Σ l, A l i :=
  ⟨s.1, term s.1 s.2 i⟩

/-- A basis term of a grouped power chooses the terms of the factors independently. -/
private def powerBasis {S : Type*} {A : I → Type*}
    (term : S → ∀ i, A i) (j : ℕ) (s : Fin j → S) (i : I) : Fin j → A i :=
  fun t => term (s t) i
/-- Direct sum of identical copies, recording the copy index at every site. -/
private def copiesBasis {S : Type*} {A : I → Type*}
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
private def IsRestriction {A B : I → Type*} [∀ i, Fintype (A i)]
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
private abbrev LocalTables {B : I → Type*} {j : ℕ} (wires : Fin j → Wire I) (F : Type*) :=
  ∀ i, B i → ((t : Fin j) → (wires t).Leg i) → F
/-- Coefficients of a network, obtained by contracting one shared index for each wire. -/
private def network {B : I → Type*} {j : ℕ} (wires : Fin j → Wire I)
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
private def copiesOfWirePower {E : Type*} [Fintype E] (wires : E → Wire I) (K j : ℕ) :=
  basisTensor (F := F) (copiesBasis (powerBasis (sumBasis fun l => (wires l).basisTerm) j) K)
/-- Ordinary local-matrix restriction from the tensor used in strict comparison. -/
private def RestrictsWirePower {B : I → Type*} {E : Type*} [Fintype E]
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
private def wireCost (length : I → I → ℝ) (e : Wire I) : ℝ :=
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

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/Restriction.lean -/
section
/-
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

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/Raw.lean -/
section
/- # Finite coefficient tensors and local restriction

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
private structure Raw (I : Type u) (K : Type w) where
  Leg : I → Type v
  finiteLeg : ∀ i, Fintype (Leg i)
  coeff : (∀ i, Leg i) → K

private instance Raw.instFintypeLeg {I : Type u} {K : Type w} (T : Raw.{v} I K) (i : I) :
    Fintype (T.Leg i) := T.finiteLeg i

namespace Raw

variable {I : Type u} {K : Type w}

noncomputable section
open scoped Classical
/-- Restriction by one matrix at each site, expressed in the chosen bases. -/
private abbrev Restricts [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) :=
  Crossing.IsRestriction X.coeff Y.coeff

/-- The equivalence relation used to form the tensor semiring. -/
private def Equivalent [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) : Prop :=
  X.Restricts Y ∧ Y.Restricts X
/-- Mutual restriction is a setoid by composition of local matrices. -/
private def setoid (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] : Setoid (Raw.{v} I K) where
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
private def zero (I : Type u) (K : Type w) [Zero K] : Raw.{v} I K :=
  ⟨fun _ => PEmpty, fun _ => inferInstance, fun _ => 0⟩

/-- The scalar unit has one basis vector at each site. -/
private def one (I : Type u) (K : Type w) [One K] : Raw.{v} I K :=
  ⟨fun _ => PUnit, fun _ => inferInstance, fun _ => 1⟩
/-- Tensor multiplication groups the two local factors at each site. -/
private def mul [Mul K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => X.Leg i × Y.Leg i, fun _ => inferInstance,
    fun x => X.coeff (fun i => (x i).1) * Y.coeff (fun i => (x i).2)⟩

/-- The common-label diagonal, with one summand per label. -/
private def diagonal (I : Type u) (K : Type w) (α : Type v) [Fintype α] [CommSemiring K] : Raw.{v} I K :=
  ⟨fun _ => α, fun _ => inferInstance, fun x => ∑ a : α, if x = fun _ => a then 1 else 0⟩
end
end Raw

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/Product.lean -/
section
/-
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

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/SumDef.lean -/
section
/- # Direct sums in coordinates

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
private def pushCoeff [AddCommMonoid K] (f : X → Y) (T : X → K) (y : Y) : K :=
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
private def sumCoeff (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (y : ∀ i, A i ⊕ B i) : K :=
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

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/Ops.lean -/
section
/- # Direct sum of finite coefficient tensors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

universe v u w

variable {I : Type u} {K : Type w} [Fintype I]
/-- The direct sum uses a disjoint union at every site. -/
private noncomputable def add [AddCommMonoid K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
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

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/Quotient.lean -/
section
/- # Tensor classes ordered by restriction

Mutual restriction identifies precisely those tensors with the same upper and lower
bounds in the local restriction preorder.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

/-- Finite site tensors up to mutual restriction. -/
private def TensorClass (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] :=
  Quotient (Raw.setoid.{v} I K)
variable {I : Type u} {K : Type w} [Fintype I] [CommSemiring K]

/-- Pass a coefficient tensor to its class under mutual restriction. -/
private def ofRaw (X : Raw.{v} I K) : TensorClass.{v} I K :=
  Quotient.mk _ X

@[simp] theorem ofRaw_eq_iff {X Y : Raw.{v} I K} :
    ofRaw X = ofRaw Y ↔ X.Equivalent Y := Quotient.eq
private instance : LE (TensorClass.{v} I K) where
  le := Quotient.lift₂ Raw.Restricts fun _ _ _ _ hX hY => propext
    ⟨fun h => restrict_trans hX.2 (restrict_trans h hY.1),
     fun h => restrict_trans hX.1 (restrict_trans h hY.2)⟩

@[simp] theorem ofRaw_le_iff {X Y : Raw.{v} I K} :
    ofRaw X ≤ ofRaw Y ↔ X.Restricts Y := Iff.rfl
private instance : PartialOrder (TensorClass.{v} I K) where
  le_refl X := Quotient.inductionOn X fun x => restrict_refl x.coeff
  le_trans X Y Z := Quotient.inductionOn₃ X Y Z fun _ _ _ => restrict_trans
  le_antisymm X Y := Quotient.inductionOn₂ X Y fun _ _ h g => Quotient.sound ⟨h, g⟩

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/Sum.lean -/
section
/- # Direct sums preserve tensor restrictions -/

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

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/AddLaws.lean -/
section
/-
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

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/MulLaws.lean -/
section
/- # Multiplication laws for finite tensors up to mutual restriction -/

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

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/Distrib.lean -/
section
/- # Tensor product distributes over the direct sum

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

/- Ported from LinearAlgebra/SpectralBooks/TensorSemiring.lean -/
section
/- # The semiring of tensors up to mutual restriction
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
private instance : Add (TensorClass.{v} I K) where
  add := Quotient.map₂ Raw.add fun _ _ h _ _ g =>
    ⟨restrict_sum h.1 g.1, restrict_sum h.2 g.2⟩

private instance : Mul (TensorClass.{v} I K) where
  mul := Quotient.map₂ Raw.mul fun _ _ h _ _ g =>
    ⟨Raw.mul_restricts h.1 g.1, Raw.mul_restricts h.2 g.2⟩

private instance : Zero (TensorClass.{v} I K) := ⟨ofRaw (Raw.zero I K)⟩
private instance : One (TensorClass.{v} I K) := ⟨ofRaw (Raw.one I K)⟩
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
private instance : CommSemiring (TensorClass.{v} I K) where
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

/- Ported from LinearAlgebra/SpectralBooks/MaskDiagonal.lean -/
section
/- # Common-label diagonals in a fixed space of sites

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
private abbrev MaskLeg (S : Finset I) (α : Type) (i : I) := i ∈ S → α

/-- A partial diagonal in the ambient site set `I`. -/
private noncomputable def Raw.maskDiagonal (K : Type*) [Field K] (S : Finset I) (α : Type) [Fintype α] :
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

/- Ported from LinearAlgebra/SpectralBooks/PolynomialOverhead.lean -/
section
/- # Removing polynomial overheads from tensor-power inequalities -/

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

/- Ported from LinearAlgebra/SpectralBooks/DimensionLaw.lean -/
section
/- # Logarithmic dependence on wire dimension

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

/- Ported from LinearAlgebra/SpectralBooks/NatSpectralExponent.lean -/
section
/- # Natural diagonal evaluations

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

/- Ported from LinearAlgebra/SpectralBooks/Doubling.lean -/
section
/-
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

/- Ported from LinearAlgebra/SpectralBooks/Spectrum.lean -/
section
/-
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
private def normalizedSpectrum (restricts : S → S → Prop) : Set (S → ℝ≥0) :=
  {f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, f (x * y) = f x * f y) ∧ ∀ x y, restricts x y → f x ≤ f y}
/-- A spectral point preserves the semiring operations. -/
private def normalizedSpectrum.toRingHom {restricts : S → S → Prop}
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

/- Ported from LinearAlgebra/SpectralBooks/StrictComparison.lean -/
section
/-
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
private def ExpandedStrictComparison (spectrum : Set (T →+ ℝ))
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

/- Ported from LinearAlgebra/SpectralBooks/PriceSelection.lean -/
section
/-
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
private def spectralLogHom (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res) :
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
private def IsSpectralPrice (hunit : ∀ t : P, res 1 t) (g : Additive P →+ ℝ) : Prop :=
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

/- Ported from LinearAlgebra/SpectralBooks/SiteSpectrum.lean -/
section
/-
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

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/Nonzero.lean -/
section
/- # Nonzero tensors up to restriction -/

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
private instance [Nonempty I] [Nontrivial K] : Nontrivial (TensorClass.{v} I K) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h' := (ofRaw_eq_zero_iff (Raw.one.{v} I K)).mp h
  exact one_ne_zero (congrFun h' (fun _ => PUnit.unit))
private instance [Nonempty I] [NoZeroDivisors K] : NoZeroDivisors (TensorClass.{v} I K) where
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

/- Ported from LinearAlgebra/SpectralBooks/RawLogPrice.lean -/
section
/-
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
private def rawLogPrice (c : ℝ) (X : Raw.{v} I K) : ℝ :=
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

/- Ported from LinearAlgebra/SpectralBooks/MaskDiagonalPrice.lean -/
section
/- # Prices of partial diagonals on a fixed set of sites

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
private def maskDiagonalHom (K : Type*) [Field K] (S : Finset I) (hS : S.Nonempty) :
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
private def maskDiagonalPrice (c : ℝ) (S : Finset I) : ℝ := rawLogPrice φ c (Raw.maskDiagonal K S (Fin 2))
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

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/DiagonalRaw.lean -/
section
/- # Diagonal tensors and their direct sums -/

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

/- Ported from LinearAlgebra/SpectralBooks/SiteTensor/Diagonal.lean -/
section
/- # Natural numbers in the tensor semiring -/

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

/- Ported from Combinatorics/Sunflower/Tensor.lean -/
section
/-
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
private def contract [CommSemiring K] [∀ i, Fintype (A i)]
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

/- Ported from Combinatorics/Sunflower/Control.lean -/
section
/- A local matrix may be chosen by a symbol at the same site. A symbol carried
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
private abbrev Map (C A B : I → Type*) := ∀ i, C i → B i → A i → ℂ

/-- The coefficient obtained by applying the chosen local matrices. -/
private def eval [Fintype I] [∀ i, Fintype (A i)] (M : Map C A B)
    (c : ∀ i, C i) (X : (∀ i, A i) → ℂ) (b : ∀ i, B i) : ℂ :=
  contract (fun i => M i (c i)) X b

/-- Apply a function to each control before reading it. -/
private def pre (f : ∀ i, D i → C i) (M : Map C A B) : Map D A B :=
  fun i d => M i (f i d)
@[simp] theorem eval_pre [Fintype I] [∀ i, Fintype (A i)]
    (f : ∀ i, D i → C i) (M : Map C A B) (d : ∀ i, D i)
    (X : (∀ i, A i) → ℂ) (b : ∀ i, B i) :
    eval (pre f M) d X b = eval M (fun i => f i (d i)) X b := rfl

/-- The identity acts on every branch of the external control. -/
private def idMap {C A : I → Type*} : Map C A A :=
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
private def retainMap (M : Map (fun i => D i × C i) A B) :
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
private def prodMap {A' B' : I → Type*} (M : Map C A B) (N : Map C A' B') :
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
private def compMap [∀ i, Fintype (B i)] (N : Map C B E) (M : Map C A B) : Map C A E :=
  fun i c e a => ∑ b, M i c b a * N i c e b

theorem eval_compMap [Fintype I] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (N : Map C B E) (M : Map C A B) (c : ∀ i, C i) (X : (∀ i, A i) → ℂ) (e : ∀ i, E i) :
    eval (compMap N M) c X e = eval N c (eval M c X) e :=
  congrFun (contract_comp (fun i => N i (c i)) (fun i => M i (c i)) X).symm e
/-- Local assembly of two block maps into a common output format. -/
private def sumMap {A' : I → Type*} (M : Map C A B) (N : Map C A' B) :
    Map C (fun i => A i ⊕ A' i) B :=
  fun i c b => Sum.elim (M i c b) (N i c b)
theorem eval_sumMap [Fintype I] {A' : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (A' i)]
    (M : Map C A B) (N : Map C A' B) (c : ∀ i, C i)
    (X : (∀ i, A i) → ℂ) (Y : (∀ i, A' i) → ℂ) (b : ∀ i, B i) :
    eval (sumMap M N) c (sumCoeff X Y) b = eval M c X b + eval N c Y b :=
  congrFun (contract_addBlocks (fun i => M i (c i)) (fun i => N i (c i)) X Y) b
/-- The distinguished site's sign changes the second summand to its negative. -/
private def diffMap {A' : I → Type*} (j : I) (M : Map C A B) (N : Map C A' B) :
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

/- Ported from Combinatorics/Sunflower/Basic.lean -/
section
/- # Sunflowers in set families and in word families -/

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {ι I α β : Type*}

/-- Every entry of the tuple has the same value. This includes the empty tuple. -/
private def IsConstant (f : ι → β) : Prop :=
  ∀ i j, f i = f j

/-- One coordinate of a sunflower has either a common symbol or pairwise distinct symbols. -/
private def Admissible (f : ι → β) : Prop :=
  IsConstant f ∨ Function.Injective f
/-- Each coordinate of the tuple of words is admissible. -/
private def WordAdmissible (w : ι → I → β) : Prop :=
  ∀ c, Admissible (fun i => w i c)

/-- Every admissible ordered tuple of words in the family repeats one word. -/
private def WordFree (r : ℕ) (W : Finset (I → β)) : Prop :=
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
private def HasSunflower [DecidableEq α] (r : ℕ) (F : Finset (Finset α)) : Prop :=
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

/- Ported from Combinatorics/Sunflower/Rules.lean -/
section
/- # The two-anchor implication system -/

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {G I α : Type*}

/-- Equality of the symbols on the two antecedents obliges the target to agree. -/
private structure Rule (G : Type*) where
  left : G
  right : G
  target : G
  deriving DecidableEq, Fintype
private def Rule.Holds (q : Rule G) (f : G → α) : Prop :=
  f q.left = f q.right → f q.left = f q.target

theorem Rule.not_holds_iff (q : Rule G) (f : G → α) :
    ¬ q.Holds f ↔ f q.left = f q.right ∧ f q.left ≠ f q.target := by
  classical
  simp [Rule.Holds]
/-- In the fourth rule each unordered pair of satellites occurs once. -/
private inductive IsAnchorRule [LT G] (A B : G) : Rule G → Prop where
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
private noncomputable def anchorRules [Fintype G] [LT G] (A B : G) : Finset (Rule G) := by
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

/- Ported from Combinatorics/Sunflower/Comparison.lean -/
section
/- # Comparing a word family with the full diagonal

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
private def fiber (group : S → G) (j : G) : Finset S :=
  Finset.univ.filter fun s => group s = j

@[simp] theorem mem_fiber {group : S → G} {j : G} {s : S} :
    s ∈ fiber group j ↔ group s = j := by simp [fiber]
theorem fiber_nonempty {group : S → G} (h : Function.Surjective group) (j : G) :
    (fiber group j).Nonempty := by
  obtain ⟨s, hs⟩ := h j
  exact ⟨s, mem_fiber.mpr hs⟩

/-- Coefficient predicate for independent word indices on the selected groups. -/
private def Compatible (group : S → G) (J : Finset G) {L : Type*} (x : S → L) : Prop :=
  ∀ s t, group s ∈ J → group s = group t → x s = x t
private def groupTensor (group : S → G) (J : Finset G) (L : Type) [Fintype L] : Raw.{0} S ℂ :=
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
private structure Device (S C : Type*) where
  R : Raw.{0} S ℂ
  Q : Raw.{0} S ℂ
  R_ne : R.coeff ≠ 0
  Q_ne : Q.coeff ≠ 0
  M : ∀ s, C → Q.Leg s → R.Leg s → ℂ

variable {C : Type*}

private def Device.out (D : Device S C) (c : S → C) : (∀ s, D.Q.Leg s) → ℂ :=
  contract (fun s => D.M s (c s)) D.R.coeff

variable [Nonempty S]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} S ℂ → _ → Prop))
private def Device.cost (D : Device S C) : ℝ := rawLogPrice φ 1 D.R - rawLogPrice φ 1 D.Q

omit [Fintype S] [Nonempty S] in
private theorem raw_mul_nonzero (X Y : Raw.{0} S ℂ)
    (hX : X.coeff ≠ 0) (hY : Y.coeff ≠ 0) : (X.mul Y).coeff ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hX
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hY
  exact Function.ne_iff.mpr ⟨fun i => (a i, b i), mul_ne_zero ha hb⟩
private def Device.parallel (D E : Device S C) : Device S C where
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
private def Device.unit (S C : Type*) : Device S C where
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
private def Device.pre {B : Type*} (D : Device S C) (f : B → C) : Device S B where
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

/- Ported from Combinatorics/Sunflower/Copy.lean -/
section
/- The single-target convex-hull copying construction. A shared binary string indexed
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

private abbrev Bits (n : ℕ) := Fin n → Bool

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
private abbrev input (P : Finset I) (z : I) (n : ℕ) : Raw.{0} I ℂ :=
  Raw.maskDiagonal ℂ (insert z P) (Bits (n + 1))

private abbrev returned (P : Finset I) (n : ℕ) : Raw.{0} I ℂ :=
  Raw.maskDiagonal ℂ P (Bits n)
/-- Each local matrix reads its own control. At the target `z`, the control is the
desired output index of the copied vector, or the symbol to compare against. -/
private def matrix (P : Finset I) (z s₀ : I) (n : ℕ) (s : I) (label : Fin (n + 1))
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
private def labelAt (z : I) {n : ℕ} (i : Fin (n+1)) : Raw.{0} I ℂ :=
  ⟨MaskLeg {z} (Fin (n+1)), fun _ ↦ Fintype.ofFinite _,
    fun x ↦ if i = x z (Finset.mem_singleton_self z) then 1 else 0⟩
/-- The copying matrix emits the chosen label at the target. Unlike the test matrix,
its target row supplies the label being tested. -/
private def copyMatrix (P : Finset I) (z s₀ : I) (n : ℕ) (s : I) (label : Fin (n+1))
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

/- Ported from Combinatorics/Sunflower/Placement/Sites.lean -/
section
/- Sites, groups, and fibers for the planar sunflower placement. -/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Placement

/-- Each anchor has an endpoint at each extreme height and one site at each satellite
height. Each satellite group consists of a single site. -/
private abbrev Site (n : ℕ) := Fin (n + 2) ⊕ (Fin (n + 2) ⊕ Fin n)

variable {n : ℕ}
private def a (j : Fin (n + 2)) : Site n := Sum.inl j
private def b (j : Fin (n + 2)) : Site n := Sum.inr (Sum.inl j)
private def z (i : Fin n) : Site n := Sum.inr (Sum.inr i)

/-- The index of the anchor site at the height of satellite `i`. -/
private def interior (i : Fin n) : Fin (n + 2) := i.succ.castSucc

@[simp] theorem interior_val (i : Fin n) : (interior i).val = i.val + 1 := rfl

theorem interior_pos (i : Fin n) : 0 < interior i := by
  change 0 < i.val + 1
  omega
theorem interior_lt_last (i : Fin n) : interior i < Fin.last (n + 1) := by
  change i.val + 1 < n + 1
  omega

/-- Group 0 is the first anchor, group 1 the second, and group `i+2` a satellite. -/
private def group : Site n → Fin (n + 2)
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

private def fiber (g : Fin (n + 2)) : Finset (Site n) := Finset.univ.filter (group · = g)

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

/- Ported from Combinatorics/Sunflower/Placement/RuleSites.lean -/
section
/- # Source and target sites of an anchor rule -/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Placement

variable {n : ℕ} {q : Rule (Fin (n + 2))}
/-- The three groups of locally readable sites for one ordered rule. -/
private structure RuleSites {n : ℕ} (q : Rule (Fin (n + 2))) where
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
private def Works (w : Finset (Site n) → ℝ) : Prop :=
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

/- Ported from Combinatorics/Sunflower/Planar.lean -/
section
/- The finite planar configurations used for the anchor and satellite rules. -/

noncomputable section
open scoped Classical Pointwise
open OAI.LinearAlgebra.SpectralBooks

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Planar

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean diagonal price laws in the full plane. -/
private structure PlanarPriceLaws (δ : Finset Plane → ℝ) : Prop where
  monotone : Monotone δ
  submodular : ∀ A B : Finset Plane, (A ∩ B).Nonempty →
    δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B
  wire : ∀ a b : Plane, δ {a, b} = dist a b
  triangle_le : ∀ a b c : Plane, δ {a,b,c} ≤ (dist a b + dist b c + dist c a) / 2

namespace PlanarPriceLaws

variable {δ : Finset Plane → ℝ} (hδ : PlanarPriceLaws δ)

include hδ in
private theorem singleton (x : Plane) : δ {x} = 0 := by
  simpa using hδ.wire x x


include hδ in
private theorem pairSubmodular {A B : Finset Plane} {x y : Plane}
    (h : {x, y} ⊆ A ∩ B) : δ (A ∪ B) + δ {x, y} ≤ δ A + δ B := by
  exact (add_le_add (le_refl (δ (A ∪ B))) (hδ.monotone h)).trans
    (hδ.submodular A B ((Finset.insert_nonempty _ _).mono h))

include hδ in
private theorem insert_segment {S : Finset Plane} {a b : Plane} (ha : a ∈ S) (hb : b ∈ S)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    δ (insert (s • a + t • b) S) = δ S := by
  let z := s • a + t • b
  change δ (insert z S) = δ S
  apply le_antisymm _ (hδ.monotone (Finset.subset_insert _ _))
  have hu : S ∪ {a,b,z} = insert z S := by
    ext p
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hp | rfl | rfl | rfl)
      · exact Or.inr hp
      · exact Or.inr ha
      · exact Or.inr hb
      · exact Or.inl rfl
    · tauto
  have hi : {a,b} ⊆ S ∩ {a,b,z} := by simp [Finset.insert_subset_iff, ha, hb]
  have hinc := hδ.pairSubmodular hi
  rw [hu, hδ.wire] at hinc
  have hz : z = a + t • (b - a) := by
    dsimp [z]
    rw [smul_sub]
    have hs' : s = 1 - t := by linarith
    rw [hs', sub_smul, one_smul]
    abel
  have habz : dist b z = s * dist a b := by
    rw [dist_eq_norm, show b - z = s • (b - a) by
      rw [hz, show s = 1 - t by linarith, sub_smul, one_smul]; abel,
      norm_smul, Real.norm_of_nonneg hs, ← dist_eq_norm, dist_comm]
  have hza : dist z a = t * dist a b := by
    rw [dist_eq_norm, hz, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht,
      ← dist_eq_norm, dist_comm]
  have htri := hδ.triangle_le a b z
  rw [habz, hza, add_assoc, ← add_mul, hst, one_mul] at htri
  linarith

include hδ in
private theorem insertHull {S : Finset Plane} {p : Plane} (hp : p ∈ convexHull ℝ (S : Set Plane)) :
    δ (insert p S) = δ S := by
  apply le_antisymm _ (hδ.monotone (Finset.subset_insert _ _))
  by_cases hS : S.Nonempty
  · let K : Set Plane := {q | δ (insert q S) ≤ δ S}
    have hK : Convex ℝ K := by
      intro x hx y hy a b ha hb hab
      let U := insert x (insert y S)
      have hUS : S ⊆ U := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
      have hInter : S ⊆ insert x S ∩ insert y S := by
        exact Finset.subset_inter (Finset.subset_insert _ _) (Finset.subset_insert _ _)
      have hUnion : insert x S ∪ insert y S = U := by
        ext z
        simp only [U, Finset.mem_union, Finset.mem_insert]
        tauto
      have hsub := hδ.submodular _ _ (hS.mono hInter)
      have hmono := hδ.monotone hInter
      rw [hUnion] at hsub
      have hu : δ U ≤ δ S := by
        change δ (insert x S) ≤ δ S at hx
        change δ (insert y S) ≤ δ S at hy
        linarith
      change δ (insert (a • x + b • y) S) ≤ δ S
      exact (hδ.monotone (Finset.insert_subset_insert _ hUS)).trans
        ((hδ.insert_segment (by simp [U]) (by simp [U]) ha hb hab).le.trans hu)
    have hSK : (S : Set Plane) ⊆ K := fun x hx => by
      change δ (insert x S) ≤ δ S
      rw [Finset.insert_eq_of_mem hx]
    exact (convexHull_min hSK hK hp : p ∈ K)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.coe_empty, convexHull_empty] at hp
    exact hp.elim


include hδ in
private theorem eq_of_hull {S T : Finset Plane} (hST : S ⊆ T)
    (hT : (T : Set Plane) ⊆ convexHull ℝ (S : Set Plane)) : δ T = δ S := by
  have hu : ∀ U : Finset Plane, (U : Set Plane) ⊆ convexHull ℝ (S : Set Plane) →
      δ (U ∪ S) = δ S := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert p U hp ih =>
      intro h
      rw [Finset.insert_union, hδ.insertHull (convexHull_mono (by simp : (S : Set Plane) ⊆ ↑(U ∪ S))
        (h (Finset.mem_insert_self _ _)))]
      exact ih fun q hq ↦ h (Finset.mem_insert_of_mem hq)
  simpa [Finset.union_eq_left.mpr hST] using hu T hT

private noncomputable def par (x u v : Plane) : Finset Plane := {x, x + u, x + v, x + u + v}


include hδ in
private theorem par_split (x u v : Plane) :
    δ (par x u v) + dist (x + u) (x + v) ≤
      δ {x, x + u, x + v} + δ {x + u + v, x + u, x + v} := by
  let A : Finset Plane := {x, x + u, x + v}
  let B : Finset Plane := {x + u + v, x + u, x + v}
  have hs : {x + u, x + v} ⊆ A ∩ B := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, A, B]
    constructor <;> simp
  have hu : par x u v = A ∪ B := by
    ext t
    simp only [par, A, B, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hu, ← hδ.wire]
  exact hδ.pairSubmodular hs

private theorem par_tri_arith (x u v : Plane) :
    (dist x (x + u) + dist (x + u) (x + v) + dist (x + v) x) / 2 =
      (‖u‖ + ‖v‖ + dist (x + u) (x + v)) / 2 ∧
    (dist (x + u + v) (x + u) + dist (x + u) (x + v) + dist (x + v) (x + u + v)) / 2 =
      (‖u‖ + ‖v‖ + dist (x + u) (x + v)) / 2 := by
  rw [show x + u + v = (x + v) + u by abel]
  have hu : dist (x + v + u) (x + u) = ‖v‖ := by
    rw [dist_add_right, dist_eq_norm, add_sub_cancel_left]
  have hv : dist (x + v) (x + v + u) = ‖u‖ := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
  have hud : dist x (x + u) = ‖u‖ := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
  have hvd : dist (x + v) x = ‖v‖ := by rw [dist_eq_norm, add_sub_cancel_left]
  rw [hu, hv, hud, hvd]
  constructor <;> ring


include hδ in
private theorem par_upper (x u v : Plane) : δ (par x u v) ≤ ‖u‖ + ‖v‖ := by
  have h₁ := hδ.triangle_le x (x + u) (x + v)
  have h₂ := hδ.triangle_le (x + u + v) (x + u) (x + v)
  rw [(par_tri_arith x u v).1] at h₁
  rw [(par_tri_arith x u v).2] at h₂
  linarith [hδ.par_split x u v]

include hδ in
private theorem triangle_lower (x u v : Plane) {ε : ℝ}
    (h : ‖u‖ + ‖v‖ - ε ≤ δ (par x u v)) :
    (dist x (x + u) + dist (x + u) (x + v) + dist (x + v) x) / 2 - ε ≤
      δ {x, x + u, x + v} := by
  have h₂ := hδ.triangle_le (x + u + v) (x + u) (x + v)
  rw [(par_tri_arith x u v).1, (par_tri_arith x u v).2] at *
  linarith [hδ.par_split x u v]

include hδ in
/-- Tiling a long parallelogram bounds the total price deficit of all its unit strips. -/
private theorem sum_par_deficit (x u v : Plane) (N : ℕ) :
    ∑ j ∈ Finset.range N, (‖u‖ + ‖v‖ - δ (par (x + (j : ℝ) • u) u v)) ≤ ‖v‖ := by
  let P (n : ℕ) := par x ((n : ℝ) • u) v
  have hstep (n : ℕ) :
      δ (P (n + 1)) + ‖v‖ ≤ δ (P n) + δ (par (x + (n : ℝ) • u) u v) := by
    let Q := par (x + (n : ℝ) • u) u v
    let E : Finset Plane := {x + (n : ℝ) • u, x + (n : ℝ) • u + v}
    have he : E ⊆ P n ∩ Q := by simp [E, P, Q, par, Finset.insert_subset_iff]
    have hu : P (n + 1) ⊆ P n ∪ Q := by
      have hsmul : x + ((n + 1 : ℕ) : ℝ) • u = x + (n : ℝ) • u + u := by
        rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_assoc]
      change par x (((n + 1 : ℕ) : ℝ) • u) v ⊆ _
      simp only [par, hsmul, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      simp [P, Q, par]
    have hv : δ E = ‖v‖ := by
      dsimp only [E]
      rw [hδ.wire, dist_comm, dist_eq_norm, add_sub_cancel_left]
    exact (add_le_add (hδ.monotone hu) (le_refl ‖v‖)).trans (hv ▸ hδ.pairSubmodular he)
  have hs (n : ℕ) :
      δ (P n) + ∑ j ∈ Finset.range n, (‖u‖ + ‖v‖ - δ (par (x + (j : ℝ) • u) u v)) ≤
        (n : ℝ) * ‖u‖ + ‖v‖ := by
    induction n with
    | zero =>
      have h : P 0 = {x, x + v} := by simp [P, par]
      rw [h, hδ.wire, dist_comm, dist_eq_norm, add_sub_cancel_left]
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ]
      linarith [hstep n]
  have hsize : (N : ℝ) * ‖u‖ ≤ δ (P N) := by
    have h : {x, x + (N : ℝ) • u} ⊆ P N := by simp [P, par]
    have hm := hδ.monotone h
    rwa [hδ.wire, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)] at hm
  linarith [hs N]

include hδ in
/-- A single translation makes all parallelogram prices in a finite list nearly maximal. -/
private theorem simultaneous_par_lower {J : Type*} [Fintype J] (u : Plane) (v : J → Plane)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ i, ‖u‖ + ‖v i‖ - ε ≤ δ (par ((n : ℝ) • u) u (v i)) := by
  let score (j : ℕ) (i : J) := ‖u‖ + ‖v i‖ - δ (par ((j : ℝ) • u) u (v i))
  have hnon (j : ℕ) (i : J) : 0 ≤ score j i :=
    sub_nonneg.mpr (hδ.par_upper _ _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt ((∑ i, ‖v i‖) / ε)
  have hN' := (div_lt_iff₀ hε).mp hN
  by_contra! h
  have hl (j : ℕ) : ε ≤ ∑ i, score j i := by
    obtain ⟨i, hi⟩ := h j
    have hb : ε ≤ score j i := by dsimp [score]; linarith
    exact hb.trans (Finset.single_le_sum (f := score j) (fun i _ => hnon j i) (Finset.mem_univ i))
  have hu : (∑ j ∈ Finset.range N, ∑ i, score j i) ≤ ∑ i, ‖v i‖ := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun i _ => by
      simpa [score] using hδ.sum_par_deficit 0 u (v i) N
  have htot : (N : ℝ) * ε ≤ ∑ j ∈ Finset.range N, ∑ i, score j i := by
    simpa using (Finset.sum_le_sum (s := Finset.range N) fun j _ => hl j)
  linarith [htot.trans hu]


end PlanarPriceLaws
private def xy (x y : ℝ) : Plane := WithLp.toLp 2 ![x,y]
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

private def rectangle (a b c d : ℝ) : Finset Plane := {xy a c, xy a d, xy b c, xy b d}

private theorem price_rectangle {δ : Finset Plane → ℝ} (hδ : PlanarPriceLaws δ) (a b c d : ℝ) :
    δ (rectangle a b c d) ≤ |a-b| + |c-d| := by
  have he : rectangle a b c d = PlanarPriceLaws.par (xy a c) (xy (b-a) 0) (xy 0 (d-c)) := by
    ext z
    simp only [rectangle, PlanarPriceLaws.par, Finset.mem_insert, Finset.mem_singleton, xy_add,
      add_zero, add_sub_cancel]
    tauto
  have hu : ‖xy (b-a) 0‖ = |a-b| := by
    rw [← dist_zero_right, show (0 : Plane) = xy 0 0 by ext i; fin_cases i <;> rfl,
      dist_xy_horiz, sub_zero, abs_sub_comm]
  have hv : ‖xy 0 (d-c)‖ = |c-d| := by
    rw [← dist_zero_right, show (0 : Plane) = xy 0 0 by ext i; fin_cases i <;> rfl,
      dist_xy_vert, sub_zero, abs_sub_comm]
  rw [he, ← hu, ← hv]
  exact hδ.par_upper _ _ _

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
theorem semiperimeter_vertical_lower {a z y t : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hz : t ≤ |a-z|) :
    1+t^2/4 ≤ (dist (xy a 0) (xy a 1) + dist (xy a 1) (xy z y) +
      dist (xy z y) (xy a 0)) / 2 := by
  rw [ dist_xy_vert, dist_xy, dist_comm (xy z y), dist_xy]
  have h₁ := vertical_offset_cost (h := a-z) (y := 1-y) (by linarith) ht0 ht1 hz
  have h₂ := vertical_offset_cost (h := a-z) hy1 ht0 ht1 hz
  simp only [zero_sub, neg_sq, abs_neg, abs_one]
  linarith

end Planar
end Sunflower
end Combinatorics
end OAI
end

/- Ported from Combinatorics/Sunflower/Placement.lean -/
section
/- # The planar anchor and satellite placement

The anchor lines are one unit tall and slightly more than one unit apart.
The satellites use well-separated rows at a common vertical translate.
The excess anchor separation is quadratic in the satellite offset. -/

noncomputable section
open scoped Classical
open OAI.LinearAlgebra.SpectralBooks OAI.Combinatorics.Sunflower.Planar
namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Placement

variable {n : ℕ}

/-- A satellite is much closer to the first anchor than consecutive candidate rows are to each other. -/
private def offset (n : ℕ) : ℝ := 1 / (32 * ((2*n : ℕ) + 1 : ℝ))

private def spanX (n : ℕ) : ℝ := 1 + (offset n)^2/8

theorem offset_pos (n : ℕ) : 0 < offset n := by unfold offset; positivity

theorem offset_le (n : ℕ) : offset n ≤ 1/32 := by
  rw [offset, div_le_div_iff₀ (by positivity) (by norm_num)]
  have hn : (0:ℝ) ≤ (2*n : ℕ) := by positivity
  linarith

theorem one_lt_spanX (n : ℕ) : 1 < spanX n := by
  have h := sq_pos_of_pos (offset_pos n)
  unfold spanX
  linarith

theorem spanX_lt_two (n : ℕ) : spanX n < 2 := by
  unfold spanX
  nlinarith [offset_pos n, offset_le n]

theorem offset_lt_spanX (n : ℕ) : offset n < spanX n := by
  linarith [offset_le n, one_lt_spanX n]

private structure Rows (δ : Finset Plane → ℝ) (n : ℕ) where
  value : Fin n → ℝ
  pos : ∀ i, 0 < value i
  lt_one : ∀ i, value i < 1
  separated : ∀ ⦃i j⦄, i ≠ j → offset n < |value i - value j|
  nearTriangle : ∀ i, 1 + 3 * (offset n)^2/16 ≤
    δ {xy 0 0, xy 0 1, xy (offset n) (value i)}
  anchorLower : 2 < δ (rectangle 0 (spanX n) 0 1)

variable {δ : Finset Plane → ℝ} (hδ : PlanarPriceLaws δ)

private def choiceHeight (i : Fin n) : ℝ := ((i.val : ℝ) + 1) / ((2*n : ℕ) + 1 : ℝ)

private theorem choiceHeight_pos (i : Fin n) : 0 < choiceHeight i := by
  unfold choiceHeight
  positivity

private theorem choiceHeight_lt_one (i : Fin n) : choiceHeight i < 1 := by
  rw [choiceHeight, div_lt_one (by positivity)]
  have hi : (i.val : ℝ) < (2*n : ℕ) := by exact_mod_cast (show i.val < 2*n by omega)
  linarith

private theorem choiceHeight_separated {i j : Fin n} (hne : i ≠ j) :
    offset n < |choiceHeight i - choiceHeight j| := by
  have hden : 0 < ((2*n : ℕ) + 1 : ℝ) := by positivity
  have habs : (1 : ℝ) ≤ |(i.val : ℝ) - j.val| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hj : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hj : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [choiceHeight, choiceHeight, ← sub_div,
    show (i.val : ℝ) + 1 - (j.val + 1) = (i.val : ℝ) - j.val by ring,
    abs_div, abs_of_pos hden]
  apply lt_of_lt_of_le _ (div_le_div_of_nonneg_right habs hden.le)
  rw [offset, div_lt_div_iff₀ (by positivity) hden]
  linarith

private def near (n : ℕ) (y : ℝ) : Finset Plane :=
  {xy 0 0, xy 0 1, xy (offset n) y}

variable (rows : Rows δ n)

private def height (j : Fin (n+2)) : ℝ := Fin.lastCases 1 (Fin.cases 0 rows.value) j

@[simp] theorem height_zero : height rows (0 : Fin (n+2)) = 0 := by
  change height rows ((0 : Fin (n+1)).castSucc) = 0
  unfold height
  rw [Fin.lastCases_castSucc, Fin.cases_zero]

@[simp] theorem height_top : height rows (Fin.last (n+1)) = 1 := by simp [height]

@[simp] theorem height_interior (i : Fin n) : height rows (interior i) = rows.value i := by
  unfold height interior
  rw [Fin.lastCases_castSucc, Fin.cases_succ]

theorem height_nonneg (j : Fin (n+2)) : 0 ≤ height rows j := by
  refine Fin.lastCases ?_ (fun j ↦ Fin.cases ?_ (fun i ↦ ?_) j) j
  · simp
  · change 0 ≤ height rows 0
    simp
  · exact (height_interior rows i).symm ▸ (rows.pos i).le

theorem height_le_one (j : Fin (n+2)) : height rows j ≤ 1 := by
  refine Fin.lastCases ?_ (fun j ↦ Fin.cases ?_ (fun i ↦ ?_) j) j
  · simp
  · change height rows 0 ≤ 1
    simp
  · exact (height_interior rows i).symm ▸ (rows.lt_one i).le

theorem height_injective : Function.Injective (height rows) := by
  intro i j
  revert j
  refine Fin.lastCases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i) i
  · intro j
    refine Fin.lastCases (fun _ ↦ rfl) (fun j ↦ Fin.cases ?_ (fun j ↦ ?_) j) j
    · change height rows (Fin.last _) = height rows 0 → _
      simp
    · change height rows (Fin.last _) = height rows (interior j) → _
      intro H
      rw [height_top, height_interior] at H
      linarith [rows.lt_one j]
  · intro j
    refine Fin.lastCases ?_ (fun j ↦ Fin.cases (fun _ ↦ rfl) (fun j ↦ ?_) j) j
    · change height rows 0 = height rows (Fin.last _) → _
      simp
    · change height rows 0 = height rows (interior j) → _
      intro H
      rw [height_zero, height_interior] at H
      linarith [rows.pos j]
  · intro j
    refine Fin.lastCases ?_ (fun j ↦ Fin.cases ?_ (fun j ↦ ?_) j) j
    · change height rows (interior i) = height rows (Fin.last _) → _
      intro H
      rw [height_interior, height_top] at H
      linarith [rows.lt_one i]
    · change height rows (interior i) = height rows 0 → _
      intro H
      rw [height_interior, height_zero] at H
      linarith [rows.pos i]
    · change height rows (interior i) = height rows (interior j) → _
      intro H
      simp only [height_interior] at H
      by_contra h
      have Q := rows.separated (show i ≠ j by intro he; subst j; exact h rfl)
      rw [H, sub_self, abs_zero] at Q
      linarith [offset_pos n]

private def position : Site n → Plane
  | .inl j => xy 0 (height rows j)
  | .inr (.inl j) => xy (spanX n) (height rows j)
  | .inr (.inr i) => xy (offset n) (height rows (interior i))
@[simp] theorem position_a (j : Fin (n+2)) : position rows (a j) = xy 0 (height rows j) := rfl
@[simp] theorem position_b (j : Fin (n+2)) : position rows (b j) = xy (spanX n) (height rows j) := rfl
@[simp] theorem position_z (i : Fin n) : position rows (z i) = xy (offset n) (height rows (interior i)) := rfl
theorem position_injective : Function.Injective (position rows) := by
  have hs : spanX n ≠ 0 := ne_of_gt (by linarith [one_lt_spanX n])
  have ht := (offset_pos n).ne'
  have hts := (offset_lt_spanX n).ne
  rintro (j|j|i) (k|k|l) h <;>
    simp only [position, xy_eq_iff] at h <;>
    first | exact congrArg _ (height_injective rows h.2)
          | exact congrArg (fun i ↦ Sum.inr (Sum.inr i)) (Fin.succ_injective _ (Fin.castSucc_injective _ (height_injective rows h.2)))
          | exact congrArg (fun j ↦ Sum.inr (Sum.inl j)) (height_injective rows h.2)
          | exact (hs h.1).elim | exact (hs h.1.symm).elim
          | exact (ht h.1).elim | exact (ht h.1.symm).elim
          | exact (hts h.1).elim | exact (hts h.1.symm).elim
private def embedding : Site n ↪ Plane := ⟨position rows, position_injective rows⟩

@[simp] theorem coe_embedding : ⇑(embedding rows) = position rows := rfl

private def width (S : Finset (Site n)) : ℝ := δ (S.map (embedding rows))

include hδ in
private theorem width_of_hull {S : Finset (Site n)} {V : Finset Plane}
    (hVS : V ⊆ S.map (embedding rows))
    (hh : (↑(S.map (embedding rows)) : Set Plane) ⊆ convexHull ℝ (V : Set Plane)) :
    width rows S = δ V :=
  hδ.eq_of_hull hVS hh

private def endsA (n : ℕ) : Finset (Site n) := {a 0, a (Fin.last (n+1))}
private def endsB (n : ℕ) : Finset (Site n) := {b 0, b (Fin.last (n+1))}
private def triA (i : Fin n) : Finset (Site n) := insert (z i) (endsA n)
private def triB (i : Fin n) : Finset (Site n) := insert (z i) (endsB n)
private def bracket (i : Fin n) : Finset (Site n) := {a (interior i), b (interior i)}
private def satPair (i j : Fin n) : Finset (Site n) := {z i, z j}
private def matchPair (i j : Fin n) : Finset (Site n) := {a (interior i), a (interior j)}
@[simp] theorem image_endsA : (endsA n).map (embedding rows) = {xy 0 0, xy 0 1} := by
  simp [endsA]
@[simp] theorem image_endsB :
    (endsB n).map (embedding rows) = {xy (spanX n) 0, xy (spanX n) 1} := by simp [endsB]
include hδ in
@[simp] theorem width_endsA : width rows (endsA n) = 1 := by
  simp [width, hδ.wire]
include hδ in
@[simp] theorem width_endsB : width rows (endsB n) = 1 := by
  simp [width, hδ.wire]
private theorem position_in_rect (s : Site n) :
    position rows s ∈ convexHull ℝ (rectangle 0 (spanX n) 0 1 : Set Plane) := by
  have h := (offset_lt_spanX n).le
  have h' := (offset_pos n).le
  rcases s with j | j | i <;> apply xy_mem_hull_rectangle <;>
    first | exact height_nonneg rows _ | exact height_le_one rows _ | linarith
private theorem rectangle_eq_ends :
    rectangle 0 (spanX n) 0 1 = ((endsA n ∪ endsB n).map (embedding rows)) := by
  ext p
  simp only [rectangle, Finset.map_union, image_endsA, image_endsB, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union]
  tauto
include hδ in
theorem width_of_corners {S : Finset (Site n)} (h : endsA n ∪ endsB n ⊆ S) :
    width rows S = δ (rectangle 0 (spanX n) 0 1) := by
  have hsub : rectangle 0 (spanX n) 0 1 ⊆ S.map (embedding rows) := by
    rw [rectangle_eq_ends]
    exact Finset.map_subset_map.mpr h
  have hh : (↑(S.map (embedding rows)) : Set Plane) ⊆
      convexHull ℝ (rectangle 0 (spanX n) 0 1 : Set Plane) := by
    intro p hp
    obtain ⟨s, -, rfl⟩ := Finset.mem_map.mp hp
    exact position_in_rect rows s

  exact width_of_hull hδ rows hsub hh

include hδ in
theorem width_corners_le {S : Finset (Site n)} (h : endsA n ∪ endsB n ⊆ S) :
    width rows S ≤ 1 + spanX n := by
  rw [width_of_corners hδ rows h]
  simpa [abs_of_pos ((zero_lt_one : (0:ℝ) < 1).trans (one_lt_spanX n)), add_comm]
    using price_rectangle hδ 0 (spanX n) 0 1

include hδ in
private theorem width_fiber_of_anchor (u : Fin (n+2) → Site n) (x : ℝ)
    (hu : ∀ j, position rows (u j) = xy x (height rows j)) :
    width rows (Finset.univ.image u) = 1 := by
  have he (j : Fin (n+2)) : xy x (height rows j) ∈ (Finset.univ.image u).map (embedding rows) :=
    Finset.mem_map.mpr ⟨u j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hu _⟩
  have hsub : {xy x 0,xy x 1} ⊆ (Finset.univ.image u).map (embedding rows) := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa only [height_zero] using he 0
    · obtain rfl := Finset.mem_singleton.mp hp
      simpa only [height_top] using he (Fin.last (n+1))
  have hh : (↑((Finset.univ.image u).map (embedding rows)) : Set Plane) ⊆
      convexHull ℝ (↑({xy x 0,xy x 1} : Finset Plane) : Set Plane) := by
    intro p hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hs
    change position rows (u j) ∈ _
    rw [hu]
    exact xy_mem_hull_vpair x (height_nonneg rows _) (height_le_one rows _)
  rw [width_of_hull hδ rows hsub hh, hδ.wire]
  simp
include hδ in
@[simp] theorem width_fiber_zero : width rows (fiber (0 : Fin (n+2))) = 1 := by
  rw [fiber_zero]
  exact width_fiber_of_anchor hδ rows a 0 (position_a rows)

include hδ in
@[simp] theorem width_fiber_one : width rows (fiber (1 : Fin (n+2))) = 1 := by
  rw [fiber_one]
  exact width_fiber_of_anchor hδ rows b (spanX n) (position_b rows)

include hδ in
@[simp] theorem width_singleton (s : Site n) : width rows {s} = 0 := by
  simp [width, hδ.singleton]
include hδ in
theorem width_groups_sum : ∑ g : Fin (n+2), width rows (fiber g) = 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  norm_num [hδ]

include hδ in
theorem deficit_pos :
    0 < width rows (Finset.univ : Finset (Site n)) - ∑ g : Fin (n+2), width rows (fiber g) := by
  rw [width_of_corners hδ rows (Finset.subset_univ _), width_groups_sum hδ rows]
  exact sub_pos.mpr rows.anchorLower
include hδ in
theorem bracket_copy (i : Fin n) :
    width rows (bracket i ∪ {z i}) = width rows (bracket i) := by
  let V := (bracket i).map (embedding rows)
  have hb : (bracket i).Nonempty := Finset.insert_nonempty _ _
  have hV : V.Nonempty := hb.map
  have hV' : V =
      {xy 0 (height rows (interior i)), xy (spanX n) (height rows (interior i))} := by simp [V,bracket]
  have hh : (↑(({z i} : Finset _).map (embedding rows)) : Set Plane) ⊆
      convexHull ℝ (V : Set Plane) := by
    intro p hp
    have hp' : p = position rows (z i) := by simpa using hp
    rw [hp', position_z rows, hV']
    exact xy_mem_hull_hpair _ (offset_pos n).le (offset_lt_spanX n).le
  apply hδ.eq_of_hull (Finset.map_subset_map.mpr Finset.subset_union_left)
  rw [Finset.map_union, Finset.coe_union]
  exact Set.union_subset (subset_convexHull ℝ _) hh
include hδ in
theorem gap_left (i : Fin n) :
    0 < width rows (triA i) + width rows (endsB n) - width rows (triA i ∪ endsB n) := by
  have hh : endsA n ∪ endsB n ⊆ triA i ∪ endsB n :=
    Finset.union_subset_union (Finset.subset_insert _ _) (Finset.Subset.refl _)
  have hupper := width_corners_le hδ rows hh
  rw [width_endsB hδ rows]
  have h := rows.nearTriangle i
  have hn : width rows (triA i) = δ (near n (rows.value i)) := by
    unfold width triA near
    rw [Finset.map_insert, image_endsA, coe_embedding, position_z, height_interior]
    congr 1
    ext p
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hn]
  change 1 + 3 * (offset n)^2 / 16 ≤ δ (near n (rows.value i)) at h
  unfold spanX at hupper
  nlinarith [sq_pos_of_pos (offset_pos n)]

private theorem far_endpoint (y : ℝ) (hy : 0 ≤ y) (hy' : y ≤ 1) :
    ∃ t ∈ ({0,1} : Finset ℝ), spanX n < dist (xy (spanX n) t) (xy (offset n) y) := by
  have hbase : (spanX n)^2 < (spanX n - offset n)^2 + (1 / 2 : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (spanX_lt_two n).le) (offset_pos n).le,
      offset_le n, sq_nonneg (offset n)]
  by_cases h : y ≤ 1/2
  · refine ⟨1, by simp, ?_⟩
    rw [dist_xy]
    apply Real.lt_sqrt_of_sq_lt
    have hh : (1 / 2 : ℝ) ≤ 1 - y := by linarith
    have hsq : (1 / 2 : ℝ)^2 ≤ (1 - y)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr hh
    linarith
  · refine ⟨0, by simp, ?_⟩
    rw [dist_xy, zero_sub, neg_sq]
    apply Real.lt_sqrt_of_sq_lt
    have hh : (1 / 2 : ℝ) ≤ y := le_of_lt (lt_of_not_ge h)
    have hsq : (1 / 2 : ℝ)^2 ≤ y^2 := (sq_le_sq₀ (by norm_num) hy).mpr hh
    linarith

include hδ in
theorem gap_right (i : Fin n) :
    0 < width rows (triB i) + width rows (endsA n) - width rows (triB i ∪ endsA n) := by
  have hh : endsA n ∪ endsB n ⊆ triB i ∪ endsA n := by
    rw [Finset.union_comm]
    exact Finset.union_subset_union (Finset.subset_insert _ _) (Finset.Subset.refl _)
  have hupper := width_corners_le hδ rows hh
  rw [width_endsA hδ rows]
  obtain ⟨t, ht, hf⟩ := far_endpoint (n := n) (rows.value i) (rows.pos i).le (rows.lt_one i).le
  have hs : {xy (spanX n) t, xy (offset n) (rows.value i)} ⊆ (triB i).map (embedding rows) := by
    simp only [triB, Finset.map_insert, image_endsB, coe_embedding, position_z, height_interior,
      Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton]
    rcases Finset.mem_insert.mp ht with rfl | he
    · simp
    · obtain rfl := Finset.mem_singleton.mp he
      simp
  have hg := hδ.monotone hs
  rw [hδ.wire] at hg
  dsimp only [width] at hupper ⊢
  linarith
include hδ in
theorem gap_satellites {i j : Fin n} (hij : i < j) :
    0 < width rows (satPair i j) + width rows (matchPair i j) -
      width rows (satPair i j ∪ matchPair i j) := by
  have hrect : (satPair i j ∪ matchPair i j).map (embedding rows) =
      rectangle (offset n) 0 (height rows (interior i)) (height rows (interior j)) := by
    ext p
    simp only [satPair,matchPair,rectangle,Finset.map_union,Finset.map_insert,Finset.map_singleton,
      coe_embedding,position_z,position_a,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  rw [width, width, width, hrect]
  have hupper := price_rectangle hδ (offset n) 0
    (height rows (interior i)) (height rows (interior j))
  simp only [sub_zero, abs_of_pos (offset_pos n), height_interior] at hupper
  simp only [satPair,matchPair,Finset.map_insert,Finset.map_singleton,
    coe_embedding,position_z,position_a,hδ.wire,dist_xy_vert,
    sub_zero,abs_of_pos (offset_pos n)]
  simp only [height_interior]
  linarith [rows.separated (ne_of_lt hij)]
end Placement
end Sunflower
end Combinatorics
end OAI
end

/- Ported from Combinatorics/Sunflower/PlanarInput.lean -/
section
/- # A single complex spectral point for a finite planar placement -/

namespace OAI
namespace Combinatorics
namespace Sunflower

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open Planar
open scoped Classical

/-- The restriction of the common-label price to each finite placement is
the scaled evaluation at a single normalized tensor spectral point. -/
private def RealizesPlanarPrice (δ : Finset Plane → ℝ) : Prop :=
  ∀ {I : Type} [Fintype I] [Nontrivial I] (x : I ↪ Plane),
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop),
      ∃ c : ℝ, 0 ≤ c ∧ ∀ S : Finset I, S.Nonempty →
        δ (S.map x) = c * maskDiagonalPrice φ 1 S

private def translateEmbedding (t : Plane) : Plane ↪ Plane := ⟨fun x => x + t, fun _ _ => add_right_cancel⟩

private theorem shift_dist (t a b : Plane) : dist (translateEmbedding t a) (translateEmbedding t b) = dist a b :=
  dist_add_right _ _ _

private theorem Planar.PlanarPriceLaws.shift {δ : Finset Plane → ℝ} (hδ : PlanarPriceLaws δ)
    (t : Plane) : PlanarPriceLaws (fun S => δ (S.map (translateEmbedding t))) := by
  refine ⟨fun _ _ h => hδ.monotone (Finset.map_subset_map.mpr h), ?_, ?_, ?_⟩
  · intro A B h
    have hi : (A.map (translateEmbedding t) ∩ B.map (translateEmbedding t)).Nonempty := by
      rw [← Finset.map_inter]
      exact h.map
    have hsub := hδ.submodular _ _ hi
    simpa only [Finset.map_union, Finset.map_inter] using hsub
  · intro a b
    simpa only [Finset.map_insert, Finset.map_singleton, shift_dist] using
      hδ.wire (translateEmbedding t a) (translateEmbedding t b)
  · intro a b c
    simpa only [Finset.map_insert, Finset.map_singleton, shift_dist] using
      hδ.triangle_le (translateEmbedding t a) (translateEmbedding t b) (translateEmbedding t c)

private theorem RealizesPlanarPrice.shift {δ : Finset Plane → ℝ}
    (h : RealizesPlanarPrice δ) (t : Plane) : RealizesPlanarPrice (fun S => δ (S.map (translateEmbedding t))) := by
  intro I _ _ x
  obtain ⟨φ, c, hc, hφ⟩ := h (x.trans (translateEmbedding t))
  exact ⟨φ, c, hc, fun S hS => by simpa only [Finset.map_map] using hφ S hS⟩

namespace Placement

private theorem exists_translated_rows {δ : Finset Plane → ℝ} (hδ : PlanarPriceLaws δ)
    (n : ℕ) : ∃ t : Plane, Nonempty (Rows (fun A => δ (A.map (translateEmbedding t))) n) := by
  let u := xy 0 1
  let v : Option (Fin n) → Plane
    | none => xy (spanX n) 0
    | some i => xy (offset n) (choiceHeight i)
  let ε := (offset n)^2 / 16
  have hε : 0 < ε := by dsimp [ε]; positivity [offset_pos n]
  obtain ⟨j, hj⟩ := hδ.simultaneous_par_lower u v hε
  let t := (j : ℝ) • u
  refine ⟨t, ⟨⟨choiceHeight, choiceHeight_pos, choiceHeight_lt_one,
    fun _ _ h => choiceHeight_separated h, ?_, ?_⟩⟩⟩
  · intro i
    have hi := hj (some i)
    have h := hδ.triangle_lower t u (v (some i)) hi
    have he : (near n (choiceHeight i)).map (translateEmbedding t) = {t, t + u, t + v (some i)} := by
      have hz : xy 0 0 = (0 : Plane) := by ext k; fin_cases k <;> rfl
      simp only [near, Finset.map_insert, Finset.map_singleton, hz]
      change {0+t, u+t, v (some i)+t} = _
      simp [add_comm]
    have hs : 1 + (offset n)^2/4 ≤
        (dist (xy 0 0) (xy 0 1) + dist (xy 0 1) (xy (offset n) (choiceHeight i)) +
          dist (xy (offset n) (choiceHeight i)) (xy 0 0)) / 2 :=
      semiperimeter_vertical_lower (choiceHeight_pos i).le (choiceHeight_lt_one i).le
        (offset_pos n).le (by linarith [offset_le n])
        (by simpa using le_abs_self (offset n))
    have h₁ : translateEmbedding t (xy 0 0) = t := by
      have hz : xy 0 0 = (0 : Plane) := by ext k; fin_cases k <;> rfl
      change xy 0 0 + t = _
      rw [hz, zero_add]
    have h₂ : translateEmbedding t (xy 0 1) = t + u := add_comm _ _
    have h₃ : translateEmbedding t (xy (offset n) (choiceHeight i)) = t + v (some i) := add_comm _ _
    have hh := shift_dist t (xy 0 0) (xy 0 1)
    have hg := shift_dist t (xy 0 1) (xy (offset n) (choiceHeight i))
    have hk := shift_dist t (xy (offset n) (choiceHeight i)) (xy 0 0)
    rw [h₁, h₂] at hh
    rw [h₂, h₃] at hg
    rw [h₃, h₁] at hk
    rw [hh, hg, hk, ← he] at h
    change _ ≤ δ ((near n (choiceHeight i)).map (translateEmbedding t))
    dsimp [ε] at h
    linarith
  · have hi := hj none
    have he : (rectangle 0 (spanX n) 0 1).map (translateEmbedding t) = PlanarPriceLaws.par t u (v none) := by
      have hz : xy 0 0 = (0 : Plane) := by ext k; fin_cases k <;> rfl
      have huv : u + v none = xy (spanX n) 1 := by simp [u, v, xy_add]
      simp only [rectangle, Finset.map_insert, Finset.map_singleton, hz, PlanarPriceLaws.par]
      change {0+t, u+t, v none+t, xy (spanX n) 1+t} = _
      rw [← huv]
      simp only [add_zero, add_assoc t, add_comm _ t]
    have hu : ‖u‖ = 1 := by
      rw [← dist_zero_right, show (0 : Plane) = xy 0 0 by ext k; fin_cases k <;> rfl]
      simp [u]
    have hv : ‖v none‖ = spanX n := by
      rw [← dist_zero_right, show (0 : Plane) = xy 0 0 by ext k; fin_cases k <;> rfl]
      simp [v, abs_of_pos ((zero_lt_one : (0 : ℝ) < 1).trans (one_lt_spanX n))]
    change 2 < δ ((rectangle 0 (spanX n) 0 1).map (translateEmbedding t))
    rw [he]
    rw [hu, hv] at hi
    have hh : 2 < 1 + spanX n - ε := by
      dsimp [spanX, ε]
      nlinarith [sq_pos_of_pos (offset_pos n)]
    exact hh.trans_le hi

end Placement

private def PlanarRealization : Prop :=
  ∃ δ : Finset Plane → ℝ, PlanarPriceLaws δ ∧ RealizesPlanarPrice δ
end Sunflower
end Combinatorics
end OAI
end

/- Ported from Combinatorics/Sunflower/Binary.lean -/
section
/- # Pair names for the binary equality filter

For a nonzero direction, eliminate one pivot coordinate by adding a multiple of the
direction. Deleting this coordinate then names the coset of the two-element subgroup.
-/

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Binary

private abbrev Word (b : ℕ) := Fin b → ZMod 2
private abbrev Direction (b : ℕ) := {p : Word b // p ≠ 0}
@[simp] theorem card_word (b : ℕ) : Fintype.card (Word b) = 2 ^ b := by
  simp [Word, ZMod.card]

@[simp] theorem card_direction (b : ℕ) : Fintype.card (Direction b) = 2 ^ b - 1 := by
  classical
  rw [show Fintype.card (Direction b) = _ from Fintype.card_subtype_compl (· = (0 : Word b))]
  simp

private instance {b : ℕ} : Nonempty (Direction (b + 1)) :=
  ⟨⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0)⟩⟩
private theorem has_pivot {b : ℕ} (p : Direction b) : ∃ i, p.val i = 1 := by
  by_contra! h
  exact p.property (funext fun i =>
    (show ∀ a : ZMod 2, a ≠ 1 → a = 0 by decide) _ (h i))

private noncomputable def pivot {b : ℕ} (p : Direction b) : Fin b :=
  Classical.choose (has_pivot p)

@[simp] theorem pivot_bit {b : ℕ} (p : Direction b) : p.val (pivot p) = 1 :=
  Classical.choose_spec (has_pivot p)
/-- The smaller alphabet names each unordered pair in direction `p`. -/
private noncomputable def pairName {b : ℕ} (p : Direction (b + 1)) (x : Word (b + 1)) : Word b :=
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
private def difference {b : ℕ} (x y : Word b) (h : x ≠ y) : Direction b :=
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

/- Ported from Combinatorics/Sunflower/CorrectionSpec.lean -/
section
/- # Local maps for correcting the binary equality test -/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

noncomputable section

open Binary Control

variable {I : Type*} [Fintype I]
/-- The correction block emits the shared difference when the promised labels disagree. -/
private def CorrectionMaps (P T : Finset I) (b : ℕ) (U V : Raw.{0} I ℂ) : Prop :=
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

/- Ported from Combinatorics/Sunflower/Filter.lean -/
section
/- # One recursive step of the binary equality filter

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
private def EqualityMaps (P T : Finset I) (A : Type) (R Q : Raw.{0} I ℂ) : Prop :=
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

/- Ported from LinearAlgebra/SpectralBooks/PlacedSpectralWires.lean -/
section
/- # Matrix multiplication wires at an injective placement

All three edge prices and the full diagonal price are evaluated at the same
three-site spectral point. This converts the binary metric-price law of a
spectral space into wire evaluations in every positive dimension.
-/
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks


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
end
end
end SpectralBooks
end LinearAlgebra
end OAI
end

/- Ported from Combinatorics/Sunflower/Prices.lean -/
section
/- # Diagonal prices and the equality-filter cost recurrence -/

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
private abbrev spectralValue (X : Raw.{0} I F) : ℝ := (φ.val (ofRaw X) : ℝ)

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

/- Ported from Combinatorics/Sunflower/Summability.lean -/
section
/- # Summing the costs of recursive equality tests -/

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

/- Ported from Combinatorics/Sunflower/Alphabet.lean -/
section
/- # Transporting an arbitrary finite alphabet to binary words -/

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {I α β : Type*}

/-- Relabel all coordinates of a word by the same alphabet embedding. -/
private def wordEmbedding (e : α ↪ β) : (I → α) ↪ (I → β) where
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
private def Binary.alphabetEmbedding (n : ℕ) : Fin n ↪ Binary.Word n where
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

/- Ported from Combinatorics/Sunflower/FilterBound.lean -/
section
/- # A uniform price for testing equality

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

/- Ported from Combinatorics/Sunflower/Fourier.lean -/
section
/- # Character matrices for a shared-label resource

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
private def fourierMatrix (K : Finset I) (i₀ : I) (phase : ∀ i, C i → B i → Γ)
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

/- Ported from Combinatorics/Sunflower/BroadcastCode.lean -/
section
/- # Finite codes for broadcasting a common label -/

namespace OAI
namespace Combinatorics
namespace Sunflower
/-- A code for broadcasting a shared label. Each control point lies on the same
sphere. For a fixed control point the source indices lie on another sphere,
in a hyperplane perpendicular to that control. -/
private structure BroadcastCode (m q N : ℕ) where
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

/- Ported from Combinatorics/Sunflower/BroadcastParameters.lean -/
section
/-
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
private def dim (h : ℕ) : ℕ := h + 6

/-- Bit depth of each coordinate. -/
private def depth (h b : ℕ) : ℕ := b / h + dim h + 2

private def side (h b : ℕ) : ℕ := 2 ^ depth h b

/-- Every coordinate of either side of the broadcast relation lies below this modulus. -/
private def modulus (h b sites : ℕ) : ℕ := 2 ^ (depth h b + sites)

private def bits (h b sites : ℕ) : ℕ := (depth h b + sites) * dim h
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

/- Ported from Combinatorics/Sunflower/Rigidity.lean -/
section
/- Rigidity of the integer relation used to broadcast a shared label. -/
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

/- Ported from Combinatorics/Sunflower/Broadcast.lean -/
section
/- # Controlled broadcasting by character orthogonality -/

namespace OAI
namespace Combinatorics
namespace Sunflower
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators Classical

noncomputable section

variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]
/-- A restriction controlled at its source sites that reproduces the common
source label at the target sites while returning a fixed resource. -/
private def Broadcasts (P T : Finset I) (A : Type) (R Q : Raw.{0} I ℂ) : Prop :=
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
private def broadcastOverhead (sites h : ℕ) : ℝ :=
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

/- Ported from Combinatorics/Sunflower/Correction.lean -/
section
/- The error correction in one equality-test step. A row of the output contains
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

/- Ported from Combinatorics/Sunflower/PositiveFilter.lean -/
section
/- # Alphabet-uniform filtering at a positive diagonal gap -/

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

/- Ported from Combinatorics/Sunflower/Placement/Rules.lean -/
section
/- The finite planar placement realizes the geometric condition for every anchor rule
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
open Planar

theorem exists_rule_sites {δ : Finset Plane → ℝ} (hδ : PlanarPriceLaws δ) (rows : Rows δ n) (q : Rule (Fin (n + 2))) (hq : q ∈ anchorRules 0 1) :
    ∃ d : RuleSites q, d.Works (width rows) := by
  apply anchorRules_fin_cases (P := fun q => ∃ d : RuleSites q, d.Works (width rows)) _ _ _ _ hq
  · intro i
    refine ⟨⟨{a (interior i)}, {b (interior i)}, {z i}, by simp, by simp, by simp,
        by simp, by simp, by simp⟩, Or.inr ⟨z i, rfl, ?_⟩⟩
    change width rows (insert (z i) ({a (interior i)} ∪ {b (interior i)})) =
      width rows ({a (interior i)} ∪ {b (interior i)})
    rw [Finset.singleton_union]
    simpa only [bracket, Finset.union_singleton] using bracket_copy hδ rows i
  · intro i
    refine ⟨⟨endsA n, {z i}, endsB n, by simp [endsA], by simp, by simp [endsB],
        endsA_subset_fiber n, by simp, endsB_subset_fiber n⟩, Or.inl ?_⟩
    simpa [triA, Finset.union_singleton] using gap_left hδ rows i
  · intro i
    refine ⟨⟨endsB n, {z i}, endsA n, by simp [endsB], by simp, by simp [endsA],
        endsB_subset_fiber n, by simp, endsA_subset_fiber n⟩, Or.inl ?_⟩
    simpa [triB, Finset.union_singleton] using gap_right hδ rows i
  · intro i j hij
    refine ⟨⟨{z i}, {z j}, matchPair i j, by simp, by simp, by simp [matchPair],
        by simp, by simp, by simp [matchPair, Finset.insert_subset_iff]⟩, Or.inl ?_⟩
    simpa [satPair] using gap_satellites hδ rows hij
/-- A fixed complex point and placement for the `n+2` groups, chosen before the
alphabet or word length. -/
private theorem exists_priced_placement_rows {δ : Finset Plane → ℝ} (hδ : PlanarPriceLaws δ)
    (hFinite : RealizesPlanarPrice δ) (rows : Rows δ n) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Site n) ℂ → _ → Prop),
      0 < 1 - ∑ g : Fin (n + 2), maskDiagonalPrice φ 1 (fiber g) ∧
      ∀ q ∈ anchorRules (0 : Fin (n + 2)) 1,
        ∃ d : RuleSites q, d.Works (maskDiagonalPrice φ 1) := by
  classical
  let : Nontrivial (Site n) := ⟨⟨a 0, b 0, by simp [a, b]⟩⟩
  obtain ⟨φ, c, _, hφ⟩ := hFinite (embedding rows)
  let D := width rows (Finset.univ : Finset (Site n))
  have hD' : 0 < D := by
    dsimp only [D]
    rw [width_of_corners hδ rows (Finset.subset_univ _)]
    exact (by norm_num : (0 : ℝ) < 2).trans rows.anchorLower
  have hD : c = D := by
    have h := hφ Finset.univ Finset.univ_nonempty
    rw [maskDiagonalPrice_univ, mul_one] at h
    exact h.symm
  have price (s : Finset (Site n)) (hs : s.Nonempty) :
      maskDiagonalPrice φ 1 s = width rows s / D := by
    rw [eq_div_iff hD'.ne', mul_comm, ← hD]
    exact (hφ s hs).symm
  refine ⟨φ, ?_, ?_⟩
  · simp_rw [fun g => price (fiber g) (fiber_nonempty g)]
    rw [← Finset.sum_div, sub_pos, div_lt_one hD']
    exact sub_pos.mp (deficit_pos hδ rows)
  · intro q hq
    obtain ⟨d, hd⟩ := exists_rule_sites hδ rows q hq
    exact ⟨d, d.works_normalize hD' price hd⟩
/-- Choose a common orientation before evaluating the rule filters. -/
theorem exists_priced_placement (hplanar : PlanarRealization) (n : ℕ) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Site n) ℂ → _ → Prop),
      0 < 1 - ∑ g : Fin (n + 2), maskDiagonalPrice φ 1 (fiber g) ∧
        ∀ q ∈ anchorRules (0 : Fin (n + 2)) 1,
          ∃ d : RuleSites q, d.Works (maskDiagonalPrice φ 1) := by
  obtain ⟨δ, hδ, hFinite⟩ := hplanar
  obtain ⟨t, ⟨rows⟩⟩ := exists_translated_rows hδ n
  exact exists_priced_placement_rows (hδ.shift t) (hFinite.shift t) rows

end Placement
end Sunflower
end Combinatorics
end OAI
end

/- Ported from Combinatorics/Sunflower/RuleDevices.lean -/
section
/- # Uniform controlled tests for the planar anchor rules

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
private def UniformRule (q : Rule (Fin (n+2))) : Prop :=
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
theorem exists_devices (hplanar : PlanarRealization) (n : ℕ) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Site n) ℂ → _ → Prop),
      0 < 1 - ∑ g, maskDiagonalPrice φ 1 (Placement.fiber g) ∧
        ∀ q ∈ anchorRules (0 : Fin (n+2)) 1, UniformRule φ q := by
  obtain ⟨φ, hdef, hgeo⟩ := exists_priced_placement hplanar n
  refine ⟨φ, hdef, fun q hq => ?_⟩
  obtain ⟨d, hw⟩ := hgeo q hq
  exact exists_rule_device φ hq d hw
end

end RuleDevices
end Sunflower
end Combinatorics
end OAI
end

namespace OAI.Combinatorics.Sunflower

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

end OAI.Combinatorics.Sunflower

/- Ported from Combinatorics/Sunflower/FixedBase.lean -/
section
/- # The fixed-base Erdős–Rado sunflower theorem -/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower
/-- For each number of petals, the planar configuration gives one base for all
word lengths and all finite alphabets. -/
theorem wordBound_of_planarRealization (hplanar : PlanarRealization) (r : ℕ) (hr : 3 ≤ r) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (k m : ℕ) (W : Finset (Fin k → Fin m)),
      WordFree r W → W.card ≤ D ^ k := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  obtain ⟨φ, hgap, htests⟩ := RuleDevices.exists_devices hplanar n
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

/- The shared-label increment argument adapts IntersectingSubmodularity.lean
and IncrementRestriction.lean of the same revision. Over the complex field,
the Fourier contraction and interpolation give the needed spectral comparison
directly. -/

namespace OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical BigOperators NNReal
open OAI.Combinatorics.Sunflower

noncomputable section

variable {I : Type} [Fintype I] [Nonempty I]

private abbrev parallelPower (T : Raw.{0} I ℂ) (n : ℕ) : Raw.{0} I ℂ :=
  ⟨fun i => Fin n → T.Leg i, fun _ => inferInstance,
    fun x => ∏ j, T.coeff (fun i => x i j)⟩

private theorem parallelPower_class (T : Raw.{0} I ℂ) (n : ℕ) :
    ofRaw (parallelPower T n) = ofRaw T ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, ← ofRaw_one]
    apply ofRaw_eq_iff.mpr
    exact Raw.reindex_equivalent (fun _ => ⟨fun _ => PUnit.unit, fun _ j => j.elim0, fun f => funext fun j => j.elim0, fun x => by cases x; rfl⟩) (fun _ => by
      simp [parallelPower, Raw.one])
  | succ n ih =>
    rw [pow_succ', ← ih, ← ofRaw_mul]
    apply ofRaw_eq_iff.mpr
    refine Raw.reindex_equivalent (fun i => (Fin.consEquiv (fun _ : Fin (n+1) => T.Leg i)).symm) ?_
    intro x
    exact Fin.prod_univ_succ _

omit [Nonempty I] in
private theorem parallelPower_restricts {X Y : Raw.{0} I ℂ} (h : X.Restricts Y) (n : ℕ) :
    (parallelPower X n).Restricts (parallelPower Y n) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨fun i x y => ∏ j, M i (x j) (y j), fun x => ?_⟩
  change (∏ j : Fin n, X.coeff (fun i => x i j)) =
    ∑ y : (i : I) → Fin n → Y.Leg i,
      (∏ j : Fin n, Y.coeff (fun i => y i j)) * ∏ i, ∏ j : Fin n, M i (x i j) (y i j)
  simp_rw [hM]
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (Equiv.piComm (fun (_ : Fin n) (i : I) => Y.Leg i))
  intro v
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  rfl

private abbrev withCoeff (T : Raw.{0} I ℂ) (c : ((i : I) → T.Leg i) → ℂ) : Raw.{0} I ℂ :=
  ⟨T.Leg, T.finiteLeg, c⟩

private theorem withCoeff_smul_restrict {X Y : Raw.{0} I ℂ}
    (h : X.Restricts Y) (a : ℂ) : (withCoeff X (a • X.coeff)).Restricts Y := by
  obtain ⟨M, hM⟩ := h
  let i₀ := Classical.arbitrary I
  refine ⟨fun i b c => (if i = i₀ then a else 1) * M i b c, fun x => ?_⟩
  change a * X.coeff x =
    contract (fun i b c => (if i = i₀ then a else 1) * M i b c) Y.coeff x
  rw [contract_scaleAt]
  exact congrArg (a * ·) (hM x)

omit [Nonempty I] in
private theorem withCoeff_add_restrict (X : Raw.{0} I ℂ)
    (a b : ((i : I) → X.Leg i) → ℂ) :
    (withCoeff X (a + b)).Restricts ((withCoeff X a).add (withCoeff X b)) := by
  let F (i : I) : X.Leg i ⊕ X.Leg i → X.Leg i := Sum.elim id id
  refine ⟨fun i j t => if F i t = j then 1 else 0, fun x => ?_⟩
  change a x + b x = ∑ t : (i : I) → X.Leg i ⊕ X.Leg i,
    sumCoeff a b t * ∏ i, if F i (t i) = x i then 1 else 0
  simp_rw [Fintype.prod_boole, ← funext_iff]
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib]
  rw [sum_pushCoeff_mul, sum_pushCoeff_mul]
  change a x + b x = (∑ v, a v * (if v = x then 1 else 0)) +
    (∑ v, b v * (if v = x then 1 else 0))
  simp [mul_ite]

private theorem value_withCoeff_sum_le {J : Type} (s : Finset J)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (X Y : Raw.{0} I ℂ) (f : J → ((i : I) → X.Leg i) → ℂ)
    (h : ∀ j ∈ s, (withCoeff X (f j)).Restricts Y) :
    φ.val (ofRaw (withCoeff X (∑ j ∈ s, f j))) ≤ s.card * φ.val (ofRaw Y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : ofRaw (withCoeff X 0) = 0 := (ofRaw_eq_zero_iff _).mpr rfl
    simp [hz, φ.property.1]
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj, Finset.card_insert_of_notMem hj, Nat.cast_add, Nat.cast_one]
    let U := withCoeff X (f j)
    let V := withCoeff X (∑ j ∈ s, f j)
    have ht := φ.property.2.2.2.2 (ofRaw (withCoeff X (f j + ∑ j ∈ s, f j))) (ofRaw (U.add V))
      (withCoeff_add_restrict X (f j) (∑ j ∈ s, f j))
    rw [ofRaw_add, φ.property.2.2.1] at ht
    have hu := φ.property.2.2.2.2 (ofRaw U) (ofRaw Y) (h j (Finset.mem_insert_self _ _))
    rw [add_mul, one_mul]
    exact ht.trans ((add_le_add hu (ih fun z hz => h z (Finset.mem_insert_of_mem hz))).trans_eq
      (add_comm _ _))

/-- Extracting the constant coefficient of a polynomial curve costs only linearly
many direct-sum blocks on each tensor power. -/
private theorem polynomialSpecialization
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (X Y : Raw.{0} I ℂ) (P : ((i : I) → X.Leg i) → Polynomial ℂ) (d : ℕ)
    (hd : ∀ x, (P x).natDegree ≤ d)
    (hzero : ∀ x, (P x).eval 0 = X.coeff x)
    (hval : ∀ t : ℂ, t ≠ 0 → (withCoeff X (fun x => (P x).eval t)).Restricts Y) :
    φ.val (ofRaw X) ≤ φ.val (ofRaw Y) := by
  apply nnreal_le_of_pow_le_polynomial_mul_pow (d + 1)
  intro n hn
  let s : Finset ℕ := Finset.range (n * d + 1)
  let v (j : ℕ) : ℂ := (j : ℂ) + 1
  have hv : Set.InjOn v (↑s : Set ℕ) := fun _ _ _ _ h => by
    exact_mod_cast (add_right_cancel h : (_ : ℂ) = _)
  let c (j : ℕ) := (Lagrange.basis s v j).eval 0
  let f (j : ℕ) (x : (i : I) → (parallelPower X n).Leg i) :=
    c j * ∏ k : Fin n, (P (fun i => x i k)).eval (v j)
  have hsum : (∑ j ∈ s, f j) = (parallelPower X n).coeff := by
    funext x
    let Q : Polynomial ℂ := ∏ k : Fin n, P (fun i => x i k)
    have hQ : Q.natDegree ≤ n * d := by
      calc
        Q.natDegree ≤ ∑ k : Fin n, (P (fun i => x i k)).natDegree :=
          Polynomial.natDegree_prod_le _ _
        _ ≤ n * d := by
          simpa using (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
            (fun k _ => hd (fun i => x i k)))
    have hdeg : Q.degree < s.card := by
      apply (Polynomial.degree_le_natDegree.trans_lt _)
      exact_mod_cast (show Q.natDegree < s.card by simpa [s] using Nat.lt_succ_of_le hQ)
    have hQeval := congrArg (Polynomial.eval 0) (Lagrange.eq_interpolate hv hdeg)
    simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Q, Polynomial.eval_prod, hzero] at hQeval
    rw [Finset.sum_apply]
    simpa only [f, c, mul_comm] using hQeval.symm
  have hterms : ∀ j ∈ s, (withCoeff (parallelPower X n) (f j)).Restricts (parallelPower Y n) := by
    intro j _
    have hj : v j ≠ 0 := by
      dsimp [v]
      exact_mod_cast Nat.succ_ne_zero j
    exact withCoeff_smul_restrict (parallelPower_restricts (hval (v j) hj) n) (c j)
  have h := value_withCoeff_sum_le s φ _ _ f hterms
  rw [hsum] at h
  change φ.val (ofRaw (parallelPower X n)) ≤ s.card * φ.val (ofRaw (parallelPower Y n)) at h
  rw [parallelPower_class, parallelPower_class] at h
  let F := normalizedSpectrum.toRingHom φ
  change F (ofRaw X ^ n) ≤ s.card * F (ofRaw Y ^ n) at h
  rw [map_pow, map_pow] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  have hlinear (j : ℕ) : n * j + 1 ≤ (n + 1) ^ (j + 1) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      calc
        n * (j + 1) + 1 = (n * j + 1) + n := by ring
        _ ≤ (n * j + 1) + (n * j + 1) * n := by
          apply Nat.add_le_add_left
          have hj : 1 ≤ n * j + 1 := by omega
          simpa only [one_mul] using Nat.mul_le_mul_right n hj
        _ = (n * j + 1) * (n + 1) := by ring
        _ ≤ (n + 1) ^ (j + 1) * (n + 1) := Nat.mul_le_mul_right _ ih
  simpa only [s, Finset.card_range, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    (show ((n * d + 1 : ℕ) : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) ^ (d + 1) by exact_mod_cast hlinear d)

end
end OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical BigOperators NNReal
open Finset

noncomputable section

variable {I : Type} [Fintype I]

private def overlapWeight (T : Finset I) (y i : I) : ℤ :=
  if i = y then -(T.erase y).card else 1

omit [Fintype I] in
private theorem overlap_sum (T : Finset I) {y : I} (hy : y ∈ T) (u : I → ℤ) :
    ∑ i ∈ T, overlapWeight T y i * u i =
      (∑ i ∈ T.erase y, u i) - (T.erase y).card * u y := by
  rw [← Finset.sum_erase_add _ _ hy]
  rw [show (∑ i ∈ T.erase y, overlapWeight T y i * u i) = ∑ i ∈ T.erase y, u i by
    apply Finset.sum_congr rfl
    intro i hi
    simp [overlapWeight, (Finset.mem_erase.mp hi).1]]
  simp [overlapWeight, sub_eq_add_neg]

private def overlapPenalty (T : Finset I) (N : ℕ) (y : I) (a b : ℤ) (u : I → ℤ) : ℤ :=
  ((T.erase y).card * (N : ℤ)^2 + 1) *
      (b^2 - a^2 + 2*a*(∑ i ∈ T, overlapWeight T y i * u i)) +
    ∑ i ∈ T, overlapWeight T y i * u i^2

/-- The phase equation makes the leading part a square. Once that square
vanishes, the rest is the sum of squared deviations from the reference label. -/
private theorem overlapPenalty_spec (T : Finset I) {y : I} (hy : y ∈ T)
    (N : ℕ) (a b : ℤ) (u : I → ℤ) (hu : 0 ≤ u y ∧ u y < N)
    (hphase : b - a + (∑ i ∈ T, overlapWeight T y i * u i) = 0) :
    0 ≤ overlapPenalty T N y a b u ∧
      (overlapPenalty T N y a b u = 0 ↔ b = a ∧ ∀ i ∈ T, u i = u y) := by
  let E := T.erase y
  let R : ℤ := E.card
  let L : ℤ := R * (N : ℤ)^2 + 1
  let Q : ℤ := (∑ i ∈ E, u i^2) - R * u y^2
  have hR : 0 ≤ R := by positivity
  have hL : 0 < L := by positivity
  have hP : overlapPenalty T N y a b u = L * (b-a)^2 + Q := by
    unfold overlapPenalty
    rw [overlap_sum T hy (fun i => u i^2)]
    have hlin : (∑ i ∈ T, overlapWeight T y i * u i) = a - b := by linarith
    rw [hlin]
    dsimp [L, Q, R, E]
    ring
  have hQ : -R*(N : ℤ)^2 ≤ Q := by
    have hsq : u y ^ 2 ≤ (N : ℤ)^2 := by nlinarith [hu.1, hu.2]
    have hsum : 0 ≤ ∑ i ∈ E, u i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    dsimp [Q]
    linarith [mul_le_mul_of_nonneg_left hsq hR]
  by_cases hba : b = a
  · have hsum : (∑ i ∈ E, u i) = R * u y := by
      rw [overlap_sum T hy, hba, sub_self, zero_add, sub_eq_zero] at hphase
      exact hphase
    have hvar : Q = ∑ i ∈ E, (u i - u y)^2 := by
      have hid (i : I) : (u i - u y)^2 = u i^2 - 2*u y*u i + u y^2 := by ring
      simp_rw [hid, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      dsimp [Q, R]
      ring
    have hP' : overlapPenalty T N y a b u = ∑ i ∈ E, (u i - u y)^2 := by
      rw [hP, hba, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, hvar]
    rw [hP']
    refine ⟨Finset.sum_nonneg fun _ _ => sq_nonneg _, ?_⟩
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (u i - u y))]
    simp only [hba, true_and, pow_eq_zero_iff (by decide : 2 ≠ 0), sub_eq_zero]
    constructor
    · intro h i hi
      by_cases hiy : i = y
      · simp [hiy]
      · exact h i (Finset.mem_erase.mpr ⟨hiy, hi⟩)
    · exact fun h i hi => h i (Finset.mem_of_mem_erase hi)
  · have hs : 1 ≤ (b-a)^2 := by
      have : (b-a)^2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hba)
      have := sq_nonneg (b-a)
      omega
    have hp : 0 < overlapPenalty T N y a b u := by
      rw [hP]
      have := mul_le_mul_of_nonneg_left hs hL.le
      dsimp [L] at this
      linarith
    simp [hp.le, hp.ne', hba]

end
end OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical BigOperators NNReal
open Finset
open OAI.Combinatorics.Sunflower

noncomputable section

variable {I : Type} [Fintype I] [Nonempty I]

omit [Nonempty I] in
private theorem contract_sharedProduct
    {A B C : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (M : ∀ i, C i → A i → ℂ) (N : ∀ i, C i → B i → ℂ)
    (T : (∀ i, A i) → ℂ) (U : (∀ i, B i) → ℂ) (x : ∀ i, C i) :
    contract (fun i c (ab : A i × B i) => M i c ab.1 * N i c ab.2)
        (fun ab => T (fun i => (ab i).1) * U (fun i => (ab i).2)) x =
      contract M T x * contract N U x := by
  exact contract_mul M N T U (fun i => (x i, x i))

private def maskInt {U : Finset I} {N : ℕ} (f : ∀ i, MaskLeg U (Fin N) i) (i : I) : ℤ :=
  if h : i ∈ U then (f i h).val else 0

omit [Fintype I] [Nonempty I] in
private theorem maskInt_range {U : Finset I} {N : ℕ} (hN : 0 < N)
    (f : ∀ i, MaskLeg U (Fin N) i) (i : I) :
    0 ≤ maskInt f i ∧ maskInt f i < N := by
  unfold maskInt
  split
  · exact ⟨Int.natCast_nonneg _, by exact_mod_cast (f i ‹_›).isLt⟩
  · exact ⟨le_rfl, by exact_mod_cast hN⟩

omit [Fintype I] [Nonempty I] in
private theorem maskInt_restrict {S T : Finset I} (h : S ⊆ T) {N : ℕ}
    (f : ∀ i, MaskLeg T (Fin N) i) (i : I) (hi : i ∈ S) :
    maskInt (U := S) (fun j hj => f j (h hj)) i = maskInt f i := by
  simp [maskInt, hi, h hi]

omit [Nonempty I] in
private theorem maskedCoeff_indicator {U : Finset I} {y : I} (hy : y ∈ U) {N : ℕ}
    (f : ∀ i, MaskLeg U (Fin N) i) :
    (Raw.maskDiagonal ℂ U (Fin N)).coeff f =
      if ∀ i ∈ U, maskInt f i = maskInt f y then 1 else 0 := by
  rw [Raw.maskDiagonal_coeff_at _ hy]
  congr 1
  apply propext
  constructor
  · intro h i hi
    simp [maskInt, hi, hy, h i hi]
  · intro h i hi
    apply Fin.ext
    exact_mod_cast (by simpa [maskInt, hi, hy] using h i hi :
      (↑(f i hi).val : ℤ) = (↑(f y hy).val : ℤ))

private def localPhase (T : Finset I) (z y : I) (v u : I → ℤ) (i : I) : ℤ :=
  (if i = z then v i else 0) - (if i = y then v i else 0) +
    if i ∈ T then overlapWeight T y i * u i else 0

private def localExponent (T : Finset I) (N : ℕ) (z y : I) (v u : I → ℤ) (i : I) : ℤ :=
  let L : ℤ := (T.erase y).card * (N : ℤ)^2 + 1
  L * ((if i = z then v i ^ 2 else 0) - (if i = y then v i ^ 2 else 0) +
    if i ∈ T then 2 * v i * (overlapWeight T y i * u i) else 0) +
    if i ∈ T then overlapWeight T y i * u i ^ 2 else 0

omit [Fintype I] [Nonempty I] in
private theorem sum_localPhase (T : Finset I) {z y : I} (hy : y ∈ T) (v u : I → ℤ) :
    ∑ i ∈ insert z T, localPhase T z y v u i =
      v z - v y + ∑ i ∈ T, overlapWeight T y i * u i := by
  simp [localPhase, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.subset_insert _ _), hy]

omit [Nonempty I] in
private theorem sum_localExponent (T : Finset I) (N : ℕ) {z y : I} (v u : I → ℤ)
    (hv : ∀ i ∈ T, v i = v y) :
    ∑ i, localExponent T N z y v u i = overlapPenalty T N y (v y) (v z) u := by
  simp only [localExponent, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_mem, Finset.univ_inter]
  have he : (∑ i ∈ T, 2 * v i * (overlapWeight T y i * u i)) =
      2 * v y * (∑ i ∈ T, overlapWeight T y i * u i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by rw [hv i hi]
  rw [he]
  rfl

omit [Nonempty I] in
private theorem phase_zmod_iff (T : Finset I) {y : I} (hy : y ∈ T)
    {N : ℕ} (hN : 0 < N) (a b : ℤ) (u : I → ℤ)
    (ha : 0 ≤ a ∧ a < N) (hb : 0 ≤ b ∧ b < N) (hu : ∀ i, 0 ≤ u i ∧ u i < N) :
    ((b - a + ∑ i ∈ T, overlapWeight T y i * u i : ℤ) :
      ZMod (2^(T.card+2) * N)) = 0 ↔
      b - a + ∑ i ∈ T, overlapWeight T y i * u i = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨fun h => Int.eq_zero_of_abs_lt_dvd h ?_, fun h => h ▸ dvd_zero _⟩
  have hC : (T.erase y).card + 1 < 2^(T.card+2) := by
    rw [Finset.card_erase_add_one hy]
    exact (show T.card < T.card + 2 by omega).trans Nat.lt_two_pow_self
  have hC' : ((T.erase y).card + 1 : ℤ) < (2 : ℤ) ^ (T.card+2) := by exact_mod_cast hC
  have hN' : 0 < (N : ℤ) := by exact_mod_cast hN
  have hs0 : (0 : ℤ) ≤ ∑ i ∈ T.erase y, u i := Finset.sum_nonneg fun i _ => (hu i).1
  have hs1 : (∑ i ∈ T.erase y, u i) ≤ (T.erase y).card * (N : ℤ) := by
    calc
      _ ≤ ∑ i ∈ T.erase y, (N : ℤ) := Finset.sum_le_sum fun i _ => (hu i).2.le
      _ = _ := by simp
  have hy0 := mul_nonneg (Int.natCast_nonneg (T.erase y).card) (hu y).1
  have hy1 := mul_le_mul_of_nonneg_left (hu y).2.le (Int.natCast_nonneg (T.erase y).card)
  have hmul := mul_lt_mul_of_pos_right hC' hN'
  push_cast
  rw [overlap_sum T hy, abs_lt]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

/-- A Fourier label on the overlap and the new site, followed by polynomial
specialization, adjoins the site and preserves one common label on the overlap. -/
private theorem overlapSpecialization
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (S T : Finset I) (hTS : T ⊆ S) {z y : I} (hy : y ∈ T) {N : ℕ} (hN : 0 < N) :
    let : NeZero (2^(T.card+2) * N) := ⟨by positivity⟩
    let L := AddChar (ZMod (2^(T.card+2) * N)) ℂ
    φ.val (ofRaw ((Raw.maskDiagonal ℂ (insert z S) (Fin N)).mul (Raw.maskDiagonal ℂ T (Fin N)))) ≤
      φ.val (ofRaw ((Raw.maskDiagonal ℂ S (Fin N)).mul (Raw.maskDiagonal ℂ (insert z T) L))) := by
  classical
  let K := insert z T
  let A := Raw.maskDiagonal ℂ (insert z S) (Fin N)
  let B := Raw.maskDiagonal ℂ T (Fin N)
  let C := Raw.maskDiagonal ℂ S (Fin N)
  let : NeZero (2^(T.card+2) * N) := ⟨by positivity⟩
  let Γ := ZMod (2^(T.card+2) * N)
  let E := Raw.maskDiagonal ℂ K (AddChar Γ ℂ)
  let X := A.mul B
  let Y := C.mul E
  change φ.val (ofRaw X) ≤ φ.val (ofRaw Y)
  let V (x : ∀ i, X.Leg i) := maskInt (fun i => (x i).1)
  let U (x : ∀ i, X.Leg i) := maskInt (fun i => (x i).2)
  let F (x : ∀ i, X.Leg i) : ∀ i, C.Leg i := fun i hi => (x i).1 (Finset.mem_insert_of_mem hi)
  let H (x : ∀ i, X.Leg i) : Prop := ∀ i ∈ S, V x i = V x y
  let p (x : ∀ i, X.Leg i) := V x z - V x y + ∑ i ∈ T, overlapWeight T y i * U x i
  let e (x : ∀ i, X.Leg i) := overlapPenalty T N y (V x y) (V x z) (U x)
  let P (x : ∀ i, X.Leg i) : Polynomial ℂ :=
    if H x ∧ p x = 0 then Polynomial.X ^ (e x).toNat else 0
  have hY : y ∈ S := hTS hy
  have hC (x : ∀ i, X.Leg i) : C.coeff (F x) = if H x then 1 else 0 := by
    rw [maskedCoeff_indicator hY]
    have hm (i : I) (hi : i ∈ S) : maskInt (F x) i = V x i := by
      exact maskInt_restrict (Finset.subset_insert z S) (fun i => (x i).1) i hi
    rw [hm _ hY]
    apply if_congr
    · exact (forall_congr' fun i => imp_congr_right fun hi => by rw [hm _ hi])
    · rfl
    · rfl
  have hp (x : ∀ i, X.Leg i) :
      ((p x : ℤ) : Γ) = 0 ↔ p x = 0 :=
    phase_zmod_iff T hy hN _ _ _ (maskInt_range hN _ _) (maskInt_range hN _ _)
      (maskInt_range hN _)
  have hspec (x : ∀ i, X.Leg i) (hx : p x = 0) :
      0 ≤ e x ∧ (e x = 0 ↔ V x z = V x y ∧ ∀ i ∈ T, U x i = U x y) :=
    overlapPenalty_spec T hy N _ _ _ (maskInt_range hN _ _) hx
  let d := Finset.univ.sup (fun x : ∀ i, X.Leg i => (P x).natDegree)
  have hd (x : ∀ i, X.Leg i) : (P x).natDegree ≤ d :=
    Finset.le_sup (f := fun x : ∀ i, X.Leg i => (P x).natDegree) (Finset.mem_univ x)
  apply polynomialSpecialization φ X Y P d hd
  · intro x
    have hA := maskedCoeff_indicator (Finset.mem_insert_of_mem (b := z) hY) (fun i => (x i).1)
    have hB := maskedCoeff_indicator hy (fun i => (x i).2)
    change (P x).eval 0 = A.coeff (fun i => (x i).1) * B.coeff (fun i => (x i).2)
    rw [hA, hB]
    change (P x).eval 0 =
      (if ∀ i ∈ insert z S, V x i = V x y then 1 else 0) *
      (if ∀ i ∈ T, U x i = U x y then 1 else 0)
    simp only [Finset.forall_mem_insert]
    by_cases h : H x
    · by_cases q : p x = 0
      · have hz : (e x).toNat = 0 ↔ e x = 0 := by
          rw [Int.toNat_eq_zero]
          exact ⟨fun he => le_antisymm he (hspec x q).1, fun he => he.le⟩
        simp only [P, h, q, and_self, if_true, Polynomial.eval_pow, Polynomial.eval_X]
        by_cases he : e x = 0
        · obtain ⟨hv, hu⟩ := (hspec x q).2.mp he
          have hOK : V x z = V x y ∧ ∀ i ∈ S, V x i = V x y := ⟨hv, h⟩
          rw [hz.mpr he, pow_zero, if_pos hOK, if_pos hu, one_mul]
        · rw [zero_pow (hz.not.mpr he)]
          by_cases hv : V x z = V x y <;> by_cases hu : ∀ i ∈ T, U x i = U x y
          · exact (he ((hspec x q).2.mpr ⟨hv, hu⟩)).elim
          all_goals simp [hv, hu]
      · have hfalse : ¬(V x z = V x y ∧ ∀ i ∈ T, U x i = U x y) := by
          rintro ⟨hv, hu⟩
          apply q
          change V x z - V x y + _ = 0
          rw [hv, sub_self, zero_add, overlap_sum T hy]
          have hc : (∑ i ∈ T.erase y, U x i) = ∑ _ ∈ T.erase y, U x y :=
            Finset.sum_congr rfl fun i hi => hu i (Finset.mem_of_mem_erase hi)
          rw [hc]
          simp
        by_cases hv : V x z = V x y
        · simp [P, q, h, hv, show ¬(∀ i ∈ T, U x i = U x y) from fun hu => hfalse ⟨hv, hu⟩]
        · simp [P, q, h, hv]
    · simp [P, h, show ¬(∀ i ∈ S, V x i = V x y) from h]
  · intro t ht
    let v₀ (i : I) (x : X.Leg i) : ℤ := if h : i ∈ insert z S then (x.1 h).val else 0
    let u₀ (i : I) (x : X.Leg i) : ℤ := if h : i ∈ T then (x.2 h).val else 0
    let exp (i : I) (x : X.Leg i) := localExponent T N z y (fun _ => v₀ i x) (fun _ => u₀ i x) i
    let phase (i : I) (_ : Unit) (x : X.Leg i) : Γ :=
      (localPhase T z y (fun _ => v₀ i x) (fun _ => u₀ i x) i : ℤ)
    let M (i : I) (x : X.Leg i) (a : C.Leg i) : ℂ :=
      if a = fun hi => x.1 (Finset.mem_insert_of_mem hi) then 1 else 0
    let J (i : I) (x : X.Leg i) (a : E.Leg i) : ℂ := fourierMatrix K y phase i () x a
    refine ⟨fun i x a => (M i x a.1 * J i x a.2) * t ^ exp i x, fun x => ?_⟩
    change (P x).eval t = ∑ a : (i : I) → Y.Leg i, Y.coeff a *
      ∏ i, (M i (x i) (a i).1 * J i (x i) (a i).2) * t ^ exp i (x i)
    simp only [Finset.prod_mul_distrib]
    have hfactor : (∑ a : (i : I) → Y.Leg i, Y.coeff a *
        (((∏ i, M i (x i) (a i).1) * ∏ i, J i (x i) (a i).2) * ∏ i, t ^ exp i (x i))) =
        (∑ a : (i : I) → Y.Leg i, Y.coeff a *
          ((∏ i, M i (x i) (a i).1) * ∏ i, J i (x i) (a i).2)) * (∏ i, t ^ exp i (x i)) := by
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    rw [hfactor]
    have hprod :
        (∑ a : (i : I) → Y.Leg i, Y.coeff a *
          ((∏ i, M i (x i) (a i).1) * ∏ i, J i (x i) (a i).2)) =
          C.coeff (F x) * (if ((p x : ℤ) : Γ) = 0 then 1 else 0) := by
      simp_rw [← Finset.prod_mul_distrib]
      change contract (fun i xx (ab : C.Leg i × E.Leg i) => M i xx ab.1 * J i xx ab.2)
        (fun ab => C.coeff (fun i => (ab i).1) * E.coeff (fun i => (ab i).2)) x = _
      rw [contract_sharedProduct M J C.coeff E.coeff x]
      congr 1
      · unfold contract
        simp only [M, Fintype.prod_boole, mul_ite, mul_one, mul_zero]
        change (∑ a : (i : I) → C.Leg i, if ∀ i, a i = F x i then C.coeff a else 0) = C.coeff (F x)
        have hread (a : (i : I) → C.Leg i) : (∀ i, a i = F x i) ↔ a = F x := funext_iff.symm
        simp [hread]
      · have hphase : (∑ i ∈ K, phase i () (x i)) = (p x : Γ) := by
          change (∑ i ∈ K, (localPhase T z y (V x) (U x) i : Γ)) = _
          rw [← Int.cast_sum, sum_localPhase T hy]
        have hf := fourierMatrix_apply K y phase (fun _ => ()) x
        rw [hphase] at hf
        by_cases hph : (p x : Γ) = 0
        · rw [if_pos hph] at hf ⊢
          exact hf
        · rw [if_neg hph] at hf ⊢
          exact hf
    rw [hprod, hC]
    by_cases hx : H x
    · by_cases hph : p x = 0
      · have hsum : ∑ i, exp i (x i) = e x := by
          change (∑ i, localExponent T N z y (fun _ => v₀ i (x i)) (fun _ => u₀ i (x i)) i) = _
          exact sum_localExponent T N (z := z) (y := y) (V x) (U x) (fun i hi => hx i (hTS hi))
        have hpower (D : Finset I) :
            (∏ i ∈ D, t ^ exp i (x i)) = t ^ (∑ i ∈ D, exp i (x i)) := by
          induction D using Finset.induction_on with
          | empty => simp
          | @insert i D hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ht]
        rw [hpower, hsum, ← Int.toNat_of_nonneg (hspec x hph).1, zpow_natCast]
        simp [P, hx, hph]
      · have hp' : (p x : Γ) ≠ 0 := fun h => hph ((hp x).mp h)
        simp [P, hx, hph, hp']
    · simp [P, hx]

end
end OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical BigOperators NNReal
open Finset OAI.Combinatorics.Sunflower

noncomputable section

variable {I : Type} [Fintype I] [Nonempty I]

private theorem maskDiagonalPrice_increment [de : DecidableEq I]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    {c : ℝ} (hc : 0 ≤ c) {S T : Finset I} (hTS : T ⊆ S) (hT : T.Nonempty) (z : I) :
    maskDiagonalPrice φ c (insert z S) + maskDiagonalPrice φ c T ≤
      maskDiagonalPrice φ c S + maskDiagonalPrice φ c (insert z T) := by
  have hde : de = Classical.decEq I := Subsingleton.elim _ _
  subst de
  obtain ⟨y, hy⟩ := hT
  have hS : S.Nonempty := ⟨y, hTS hy⟩
  have hT : T.Nonempty := ⟨y, hy⟩
  let f := maskDiagonalPrice φ c
  have hscaled (m : ℕ) :
      (f (insert z S) + f T) * (m : ℝ) ≤
        (f S + f (insert z T)) * (m : ℝ) + f (insert z T) * ((T.card : ℝ) + 2) := by
    let N : ℕ := 2 ^ m
    let M : ℕ := 2^(T.card+2) * N
    have hN : 0 < N := by positivity
    have hM : 0 < M := by positivity
    let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
    let : NeZero M := ⟨hM.ne'⟩
    let L := AddChar (ZMod M) ℂ
    let A := Raw.maskDiagonal ℂ (insert z S) (Fin N)
    let B := Raw.maskDiagonal ℂ T (Fin N)
    let C := Raw.maskDiagonal ℂ S (Fin N)
    let E := Raw.maskDiagonal ℂ (insert z T) L
    have hval := overlapSpecialization φ S T hTS (z := z) hy hN
    change φ.val (ofRaw (A.mul B)) ≤ φ.val (ofRaw (C.mul E)) at hval
    have hA := Raw.maskDiagonal_ne_zero (K := ℂ) (insert z S) (Finset.insert_nonempty _ _) (Fin N)
    have hB := Raw.maskDiagonal_ne_zero (K := ℂ) T hT (Fin N)
    have hC := Raw.maskDiagonal_ne_zero (K := ℂ) S hS (Fin N)
    have hE := Raw.maskDiagonal_ne_zero (K := ℂ) (insert z T) (Finset.insert_nonempty _ _) L
    have hpos : (0 : ℝ) < φ.val (ofRaw (A.mul B)) := by
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hA
      obtain ⟨b, hb⟩ := Function.ne_iff.mp hB
      have hne : (A.mul B).coeff ≠ 0 :=
        Function.ne_iff.mpr ⟨fun i => (a i, b i), mul_ne_zero ha hb⟩
      exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ _ hne)
    have hprice : rawLogPrice φ c (A.mul B) ≤ rawLogPrice φ c (C.mul E) := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact Real.logb_le_logb_of_le (by norm_num) hpos (by exact_mod_cast hval)
    rw [rawLogPrice_mul φ c _ _ hA hB, rawLogPrice_mul φ c _ _ hC hE] at hprice
    rw [rawLogPrice_maskDiagonal φ c _ (Finset.insert_nonempty _ _) hN,
      rawLogPrice_maskDiagonal φ c _ hT hN, rawLogPrice_maskDiagonal φ c _ hS hN,
      rawLogPrice_maskDiagonal_card φ c _ (Finset.insert_nonempty _ _) L] at hprice
    have hlogN : Real.logb 2 N = m := by
      simp [N, Real.logb_pow]
    have hlogM : Real.logb 2 (Fintype.card L) = (m : ℝ) + ((T.card : ℝ) + 2) := by
      rw [AddChar.card_eq, ZMod.card]
      simp [M, N, Nat.cast_mul, Nat.cast_pow, Real.logb_mul, Real.logb_pow,
        add_comm]
    rw [hlogN, hlogM] at hprice
    dsimp [f]
    linarith
  by_contra! h
  have hpos : 0 < (f (insert z S) + f T) - (f S + f (insert z T)) := sub_pos.mpr h
  obtain ⟨m, hm⟩ := exists_lt_nsmul hpos (f (insert z T) * ((T.card : ℝ) + 2))
  rw [nsmul_eq_mul] at hm
  have := hscaled m
  linarith

/-- Telescoping diminishing increments gives intersecting submodularity. -/
private theorem maskDiagonalPrice_submodular [DecidableEq I]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    {c : ℝ} (hc : 0 ≤ c) (S T : Finset I) (h : (S ∩ T).Nonempty) :
    maskDiagonalPrice φ c (S ∪ T) + maskDiagonalPrice φ c (S ∩ T) ≤
      maskDiagonalPrice φ c S + maskDiagonalPrice φ c T := by
  let P := S ∩ T
  let f := maskDiagonalPrice φ c
  have hl : P ⊆ S := Finset.inter_subset_left
  have hr : P ⊆ T := Finset.inter_subset_right
  have H (U : Finset I) : f (S ∪ U) + f P ≤ f S + f (P ∪ U) := by
    induction U using Finset.induction_on with
    | empty => simp
    | @insert z U hz ih =>
      have hinc := maskDiagonalPrice_increment φ hc
        (Finset.union_subset_union hl (Finset.Subset.refl U))
        (h.mono (Finset.subset_union_left (s₂ := U))) z
      simp only [Finset.union_insert]
      change f (insert z (S ∪ U)) + f (P ∪ U) ≤
        f (S ∪ U) + f (insert z (P ∪ U)) at hinc
      linarith
  have h' := H T
  rwa [Finset.union_eq_right.mpr hr] at h'

end
end OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI.Combinatorics.Sunflower

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open Planar
open scoped Classical

private theorem RealizesPlanarPrice.sharedPair {δ : Finset Plane → ℝ}
    (h : RealizesPlanarPrice δ) {A B : Finset Plane} {x y : Plane} (hxy : {x,y} ⊆ A ∩ B) :
    δ (A ∪ B) + δ {x,y} ≤ δ A + δ B := by
  let Z := A ∪ B
  let I := {a : Plane // a ∈ Z}
  have hx : x ∈ A ∩ B := hxy (Finset.mem_insert_self _ _)
  have hxZ : x ∈ Z := Finset.mem_union_left _ (Finset.mem_inter.mp hx).1
  by_cases hn : Nontrivial I
  · let : Nontrivial I := hn
    let p : Plane → Prop := (· ∈ Z)
    let e : I ↪ Plane := Function.Embedding.subtype p
    obtain ⟨φ, c, hc, hφ⟩ := h e
    let A' := A.subtype p
    let B' := B.subtype p
    let C' := ({x,y} : Finset Plane).subtype p
    have hC : C' ⊆ A' ∩ B' := by
      intro i hi
      have hh := Finset.mem_inter.mp (hxy (Finset.mem_subtype.mp hi))
      exact Finset.mem_inter.mpr ⟨Finset.mem_subtype.mpr hh.1, Finset.mem_subtype.mpr hh.2⟩
    have hnC : C'.Nonempty := ⟨⟨x, hxZ⟩, Finset.mem_subtype.mpr (Finset.mem_insert_self _ _)⟩
    have hnAB := hnC.mono hC
    have hnA := hnAB.mono Finset.inter_subset_left
    have hnB := hnAB.mono Finset.inter_subset_right
    have hnU := hnA.mono (Finset.subset_union_left (s₂ := B'))
    have hmA : A'.map e = A := Finset.subtype_map_of_mem fun _ ha => Finset.mem_union_left _ ha
    have hmB : B'.map e = B := Finset.subtype_map_of_mem fun _ hb => Finset.mem_union_right _ hb
    have hmC : C'.map e = {x,y} := Finset.subtype_map_of_mem fun _ hi =>
      Finset.mem_union_left _ (Finset.mem_inter.mp (hxy hi)).1
    have hmU : (A' ∪ B').map e = A ∪ B := by rw [Finset.map_union, hmA, hmB]
    rw [← hmU, ← hmC, ← hmA, ← hmB, hφ _ hnU, hφ _ hnC, hφ _ hnA, hφ _ hnB]
    have hsub := maskDiagonalPrice_submodular φ (c := 1) zero_le_one A' B' hnAB
    have hmono := maskDiagonalPrice_mono (c := 1) φ zero_le_one hC
    simp only [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hc
    refine le_trans ?_ hsub
    gcongr
  · have he : ∀ z ∈ Z, z = x := by
      intro z hz
      let : Subsingleton I := not_nontrivial_iff_subsingleton.mp hn
      exact congrArg Subtype.val (Subsingleton.elim (⟨z, hz⟩ : I) ⟨x, hxZ⟩)
    have hsing (S : Finset Plane) (hs : S ⊆ Z) (hm : x ∈ S) : S = {x} := by
      apply Finset.Subset.antisymm
      · intro z hz
        simpa using he z (hs hz)
      · exact Finset.singleton_subset_iff.mpr hm
    rw [show A = {x} from hsing A Finset.subset_union_left (Finset.mem_inter.mp hx).1,
      show B = {x} from hsing B Finset.subset_union_right (Finset.mem_inter.mp hx).2,
      show ({x,y} : Finset Plane) = {x} from hsing _ (hxy.trans
        (Finset.inter_subset_left.trans Finset.subset_union_left)) (Finset.mem_insert_self _ _)]
    simp

end OAI.Combinatorics.Sunflower


namespace OAI.LinearAlgebra.SpectralBooks.SiteTensor

open scoped Classical BigOperators NNReal

noncomputable section

variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]

/-- A 3AP-free family of differences gives an induced diagonal in three wires. -/
private theorem triangle_restriction (a b c : I) (N : ℕ) (D : Finset ℕ)
    (hD : D ⊆ Finset.range N) (hAP : ThreeAPFree (D : Set ℕ)) :
    (Raw.maskDiagonal ℂ {a,b,c} (Fin N × D)).Restricts
      (((Raw.maskDiagonal ℂ {a,b} (Fin (3*N))).mul
        (Raw.maskDiagonal ℂ {b,c} (Fin (3*N)))).mul (Raw.maskDiagonal ℂ {c,a} (Fin (3*N)))) := by
  let S : Finset I := {a,b,c}
  let Lab := Fin N × D
  let W := Fin (3*N)
  let first (l : Lab) : W := ⟨l.1.val, by omega⟩
  have hval (l : Lab) : (l.2 : ℕ) < N := Finset.mem_range.mp (hD l.2.property)
  let second (l : Lab) : W := ⟨l.1.val + l.2.val, by have := hval l; omega⟩
  let third (l : Lab) : W := ⟨l.1.val + 2*l.2.val, by have := hval l; omega⟩
  have hAB : ({a,b} : Finset I) ⊆ S := by simp [S]
  have hBC : ({b,c} : Finset I) ⊆ S := by simp [S]
  have hCA : ({c,a} : Finset I) ⊆ S := by simp [S, Finset.insert_subset_iff]
  have ha : a ∈ S := by simp [S]
  have hb : b ∈ S := by simp [S]
  have hc : c ∈ S := by simp [S]
  apply Raw.restrict_by_read
    (fun i (x : MaskLeg S Lab i) =>
      ((fun h => first (x (hAB h)), fun h => second (x (hBC h))),
        fun h => third (x (hCA h))))
  intro x
  change (∀ i, MaskLeg S Lab i) at x
  have read_pair (p q : I) (hpq : ({p,q} : Finset I) ⊆ S) (f : Lab → W) :
      (Raw.maskDiagonal ℂ {p,q} W).coeff (fun i hi => f (x i (hpq hi))) =
        if f (x p (hpq (by simp))) = f (x q (hpq (by simp))) then 1 else 0 := by
    rw [Raw.maskDiagonal_coeff_at _ (Finset.mem_insert_self p _)]
    congr 1
    apply propext
    constructor
    · intro h
      exact (h q (by simp)).symm
    · intro h i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rfl
      · obtain rfl := Finset.mem_singleton.mp hi
        exact h.symm
  have hcoeff :
      ((∀ i (hi : i ∈ S), x i hi = x a ha)) ↔
        first (x a ha) = first (x b hb) ∧ second (x b hb) = second (x c hc) ∧
        third (x c hc) = third (x a ha) := by
    constructor
    · intro h
      rw [h b hb, h c hc]
      exact ⟨rfl,rfl,rfl⟩
    · rintro ⟨he₁,he₂,he₃⟩
      let la := x a ha
      let lb := x b hb
      let lc := x c hc
      have e₁ : la.1.val = lb.1.val := congrArg (fun y : W => y.val) he₁
      have e₂ : lb.1.val + lb.2.val = lc.1.val + lc.2.val := congrArg (fun y : W => y.val) he₂
      have e₃ : lc.1.val + 2*lc.2.val = la.1.val + 2*la.2.val := congrArg (fun y : W => y.val) he₃
      have e : lb.2.val + lc.2.val = la.2.val + la.2.val := by omega
      have hd : lb.2.val = lc.2.val :=
        threeAPFree_iff_eq_right.mp hAP lb.2.property la.2.property lc.2.property e
      have hba : lb = la := Prod.ext (Fin.ext e₁.symm) (Subtype.ext (by omega))
      have hca : lc = la := Prod.ext (Fin.ext (by omega)) (Subtype.ext (by omega))
      intro i hi
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · rfl
      · exact hba
      · exact hca
  change (Raw.maskDiagonal ℂ S Lab).coeff x =
    ((Raw.maskDiagonal ℂ {a,b} W).coeff (fun i hi => first (x i (hAB hi))) *
      (Raw.maskDiagonal ℂ {b,c} W).coeff (fun i hi => second (x i (hBC hi)))) *
      (Raw.maskDiagonal ℂ {c,a} W).coeff (fun i hi => third (x i (hCA hi)))
  rw [Raw.maskDiagonal_coeff_at (K := ℂ) S ha x, read_pair a b hAB first,
    read_pair b c hBC second, read_pair c a hCA third]
  simp only [hcoeff]
  by_cases e₁ : first (x a ha) = first (x b hb) <;>
    by_cases e₂ : second (x b hb) = second (x c hc) <;>
    by_cases e₃ : third (x c hc) = third (x a ha) <;> simp [e₁,e₂,e₃]

end
end OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI.LinearAlgebra.SpectralBooks.SiteTensor

open scoped Classical BigOperators NNReal

noncomputable section

variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]

/-- The Behrend construction gives a diagonal of dimension N^(2-o(1)) inside
three wires of dimension 3N, hence the semiperimeter upper bound. -/
private theorem triangle_price_bound
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop)) (a b c : I) :
    maskDiagonalPrice φ 1 {a,b,c} ≤
      (maskDiagonalPrice φ 1 {a,b} + maskDiagonalPrice φ 1 {b,c} +
        maskDiagonalPrice φ 1 {c,a}) / 2 := by
  let S : Finset I := {a,b,c}
  let A : Finset I := {a,b}
  let B : Finset I := {b,c}
  let C : Finset I := {c,a}
  let p := maskDiagonalPrice φ 1 S
  let q := maskDiagonalPrice φ 1 A + maskDiagonalPrice φ 1 B + maskDiagonalPrice φ 1 C
  change p ≤ q / 2
  have hp : 0 ≤ p := maskDiagonalPrice_nonneg φ zero_le_one S
  have hq : 0 ≤ q := add_nonneg (add_nonneg
    (maskDiagonalPrice_nonneg φ zero_le_one A) (maskDiagonalPrice_nonneg φ zero_le_one B))
    (maskDiagonalPrice_nonneg φ zero_le_one C)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  have hA : A.Nonempty := Finset.insert_nonempty _ _
  have hB : B.Nonempty := Finset.insert_nonempty _ _
  have hC : C.Nonempty := Finset.insert_nonempty _ _
  have hestimate (N : ℕ) (hN : 0 < N) :
      p * (2 * Real.log N - 4 * Real.sqrt (Real.log N)) ≤ q * (Real.log N + Real.log 3) := by
    obtain ⟨D, hD, hcard, hAP⟩ := rothNumberNat_spec N
    have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
    have he : 0 < (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) := by positivity
    have hBehrend := Behrend.roth_lower_bound (N := N)
    rw [← hcard] at hBehrend
    have hD' : 0 < (D.card : ℝ) := he.trans_le hBehrend
    have hDpos : 0 < D.card := by exact_mod_cast hD'
    have hM : 0 < 3*N := by omega
    let : Nonempty (Fin (3*N)) := Fin.pos_iff_nonempty.mp hM
    let U := Raw.maskDiagonal ℂ A (Fin (3*N))
    let V := Raw.maskDiagonal ℂ B (Fin (3*N))
    let W := Raw.maskDiagonal ℂ C (Fin (3*N))
    have hU := Raw.maskDiagonal_ne_zero (K := ℂ) A hA (Fin (3*N))
    have hV := Raw.maskDiagonal_ne_zero (K := ℂ) B hB (Fin (3*N))
    have hW := Raw.maskDiagonal_ne_zero (K := ℂ) C hC (Fin (3*N))
    have hUV : (U.mul V).coeff ≠ 0 := by
      obtain ⟨u, hu⟩ := Function.ne_iff.mp hU
      obtain ⟨v, hv⟩ := Function.ne_iff.mp hV
      exact Function.ne_iff.mpr ⟨fun i => (u i, v i), mul_ne_zero hu hv⟩
    have h := rawLogPrice_mono φ (c := 1) zero_le_one (triangle_restriction a b c N D hD hAP)
    change rawLogPrice φ 1 (Raw.maskDiagonal ℂ S (Fin N × D)) ≤
      rawLogPrice φ 1 ((U.mul V).mul W) at h
    rw [rawLogPrice_mul φ 1 _ _ hUV hW, rawLogPrice_mul φ 1 _ _ hU hV] at h
    have hL : Fintype.card (Fin N × D) = N * D.card := by simp
    have hLeft : rawLogPrice φ 1 (Raw.maskDiagonal ℂ S (Fin N × D)) =
        p * Real.logb 2 ((N*D.card : ℕ) : ℝ) := by
      have hR := ofRaw_maskDiagonal_equiv (K := ℂ) S hS (Fintype.equivFin (Fin N × D))
      calc
        _ = rawLogPrice φ 1 (Raw.maskDiagonal ℂ S (Fin (Fintype.card (Fin N × D)))) := by
          unfold rawLogPrice
          rw [hR]
        _ = _ := by rw [hL, rawLogPrice_maskDiagonal φ 1 S hS (Nat.mul_pos hN hDpos)]
    rw [hLeft, rawLogPrice_maskDiagonal φ 1 A hA hM, rawLogPrice_maskDiagonal φ 1 B hB hM,
      rawLogPrice_maskDiagonal φ 1 C hC hM, ← add_mul, ← add_mul] at h
    change p * Real.logb 2 ((N*D.card : ℕ) : ℝ) ≤ q * Real.logb 2 ((3*N : ℕ) : ℝ) at h
    have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    simp only [Real.logb, ← mul_div_assoc, div_le_div_iff_of_pos_right hlog2, Nat.cast_mul,
      Nat.cast_ofNat] at h
    rw [Real.log_mul hN'.ne' hD'.ne', Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hN'.ne',
      add_comm (Real.log 3)] at h
    have hd := Real.log_le_log he hBehrend
    rw [Real.log_mul hN'.ne' (Real.exp_pos _).ne', Real.log_exp] at hd
    have hl : 2 * Real.log N - 4 * Real.sqrt (Real.log N) ≤ Real.log N + Real.log D.card := by linarith
    exact (mul_le_mul_of_nonneg_left hl hp).trans h
  by_contra! hbad
  let gap := 2*p - q
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let d := 4*p + q * Real.log 3
  have hd : 0 ≤ d := add_nonneg (by positivity) (mul_nonneg hq (Real.log_nonneg (by norm_num)))
  let L := 1 + (d + 1) / gap
  have hL : 1 ≤ L := by dsimp [L]; linarith [div_nonneg (by linarith : 0 ≤ d+1) hgap.le]
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (L^2))
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos _).trans hN
  have hlog := Real.log_lt_log (Real.exp_pos _) hN
  rw [Real.log_exp] at hlog
  let t := Real.sqrt (Real.log N)
  have ht : L < t := Real.lt_sqrt_of_sq_lt hlog
  have ht₁ : 1 ≤ t := hL.trans ht.le
  have ht_sq : t^2 = Real.log N := Real.sq_sqrt (by linarith [sq_nonneg L])
  have hgd : d < gap * t := by
    have hmul := mul_lt_mul_of_pos_left ht hgap
    have hform : gap * L = gap + d + 1 := by
      dsimp [L]
      field_simp
      ring
    rw [hform] at hmul
    linarith
  have hbig := mul_lt_mul_of_pos_right hgd (by linarith : 0 < t)
  have hsmall := hestimate N (by exact_mod_cast hNpos)
  change p * (2 * Real.log N - 4*t) ≤ q * (Real.log N + Real.log 3) at hsmall
  rw [← ht_sq] at hsmall
  have he := mul_le_mul_of_nonneg_left ht₁ (mul_nonneg hq (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)))
  dsimp [d, gap] at hbig
  nlinarith only [hbig, hsmall, he]

end
end OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI.Combinatorics.Sunflower

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open Planar
open scoped Classical

private theorem RealizesPlanarPrice.submodular {δ : Finset Plane → ℝ}
    (h : RealizesPlanarPrice δ)
    (A B : Finset Plane) (hAB : (A ∩ B).Nonempty) :
    δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B := by
  obtain ⟨x, hx⟩ := hAB
  let Z := A ∪ B
  let I := {a : Plane // a ∈ Z}
  have hxZ : x ∈ Z := Finset.mem_union_left _ (Finset.mem_inter.mp hx).1
  by_cases hn : Nontrivial I
  · let : Nontrivial I := hn
    let p : Plane → Prop := (· ∈ Z)
    let e : I ↪ Plane := Function.Embedding.subtype p
    obtain ⟨φ, c, hc, hφ⟩ := h e
    let A' := A.subtype p
    let B' := B.subtype p
    have hnAB : (A' ∩ B').Nonempty := by
      refine ⟨⟨x,hxZ⟩, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_subtype.mpr (Finset.mem_inter.mp hx).1
      · exact Finset.mem_subtype.mpr (Finset.mem_inter.mp hx).2
    have hnA := hnAB.mono Finset.inter_subset_left
    have hnB := hnAB.mono Finset.inter_subset_right
    have hnU := hnA.mono (Finset.subset_union_left (s₂ := B'))
    have hmA : A'.map e = A := Finset.subtype_map_of_mem fun _ ha => Finset.mem_union_left _ ha
    have hmB : B'.map e = B := Finset.subtype_map_of_mem fun _ hb => Finset.mem_union_right _ hb
    have hmI : (A' ∩ B').map e = A ∩ B := by rw [Finset.map_inter, hmA, hmB]
    have hmU : (A' ∪ B').map e = A ∪ B := by rw [Finset.map_union, hmA, hmB]
    rw [← hmU, ← hmI, ← hmA, ← hmB, hφ _ hnU, hφ _ hnAB, hφ _ hnA, hφ _ hnB]
    simp only [← mul_add]
    exact mul_le_mul_of_nonneg_left (maskDiagonalPrice_submodular φ zero_le_one A' B' hnAB) hc
  · have he : ∀ z ∈ Z, z = x := by
      intro z hz
      let : Subsingleton I := not_nontrivial_iff_subsingleton.mp hn
      exact congrArg Subtype.val (Subsingleton.elim (⟨z, hz⟩ : I) ⟨x, hxZ⟩)
    have hsing (S : Finset Plane) (hs : S ⊆ Z) (hm : x ∈ S) : S = {x} := by
      apply Finset.Subset.antisymm
      · intro z hz
        simpa using he z (hs hz)
      · exact Finset.singleton_subset_iff.mpr hm
    rw [show A = {x} from hsing A Finset.subset_union_left (Finset.mem_inter.mp hx).1,
      show B = {x} from hsing B Finset.subset_union_right (Finset.mem_inter.mp hx).2]
    simp

private def TrianglePriceBound : Prop :=
  ∀ (I : Type) [Fintype I] [Nontrivial I] [DecidableEq I]
      (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop)) (a b c : I),
    maskDiagonalPrice φ 1 {a,b,c} ≤
      (maskDiagonalPrice φ 1 {a,b} + maskDiagonalPrice φ 1 {b,c} +
        maskDiagonalPrice φ 1 {c,a}) / 2

private theorem RealizesPlanarPrice.triangle_le {δ : Finset Plane → ℝ}
    (h : RealizesPlanarPrice δ) (hwire : ∀ a b : Plane, δ {a,b} = dist a b)
    (htri : TrianglePriceBound) (a b c : Plane) :
    δ {a,b,c} ≤ (dist a b + dist b c + dist c a) / 2 := by
  let U : Finset Plane := {a,b,c}
  let I := {x : Plane // x ∈ U}
  let a' : I := ⟨a, by simp [U]⟩
  let b' : I := ⟨b, by simp [U]⟩
  let c' : I := ⟨c, by simp [U]⟩
  by_cases hnt : Nontrivial I
  · let : Nontrivial I := hnt
    let e : I ↪ Plane := Function.Embedding.subtype (· ∈ U)
    obtain ⟨φ, C, hC, hφ⟩ := h e
    have eqAB := hφ {a',b'} (Finset.insert_nonempty _ _)
    have eqBC := hφ {b',c'} (Finset.insert_nonempty _ _)
    have eqCA := hφ {c',a'} (Finset.insert_nonempty _ _)
    have eqABC := hφ {a',b',c'} (Finset.insert_nonempty _ _)
    simp only [Finset.map_insert, Finset.map_singleton] at eqAB eqBC eqCA eqABC
    change δ {a,b} = _ at eqAB
    change δ {b,c} = _ at eqBC
    change δ {c,a} = _ at eqCA
    change δ {a,b,c} = _ at eqABC
    have hprice := mul_le_mul_of_nonneg_left (htri I φ a' b' c') hC
    rw [← mul_div_assoc, mul_add, mul_add] at hprice
    have hAB : δ {a,b} = C * maskDiagonalPrice φ 1 {a',b'} := eqAB
    have hBC : δ {b,c} = C * maskDiagonalPrice φ 1 {b',c'} := eqBC
    have hCA : δ {c,a} = C * maskDiagonalPrice φ 1 {c',a'} := eqCA
    have hABC : δ {a,b,c} = C * maskDiagonalPrice φ 1 {a',b',c'} := eqABC
    have hg : δ {a,b,c} ≤ (δ {a,b} + δ {b,c} + δ {c,a}) / 2 := by
      rw [hABC, hAB, hBC, hCA]
      exact hprice
    simpa only [hwire] using hg
  · let : Subsingleton I := not_nontrivial_iff_subsingleton.mp hnt
    have hab : a = b := congrArg Subtype.val (Subsingleton.elim a' b')
    have hac : a = c := congrArg Subtype.val (Subsingleton.elim a' c')
    subst b
    subst c
    have hzero : δ {a} = 0 := by simpa using hwire a a
    simp [hzero]

end OAI.Combinatorics.Sunflower

/- Elementary counting and prime-exponent representation for arithmetic sunflowers. -/

namespace OMA.SunflowerScratch

open scoped BigOperators ArithmeticFunction.Omega

private theorem countBooleanExtensions {ι : Type*} [DecidableEq ι]
    {U S P : Finset ι} (hS : S ⊆ U) (hP : P ⊆ S) :
    (U.powerset.filter (fun W => W ∩ S = P)).card = 2 ^ (U.card - S.card) := by
  have hEq : U.powerset.filter (fun W => W ∩ S = P) =
      (U \ S).powerset.image (fun T => T ∪ P) := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hWU, hWP⟩
      refine ⟨W \ S, ?_, ?_⟩
      · intro i hi
        have hi' := Finset.mem_sdiff.mp hi
        exact Finset.mem_sdiff.mpr ⟨hWU hi'.1, hi'.2⟩
      · rw [← hWP, Finset.sdiff_union_inter]
    · rintro ⟨T, hT, rfl⟩
      constructor
      · intro i hi
        exact (Finset.mem_union.mp hi).elim
          (fun hi' => (Finset.mem_sdiff.mp (hT hi')).1)
          (fun hi' => hS (hP hi'))
      · ext i
        simp only [Finset.mem_inter, Finset.mem_union]
        exact ⟨fun ⟨hi, his⟩ => hi.elim
          (fun hit => False.elim ((Finset.mem_sdiff.mp (hT hit)).2 his)) id,
          fun hip => ⟨Or.inr hip, hP hip⟩⟩
  have hInj : Set.InjOn (fun T : Finset ι => T ∪ P) (↑((U \ S).powerset) : Set (Finset ι)) := by
    intro T hT V hV hEq'
    change T ∪ P = V ∪ P at hEq'
    ext i
    have hDisj (T : Finset ι) (hT : T ∈ (U \ S).powerset) (hi : i ∈ T) : i ∉ P :=
      fun hip => (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hT hi)).2 (hP hip)
    constructor
    · intro hi
      have hi' : i ∈ V ∪ P := hEq' ▸ Finset.mem_union_left _ hi
      exact (Finset.mem_union.mp hi').resolve_right (hDisj T hT hi)
    · intro hi
      have hi' : i ∈ T ∪ P := hEq'.symm ▸ Finset.mem_union_left _ hi
      exact (Finset.mem_union.mp hi').resolve_right (hDisj V hV hi)
  rw [hEq, Finset.card_image_of_injOn hInj, Finset.card_powerset,
    Finset.card_sdiff_of_subset hS]

private theorem thinBooleanRestrictions {α ι : Type*} [DecidableEq ι]
    (A : Finset α) (D P : α → Finset ι) (k : ℕ)
    (hD : ∀ n ∈ A, (D n).card = k) (hP : ∀ n ∈ A, P n ⊆ D n) :
    ∃ W : Finset ι, A.card ≤ 2 ^ k * (A.filter (fun n => W ∩ D n = P n)).card := by
  classical
  by_cases hA : A.Nonempty
  · let U := A.biUnion D
    have hU {n} (hn : n ∈ A) : D n ⊆ U := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨n, hn, hx⟩
    have hk : k ≤ U.card := by
      obtain ⟨n, hn⟩ := hA
      rw [← hD n hn]
      exact Finset.card_le_card (hU hn)
    let score (W : Finset ι) := (A.filter (fun n => W ∩ D n = P n)).card
    obtain ⟨W, _, hW⟩ := Finset.exists_max_image U.powerset score
      ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset U)⟩
    refine ⟨W, ?_⟩
    have hSum : (∑ V ∈ U.powerset, score V) = A.card * 2 ^ (U.card - k) := by
      calc
        _ = ∑ V ∈ U.powerset, ∑ n ∈ A, if V ∩ D n = P n then 1 else 0 := by
          simp only [score, Finset.sum_boole, Nat.cast_id]
        _ = ∑ n ∈ A, ∑ V ∈ U.powerset, if V ∩ D n = P n then 1 else 0 :=
          Finset.sum_comm
        _ = ∑ _ ∈ A, 2 ^ (U.card - k) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.sum_boole, Nat.cast_id, countBooleanExtensions (hU hn) (hP n hn),
            hD n hn]
        _ = _ := by simp
    have hBound : (∑ V ∈ U.powerset, score V) ≤ U.powerset.card * score W := by
      calc
        _ ≤ ∑ _ ∈ U.powerset, score W := Finset.sum_le_sum hW
        _ = _ := by simp
    have hPow : 2 ^ U.card = 2 ^ (U.card - k) * 2 ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    rw [hSum, Finset.card_powerset, hPow] at hBound
    have hMul : 0 < 2 ^ (U.card - k) := by positivity
    exact Nat.le_of_mul_le_mul_left (by simpa only [mul_assoc, mul_comm A.card] using hBound) hMul
  · exact ⟨∅, by simp [Finset.not_nonempty_iff_eq_empty.mp hA]⟩

private def layers (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  n.primeFactors.sigma (fun p => Finset.range (n.factorization p))

private def terminalLayers (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (layers n).filter (fun x => x.2 + 1 = n.factorization x.1)

@[simp] private theorem memLayers {n p i : ℕ} :
    (⟨p, i⟩ : Σ _ : ℕ, ℕ) ∈ layers n ↔ i < n.factorization p := by
  simp only [layers, Finset.mem_sigma, Finset.mem_range]
  refine ⟨And.right, fun hi => ⟨?_, hi⟩⟩
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  omega

private theorem layersCard (n : ℕ) : (layers n).card = Ω n := by
  rw [layers, Finset.card_sigma, ArithmeticFunction.cardFactors_eq_sum_factorization]
  simp [Finsupp.sum]

private theorem layersGcd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    layers (a.gcd b) = layers a ∩ layers b := by
  ext ⟨p, i⟩
  simp only [Finset.mem_inter, memLayers, Nat.factorization_gcd ha hb]
  change i < min (a.factorization p) (b.factorization p) ↔ _
  exact lt_min_iff

private theorem layersInjOn : Set.InjOn layers {n : ℕ | n ≠ 0} := by
  intro a ha b hb h
  apply Nat.factorization_inj ha hb
  ext p
  apply le_antisymm
  · by_contra! hl
    have hmem : (⟨p, b.factorization p⟩ : Σ _ : ℕ, ℕ) ∈ layers a := memLayers.mpr hl
    rw [h] at hmem
    exact (lt_irrefl _) (memLayers.mp hmem)
  · by_contra! hl
    have hmem : (⟨p, a.factorization p⟩ : Σ _ : ℕ, ℕ) ∈ layers b := memLayers.mpr hl
    rw [← h] at hmem
    exact (lt_irrefl _) (memLayers.mp hmem)

private theorem agreeingExponents {W : Finset (Σ _ : ℕ, ℕ)} {a b p : ℕ}
    (ha : W ∩ layers a = terminalLayers a) (hb : W ∩ layers b = terminalLayers b)
    (hpa : 0 < a.factorization p) (hpb : 0 < b.factorization p) :
    a.factorization p = b.factorization p := by
  have step {n m : ℕ} (hn : W ∩ layers n = terminalLayers n)
      (hm : W ∩ layers m = terminalLayers m) (hpn : 0 < n.factorization p)
      (hle : n.factorization p ≤ m.factorization p) :
      n.factorization p = m.factorization p := by
    let x : Σ _ : ℕ, ℕ := ⟨p, n.factorization p - 1⟩
    have hxN : x ∈ terminalLayers n := by
      simp only [x, terminalLayers, Finset.mem_filter, memLayers]
      omega
    have hxW : x ∈ W := by
      rw [← hn] at hxN
      exact (Finset.mem_inter.mp hxN).1
    have hxM : x ∈ terminalLayers m := by
      rw [← hm]
      exact Finset.mem_inter.mpr ⟨hxW, memLayers.mpr (by omega)⟩
    have he := (Finset.mem_filter.mp hxM).2
    dsimp [x] at he
    omega
  rcases le_total (a.factorization p) (b.factorization p) with hle | hle
  · exact step ha hb hpa hle
  · exact (step hb ha hpb hle).symm

private theorem coprimeGcdQuotient {W : Finset (Σ _ : ℕ, ℕ)} {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hwa : W ∩ layers a = terminalLayers a)
    (hwb : W ∩ layers b = terminalLayers b) :
    ∃ q, a = (a.gcd b) * q ∧ Nat.gcd q (a.gcd b) = 1 := by
  let d := a.gcd b
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ ha
  obtain ⟨q, hq⟩ := Nat.gcd_dvd_left a b
  change a = d * q at hq
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hq
    omega
  refine ⟨q, hq, Nat.coprime_of_dvd ?_⟩
  intro p hp hpq hpd
  have hpa : 0 < a.factorization p :=
    hp.factorization_pos_of_dvd ha.ne' (hpd.trans (Nat.gcd_dvd_left a b))
  have hpb : 0 < b.factorization p :=
    hp.factorization_pos_of_dvd hb.ne' (hpd.trans (Nat.gcd_dvd_right a b))
  have hpd' : d.factorization p = a.factorization p := by
    dsimp [d]
    rw [Nat.factorization_gcd ha.ne' hb.ne']
    change min (a.factorization p) (b.factorization p) = a.factorization p
    rw [agreeingExponents hwa hwb hpa hpb, min_self]
  have hpq' : 0 < q.factorization p := hp.factorization_pos_of_dvd hq0 hpq
  have hsum : a.factorization p = d.factorization p + q.factorization p := by
    rw [hq, Nat.factorization_mul hd.ne' hq0]
    rfl
  omega

theorem integerFamilyRepresentation :
    ∀ (r k : ℕ) (A : Finset ℕ), Erdos535.AllBigOmega k A →
      ∃ B ⊆ A, A.card ≤ 2 ^ k * B.card ∧
        ∃ enc : ℕ → Finset ℕ, Set.InjOn enc (B : Set ℕ) ∧
          (∀ n ∈ B, (enc n).card = k) ∧
          (∀ S ⊆ B, S.card = r →
            (∃ K : Finset ℕ,
              (S : Set ℕ).Pairwise (fun a b => enc a ∩ enc b = K)) →
            ∃ d, 0 < d ∧ (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d) ∧
              ∀ a ∈ S, ∃ b, a = d * b ∧ Nat.gcd b d = 1) := by
  intro r k A hΩ
  obtain ⟨W, hW⟩ := thinBooleanRestrictions A layers terminalLayers k
    (fun n hn => (layersCard n).trans (hΩ n hn).2)
    (fun n _ => Finset.filter_subset _ _)
  let B := A.filter (fun n => W ∩ layers n = terminalLayers n)
  let e := ((Equiv.sigmaEquivProd ℕ ℕ).trans Nat.pairEquiv).toEmbedding
  let enc (n : ℕ) := (layers n).map e
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have positive {a : ℕ} (ha : a ∈ B) : 0 < a := (hΩ a (hBA ha)).1
  have compatible {a : ℕ} (ha : a ∈ B) : W ∩ layers a = terminalLayers a :=
    (Finset.mem_filter.mp ha).2
  refine ⟨B, hBA, hW, enc, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    exact layersInjOn (positive ha).ne' (positive hb).ne' (Finset.map_injective e hab)
  · intro n hn
    change ((layers n).map e).card = k
    rw [Finset.card_map, layersCard, (hΩ n (hBA hn)).2]
  intro S hSB hSr hSunflower
  by_cases hSmall : r ≤ 1
  · refine ⟨1, by decide, ?_, fun a _ => ⟨a, by simp, by simp⟩⟩
    intro a ha b hb hab
    have hcard : 1 < S.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
    omega
  have hcard : 1 < S.card := by omega
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨K, hK⟩ := hSunflower
  let d := a₀.gcd b₀
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (positive (hSB ha₀))
  have common {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
      a.gcd b = d := by
    apply layersInjOn (Nat.gcd_pos_of_pos_left _ (positive (hSB ha))).ne' hd.ne'
    change layers (a.gcd b) = layers (a₀.gcd b₀)
    rw [layersGcd (positive (hSB ha)).ne' (positive (hSB hb)).ne',
      layersGcd (positive (hSB ha₀)).ne' (positive (hSB hb₀)).ne']
    apply Finset.map_injective e
    simpa only [Finset.map_inter] using (hK ha hb hab).trans (hK ha₀ hb₀ hab₀).symm
  refine ⟨d, hd, fun _ ha _ hb hab => common ha hb hab, ?_⟩
  intro a ha
  obtain ⟨b, hb, hab⟩ : ∃ b ∈ S, a ≠ b := by
    by_cases h : a = a₀
    · exact ⟨b₀, hb₀, h ▸ hab₀⟩
    · exact ⟨a₀, ha₀, h⟩
  simpa only [common ha hb hab] using
    coprimeGcdQuotient (positive (hSB ha)) (positive (hSB hb))
      (compatible (hSB ha)) (compatible (hSB hb))

end OMA.SunflowerScratch

namespace OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1

open Erdos535

private def FixedBaseSets : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ C : ℕ, 1 ≤ C ∧
    ∀ (k : ℕ) (F : Finset (Finset ℕ)),
      (∀ A ∈ F, A.card = k) → C ^ k < F.card →
      ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset ℕ,
        ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K

theorem main : FixedBaseSets → type_of% @Erdos535.erdos_535.variants.sunflower_strong := by
  intro h₁ r hr
  have h₂ := @OMA.SunflowerScratch.integerFamilyRepresentation
  obtain ⟨C, hC, hSunflower⟩ := h₁ r hr
  refine ⟨↑(2 * C : ℕ), by exact_mod_cast (by omega : 0 < 2 * C), ?_⟩
  intro k A hA hNoSunflower
  obtain ⟨B, hBA, hlarge, enc, henc, hsize, hlift⟩ := h₂ r k A hA
  have hBound : B.card ≤ C ^ k := by
    by_contra h
    have hG : C ^ k < (B.image enc).card := by
      rwa [Finset.card_image_of_injOn henc, ← not_le]
    obtain ⟨G, hGB, hGr, K, hGinter⟩ :=
      hSunflower k (B.image enc)
        (by
          intro L hL
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hL
          exact hsize n hn)
        hG
    let S := B.filter (fun n => enc n ∈ G)
    have hSB : S ⊆ B := Finset.filter_subset _ _
    have hSG : S.image enc = G := by
      ext L
      constructor
      · intro hL
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hL
        exact (Finset.mem_filter.mp hn).2
      · intro hL
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (hGB hL)
        exact Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ⟨hn, hL⟩, rfl⟩
    have hencS : Set.InjOn enc (S : Set ℕ) :=
      henc.mono (by exact hSB)
    have hSr : S.card = r := by
      rw [← Finset.card_image_of_injOn hencS, hSG, hGr]
    apply hNoSunflower S (hSB.trans hBA) hSr
    refine hlift S hSB hSr ⟨K, ?_⟩
    intro a ha b hb hab
    exact hGinter _ (Finset.mem_filter.mp ha).2 _ (Finset.mem_filter.mp hb).2
      (fun hEq => hab (hencS ha hb hEq))
  have hCard : A.card ≤ (2 * C) ^ k := by
    rw [mul_pow]
    exact hlarge.trans (Nat.mul_le_mul_left _ hBound)
  exact_mod_cast hCard

end OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1




/- The set sunflower bound follows from its word version and a finite coloring argument. -/

namespace OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1

private def FixedBaseWords : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ D : ℕ, 1 ≤ D ∧
    ∀ (k m : ℕ) (W : Finset (Fin k → Fin m)),
      (∀ w : Fin r → Fin k → Fin m, (∀ i, w i ∈ W) →
        (∀ j, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
        ∀ a b, w a = w b) → W.card ≤ D ^ k

private def RainbowExtraction : Prop :=
  ∀ (r k : ℕ), 0 < k → ∀ F : Finset (Finset ℕ), (∀ A ∈ F, A.card = k) →
    (¬ ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset ℕ,
      ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K) →
    ∃ (m : ℕ) (W : Finset (Fin k → Fin m)), F.card ≤ 3 ^ k * W.card ∧
      ∀ w : Fin r → Fin k → Fin m, (∀ i, w i ∈ W) →
        (∀ j, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
        ∀ a b, w a = w b

theorem main : FixedBaseWords → RainbowExtraction → OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1.FixedBaseSets := by
  unfold FixedBaseWords RainbowExtraction OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1.FixedBaseSets
  intro hWord hTransfer r hr
  obtain ⟨D, hD, hBound⟩ := hWord r hr
  refine ⟨3 * D, by omega, ?_⟩
  intro k F hUniform hLarge
  by_cases hZero : k = 0
  · subst k
    have hSmall : F.card ≤ 1 := Finset.card_le_one.mpr fun A hA B hB =>
      (Finset.card_eq_zero.mp (hUniform A hA)).trans
        (Finset.card_eq_zero.mp (hUniform B hB)).symm
    simp only [pow_zero] at hLarge
    exact (hLarge.not_ge hSmall).elim
  · by_contra hFree
    obtain ⟨m, W, hSize, hWordFree⟩ := hTransfer r k (Nat.pos_of_ne_zero hZero) F hUniform hFree
    apply hLarge.not_ge
    rw [mul_pow]
    exact hSize.trans (Nat.mul_le_mul_left _ (hBound k m W hWordFree))

end OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1



/- A finite rainbow coloring embeds a large subfamily into words. -/

/-
Ported from OpenAI math, commit 3344da59991ed94f9ba711217b29c1d760badfa6.
The source modules are Basic, ColorCount, Rounding and Transfer in
lean/OAI/Combinatorics/Sunflower. Changes inline the dependency modules, retain
the coloring and embedding arguments and pin the resulting statement to RainbowExtraction.
Licensed under the Apache License, Version 2.0, reproduced in LICENSE.OpenAI.
-/

/- # Sunflowers in set families and in word families -/

namespace RainbowOAI
namespace Combinatorics
namespace Sunflower

variable {ι I α β : Type*}

/-- Every entry of the tuple has the same value. This includes the empty tuple. -/
private def IsConstant (f : ι → β) : Prop :=
  ∀ i j, f i = f j

/-- One coordinate of a sunflower has either a common symbol or pairwise distinct symbols. -/
private def Admissible (f : ι → β) : Prop :=
  IsConstant f ∨ Function.Injective f

/-- Each coordinate of the tuple of words is admissible. -/
private def WordAdmissible (w : ι → I → β) : Prop :=
  ∀ c, Admissible (fun i => w i c)

/-- Every admissible ordered tuple of words in the family repeats one word. -/
private def WordFree (r : ℕ) (W : Finset (I → β)) : Prop :=
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
private def HasSunflower [DecidableEq α] (r : ℕ) (F : Finset (Finset α)) : Prop :=
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

end Sunflower
end Combinatorics
end RainbowOAI

/- # Counting rainbow members of uniform set families -/

open Finset

namespace RainbowOAI
namespace Combinatorics
namespace Sunflower

private noncomputable def extendColor {α : Type*} {k : ℕ} (hk : 0 < k)
    (U : Finset α) (f : U → Fin k) (x : α) : Fin k := by
  classical
  exact if h : x ∈ U then f ⟨x, h⟩ else ⟨0, hk⟩

/-- Fixing a bijection on a member of the family leaves all colors on its complement free. -/
private theorem card_good_colors {α : Type*} [DecidableEq α] {k : ℕ} (hk : 0 < k)
    (A U : Finset α) (hAU : A ⊆ U) (hA : A.card = k) :
    k.factorial * k ^ U.card ≤
      (univ.filter (fun f : U → Fin k =>
        Function.Bijective (fun x : A => extendColor hk U f x))).card * k ^ k := by
  classical
  let Good := fun f : U → Fin k => Function.Bijective (fun x : A => extendColor hk U f x)
  let join : (A ≃ Fin k) × ((U \ A : Finset α) → Fin k) → (U → Fin k) :=
    fun p u => if h : u.val ∈ A then p.1 ⟨u, h⟩
      else p.2 ⟨u, mem_sdiff.mpr ⟨u.property, h⟩⟩
  have hjoin (p) : Good (join p) := by
    change Function.Bijective (fun x : A => extendColor hk U (join p) x)
    convert p.1.bijective using 1
    funext x
    simp [extendColor, join, x.property, hAU x.property]
  have hinj : Function.Injective join := by
    intro p q h
    apply Prod.ext
    · apply Equiv.ext
      intro x
      have he := congrFun h (⟨x, hAU x.property⟩ : U)
      simpa [join, x.property] using he
    · funext x
      obtain ⟨hxU, hxA⟩ := mem_sdiff.mp x.property
      have he := congrFun h (⟨x, hxU⟩ : U)
      simpa [join, hxA] using he
  have hcount := Fintype.card_le_of_injective
    (fun p => (⟨join p, hjoin p⟩ : {f // Good f})) (fun _ _ h => hinj (congrArg Subtype.val h))
  have e : A ≃ Fin k := Fintype.equivFinOfCardEq (by simpa using hA)
  rw [Fintype.card_prod, Fintype.card_equiv e, Fintype.card_fun] at hcount
  simp only [Fintype.card_coe, hA, Fintype.card_fin] at hcount
  rw [Fintype.card_of_subtype (univ.filter Good) (by simp)] at hcount
  have hsum : (U \ A).card + k = U.card := hA ▸ card_sdiff_add_card_eq_card hAU
  calc
    k.factorial * k ^ U.card =
        (k.factorial * k ^ (U \ A).card) * k ^ k := by rw [← hsum, pow_add, mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ hcount

/-- Some coloring retains at least the fraction `k! / k^k` of a finite uniform family. -/
theorem exists_rainbow_subfamily {α : Type*} {k : ℕ} (hk : 0 < k)
    (F : Finset (Finset α)) (hF : ∀ A ∈ F, A.card = k) :
    ∃ (c : α → Fin k) (G : Finset (Finset α)), G ⊆ F ∧
      (∀ A ∈ G, Function.Bijective (fun x : A => c x)) ∧
      F.card * k.factorial ≤ G.card * k ^ k := by
  classical
  let U : Finset α := F.biUnion id
  let Good := fun (c : U → Fin k) (A : Finset α) =>
    Function.Bijective (fun x : A => extendColor hk U c x)
  let _ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨c, _, hc⟩ := (univ : Finset (U → Fin k)).exists_max_image
    (fun c => (F.filter (Good c)).card) univ_nonempty
  refine ⟨extendColor hk U c, F.filter (Good c), filter_subset _ _, ?_, ?_⟩
  · exact fun _ hA => (mem_filter.mp hA).2
  · have hcount (A) (hA : A ∈ F) := card_good_colors hk A U
        (subset_biUnion_of_mem id hA) (hF A hA)
    have hswap :
        ∑ A ∈ F, (univ.filter (fun c => Good c A)).card =
          ∑ f : U → Fin k, (F.filter (Good f)).card := by
      simp only [card_filter]
      rw [sum_comm]
    have allColors : Fintype.card (U → Fin k) = k ^ U.card := by
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    have htotal :
        F.card * (k.factorial * k ^ U.card) ≤
          (k ^ U.card * (F.filter (Good c)).card) * k ^ k := calc
      _ = ∑ _A ∈ F, k.factorial * k ^ U.card := by simp
      _ ≤ ∑ A ∈ F, (univ.filter (fun c => Good c A)).card * k ^ k :=
        sum_le_sum hcount
      _ = (∑ f : U → Fin k, (F.filter (Good f)).card) * k ^ k := by rw [← sum_mul, hswap]
      _ ≤ (∑ _f : U → Fin k, (F.filter (Good c)).card) * k ^ k :=
        Nat.mul_le_mul_right _ (sum_le_sum hc)
      _ = _ := by simp [allColors]
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < k ^ U.card from Nat.pow_pos hk)
    · simpa only [mul_left_comm, mul_assoc, mul_comm] using htotal

end Sunflower
end Combinatorics
end RainbowOAI

/- # Exponential bounds for coloring and word comparisons -/

namespace RainbowOAI
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

end Sunflower
end Combinatorics
end RainbowOAI

/- # Transferring word bounds to uniform set families -/

namespace RainbowOAI
namespace Combinatorics
namespace Sunflower

/-- Ordering each rainbow member by color gives a word. A finite alphabet suffices
even when the ground type is infinite. -/
private theorem rainbow_encoding {α : Type*} [DecidableEq α] {k : ℕ}
    (G : Finset (Finset α)) (c : α → Fin k)
    (hc : ∀ A ∈ G, Function.Bijective (fun x : A => c x)) :
    ∃ (n : ℕ) (encode : G → Fin k → Fin n) (decode : Fin n → α),
      Function.Injective decode ∧
      ∀ (A : G) (x : α), x ∈ (A : Finset α) ↔ decode (encode A (c x)) = x := by
  classical
  let U := G.biUnion id
  let e (A : G) : (A : Finset α) ≃ Fin k := Equiv.ofBijective _ (hc A A.property)
  let point (A : G) (j : Fin k) : U :=
    ⟨(e A).symm j, Finset.mem_biUnion.mpr ⟨A, A.property, ((e A).symm j).property⟩⟩
  let encode (A : G) (j : Fin k) := U.equivFin (point A j)
  let decode (u : Fin U.card) : α := U.equivFin.symm u
  have hdecode (A : G) (j : Fin k) :
      decode (encode A j) = ((e A).symm j).val := by
    simp [decode, encode, point]
  refine ⟨U.card, encode, decode, Subtype.val_injective.comp U.equivFin.symm.injective, ?_⟩
  intro A x
  rw [hdecode]
  constructor
  · intro hx
    have he : (e A) ⟨x, hx⟩ = c x := rfl
    rw [← he, Equiv.symm_apply_apply]
  · intro hx
    exact hx ▸ ((e A).symm (c x)).property

/-- A rainbow subfamily of a sunflower-free family embeds as an equally large
sunflower-free family of words over one finite alphabet. -/
theorem exists_word_family_of_rainbow {α : Type*} [DecidableEq α] {k r : ℕ}
    {G F : Finset (Finset α)} (hGF : G ⊆ F) (c : α → Fin k)
    (hc : ∀ A ∈ G, Function.Bijective (fun x : A => c x))
    (hfree : ¬ HasSunflower r F) :
    ∃ (n : ℕ) (W : Finset (Fin k → Fin n)), W.card = G.card ∧ WordFree r W := by
  classical
  obtain ⟨n, encode, decode, hd, hmem⟩ := rainbow_encoding G c hc
  have hinj : Function.Injective encode := by
    intro A B hab
    apply Subtype.ext
    ext x
    rw [hmem, hmem, hab]
  let W := Finset.univ.image encode
  refine ⟨n, W, ?_, ?_⟩
  · simp [W, Finset.card_image_of_injective _ hinj]
  intro w hw hadm
  by_contra hnc
  have hwi := hadm.injective_of_not_isConstant hnc
  have hlift (i : Fin r) : ∃ A : G, encode A = w i := by
    obtain ⟨A, _, ha⟩ := Finset.mem_image.mp (hw i)
    exact ⟨A, ha⟩
  choose A hA using hlift
  have hAinj : Function.Injective (fun i => (A i : Finset α)) := by
    intro i j hij
    apply hwi
    rw [← hA i, ← hA j, Subtype.ext hij]
  have hAmem (i : Fin r) (x : α) :
      x ∈ (A i : Finset α) ↔ decode (w i (c x)) = x := by rw [← hA, hmem]
  let K := (G.biUnion id).filter fun x => ∀ i, x ∈ (A i : Finset α)
  apply hfree
  apply hasSunflower_of_indexed (K := K) (fun i => hGF (A i).property) hAinj
  intro i j hij
  ext x
  constructor
  · intro hx
    obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨A i, (A i).property, hi⟩, ?_⟩
    have heq : w i (c x) = w j (c x) :=
      hd (((hAmem i x).mp hi).trans ((hAmem j x).mp hj).symm)
    rcases hadm (c x) with hall | hdistinct
    · intro t
      exact (hAmem t x).mpr ((congrArg decode (hall t i)).trans ((hAmem i x).mp hi))
    · exact (hij (hdistinct heq)).elim
  · intro hx
    have hAll := (Finset.mem_filter.mp hx).2
    exact Finset.mem_inter.mpr ⟨hAll i, hAll j⟩

end Sunflower
end Combinatorics
end RainbowOAI

open RainbowOAI.Combinatorics.Sunflower

private theorem rainbowTransfer : OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1.RainbowExtraction := by
  intro r k hk F hUniform hFree
  obtain ⟨c, G, hGF, hc, hCount⟩ := exists_rainbow_subfamily hk F hUniform
  obtain ⟨m, W, hCard, hW⟩ := exists_word_family_of_rainbow hGF c hc
    (show ¬ HasSunflower r F from hFree)
  refine ⟨m, W, ?_, hW⟩
  apply Nat.le_of_mul_le_mul_right (c := k.factorial) _ (Nat.factorial_pos k)
  calc
    F.card * k.factorial ≤ G.card * k ^ k := hCount
    _ ≤ G.card * (3 ^ k * k.factorial) :=
      Nat.mul_le_mul_left _ (pow_self_le_three_pow_mul_factorial k)
    _ = (3 ^ k * W.card) * k.factorial := by rw [hCard]; ac_rfl







namespace OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R2

open OAI.Combinatorics.Sunflower OAI.Combinatorics.Sunflower.Planar
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

private abbrev FourSiteSpectrum :=
  normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 4) ℂ → _ → Prop)

/-- The four-point condition fails when just one of the three pair sums is largest. -/
private def NonTreeFourPoint (φ : FourSiteSpectrum) : Prop :=
  let w (i j : Fin 4) := maskDiagonalPrice φ 1 {i,j}
  max (w 0 2 + w 1 3) (w 0 3 + w 1 2) < w 0 1 + w 2 3

/-- There is a complex tensor spectral point with a non-tree wire metric. -/
def H1 : Prop :=
  ∃ φ : FourSiteSpectrum, NonTreeFourPoint φ

/-- A non-tree spectral point gives a planar price realized at one spectral point
on each finite placement, with Euclidean distances as its two-site prices. -/
def H2 : Prop :=
  ∀ φ : FourSiteSpectrum, NonTreeFourPoint φ →
    ∃ δ : Finset Plane → ℝ, RealizesPlanarPrice δ ∧ Monotone δ ∧
      ∀ a b : Plane, δ {a,b} = dist a b

theorem main : H1 → H2 → type_of% @Erdos535.erdos_535.variants.sunflower_strong := by
  rintro ⟨ψ, hψ⟩ hplanar
  obtain ⟨δ, hfinite, hmono, hwire⟩ := hplanar ψ hψ
  have htri : TrianglePriceBound := fun _ _ _ _ φ a b c => triangle_price_bound φ a b c
  apply OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1.main
  apply OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1.main
  · exact wordBound_of_planarRealization
      ⟨δ, ⟨hmono, hfinite.submodular, hwire, hfinite.triangle_le hwire htri⟩, hfinite⟩
  · exact rainbowTransfer

end OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R2
