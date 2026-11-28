import FormalConjectures.Paper.FiniteLocallyFreeGroupSchemeExponent
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations

/- Adapted from github.com/TauCetiProject/TauCeti (commit ac8801f612041ee3dcb3fa3f950f01318206737c), (c) 2026 The Tau Ceti contributors, Apache-2.0 licence. Files: TauCeti/Algebra/AlgebraicGroup/KilledByRank.lean and its imports FunctorOfPoints, BaseChange/Basic, HopfAlgebra/TensorShear, Coalgebra/Convolution, RingTheory/TensorProduct/Maps, LinearAlgebra/TensorProduct/Basic, concatenated and ported to Lean 4.33.1 / Mathlib 0df444a. -/
section
open WithConv TensorProduct Coalgebra
noncomputable def AlgHom.convPostcomp {R B B' C : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    [Semiring B'] [Algebra R B'] [AddCommMonoid C] [Module R C] [Coalgebra R C] (g : B →ₐ[R] B') :
    WithConv (C →ₗ[R] B) →ₐ[R] WithConv (C →ₗ[R] B') where
  toFun f := toConv (g.toLinearMap ∘ₗ f.ofConv)
  map_one' := by
    apply WithConv.ofConv_injective
    ext c
    simp [LinearMap.convOne_def]
  map_mul' f h := by
    apply WithConv.ofConv_injective
    exact LinearMap.algHom_comp_convMul_distrib g f h
  map_zero' := by
    apply WithConv.ofConv_injective
    ext c
    simp
  map_add' f h := by
    apply WithConv.ofConv_injective
    ext c
    simp
  commutes' r := by
    apply WithConv.ofConv_injective
    ext c
    simp [LinearMap.convAlgebraMap_apply, Algebra.algebraMap_eq_smul_one]

@[simp]
theorem AlgHom.convPostcomp_apply_ofConv {R B B' C : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    [Semiring B'] [Algebra R B'] [AddCommMonoid C] [Module R C] [Coalgebra R C] (g : B →ₐ[R] B')
    (f : WithConv (C →ₗ[R] B)) :
    (AlgHom.convPostcomp (C := C) g f).ofConv = g.toLinearMap ∘ₗ f.ofConv := rfl
end
section
-- MODULE LinearAlgebra/TensorProduct/Basic
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/








/-!
# Tensor-product naturality, contractions and trace identities

This file records how tensor reassociation interacts with tensoring composite maps, and that
`f ⊗ 𝟙` sends pure tensors with a left factor in the kernel of `f` to zero. It defines
contraction against a linear functional on the right factor, bundled as a linear map in the
functional, and records its behavior on pure tensors and under tensor-product maps.
Such contractions extract coordinates and test tensor identities, supporting componentwise
arguments about coactions and weight spaces. The file also proves the tensor identity that makes
the Casimir element of a trace commute with multiplication, and writes every tensor as a sum of
pure tensors over a finite spanning family of the right factor. It also expands pure tensors
with a multiset sum in one factor. Finally, it shows that a scalar action which can be moved
across `M ⊗[R] N` can also be moved across `M ⊗[R] (N ⊗[K] P)`.

## Main declarations

* `LinearMap.assoc_rTensor_lTensor_comp`: reassociation commutes with tensoring a composite map.
* `LinearMap.lTensor_rTensor_comm`: tensoring maps on the two factors commutes elementwise.
* `LinearMap.rTensor_add_lTensor_comp_rTensor_comp_self`: the twisted co-Leibniz operator
  `b ⊗ 𝟙 + (𝟙 ⊗ d) ∘ (τ ⊗ 𝟙)` on `N ⊗ P` composed with itself, for an involution `τ`
  anticommuting with `b`.
* `LinearMap.injective_rTensor_congr`: injectivity of `f ⊗ 𝟙 M` is invariant under isomorphisms
  of `M`.
* `LinearMap.tmul_mem_ker_rTensor`: tensoring an element of the kernel of `f` with any `w` gives
  an element of the kernel of `f ⊗ 𝟙`.
* `LinearMap.tensorComponent`: contraction against the right factor of a tensor product.
* `LinearMap.tensorComponentEquiv`: tensors as linear maps from the dual of a finite projective
  right factor.
* `LinearMap.sum_tensorComponent_tmul`: reconstruct a tensor from a dual family.
* `LinearMap.tensorComponent_eq_liftBaseChange`: contraction as scalar-linear extension.
* `LinearMap.tensorComponent_map`: naturality of contraction under `TensorProduct.map`.
* `LinearMap.tensorComponent_assoc_symm`: contraction commutes with reassociation.
* `LinearMap.comp_tensorComponent`: contraction commutes with a functional on the left.
* `LinearMap.tensorComponent_comp_tensorComponent`: successive contractions combine after
  reassociation.
* `LinearMap.tensorComponent_mul`: contracting a product in an algebra tensor product against a
  functional which splits on products splits the contraction accordingly.
* `LinearMap.lid_lTensor_apply` and `LinearMap.rid_rTensor_apply`: naturality of the left and
  right tensor unitors.
* `LinearMap.sum_mul_tmul_eq_sum_tmul_mul`: the Casimir element of a trace commutes with
  multiplication.
* `TensorProduct.tmul_multiset_sum`, `TensorProduct.multiset_sum_tmul`: a pure tensor with a
  multiset sum in one factor is the sum of the pure tensors.
* `TensorProduct.map_neg_left` and `TensorProduct.map_neg_right`: negating either argument of
  `TensorProduct.map` negates the tensor-product map.
* `TensorProduct.exists_eq_sum_tmul_of_span_eq_top`: over a finite spanning family of the right
  factor, every tensor is a sum of pure tensors with those right factors.
* `TensorProduct.nontrivial_right`: the right factor is nontrivial when the tensor product is.
* `TensorProduct.mk_one_eq_rTensor_comp_lid_symm`: the map `M → A ⊗[R] M`, `m ↦ 1 ⊗ m`, is the
  structure map `R → A` tensored with `M`.
* `TensorProduct.injective_mk_one_iff`: `m ↦ 1 ⊗ m` is injective iff the structure map `R → A`
  stays injective after tensoring with `M`.
* `TensorProduct.tensorTensorTensorComm_comm_tmul_comm`: exchanging the factors of both arguments
  of `tensorTensorTensorComm` exchanges the factors of its value.
* `TensorProduct.assoc_rTensor_tensorTensorTensorComm_tmul`: reassociating both arguments of
  `tensorTensorTensorComm` reassociates its value, and
  `TensorProduct.assoc_rTensor_comp_map_tensorTensorTensorComm_tmul` is its form after maps into
  the first two factors.
* `TensorProduct.CompatibleSMul.tensorProduct`: `K`-balanced and `R`-balanced tensors agreeing in
  `M ⊗[R] N` agree in `M ⊗[R] (N ⊗[K] P)`.
* `TensorProduct.map_sum_left` and `TensorProduct.map_sum_right`: the tensor product of linear maps
  is additive in each factor over finite sums.
* `TensorProduct.map_sub_left` and `TensorProduct.map_sub_right`, with their applied forms
  `TensorProduct.map_sub_left_apply` and `TensorProduct.map_sub_right_apply`: the tensor product of
  linear maps is subtractive in each factor.

## References

* L. Kadison, *New examples of Frobenius extensions*, University Lecture Series 14, AMS, 1999
  (dual bases of Frobenius algebras and extensions, and their Casimir elements).
-/


open TensorProduct
open scoped TensorProduct

namespace LinearMap

universe u v w x y

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

section Naturality

variable {P Q S T : Type*}
variable [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
variable [AddCommMonoid S] [Module R S] [AddCommMonoid T] [Module R T]

/-- Reassociation commutes with tensoring a composite linear map and changing the last factor. -/
theorem assoc_rTensor_lTensor_comp (f : N →ₗ[R] P) (g : Q →ₗ[R] S)
    (ρ : M →ₗ[R] T ⊗[R] N) (t : M ⊗[R] Q) :
    TensorProduct.assoc R T P S ((f.lTensor T ∘ₗ ρ).rTensor S (g.lTensor M t)) =
      TensorProduct.map id (TensorProduct.map f g)
        (TensorProduct.assoc R T N Q (ρ.rTensor Q t)) := by
  simp only [lTensor_def, rTensor_map, comp_id]
  rw [← map_rTensor, ← TensorProduct.map_map_assoc]

/-- Tensoring maps on the two factors commutes, elementwise: `(𝟙 ⊗ g) ∘ (f ⊗ 𝟙)` and
`(f ⊗ 𝟙) ∘ (𝟙 ⊗ g)` agree on every element. -/
theorem lTensor_rTensor_comm (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : M ⊗[R] N) :
    g.lTensor P (f.rTensor N x) = f.rTensor Q (g.lTensor M x) := by
  rw [← comp_apply, lTensor_comp_rTensor, ← rTensor_comp_lTensor, comp_apply]

/-- Injectivity of `f ⊗ 𝟙 M` only depends on `M` up to isomorphism. -/
theorem injective_rTensor_congr (f : N →ₗ[R] P) (e : M ≃ₗ[R] Q) :
    Function.Injective (f.rTensor M) ↔ Function.Injective (f.rTensor Q) := by
  have h : e.lTensor P ∘ f.rTensor M = f.rTensor Q ∘ e.lTensor N :=
    funext fun x ↦ lTensor_rTensor_comm f e.toLinearMap x
  rw [← EquivLike.comp_injective _ (e.lTensor P), h, EquivLike.injective_comp]

/-- Tensoring with any `w` sends the kernel of a linear map `f` into the kernel of `f ⊗ 𝟙`. -/
theorem tmul_mem_ker_rTensor {f : N →ₗ[R] P} {x : N} (hx : x ∈ ker f) (w : M) :
    x ⊗ₜ w ∈ ker (f.rTensor M) := by
  rw [mem_ker, rTensor_tmul, mem_ker.mp hx, zero_tmul]

/-- Composing the twisted co-Leibniz operator `b ⊗ 𝟙 + (𝟙 ⊗ d) ∘ (τ ⊗ 𝟙)` on `N ⊗ P` with itself:
if `τ` is an involution anticommuting with `b`, the cross terms cancel and the composite is
`(b ∘ b) ⊗ 𝟙 + 𝟙 ⊗ (d ∘ d)`. -/
theorem rTensor_add_lTensor_comp_rTensor_comp_self (b τ : N →ₗ[R] N) (d : P →ₗ[R] P)
    (hτ : τ ∘ₗ τ = id) (hodd : b ∘ₗ τ + τ ∘ₗ b = 0) :
    (b.rTensor P + d.lTensor N ∘ₗ τ.rTensor P) ∘ₗ (b.rTensor P + d.lTensor N ∘ₗ τ.rTensor P) =
      (b ∘ₗ b).rTensor P + (d ∘ₗ d).lTensor N := by
  refine ext fun w ↦ ?_
  have hcross : TensorProduct.map (b ∘ₗ τ) d w + TensorProduct.map (τ ∘ₗ b) d w = 0 := by
    rw [← LinearMap.add_apply, ← TensorProduct.map_add_left, hodd, TensorProduct.map_zero_left,
      LinearMap.zero_apply]
  have hcommute (y : N ⊗[R] P) : τ.rTensor P (d.lTensor N y) = d.lTensor N (τ.rTensor P y) :=
    (lTensor_rTensor_comm τ d y).symm
  have hlast : d.lTensor N (τ.rTensor P (d.lTensor N (τ.rTensor P w))) = (d ∘ₗ d).lTensor N w := by
    rw [hcommute, ← lTensor_comp_apply, ← rTensor_comp_apply, hτ, rTensor_id_apply]
  have hcrossLeft :
      b.rTensor P (d.lTensor N (τ.rTensor P w)) = TensorProduct.map (b ∘ₗ τ) d w := by
    rw [← comp_apply, rTensor_comp_lTensor, map_rTensor]
  have hcrossRight :
      d.lTensor N (τ.rTensor P (b.rTensor P w)) = TensorProduct.map (τ ∘ₗ b) d w := by
    rw [← rTensor_comp_apply, ← comp_apply, lTensor_comp_rTensor]
  simp only [LinearMap.add_apply, comp_apply, map_add]
  rw [hcrossLeft, hcrossRight, hlast, ← rTensor_comp_apply]
  rw [show ∀ A B X Y : N ⊗[R] P, A + Y + (X + B) = A + B + (X + Y) from fun A B X Y ↦ by abel,
    hcross, add_zero]

end Naturality

/-- Apply a linear functional to the right factor of a tensor, linearly in the functional. -/
noncomputable def tensorComponent : (N →ₗ[R] R) →ₗ[R] M ⊗[R] N →ₗ[R] M :=
  (compRight R (TensorProduct.rid R M).toLinearMap).comp (lTensorHom M)

/-- A right tensor component sends a pure tensor to the corresponding scalar multiple. -/
@[simp]
theorem tensorComponent_tmul (phi : N →ₗ[R] R) (m : M) (n : N) :
    tensorComponent (R := R) (M := M) phi (m ⊗ₜ[R] n) = phi n • m := by
  simp [tensorComponent]

/-- For a finite projective right factor, contraction identifies tensors with linear maps
from its dual. This is `dualTensorHomEquiv` transported through `Module.evalEquiv` and
`TensorProduct.comm`. -/
noncomputable def tensorComponentEquiv [Module.Projective R N] [Module.Finite R N] :
    M ⊗[R] N ≃ₗ[R] (Module.Dual R N →ₗ[R] M) :=
  TensorProduct.comm R M N ≪≫ₗ
    TensorProduct.congr (Module.evalEquiv R N) (.refl R M) ≪≫ₗ
    dualTensorHomEquiv R (Module.Dual R N) M

/-- Evaluating the tensor–dual-Hom equivalence is contraction against the given functional. -/
@[simp]
theorem tensorComponentEquiv_apply [Module.Projective R N] [Module.Finite R N]
    (x : M ⊗[R] N) (φ : Module.Dual R N) :
    tensorComponentEquiv x φ = tensorComponent φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [tensorComponentEquiv]
  | add x y hx hy => simp [hx, hy]

/-- A family of vectors and functionals that reconstructs each vector also reconstructs
any tensor, by contracting its second factor. The family need not be linearly independent. -/
theorem sum_tensorComponent_tmul {ι : Type*} [Fintype ι]
    (b : ι → N) (φ : ι → N →ₗ[R] R)
    (hb : ∀ x, ∑ i, φ i x • b i = x) (z : M ⊗[R] N) :
    ∑ i, tensorComponent (φ i) z ⊗ₜ[R] b i = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simpa only [tensorComponent_tmul, smul_tmul, ← tmul_sum] using
      congrArg (fun n ↦ m ⊗ₜ[R] n) (hb n)
  | add z w hz hw => simp [add_tmul, Finset.sum_add_distrib, hz, hw]

/-- Over an algebra, contraction is the scalar-linear extension of the functional followed
by the algebra map. This expresses contraction as a linear map over the larger scalar ring. -/
theorem tensorComponent_eq_liftBaseChange {S : Type*} [CommSemiring S] [Algebra R S]
    (φ : N →ₗ[R] R) (z : S ⊗[R] N) :
    tensorComponent φ z = ((Algebra.linearMap R S).comp φ).liftBaseChange S z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s n => simp [Algebra.smul_def, mul_comm]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Taking a right tensor component commutes with a map on both tensor factors. -/
@[simp]
theorem tensorComponent_map {M' : Type x} {N' : Type y}
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    (phi : N' →ₗ[R] R) (f : M →ₗ[R] M') (g : N →ₗ[R] N') (t : M ⊗[R] N) :
    tensorComponent phi (TensorProduct.map f g t) =
      f (tensorComponent (phi.comp g) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m n => simp

/-- Taking a right tensor component commutes with a map on the left factor. -/
@[simp]
theorem tensorComponent_rTensor {M' : Type x} [AddCommMonoid M'] [Module R M']
    (phi : N →ₗ[R] R) (f : M →ₗ[R] M') (t : M ⊗[R] N) :
    tensorComponent phi (f.rTensor N t) = f (tensorComponent phi t) := by
  simp [rTensor_def]

section

variable {R M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- Contraction of the last tensor factor commutes with reassociation. -/
@[simp]
theorem tensorComponent_assoc_symm (phi : P →ₗ[R] R) (u : M ⊗[R] (N ⊗[R] P)) :
    tensorComponent phi ((TensorProduct.assoc R M N P).symm u) =
      (tensorComponent phi).lTensor M u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul m v =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [tmul_add, map_add, hv, hw]
    | tmul n p =>
      simp only [TensorProduct.assoc_symm_tmul, tensorComponent_tmul,
        lTensor_tmul, TensorProduct.tmul_smul]

/-- Contracting the middle factor after reassociation is contraction of the left factor of the
second tensor factor, followed by the left unitor. -/
@[simp]
theorem rTensor_tensorComponent_assoc_symm (phi : N →ₗ[R] R) (u : M ⊗[R] (N ⊗[R] P)) :
    (tensorComponent phi).rTensor P ((TensorProduct.assoc R M N P).symm u) =
      (TensorProduct.lid R P ∘ₗ phi.rTensor P).lTensor M u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul m v =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [tmul_add, map_add, hv, hw]
    | tmul n p => simp [TensorProduct.smul_tmul]

/-- Applying two tensor components successively is contraction by the composed functional
on the last two factors, after reassociation. -/
theorem tensorComponent_comp_tensorComponent (phi : N →ₗ[R] R) (psi : P →ₗ[R] R) :
    tensorComponent (M := M) phi ∘ₗ tensorComponent (M := M ⊗[R] N) psi =
      tensorComponent (M := M) (phi ∘ₗ tensorComponent psi) ∘ₗ
        (TensorProduct.assoc R M N P).toLinearMap := by
  refine TensorProduct.ext_threefold fun m n p ↦ ?_
  simp [smul_smul]

/-- Applying functionals to both factors is independent of the order of contraction. -/
theorem comp_tensorComponent (psi : M →ₗ[R] R) (phi : N →ₗ[R] R) :
    psi ∘ₗ tensorComponent phi =
      phi ∘ₗ (TensorProduct.lid R N).toLinearMap ∘ₗ psi.rTensor N := by
  refine TensorProduct.ext' fun m n ↦ ?_
  simp only [comp_apply, tensorComponent_tmul, map_smul,
    smul_eq_mul, rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    mul_comm]

/-- Contracting the coefficient of a product in an algebra tensor product `A ⊗ C` against a
functional which splits on products as `θ (a * b) = φ a * ψ b + φ' a * ψ' b` splits the
contraction accordingly. For a comodule algebra this computes the contraction of the coaction of
a product. -/
theorem tensorComponent_mul {A C : Type*} [Semiring A] [Algebra R A] [Semiring C] [Algebra R C]
    {θ φ ψ φ' ψ' : C →ₗ[R] R} (hθ : ∀ a b, θ (a * b) = φ a * ψ b + φ' a * ψ' b)
    (x y : A ⊗[R] C) :
    tensorComponent θ (x * y) =
      tensorComponent φ x * tensorComponent ψ y + tensorComponent φ' x * tensorComponent ψ' y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' =>
    simp only [add_mul, map_add, hx, hx']
    abel
  | tmul a c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' =>
      simp only [mul_add, map_add, hy, hy']
      abel
    | tmul b c' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorComponent_tmul, hθ, add_smul,
        smul_mul_smul_comm]

end

/-- The left tensor unitor is natural with respect to a linear map in its right factor. -/
@[simp]
theorem lid_lTensor_apply (f : M →ₗ[R] N) (t : R ⊗[R] M) :
    TensorProduct.lid R N (lTensor R f t) = f (TensorProduct.lid R M t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The right tensor unitor is natural with respect to a linear map in its left factor. -/
@[simp]
theorem rid_rTensor_apply (f : M →ₗ[R] N) (t : M ⊗[R] R) :
    TensorProduct.rid R N (rTensor R f t) = f (TensorProduct.rid R M t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m r => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The Casimir element of a trace

Let `φ : A →ₗ[k] k` be a trace on a `k`-algebra `A`, so `φ (a * b) = φ (b * a)`, and let `x` and
`y` be finite families dual to each other for the pairing `(a, b) ↦ φ (a * b)`, in the sense that
every element expands in either family with coefficients read off by pairing against the other:

```text
a = ∑ i, φ (a * y i) • x i,        a = ∑ i, φ (x i * a) • y i.
```

For a finite free symmetric Frobenius algebra, a basis and its dual basis give such families;
the expansion identities also allow redundant families. The **Casimir element** `∑ i, x i ⊗ y i`
of `A ⊗[k] A` then commutes with `A` in the bimodule sense:

```text
∑ i, (a * x i) ⊗ y i = ∑ i, x i ⊗ (y i * a).
```

This is what makes `1 ↦ ∑ i, x i ⊗ y i` a map of `A`-bimodules `A → A ⊗[k] A`, the coevaluation of
a symmetric Frobenius algebra; for a Frobenius coalgebra in Mathlib's sense
(`Coalgebra.IsFrobenius`) with counit `φ`, the element is the comultiplication of `1`.

The tensor identity itself needs only a `k`-module `A` with an associative multiplication.
No multiplicative identity, distributivity, or compatibility with scalar multiplication is needed.

-/

section Casimir

variable {k A : Type*} [CommSemiring k] [AddCommMonoid A] [Semigroup A] [Module k A]

/-- **The Casimir element of a trace commutes with multiplication.** If `φ` is a trace on `A`
and the finite families `x` and `y` are dual for `(a, b) ↦ φ (a * b)`, then
`∑ i, (a * x i) ⊗ y i = ∑ i, x i ⊗ (y i * a)` for every `a : A`. -/
theorem sum_mul_tmul_eq_sum_tmul_mul {ι : Type*} [Fintype ι] (φ : A →ₗ[k] k)
    (hφ : ∀ a b : A, φ (a * b) = φ (b * a)) {x y : ι → A}
    (hx : ∀ a : A, ∑ i, φ (a * y i) • x i = a) (hy : ∀ a : A, ∑ i, φ (x i * a) • y i = a)
    (a : A) :
    ∑ i, (a * x i) ⊗ₜ[k] y i = ∑ i, x i ⊗ₜ[k] (y i * a) := by
  -- Expand each `a * x i` in the family `x`; the coefficients then match those of the expansion
  -- of `y j * a` in the family `y`, by the trace property.
  have expand (i : ι) :
      (a * x i) ⊗ₜ[k] y i = ∑ j, x j ⊗ₜ[k] (φ (x i * (y j * a)) • y i) := by
    conv_lhs => rw [← hx (a * x i)]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul, mul_assoc, hφ, mul_assoc]
  simp_rw [expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← TensorProduct.tmul_sum, hy]

end Casimir

end LinearMap

namespace TensorProduct

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A pure tensor with a multiset sum in its right factor is the sum of the pure tensors. This is
the multiset version of `TensorProduct.tmul_sum`. -/
theorem tmul_multiset_sum (m : M) (s : Multiset N) :
    m ⊗ₜ[R] s.sum = (s.map (m ⊗ₜ[R] ·)).sum :=
  map_multiset_sum (mk R M N m) s

/-- A pure tensor with a multiset sum in its left factor is the sum of the pure tensors. This is
the multiset version of `TensorProduct.sum_tmul`. -/
theorem multiset_sum_tmul (s : Multiset M) (n : N) :
    s.sum ⊗ₜ[R] n = (s.map (· ⊗ₜ[R] n)).sum :=
  map_multiset_sum ((mk R M N).flip n) s

/-- If a finite family `n` spans `N`, then every element of `M ⊗[R] N` is `∑ j, mⱼ ⊗ nⱼ` for some
family `m` of elements of `M`. -/
theorem exists_eq_sum_tmul_of_span_eq_top {κ : Type*} [Fintype κ] {n : κ → N}
    (hn : Submodule.span R (Set.range n) = ⊤) (x : M ⊗[R] N) :
    ∃ m : κ → M, x = ∑ j, m j ⊗ₜ[R] n j := by
  induction x with
  | zero => exact ⟨0, by simp⟩
  | tmul a y =>
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
      (hn ▸ Submodule.mem_top : y ∈ Submodule.span R (Set.range n))
    exact ⟨fun j ↦ c j • a, by simp [tmul_sum, smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨m', rfl⟩ := hy
    exact ⟨m + m', by simp [add_tmul, Finset.sum_add_distrib]⟩

/-- Negating the left map of `TensorProduct.map` negates the tensor-product map. -/
@[simp]
theorem map_neg_left {R₁ R₂ M N M₂ N₂ : Type*} [CommSemiring R₁] [CommSemiring R₂]
    {σ₁₂ : R₁ →+* R₂} [AddCommMonoid M] [Module R₁ M] [AddCommMonoid N] [Module R₁ N]
    [AddCommGroup M₂] [Module R₂ M₂] [AddCommMonoid N₂] [Module R₂ N₂]
    (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    map (-f) g = -map f g := by
  simpa only [LinearMap.flip_apply, mapBilinear_apply] using
    map_neg ((mapBilinear σ₁₂ M N M₂ N₂).flip g) f

/-- Negating the right map of `TensorProduct.map` negates the tensor-product map. -/
@[simp]
theorem map_neg_right {R₁ R₂ M N M₂ N₂ : Type*} [CommSemiring R₁] [CommSemiring R₂]
    {σ₁₂ : R₁ →+* R₂} [AddCommMonoid M] [Module R₁ M] [AddCommMonoid N] [Module R₁ N]
    [AddCommGroup M₂] [Module R₂ M₂] [AddCommGroup N₂] [Module R₂ N₂]
    (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    map f (-g) = -map f g := by
  simpa only [mapBilinear_apply] using map_neg (mapBilinear σ₁₂ M N M₂ N₂ f) g

variable {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/-- Exchanging the factors of both arguments of `tensorTensorTensorComm` exchanges the factors of
its value: `(n ⊗ m) ⊗ (q ⊗ p) ↦ (n ⊗ q) ⊗ (m ⊗ p)` is the exchange of
`(m ⊗ n) ⊗ (p ⊗ q) ↦ (m ⊗ p) ⊗ (n ⊗ q)`. -/
theorem tensorTensorTensorComm_comm_tmul_comm (x : M ⊗[R] N) (y : P ⊗[R] Q) :
    tensorTensorTensorComm R N M Q P (TensorProduct.comm R M N x ⊗ₜ TensorProduct.comm R P Q y) =
      TensorProduct.comm R _ _ (tensorTensorTensorComm R M N P Q (x ⊗ₜ y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' h h' => simp only [map_add, add_tmul, h, h']
  | tmul m n =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => simp only [map_add, tmul_add, h, h']
    | tmul p q => simp

variable {O S : Type*} [AddCommMonoid O] [Module R O] [AddCommMonoid S] [Module R S]

/-- **Reassociating both arguments of `tensorTensorTensorComm` reassociates its value.** The
rearrangement `((m ⊗ n) ⊗ o) ⊗ ((p ⊗ q) ⊗ s) ↦ (m ⊗ p) ⊗ ((n ⊗ q) ⊗ (o ⊗ s))`, applying
`tensorTensorTensorComm` to the outer factors, then to the first, and reassociating, agrees with
reassociating both arguments, `(m ⊗ (n ⊗ o)) ⊗ (p ⊗ (q ⊗ s))`, and then applying
`tensorTensorTensorComm` to the outer factors and to the second. -/
theorem assoc_rTensor_tensorTensorTensorComm_tmul (x : (M ⊗[R] N) ⊗[R] O)
    (y : (P ⊗[R] Q) ⊗[R] S) :
    TensorProduct.assoc R _ _ _ ((tensorTensorTensorComm R M N P Q).toLinearMap.rTensor _
        (tensorTensorTensorComm R _ O _ S (x ⊗ₜ y))) =
      (tensorTensorTensorComm R N O Q S).toLinearMap.lTensor _
        (tensorTensorTensorComm R M _ P _
          (TensorProduct.assoc R M N O x ⊗ₜ TensorProduct.assoc R P Q S y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' h h' => simp only [map_add, add_tmul, h, h']
  | tmul mn o =>
    induction mn using TensorProduct.induction_on with
    | zero => simp
    | add z z' h h' => simp only [map_add, add_tmul, h, h']
    | tmul m n =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add, tmul_add, h, h']
      | tmul pq s =>
        induction pq using TensorProduct.induction_on with
        | zero => simp
        | add z z' h h' => simp only [map_add, add_tmul, tmul_add, h, h']
        | tmul p q => simp

variable {X Y X' Y' : Type*} [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
  [AddCommMonoid X'] [Module R X'] [AddCommMonoid Y'] [Module R Y']

/-- **`TensorProduct.assoc_rTensor_tensorTensorTensorComm_tmul` after maps into the first two
factors.** Let `p : X → M ⊗ N`, `q : Y → P ⊗ Q`, `p' : X' → N ⊗ O` and `q' : Y' → Q ⊗ S`, and let
`x`, `y`, `x'`, `y'` be tensors whose images under `p ⊗ 1` and `q ⊗ 1`, reassociated, are the
images of `x'` and `y'` under `1 ⊗ p'` and `1 ⊗ q'`. Then rearranging `x ⊗ y` by
`tensorTensorTensorComm` and applying `tensorTensorTensorComm ∘ (p ⊗ q)` to the first factor gives,
after reassociation, the rearrangement of `x' ⊗ y'` with `tensorTensorTensorComm ∘ (p' ⊗ q')`
applied to the second factor. -/
theorem assoc_rTensor_comp_map_tensorTensorTensorComm_tmul {p : X →ₗ[R] M ⊗[R] N}
    {q : Y →ₗ[R] P ⊗[R] Q} {p' : X' →ₗ[R] N ⊗[R] O} {q' : Y' →ₗ[R] Q ⊗[R] S}
    {x : X ⊗[R] O} {y : Y ⊗[R] S} {x' : M ⊗[R] X'} {y' : P ⊗[R] Y'}
    (hx : TensorProduct.assoc R M N O (p.rTensor O x) = p'.lTensor M x')
    (hy : TensorProduct.assoc R P Q S (q.rTensor S y) = q'.lTensor P y') :
    TensorProduct.assoc R _ _ _
        (((tensorTensorTensorComm R M N P Q).toLinearMap ∘ₗ map p q).rTensor _
          (tensorTensorTensorComm R X O Y S (x ⊗ₜ y))) =
      ((tensorTensorTensorComm R N O Q S).toLinearMap ∘ₗ map p' q').lTensor _
        (tensorTensorTensorComm R M X' P Y' (x' ⊗ₜ y')) := by
  -- Move `p ⊗ q` and `p' ⊗ q'` inside the rearrangements (`tensorTensorTensorComm_comp_map`).
  have hl : (map p q).rTensor (O ⊗[R] S) (tensorTensorTensorComm R X O Y S (x ⊗ₜ y)) =
      tensorTensorTensorComm R _ O _ S (p.rTensor O x ⊗ₜ q.rTensor S y) := by
    have := LinearMap.congr_fun (tensorTensorTensorComm_comp_map R p LinearMap.id q LinearMap.id)
      (x ⊗ₜ y)
    simpa [map_id, LinearMap.rTensor_def] using this.symm
  have hr : (map p' q').lTensor (M ⊗[R] P) (tensorTensorTensorComm R M X' P Y' (x' ⊗ₜ y')) =
      tensorTensorTensorComm R M _ P _ (p'.lTensor M x' ⊗ₜ q'.lTensor P y') := by
    have := LinearMap.congr_fun (tensorTensorTensorComm_comp_map R LinearMap.id p' LinearMap.id q')
      (x' ⊗ₜ y')
    simpa [map_id, LinearMap.lTensor_def] using this.symm
  rw [LinearMap.rTensor_comp_apply, hl, assoc_rTensor_tensorTensorTensorComm_tmul, hx, hy,
    LinearMap.lTensor_comp_apply, hr]

/-- If `M ⊗[R] N` is nontrivial then so is `N`: were `N` trivial, the tensor product would be
trivial too (`TensorProduct.uniqueRight`). -/
theorem nontrivial_right [Nontrivial (M ⊗[R] N)] : Nontrivial N :=
  not_subsingleton_iff_nontrivial.1 fun _ =>
    not_subsingleton (M ⊗[R] N) uniqueRight.instSubsingleton

variable (M) in
/-- The map `M → A ⊗[R] M`, `m ↦ 1 ⊗ m`, is `(Algebra.linearMap R A).rTensor M` composed with the
identification `M ≃ R ⊗[R] M`. -/
theorem mk_one_eq_rTensor_comp_lid_symm (A : Type*) [Semiring A] [Algebra R A] :
    mk R A M 1 = (Algebra.linearMap R A).rTensor M ∘ₗ (TensorProduct.lid R M).symm.toLinearMap := by
  ext
  simp

variable (M) in
/-- The map `M → A ⊗[R] M`, `m ↦ 1 ⊗ m`, is injective iff `(Algebra.linearMap R A).rTensor M`
is. -/
theorem injective_mk_one_iff (A : Type*) [Semiring A] [Algebra R A] :
    Function.Injective (mk R A M 1) ↔ Function.Injective ((Algebra.linearMap R A).rTensor M) := by
  rw [mk_one_eq_rTensor_comp_lid_symm, LinearMap.coe_comp, LinearEquiv.coe_coe,
    EquivLike.injective_comp]

section CompatibleSMul

variable {K : Type*} [CommSemiring K] [Algebra R K] [Module K M] [Module K N] [IsScalarTower R K N]
  [Module K P]

/-- If `K`-balanced and `R`-balanced tensors agree in `M ⊗[R] N`, they agree in
`M ⊗[R] (N ⊗[K] P)`, where `K` acts on `N ⊗[K] P` through `N`. -/
-- A pure tensor `n ⊗ p` of `N ⊗[K] P` is the image of `n` under the `K`-linear map `· ⊗ p`.
instance CompatibleSMul.tensorProduct [CompatibleSMul R K M N] :
    CompatibleSMul R K M (N ⊗[K] P) where
  smul_tmul k m t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [smul_add, tmul_add, hs, ht]
    | tmul n p =>
      rw [smul_tmul']
      exact congrArg (LinearMap.lTensor M (((TensorProduct.mk K N P).flip p).restrictScalars R))
        (TensorProduct.smul_tmul (R := R) k m n)

end CompatibleSMul

/-- The tensor product of linear maps is additive in its left factor, over a finite sum. -/
theorem map_sum_left {ι : Type*} (s : Finset ι) (f : ι → M →ₗ[R] P) (g : N →ₗ[R] Q) :
    map (∑ i ∈ s, f i) g = ∑ i ∈ s, map (f i) g := by
  simp only [← mapBilinear_apply, map_sum, LinearMap.sum_apply]

/-- The tensor product of linear maps is additive in its right factor, over a finite sum. -/
theorem map_sum_right {ι : Type*} (s : Finset ι) (f : M →ₗ[R] P) (g : ι → N →ₗ[R] Q) :
    map f (∑ i ∈ s, g i) = ∑ i ∈ s, map f (g i) := by
  simp only [← mapBilinear_apply, map_sum]

end TensorProduct

namespace TensorProduct

variable {R M N P Q : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- The tensor product of linear maps is subtractive in its left factor. -/
theorem map_sub_left [AddCommGroup P] [Module R P] [AddCommMonoid Q] [Module R Q]
    (f₁ f₂ : M →ₗ[R] P) (g : N →ₗ[R] Q) : map (f₁ - f₂) g = map f₁ g - map f₂ g := by
  simp only [← mapBilinear_apply, map_sub, LinearMap.sub_apply]

/-- `TensorProduct.map_sub_left`, applied to an element.  This form only uses subtraction in
`P ⊗[R] Q`, so it also applies where the linear endomorphisms of a tensor product have no
synthesizable subtraction, as for the tensor square of a direct sum. -/
theorem map_sub_left_apply [AddCommGroup P] [Module R P] [AddCommMonoid Q] [Module R Q]
    (f₁ f₂ : M →ₗ[R] P) (g : N →ₗ[R] Q) (z : M ⊗[R] N) :
    map (f₁ - f₂) g z = map f₁ g z - map f₂ g z := by
  rw [map_sub_left, LinearMap.sub_apply]

/-- The tensor product of linear maps is subtractive in its right factor.  The left target is an
additive group too, since Mathlib's negation on `P ⊗[R] Q` comes from the left factor. -/
theorem map_sub_right [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] P) (g₁ g₂ : N →ₗ[R] Q) : map f (g₁ - g₂) = map f g₁ - map f g₂ := by
  simp only [← mapBilinear_apply, map_sub]

/-- `TensorProduct.map_sub_right`, applied to an element. -/
theorem map_sub_right_apply [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] P) (g₁ g₂ : N →ₗ[R] Q) (z : M ⊗[R] N) :
    map f (g₁ - g₂) z = map f g₁ z - map f g₂ z := by
  rw [map_sub_right, LinearMap.sub_apply]

end TensorProduct

end

section
-- MODULE RingTheory/TensorProduct/Maps
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/







/-!
# Maps between tensor products of algebras

The base change `Algebra.TensorProduct.map (AlgHom.id R S) f : S ⊗[R] B → S ⊗[R] C` of an
algebra map `f : B →ₐ[R] C` agrees with `LinearMap.lTensor S` applied to the underlying
linear map of `f`, and similarly on the right with `LinearMap.rTensor S`. This lets results
about base change of linear maps, such as flatness preserving injectivity and exactness, be
applied to base change of algebra maps.

For an `S`-algebra `B` over `R` which need not be commutative, the multiplication maps
`S ⊗[R] B → B` and `B ⊗[R] S → B` are `S`-algebra maps, because `S` acts through its central
image in `B`. Mathlib's `Algebra.TensorProduct.lmul''` and `Algebra.TensorProduct.productMap`
require a commutative target.

For commutative `R`-algebras `A` and `B`, the tensor product `A ⊗[R] B` is the pushout of
`A ← R → B` in commutative semirings. Mathlib's `Algebra.TensorProduct.productMap` expresses this
universal property for algebra homomorphisms into an `R`-algebra, and
`Algebra.TensorProduct.ringHom_ext` is its uniqueness half for ring homomorphisms.
`Algebra.TensorProduct.liftRingHomOfCommute` is the existence half for ring homomorphisms: ring
homomorphisms `x : A →+* T` and `y : B →+* T` which agree on `R` and have commuting images
induce `a ⊗ b ↦ x a * y b`, for any semirings `A`, `B` and `T`, with no `R`-algebra structure
on `T` involved; `Algebra.TensorProduct.liftRingHom` is its case of a commutative `T`. This is
the form needed when `T` already carries an `R`-algebra structure which `x` and `y` do not
respect, for instance when `T` is itself a tensor product over `R` and `x` twists the first
factor by a ring automorphism.

Mathlib's `LinearMap.tensorProduct` and `LinearMap.tensorProductEnd` send `a ⊗ f` to `a` times the
base change of `f`, but their generated computation lemmas unfold to `TensorProduct.liftAux`; this
file records their values on pure tensors as `simp` lemmas of higher priority than the generated
ones, so the public `LinearMap.baseChange` API applies.

## Main declarations

* `Subalgebra.toSubmodule_baseChange`: the underlying submodule of `C.baseChange T` is
  `(Subalgebra.toSubmodule C).baseChange T`.
* `Subalgebra.baseChange_bot`: the base change of the bottom subalgebra is the bottom subalgebra.
* `AlgHom.lTensor_toLinearMap_apply`: `f.toLinearMap.lTensor S` is
  `Algebra.TensorProduct.map (AlgHom.id R S) f`.
* `AlgHom.rTensor_toLinearMap_apply`: `f.toLinearMap.rTensor S` is
  `Algebra.TensorProduct.map f (AlgHom.id R S)`.
* `AlgHom.lTensor_rTensor_comm`: scalar extension of an algebra map commutes with changing the
  coefficient algebra.
* `LinearMap.tensorProduct_tmul`, `LinearMap.tensorProductEnd_tmul`: the extension of linear maps
  and of endomorphisms sends `a ⊗ f` to `a • f.baseChange A`.
* `Algebra.TensorProduct.mulLeft`, `Algebra.TensorProduct.mulRight`: the
  multiplication maps `s ⊗ b ↦ s • b` and `b ⊗ t ↦ b * t`.
* `Algebra.TensorProduct.liftRingHomOfCommute x y h hxy`: the ring homomorphism
  `a ⊗ b ↦ x a * y b` for ring homomorphisms with commuting images, and
  `Algebra.TensorProduct.liftRingHom x y h` for a commutative target.
* `Algebra.TensorProduct.map_productMap_eq_zero_of_comp_eq`: if `p : T → U` equalizes
  `f, g : S → T`, then `p` kills `productMap f g e` (`s ⊗ t ↦ f s * g t`) for every `e` in the
  kernel of multiplication `S ⊗[R] S → S`.
* `Algebra.TensorProduct.productMap_mem_of_comp_eq`: if `f, g` agree modulo an ideal `J` of `T`,
  then `productMap f g e ∈ J` for every such `e`.
* `AlgHom.productMap_comp_includeLeft_includeRight`: an algebra map `g` out of `H₁ ⊗[R] H₂` is
  the `productMap` of its restrictions along the two canonical inclusions; `H₁` and `H₂` need not
  be commutative.
* `Algebra.TensorProduct.mulLeft_map`, `Algebra.TensorProduct.mulLeft_map_includeRight`:
  naturality of tensor multiplication and cancellation of an inserted middle factor `1`.
* `Algebra.TensorProduct.map_rTensor_eq_rTensor_lTensor`: `g ⊗ φ` after `f ⊗ id` is
  `(g ∘ f) ⊗ id` after `id ⊗ φ`, for algebra maps `g, φ` and a linear map `f`.
* `Algebra.TensorProduct.map_assoc_tmul_one`: applying `f : B ⊗[R] C → D` after
  reassociating `y ⊗ 1` is the base change of `b ↦ f (b ⊗ 1)`.
* `Algebra.TensorProduct.assoc_comp_includeLeft_comp_includeLeft`,
  `Algebra.TensorProduct.assoc_comp_includeLeft_comp_includeRight`,
  `Algebra.TensorProduct.assoc_comp_includeRight`: the associator restricted to each of the three
  tensor factors.
* `Algebra.TensorProduct.mapRingHom_id_eq_map`, `Algebra.TensorProduct.mapRingHom_id_surjective`,
  `Algebra.TensorProduct.ker_mapRingHom_id`: over the identity of the base, `mapRingHom` is
  `Algebra.TensorProduct.map`; for surjective maps it is surjective, and its kernel is generated
  by the two kernels.
* `Algebra.TensorProduct.coe_rid`: the right unitor `A ⊗[R] R ≃ₐ[S] A` is, as a function, the
  linear right unitor over `R`, whatever the scalars `S`.
* `AlgHom.sectionBaseChange`: the base change `T ⊗[A] B →ₐ[T] T` of an `A`-algebra map
  `s : B →ₐ[A] A`, that is, the pullback to `Spec T` of the section of `Spec B → Spec A` given by
  `s`, with its value `AlgHom.sectionBaseChange_sum_tmul` on sums of pure tensors, its
  naturality `AlgHom.sectionBaseChange_rTensor` in `T`, and its transitivity
  `AlgHom.sectionBaseChange_sectionBaseChange` along `A → A' → T`.
* `AlgHom.semilinearTwist y σ φ hφ`: the twist `(σ⁻¹ ⊗ T) ∘ y ∘ φ` of an algebra map
  `y : D →ₐ[C] C ⊗[A] T` by a ring homomorphism `φ` semilinear over an automorphism `σ` of `C`.
-/


open TensorProduct

/-- The underlying submodule of a base-changed subalgebra is the base change of its
underlying submodule. -/
theorem Subalgebra.toSubmodule_baseChange {R S : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] (T : Type*) [CommSemiring T] [Algebra R T] (C : Subalgebra R S) :
    Subalgebra.toSubmodule (C.baseChange T) = (Subalgebra.toSubmodule C).baseChange T :=
  -- Both ranges use the tensor map induced by the identity on `T` and the inclusion of `C`.
  -- The algebra tensor map and the base change of the linear inclusion have the same function.
  rfl

/-- The base change of the bottom subalgebra is the bottom subalgebra: `t ⊗ r = (r t) ⊗ 1` for
`r` in the image of `R`. -/
@[simp]
theorem Subalgebra.baseChange_bot {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (T : Type*) [CommSemiring T] [Algebra R T] :
    (⊥ : Subalgebra R S).baseChange T = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t s =>
    obtain ⟨r, hr⟩ := Algebra.mem_bot.1 s.property
    have : t ⊗ₜ[R] (s : S) = algebraMap T (T ⊗[R] S) (r • t) := by
      rw [← hr, Algebra.algebraMap_eq_smul_one, ← smul_tmul,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
    simpa [this] using (⊥ : Subalgebra T (T ⊗[R] S)).algebraMap_mem (r • t)
  | add x y hx hy => simpa using add_mem hx hy

/-- Base change of the underlying linear map of an algebra map is the base change of the
algebra map. -/
theorem AlgHom.lTensor_toLinearMap_apply {R B C : Type*} (S : Type*) [CommSemiring R]
    [Semiring S] [Algebra R S] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (f : B →ₐ[R] C) (x : S ⊗[R] B) :
    f.toLinearMap.lTensor S x = Algebra.TensorProduct.map (AlgHom.id R S) f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => simp
  | add x y hx hy => simp [hx, hy]

/-- Right base change of the underlying linear map of an algebra map is the right base change of
the algebra map. -/
theorem AlgHom.rTensor_toLinearMap_apply {R B C : Type*} (S : Type*) [CommSemiring R]
    [Semiring S] [Algebra R S] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (f : B →ₐ[R] C) (x : B ⊗[R] S) :
    f.toLinearMap.rTensor S x = Algebra.TensorProduct.map f (AlgHom.id R S) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b s => simp
  | add x y hx hy => simp [hx, hy]

/-- The natural map `A ⊗[R] (M →ₗ[R] N) → (A ⊗[R] M →ₗ[A] A ⊗[R] N)` sends `a ⊗ f` to
`a • f.baseChange A`, so that `LinearMap.baseChange_tmul` computes its values on pure tensors. -/
@[simp]
theorem LinearMap.tensorProduct_tmul {R A M N : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (a : A)
    (f : M →ₗ[R] N) : LinearMap.tensorProduct R A M N (a ⊗ₜ f) = a • f.baseChange A := by
  simp only [LinearMap.tensorProduct_apply, TensorProduct.liftAux_tmul,
    LinearMap.coe_restrictScalars, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    LinearMap.baseChangeHom_apply]

/-- The natural algebra map `A ⊗[R] Module.End R M → Module.End A (A ⊗[R] M)` sends `a ⊗ f` to
`a • f.baseChange A`. -/
@[simp]
theorem LinearMap.tensorProductEnd_tmul {R A M : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] (a : A) (f : Module.End R M) :
    LinearMap.tensorProductEnd R A M (a ⊗ₜ f) = a • f.baseChange A :=
  LinearMap.tensorProduct_tmul a f

/-- Extension of scalars of an algebra map commutes with changing the coefficient algebra. -/
theorem AlgHom.lTensor_rTensor_comm {R B C D E : Type*} [CommSemiring R]
    [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C]
    [Semiring D] [Algebra R D] [Semiring E] [Algebra R E]
    (φ : D →ₐ[R] E) (ρ : B →ₐ[R] C) (x : B ⊗[R] D) :
    Algebra.TensorProduct.lTensor (S := C) C φ (Algebra.TensorProduct.rTensor D ρ x) =
      Algebra.TensorProduct.rTensor E ρ (Algebra.TensorProduct.lTensor (S := B) B φ x) := by
  have hC : (Algebra.TensorProduct.lTensor (S := C) C φ).restrictScalars R =
      Algebra.TensorProduct.map (AlgHom.id R C) φ := by ext <;> simp
  have hB : (Algebra.TensorProduct.lTensor (S := B) B φ).restrictScalars R =
      Algebra.TensorProduct.map (AlgHom.id R B) φ := by ext <;> simp
  rw [← AlgHom.coe_restrictScalars' R (Algebra.TensorProduct.lTensor (S := C) C φ), hC,
    ← AlgHom.coe_restrictScalars' R (Algebra.TensorProduct.lTensor (S := B) B φ), hB,
    ← AlgHom.lTensor_toLinearMap_apply, ← AlgHom.lTensor_toLinearMap_apply,
    Algebra.TensorProduct.rTensor, Algebra.TensorProduct.rTensor,
    ← AlgHom.rTensor_toLinearMap_apply, ← AlgHom.rTensor_toLinearMap_apply]
  exact LinearMap.lTensor_rTensor_comm ρ.toLinearMap φ.toLinearMap x

namespace Algebra.TensorProduct

section LiftRingHomOfCommute

variable {R A B T : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
  [Algebra R B] [Semiring T]

/-- The ring homomorphism `A ⊗[R] B →+* T`, `a ⊗ b ↦ x a * y b`, induced by ring homomorphisms
`x : A →+* T` and `y : B →+* T` which agree on `R` and have commuting images. This is the
ring-homomorphism form of `Algebra.TensorProduct.lift`: no `R`-algebra structure on `T` is
involved, and `T` need not be commutative. -/
noncomputable def liftRingHomOfCommute (x : A →+* T) (y : B →+* T)
    (h : x.comp (algebraMap R A) = y.comp (algebraMap R B))
    (hxy : ∀ a b, Commute (x a) (y b)) : A ⊗[R] B →+* T :=
  let C := Subsemiring.centralizer (Set.range (x.comp (algebraMap R A)))
  let x' : A →+* C := x.codRestrict C fun a ↦ by
    rintro _ ⟨r, rfl⟩
    exact ((Algebra.commute_algebraMap_left r a).map x).eq
  let y' : B →+* C := y.codRestrict C fun b ↦ by
    rintro _ ⟨r, rfl⟩
    have hr : x (algebraMap R A r) = y (algebraMap R B r) := congr($h r)
    rw [RingHom.comp_apply, hr]
    exact ((Algebra.commute_algebraMap_left r b).map y).eq
  letI : Algebra R C := (x'.comp (algebraMap R A)).toAlgebra' fun r c ↦
    Subtype.ext (c.property _ ⟨r, rfl⟩)
  C.subtype.comp (lift (S := R) { x' with commutes' := fun _ ↦ rfl }
    { y' with commutes' := fun r ↦ Subtype.ext (congr($h r).symm) }
    fun a b ↦ Subtype.ext (hxy a b).eq).toRingHom

variable (x : A →+* T) (y : B →+* T) (h : x.comp (algebraMap R A) = y.comp (algebraMap R B))
  (hxy : ∀ a b, Commute (x a) (y b))

@[simp]
theorem liftRingHomOfCommute_tmul (a : A) (b : B) :
    liftRingHomOfCommute x y h hxy (a ⊗ₜ b) = x a * y b := by
  -- `lift_tmul` gives `x' a * y' b` in the centralizer, whose subtype coercion is `x a * y b`.
  unfold liftRingHomOfCommute
  rfl

@[simp]
theorem liftRingHomOfCommute_comp_includeLeftRingHom :
    (liftRingHomOfCommute x y h hxy).comp includeLeftRingHom = x := by
  ext a
  simp

@[simp]
theorem liftRingHomOfCommute_comp_includeRight :
    (liftRingHomOfCommute x y h hxy).comp (includeRight : B →ₐ[R] A ⊗[R] B) = y := by
  ext b
  simp

end LiftRingHomOfCommute

section LiftRingHom

variable {R A B T : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
  [Algebra R B] [CommSemiring T]

/-- The ring homomorphism `A ⊗[R] B →+* T`, `a ⊗ b ↦ x a * y b`, induced by ring homomorphisms
`x : A →+* T` and `y : B →+* T` into a commutative semiring which agree on `R`: the case of
`liftRingHomOfCommute` where the images commute automatically. The sources `A` and `B` need not
be commutative, and no `R`-algebra structure on `T` is involved. -/
noncomputable def liftRingHom (x : A →+* T) (y : B →+* T)
    (h : x.comp (algebraMap R A) = y.comp (algebraMap R B)) : A ⊗[R] B →+* T :=
  liftRingHomOfCommute x y h fun _ _ ↦ .all _ _

variable (x : A →+* T) (y : B →+* T) (h : x.comp (algebraMap R A) = y.comp (algebraMap R B))

@[simp]
theorem liftRingHom_tmul (a : A) (b : B) : liftRingHom x y h (a ⊗ₜ b) = x a * y b := by
  simp [liftRingHom]

@[simp]
theorem liftRingHom_comp_includeLeftRingHom :
    (liftRingHom x y h).comp includeLeftRingHom = x := by
  ext a
  simp

@[simp]
theorem liftRingHom_comp_includeRight :
    (liftRingHom x y h).comp (includeRight : B →ₐ[R] A ⊗[R] B) = y := by
  ext b
  simp

end LiftRingHom

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R A]
  [Semiring B] [Algebra R B]

/-- Reassociating `y ⊗ 1 ∈ (A ⊗[R] B) ⊗[R] C` and applying `f : B ⊗[R] C → D` to the last two
factors is the base change of `b ↦ f (b ⊗ 1)`. -/
theorem map_assoc_tmul_one {C D : Type*} [Semiring C] [Algebra R C] [Semiring D] [Algebra R D]
    (f : B ⊗[R] C →ₐ[R] D) (y : A ⊗[R] B) :
    map (AlgHom.id R A) f (Algebra.TensorProduct.assoc R R R A B C (y ⊗ₜ 1)) =
      map (AlgHom.id R A) (f.comp includeLeft) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

/-- Applying `g ⊗ φ` after `f ⊗ id`, for algebra maps `g, φ` and a linear map `f` into the source
of `g`, is applying `id ⊗ φ` and then `(g ∘ f) ⊗ id`. For `g` the identity this lets tensor
constructions on the image of `f` pass through a change of the coefficient algebra. -/
theorem map_rTensor_eq_rTensor_lTensor {M C D : Type*} [AddCommMonoid M] [Module R M]
    [Semiring C] [Algebra R C] [Semiring D] [Algebra R D] (g : A →ₐ[R] C) (φ : B →ₐ[R] D)
    (f : M →ₗ[R] A) (z : M ⊗[R] B) :
    map g φ (f.rTensor B z) = (g.toLinearMap ∘ₗ f).rTensor D (φ.toLinearMap.lTensor M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

section AssocInclude

variable {C : Type*} [Semiring C] [Algebra R C]

/-- Restricting the associator `(A ⊗[R] B) ⊗[R] C ≃ A ⊗[R] (B ⊗[R] C)` to the left factor `A`
gives the inclusion of the left factor. -/
theorem assoc_comp_includeLeft_comp_includeLeft :
    (((Algebra.TensorProduct.assoc R R R A B C).toAlgHom.comp includeLeft).comp includeLeft :
      A →ₐ[R] A ⊗[R] (B ⊗[R] C)) = includeLeft :=
  AlgHom.ext fun _ ↦ rfl

/-- Restricting the associator `(A ⊗[R] B) ⊗[R] C ≃ A ⊗[R] (B ⊗[R] C)` to the middle factor `B`
gives the inclusion of `B` into the left factor of `B ⊗[R] C`. -/
theorem assoc_comp_includeLeft_comp_includeRight :
    (((Algebra.TensorProduct.assoc R R R A B C).toAlgHom.comp includeLeft).comp includeRight :
      B →ₐ[R] A ⊗[R] (B ⊗[R] C)) = includeRight.comp includeLeft :=
  AlgHom.ext fun _ ↦ rfl

/-- Restricting the associator `(A ⊗[R] B) ⊗[R] C ≃ A ⊗[R] (B ⊗[R] C)` to the right factor `C`
gives the inclusion of `C` into the right factor of `B ⊗[R] C`. -/
theorem assoc_comp_includeRight :
    ((Algebra.TensorProduct.assoc R R R A B C).toAlgHom.comp includeRight :
      C →ₐ[R] A ⊗[R] (B ⊗[R] C)) = includeRight.comp includeRight :=
  AlgHom.ext fun _ ↦ rfl

end AssocInclude

variable [Algebra S B]

variable [Algebra R S] [IsScalarTower R S B]

/-- The multiplication map `S ⊗[R] B →ₐ[S] B`, `s ⊗ b ↦ s • b`, for an `S`-algebra `B` which
need not be commutative. -/
noncomputable def mulLeft : S ⊗[R] B →ₐ[S] B :=
  lift (Algebra.ofId S B) (AlgHom.id R B)
    (fun s b ↦ by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left s _)

@[simp]
theorem mulLeft_tmul (s : S) (b : B) :
    (mulLeft (s ⊗ₜ[R] b) : B) = algebraMap S B s * b := by
  simp [mulLeft]

/-- Tensor multiplication commutes with an algebra map over `S`. -/
@[simp]
theorem mulLeft_map {C : Type*} [Semiring C] [Algebra R C] [Algebra S C]
    [IsScalarTower R S C] (f : B →ₐ[S] C) (x : S ⊗[R] B) :
    mulLeft (map (AlgHom.id R S) (f.restrictScalars R) x) = f (mulLeft x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Algebra S B] [IsScalarTower R S B] in
/-- Multiplying the first two factors cancels insertion of `1` in the middle factor. -/
@[simp]
theorem mulLeft_map_includeRight (x : S ⊗[R] B) :
    mulLeft (map (AlgHom.id R S) (includeRight : B →ₐ[R] S ⊗[R] B) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => simp [algebraMap_apply, tmul_mul_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The multiplication map `B ⊗[R] S →ₐ[S] B`, `b ⊗ t ↦ b * t`, for an `S`-algebra `B` which
need not be commutative. -/
noncomputable def mulRight : B ⊗[R] S →ₐ[S] B :=
  lift (AlgHom.id S B) (IsScalarTower.toAlgHom R S B)
    (fun b t ↦ by rw [IsScalarTower.coe_toAlgHom']; exact Algebra.commute_algebraMap_right t b)

@[simp]
theorem mulRight_tmul (b : B) (t : S) :
    (mulRight (b ⊗ₜ[R] t) : B) = b * algebraMap S B t := by
  simp [mulRight]

/-- Multiplication on a self-tensor product is natural in the algebra. -/
@[simp]
theorem lmul'_map_self {R A C : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring C] [Algebra R A] [Algebra R C] (f : A →ₐ[R] C) (x : A ⊗[R] A) :
    lmul' R (map f f x) = f (lmul' R x) := by
  have h : (lmul' R).comp (map f f) = f.comp (lmul' R) := by ext <;> simp
  exact DFunLike.congr_fun h x

section Product

/-- If two algebra maps `f, g : S → T` agree after composing with `p : T → U`, then `p` kills
`productMap f g e` (the map `s ⊗ t ↦ f s * g t` applied to `e`) for every element `e` of the
kernel of multiplication `S ⊗[R] S → S`. -/
theorem map_productMap_eq_zero_of_comp_eq {R S T U : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring T] [Semiring U] [Algebra R S] [Algebra R T] [Algebra R U]
    {e : S ⊗[R] S} (he : lmul' R e = 0)
    {f g : S →ₐ[R] T} (p : T →ₐ[R] U) (hfg : p.comp f = p.comp g) :
    p (productMap f g e) = 0 := by
  have hp : p.comp (productMap f g) =
      (p.comp f).comp (lmul' R) := by
    ext s
    · simp
    · simpa using DFunLike.congr_fun hfg.symm s
  simpa only [AlgHom.comp_apply, he, map_zero] using DFunLike.congr_fun hp e

/-- If two algebra maps `f, g : S → T` agree modulo an ideal `J` of `T`, then `productMap f g`
(the map `s ⊗ t ↦ f s * g t`) sends every element of the kernel of multiplication
`S ⊗[R] S → S` into `J`. -/
theorem productMap_mem_of_comp_eq {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommRing T]
    [Algebra R S] [Algebra R T]
    {e : S ⊗[R] S} (he : lmul' R e = 0) (J : Ideal T)
    {f g : S →ₐ[R] T}
    (hfg : (Ideal.Quotient.mkₐ R J).comp f = (Ideal.Quotient.mkₐ R J).comp g) :
    productMap f g e ∈ J :=
  Ideal.Quotient.eq_zero_iff_mem.mp
    (map_productMap_eq_zero_of_comp_eq he (Ideal.Quotient.mkₐ R J) hfg)

end Product

section MapRingHom

section CommSemiring

variable {R S S' T T' : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring S']
  [CommSemiring T] [CommSemiring T'] [Algebra R S] [Algebra R S'] [Algebra R T] [Algebra R T']
  {fS : S →+* S'} {fT : T →+* T'} (HS : fS.comp (algebraMap R S) = algebraMap R S')
  (HT : fT.comp (algebraMap R T) = algebraMap R T')

/-- Over the identity of `R`, the ring homomorphism `mapRingHom` of ring homomorphisms commuting
with the structure maps is `Algebra.TensorProduct.map` of the corresponding `R`-algebra maps. -/
theorem mapRingHom_id_eq_map :
    mapRingHom (RingHom.id R) fS fT HS HT =
      (map ({ fS with commutes' := RingHom.congr_fun HS } : S →ₐ[R] S')
        ({ fT with commutes' := RingHom.congr_fun HT } : T →ₐ[R] T') : S ⊗[R] T →+* S' ⊗[R] T') :=
  ringHom_ext (by ext; simp) (by ext; simp)

/-- `mapRingHom` of surjective ring homomorphisms over the identity of `R` is surjective. -/
theorem mapRingHom_id_surjective (hS : Function.Surjective fS) (hT : Function.Surjective fT) :
    Function.Surjective (mapRingHom (RingHom.id R) fS fT HS HT) := by
  rw [mapRingHom_id_eq_map HS HT, RingHom.coe_coe, ← AlgHom.coe_toLinearMap, toLinearMap_map,
    AlgebraTensorModule.map_eq]
  exact _root_.TensorProduct.map_surjective hS hT

end CommSemiring

variable {R S S' T T' : Type*} [CommRing R] [CommRing S] [CommRing S'] [CommRing T] [CommRing T']
  [Algebra R S] [Algebra R S'] [Algebra R T] [Algebra R T'] {fS : S →+* S'} {fT : T →+* T'}
  (HS : fS.comp (algebraMap R S) = algebraMap R S')
  (HT : fT.comp (algebraMap R T) = algebraMap R T')

/-- **Right exactness of the tensor product for ring homomorphisms.** The kernel of `mapRingHom`
of surjective ring homomorphisms `fS`, `fT` over the identity of `R` is generated by the images of
`ker fS` and `ker fT` (`Algebra.TensorProduct.map_ker`). -/
theorem ker_mapRingHom_id (hS : Function.Surjective fS) (hT : Function.Surjective fT) :
    RingHom.ker (mapRingHom (RingHom.id R) fS fT HS HT) =
      (RingHom.ker fS).map (includeLeft : S →ₐ[R] S ⊗[R] T) ⊔
        (RingHom.ker fT).map (includeRight : T →ₐ[R] S ⊗[R] T) := by
  rw [mapRingHom_id_eq_map HS HT, ← AlgHom.ker_coe, map_ker _ _ hS hT]
  -- the kernels of `fS` and `fT` as `R`-algebra maps are their kernels as ring maps
  rfl

end MapRingHom

/-- The right unitor `A ⊗[R] R ≃ A` is the same function whichever scalars `S` it is linear
over: it is the linear right unitor `a ⊗ r ↦ r • a` over `R`. -/
theorem coe_rid (R S A : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring A]
    [Algebra R A] [Algebra S A] [IsScalarTower R S A] :
    ⇑(Algebra.TensorProduct.rid R S A) = _root_.TensorProduct.rid R A := by
  funext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => simp
  | add x y hx hy => simp [hx, hy]

end Algebra.TensorProduct

namespace AlgHom

section ProductMap

variable {R H₁ H₂ A : Type*} [CommSemiring R] [Semiring H₁] [Semiring H₂] [CommSemiring A]
  [Algebra R H₁] [Algebra R H₂] [Algebra R A]

/-- An algebra map out of a tensor product is recovered from its two restrictions. -/
@[simp]
theorem productMap_comp_includeLeft_includeRight (g : H₁ ⊗[R] H₂ →ₐ[R] A) :
    Algebra.TensorProduct.productMap (g.comp Algebra.TensorProduct.includeLeft)
        (g.comp Algebra.TensorProduct.includeRight) = g :=
  Algebra.TensorProduct.ext' fun _ _ ↦ by simp [← map_mul]

end ProductMap

variable {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]

/-- The base change `T ⊗[A] B →ₐ[T] T`, `t ⊗ b ↦ t * s b`, of an `A`-algebra map
`s : B →ₐ[A] A`. Geometrically, `s` is a section of `Spec B → Spec A`, and this is its pullback
along `Spec T → Spec A`. -/
noncomputable def sectionBaseChange (s : B →ₐ[A] A) (T : Type*) [CommSemiring T] [Algebra A T] :
    T ⊗[A] B →ₐ[T] T :=
  Algebra.TensorProduct.productLeftAlgHom (AlgHom.id T T) ((Algebra.ofId A T).comp s)

@[simp]
theorem sectionBaseChange_tmul (s : B →ₐ[A] A) {T : Type*} [CommSemiring T] [Algebra A T] (t : T)
    (b : B) : s.sectionBaseChange T (t ⊗ₜ b) = t * algebraMap A T (s b) := by
  simp [sectionBaseChange]

/-- The base change of a section `s` takes `∑ j ∈ u, tⱼ ⊗ bⱼ` to `∑ j ∈ u, s(bⱼ) • tⱼ`; for
`tⱼ = Xⱼ` and a basis `b`, the generic element goes to the linear form with coefficients
`s(bⱼ)`. -/
theorem sectionBaseChange_sum_tmul (s : B →ₐ[A] A) {T : Type*} [CommSemiring T] [Algebra A T]
    {κ : Type*} (u : Finset κ) (t : κ → T) (b : κ → B) :
    s.sectionBaseChange T (∑ j ∈ u, t j ⊗ₜ b j) = ∑ j ∈ u, s (b j) • t j := by
  simp [Algebra.smul_def, mul_comm]

/-- The base change of a section is natural in the base: it commutes with
`Algebra.TensorProduct.rTensor B φ` for an `A`-algebra map `φ : T →ₐ[A] T'`. -/
@[simp]
theorem sectionBaseChange_rTensor (s : B →ₐ[A] A) {T T' : Type*} [CommSemiring T] [Algebra A T]
    [CommSemiring T'] [Algebra A T'] (φ : T →ₐ[A] T') (x : T ⊗[A] B) :
    s.sectionBaseChange T' (Algebra.TensorProduct.rTensor B φ x) = φ (s.sectionBaseChange T x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Base change of a section is transitive: along `A → A' → T`, base changing `s` to `A'` and
then to `T` is base changing `s` to `T`, through the identification
`T ⊗[A'] (A' ⊗[A] B) ≃ T ⊗[A] B`. -/
@[simp]
theorem sectionBaseChange_sectionBaseChange {B : Type*} [CommSemiring B] [Algebra A B]
    (s : B →ₐ[A] A) {A' T : Type*} [CommSemiring A'] [Algebra A A'] [CommSemiring T]
    [Algebra A T] [Algebra A' T] [IsScalarTower A A' T] (x : T ⊗[A'] (A' ⊗[A] B)) :
    (s.sectionBaseChange A').sectionBaseChange T x =
      s.sectionBaseChange T (Algebra.TensorProduct.cancelBaseChange A A' T T B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [sectionBaseChange_tmul, Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.smul_def, IsScalarTower.algebraMap_apply A A' T, map_mul]
      ac_rfl
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

section SemilinearTwist

variable {C D T : Type*} [CommSemiring C] [Algebra A C] [Semiring D] [Semiring T] [Algebra A T]
  [Algebra C D]

/-- The **semilinear twist** of an algebra map `y : D →ₐ[C] C ⊗[A] T`, where `C` is a commutative
`A`-algebra, by a ring homomorphism `φ : E →+* D` semilinear over an `A`-algebra automorphism
`σ` of `C`, in the sense that `φ (c • e) = σ c • φ e`: the composite `(σ⁻¹ ⊗ T) ∘ y ∘ φ`. Neither
`y ∘ φ` nor `σ⁻¹ ⊗ T` is `C`-linear, but their composite is. -/
noncomputable def semilinearTwist {E : Type*} [Semiring E] [Algebra C E] (y : D →ₐ[C] C ⊗[A] T)
    (σ : C ≃ₐ[A] C) (φ : E →+* D) (hφ : ∀ c, φ (algebraMap C E c) = algebraMap C D (σ c)) :
    E →ₐ[C] C ⊗[A] T where
  toRingHom := (Algebra.TensorProduct.rTensor T (σ.symm : C →ₐ[A] C)).toRingHom.comp
    ((y : D →+* C ⊗[A] T).comp φ)
  commutes' c := by simp [hφ]

@[simp]
theorem semilinearTwist_apply {E : Type*} [Semiring E] [Algebra C E] (y : D →ₐ[C] C ⊗[A] T)
    (σ : C ≃ₐ[A] C) (φ : E →+* D) (hφ : ∀ c, φ (algebraMap C E c) = algebraMap C D (σ c))
    (e : E) :
    y.semilinearTwist σ φ hφ e = Algebra.TensorProduct.rTensor T (σ.symm : C →ₐ[A] C) (y (φ e)) :=
  (rfl)

end SemilinearTwist

end AlgHom

namespace AlgHom

end AlgHom

end

section
-- MODULE Algebra/Coalgebra/Convolution
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/





/-!
# Comultiplication as a convolution product

Let `C` be an `R`-algebra carrying a comultiplication. This file records that, for the convolution
product of linear maps `C →ₗ[R] C ⊗[R] C`, comultiplication is the convolution product of the two
canonical inclusions `c ↦ c ⊗ₜ 1` and `c ↦ 1 ⊗ₜ c` of `C` into its tensor square.

For the convolution dual `Module.Dual R C` of a module carrying comultiplication and counit
data, the element `1` is the counit and multiplication is successive contraction of
comultiplication. Only when the counit laws hold (for a `Coalgebra`) is this `1` a
multiplicative identity.

The file also provides the exterior convolution product `WithConv.mulTensor`: linear maps
out of modules `M` and `N`, valued in a (not necessarily unital or associative) algebra,
applied legwise on `M ⊗[R] N` and multiplied in the codomain. Its normalization rules (zero,
addition, scalars) and its multiplicativity for the convolution product make it the engine for
composition-level convolution calculations: when the coefficient multiplication is commutative
and associative, convolution products interleave legwise. Composing a multiplicative map with a
multiplication gives its exterior square (`NonUnitalAlgHom.toConv_coe_comp_mul'`, with the
algebra-map form `AlgHom.toConv_toLinearMap_comp_mul'`). The Leibniz-rule counterpart, that a
counit-valued derivation composed with multiplication is the sum of its two exterior products
with the counit, is in `TauCeti/Algebra/AlgebraicGroup/Tangent/Basic.lean`.

The file also records how convolution algebras change with their coefficients. An algebra
map `g : B →ₐ[R] B'` induces Mathlib's `AlgHom.convPostcomp` on convolution algebras, and when
`B'` is a `B`-algebra with a finite basis over `B`, taking coordinates identifies the
convolution algebra with coefficients in `B'` with a free module over the one with coefficients
in `B`.

Finally, convolution products respect submodule-valued maps: the convolution product of maps with
values in `R`-submodules `M` and `N` of the algebra has values in `M * N`, so the `n`-th
convolution power of a map with values in `M` has values in `M ^ n`. Applied to an ideal `I`,
viewed as an `R`-submodule, and a point `x = 1 + D` of an affine group with `D` valued in `I`,
this controls the binomial expansion of the powers of `x`.

## Main declarations

* `LinearMap.ofConv_one_eq_counit`: the convolution dual's `1` is the counit.
* `LinearMap.convMul_eq_comp_tensorComponent`: convolution-dual multiplication as contraction.
* `LinearMap.tensorComponent_lTensor_comul`: successive contractions on the right tensor factor.
* `IsGroupLikeElem.ofConv_convMul_apply`: at a group-like element, a convolution product is the
  product of the values.
* `TauCeti.Coalgebra.comul_eq_convMul_includeLeft_includeRight`: comultiplication as the
  convolution product of the two tensor inclusions.
* `TauCeti.Bialgebra.comulPoint_eq_include_mul`: the corresponding identity for the
  algebra-hom points of a commutative bialgebra.
* `AlgHom.toConv_comp_comulAlgHom`: the functorial form of the previous identity, after
  post-composing with an arbitrary algebra map out of the tensor square.
* `TauCeti.Bialgebra.ofConv_one_eq_counitAlgHom`: the identity base-valued point is the counit.
* `AlgHom.map_comp_comulAlgHom_of_mul`: an algebra map into a commutative bialgebra respects
  the comultiplications when pre-composition with it is multiplicative on points.
* `WithConv.mulTensor`: the exterior convolution product, with its
  normalization rules and `WithConv.mulTensor_convMul`.
* `NonUnitalAlgHom.toConv_coe_comp_mul'`: a non-unital algebra map composed with
  multiplication is its own exterior square, with the algebra-map form
  `AlgHom.toConv_toLinearMap_comp_mul'`.
* `Module.Basis.convCoordEquiv`: the coordinates of a convolution-algebra element in a finite
  basis of the coefficients, with `Module.Basis.convCoordEquiv_convPostcomp_mul` recording that
  they are linear over the convolution algebra of the smaller coefficient ring.
* `LinearMap.convMul_apply_mem_mul` and `LinearMap.convPow_apply_mem_pow`: convolution products
  and powers of submodule-valued maps.
-/


open TensorProduct WithConv

namespace LinearMap

variable {R C : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The element `1` of the convolution dual is the counit. It is a multiplicative identity only
when the counit laws hold, as for a `Coalgebra`. -/
@[simp]
theorem ofConv_one_eq_counit :
    (1 : WithConv (Module.Dual R C)).ofConv = Coalgebra.counit := by
  simp [convOne_def]

/-- Multiplication in the convolution dual is successive contraction of comultiplication. -/
theorem convMul_eq_comp_tensorComponent (f g : WithConv (Module.Dual R C)) :
    (f * g).ofConv = f.ofConv ∘ₗ tensorComponent g.ofConv ∘ₗ Coalgebra.comul := by
  have hp : f.ofConv ∘ₗ tensorComponent g.ofConv =
      LinearMap.mul' R R ∘ₗ TensorProduct.map f.ofConv g.ofConv := by
    ext c d
    simp [mul_comm]
  rw [← comp_assoc, hp, convMul_def, comp_assoc]

/-- Successive contractions of a comultiplication on the right tensor factor are
contraction by the convolution product. -/
theorem tensorComponent_lTensor_comul {M : Type*} [AddCommMonoid M] [Module R M]
    (f g : WithConv (Module.Dual R C)) (x : M ⊗[R] C) :
    tensorComponent f.ofConv
        ((tensorComponent g.ofConv).lTensor M (Coalgebra.comul.lTensor M x)) =
      tensorComponent (f * g).ofConv x := by
  simp [lTensor_def, convMul_eq_comp_tensorComponent, comp_assoc]

end LinearMap

/-- A convolution product evaluated at a group-like element is the product of the values. -/
theorem IsGroupLikeElem.ofConv_convMul_apply {R C A : Type*} [CommSemiring R] [AddCommMonoid C]
    [Module R C] [Coalgebra R C] [Semiring A] [Algebra R A] {c : C} (hc : IsGroupLikeElem R c)
    (f g : WithConv (C →ₗ[R] A)) : (f * g).ofConv c = f.ofConv c * g.ofConv c := by
  rw [LinearMap.convMul_apply, hc.comul_eq_tmul_self, TensorProduct.map_tmul,
    LinearMap.mul'_apply]

namespace TauCeti

namespace Coalgebra

variable {R : Type*} {C : Type*} [CommSemiring R] [Semiring C] [Algebra R C]
  [_root_.CoalgebraStruct R C]

/-- **Comultiplication is the convolution product of the two tensor inclusions.** In the
convolution product on maps `C →ₗ[R] C ⊗[R] C`, the product of `includeLeft` and `includeRight`
multiplies the two legs of `Δ c` back together in order, which is `Δ` itself.

Only the comultiplication *data* is used, so this needs `CoalgebraStruct` rather than
`Coalgebra`: no coalgebra law, bialgebra compatibility or antipode axiom enters. -/
theorem comul_eq_convMul_includeLeft_includeRight :
    (toConv (Coalgebra.comul : C →ₗ[R] C ⊗[R] C) : WithConv (C →ₗ[R] C ⊗[R] C)) =
      toConv (Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap *
        toConv (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap := by
  apply WithConv.ofConv_injective
  have hmul : LinearMap.mul' R (C ⊗[R] C) ∘ₗ
      TensorProduct.map
        (Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap
        (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap =
      LinearMap.id := by
    -- Mathlib's `lmul'_comp_map` requires a commutative target algebra, whereas `C ⊗[R] C`
    -- is only a semiring here. `lift_includeLeft_includeRight` computes the same pure tensors,
    -- but identifying this linear composite still requires tensor-product extensionality.
    apply TensorProduct.ext
    ext x y
    simp
  simp only [LinearMap.convMul_def]
  rw [← LinearMap.comp_assoc, hmul]
  simp

end Coalgebra

namespace Bialgebra

variable {R : Type*} [CommSemiring R]

section Semiring

variable {H : Type*} [Semiring H] [_root_.Bialgebra R H]

/-- **Post-composition splits the comultiplication point into its two inclusions.** For any
algebra map `φ` out of the tensor square, the point `φ ∘ Δ` is the convolution product of `φ`
restricted along the two inclusions.

The convolution monoid here is the one on points of `H` with values in the *commutative* algebra
`A`, so `H` itself need only be a semiring: the tensor square `H ⊗[R] H` is used solely as the
source of `φ`, never as a convolution target. That is why this is proved from the linear-map
identity `TauCeti.Coalgebra.comul_eq_convMul_includeLeft_includeRight` rather than from
`TauCeti.Bialgebra.comulPoint_eq_include_mul`, which needs `H ⊗[R] H` to be commutative. -/
theorem _root_.AlgHom.toConv_comp_comulAlgHom {A : Type*} [CommSemiring A] [Algebra R A]
    (phi : H ⊗[R] H →ₐ[R] A) :
    toConv (phi.comp (Bialgebra.comulAlgHom R H)) =
      toConv (phi.comp (Algebra.TensorProduct.includeLeft
        (R := R) (A := H) (B := H))) *
      toConv (phi.comp (Algebra.TensorProduct.includeRight
        (R := R) (A := H) (B := H))) := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul, AlgHom.comp_toLinearMap, Bialgebra.toLinearMap_comulAlgHom]
  -- Split `Δ` into the two tensor inclusions and distribute `phi` over their product.
  rw [← ofConv_toConv Coalgebra.comul, Coalgebra.comul_eq_convMul_includeLeft_includeRight,
    LinearMap.algHom_comp_convMul_distrib, toConv_ofConv]
  simp only [AlgHom.comp_toLinearMap]

/-- The identity of the convolution monoid of base-valued points `H →ₐ[R] R` is the counit. -/
theorem ofConv_one_eq_counitAlgHom :
    (1 : WithConv (H →ₐ[R] R)).ofConv = Bialgebra.counitAlgHom R H := by
  rw [AlgHom.convOne_def, ofConv_toConv, Algebra.ofId_self, AlgHom.id_comp]

end Semiring

variable {H : Type*} [CommSemiring H] [_root_.Bialgebra R H]

/-- The comultiplication point of a commutative bialgebra is the convolution product of the
two canonical tensor-factor points. This is the algebra-hom form of
`Coalgebra.comul_eq_convMul_includeLeft_includeRight`. -/
theorem comulPoint_eq_include_mul :
    toConv (Bialgebra.comulAlgHom R H) =
      toConv (Algebra.TensorProduct.includeLeft
        (R := R) (A := H) (B := H)) *
      toConv (Algebra.TensorProduct.includeRight
        (R := R) (A := H) (B := H)) := by
  simpa only [AlgHom.id_comp] using
    (AlgHom.id R (H ⊗[R] H)).toConv_comp_comulAlgHom

/-- **A criterion for respecting comultiplication.** An `R`-algebra map `φ : A →ₐ[R] B` of
bialgebras, with `B` commutative, respects the comultiplications as soon as pre-composition with
`φ` is multiplicative on the convolution monoid of points of `B` with values in `B ⊗[R] B`, where
the comultiplication of `B` is the product of the two tensor inclusions
(`TauCeti.Bialgebra.comulPoint_eq_include_mul`). In particular it suffices that pre-composition
with `φ` is multiplicative on points with values in every commutative `R`-algebra. -/
theorem _root_.AlgHom.map_comp_comulAlgHom_of_mul {A B : Type*} [Semiring A] [CommSemiring B]
    [_root_.Bialgebra R A] [_root_.Bialgebra R B] (φ : A →ₐ[R] B)
    (hmul : ∀ f g : WithConv (B →ₐ[R] B ⊗[R] B),
      toConv ((f * g).ofConv.comp φ) = toConv (f.ofConv.comp φ) * toConv (g.ofConv.comp φ)) :
    (Algebra.TensorProduct.map φ φ).comp (Bialgebra.comulAlgHom R A) =
      (Bialgebra.comulAlgHom R B).comp φ := by
  refine WithConv.toConv_injective ?_
  rw [AlgHom.toConv_comp_comulAlgHom, Algebra.TensorProduct.map_comp_includeLeft,
    Algebra.TensorProduct.map_comp_includeRight, ← hmul, ← comulPoint_eq_include_mul,
    ofConv_toConv]

end Bialgebra

end TauCeti

section ExteriorProduct

open WithConv TensorProduct

variable {R M N S : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [NonUnitalNonAssocSemiring S] [Module R S]
  [SMulCommClass R S S] [IsScalarTower R S S]

namespace WithConv

/-- The exterior convolution product on `M ⊗[R] N`: apply one factor on each tensor
leg and multiply the results in the coefficients. It underlies the Leibniz-rule
manipulations for counit-valued derivations (there at `N = M`): a derivation `d` composed with
the multiplication of the bialgebra is the sum `mulTensor 1 d + mulTensor d 1` of its two
exterior products with the counit. -/
def mulTensor (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    WithConv (M ⊗[R] N →ₗ[R] S) :=
  toConv (LinearMap.mul' R S ∘ₗ map s.ofConv t.ofConv)

/-- The exterior product evaluates a pure tensor legwise and multiplies the results
in the coefficients. -/
@[simp]
lemma mulTensor_apply_tmul
    (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) (x : M) (y : N) :
    (mulTensor s t).ofConv (x ⊗ₜ[R] y) = s.ofConv x * t.ofConv y := by
  simp [mulTensor]

/-- The exterior product vanishes when the left factor is zero. -/
@[simp]
lemma mulTensor_zero_left (t : WithConv (N →ₗ[R] S)) :
    mulTensor (0 : WithConv (M →ₗ[R] S)) t = 0 := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

/-- The exterior product vanishes when the right factor is zero. -/
@[simp]
lemma mulTensor_zero_right (s : WithConv (M →ₗ[R] S)) :
    mulTensor s (0 : WithConv (N →ₗ[R] S)) = 0 := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

/-- The exterior product is additive in the left factor. -/
@[simp]
lemma mulTensor_add_left (s₁ s₂ : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor (s₁ + s₂) t = mulTensor s₁ t + mulTensor s₂ t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [add_mul]

/-- The exterior product is additive in the right factor. -/
@[simp]
lemma mulTensor_add_right (s : WithConv (M →ₗ[R] S)) (t₁ t₂ : WithConv (N →ₗ[R] S)) :
    mulTensor s (t₁ + t₂) = mulTensor s t₁ + mulTensor s t₂ := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [mul_add]

/-- Scalars pull out of the left factor of the exterior product. -/
@[simp]
lemma mulTensor_smul_left (r : R) (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor (r • s) t = r • mulTensor s t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [smul_mul_assoc]

/-- Scalars pull out of the right factor of the exterior product. -/
@[simp]
lemma mulTensor_smul_right (r : R) (s : WithConv (M →ₗ[R] S)) (t : WithConv (N →ₗ[R] S)) :
    mulTensor s (r • t) = r • mulTensor s t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [mul_smul_comm]

end WithConv

end ExteriorProduct

section ExteriorProductAlgHom

variable {R A S : Type*} [CommSemiring R]

namespace NonUnitalAlgHom

variable [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonUnitalNonAssocSemiring S] [Module R S] [SMulCommClass R S S] [IsScalarTower R S S]

/-- A multiplicative linear map composed with multiplication is its own exterior square:
the multiplicativity of the map, in convolution form. Neither algebra need be unital or
associative. -/
@[simp]
lemma toConv_coe_comp_mul' (g : A →ₙₐ[R] S) :
    toConv ((g : A →ₗ[R] S) ∘ₗ LinearMap.mul' R A) =
      mulTensor (toConv (g : A →ₗ[R] S)) (toConv (g : A →ₗ[R] S)) := by
  -- Not a re-derivation: this is Mathlib's `NonUnitalAlgHom.comp_mul'` transported into the
  -- file's own `mulTensor` vocabulary, which is what consumers rewrite with.
  exact congrArg toConv (NonUnitalAlgHom.comp_mul' g)

end NonUnitalAlgHom

namespace AlgHom

variable [Semiring A] [Algebra R A] [Semiring S] [Algebra R S]

/-- An algebra-map point composed with multiplication is its own exterior square. This is
`NonUnitalAlgHom.toConv_coe_comp_mul'` in the `AlgHom.toLinearMap` form that algebra-map points
are written in. -/
@[simp]
lemma toConv_toLinearMap_comp_mul' (g : A →ₐ[R] S) :
    toConv (g.toLinearMap ∘ₗ LinearMap.mul' R A) =
      mulTensor (toConv g.toLinearMap) (toConv g.toLinearMap) :=
  (g : A →ₙₐ[R] S).toConv_coe_comp_mul'

end AlgHom

end ExteriorProductAlgHom

section ExteriorConvolution

open WithConv TensorProduct

variable {R C D S : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]
  [AddCommMonoid D] [Module R D] [CoalgebraStruct R D]
  [NonUnitalCommSemiring S] [Module R S] [SMulCommClass R S S] [IsScalarTower R S S]

namespace WithConv

/-- The exterior product is multiplicative for convolution: products interleave
legwise. Only the comultiplication *data* on each leg is used — no multiplication on the
sources and no bialgebra compatibility — so the two legs may be distinct coalgebras. The
coefficients need to be commutative and associative, but not unital. -/
@[simp]
lemma mulTensor_convMul
    (s u : WithConv (C →ₗ[R] S)) (t v : WithConv (D →ₗ[R] S)) :
    mulTensor s t * mulTensor u v = mulTensor (s * u) (t * v) := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp only [LinearMap.convMul_apply, TensorProduct.comul_tmul, mulTensor_apply_tmul]
  -- On pure tensors `Δ x = a ⊗ b` and `Δ y = c ⊗ d` both sides are
  -- `s a * u b * (t c * v d)` up to `mul_mul_mul_comm`; extend additively in each leg.
  induction (CoalgebraStruct.comul x : C ⊗[R] C) with
  | zero => simp_all
  | add a b ha hb => simp_all [add_tmul, add_mul]
  | tmul a b =>
    induction (CoalgebraStruct.comul y : D ⊗[R] D) with
    | zero => simp_all
    | add c d hc hd => simp_all [tmul_add, mul_add]
    | tmul c d => simp [mul_mul_mul_comm]

end WithConv

end ExteriorConvolution

section CoefficientChange

open WithConv

/-- A finite basis of `B'` over `B` identifies linear maps `C → B'` with families of linear maps
`C → B`, by taking coordinates. -/
noncomputable def _root_.Module.Basis.convCoordEquiv {ι B B' : Type*} [Finite ι]
    [Semiring B] [AddCommMonoid B'] [Module B B'] (b : Module.Basis ι B B') (R : Type*)
    [CommSemiring R] [Algebra R B] [Module R B'] [IsScalarTower R B B'] (C : Type*)
    [AddCommMonoid C] [Module R C] :
    WithConv (C →ₗ[R] B') ≃ₗ[R] (ι → WithConv (C →ₗ[R] B)) where
  toFun φ i := toConv ((b.coord i).restrictScalars R ∘ₗ φ.ofConv)
  invFun v := toConv ((b.equivFun.symm.toLinearMap.restrictScalars R) ∘ₗ
    _root_.LinearMap.pi fun i => (v i).ofConv)
  map_add' φ ψ := by ext; simp
  map_smul' r φ := by ext; simp
  left_inv φ := by
    ext c
    simp [LinearEquiv.symm_apply_eq, funext_iff]
  right_inv v := by
    ext i c
    simp [← Module.Basis.equivFun_apply]

section Basis

variable {ι B B' R C : Type*} [Finite ι] [CommSemiring R] [AddCommMonoid C] [Module R C]

section Module

variable [Semiring B] [AddCommMonoid B'] [Module B B'] [Algebra R B] [Module R B']
  [IsScalarTower R B B']

/-- The `i`-th component of `b.convCoordEquiv R C φ` is the `i`-th coordinate of `φ`. -/
@[simp]
theorem _root_.Module.Basis.convCoordEquiv_apply (b : Module.Basis ι B B')
    (φ : WithConv (C →ₗ[R] B')) (i : ι) :
    b.convCoordEquiv R C φ i = toConv ((b.coord i).restrictScalars R ∘ₗ φ.ofConv) :=
  (rfl)

/-- The inverse of `b.convCoordEquiv R C` reassembles a family of coordinate maps. -/
@[simp]
theorem _root_.Module.Basis.convCoordEquiv_symm_apply (b : Module.Basis ι B B')
    (v : ι → WithConv (C →ₗ[R] B)) :
    (b.convCoordEquiv R C).symm v =
      toConv ((b.equivFun.symm.toLinearMap.restrictScalars R) ∘ₗ
        _root_.LinearMap.pi fun i => (v i).ofConv) :=
  (rfl)

end Module

variable [CommSemiring B] [Semiring B'] [Algebra B B'] [Algebra R B] [Algebra R B']
  [IsScalarTower R B B']

/-- Taking coordinates in a finite basis of `B'` over `B` is linear over the convolution algebra
with coefficients in `B`, which acts on maps into `B'` through post-composition with
`algebraMap B B'`. -/
theorem _root_.Module.Basis.convCoordEquiv_convPostcomp_mul [_root_.Coalgebra R C]
    (b : Module.Basis ι B B') (f : WithConv (C →ₗ[R] B)) (φ : WithConv (C →ₗ[R] B')) (i : ι) :
    b.convCoordEquiv R C ((IsScalarTower.toAlgHom R B B').convPostcomp (C := C) f * φ) i =
      f * b.convCoordEquiv R C φ i := by
  ext c
  simp only [Module.Basis.convCoordEquiv_apply, AlgHom.convPostcomp_apply_ofConv,
    _root_.LinearMap.convMul_apply, _root_.LinearMap.comp_apply, ofConv_toConv]
  induction (CoalgebraStruct.comul c : C ⊗[R] C) with
  | zero => simp_all
  | tmul x y => simp [← Algebra.smul_def]
  | add x y hx hy => simp_all [map_add]

end Basis

end CoefficientChange

section SubmoduleValued

open WithConv

namespace LinearMap

variable {R C A : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Semiring A]
  [Algebra R A]

/-- The convolution product of a linear map with values in a submodule `M` and one with values in
a submodule `N` has values in `M * N`. -/
theorem convMul_apply_mem_mul [CoalgebraStruct R C] {M N : Submodule R A}
    {f g : WithConv (C →ₗ[R] A)} (hf : ∀ c, f c ∈ M) (hg : ∀ c, g c ∈ N) (c : C) :
    (f * g) c ∈ M * N := by
  rw [(Coalgebra.Repr.arbitrary R c).convMul_apply]
  exact (M * N).sum_mem fun i _ => Submodule.mul_mem_mul (hf _) (hg _)

/-- The `n`-th convolution power of a linear map with values in a submodule `M` has values in
`M ^ n`. -/
theorem convPow_apply_mem_pow [_root_.Coalgebra R C] {M : Submodule R A}
    {f : WithConv (C →ₗ[R] A)} (hf : ∀ c, f c ∈ M) (n : ℕ) (c : C) : (f ^ n) c ∈ M ^ n := by
  induction n generalizing c with
  | zero => simp
  | succ n ih => simpa [pow_succ, Submodule.pow_succ] using convMul_apply_mem_mul ih hf c

end LinearMap

end SubmoduleValued

end

section
-- MODULE Algebra/HopfAlgebra/TensorShear
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/




/-!
# The tensor shear of a commutative Hopf algebra

The pullback of `(g, h) ↦ (g, gh)` is an automorphism of `H ⊗[R] H`. It fixes
the left factor and sends the right factor to comultiplication. Its inverse uses
the antipode in the left factor. This is the algebraic change of coordinates used
in the canonical map for a quotient by a closed subgroup. The mirror shear along
`(g, h) ↦ (g h, h⁻¹)` is also recorded; after comultiplication it contracts to
`x ↦ x ⊗ 1`.
-/


open scoped TensorProduct
open WithConv Algebra.TensorProduct

namespace TauCeti.HopfAlgebra

variable {R H : Type*} [CommSemiring R] [CommSemiring H] [_root_.HopfAlgebra R H]

/-- The forward algebra map underlying the tensor shear. -/
private noncomputable def tensorShearHom : H ⊗[R] H →ₐ[R] H ⊗[R] H :=
  lift includeLeft (Bialgebra.comulAlgHom R H) (fun _ _ ↦ .all _ _)

/-- The inverse algebra map underlying the tensor shear. -/
private noncomputable def tensorShearInv : H ⊗[R] H →ₐ[R] H ⊗[R] H :=
  lift includeLeft
    ((toConv (includeLeft : H →ₐ[R] H ⊗[R] H))⁻¹ * toConv includeRight).ofConv
    (fun _ _ ↦ .all _ _)

private theorem tensorShearHom_comp_inv :
    (tensorShearHom (R := R) (H := H)).comp tensorShearInv = AlgHom.id R _ := by
  apply Algebra.TensorProduct.ext
  · simp [AlgHom.comp_assoc, tensorShearHom, tensorShearInv]
  · -- Tensor extensionality restricts scalars from `R` to itself on the second factor.
    change tensorShearHom.comp (tensorShearInv.comp includeRight) = includeRight
    rw [tensorShearInv, lift_comp_includeRight']
    apply toConv_injective
    rw [AlgHom.comp_convMul_distrib]
    -- Mathlib defines convolution inversion by precomposing with the antipode,
    -- so associativity of composition identifies the first factor with this inverse.
    change (toConv ((tensorShearHom (R := R) (H := H)).comp includeLeft))⁻¹ *
      toConv (tensorShearHom.comp includeRight) = toConv includeRight
    simpa only [tensorShearHom, lift_comp_includeLeft, lift_comp_includeRight',
      Bialgebra.comulPoint_eq_include_mul] using
      inv_mul_cancel_left (toConv (includeLeft : H →ₐ[R] H ⊗[R] H)) (toConv includeRight)

private theorem tensorShearInv_comp_hom :
    (tensorShearInv (R := R) (H := H)).comp tensorShearHom = AlgHom.id R _ := by
  apply Algebra.TensorProduct.ext
  · simp [AlgHom.comp_assoc, tensorShearHom, tensorShearInv]
  · -- Tensor extensionality inserts the same redundant scalar restriction here.
    change tensorShearInv.comp (tensorShearHom.comp includeRight) = includeRight
    rw [tensorShearHom, lift_comp_includeRight',
      ← ofConv_toConv (Bialgebra.comulAlgHom R H), Bialgebra.comulPoint_eq_include_mul,
      AlgHom.comp_convMul_distrib]
    simpa only [tensorShearInv, lift_comp_includeLeft,
      lift_comp_includeRight', toConv_ofConv] using congrArg ofConv
        (mul_inv_cancel_left (toConv (includeLeft : H →ₐ[R] H ⊗[R] H)) (toConv includeRight))

/-- The coordinate automorphism of `(g, h) ↦ (g, gh)` on the tensor square of a
commutative Hopf algebra. -/
noncomputable def tensorShearMulRight : H ⊗[R] H ≃ₐ[R] H ⊗[R] H :=
  AlgEquiv.ofAlgHom tensorShearHom tensorShearInv
    tensorShearHom_comp_inv tensorShearInv_comp_hom

/-- The tensor shear fixes the first coordinate and multiplies the second by it. -/
@[simp]
theorem tensorShearMulRight_tmul (a b : H) :
    tensorShearMulRight (R := R) (a ⊗ₜ[R] b) =
      (a ⊗ₜ[R] 1) * Coalgebra.comul (R := R) b := by
  simp [tensorShearMulRight, tensorShearHom]

/-- The inverse tensor shear divides the second coordinate by the first. -/
@[simp]
theorem tensorShearMulRight_symm_tmul (a b : H) :
    (tensorShearMulRight (R := R)).symm (a ⊗ₜ[R] b) =
      (a ⊗ₜ[R] 1) * TensorProduct.map (HopfAlgebraStruct.antipode R) LinearMap.id
        (Coalgebra.comul (R := R) b) := by
  simp only [tensorShearMulRight, AlgEquiv.ofAlgHom_symm_apply, tensorShearInv, lift_tmul,
    includeLeft_apply, AlgHom.convMul_apply]
  congr 1
  induction Coalgebra.comul (R := R) b with
  | zero => simp_all
  | tmul x y =>
    -- Expand the convolution inverse's antipode action on this pure tensor.
    change (HopfAlgebra.antipodeAlgHom R H x ⊗ₜ[R] 1) * (1 ⊗ₜ[R] y) = _
    simp [HopfAlgebra.antipodeAlgHom]
  | add x y hx hy => simp [hx, hy]

section BaseChange

variable (A : Type*) [CommSemiring A] [Algebra R A]

-- Scalar extension of the shear, expressed using the associators of algebras.
private noncomputable def tensorShearMulRightBaseChangeAux :
    (A ⊗[R] H) ⊗[R] H ≃ₐ[R] (A ⊗[R] H) ⊗[R] H :=
  (Algebra.TensorProduct.assoc R R R A H H).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[R] A)
      (tensorShearMulRight (R := R) (H := H))).trans
        (Algebra.TensorProduct.assoc R R R A H H).symm)

/-- The Hopf tensor shear after scalar extension to `A`, regarded as an automorphism over
`A ⊗[R] H`: pullback by `(x, g, h) ↦ (x, g, gh)` fixes the coordinates `(x, g)`. -/
noncomputable def tensorShearMulRightBaseChange :
    (A ⊗[R] H) ⊗[R] H ≃ₐ[A ⊗[R] H] (A ⊗[R] H) ⊗[R] H :=
  AlgEquiv.ofRingEquiv (f := (tensorShearMulRightBaseChangeAux A).toRingEquiv) fun z ↦ by
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    induction z with
    | zero => simp_all
    | tmul a h => simp [tensorShearMulRightBaseChangeAux]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

/-- The scalar-extended shear is pullback along the point map `(x, u, v) ↦ (x, u, uv)`. On a
pure tensor this sends `(a ⊗ g) ⊗ h` to `a ⊗ ((g ⊗ 1) * Δ(h))`, up to reassociation: the first
tensor factor is fixed, and the last factor `h` is replaced by its comultiplication, multiplied
by `g` in the middle factor. -/
@[simp]
theorem tensorShearMulRightBaseChange_tmul (a : A) (g h : H) :
    tensorShearMulRightBaseChange A ((a ⊗ₜ[R] g) ⊗ₜ[R] h) =
      (Algebra.TensorProduct.assoc R R R A H H).symm
        (a ⊗ₜ[R] ((g ⊗ₜ[R] 1) * Coalgebra.comul (R := R) h)) := by
  simp [tensorShearMulRightBaseChange, tensorShearMulRightBaseChangeAux]

/-- The inverse scalar-extended shear is pullback along the point map `(x, u, v) ↦ (x, u, u⁻¹v)`.
On a pure tensor this sends `(a ⊗ g) ⊗ h` to `a ⊗ ((g ⊗ 1) * (S ⊗ id)(Δ(h)))`, up to
reassociation, where `S` is the antipode. -/
@[simp]
theorem tensorShearMulRightBaseChange_symm_tmul (a : A) (g h : H) :
    (tensorShearMulRightBaseChange A).symm ((a ⊗ₜ[R] g) ⊗ₜ[R] h) =
      (Algebra.TensorProduct.assoc R R R A H H).symm
        (a ⊗ₜ[R] ((g ⊗ₜ[R] 1) * TensorProduct.map (HopfAlgebraStruct.antipode R) LinearMap.id
          (Coalgebra.comul (R := R) h))) := by
  simp [tensorShearMulRightBaseChange, tensorShearMulRightBaseChangeAux]

end BaseChange

/-- The mirror tensor shear, which pulls back along `(g, h) ↦ (g h, h⁻¹)`. -/
noncomputable def tensorShearMulLeftInvRight : H ⊗[R] H →ₐ[R] H ⊗[R] H :=
  lift (Bialgebra.comulAlgHom R H) (includeRight.comp (HopfAlgebra.antipodeAlgHom R H))
    (fun _ _ ↦ .all _ _)

/-- On pure tensors the mirror tensor shear is `a ⊗ b ↦ Δ(a) * (1 ⊗ S(b))`, the pullback along
`(g, h) ↦ (g h, h⁻¹)`. -/
@[simp]
theorem tensorShearMulLeftInvRight_tmul (a b : H) :
    tensorShearMulLeftInvRight (R := R) (a ⊗ₜ[R] b) =
      Coalgebra.comul (R := R) a * (1 ⊗ₜ[R] HopfAlgebra.antipode R b) := by
  simp [tensorShearMulLeftInvRight]

/-- Applying the mirror tensor shear after comultiplication leaves the left coordinate. -/
@[simp]
theorem tensorShearMulLeftInvRight_comul (x : H) :
    tensorShearMulLeftInvRight (R := R) (Coalgebra.comul (R := R) x) =
      x ⊗ₜ[R] (1 : H) := by
  let Φ : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] H :=
    (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).lTensor H).lTensor H
  have hshear (y : H ⊗[R] H) :
      tensorShearMulLeftInvRight (R := R) y =
        Φ (TensorProduct.assoc R H H H ((Coalgebra.comul (R := R)).rTensor H y)) := by
    induction y with
    | zero => simp_all
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul a b =>
      simp only [tensorShearMulLeftInvRight_tmul, LinearMap.rTensor_tmul]
      induction Coalgebra.comul (R := R) a with
      | zero => simp_all
      | add y z hy hz => simp only [add_mul, map_add, TensorProduct.add_tmul, hy, hz]
      | tmul c d => simp [Φ]
  have hΦ : Φ ∘ₗ (Coalgebra.comul (R := R) (A := H)).lTensor H =
      (Algebra.linearMap R H).lTensor H ∘ₗ (Coalgebra.counit (R := R) (A := H)).lTensor H := by
    rw [← LinearMap.lTensor_comp, LinearMap.comp_assoc, HopfAlgebra.mul_antipode_lTensor_comul,
      LinearMap.lTensor_comp]
  rw [hshear, Coalgebra.coassoc_apply, ← LinearMap.comp_apply (f := Φ), hΦ,
    LinearMap.comp_apply, Coalgebra.lTensor_counit_comul]
  simp

end TauCeti.HopfAlgebra

end

section
-- MODULE Algebra/AlgebraicGroup/FunctorOfPoints
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/




/-!
# Convolution groups of algebra homomorphisms out of a Hopf algebra

For an arbitrary Hopf algebra `H` over `R` and a commutative `R`-algebra `A`, the convolution
monoid of `R`-algebra homomorphisms `H →ₐ[R] A` is a **group**, with inverse `f ↦ f ∘ S`,
where `S` is the antipode of `H`. The source `H` need only be a Hopf algebra; it is *not*
required to be commutative.

Mathlib already constructs the convolution `Monoid` on `WithConv (H →ₐ[R] A)` for `H` a
bialgebra (`Mathlib/RingTheory/Bialgebra/Convolution.lean`): multiplication is the
convolution product `(f * g)(h) = ∑ f(h₍₁₎) * g(h₍₂₎)` and the unit is
`algebraMap ∘ ε`.
What is added here is the **inverse** and hence the **group** structure, available exactly
when `H` carries an antipode `S`: the inverse of `f` is `f ∘ S`.
Mathlib's `AlgHom.convInv` and `AlgHom.convGroup` additionally assume that the source is
commutative and the value algebra is a bialgebra; the constructions here remove those requirements.

The construction is functorial in the value algebra: post-composition with an `R`-algebra
homomorphism `φ : A →ₐ[R] B` gives a monoid homomorphism `mapValue φ` between the convolution
monoids, preserving identities and composition. This part needs only the bialgebra structure
on `H` (the convolution monoid), so it lives in its own `Bialgebra` section.

## Application: affine group schemes

When `H` is moreover *commutative*, `Spec H` is an affine group scheme, and the above is
the group structure on its functor of points `A ↦ (H →ₐ[R] A)`, with functoriality in
`A` realizing the `R-Alg ⥤ Grp` structure, where the counit is the identity and `f ∘ S` is
the inverse.

## Main results

* `WithConv.algHom_inv_apply`: pointwise, the convolution inverse of `f` sends `h` to `f (S h)`.
* `AlgHom.convGroupOfSemiring`, `AlgHom.convCommGroupOfSemiring`: for `H` a Hopf algebra over `R`
  and `A` a commutative `R`-algebra, `WithConv (H →ₐ[R] A)` is a group, commutative when `H`
  is cocommutative.
* `WithConv.algHom_toConv_mul_toConv_inv`, `WithConv.algHom_toConv_inv_mul_toConv`: a point and
  its inverse are convolution inverses as linear maps.
* `AlgHom.mapValue`: post-composition with `φ : A →ₐ[R] B` as a monoid homomorphism of
  convolution monoids, with `AlgHom.ofConv_comp_mapValue` describing it on underlying
  homomorphisms, `AlgHom.mapValue_id`, `AlgHom.mapValue_comp` recording its
  functoriality in the value algebra, `AlgHom.mapValue_injective` recording that it loses no
  information when `φ` does not, and `AlgHom.range_mapValue` describing its image.
* `AlgHom.mem_mrange_mapValue_iff_mapValue_eq_mapValue`: points preserve equalizers; when an
  injective `φ` maps onto the equalizer of `ψ₁` and `ψ₂`, the points coming from the source of `φ`
  are those on which `mapValue ψ₁` and `mapValue ψ₂` agree.
* `AlgHom.mem_mrange_mapValue_iff_mapValue_eq`: when the image of an injective `φ` is the fixed
  ring of an endomorphism `τ`, the points coming from the source of `φ` are those fixed by
  `mapValue τ`.
* `AlgEquiv.mapValueMulEquiv`: an isomorphism of value algebras induces an isomorphism of
  convolution monoids.
* `AlgHom.piValueMulEquiv`: points valued in a product of commutative algebras are families of
  points valued in the factors.
* `AlgHom.mapValue_mapValue_ofId`: extending a base-valued point to `A` and then mapping it along
  `φ : A →ₐ[R] B` extends it to `B`.

## References

The convolution monoid on algebra homomorphisms builds on Mathlib's convolution monoid of
Yaël Dillies and Michał Mrugała, and the Hopf convolution algebra developed by
Yaël Dillies, Michał Mrugała, and Yunzhou Xie.
-/


open _root_.Coalgebra HopfAlgebra TensorProduct WithConv

namespace AlgHom

variable {R H A : Type*} [CommSemiring R]

section Hopf

variable [Semiring H] [_root_.HopfAlgebra R H] [CommSemiring A] [Algebra R A]

/-- Precomposition of an algebra homomorphism `f : H →ₐ[R] A` with the antipode `S` of
`H`, as an `R`-algebra homomorphism `H →ₐ[R] A`. Its underlying linear map is
`f.toLinearMap ∘ₗ HopfAlgebra.antipode R`. This is well-defined even when `H` is
noncommutative: `S` is an antihomomorphism (`HopfAlgebra.antipode_mul_antidistrib`), and `A` is
commutative, so `f ∘ S` is a homomorphism. The construction composes
`HopfAlgebra.antipodeAlgHomOp` with `AlgHom.fromOpposite`. -/
noncomputable def antipodeComp (f : H →ₐ[R] A) : H →ₐ[R] A :=
  (f.fromOpposite fun x y => Commute.all (f x) (f y)).comp (HopfAlgebra.antipodeAlgHomOp R H)

/-- Evaluation of `antipodeComp f` at an element `h : H` is `f (S h)`. -/
@[simp]
lemma antipodeComp_apply (f : H →ₐ[R] A) (h : H) :
    antipodeComp f h = f (antipode R h) := (rfl)

/-- The underlying linear map of `antipodeComp f` is `f.toLinearMap ∘ₗ antipode R`. -/
@[simp]
lemma toLinearMap_antipodeComp (f : H →ₐ[R] A) :
    (antipodeComp f).toLinearMap = f.toLinearMap ∘ₗ antipode R :=
  LinearMap.ext (antipodeComp_apply f)

/-- The convolution inverse of an `R`-algebra homomorphism `f : H →ₐ[R] A` out of a Hopf
algebra is `f ∘ S`, where `S` is the antipode. The source need only be a semiring, so it can be
noncommutative, and the commutative value algebra `A` need not be a bialgebra. -/
noncomputable instance convInvOfSemiring : Inv (WithConv (H →ₐ[R] A)) where
  inv f := toConv (antipodeComp f.ofConv)

/-- The convolution inverse of `f` is `f ∘ S`, where `S` is the antipode:
`f⁻¹ = toConv (antipodeComp f.ofConv)`. -/
lemma _root_.WithConv.algHom_inv_def (f : WithConv (H →ₐ[R] A)) :
    f⁻¹ = toConv (antipodeComp f.ofConv) := rfl

/-- Pointwise, the convolution inverse of `f` sends `h` to `f (S h)`, where `S` is the
antipode. -/
@[simp]
lemma _root_.WithConv.algHom_inv_apply (f : WithConv (H →ₐ[R] A)) (h : H) :
    f⁻¹ h = f.ofConv (antipode R h) := by
  -- `algHom_inv_def` exposes `toConv (antipodeComp f.ofConv)`; under the coercion from `WithConv`,
  -- `(toConv g) h` evaluates as `g h`.
  rw [WithConv.algHom_inv_def, AlgHom.antipodeComp_apply]

/-- For a Hopf algebra `H` over `R` and a commutative `R`-algebra `A`, the convolution
monoid of `R`-algebra homomorphisms `H →ₐ[R] A` is a group, with inverse `f ↦ f ∘ S`. When
`H` is moreover commutative, `Spec H` is an affine group scheme and this is the group
structure on its functor of points evaluated at `A`. -/
noncomputable instance convGroupOfSemiring : Group (WithConv (H →ₐ[R] A)) where
  inv_mul_cancel f := by
    -- Pass to linear maps to use the Sweedler formula for convolution.
    refine WithConv.ofConv_injective (AlgHom.toLinearMap_injective (WithConv.toConv_injective ?_))
    rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne, algHom_inv_def, toConv_ofConv,
      AlgHom.toLinearMap_antipodeComp]
    ext h
    rw [(ℛ R h).convMul_apply]
    simp only [LinearMap.comp_apply, AlgHom.coe_toLinearMap, LinearMap.convOne_apply,
      ← map_mul, ← map_sum, sum_antipode_mul_eq_algebraMap_counit, AlgHom.commutes]

/-- A point convolved with its inverse, as linear maps, is the convolution unit. -/
lemma _root_.WithConv.algHom_toConv_mul_toConv_inv (f : WithConv (H →ₐ[R] A)) :
    toConv f.ofConv.toLinearMap * toConv (f⁻¹).ofConv.toLinearMap = 1 := by
  rw [← AlgHom.toLinearMap_convMul, mul_inv_cancel, AlgHom.toLinearMap_convOne]

/-- The inverse of a point convolved with the point, as linear maps, is the convolution unit. -/
lemma _root_.WithConv.algHom_toConv_inv_mul_toConv (f : WithConv (H →ₐ[R] A)) :
    toConv (f⁻¹).ofConv.toLinearMap * toConv f.ofConv.toLinearMap = 1 := by
  rw [← AlgHom.toLinearMap_convMul, inv_mul_cancel, AlgHom.toLinearMap_convOne]

/-- Precomposing an algebra homomorphism into a commutative algebra twice with the antipode gives
it back: `f ∘ S² = f`, since `f ∘ S` is the convolution inverse of `f` and inversion in the
convolution group is involutive. The antipode itself need not be involutive. -/
@[simp]
lemma antipodeComp_antipodeComp (f : H →ₐ[R] A) : antipodeComp (antipodeComp f) = f := by
  simpa only [WithConv.algHom_inv_def, ofConv_toConv] using
    congrArg WithConv.ofConv (inv_inv (toConv f))

/-- Pointwise form of `antipodeComp_antipodeComp`: an algebra homomorphism into a commutative
algebra is invariant under the square of the antipode, `f (S (S h)) = f h`. -/
@[simp]
lemma apply_antipode_antipode (f : H →ₐ[R] A) (h : H) :
    f (antipode R (antipode R h)) = f h := by
  simpa only [antipodeComp_apply] using DFunLike.congr_fun (antipodeComp_antipodeComp f) h

end Hopf

section Bialgebra

variable [Semiring H] [_root_.Bialgebra R H] [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- Functoriality of `A ↦ (H →ₐ[R] A)` in the value algebra: an `R`-algebra homomorphism
`φ : A →ₐ[R] B` induces, by post-composition, a monoid homomorphism between the convolution
monoids. This needs only the bialgebra structure on `H`. When `H` is moreover a Hopf algebra,
these convolution monoids are the convolution groups (`convGroupOfSemiring`); a `MonoidHom`
between groups is automatically a group homomorphism, so no separate construction is needed
there. -/
noncomputable def mapValue (φ : A →ₐ[R] B) :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] B) where
  toFun f := toConv (φ.comp f.ofConv)
  map_one' := by simp [AlgHom.convOne_def, ← AlgHom.comp_assoc]
  map_mul' f g := by simp [AlgHom.comp_convMul_distrib]

/-- `mapValue φ` acts pointwise by post-composition: `(mapValue φ f) = φ ∘ f`. -/
@[simp]
lemma mapValue_apply (φ : A →ₐ[R] B) (f : WithConv (H →ₐ[R] A)) :
    mapValue φ f = toConv (φ.comp f.ofConv) := (rfl)

/-- On underlying homomorphisms, `mapValue φ` is post-composition with `φ`, as functions. -/
lemma ofConv_comp_mapValue (φ : A →ₐ[R] B) :
    ofConv ∘ mapValue (H := H) φ = (fun f : H →ₐ[R] A ↦ φ.comp f) ∘ ofConv := by
  ext f h
  simp

/-- `mapValue` preserves the identity: `mapValue (𝟙 A)` is the identity monoid homomorphism. -/
@[simp]
lemma mapValue_id :
    mapValue (H := H) (AlgHom.id R A) = MonoidHom.id (WithConv (H →ₐ[R] A)) := by
  ext f : 1
  simp

/-- An injective homomorphism of value algebras induces an injective map on points: a point is
determined by its values. -/
lemma mapValue_injective {φ : A →ₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (mapValue (H := H) φ) := by
  intro f g hfg
  rw [mapValue_apply, mapValue_apply] at hfg
  refine WithConv.ofConv_injective (AlgHom.ext fun h => hφ ?_)
  exact DFunLike.congr_fun (WithConv.toConv_injective hfg) h

/-- The image of `mapValue φ` consists of the points whose underlying homomorphisms factor
through `φ`. -/
lemma range_mapValue (φ : A →ₐ[R] B) :
    Set.range (mapValue (H := H) φ) = ofConv ⁻¹' Set.range fun f : H →ₐ[R] A ↦ φ.comp f := by
  ext f
  refine ⟨?_, fun ⟨g, hg⟩ => ⟨toConv g, ?_⟩⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g.ofConv, by simp⟩
  · simp [hg]

/-- For an injective homomorphism `φ` of value algebras, a point comes from a point valued in the
source of `φ` exactly when each of its values lies in the range of `φ`. -/
lemma mem_mrange_mapValue_iff {φ : A →ₐ[R] B} (hφ : Function.Injective φ)
    {f : WithConv (H →ₐ[R] B)} :
    f ∈ MonoidHom.mrange (mapValue (H := H) φ) ↔ ∀ h, f.ofConv h ∈ φ.range := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨g, rfl⟩ h
    rw [mapValue_apply, ofConv_toConv]
    exact φ.mem_range_self _
  · -- The values lie in the range of `φ`; invert `φ` there.
    refine ⟨toConv ((AlgEquiv.ofInjective φ hφ).symm.toAlgHom.comp (f.ofConv.codRestrict _ hf)),
      WithConv.ofConv_injective (AlgHom.ext fun h => ?_)⟩
    simp [← AlgEquiv.ofInjective_apply _ hφ]

variable {C : Type*} [CommSemiring C] [Algebra R C]

/-- **Points preserve equalizers.** When an injective `φ : A →ₐ[R] B` maps onto the equalizer of
`ψ₁ ψ₂ : B →ₐ[R] C`, a point comes from a point valued in `A` exactly when its two images under
`mapValue ψ₁` and `mapValue ψ₂` agree. -/
lemma mem_mrange_mapValue_iff_mapValue_eq_mapValue {φ : A →ₐ[R] B} (hφ : Function.Injective φ)
    {ψ₁ ψ₂ : B →ₐ[R] C} (hψ : {b | ψ₁ b = ψ₂ b} = Set.range φ) {f : WithConv (H →ₐ[R] B)} :
    f ∈ MonoidHom.mrange (mapValue (H := H) φ) ↔ mapValue ψ₁ f = mapValue ψ₂ f := by
  simp [mem_mrange_mapValue_iff hφ, AlgHom.ext_iff, ← SetLike.mem_coe, ← hψ]

/-- When the image of an injective `φ : A →ₐ[R] B` is exactly the set of fixed points of an
endomorphism `τ` of `B`, a point comes from a point valued in `A` exactly when it is fixed by
`mapValue τ`: descent of points along an extension of coefficients whose fixed ring is the base. -/
lemma mem_mrange_mapValue_iff_mapValue_eq {φ : A →ₐ[R] B} (hφ : Function.Injective φ)
    {τ : B →ₐ[R] B} (hτ : {b | τ b = b} = Set.range φ) {f : WithConv (H →ₐ[R] B)} :
    f ∈ MonoidHom.mrange (mapValue (H := H) φ) ↔ mapValue τ f = f := by
  rw [mem_mrange_mapValue_iff_mapValue_eq_mapValue hφ (ψ₂ := AlgHom.id R B) hτ, mapValue_id,
    MonoidHom.id_apply]

/-- `mapValue` preserves composition: `mapValue (ψ ∘ φ) = mapValue ψ ∘ mapValue φ`. -/
lemma mapValue_comp (ψ : B →ₐ[R] C) (φ : A →ₐ[R] B) :
    mapValue (H := H) (ψ.comp φ) = (mapValue ψ).comp (mapValue φ) := by
  ext f : 1
  simp [AlgHom.comp_assoc]

/-- Extending a base-valued point to `A` and then mapping it along `φ : A →ₐ[R] B` extends it to
`B`. -/
lemma mapValue_mapValue_ofId (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] R)) :
    mapValue φ (mapValue (Algebra.ofId R A) g) = mapValue (Algebra.ofId R B) g := by
  rw [← MonoidHom.comp_apply, ← mapValue_comp, Algebra.comp_ofId]

/-- An isomorphism `e : A ≃ₐ[R] B` of value algebras induces, by post-composition, an
isomorphism of convolution monoids, with inverse induced by `e.symm`. -/
noncomputable def _root_.AlgEquiv.mapValueMulEquiv (e : A ≃ₐ[R] B) :
    WithConv (H →ₐ[R] A) ≃* WithConv (H →ₐ[R] B) where
  toFun := mapValue (e : A →ₐ[R] B)
  invFun := mapValue (e.symm : B →ₐ[R] A)
  left_inv f := by
    rw [← MonoidHom.comp_apply, ← mapValue_comp, AlgEquiv.symm_comp, mapValue_id,
      MonoidHom.id_apply]
  right_inv f := by
    rw [← MonoidHom.comp_apply, ← mapValue_comp, AlgEquiv.comp_symm, mapValue_id,
      MonoidHom.id_apply]
  map_mul' := map_mul _

@[simp]
lemma _root_.AlgEquiv.mapValueMulEquiv_apply (e : A ≃ₐ[R] B) (f : WithConv (H →ₐ[R] A)) :
    e.mapValueMulEquiv f = mapValue (e : A →ₐ[R] B) f := (rfl)

@[simp]
lemma _root_.AlgEquiv.mapValueMulEquiv_symm_apply (e : A ≃ₐ[R] B) (f : WithConv (H →ₐ[R] B)) :
    e.mapValueMulEquiv.symm f = mapValue (e.symm : B →ₐ[R] A) f := (rfl)

end Bialgebra

section Pi

variable [Semiring H] [_root_.Bialgebra R H] {ι : Type*} {B : ι → Type*}
  [∀ i, CommSemiring (B i)] [∀ i, Algebra R (B i)]

/-- **Points valued in a product.** A point valued in a product `∀ i, B i` of commutative
algebras is the family of its components, as an isomorphism of convolution monoids. Its inverse
is Mathlib's `AlgHom.pi`. -/
noncomputable def piValueMulEquiv :
    WithConv (H →ₐ[R] ∀ i, B i) ≃* ∀ i, WithConv (H →ₐ[R] B i) where
  toFun f i := mapValue (Pi.evalAlgHom R B i) f
  invFun g := toConv (AlgHom.pi fun i ↦ (g i).ofConv)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' f g := funext fun i ↦ map_mul (mapValue (Pi.evalAlgHom R B i)) f g

@[simp]
lemma piValueMulEquiv_apply (f : WithConv (H →ₐ[R] ∀ i, B i)) (i : ι) (h : H) :
    (piValueMulEquiv f i).ofConv h = f.ofConv h i := (rfl)

@[simp]
lemma piValueMulEquiv_symm_apply (g : ∀ i, WithConv (H →ₐ[R] B i)) (h : H) (i : ι) :
    (piValueMulEquiv.symm g).ofConv h i = (g i).ofConv h := (rfl)

end Pi

section CommHopf

variable [Semiring H] [_root_.HopfAlgebra R H] [IsCocomm R H] [CommSemiring A] [Algebra R A]

/-- When `H` is moreover cocommutative, the convolution group of `R`-algebra homomorphisms
`H →ₐ[R] A` is abelian. -/
noncomputable instance convCommGroupOfSemiring : CommGroup (WithConv (H →ₐ[R] A)) where
  mul_comm := mul_comm

end CommHopf

end AlgHom

end

section
-- MODULE Algebra/AlgebraicGroup/BaseChange/Basic
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/





/-!
# Base change of bialgebra points

This file records that the usual algebraic base-change adjunction is compatible with the
convolution monoid structure on the functor of points of a bialgebra. For a bialgebra `A` over
`k`, a `k`-algebra `K`, and a commutative `K`-algebra `R`, the `R`-points of the base-changed
bialgebra `K ⊗[k] A` over `K` are the same as `k`-algebra maps `A →ₐ[k] R`, and this
identification is a monoid isomorphism for convolution. When `A` is a Hopf algebra, these are
the convolution groups of points.

This construction builds on Mathlib's tensor-product bialgebra instance, Mathlib's
tensor-product Hopf algebra antipode formula, and `AlgHom.liftEquiv`.

## Main definitions

* `TauCeti.AlgHom.baseChangePointsMulEquiv`: the convolution monoid isomorphism between
  `A →ₐ[k] R` and `K ⊗[k] A →ₐ[K] R`. When `A` is a Hopf algebra these are convolution
  groups, so this is automatically an isomorphism of groups.
* `TauCeti.AlgHom.pointsBaseChange`: base change of base-valued points,
  `WithConv (A →ₐ[k] k) →* WithConv (K ⊗[k] A →ₐ[K] K)`, as a convolution monoid homomorphism.
* `TauCeti.AlgHom.pointsLTensor`: base change of arbitrary points,
  `WithConv (A →ₐ[k] T) →* WithConv (K ⊗[k] A →ₐ[K] K ⊗[k] T)`, `f ↦ K ⊗[k] f`, as a convolution
  monoid homomorphism.
* `TauCeti.AlgHom.baseChangePointsMulEquiv_inv_apply_tmul` and
  `TauCeti.AlgHom.baseChangePointsMulEquiv_symm_inv_apply`: pointwise formulas for
  convolution inverses of base-changed points.

## See also

The tensor-product bialgebra and Hopf-algebra structures and algebra base-change adjunction
used here are from Mathlib, respectively `Mathlib.RingTheory.Bialgebra.TensorProduct`,
`Mathlib.RingTheory.HopfAlgebra.TensorProduct`, and `AlgHom.liftEquiv`.
-/


open _root_.Coalgebra HopfAlgebra TensorProduct WithConv

namespace TauCeti

namespace AlgHom

variable {k K A R : Type*} [CommSemiring k] [CommSemiring K] [Semiring A]
  [CommSemiring R] [Algebra k K] [_root_.Bialgebra k A] [Algebra K R] [Algebra k R]
  [IsScalarTower k K R]

private lemma liftEquiv_map_mul
    (f g : WithConv (A →ₐ[k] R)) :
    AlgHom.liftEquiv k K A R
      (WithConv.ofConv (f * g)) =
    WithConv.ofConv
      ((WithConv.toConv (AlgHom.liftEquiv k K A R f.ofConv) *
        WithConv.toConv (AlgHom.liftEquiv k K A R g.ofConv)) :
          WithConv (K ⊗[k] A →ₐ[K] R)) := by
  ext a
  suffices
      (Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ => .all _ _))
        (Coalgebra.comul (R := k) a) =
      (Algebra.TensorProduct.lift (AlgHom.liftEquiv k K A R f.ofConv)
        (AlgHom.liftEquiv k K A R g.ofConv) (fun _ _ => .all _ _))
        ((AlgebraTensorModule.tensorTensorTensorComm k K k K K K A A)
          (1 ⊗ₜ[K] 1 ⊗ₜ[k] Coalgebra.comul (R := k) a)) by
    simpa only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, AlgHom.liftEquiv_tmul, one_smul,
      AlgHom.convMul_apply, TensorProduct.comul_tmul, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def] using this
  induction Coalgebra.comul (R := k) a with
  | zero => simp_all
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul a₁ a₂ =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgebraTensorModule.tensorTensorTensorComm_tmul,
        AlgHom.liftEquiv_tmul, Algebra.smul_def, map_one, one_mul]

/-- Base change of bialgebra points is a monoid isomorphism for the convolution product.

The forward direction sends `f : A →ₐ[k] R` to `s ⊗ a ↦ s • f a`; the inverse restricts a
`K`-algebra map `K ⊗[k] A →ₐ[K] R` along `a ↦ 1 ⊗ a`. -/
noncomputable def baseChangePointsMulEquiv :
    WithConv (A →ₐ[k] R) ≃* WithConv (K ⊗[k] A →ₐ[K] R) :=
  { WithConv.congr (AlgHom.liftEquiv k K A R) with
  map_mul' f g := by
    apply WithConv.ext
    ext a
    simp [liftEquiv_map_mul] }

/-- The base-change convolution-monoid isomorphism sends `f` to `s ⊗ a ↦ s • f a`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_ofConv (f : WithConv (A →ₐ[k] R)) :
    (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R) f).ofConv =
      AlgHom.liftEquiv k K A R f.ofConv :=
  rfl

/-- The inverse base-change convolution-monoid isomorphism is restriction along
`A → K ⊗[k] A`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_ofConv (f : WithConv (K ⊗[k] A →ₐ[K] R)) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm f).ofConv =
      (AlgHom.liftEquiv k K A R).symm f.ofConv :=
  rfl

/-- The base-change convolution-monoid isomorphism sends `f` to `s ⊗ a ↦ s • f a`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_tmul (f : WithConv (A →ₐ[k] R)) (s : K) (a : A) :
    baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R) f (s ⊗ₜ[k] a) =
      s • f.ofConv a :=
  rfl

/-- The inverse of the base-change convolution-monoid isomorphism restricts along
`a ↦ 1 ⊗ a`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_apply (f : WithConv (K ⊗[k] A →ₐ[K] R)) (a : A) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm f).ofConv a =
      f.ofConv (1 ⊗ₜ[k] a) :=
  rfl

end AlgHom

namespace AlgHom

variable {k K A R : Type*} [CommSemiring k] [CommSemiring K] [Semiring A]
  [CommSemiring R] [Algebra k K] [_root_.HopfAlgebra k A] [Algebra K R] [Algebra k R]
  [IsScalarTower k K R]

/-- Pointwise inverse formula after base change: on a pure tensor `s ⊗ a`, the convolution
inverse of a base-changed point has value `s • f (S a)`.

The `≃*` `AlgHom.baseChangePointsMulEquiv` is automatically a group isomorphism here, since
`A` is a Hopf algebra; this records the value of an inverse point on pure tensors. -/
lemma baseChangePointsMulEquiv_inv_apply_tmul (f : WithConv (A →ₐ[k] R)) (s : K) (a : A) :
    (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R) f)⁻¹ (s ⊗ₜ[k] a) =
      s • f.ofConv (antipode k a) := by
  rw [algHom_inv_apply]
  simp

/-- Pointwise inverse formula after restricting a base-changed point along `a ↦ 1 ⊗ a`:
the inverse of `(e.symm f)` has value `f (1 ⊗ S a)` at `a`. -/
lemma baseChangePointsMulEquiv_symm_inv_apply (f : WithConv (K ⊗[k] A →ₐ[K] R)) (a : A) :
    (((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm f)⁻¹).ofConv a =
      f.ofConv (1 ⊗ₜ[k] antipode k a) := by
  rw [algHom_inv_apply, baseChangePointsMulEquiv_symm_apply]

end AlgHom

namespace AlgHom

variable {k A : Type*} (K : Type*) [CommSemiring k] [CommSemiring K] [Semiring A] [Algebra k K]
  [_root_.Bialgebra k A]

/-- Base change of base-valued points along `k → K`: a point `f : A →ₐ[k] k` of a bialgebra gives
the point `s ⊗ a ↦ s * f a` of `K ⊗[k] A` over `K`. It is a monoid homomorphism for convolution,
the composite of `AlgHom.mapValue (Algebra.ofId k K)` with `AlgHom.baseChangePointsMulEquiv`. -/
noncomputable def pointsBaseChange : WithConv (A →ₐ[k] k) →* WithConv (K ⊗[k] A →ₐ[K] K) :=
  (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := K)).toMonoidHom.comp
    (AlgHom.mapValue (Algebra.ofId k K))

/-- The base change of a point `f` sends `s ⊗ a` to `s * f a`. -/
@[simp]
lemma pointsBaseChange_apply_tmul (f : WithConv (A →ₐ[k] k)) (s : K) (a : A) :
    pointsBaseChange K f (s ⊗ₜ[k] a) = s * algebraMap k K (f.ofConv a) := by
  simp [pointsBaseChange, smul_eq_mul]

variable {T : Type*} [CommSemiring T] [Algebra k T]

/-- Base change of points along `k → K`: a point `f : A →ₐ[k] T` of a bialgebra gives the point
`K ⊗[k] f : K ⊗[k] A →ₐ[K] K ⊗[k] T`, `s ⊗ a ↦ s ⊗ f a`, of the base change. It is a monoid
homomorphism for convolution, the composite of `AlgHom.mapValue` along `T → K ⊗[k] T` with
`AlgHom.baseChangePointsMulEquiv`. -/
noncomputable def pointsLTensor : WithConv (A →ₐ[k] T) →* WithConv (K ⊗[k] A →ₐ[K] K ⊗[k] T) :=
  (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := K ⊗[k] T)).toMonoidHom.comp
    (AlgHom.mapValue Algebra.TensorProduct.includeRight)

/-- The base change of a point `f` is the algebra map `K ⊗[k] f`. -/
@[simp]
lemma ofConv_pointsLTensor (f : WithConv (A →ₐ[k] T)) :
    (pointsLTensor K f).ofConv = Algebra.TensorProduct.lTensor K f.ofConv := by
  ext a
  simp [pointsLTensor]

end AlgHom

end TauCeti

end

section
-- MODULE Algebra/AlgebraicGroup/KilledByRank
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/








/-!
# Finite flat commutative Hopf algebras are killed by their rank

Let `H` be a commutative and cocommutative Hopf algebra over a commutative ring `R`, so that
`Spec H` is a commutative affine group scheme over `R` whose group of `A`-valued points is the
convolution group `WithConv (H →ₐ[R] A)`. If `H` is finite flat over `R` of constant stalk rank
`n`, then every point is killed by `n`: `x ^ n = 1` for every commutative `R`-algebra `A` and every
`x : WithConv (H →ₐ[R] A)`. This includes Deligne's theorem for finite locally free commutative
group schemes. It is the input which turns a Drinfeld point of exact order `n` into an
`n`-torsion section, and which makes the factorisation construction of dual isogenies possible.

## Main results

* `TauCeti.AlgHom.convPow_finrank_eq_one`: when `H` is free over `R`, every point
  is killed by `Module.finrank R H`.
* `TauCeti.AlgHom.convPow_eq_one_of_rankAtStalk`: when `H` is finite flat over `R` and its
  rank at every prime is `n`, every point is killed by `n`.

## Implementation notes

The free case is the norm argument of Deligne, as presented by Tate and Oort. The convolution
algebra of linear maps `H →ₗ[R] B` plays the role of the coordinate ring of the Cartier dual with
coefficients in `B`. For `B = H` and `B' = H ⊗[R] H`, a basis of `H` over `R` makes the
convolution algebra of `H →ₗ[R] B'` free of rank `n` over that of `H →ₗ[R] B`, so it has a norm.
Write `ι₁` and `ι₂` for the two inclusions `H → H ⊗[R] H`. The shear automorphism
`a ⊗ b ↦ (a ⊗ 1) Δ b` of `H ⊗[R] H` over its left factor preserves norms and sends `ι₂` to
`Δ = ι₁ * ι₂`, where `ι₁` comes from the identity of `H`. Taking norms gives
`N(ι₂) = id ^ n * N(ι₂)`, and `ι₂` is a unit, so `id ^ n = 1`. The universal point `id` then
controls every point. The finite flat case follows by checking the resulting identity of
elements of `H` after localizing at every maximal ideal of `R`, where finite flat modules are free.

## References

* J. Tate and F. Oort, *Group schemes of prime order*, Ann. Sci. École Norm. Sup. (4) 3 (1970),
  1–21, §1.
* J. Tate, *Finite flat group schemes*, in *Modular Forms and Fermat's Last Theorem*, Springer,
  1997.
-/


open WithConv TensorProduct

namespace TauCeti.AlgHom

variable {R H : Type*} [CommRing R] [CommRing H] [_root_.HopfAlgebra R H]
  [Coalgebra.IsCocomm R H]

section Free

/-- The convolution algebra of linear maps `H → H ⊗[R] H` as an algebra over the convolution
algebra of linear maps `H → H`, through the left tensor factor. -/
noncomputable local instance convTensorAlgebra :
    Algebra (WithConv (H →ₗ[R] H)) (WithConv (H →ₗ[R] H ⊗[R] H)) :=
  ((IsScalarTower.toAlgHom R H (H ⊗[R] H)).convPostcomp (C := H)).toRingHom.toAlgebra


/-- The structure map of `convTensorAlgebra` is post-composition with the left inclusion. -/
private theorem algebraMap_convTensor (f : WithConv (H →ₗ[R] H)) :
    algebraMap (WithConv (H →ₗ[R] H)) (WithConv (H →ₗ[R] H ⊗[R] H)) f =
      (IsScalarTower.toAlgHom R H (H ⊗[R] H)).convPostcomp (C := H) f :=
  rfl

/-- A basis of `H` over `R` gives a basis of the convolution algebra of `H → H ⊗[R] H` over the
convolution algebra of `H → H`, by taking coordinates in the right tensor factor. -/
private noncomputable def convTensorBasis {ι : Type*} [Finite ι] (b : Module.Basis ι R H) :
    Module.Basis ι (WithConv (H →ₗ[R] H)) (WithConv (H →ₗ[R] H ⊗[R] H)) :=
  .ofEquivFun
    { (Algebra.TensorProduct.basis H b).convCoordEquiv R H with
      map_smul' := fun f φ => funext fun i => by
        simpa [Algebra.smul_def, algebraMap_convTensor] using
          (Algebra.TensorProduct.basis H b).convCoordEquiv_convPostcomp_mul f φ i }

/-- Post-composition with the shear automorphism `a ⊗ b ↦ (a ⊗ 1) Δ b` of `H ⊗[R] H`, as an
automorphism of the convolution algebra of `H → H ⊗[R] H` over that of `H → H`. -/
private noncomputable def convTensorShear :
    WithConv (H →ₗ[R] H ⊗[R] H) ≃ₐ[WithConv (H →ₗ[R] H)] WithConv (H →ₗ[R] H ⊗[R] H) where
  toFun := (HopfAlgebra.tensorShearMulRight (R := R) (H := H) :
    H ⊗[R] H →ₐ[R] H ⊗[R] H).convPostcomp (C := H)
  invFun :=
    (HopfAlgebra.tensorShearMulRight (R := R) (H := H)).symm.toAlgHom.convPostcomp (C := H)
  left_inv φ := by ext; simp
  right_inv φ := by ext; simp
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' f := by
    ext c
    simp [algebraMap_convTensor, Algebra.TensorProduct.algebraMap_apply]

/-- The shear sends the right tensor inclusion to the comultiplication, which is the convolution
product of the two tensor inclusions. -/
private theorem convTensorShear_includeRight :
    convTensorShear (toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap) =
      algebraMap (WithConv (H →ₗ[R] H)) (WithConv (H →ₗ[R] H ⊗[R] H))
          (toConv _root_.LinearMap.id) *
        toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap := by
  have hτ : (HopfAlgebra.tensorShearMulRight (R := R) (H := H) :
      H ⊗[R] H →ₐ[R] H ⊗[R] H).toLinearMap ∘ₗ
        (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap =
      CoalgebraStruct.comul := by
    ext a
    simp [← Algebra.TensorProduct.one_def]
  have hι : (IsScalarTower.toAlgHom R H (H ⊗[R] H)).toLinearMap ∘ₗ _root_.LinearMap.id =
      (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H).toLinearMap := by
    ext a
    simp [Algebra.TensorProduct.algebraMap_apply]
  apply ofConv_injective
  simpa only [convTensorShear, algebraMap_convTensor, AlgEquiv.coe_mk, Equiv.coe_fn_mk,
    _root_.LinearMap.convMul_def, ofConv_toConv,
    _root_.AlgHom.convPostcomp_apply_ofConv, hτ, hι] using
    congrArg ofConv (Coalgebra.comul_eq_convMul_includeLeft_includeRight (R := R) (C := H))

omit [Coalgebra.IsCocomm R H] in
/-- The right tensor inclusion is a convolution unit, being an algebra-homomorphism point. -/
private theorem isUnit_includeRight :
    IsUnit (toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap) := by
  let toLinear : WithConv (H →ₐ[R] H ⊗[R] H) →* WithConv (H →ₗ[R] H ⊗[R] H) :=
    { toFun f := toConv f.ofConv.toLinearMap
      map_one' := _root_.AlgHom.toLinearMap_convOne
      map_mul' := _root_.AlgHom.toLinearMap_convMul }
  exact (Group.isUnit (toConv Algebra.TensorProduct.includeRight)).map toLinear

/-- The convolution power of the identity of a free Hopf algebra by its rank is the unit. -/
private theorem convPow_id_eq_one [Module.Free R H] [Module.Finite R H] :
    toConv (_root_.LinearMap.id : H →ₗ[R] H) ^ Module.finrank R H = 1 := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · have : Subsingleton H := Module.subsingleton R H
    exact Subsingleton.elim _ _
  have hnorm := Algebra.norm_eq_of_algEquiv convTensorShear
    (toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H).toLinearMap)
  rw [convTensorShear_includeRight, map_mul,
    Algebra.norm_algebraMap_of_basis (convTensorBasis (Module.Free.chooseBasis R H)),
    ((isUnit_includeRight (R := R) (H := H)).map
      (Algebra.norm (WithConv (H →ₗ[R] H)))).mul_eq_right] at hnorm
  rwa [Module.finrank_eq_card_chooseBasisIndex]

/-- **Deligne's theorem, free case.** Every point of a commutative and cocommutative Hopf algebra
which is free of rank `n` over `R` is killed by `n`. -/
theorem convPow_finrank_eq_one [Module.Free R H] {A : Type*}
    [CommSemiring A] [Algebra R A] (x : WithConv (H →ₐ[R] A)) :
    x ^ Module.finrank R H = 1 := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · have : Subsingleton A := Module.subsingleton R A
    exact Subsingleton.elim (α := WithConv (H →ₐ[R] A)) _ _
  by_cases hfin : Module.Finite R H
  swap
  · rw [Module.finrank_of_not_finite hfin, pow_zero]
  have hid : toConv (_root_.AlgHom.id R H) ^ Module.finrank R H = 1 := by
    apply ofConv_injective
    apply _root_.AlgHom.toLinearMap_injective
    apply toConv_injective
    rw [_root_.AlgHom.toLinearMap_convPow, _root_.AlgHom.toLinearMap_convOne]
    exact convPow_id_eq_one
  have hx : x = AlgHom.mapValue x.ofConv (toConv (_root_.AlgHom.id R H)) := by simp
  rw [hx, ← map_pow, hid, map_one]

end Free

/-- If `H` becomes free after base change to `S`, then every point of `H` with values in an
`S`-algebra is killed by the rank of `S ⊗[R] H` over `S`. -/
private theorem convPow_eq_one_of_baseChange {S : Type*} [CommRing S] [Algebra R S]
    [Module.Free S (S ⊗[R] H)] {A : Type*} [CommSemiring A]
    [Algebra S A] [Algebra R A] [IsScalarTower R S A] (x : WithConv (H →ₐ[R] A)) :
    x ^ Module.finrank S (S ⊗[R] H) = 1 := by
  let e := baseChangePointsMulEquiv (k := R) (K := S) (A := H) (R := A)
  rw [← e.symm_apply_apply x, ← map_pow, convPow_finrank_eq_one, map_one]

/-- **Deligne's theorem.** Every point of a commutative and cocommutative Hopf algebra which is
finite flat of constant stalk rank `n` over `R` is killed by `n`. -/
theorem convPow_eq_one_of_rankAtStalk [Module.Finite R H] [Module.Flat R H] {n : ℕ}
    (hn : ∀ p, Module.rankAtStalk (R := R) H p = n) {A : Type*} [CommSemiring A] [Algebra R A]
    (x : WithConv (H →ₐ[R] A)) : x ^ n = 1 := by
  -- It suffices to treat the universal point, the identity of `H`. Its `n`-th power and the
  -- unit are compared as elements of `H` after localizing at each maximal ideal `P`, where `H`
  -- becomes free of rank `n`.
  have hid : toConv (_root_.AlgHom.id R H) ^ n = 1 := by
    apply ofConv_injective
    ext h
    refine Module.eq_of_localization_maximal (fun P _ => Localization.AtPrime P ⊗[R] H)
      (fun P _ => TensorProduct.mk R (Localization.AtPrime P) H 1) _ _ fun P _ => ?_
    let j : H →ₐ[R] Localization.AtPrime P ⊗[R] H := Algebra.TensorProduct.includeRight
    have := Module.free_of_flat_of_isLocalRing (R := Localization.AtPrime P)
      (P := Localization.AtPrime P ⊗[R] H)
    have hP := hn ⟨P, inferInstance⟩
    rw [Module.rankAtStalk_eq_finrank_tensorProduct] at hP
    have hj := convPow_eq_one_of_baseChange (S := Localization.AtPrime P) (toConv j)
    rw [hP] at hj
    have key : AlgHom.mapValue j (toConv (_root_.AlgHom.id R H) ^ n) = 1 := by
      rw [map_pow]
      simpa using hj
    have := congrArg (fun y => y.ofConv h) key
    simp only [AlgHom.mapValue_apply, ofConv_toConv, _root_.AlgHom.comp_apply,
      _root_.AlgHom.convOne_apply, j, Algebra.TensorProduct.includeRight_apply] at this
    simp [this, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
  have hx : x = AlgHom.mapValue x.ofConv (toConv (_root_.AlgHom.id R H)) := by simp
  rw [hx, ← map_pow, hid, map_one]

end TauCeti.AlgHom

end

theorem OMA.solution : type_of% @FiniteLocallyFreeGroupSchemeExponent.killed_by_rank.variants.commutative := by
  intro n R _ A _ _ _ _ _ hn
  have hn' : ∀ p, Module.rankAtStalk (R := R) A p = (n : ℕ) := fun p => congrFun hn p
  exact TauCeti.AlgHom.convPow_eq_one_of_rankAtStalk (R := R) (H := A) (n := (n : ℕ)) hn'
    (WithConv.toConv (AlgHom.id R A))
