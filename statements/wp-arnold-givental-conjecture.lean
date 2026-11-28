import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Immersion

/-!
# Arnold–Givental conjecture

Source: https://en.wikipedia.org/wiki/Arnold–Givental_conjecture
Credit: @SubhanAfz

If a compact real Lagrangian in a compact symplectic manifold meets its
Hamiltonian image transversely, the number of intersection points is at
least the sum of its mod-two Betti numbers. Bai, Shelukhin, Wang and Xu
announced a proof in arXiv:2608.27242.
-/

namespace OMA.S_wp_arnold_givental_conjecture

open Manifold Set Topology
open scoped ContDiff Manifold

universe u

abbrev Coord (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable abbrev model (n : ℕ) := 𝓘(ℝ, Coord n)
abbrev TwoForm (n : ℕ) := Coord n [⋀^Fin 2]→L[ℝ] ℝ

/-- The pullback of a two-form to a chart by its inverse. -/
noncomputable def chartForm {d : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (Coord d) M] [IsManifold (model d) ∞ M]
    (form : M → TwoForm d) (p : M) : Coord d → TwoForm d :=
  fun x =>
    let inverse := (chartAt (Coord d) p).symm
    (form (inverse x)).compContinuousLinearMap (mfderiv (model d) (model d) inverse x)

/-- A smooth, closed, pointwise nondegenerate two-form. -/
def IsSymplectic {d : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (Coord d) M] [IsManifold (model d) ∞ M]
    (form : M → TwoForm d) : Prop :=
  (∀ p v, (∀ w, form p ![v, w] = 0) → v = 0) ∧
  ∀ p, ContDiffOn ℝ ∞ (chartForm form p) (chartAt (Coord d) p).target ∧
    ∀ x ∈ (chartAt (Coord d) p).target, extDeriv (chartForm form p) x = 0

/-- A smooth isotopy starting at the identity, generated on the unit time
interval by a smooth Hamiltonian. The convention is ι_X ω = -dH. -/
def IsHamiltonianFlow {d : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (Coord d) M] [IsManifold (model d) ∞ M]
    (form : M → TwoForm d) (φ : ℝ → Diffeomorph (model d) (model d) M M ∞) : Prop :=
  ∃ H : ℝ × M → ℝ,
    ContMDiffOn (𝓘(ℝ, ℝ).prod (model d)) 𝓘(ℝ, ℝ) ∞ H (Icc 0 1 ×ˢ univ) ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod (model d)) (model d) ∞
      (fun p : ℝ × M => φ p.1 p.2) (Icc 0 1 ×ˢ univ) ∧
    (∀ x, φ 0 x = x) ∧
    ∀ (t : ℝ) (_ : t ∈ Icc 0 1) (x : M) (v : Coord d),
      form (φ t x) ![
        mfderivWithin 𝓘(ℝ, ℝ) (model d) (fun s => φ s x) (Icc 0 1) t (1 : ℝ), v] =
        -mfderiv (model d) 𝓘(ℝ, ℝ) (fun y => H (t, y)) (φ t x) v

/-- The dimension of singular homology over the field with two elements. -/
noncomputable def modTwoBetti (L : Type u) [TopologicalSpace L] (j : ℕ) : ℕ :=
  let C := ModuleCat.{u} (ZMod 2)
  let H := ((AlgebraicTopology.singularHomologyFunctor C j).obj
    (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj (TopCat.of L)
  Module.finrank (ZMod 2) H

theorem main : ∀ (n : ℕ) (M L : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (Coord (2 * n)) M] [IsManifold (model (2 * n)) ∞ M]
    [TopologicalSpace L] [T2Space L] [SecondCountableTopology L] [CompactSpace L]
    [ChartedSpace (Coord n) L] [IsManifold (model n) ∞ L]
    (form : M → TwoForm (2 * n)) (hForm : IsSymplectic form)
    (ι : L → M) (hEmbed : IsEmbedding ι)
    (hImmersion : IsImmersion (model n) (model (2 * n)) ∞ ι)
    (hLagrangian : ∀ x v w,
      form (ι x) ![mfderiv (model n) (model (2 * n)) ι x v,
        mfderiv (model n) (model (2 * n)) ι x w] = 0)
    (τ : Diffeomorph (model (2 * n)) (model (2 * n)) M M ∞)
    (hInvolution : Function.Involutive τ)
    (hAnti : ∀ x, (form (τ x)).compContinuousLinearMap
      (mfderiv (model (2 * n)) (model (2 * n)) τ x) = -form x)
    (hFixed : Set.range ι = {x | τ x = x})
    (φ : ℝ → Diffeomorph (model (2 * n)) (model (2 * n)) M M ∞)
    (hHamiltonian : IsHamiltonianFlow form φ)
    (hTransverse : ∀ x y : L, φ 1 (ι x) = ι y →
      (mfderiv (model n) (model (2 * n)) (φ 1 ∘ ι) x).range ⊔
        (mfderiv (model n) (model (2 * n)) ι y).range = ⊤),
    ((∑ j ∈ Finset.range (n + 1), modTwoBetti L j : ℕ) : ℕ∞) ≤
      (Set.range (φ 1 ∘ ι) ∩ Set.range ι).encard := by
  sorry

end OMA.S_wp_arnold_givental_conjecture
