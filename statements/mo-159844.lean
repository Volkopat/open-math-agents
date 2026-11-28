import Mathlib

/-!
# Sharp symmetric perturbations preserving positive solutions

Source: https://mathoverflow.net/questions/159844 (Peter Dukes, CC BY-SA 3.0).
Credit: @connoranderson

The norm is the induced infinity norm (maximum absolute row sum). Below any
positive spectral lower bound the general test removes one row and column,
and replaces the deleted row by scalar capacities sharing the same norm
budget. Testing each choice of deleted coordinate gives the exact criterion.
Even the identity has radius strictly smaller than one from dimension three
onward. In dimension n+1 its radius is n/(2n-1) for n≥1. Thus the author's
dimension-free lower bound 1/(2‖A⁻¹‖∞) has the best possible constant.
-/

namespace OMA.S_mo_159844
open Finset Matrix
noncomputable section

abbrev Mat (ι : Type*) := Matrix ι ι ℝ

def sym {ι : Type*} (A : Mat ι) := ∀ i j, A i j=A j i

def rows {ι : Type*} [Fintype ι] (A : Mat ι) (δ : ℝ) := ∀ i, ∑ j, |A i j| ≤ δ

def protectedAt {ι : Type*} [Fintype ι] (A : Mat ι) (i : ι) (r : ℝ) :=
  ∀ δ : ℝ, 0 ≤ δ → δ < r → ∀ E : Mat ι, sym E → rows E δ →
    Function.Bijective (A+E).mulVec ∧ ∀ x, (A+E).mulVec x=1 → 0<x i

def coercive {ι : Type*} [Fintype ι] (A : Mat ι) (μ : ℝ) :=
  ∀ x, μ*(∑ i, (x i)^2) ≤ ∑ i, x i * A.mulVec x i

def principal {ι : Type*} (A : Mat (Option ι)) : Mat ι := fun i j => A (some i) (some j)

def test {ι : Type*} [Fintype ι] (A : Mat (Option ι)) (r : ℝ) :=
  ∀ δ : ℝ, 0 ≤ δ → δ<r → ∀ (F : Mat ι) (e : ι → ℝ), sym F →
    (∑ j, |e j|) ≤ δ → (∀ j, |e j| + ∑ k, |F j k| ≤ δ) →
    ∀ u, (principal A + F).mulVec u=1 → ∑ j, (A none (some j)+e j)*u j < 1

def radius (n : ℕ) : ℝ := (n:ℝ)/(2*n-1)

theorem main :
    (∀ {ι : Type} [Fintype ι] (A : Mat (Option ι)) (μ r : ℝ),
      sym A → coercive A μ → r ≤ μ → (protectedAt A none r ↔ test A r)) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Mat ι) (K : ℝ), 0<K →
      B*A=1 → A.mulVec 1=1 → rows B K → ∀ i, protectedAt A i (1/(2*K))) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, (∀ i : Option (Fin n), protectedAt 1 i r) ↔ r ≤ radius n) ∧
    (∀ c : ℝ, 1/2 < c → ∃ n : ℕ, 1 ≤ n ∧ radius n < c) := by
  sorry
end
end OMA.S_mo_159844
