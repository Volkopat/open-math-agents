import Mathlib

/-!
# The Hermite remainder point for the reciprocal square

Source: spray_user, https://mathoverflow.net/questions/221284 (CC BY-SA 3.0).
Credit: @connoranderson.

We use the n distinct double nodes in the displayed remainder formula and
the interpolant of degree at most 2n−1, as clarified by the author.
For f(x)=1/x² the normalized derivative of order 2n is (2n+1)/x^(2n+2).
Away from the nodes the positive remainder point is unique. At a node the
remainder product vanishes and the formula alone cannot determine a point.
The asymptotic claim interprets much larger as the ratio tending to infinity.
-/

namespace OMA.S_mo_221284
open Polynomial Filter
open scoped Topology
noncomputable section

def Interpolates {n : ℕ} (p : ℝ[X]) (t : Fin n → ℝ) : Prop :=
  p.natDegree < 2*n ∧ ∀ i, p.eval (t i) = 1/(t i)^2 ∧ p.derivative.eval (t i) = -2/(t i)^3

def Remainder {n : ℕ} (p : ℝ[X]) (t : Fin n → ℝ) (x τ : ℝ) : Prop :=
  1/x^2 = p.eval x + (2*n+1:ℕ)/τ^(2*n+2) * ∏ i, (x-t i)^2

def point {n : ℕ} (t : Fin n → ℝ) (x : ℝ) : ℝ :=
  (((2*n+1:ℕ):ℝ)*x^2*(∏ i,(t i)^2)/(1+2*x*∑ i,(t i)⁻¹))^(((2*n+2:ℕ):ℝ)⁻¹)

def scale {n : ℕ} (ε x : ℝ) (t : Fin n → ℝ) : ℝ :=
  (x/ε)*(∏ i,(t i/ε)^2)

theorem main :
    (∀ (n : ℕ) (t : Fin n → ℝ) (p : ℝ[X]) (x τ : ℝ), Function.Injective t →
      (∀ i, 0<t i) → Interpolates p t → 0<x → (∀ i, x≠t i) → 0<τ →
      (Remainder p t x τ ↔ τ=point t x)) ∧
    (∀ (n : ℕ) (ε x : ℕ → ℝ) (t : ℕ → Fin n → ℝ), Tendsto ε atTop (𝓝 0) →
      (∀ j, 0<ε j ∧ ε j≤x j ∧ x j≤1 ∧ ∀ i, ε j≤t j i ∧ t j i≤1) →
      (Tendsto (fun j => point (t j) (x j)/ε j) atTop atTop ↔
       Tendsto (fun j => scale (ε j) (x j) (t j)) atTop atTop)) := by
  sorry

end
end OMA.S_mo_221284
