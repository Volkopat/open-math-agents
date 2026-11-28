import Mathlib

/-!
# Consistency of dyadic Bernstein approximations

Peter O. asks whether the uniform approximation rate of the Bernstein
polynomials of operator outputs forces a uniform lower bound on the change
of their coefficients under degree elevation. We use the equivalent
inequality (PB) in the question. Stage i has degree 2^i. The elevation
operator averages the old coefficients with hypergeometric weights.

The scale M is the maximum of the absolute derivatives in the smooth case.
The Lipschitz version uses the supremum of the absolute function and of the
difference quotients for derivatives of orders below r. Values and
derivatives are restricted to the closed unit interval.

Source: https://mathoverflow.net/questions/427595 (Peter O., CC BY-SA)
Credit: @connoranderson
-/

namespace OMA.S_mo_427595
open Set Filter
open scoped BigOperators

abbrev interval : Set ℝ := Icc 0 1

noncomputable def basis (n k : ℕ) (x : ℝ) : ℝ :=
  (n.choose k : ℝ)*x^k*(1-x)^(n-k)

noncomputable def bernstein (n : ℕ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), g ((k:ℝ)/n)*basis n k x

noncomputable def elevated (n k : ℕ) (g : ℝ → ℝ) : ℝ :=
  (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, (n.choose p.1 : ℝ)*(n.choose p.2 : ℝ)*g ((p.1:ℝ)/n)) /
    ((2*n).choose k : ℝ)

def smoothControl (r : ℕ) (f : ℝ → ℝ) (M : ℝ) : Prop :=
  ContDiffOn ℝ r f interval ∧
  IsGreatest {z : ℝ | ∃ j ≤ r, ∃ x ∈ interval, z=|iteratedDerivWithin j f interval x|} M

def lipschitzControl (r : ℕ) (f : ℝ → ℝ) (M : ℝ) : Prop :=
  ContDiffOn ℝ (r-1 : ℕ) f interval ∧
  IsLUB ((fun x => |f x|) '' interval ∪ {z : ℝ | ∃ j < r, ∃ x ∈ interval, ∃ y ∈ interval,
      x≠y ∧ z=|iteratedDerivWithin j f interval x - iteratedDerivWithin j f interval y| / |x-y|}) M

theorem main : ∀ (r : ℕ) (W : ℕ → (ℝ → ℝ) → ℝ → ℝ) (D : ℝ), 1 ≤ r → 0 < D →
    (∀ i g, ContinuousOn g interval → BddAbove ((fun x => |W i g x|) '' interval)) →
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (M : ℝ),
      MapsTo f interval (Ioo 0 1) → (smoothControl r f M ∨ lipschitzControl r f M) →
      TendstoUniformlyOn (fun i => W i f) f atTop interval →
      (∀ i : ℕ, ∀ x ∈ interval, |f x-bernstein (2^i) (W i f) x| ≤ D*M/(2^i : ℝ)^((r:ℝ)/2)) →
      ∀ i k : ℕ, k ≤ 2*(2^i) →
        elevated (2^i) k (W i f) ≤
          W (i+1) f ((k:ℝ)/(2*(2^i : ℝ)))+C*M/(2^i : ℝ)^((r:ℝ)/2) := by
  sorry

end OMA.S_mo_427595
