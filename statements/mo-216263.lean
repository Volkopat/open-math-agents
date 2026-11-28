import Mathlib

/-!
# Interpolating with nonnegative polynomial coefficients

Source: Qzyx, MathOverflow question 216263 (CC BY-SA 3.0),
https://mathoverflow.net/questions/216263.
Credit: @connoranderson.

A matrix with N columns uses powers 0 through N-1. All interpolants differ by a
multiple of the nodal polynomial. For data supplied by a nonnegative power
series with positive first M coefficients, the Taylor truncation plus the
Lagrange interpolant of its residual gives explicit feasible coefficients for
every sufficiently large N. This applies to the specified data M/j².
-/
namespace OMA.S_mo_216263

open Polynomial Finset Filter

noncomputable def truncation (c : ℕ → ℝ) (N : ℕ) : ℝ[X] :=
  ∑ j ∈ range N, monomial j (c j)

noncomputable def corrected {M : ℕ} (x v : Fin M → ℝ) (c : ℕ → ℝ) (N : ℕ) : ℝ[X] :=
  truncation c N + Lagrange.interpolate univ x (fun i => v i - (truncation c N).eval (x i))

def Feasible {M : ℕ} (x v : Fin M → ℝ) (N : ℕ) (p : ℝ[X]) : Prop :=
  p.degree < (N : WithBot ℕ) ∧ (∀ j, 0 ≤ p.coeff j) ∧ ∀ i, p.eval (x i) = v i

noncomputable def nodes (M : ℕ) (i : Fin M) : ℝ := 1-((i.val:ℝ)+1)/M

noncomputable def values (M : ℕ) (i : Fin M) : ℝ := (M:ℝ)/((i.val:ℝ)+1)^2

theorem main :
    (∀ {M : ℕ} (x v : Fin M → ℝ), Function.Injective x →
      (∀ p : ℝ[X], (∀ i, p.eval (x i) = v i) ↔
        ∃ q, p = Lagrange.interpolate univ x v + Lagrange.nodal univ x*q) ∧
      (∀ c : ℕ → ℝ, (∀ j, 0 ≤ c j) → (∀ j < M, 0 < c j) →
        (∀ i, HasSum (fun j => c j*(x i)^j) (v i)) →
        ∀ᶠ N in atTop, Feasible x v N (corrected x v c N))) ∧
    ∀ M : ℕ, 0 < M → ∀ᶠ N in atTop,
      Feasible (nodes M) (values M) N
        (corrected (nodes M) (values M) (fun j => ((j:ℝ)+1)/M) N) := by
  sorry

end OMA.S_mo_216263
