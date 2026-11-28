import Mathlib

namespace OMA.S_arxiv_2412_01494

/-- A real `q × q` collision matrix `C` defines a valid stable linear 1D lattice Boltzmann
scheme (with one conserved mass variable) if:
1. every entry of `C` is strictly positive,
2. each column of `C` sums to `1` (conservation of mass), and
3. `C` is diagonalizable in moment space via an invertible moment matrix `M` whose first row
   is all ones, with relaxation rates `s 0 = 0`, `s i ∈ (0, 2)` for `i ≠ 0`, and equilibrium
   moments `eq` with `eq 0 = 1`. -/
def IsValidLBCollision {q : ℕ} [NeZero q] (C : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  (∀ i j : Fin q, 0 < C i j) ∧
  (∀ j : Fin q, ∑ i : Fin q, C i j = 1) ∧
  ∃ (M : Matrix (Fin q) (Fin q) ℝ) (s eq : Fin q → ℝ),
    M.det ≠ 0 ∧
    (∀ j : Fin q, M 0 j = 1) ∧
    s 0 = 0 ∧
    (∀ i : Fin q, i ≠ 0 → 0 < s i ∧ s i < 2) ∧
    eq 0 = 1 ∧
    M * C =
      (Matrix.diagonal (fun i => 1 - s i) +
        Matrix.of fun i j => if j = 0 then s i * eq i else 0) * M

/-- The characteristic polynomial of the spatial-shift evolution matrix
`E(ξ) = diag(ξ^{c_0}, ..., ξ^{c_{q-1}}) * C` at nonzero shift parameter `ξ : ℝ`, which
determines the equivalent multi-step finite difference scheme on the conserved variable
(Bellotti–Graille–Massot 2022). -/
noncomputable def fdsCharPoly {q : ℕ} (c : Fin q → ℤ) (C : Matrix (Fin q) (Fin q) ℝ) (ξ : ℝ) :
    Polynomial ℝ :=
  (Matrix.diagonal (fun i => ξ ^ (c i)) * C).charpoly

/-- Conjecture (addressed in Kummer & Simonis, arXiv:2412.01494):
Every multi-step finite difference scheme arising from a stable linear lattice Boltzmann
scheme has a unique lattice Boltzmann formulation on the same discrete velocity stencil. -/
theorem main :
    ∀ (q : ℕ) [NeZero q] (c : Fin q → ℤ) (C₁ C₂ : Matrix (Fin q) (Fin q) ℝ),
      IsValidLBCollision C₁ →
      IsValidLBCollision C₂ →
      (∀ ξ : ℝ, ξ ≠ 0 → fdsCharPoly c C₁ ξ = fdsCharPoly c C₂ ξ) →
      C₁ = C₂ := by
  sorry

end OMA.S_arxiv_2412_01494
