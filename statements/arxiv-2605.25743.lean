import Mathlib

namespace OMA.S_arxiv_2605_25743

/-- Elementary symmetric polynomial `e_j` in `n` real variables. -/
noncomputable def esymmPoly (n j : ℕ) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.esymm (Fin n) ℝ j

/-- Discriminant of a quartic polynomial `a t^4 + b t^3 + c t^2 + d t + e`. -/
def quarticDisc {R : Type*} [CommRing R] (a b c d e : R) : R :=
  256 * a ^ 3 * e ^ 3 - 192 * a ^ 2 * b * d * e ^ 2 - 128 * a ^ 2 * c ^ 2 * e ^ 2 +
  144 * a ^ 2 * c * d ^ 2 * e - 27 * a ^ 2 * d ^ 4 + 144 * a * b ^ 2 * c * e ^ 2 -
  6 * a * b ^ 2 * d ^ 2 * e - 80 * a * b * c ^ 2 * d * e + 18 * a * b * c * d ^ 3 +
  16 * a * c ^ 4 * e - 4 * a * c ^ 3 * d ^ 2 - 27 * b ^ 4 * e ^ 2 +
  18 * b ^ 3 * c * d * e - 4 * b ^ 3 * d ^ 3 - 4 * b ^ 2 * c ^ 3 * e + b ^ 2 * c ^ 2 * d ^ 2

/-- Discriminant of the scaled `(n - 4)`-th derivative `P^{(n - 4)}(t) / (n - 4)!`
of the generic monic degree-`n` polynomial `P(t) = ∏_{i : Fin n} (t - X_i)`. -/
noncomputable def terminalQuarticDisc (n : ℕ) : MvPolynomial (Fin n) ℝ :=
  quarticDisc
    (MvPolynomial.C (Nat.choose n 4 : ℝ))
    (-MvPolynomial.C (Nat.choose (n - 1) 3 : ℝ) * esymmPoly n 1)
    (MvPolynomial.C (Nat.choose (n - 2) 2 : ℝ) * esymmPoly n 2)
    (-MvPolynomial.C ((n - 3 : ℕ) : ℝ) * esymmPoly n 3)
    (esymmPoly n 4)

/-- Symmetrized square-graph monomial associated to a finite multigraph with edge list `E`
on `Fin n`: `∑_{σ ∈ S_n} ∏_{(u, v) ∈ E} (X_{σ u} - X_{σ v})^2`. -/
noncomputable def symSquareGraphPoly (n : ℕ) (E : List (Fin n × Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  ∑ σ : Equiv.Perm (Fin n),
    (E.map (fun e => (MvPolynomial.X (σ e.1) - MvPolynomial.X (σ e.2)) ^ 2)).prod

/-- Membership in the square-graph cone of Alexandersson and Shapiro: a finite nonnegative
linear combination of symmetrized square-graph monomials. -/
def InSquareGraphCone (n : ℕ) (f : MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℝ) (E : Fin m → List (Fin n × Fin n)),
    (∀ i, 0 ≤ c i) ∧
    f = ∑ i : Fin m, MvPolynomial.C (c i) * symSquareGraphPoly n (E i)

/-- The Alexandersson–Shapiro square-graph cone conjecture for the terminal quartic family
`k = n - 4` (refuted in arXiv:2605.25743 at `n = 23`): for every `n ≥ 4`, the discriminant of
the `(n - 4)`-th derivative of `P(t) = ∏ (t - X_i)` lies in the square-graph cone. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n → InSquareGraphCone n (terminalQuarticDisc n) := by sorry

end OMA.S_arxiv_2605_25743
