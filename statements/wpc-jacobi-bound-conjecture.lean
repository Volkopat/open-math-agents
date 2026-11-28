import Mathlib

/-!
# Jacobi bound conjecture for differential systems

Source: https://en.wikipedia.org/wiki/Jacobi_bound_problem
Credit: @eltociear

Wikipedia: let `(K, ∂)` be a differential field of characteristic zero and `Γ` the differential
algebraic variety defined by the vanishing of differential polynomials
`u₁, …, uₙ ∈ K{x₁, …, xₙ}`. If `Γ₁` is an irreducible component of `Γ` of finite absolute
dimension, then `a(Γ₁) ≤ J(u₁, …, uₙ)`, where the Jacobi number is
`J = max_{σ ∈ Sₙ} ∑ᵢ ord_{xᵢ}(u_{σ(i)})`.

Encoding (standard Ritt–Kolchin dictionary):
* `K{x₁, …, xₙ}` is the polynomial ring over `K` in the indeterminates `x_j^{(k)}`, here
  `X (j, k)` for `j : Fin n`, `k : ℕ`, with the derivation `diffDeriv δ` extending `δ` on the
  coefficients and sending `x_j^{(k)}` to `x_j^{(k+1)}`.
* `ord_{x_j}(u)` is the largest `k` such that `x_j^{(k)}` occurs in `u`, and `⊥ = -∞` when no
  derivative of `x_j` occurs (the usual convention of Jacobi, Ritt and Lando). The Jacobi number
  lives in `WithBot ℕ`, where `⊥` absorbs sums, so a permutation meeting a `-∞` entry contributes
  `-∞`.
* By the differential Nullstellensatz, the irreducible components of `Γ` correspond to the
  minimal prime differential ideals `P` of `K{x}` containing `u₁, …, uₙ`; the absolute dimension
  (Ritt's order) of the component is the transcendence degree over `K` of its differential
  function field, i.e. `Algebra.trdeg K (K{x} ⧸ P)` (a domain has the transcendence degree of
  its fraction field).
* "Finite absolute dimension" is `trdeg < ℵ₀`; the conclusion says `J` is a natural number `m`
  (not `-∞`) and `trdeg ≤ m`.
-/

universe u

namespace OMA.S_wpc_jacobi_bound_conjecture

open MvPolynomial

/-- The derivation of the differential polynomial ring `K{x₀, …, x_{n-1}}`: it applies `δ` to the
coefficients and sends `x_j^{(k)} = X (j, k)` to `x_j^{(k+1)} = X (j, k + 1)`. -/
noncomputable def diffDeriv {K : Type u} [Field K] {n : ℕ} (δ : Derivation ℤ K K)
    (f : MvPolynomial (Fin n × ℕ) K) : MvPolynomial (Fin n × ℕ) K :=
  (∑ m ∈ f.support, monomial m (δ (f.coeff m))) +
    mkDerivation K (fun v : Fin n × ℕ => (X (v.1, v.2 + 1) : MvPolynomial (Fin n × ℕ) K)) f

/-- `ord_{x_j}(u)`: the highest order of a derivative of `x_j` occurring in `u`,
`⊥` (that is `-∞`) when none occurs. -/
noncomputable def ord {K : Type u} [Field K] {n : ℕ} (j : Fin n)
    (f : MvPolynomial (Fin n × ℕ) K) : WithBot ℕ :=
  (f.vars.filter (fun v => v.1 = j)).sup (fun v => (v.2 : WithBot ℕ))

/-- The Jacobi number `J(u₁, …, uₙ) = max_{σ ∈ Sₙ} ∑ᵢ ord_{xᵢ}(u_{σ(i)})`. -/
noncomputable def jacobiNumber {K : Type u} [Field K] {n : ℕ}
    (U : Fin n → MvPolynomial (Fin n × ℕ) K) : WithBot ℕ :=
  Finset.univ.sup (fun σ : Equiv.Perm (Fin n) => ∑ i, ord i (U (σ i)))

/-- `P` is a minimal prime differential ideal containing `u₁, …, uₙ`, i.e. it defines an
irreducible component of the differential variety `u₁ = … = uₙ = 0`. -/
def IsComponent {K : Type u} [Field K] {n : ℕ} (δ : Derivation ℤ K K)
    (U : Fin n → MvPolynomial (Fin n × ℕ) K) (P : Ideal (MvPolynomial (Fin n × ℕ) K)) : Prop :=
  Minimal (fun Q : Ideal (MvPolynomial (Fin n × ℕ) K) =>
    Q.IsPrime ∧ (∀ p ∈ Q, diffDeriv δ p ∈ Q) ∧ ∀ i, U i ∈ Q) P

theorem main : ∀ (K : Type u) [Field K] [CharZero K] (δ : Derivation ℤ K K) (n : ℕ)
    (U : Fin n → MvPolynomial (Fin n × ℕ) K) (P : Ideal (MvPolynomial (Fin n × ℕ) K)),
    IsComponent δ U P →
    Algebra.trdeg K (MvPolynomial (Fin n × ℕ) K ⧸ P) < Cardinal.aleph0 →
    ∃ m : ℕ, jacobiNumber U = (m : WithBot ℕ) ∧
      Algebra.trdeg K (MvPolynomial (Fin n × ℕ) K ⧸ P) ≤ (m : Cardinal) := by
  sorry

end OMA.S_wpc_jacobi_bound_conjecture
