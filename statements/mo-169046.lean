import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

namespace OMA.S_mo_169046

open scoped BigOperators

abbrev SymmetricPolynomialAmbient (N : ℕ) := MvPolynomial (Fin N) ℝ
abbrev Pairing (N : ℕ) :=
  SymmetricPolynomialAmbient N →ₗ[ℝ] SymmetricPolynomialAmbient N →ₗ[ℝ] ℝ
abbrev JackFamily (N : ℕ) := ∀ d : ℕ, Nat.Partition d → SymmetricPolynomialAmbient N

/-- The usual centralizer factor for the cycle type represented by a partition. -/
def centralizerFactor {d : ℕ} (lam : Nat.Partition d) : ℕ :=
  ∏ i ∈ lam.parts.toFinset, i ^ lam.parts.count i * (lam.parts.count i).factorial

/-- Strict dominance for two partitions of the same integer. -/
def StrictlyDominated {d : ℕ} (μ lam : Nat.Partition d) : Prop :=
  μ ≠ lam ∧ ∀ i : ℕ,
    ((μ.parts.sort (· ≥ ·)).take i).sum ≤ ((lam.parts.sort (· ≥ ·)).take i).sum

/-- The Jack scalar product on power sums in the stable degree range. -/
def IsJackPairing {N : ℕ} (α : ℝ) (B : Pairing N) : Prop :=
  ∀ (d e : ℕ), d ≤ N → e ≤ N →
    ∀ (lam : Nat.Partition d) (μ : Nat.Partition e),
      B (MvPolynomial.psumPart (Fin N) ℝ lam) (MvPolynomial.psumPart (Fin N) ℝ μ) =
        if lam.parts = μ.parts then α ^ lam.parts.card * (centralizerFactor lam : ℝ) else 0

/-- The monic Jack polynomials are triangular in the monomial symmetric basis
and orthogonal for the Jack scalar product. -/
def IsMonicJackFamily {N : ℕ} (B : Pairing N) (P : JackFamily N) : Prop :=
  (∀ d : ℕ, d ≤ N → ∀ lam : Nat.Partition d,
    P d lam - MvPolynomial.msymm (Fin N) ℝ lam ∈
      Submodule.span ℝ {f | ∃ μ : Nat.Partition d,
        StrictlyDominated μ lam ∧ f = MvPolynomial.msymm (Fin N) ℝ μ}) ∧
  (∀ (d e : ℕ), d ≤ N → e ≤ N →
    ∀ (lam : Nat.Partition d) (μ : Nat.Partition e),
      lam.parts ≠ μ.parts → B (P d lam) (P e μ) = 0)

/-- Littlewood–Richardson coefficients for Jack symmetric functions are
nonnegative at every positive real parameter. Monic normalization preserves their sign. -/
theorem main :
    ∀ (N : ℕ) (α : ℝ), 0 < α →
      ∃ (B : Pairing N) (P : JackFamily N),
        IsJackPairing α B ∧ IsMonicJackFamily B P ∧
        ∀ (d e f : ℕ), d ≤ N → e + f ≤ N →
          ∀ (lam : Nat.Partition d) (μ : Nat.Partition e) (ν : Nat.Partition f),
            0 ≤ B (P e μ * P f ν) (P d lam) := by
  sorry

end OMA.S_mo_169046
