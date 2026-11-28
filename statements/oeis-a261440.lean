import Mathlib

/-!
# Schulte's implicit trinomial series and its lattice paths

Source: https://oeis.org/A261440 (Werner Schulte, 2015).

The formal series is specified independently by its unique defining equation.
A path is a finite word in labels 0, 1, 2. Label r represents the planar step
(1,n*r-1). The positive-height test before subtraction prevents a step below
the horizontal axis; the empty word is accepted precisely at height zero.
For positive n the three labels represent distinct steps. Thus pathCount counts
actual nonnegative paths with the prescribed length and endpoint, rather than
being defined by a recurrence of numbers or by the proposed generating series.

The all-m assertions include the m=1 assertions. The latter are displayed too
so that both source formulas and both source path claims remain explicit.
The logarithmic coefficient identity is accompanied by the source's formal
exponential identity. All sums and formal series have rational coefficients.
Natural-number subtractions in binomial indices are truncated; when j>N the
factor binomial(N,j) vanishes, as in the source's finite sums.
-/

namespace OMA.S_oeis_a261440
open PowerSeries

def Native (n : ℕ) (P : PowerSeries ℚ) : Prop :=
  P = 1 + X * P^n + X^2 * P^(2*n)

def IsPath (n : ℕ) : ℕ → List ℕ → Prop
  | h, [] => h=0
  | h, r::w => r ≤ 2 ∧ 0 < h+n*r ∧ IsPath n (h+n*r-1) w

noncomputable def pathCount (n length initialHeight : ℕ) : ℕ :=
  Nat.card {w : List ℕ // w.length=length ∧ IsPath n initialHeight w}

def signedSum (N k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k+1), (-1:ℚ)^j * (Nat.choose N j:ℚ) *
    (Nat.choose (2*N-2*j) (k-j):ℚ)

noncomputable def logarithmicSeries (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => if k=0 then 0 else
    (((n*k:ℕ):ℚ))⁻¹ * signedSum (n*k) k

theorem main :
    (∀ n : ℕ, ∃! P : PowerSeries ℚ, Native n P) ∧
    ∀ (n : ℕ) (P : PowerSeries ℚ), Native n P →
      (∀ k : ℕ, coeff k P =
        (((n*k+1:ℕ):ℚ))⁻¹ * signedSum (n*k+1) k) ∧
      (0 < n →
        (∀ m k : ℕ, 0 < m → coeff k (P^m) =
          (m:ℚ) / ((n*k+m:ℕ):ℚ) * signedSum (n*k+m) k) ∧
        (∀ k : ℕ, (pathCount n (n*k) 0:ℚ) = coeff k P) ∧
        (∀ m k : ℕ, 0 < m →
          (pathCount n (n*k+m-1) (m-1):ℚ) = coeff k (P^m)) ∧
        (∀ k : ℕ, 0 < k → coeff k (logOf P) =
          (((n*k:ℕ):ℚ))⁻¹ * signedSum (n*k) k) ∧
        (PowerSeries.exp ℚ).subst (logarithmicSeries n) = P) := by
  sorry

end OMA.S_oeis_a261440
