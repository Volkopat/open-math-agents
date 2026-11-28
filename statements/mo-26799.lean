import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Card
import Mathlib.Topology.Connected.Basic

open Polynomial

namespace OMA.S_mo_26799

/-- The coefficient vector encodes the terms below the monic leading term. -/
noncomputable def monicPolynomial (n : ℕ) (a : Fin n → ℂ) : Polynomial ℂ :=
  X ^ n + ∑ i : Fin n, C (a i) * X ^ i.val

/-- Every root is a vertex of the convex hull of the roots, and the
number of distinct roots equals the degree. -/
def rootsInStrictConvexPosition (p : Polynomial ℂ) (m : ℕ) : Prop :=
  let roots : Set ℂ := {z | p.eval z = 0}
  roots.ncard = m ∧ ∀ z ∈ roots, z ∉ convexHull ℝ (roots \ {z})

/-- Is the space of complex monic polynomials whose indicated derivatives
have roots in strictly convex position connected? -/
theorem main :
    ∀ n : ℕ,
      IsConnected {a : Fin n → ℂ |
        ∀ k : ℕ, k + 2 ≤ n →
          rootsInStrictConvexPosition ((Polynomial.derivative^[k]) (monicPolynomial n a))
            (n - k)} := by
  sorry

end OMA.S_mo_26799
