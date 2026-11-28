import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice.Nat

/-!
# MO 107600: density of pairwise noncommuting matrices

Source:
https://mathoverflow.net/questions/107600/what-is-the-order-of-the-largest-subset-of-m-nz-p-such-that-no-two-elements-co

For positive n and prime p, the source defines A(n,p) as the largest size of
a subset of M_n(Z_p) whose distinct members never commute. Its explicit
conjecture is that A(n,p)/p^(n^2) tends to 1 as p tends to infinity through
the primes. We state this limit using the usual epsilon/N definition.

The supremum below is over the attainable finite cardinalities. For prime p
the matrix ring is finite, so this is the ordinary maximum. The definition
at nonprime moduli does not enter the conjecture. The separate source requests
for sharper asymptotics and growth with n are not part of this assertion.
-/

namespace OMA.S_mo_107600

/-- Cardinalities of finite sets of matrices with pairwise noncommuting members. -/
def attainableSizes (n p : ℕ) : Set ℕ :=
  {k | ∃ S : Finset (Matrix (Fin n) (Fin n) (ZMod p)),
    (S : Set (Matrix (Fin n) (Fin n) (ZMod p))).Pairwise
      (fun A B => ¬ Commute A B) ∧ S.card = k}

/-- The largest attainable cardinality when the matrix ring is finite. -/
noncomputable def maxNoncommuting (n p : ℕ) : ℕ := sSup (attainableSizes n p)

/-- The proposed density-one limit, as the modulus tends to infinity through primes. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ p : ℕ, p.Prime → N ≤ p →
        |(maxNoncommuting n p : ℝ) / (p : ℝ) ^ (n * n) - 1| < ε := by
  sorry

end OMA.S_mo_107600
