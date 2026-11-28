import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.NumberTheory.Divisors
import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a056793

/-- Least common multiple of `{1, 2, ..., n}` (OEIS A003418). -/
def lcmUpTo (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

/-- OEIS A056793: number of divisors of `lcm(1..n)`. -/
def a056793 (n : ℕ) : ℕ :=
  (lcmUpTo n).divisors.card

/-- OEIS A034699: largest prime power factor of `m` (with `1` for `m = 1`). -/
def maxPrimePower (m : ℕ) : ℕ :=
  max 1 (m.primeFactors.sup (fun p => p ^ (m.factorization p)))

/-- OEIS A101207: number of positive integers having `k` as their greatest prime power factor. -/
noncomputable def a101207 (k : ℕ) : ℕ :=
  Nat.card {m : ℕ // 1 ≤ m ∧ maxPrimePower m = k}

/-- OEIS A056793 conjecture (Sean A. Irvine, Jun 25 2022):
`a056793` is the sequence of partial sums of `A101207`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a056793 n = ∑ k ∈ Finset.Icc 1 n, a101207 k := by
  sorry

end OMA.S_oeis_a056793
