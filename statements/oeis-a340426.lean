import Mathlib

/-!
# A340426: Triangle read by rows: T(n,k) = A000203(n-k+1)*A002865(k-1), 1 <= k <= n.

Source: https://oeis.org/A340426
Credit: @esracummings31-blip

Conjecture (Omar E. Pol): the sum of row n equals A138879(n), the sum of all parts in the last
section of the set of partitions of n.

Conventions.
* A000203(m) = sigma(m) is the sum of the divisors of m.
* A002865(j) is the number of partitions of j that contain no part 1 (so A002865(0) = 1).
* A138879 is given in the OEIS by a(n) = A066186(n) - A066186(n-1) for n >= 1, where
  A066186(n) is the sum of all parts of all partitions of n; this is the definition used here.
-/

namespace OMA.S_oeis_a340426

/-- A002865: the number of partitions of j with no part equal to 1. -/
def A002865 (j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition j)).filter (fun p => 1 ∉ p.parts)).card

/-- A000203: the sum of the divisors of m. -/
def A000203 (m : ℕ) : ℕ := ∑ d ∈ Nat.divisors m, d

/-- A066186: the sum of all parts of all partitions of n. -/
def A066186 (n : ℕ) : ℕ := ∑ p : Nat.Partition n, p.parts.sum

/-- A138879(n) = A066186(n) - A066186(n-1) (for n >= 1). -/
def A138879 (n : ℕ) : ℤ := (A066186 n : ℤ) - A066186 (n - 1)

/-- T(n,k) = A000203(n-k+1) * A002865(k-1). -/
def T (n k : ℕ) : ℕ := A000203 (n - k + 1) * A002865 (k - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → ((∑ k ∈ Finset.Icc 1 n, T n k : ℕ) : ℤ) = A138879 n := by
  sorry

end OMA.S_oeis_a340426
