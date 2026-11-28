import Mathlib

/-!
# A340524: Triangle read by rows: T(n,k) = A000005(n-k+1)*A002865(k-1), 1 <= k <= n.

Source: https://oeis.org/A340524
Credit: @esracummings31-blip

Conjecture (Omar E. Pol): the sum of row n equals A138137(n), the total number of parts in the
last section of the set of partitions of n.

Conventions.
* A000005(m) is the number of divisors of m.
* A002865(j) is the number of partitions of j that contain no part 1 (so A002865(0) = 1).
* A138137 is defined in the OEIS as the first differences of A006128, where A006128(n) is the
  total number of parts in all partitions of n; this is the definition used here,
  A138137(n) = A006128(n) - A006128(n-1) for n >= 1.
-/

namespace OMA.S_oeis_a340524

/-- A002865: the number of partitions of j with no part equal to 1. -/
def A002865 (j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition j)).filter (fun p => 1 ∉ p.parts)).card

/-- A006128: the total number of parts in all partitions of n. -/
def A006128 (n : ℕ) : ℕ := ∑ p : Nat.Partition n, Multiset.card p.parts

/-- A138137: first differences of A006128 (for n >= 1). -/
def A138137 (n : ℕ) : ℤ := (A006128 n : ℤ) - A006128 (n - 1)

/-- T(n,k) = A000005(n-k+1) * A002865(k-1). -/
def T (n k : ℕ) : ℕ := (Nat.divisors (n - k + 1)).card * A002865 (k - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → ((∑ k ∈ Finset.Icc 1 n, T n k : ℕ) : ℤ) = A138137 n := by
  sorry

end OMA.S_oeis_a340524
