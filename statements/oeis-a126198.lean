import Mathlib

/-!
# A126198: Triangle read by rows: T(n,k) (1 <= k <= n) = number of compositions of n into parts of size <= k.

Source: https://oeis.org/A126198
Credit: @agchua

Formula line of A126198 (the entry is by N. J. A. Sloane, Mar 09 2007):
  Conjecture: Sum_{k=1..n} T(n,k) = A039671(n), n>0. - L. Edson Jeffery, Nov 29 2013
The claim is stated for every n ≥ 1, as in the entry. `T n k` counts the compositions of n
(Mathlib's `Composition n`: lists of positive integers with sum n, in order) all of whose parts
are at most k.

The referenced sequence, by its own entry's definition:
* A039671 (offset 0) is the sequence of row sums up to the main diagonal of the postage stamp
  array (n, m >= 0) defined in A007059, i.e. A039671(n) = F(n, 0) + F(n, 1) + ... + F(n, n).
  A007059 defines the array by F(n, m) = F(n-1, m) + F(n-2, m) + ... + F(n-m, m), with
  F(0, m) = 1 (m >= 0), F(n, m) = 0 (n < 0) and F(n, 0) = 0 (n > 0). In `F` below, the term
  F(n+1-(i+1), m) of the sum for row n+1 is written F(n - i, m) when i ≤ n and 0 otherwise.
-/

namespace OMA.S_oeis_a126198

/-- T(n, k): the number of compositions of n into parts of size at most k. -/
def T (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Composition n)).filter (fun c => ∀ b ∈ c.blocks, b ≤ k)).card

/-- The postage stamp array of A007059: F(0, m) = 1 and, for n ≥ 0,
F(n+1, m) = F(n, m) + F(n-1, m) + ... + F(n+1-m, m), terms with a negative row being 0. -/
def F : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, m => ∑ i ∈ Finset.range m, if i ≤ n then F (n - i) m else 0
termination_by n _ => n

/-- A039671(n): the sum of the entries F(n, 0), ..., F(n, n) of row n up to the main diagonal. -/
def a039671 (n : ℕ) : ℕ := ∑ m ∈ Finset.range (n + 1), F n m

/-- The conjecture: Sum_{k=1..n} T(n, k) = A039671(n) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Finset.Icc 1 n, T n k = a039671 n := by
  sorry

end OMA.S_oeis_a126198
