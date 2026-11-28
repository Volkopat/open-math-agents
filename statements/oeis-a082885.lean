import Mathlib

/-!
# A082885: Primes followed by a larger-than-average prime gap.

Source: https://oeis.org/A082885
Credit: @gblacher2

Conjecture (formula line of A082885, Alain Rocchelli, Dec 18 2023):
"Limit_{N->oo} (Sum_{n=1..N} a(n)) / (Sum_{n=1..N} prime(n)) = e (A001113)."

Definition (comment in A082885): "Primes p(j) such that p(j+1)-p(j) > log(p(j)), where log is
the natural logarithm." So a prime `p` is a term when the next prime after `p` exceeds `p` by
more than `Real.log p`.

Conventions:
* `nextPrime p` is the least prime `> p`, so for a prime `p = p(j)` it is `p(j+1)`;
* A082885 has offset 1 and is increasing; `a i` is its `(i+1)`-th term, i.e.
  `Nat.nth IsA082885 i`, so `Sum_{n=1..N} a(n)` is `∑ i ∈ Finset.range N, a i`;
* likewise `prime(n)` (offset 1) is `Nat.nth Nat.Prime (n - 1)`, so
  `Sum_{n=1..N} prime(n)` is `∑ i ∈ Finset.range N, Nat.nth Nat.Prime i`;
* `e` is `Real.exp 1`.
-/

namespace OMA.S_oeis_a082885

open Filter Topology

/-- The least prime greater than `p`. -/
def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- `p` is a term of A082885: a prime whose following prime gap exceeds `log p`. -/
def IsA082885 (p : ℕ) : Prop :=
  p.Prime ∧ Real.log p < ((nextPrime p : ℝ) - p)

/-- `a i` is the `(i+1)`-th term of A082885 (A082885 has offset 1). -/
noncomputable def a (i : ℕ) : ℕ := Nat.nth IsA082885 i

/-- The conjecture: `(a(1) + ... + a(N)) / (prime(1) + ... + prime(N))` tends to `e`. -/
theorem main :
    Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, (a i : ℝ)) /
        (∑ i ∈ Finset.range N, (Nat.nth Nat.Prime i : ℝ))) atTop (𝓝 (Real.exp 1)) := by
  sorry

end OMA.S_oeis_a082885
