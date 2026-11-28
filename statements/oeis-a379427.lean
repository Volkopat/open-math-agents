import Mathlib

/-!
# A379427: Numbers m such that prime(k)*m + prime(k+1), for k=1..8 all are primes.

Source: https://oeis.org/A379427
Credit: @luciusacarr

The entry (data 5600384, 12269234, 12700154, ...) records the claim (Miquel Cerda, Oct 19 2026):
all terms satisfy m == 14 (mod 30). (The same comment also gives a Bateman-Horn style heuristic for
the counting function; that asymptotic is not part of this statement.)

Reading of the source:
* `prime(k)` is the k-th prime with `prime(1) = 2`; in Lean `prime(k) = Nat.nth Nat.Prime (k - 1)`.
  So the eight numbers are 2m+3, 3m+5, 5m+7, 7m+11, 11m+13, 13m+17, 17m+19, 19m+23.
* The terms are positive integers m (m = 0 would trivially make all eight numbers prime, but 0
  is not a term: the listed terms start at 5600384).
* The claim: for every m ≥ 1, if `prime(k) * m + prime(k+1)` is prime for every k = 1, ..., 8,
  then `m % 30 = 14`.
-/

namespace OMA.S_oeis_a379427

/-- The k-th prime, 1-indexed: `prime 1 = 2`, `prime 2 = 3`, ... -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

theorem main :
    ∀ m : ℕ, 1 ≤ m → (∀ k ∈ Finset.Icc 1 8, (prime k * m + prime (k + 1)).Prime) → m % 30 = 14 := by
  sorry

end OMA.S_oeis_a379427
