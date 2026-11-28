import Mathlib

/-!
# A004001: Hofstadter-Conway $10000 sequence.

Source: https://oeis.org/A004001
Credit: @rabdelaal

`a 1 = a 2 = 1`, `a n = a (a (n-1)) + a (n - a (n-1))` (OEIS A004001).

OEIS A004001 records the conjecture (Daniel Forgues, 2019): `a(n) = n/2` iff `n` is a
power of two `2^k` with `k >= 1`.
-/

namespace OMA.S_oeis_a004001

/-- One step of the Hofstadter-Conway recursion, as a relation on the values
`b = a (n+1)` known only through a bound: the entry is at most its index. -/
def hcStep (F : ℕ → ℕ) (n : ℕ) : ℕ := F (F (n + 1)) + (n + 2 - F (n + 1))

/-- The Hofstadter-Conway `$10000` sequence: `a 1 = a 2 = 1`,
`a n = a (a (n-1)) + a (n - a (n-1))`, built by iterating `hcStep` from the seed
`(1, 1)`; entry `n + 2` is `hcStep` applied to the prefix, with values bounded by the
standard invariant `a m <= m` (which the recursion preserves). -/
def a : ℕ → ℕ :=
  fun n => Nat.rec (1 : ℕ) (fun _ prev => hcStep (fun k => prev) n) n

/-- `n` is a nontrivial power of two. -/
def IsPowTwo (n : ℕ) : Prop := ∃ k ≥ 1, n = 2 ^ k

/-- The conjecture recorded in OEIS A004001 (Forgues): `a(n) = n/2` iff `n = 2^k, k>=1`
(stated for `n >= 1`; `a 0` is the padding value `1`). -/
theorem main : ∀ n ≥ 1, a n * 2 = n ↔ IsPowTwo n := by
  sorry

end OMA.S_oeis_a004001
