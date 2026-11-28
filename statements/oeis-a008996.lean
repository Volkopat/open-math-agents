import Mathlib

/-!
# A008996: Increasing length runs of consecutive composite numbers (records).

Source: https://oeis.org/A008996
Credit: @EmircanEsen

Conjecture (Alexei Kourbatov, Jan 23 2019): `a(n) = O(n^2)`; specifically, `a(n) ≤ n^2`.

The sequence has offset 1 and begins `a(1) = 1`, `a(2) = 3`, `a(3) = 5`, `a(4) = 7`, `a(5) = 13`,
… This file states the specific form `a(n) ≤ n^2` for every `n ≥ 1`, which implies the `O(n^2)`
form. It holds for all 82 terms in the OEIS b-file, with equality only at `n = 1`.

Formalization notes:
* Between consecutive primes `prime k < prime (k+1)` lie exactly `prime (k+1) - prime k - 1`
  consecutive composite numbers, and every maximal run of composites (from `4` on) arises this
  way. So the record run lengths are the record prime gaps minus `1`: the entry's formula
  `a(n) = A005250(n+1) - 1`. The first record gap, `3 - 2 = 1`, gives the empty run between `2`
  and `3` and is not a term; the next one, `5 - 3 = 2`, gives the run `{4}` of length `1 = a(1)`.
* Conventions, as in the merged statement of A053695 (differences between record prime gaps): a
  gap is `prime (k+1) - prime k` with `prime k = Nat.nth Nat.Prime k` (so `prime 0 = 2` and
  `gap 0 = 1`), and `gap k` is a record when it is larger than every earlier gap `gap i`,
  `i < k`. Record gaps increase strictly with `k`, so `Nat.nth` enumerates the record values in
  increasing order; `Nat.nth _ 0 = 1`, `Nat.nth _ 1 = 2`, `Nat.nth _ 2 = 4`, ….
  With the offset of A008996, `a n = Nat.nth _ n - 1`: `a 1 = 2 - 1 = 1`, `a 2 = 4 - 1 = 3`, ….
* The set of record values is infinite (prime gaps are unbounded), so `Nat.nth` does not fall
  back to its junk value `0` on it.
-/

namespace OMA.S_oeis_a008996

/-- The gap `prime(k+1) - prime(k)` after the `k`-th prime (0-indexed: `prime 0 = 2`). -/
noncomputable def gap (k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k

/-- `gap k` is a record: it exceeds every earlier gap. -/
def IsRecord (k : ℕ) : Prop := ∀ i < k, gap i < gap k

/-- OEIS A008996 with its offset 1: `a n` is the `n`-th record length of a run of consecutive
composite numbers, i.e. the `(n+1)`-st record prime gap minus one. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun g => ∃ k, IsRecord k ∧ gap k = g) n - 1

/-- Kourbatov's conjecture: the `n`-th record run of consecutive composites has length at most
`n^2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ n ^ 2 := by
  sorry

end OMA.S_oeis_a008996
