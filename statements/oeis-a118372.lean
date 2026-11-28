import Mathlib

/-!
# A118372: S-perfect numbers.

Source: https://oeis.org/A118372
Credit: @divmxnd0x

The set `S` (Granville, December 1996; De Koninck, *Those Fascinating Numbers*, 2009) is defined
recursively: `1 ∈ S`, and an integer `n > 1` belongs to `S` when the sum of the proper divisors of
`n` that lie in `S` is at most `n`. A number `n` is S-perfect (a Granville number) when the sum of
its proper divisors lying in `S` equals `n`.

A Zumkeller (integer-perfect) number (A083207) is a positive integer whose divisors can be
partitioned into two disjoint sets with equal sum.

Conjecture (Ivan N. Ianakiev, Apr 23 2017): if `k` is S-perfect, then `σ(k)/2` (A000203(k)/2) is a
Zumkeller number.

Formalization notes:
* `inS n` decides membership of `n` in `S`: `0 ∉ S`, `1 ∈ S`, and for `n ≥ 2` it applies the
  defining condition, which only refers to proper divisors of `n`, all smaller than `n`.
* Every S-perfect number is a Zumkeller number (comment of A118372), so `σ(k)` is even and
  `σ(k) / 2` below is exact.
* A partition of the divisors into two sets is given by one set `A` of divisors and its complement.
* With these definitions the S-perfect numbers below 10000 are 6, 24, 28, 96, 126, 224, 384, 496,
  1536, 1792, 6144, 8128 (data of A118372), the Zumkeller numbers below 120 are 6, 12, 20, 24, 28,
  30, 40, 42, 48, 54, 56, 60, 66, 70, 78, 80, 84, 88, 90, 96, 102, 104, 108, 112, 114 (data of
  A083207), and the conjecture holds for the S-perfect numbers 6, ..., 1792.
-/

namespace OMA.S_oeis_a118372

/-- Membership in Granville's set `S`. -/
def inS : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 => decide ((∑ d ∈ (n + 2).properDivisors.attach, if inS d.1 then d.1 else 0) ≤ n + 2)
decreasing_by
  all_goals
    have h := (Nat.mem_properDivisors.mp d.2).2
    simp_wf
    omega

/-- The sum of the proper divisors of `n` that lie in `S`. -/
def sSum (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, if inS d then d else 0

/-- `n` is S-perfect (a Granville number). -/
def IsSPerfect (n : ℕ) : Prop :=
  0 < n ∧ sSum n = n

/-- `n` is a Zumkeller number: its divisors split into two disjoint sets with equal sum. -/
def IsZumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ A ⊆ n.divisors, ∑ d ∈ A, d = ∑ d ∈ n.divisors \ A, d

/-- Ianakiev's conjecture: for every S-perfect `k`, `σ(k)/2` is a Zumkeller number. -/
theorem main : ∀ k : ℕ, IsSPerfect k → IsZumkeller ((∑ d ∈ k.divisors, d) / 2) := by
  sorry

end OMA.S_oeis_a118372
