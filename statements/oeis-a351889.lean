import Mathlib

/-!
# OEIS A351889: period of n-step Fibonacci numbers mod k

`T(n,k)` (`n >= 1, k >= 1`, table read by downward antidiagonals) is the
period of the n-step Fibonacci sequence modulo `k`, seeded by `0,...,0,1`
(`n - 1` zeros then a `1`), each term the sum of the `n` previous terms
reduced mod `k`. The state is the sliding window of the last `n` terms,
an element of `Fin n → ZMod k`; `vstep` shifts it left and appends the
window sum. The orbit is purely periodic because `vstep` is injective
(the companion matrix of `x^n - x^(n-1) - ... - 1` is invertible mod `k`),
so `T(n,k)` is the least positive eventual period, i.e. `sInf periodSet`.

The OEIS comment states two conjectures (verbatim):

Conjecture 1: T(n,2^m) = (n+1)*2^(m-1) for n > 1.
Conjecture 2: For p prime, if T(n,p) != T(n,p^2) then
T(n,p^k) = p^(k-1)*T(n,p).

The comment adds that Conjecture 2 is true for n = 2, 3, 4
(Wall 1960, Waddill 1978, Waddill 1992 resp.), that T(n,4) != n+1
for all n, and hence that Conjecture 2 implies Conjecture 1.

Range notes for the faithful translation. In Conjecture 1 the modulus
exponent needs `1 <= m`: at `m = 0`, `T(n,1) = 1` while `(n+1)*2^(m-1)`
reads `n+1` in `Nat` (truncated `m - 1`), so the bare claim would be
false; the comment is visibly about powers `2^m` with `m >= 1`. In
Conjecture 2 the power index likewise needs `1 <= k` (at `k = 0`,
`T(2,1) = 1` but `2^(k-1)*T(2,2) = 3`). The row index in Conjecture 2
ranges over the table domain `1 <= n`; the premise is vacuous at
`n = 1` anyway since `T(1,k) = 1`.

Source: https://oeis.org/A351889
-/

namespace OMA.S_oeis_a351889

/-- The verbatim OEIS seed `(0,...,0,1)`: `n - 1` zeros then a `1`,
in `(ZMod k)^n`. -/
def vinit (n k : ℕ) : Fin n → ZMod k :=
  fun i => if (i : ℕ) + 1 < n then 0 else 1

/-- One step of the dynamics: shift left; the last entry is the sum of
the `n` terms of the window (in `ZMod k`). -/
def vstep (n k : ℕ) (v : Fin n → ZMod k) : Fin n → ZMod k :=
  fun i => if h : (i : ℕ) + 1 < n then v ⟨i + 1, h⟩ else ∑ j, v j

/-- Window at time `m`: `m` iterates of `vstep` from the seed. -/
def vstate (n k m : ℕ) : Fin n → ZMod k := (vstep n k)^[m] (vinit n k)

/-- The OEIS sequence: the term of index `m` is the head of the window
at time `m`. Dummy value `0` off-domain (`n = 0`). -/
def seqN (n k m : ℕ) : ZMod k := if h : 0 < n then vstate n k m ⟨0, h⟩ else 0

/-- `p` is an eventual period of the sequence: from some rank `m0` on,
the terms `m` and `m + p` coincide. -/
def IsEventualPeriod (n k p : ℕ) : Prop :=
  ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → seqN n k (m + p) = seqN n k m

/-- `p` is a pure period of the sequence: for all `m`, the terms `m`
and `m + p` coincide. -/
def IsPurePeriod (n k p : ℕ) : Prop :=
  ∀ m : ℕ, seqN n k (m + p) = seqN n k m

/-- The set of positive eventual periods of the sequence. -/
abbrev periodSet (n k : ℕ) : Set ℕ := {p : ℕ | 0 < p ∧ IsEventualPeriod n k p}

/-- The OEIS term `T(n,k)`: the least element of `periodSet n k`
(`sInf` on `ℕ`, `0` by convention if empty, off-domain `n = 0` or
`k = 0`). -/
noncomputable def a351889 (n k : ℕ) : ℕ := sInf (periodSet n k)

theorem main :
    (∀ n m : ℕ, 1 < n → 1 ≤ m → a351889 n (2 ^ m) = (n + 1) * 2 ^ (m - 1)) ∧
    (∀ n p k : ℕ, 1 ≤ n → p.Prime → 1 ≤ k →
      a351889 n p ≠ a351889 n (p ^ 2) →
      a351889 n (p ^ k) = p ^ (k - 1) * a351889 n p) := by
  sorry

end OMA.S_oeis_a351889
