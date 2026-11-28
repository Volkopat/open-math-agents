import Mathlib

/-!
# OEIS A145047: the least s with s*p - floor(sqrt(s*p))^2 a square lies in A008784

Source: https://oeis.org/A145047 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Vladimir Shevelev, Sep 30 2008), offset 1: Primes p of the form 4k+1 for which s=10 is the
least positive integer such that sp-(floor(sqrt(sp)))^2 is a square. Comment: Conjecture: The least
positive integer s can take values only from A008784 (see for s=1,2,5,10 sequences A145016,
A145022, A145023 and this sequence). A008784: numbers k such that sqrt(-1) mod k exists.

Formalization notes:
* Good p s says that s * p - (Nat.sqrt (s * p))^2 is a perfect square (0 counts as a square,
  so s = p is always good and the least s exists).
* InA008784 k says that -1 is a square in ZMod k, the entry's definition of A008784.
* main says: for every prime p ≡ 1 (mod 4) and every s > 0 that is good for p while no smaller
  positive t is, s lies in A008784.
* Control proved in the proof file: for p = 1237, the first term, s = 1, ..., 9 fail and s = 10
  is good.
-/

namespace OMA.S_oeis_a145047

/-- `s * p - ⌊√(s * p)⌋ ^ 2` is a perfect square. -/
def Good (p s : ℕ) : Prop := IsSquare (s * p - Nat.sqrt (s * p) ^ 2)

/-- A008784: numbers `k` such that `-1` is a square modulo `k`. -/
def InA008784 (k : ℕ) : Prop := IsSquare (-1 : ZMod k)

/-- Shevelev's conjecture: the least good s for a prime p ≡ 1 (mod 4) is in A008784. -/
theorem main : ∀ p s : ℕ, p.Prime → p % 4 = 1 → 0 < s → Good p s →
    (∀ t, 0 < t → t < s → ¬ Good p t) → InA008784 s := by
  sorry

end OMA.S_oeis_a145047
