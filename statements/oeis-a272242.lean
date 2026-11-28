import Mathlib

/-!
# A272242: least `c` such that there are exactly `n` abc-hits with third member `c`.

Source: https://oeis.org/A272242
Credit: @cjchaffin

An abc-hit is a triple of coprime positive integers `a`, `b`, `c` such that `a + b = c` and
`rad(a*b*c) < c`, where `rad` is the radical (largest squarefree divisor). The example
`a(2) = 81` counts the two hits `(1, 80, 81)` and `(32, 49, 81)`, so the two summands are
taken in increasing order.

Conjecture (Jianing Song, Sep 21 2018): `a(n) > 0` for all `n`, i.e. for every positive
`n` some `c` has exactly `n` abc-hits. The conjecture is formalized as existence only, not
the “least `c`” part of the name.

Conventions: offset 1; `UniqueFactorizationMonoid.radical` is the radical of A007947.
-/

namespace OMA.S_oeis_a272242

/-- An abc-hit with third member `c`, written with `a < b`. -/
def IsAbcHit (a b c : ℕ) : Prop :=
  0 < a ∧ a < b ∧ a + b = c ∧ Nat.Coprime a b ∧
    UniqueFactorizationMonoid.radical (a * b * c) < c

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ c : ℕ, Nat.card { a : ℕ | ∃ b, IsAbcHit a b c } = n := by
  sorry

end OMA.S_oeis_a272242
