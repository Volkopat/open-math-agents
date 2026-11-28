import Mathlib

/-!
# A308833: Numbers r such that the r-th tetrahedral number A000292(r) divides r!

Source: https://oeis.org/A308833
Credit: @xor2k

Formalizes the OEIS A308833 conjecture: for every odd integer r > 1, the following statements
are equivalent: a) r is a term of this sequence, b) r + 1 is a term of this sequence,
c) r + 2 is composite.

Conventions: `T r = r*(r+1)*(r+2)/6` is A000292 (exact division in `ℕ`), and `r` is a term iff
`T r ∣ r!`; this reproduces the OEIS data (offset 1, first term 1; `r = 0` is excluded since
`T 0 = 0` does not divide `0! = 1`). Composite is `1 < r + 2 ∧ ¬ (r + 2).Prime`. The
equivalence of a), b), c) is stated as the two equivalences a ↔ b and b ↔ c.
-/

namespace OMA.S_oeis_a308833

/-- The tetrahedral number A000292: `T(r) = r*(r+1)*(r+2)/6`. -/
def T (r : ℕ) : ℕ :=
  r * (r + 1) * (r + 2) / 6

/-- `r` is a term of A308833: `T(r)` divides `r!`. -/
def IsTerm (r : ℕ) : Prop :=
  T r ∣ Nat.factorial r

/-- For every odd `r > 1`: `r` is a term iff `r + 1` is a term iff `r + 2` is composite. -/
theorem main :
    ∀ r : ℕ, Odd r → 1 < r →
      (IsTerm r ↔ IsTerm (r + 1)) ∧ (IsTerm (r + 1) ↔ (1 < r + 2 ∧ ¬ (r + 2).Prime)) := by
  sorry

end OMA.S_oeis_a308833
