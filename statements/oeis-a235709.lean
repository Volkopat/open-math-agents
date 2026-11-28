import Mathlib

/-!
# A235709: a prime q < p with 2^q - 1 a quadratic residue modulo p

Source: https://oeis.org/A235709

A235709 (offset 1): `a(n)` is the least prime `p < prime(n)` with `2^p - 1` a quadratic residue
modulo `prime(n)`, or 0 if such a number does not exist. For example `a(8) = 3` since
`2^3 - 1 = 7` is a quadratic residue modulo `prime(8) = 19`, but `2^2 - 1 = 3` is not.

Conjecture (Zhi-Wei Sun, Apr 20 2014): `a(n) > 0` for all `n > 4`. The entry notes that this has
been verified for all `n = 5, …, 10^8`.

`a(n) > 0` means that a prime `q < prime(n)` with `2^q - 1` a quadratic residue modulo `prime(n)`
exists (0 is only the entry's marker for non-existence), and `n > 4` is the same as
`prime(n) > 7`, since `prime(4) = 7`. So the conjecture is stated as: for every prime `p > 7`
there is a prime `q < p` such that `2^q - 1` is a quadratic residue modulo `p`.

Conventions:
- A quadratic residue modulo the prime `p` is an integer that is not divisible by `p` and is
  congruent to a square modulo `p` (Legendre symbol equal to 1). This matches the entry's
  Mathematica program, which tests `JacobiSymbol[2^q - 1, p] == 1`, and it is the reading that
  reproduces the listed terms.
- Everything is in `ℕ`; `2^q - 1` is an exact subtraction, and the square root modulo `p` is
  taken among natural numbers `x`, which represent all residue classes.
-/

namespace OMA.S_oeis_a235709

/-- `a` is a quadratic residue modulo `p`: not divisible by `p` and congruent to a square. -/
def IsQuadraticResidue (a p : ℕ) : Prop := ¬ p ∣ a ∧ ∃ x : ℕ, x ^ 2 ≡ a [MOD p]

theorem main :
    ∀ p : ℕ, Nat.Prime p → 7 < p →
      ∃ q : ℕ, Nat.Prime q ∧ q < p ∧ IsQuadraticResidue (2 ^ q - 1) p := by
  sorry

end OMA.S_oeis_a235709
