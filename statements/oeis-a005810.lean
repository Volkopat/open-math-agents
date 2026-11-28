import Mathlib

/-!
# A005810: a(n) = binomial(4n, n).

Source: https://oeis.org/A005810
Credit: @rabdelaal

OEIS A005810 records the conjecture (Gary Detlefs, 2013) that `binomial(4n, n) = 4`
modulo `n ^ 3` iff `n` is prime. For prime `p` this is a known generalization of
Wolstenholme's theorem (Mestrovic, Section 6, equation 35); the converse for composite
`n` completes the stated iff.
-/

namespace OMA.S_oeis_a005810

/-- The OEIS A005810 entry: `binomial(4n, n)`. -/
def a (n : ℕ) : ℕ := Nat.choose (4 * n) n

/-- The conjecture recorded in OEIS A005810 (Detlefs): `binomial(4n, n) ≡ 4 (mod n³)`
iff `n` is prime. -/
theorem main : ∀ n ≥ 1, a n % n ^ 3 = 4 % (n ^ 3) ↔ Nat.Prime n := by
  sorry

end OMA.S_oeis_a005810
