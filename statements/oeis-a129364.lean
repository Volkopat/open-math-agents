import Mathlib

/-!
# A129364: `a(n) = ∏_{k=1..n} A066841(k)`, with `A066841(k) = ∏_{d|k} d^(k/d)`.

Source: https://oeis.org/A129364 (and A066841, A092287)
Credit: @cjchaffin

A092287 is `∏_{j=1..n} ∏_{k=1..n} gcd(j,k)` (offset 0, with the empty product
`a(0) = 1`).

Conjecture (on the OEIS page, cf. A129365): `a(n)` divides `A092287(n)` for all `n`.

Conventions: the quantified `n` starts at 1, matching the offset of A129364. The
initial terms `1, 2, 6, 96, 480, 207360` divide the corresponding terms
`1, 2, 6, 96, 480, 414720` of A092287.
-/

namespace OMA.S_oeis_a129364

/-- `A066841(k) = ∏_{d | k} d^(k/d)`. -/
def A066841 (k : ℕ) : ℕ :=
  ∏ d ∈ k.divisors, d ^ (k / d)

def a (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 1 n, A066841 k

/-- `A092287(n) = ∏_{j=1..n} ∏_{k=1..n} gcd(j,k)` for `n ≥ 1`. -/
def A092287 (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 1 n, ∏ k ∈ Finset.Icc 1 n, Nat.gcd j k

theorem main : ∀ n : ℕ, 1 ≤ n → a n ∣ A092287 n := by
  sorry

end OMA.S_oeis_a129364
