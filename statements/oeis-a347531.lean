import Mathlib

/-!
# OEIS A347531: consecutive primes p, q, r with r^2-p^2+p, r^2-p^2+q, r^2-p^2+r consecutive primes

Source: https://oeis.org/A347531
Credit: @unserus

OEIS: "Dickson's conjecture implies that there are infinitely many terms with,
for example, the first three consecutive primes p, p+2, p+6 and the second three
13*p+36, 13*p+38 and 13*p+42."

The terms are the primes `p` such that, with `q` the next prime after `p` and
`r` the next prime after `q`, the numbers `r^2 - p^2 + p`, `r^2 - p^2 + q`
and `r^2 - p^2 + r` are three consecutive primes (each the next prime after the
previous one). `r^2 - p^2` does not truncate since `p < r`. The open statement
is that the sequence is infinite.
-/

namespace OMA.S_oeis_a347531

/-- `b` is the least prime greater than `a`. -/
def IsNextPrime (a b : ℕ) : Prop :=
  b.Prime ∧ a < b ∧ ∀ c, a < c → c < b → ¬ c.Prime

/-- The terms of A347531. -/
def a347531Set : Set ℕ :=
  {p | p.Prime ∧ ∃ q r, IsNextPrime p q ∧ IsNextPrime q r ∧
    (r ^ 2 - p ^ 2 + p).Prime ∧ IsNextPrime (r ^ 2 - p ^ 2 + p) (r ^ 2 - p ^ 2 + q) ∧
    IsNextPrime (r ^ 2 - p ^ 2 + q) (r ^ 2 - p ^ 2 + r)}

/-- A347531 is infinite. -/
theorem main : a347531Set.Infinite := by
  sorry

end OMA.S_oeis_a347531
