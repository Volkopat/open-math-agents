import Mathlib

/-!
# OEIS A101424: cuboids with volume p^4 q^n

Source: https://oeis.org/A101424
Credit: Sudharsan Rajendiran

A101424(n) is the number of different cuboids with volume `p^4 * q^n`, where `p, q` are distinct
primes, i.e. A034836(p^4 q^n): the number of ways to write the volume as `x * y * z` with integer
sides `x ≤ y ≤ z`. Colin Barker conjectured (Mar 2014) `a(n) = (29 + 3(-1)^n + 36n + 10n^2)/8`, together with the recurrence
`a(n) = 2a(n-1) - 2a(n-3) + a(n-4)` and the g.f. `-(x + 4)/((x + 1)(x - 1)^3)` (both follow from the closed form). We state
the closed form for all distinct primes `p, q` and all `n ≥ 0`.

Conventions: offset `0`; `cuboids V` counts triples `(x, y, z)` of divisors of `V` with `x ≤ y ≤ z`
and `x * y * z = V`; the identity is taken in `ℤ`.
-/

namespace OMA.S_oeis_a101424

/-- The number of cuboids with integer sides `x ≤ y ≤ z` and volume `V`, i.e. the number of ways to
write `V = x * y * z` with `x ≤ y ≤ z` (this is A034836(V)). -/
def cuboids (V : ℕ) : ℕ :=
  ((V.divisors ×ˢ V.divisors ×ˢ V.divisors).filter
    (fun t : ℕ × ℕ × ℕ => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 * t.2.1 * t.2.2 = V)).card

theorem main : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ∀ n : ℕ,
    8 * (cuboids (p ^ 4 * q ^ n) : ℤ) = 29 + 3 * (-1) ^ n + 36 * n + 10 * n ^ 2 := by
  sorry

end OMA.S_oeis_a101424
