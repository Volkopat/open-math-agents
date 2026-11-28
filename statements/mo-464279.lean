import Mathlib

/-!
# Binary polynomials of maximal thickness

Source: https://mathoverflow.net/questions/464279
Asked by MathOverflow user Sayan Dutta.

OEIS A169945 defines the thickness of a polynomial as the largest magnitude of a coefficient
of its square. Among the `2^(n+1)` polynomials with coefficients `0` or `1` and degree at most
`n`, let `T(n,k)` be the number of those of thickness `k`. The question asks for formulas and
patterns for the triangle `T(n,k)`, and observes in particular that `T(n,n)` seems to follow
the pattern `2, 3, 2, 3, ...`.

This file formalizes that observed pattern: for every `n ≥ 1`, `T(n,n) = 3` if `n` is even
and `T(n,n) = 2` if `n` is odd. The other questions in the post (general formulas,
asymptotics, the pattern of `T(n,n-1)`) are not formalized here.

Translation choices.
* A polynomial with coefficients `0` or `1` and degree at most `n` is determined by its set of
  exponents `S ⊆ {0, ..., n}`; it is `poly S = ∑_{i ∈ S} X^i` in `ℤ[X]`, and `T n k` counts
  the subsets `S` of `Finset.range (n + 1)` whose polynomial has thickness `k`.
* `thickness p` is the largest absolute value of a coefficient of `p^2` (and `0` for `p = 0`).
-/

namespace OMA.S_mo_464279

open Polynomial

/-- The `0`/`1` polynomial with exponent set `S`. -/
noncomputable def poly (S : Finset ℕ) : ℤ[X] := ∑ i ∈ S, X ^ i

/-- The thickness of `p`: the largest absolute value of a coefficient of `p^2`. -/
noncomputable def thickness (p : ℤ[X]) : ℕ := (p ^ 2).support.sup fun j => ((p ^ 2).coeff j).natAbs

/-- `T n k`: the number of `0`/`1` polynomials of degree at most `n` with thickness `k`. -/
noncomputable def T (n k : ℕ) : ℕ :=
  ((Finset.range (n + 1)).powerset.filter fun S => thickness (poly S) = k).card

theorem main : ∀ n : ℕ, 1 ≤ n → T n n = if Even n then 3 else 2 := by
  sorry

end OMA.S_mo_464279
