import Mathlib

/-!
# A006308. A coefficient of a period polynomial

Michael Somos's conjecture, using Sean A. Irvine's period-polynomial definition.
The sequence begins at the second prime, so `p` ranges over the odd primes.
The natural number `p * (p - 1) / 2` is the defining formula for A008837.

Sources: https://oeis.org/A006308 and https://oeis.org/A008837
Credit: @dwilfand-sys
-/

namespace OMA.S_oeis_a006308

noncomputable def period (p g k : ℕ) : ℂ :=
  let q := g ^ p
  let zeta := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ) ^ 2)
  ∑ j ∈ Finset.range (p - 1), zeta ^ ((q + k * p) * q ^ j)

noncomputable def periodPolynomial (p g : ℕ) : Polynomial ℂ :=
  ∏ k ∈ Finset.range p, (Polynomial.X - Polynomial.C (period p g k))

theorem main : ∀ p g : ℕ, p.Prime → 2 < p →
    orderOf (g : ZMod (p ^ 2)) = p * (p - 1) →
    -(periodPolynomial p g).coeff (p - 2) = ((p * (p - 1) / 2 : ℕ) : ℂ) ∧
      p * (p - 1) / 2 = ∑ k ∈ Finset.range p, k ^ 3 % p := by
  sorry

end OMA.S_oeis_a006308
