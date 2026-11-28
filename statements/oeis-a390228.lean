import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# Prime discriminators of the modular j coefficients

Sources: https://oeis.org/A390228 and https://oeis.org/A000521
Credit: @luciusacarr

The worked example, program, and listed terms use the discriminator of
`c(k) * (c(k) - 1)`, where `c(k)` is the coefficient of `q^k` in `j(q)`.
-/

namespace OMA.S_oeis_a390228

open Polynomial

/-- The coefficient of `q^k` in `j(q)`. The product for `q * j(q)` can be
cut off at degree `k + 1`. Each inverse factor is expanded using a
finite geometric sum before taking its 24th power. -/
noncomputable def jCoeff (k : ℕ) : ℕ :=
  let degree := k + 1
  let exponents := Finset.range (degree + 1)
  let positive := exponents.erase 0
  let E4 : ℕ[X] := 1 + ∑ d ∈ positive, monomial d
    (240 * ∑ t ∈ (Finset.range (d + 1)).erase 0, if t ∣ d then t ^ 3 else 0)
  let inverseFactors : ℕ[X] :=
    ∏ d ∈ positive, (∑ j ∈ exponents, (X : ℕ[X]) ^ (d * j)) ^ 24
  (E4 ^ 3 * inverseFactors).coeff degree

noncomputable def transformedCoeff (k : ℕ) : ℕ :=
  let c := jCoeff k
  c * (c - 1)

def Discriminates (n m : ℕ) : Prop :=
  0 < m ∧ ∀ i j : ℕ, i < j → j < n → transformedCoeff i % m ≠ transformedCoeff j % m

theorem main : ∀ n : ℕ, 4 < n →
    ∃ m : ℕ, IsLeast {d : ℕ | Discriminates n d} m ∧ m.Prime := by
  sorry

end OMA.S_oeis_a390228
