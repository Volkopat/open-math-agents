import Mathlib

/-!
# Odd-indexed terms of the Bernoulli-polynomial transform in OEIS A228767

Source: https://oeis.org/A228767
Credit: @etaubman

The input is Michel Marcus's Bernoulli-polynomial formula in the source entry.
The inverse binomial transform is taken over the rationals. The sequence picks
indices 1, 3, 5, ... and its ordinary generating series has constant term zero.
Both proposed formulas were recorded by Bruno Berselli in September 2013.
-/

namespace OMA.S_oeis_a228767

noncomputable def input (k : ℕ) : ℚ :=
  (-1 : ℚ)^k * ((Polynomial.bernoulli k).eval 1 + (Polynomial.bernoulli k).eval 2) / 2

noncomputable def transformed (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n+1), (-1 : ℚ)^(n-k) * (n.choose k : ℚ) * input k

noncomputable def term : ℕ → ℚ
  | 0 => 0
  | k+1 => transformed (2*k+1)

open PowerSeries

theorem main : term 1 = -2 ∧ (∀ k : ℕ,
    term (k+2) = (8 + 4^(k+2)) * (1 - 2*((k:ℚ)+2)) / 8) ∧
    (1-X)^2 * (1-4*X)^2 * mk term =
      (-X * (2 - 11*X + 21*X^2 - 2*X^3 + 8*X^4) : PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a228767
