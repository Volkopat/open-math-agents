import Mathlib

/-!
# A004018: Theta series of square lattice (or number of ways of writing n as a sum of 2 squares). Often denoted by r(n) or r_2(n).

Source: https://oeis.org/A004018
Credit: @darealpandaboi

Conjecture (Plouffe; stated as proved on the OEIS page, see the Fried link):
Sum_{k>=0} a(k) / exp(k*Pi) = Pi^(1/2) / Gamma(3/4)^2 = A175574.

Translation notes.
* a(n) = r_2(n) counts ordered pairs (x, y) of integers, signs included, with x^2 + y^2 = n,
  so a(0) = 1, a(1) = 4, a(2) = 4, a(3) = 0, a(5) = 8 (the listed terms).
* Every such pair has |x|, |y| <= n, so counting inside [-n, n] x [-n, n] is exact.
* Numerically both sides are 1.18034059901609...
-/

namespace OMA.S_oeis_a004018

/-- r_2(n): the number of (x, y) in ℤ × ℤ with x^2 + y^2 = n. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun p : ℤ × ℤ => p.1 ^ 2 + p.2 ^ 2 = n)).card

theorem main :
    ∑' k : ℕ, (a k : ℝ) / Real.exp (k * Real.pi) = Real.sqrt Real.pi / Real.Gamma (3 / 4) ^ 2 := by
  sorry

end OMA.S_oeis_a004018
