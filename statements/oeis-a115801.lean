import Mathlib

/-!
# A115801: Numbers k such that 9*k = A048720(25,k), where A048720 is carryless base-2 multiplication.

Source: https://oeis.org/A115801
Credit: @agchua

Comment line of A115801, by Antti Karttunen, Dec 21 2025:
  Conjecture: also k such that 15*k = A048720(19,k). This has been checked for all k in
  range 0 .. 2^25.
A115801 has offset 1 and lists, in increasing order, every k >= 0 with 9*k = A048720(25,k)
(0, 15, 30, 31, 60, 62, 63, 120, ...). The conjecture says that these are exactly the k >= 0 with
15*k = A048720(19,k), so it is stated as an equivalence for every natural number k.
A048720(b,c) is the carryless product of b and c: the binary digits are multiplied as polynomials
with coefficients mod 2 (the PARI line of the entry: fromdigits(Vec(Pol(binary(b))*Pol(binary(c)))%2, 2)).
Below, `clmul b c` is this product, computed by shift and XOR over the binary digits of c:
clmul b 0 = 0 and clmul b (2*c' + e) = (e*b) XOR (2 * clmul b c') for a binary digit e.
With it, the 58 listed terms of A115801 are reproduced.
-/

namespace OMA.S_oeis_a115801

/-- A048720(b,c): the carryless (XOR) product of b and c in base 2. -/
def clmul (b c : ℕ) : ℕ :=
  if _h : c = 0 then 0
  else (if c % 2 = 1 then b else 0) ^^^ (2 * clmul b (c / 2))
termination_by c
decreasing_by all_goals omega

/-- Karttunen's conjecture: 9*k = A048720(25,k) holds exactly when 15*k = A048720(19,k). -/
theorem main : ∀ k : ℕ, 9 * k = clmul 25 k ↔ 15 * k = clmul 19 k := by
  sorry

end OMA.S_oeis_a115801
