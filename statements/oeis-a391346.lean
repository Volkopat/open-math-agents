import Mathlib

/-!
# A391346: Numbers k such that Stern polynomial B(5*k,x) is a multiple of B(5,x).

Source: https://oeis.org/A391346
Credit: @agchua

Antti Karttunen (Dec 13 2025), in the formula section of A391346:
  a(n) = A391566(n)/5. [Conjectured]

The Stern polynomials (A125184, A260443) are B(0,x) = 0, B(1,x) = 1, B(2n,x) = x*B(n,x) and
B(2n+1,x) = B(n,x) + B(n+1,x); below this is `B n`, a polynomial with integer coefficients.
B(5,x) = 2x + 1. A391346 (offset 1) lists the positive integers k such that B(5,x) divides
B(5k,x), in increasing order (data 1, 2, 4, 7, 8, ...); A391566 (offset 1) lists the positive
integers k such that B(5,x) divides B(k,x) (data 5, 10, 20, 35, 40, ...). The value k = 0, for
which B(0,x) = 0, is not a term of either entry, so both definitions require 0 < k. Divisibility
is taken in ℤ[x]; since 2x + 1 is primitive, by Gauss's lemma this is the same as divisibility in
ℚ[x], which is what the PARI program of the entry tests. The n-th term is `Nat.nth` at n - 1.
The quotient A391566(n)/5 is taken in ℚ, so the claim includes that A391566(n) is divisible by 5.
-/

namespace OMA.S_oeis_a391346

/-- The Stern polynomials: B(0) = 0, B(1) = 1, B(2n) = x*B(n), B(2n+1) = B(n) + B(n+1). -/
noncomputable def B (n : ℕ) : Polynomial ℤ :=
  if _h0 : n = 0 then 0
  else if _h1 : n = 1 then 1
  else if _h2 : n % 2 = 0 then Polynomial.X * B (n / 2)
  else B (n / 2) + B (n / 2 + 1)
decreasing_by all_goals omega

/-- A391346(n): the n-th positive integer k such that B(5,x) divides B(5k,x). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => 0 < k ∧ B 5 ∣ B (5 * k)) (n - 1)

/-- A391566(n): the n-th positive integer k such that B(5,x) divides B(k,x). -/
noncomputable def A391566 (n : ℕ) : ℕ := Nat.nth (fun k => 0 < k ∧ B 5 ∣ B k) (n - 1)

/-- Karttunen's conjecture: a(n) = A391566(n)/5 for all n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (A391566 n : ℚ) / 5 := by
  sorry

end OMA.S_oeis_a391346
