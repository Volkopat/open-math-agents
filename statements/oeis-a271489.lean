import Mathlib

/-!
# OEIS A271489: Barker's conjectures for the maximal term of the TRIP-Stern sequence (e,132,e)

Source: https://oeis.org/A271489 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A271489 (N. J. A. Sloane, Apr 13 2016), offset 0: Maximal term of TRIP-Stern sequence of
level n corresponding to permutation triple (e,132,e).
Data: 1, 2, 3, 4, 5, 7, 10, 13, 18, 25, 34, 46, ...
Mathematica (Jean-Francois Alcover, after R. J. Mathar): A271487T[1] = {1, 1, 1}; for n > 1,
with an = A271487T[Floor[n/2]], A271487T[n] = {an[[3]], an[[1]] + an[[3]], an[[2]]} for even n and
{an[[1]], an[[2]], an[[1]] + an[[3]]} for odd n; a(n) = the largest entry of A271487T[l] over
2^n <= l <= 2^(n+1) - 1.
Formula section (Barker's part; the per-residue conjectures of Lars Blomberg are separate claims
and are not part of this statement):
Conjectures from Colin Barker, Jan 09 2018: (Start)
G.f.: (1 + 2*x + 3*x^2 + 2*x^3 + x^4 + x^5 + x^6 + x^7 + x^8 + x^10 - x^13) / (1 - 2*x^3 - x^6 - x^9).
a(n) = 2*a(n-3) + a(n-6) + a(n-9) for n>8.
(End)

Formalization notes:
* `T` is A271487T of the entry's program (T 0 is set to (1, 1, 1) too; it is never used for
  n >= 0 since 2^n >= 1). a(n) is the largest entry of T l over 2^n <= l <= 2^(n+1) - 1; this
  reproduces the first 20 listed terms (direct computation).
* The statement is the conjunction of Barker's recurrence (for n > 8, in the integers) and g.f.;
  the identity A(x) = N/D is stated as A * D = N in the formal power series ring over the
  integers (D has constant term 1).
-/

namespace OMA.S_oeis_a271489

open PowerSeries

/-- The TRIP-Stern triples of the entry's program. -/
def T (n : ℕ) : ℕ × ℕ × ℕ :=
  if h : n ≤ 1 then (1, 1, 1)
  else
    have : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
    let t := T (n / 2)
    if n % 2 = 0 then (t.2.2, t.1 + t.2.2, t.2.1) else (t.1, t.2.1, t.1 + t.2.2)

/-- A271489(n): the largest entry of the triples of level n. -/
def a (n : ℕ) : ℕ :=
  (Finset.Icc (2 ^ n) (2 ^ (n + 1) - 1)).sup fun l => max (T l).1 (max (T l).2.1 (T l).2.2)

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 3) + a (n - 6) + a (n - 9)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - 2 * X ^ 3 - X ^ 6 - X ^ 9)) =
      ((1 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 + X ^ 10 - X ^ 13) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a271489
