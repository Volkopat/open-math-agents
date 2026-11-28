import Mathlib

/-!
# OEIS A209724: the conjectures of Reverter i Bigas and Barker for 1/4 the number of (n+1) X 6 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences

Source: https://oeis.org/A209724 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A209724 (R. H. Hardin, Mar 12 2012), offset 1: 1/4 the number of (n+1) X 6 0..2 arrays
with every 2 X 2 subblock having distinct clockwise edge differences.
Data: 8, 9, 10, 12, 14, 18, 22, 30, 38, 54, 70, 102, 134, 198, 262, 390, 518, ...

The two conjectures of the entry, as the site states the problem:
* Comment section: Conjecture: a(1) = 8; for n > 1, a(n) is the smallest integer m such that
  m = ((2x * a(n-1)) /(x+1)) - x, with x a positive nontrivial divisor of m.
  (This is true at least for a(1) to a(100).) - Enric Reverter i Bigas, Oct 11 2020
* Formula section: Conjectures from Colin Barker, Mar 07 2018:
  G.f.: x*(8 + x - 15*x^2) / ((1 - x)*(1 - 2*x^2)).
  a(n) = 3*2^(n/2-1) + 6 for n even.
  a(n) = 2^((n+1)/2) + 6 for n odd.

Formalization notes:
* An (n+1) X 6 array with entries in 0..2 is a map x : Fin (n + 1) → Fin 6 → Fin 3 (row i,
  column j). Its 2 X 2 subblocks are formed by two adjacent rows i, i+1 and two adjacent columns
  j, j+1. For the subblock [[p, q], [r, s]] (p, q in the upper row), going clockwise
  p -> q -> s -> r -> p gives the edge differences q - p, s - q, r - s, p - r, computed as
  integers; the condition is that these four are pairwise distinct (`CW`). Going counterclockwise,
  or taking each difference with the opposite sign, only permutes and negates the four
  differences, so the condition does not depend on those conventions.
* N(n) is the number of such arrays and a(n) = N(n)/4 is taken as a rational number, so that no
  rounding is involved (the conjectured formulas say that it is an integer).
* Reverter i Bigas: the positive nontrivial divisors of m are the divisors x of m with 1 < x < m.
  The statement says that a(n) is a natural number m that satisfies the condition with
  A = a(n - 1), and that every natural number satisfying it is at least m (`IsLeast`). The
  equation is read in the rationals, with / the exact division. Natural numbers suffice for the
  smallest integer: if an integer m satisfies the equation for a positive integer x and a
  positive integer A, then x + 1 divides 2 x A, hence 2 A, so x + 1 <= 2 A and
  m = x (2 A - x - 1) / (x + 1) >= 0, and m = 0 has no divisor x with 1 < x < m.
* The g.f. is the series A(x) = Sum_{n >= 1} a(n) x^n (the entry starts at n = 1, so the constant
  coefficient is 0). It is stated as A(x) * (1 - x) * (1 - 2 x^2) = x (8 + x - 15 x^2) in the
  ring of formal power series over the rationals; since (1 - x) (1 - 2 x^2) has constant
  coefficient 1 and is invertible there, this is the same as the stated quotient.
* The two parity formulas are stated for every n >= 1 of the given parity, with natural-number
  exponents (n/2 - 1 for even n >= 2 and (n+1)/2 for odd n are exact).
* The definition reproduces all 41 terms of the entry's data (checked by a transfer-matrix
  enumeration of the compatible pairs of rows, which agrees with direct enumeration for small n).
-/

namespace OMA.S_oeis_a209724

open PowerSeries

/-- The clockwise edge differences of the subblock [[p, q], [r, s]] are pairwise distinct. -/
def CW (p q r s : Fin 3) : Prop :=
  [(q : ℤ) - p, (s : ℤ) - q, (r : ℤ) - s, (p : ℤ) - r].Nodup

/-- Every 2 X 2 subblock formed by the rows u (upper) and v (lower) satisfies the condition. -/
def BlockOK (u v : Fin 6 → Fin 3) : Prop :=
  ∀ j : Fin 5, CW (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

/-- N(n): the number of (n+1) X 6 0..2 arrays all of whose 2 X 2 subblocks satisfy the condition. -/
noncomputable def N (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 6 → Fin 3 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- A209724: a(n) = N(n)/4. -/
noncomputable def a (n : ℕ) : ℚ := (N n : ℚ) / 4

/-- Reverter i Bigas's condition on m for the previous term A: m = 2 x A / (x + 1) - x for some
positive nontrivial divisor x of m. -/
def Rev (A : ℚ) (m : ℕ) : Prop :=
  ∃ x : ℕ, x ∣ m ∧ 1 < x ∧ x < m ∧ (m : ℚ) = 2 * x * A / (x + 1) - x

/-- The conjectures of Reverter i Bigas and of Barker. -/
theorem main :
    (a 1 = 8 ∧ ∀ n : ℕ, 1 < n → ∃ m : ℕ, a n = m ∧ IsLeast {k : ℕ | Rev (a (n - 1)) k} m) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((1 - X) * (1 - 2 * X ^ 2)) =
      X * (8 + X - 15 * X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → a n = 3 * 2 ^ (n / 2 - 1) + 6) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → a n = 2 ^ ((n + 1) / 2) + 6) := by
  sorry

end OMA.S_oeis_a209724
