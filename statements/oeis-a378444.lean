import Mathlib

/-!
# A378444: the number of divisors d of n with A083345(d) even is ceiling(A174273(n)/2)

Source: https://oeis.org/A378444 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A378444, offset 1: a(n) is the number of divisors d of n such that A083345(d) is even,
where A083345(n) is the numerator of Sum(e/p: n=Product(p^e)). Data
1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, ...
Entry A083345: Numerator of r(n) = Sum(e/p: n=Product(p^e)) (0, 1, 1, 1, 1, 5, 1, 3, 2, 7, ...).
Entry A174273: Inverse Moebius transform of A035263 (1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 4, ...).
Entry A035263: parity of the 2-adic valuation of 2n, that is, A035263(n) = 1 if the 2-adic
valuation of n is even, and 0 otherwise (1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, ...).

Formula section: a(n) = ceiling(A174273(n)/2). [Conjectured] - Antti Karttunen, May 14 2025

Formalization notes.
* `f n` is the rational number r(n), the sum of e/p over the prime factorization of n
  (`Nat.factorization`), and A083345(n) is its numerator `(f n).num` in lowest terms
  (r(1) = 0 has the numerator 0, which is even).
* `a n` counts the divisors d of n with `(f d).num` even.
* `b n` is A174273(n): the inverse Moebius transform of A035263 is the sum of A035263(d) over
  the divisors d of n.
* ceiling(b/2) is (b + 1) / 2 with the division of natural numbers. `main` is stated for all
  n >= 1 (the offset is 1).
-/

namespace OMA.S_oeis_a378444

/-- r(n) = Sum (e/p : n = Product p^e), the sum over the prime factorization of n. -/
noncomputable def f (n : ℕ) : ℚ := n.factorization.sum (fun p e => (e : ℚ) / (p : ℚ))

/-- A378444(n): the number of divisors d of n such that A083345(d), the numerator of r(d),
is even. -/
noncomputable def a (n : ℕ) : ℕ :=
  open Classical in (n.divisors.filter (fun d => Even (f d).num)).card

/-- A174273(n): the sum over the divisors d of n of A035263(d), where A035263(d) = 1 if the
2-adic valuation of d is even, and 0 otherwise. -/
def b (n : ℕ) : ℕ := ∑ d ∈ n.divisors, if Even (padicValNat 2 d) then 1 else 0

/-- Karttunen's conjecture: a(n) = ceiling(A174273(n)/2). -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = (b n + 1) / 2 := by
  sorry

end OMA.S_oeis_a378444
