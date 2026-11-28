import Mathlib

/-!
# A330719: a(n) = denominator(Sum_{k=1..n} (2^(k-1) - 1)/k)

Source: https://oeis.org/A330719 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A330719, offset 1: a(n) = denominator(Sum_{k=1..n} (2^(k-1) - 1)/k). Data
1, 2, 2, 4, 4, 12, 12, 24, 8, 40, 40, 120, 120, 840, 840, 1680, 1680, 5040, 5040, 5040, ...
(the denominators of 0, 1/2, 3/2, 13/4, 25/4, 137/12, 245/12, ...).
Entry A330718, offset 1: a(n) = numerator(Sum_{k=1..n} (2^k - 2)/k). Data
0, 1, 3, 13, 25, 137, 245, 871, 517, 4629, 8349, 45517, 83317, ...

Comments of A330719, from Amiram Eldar and Thomas Ordowski, Dec 2019:
Conjecture: if p is an odd prime, then p | A330718(p+1) - a(p+1).

Formalization notes.
* `a n` is A330719(n): the denominator (`Rat.den`, a positive natural number) of the rational
  number Sum_{k=1..n} (2^(k-1) - 1)/k. The sum is over `Finset.Icc 1 n`, so the natural
  subtraction `k - 1` is exact.
* `b n` is A330718(n): the numerator (`Rat.num`, an integer, of the fraction in lowest terms)
  of the rational number Sum_{k=1..n} (2^k - 2)/k.
* `main` is the conjecture: for each odd prime p, p divides A330718(p+1) - A330719(p+1).
-/

namespace OMA.S_oeis_a330719

/-- A330719(n): the denominator of Sum_{k=1..n} (2^(k-1) - 1)/k. -/
def a (n : ℕ) : ℕ := (∑ k ∈ Finset.Icc 1 n, ((2 : ℚ) ^ (k - 1) - 1) / k).den

/-- A330718(n): the numerator of Sum_{k=1..n} (2^k - 2)/k. -/
def b (n : ℕ) : ℤ := (∑ k ∈ Finset.Icc 1 n, ((2 : ℚ) ^ k - 2) / k).num

/-- If p is an odd prime, then p divides A330718(p+1) - A330719(p+1). -/
theorem main : ∀ p : ℕ, p.Prime → Odd p → (p : ℤ) ∣ b (p + 1) - (a (p + 1) : ℤ) := by
  sorry

end OMA.S_oeis_a330719
