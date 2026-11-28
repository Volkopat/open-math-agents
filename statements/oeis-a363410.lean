import Mathlib

/-!
# A363410: a(n) = 1/sqrt(2) * the imaginary part of Product_{k = 1..n} (1 + k*sqrt(-2)).

Source: https://oeis.org/A363410 (Peter Bala)
Credit: @Squee451

Data (offset 0): 0, 1, 3, -6, -90, 45, 5607, 8316, -616572, -2517075, 106354215, 779869134, ...

The entry's comments divide the primes into three types, following Moll's study of A105750;
"Type 1: primes p that do not divide any element of the sequence {a(n)}", and then:
"We conjecture that in this case, unlike in A105750, the set of type 1 primes is empty; that is,
every prime p divides some term of this sequence."

Conventions.
* `sqrt(-2)` is `i * sqrt 2`, so `a n` is the imaginary part of the complex product divided by the
  real number `sqrt 2`. The terms are integers; `a n` is defined here as a real number, exactly as in
  the title, and "p divides a(n)" is written `a n = p * q` for an integer `q`.
* a(0) = 0 (empty product), which every prime divides trivially; the entry's valuation tables run
  over n >= 1. The statement therefore asks for an index `n ≥ 1`.
* The entry's other conjectures (the description of the type 2 and type 3 primes and the asymptotic
  valuation) are not part of this statement.
-/

namespace OMA.S_oeis_a363410

/-- A363410: `a n = (1 / sqrt 2) * Im (∏_{k=1..n} (1 + k * sqrt(-2)))`, with `sqrt(-2) = i * sqrt 2`. -/
noncomputable def a (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.Icc 1 n, (1 + (k : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) * Complex.I)).im / Real.sqrt 2

/-- Every prime divides some term `a n` with `n ≥ 1`. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ n : ℕ, 1 ≤ n ∧ ∃ q : ℤ, a n = (p : ℝ) * (q : ℝ) := by
  sorry

end OMA.S_oeis_a363410
