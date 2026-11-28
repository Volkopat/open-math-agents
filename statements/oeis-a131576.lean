import Mathlib

/-!
# OEIS A131576: sums of an even number of consecutive integers

Source: https://oeis.org/A131576 (OEIS Foundation, CC BY-SA 4.0).

`a(n)` is the number of ways to represent `n` as a sum of an even number of consecutive integers.
Offset 1; the data begins `0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, ...`. The integers are positive:
with `0` or negative terms allowed, `1 = 0 + 1` and `2 = -1 + 0 + 1 + 2` would make `a(1)` and
`a(2)` positive, against the data (and against the entry's comment that `a(n)` is the number of
odd divisors of `n` greater than `sqrt(2n)`).

Conjectures (Omar E. Pol, Feb 22 2017, formula section of the entry):
`a(n) = (A001227(n) - A067742(n))/2 = A082647(n) - A067742(n)`, where
* A001227(n) is the number of odd divisors of `n`;
* A067742(n) is the number of middle divisors of `n`, i.e. divisors in the half-open interval
  `[sqrt(n/2), sqrt(n*2))`;
* A082647(n) is the number of ways `n` can be expressed as the sum of `d` consecutive positive
  integers where `d > 0` is a divisor of `n`.

Formalization notes:
* A representation of `n` as a sum of `j` consecutive positive integers is a pair `(s, j)` with
  `s, j ≥ 1` and `s + (s + 1) + ... + (s + j - 1) = n`; both `s` and `j` are then at most `n`.
* Both conjectured identities are stated, with natural-number subtraction and division, for every
  `n ≥ 1`.
-/

namespace OMA.S_oeis_a131576

/-- Pairs `(s, j)` with `s, j ≥ 1` and `s + (s + 1) + ... + (s + j - 1) = n`. -/
def reps (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p => ∑ i ∈ Finset.range p.2, (p.1 + i) = n)

/-- A131576(n): the number of ways to write `n` as a sum of an even number of consecutive positive
integers. -/
def a (n : ℕ) : ℕ := ((reps n).filter (fun p => Even p.2)).card

/-- A001227(n): the number of odd divisors of `n`. -/
def A001227 (n : ℕ) : ℕ := (n.divisors.filter Odd).card

open Classical in
/-- A067742(n): the number of divisors of `n` in the half-open interval `[sqrt(n/2), sqrt(n*2))`. -/
noncomputable def A067742 (n : ℕ) : ℕ :=
  (n.divisors.filter
    (fun d : ℕ => Real.sqrt ((n : ℝ) / 2) ≤ (d : ℝ) ∧ (d : ℝ) < Real.sqrt ((n : ℝ) * 2))).card

/-- A082647(n): the number of ways `n` is the sum of `d` consecutive positive integers where
`d > 0` is a divisor of `n`. -/
def A082647 (n : ℕ) : ℕ := ((reps n).filter (fun p => p.2 ∣ n)).card

/-- Pol's conjectures. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = (A001227 n - A067742 n) / 2 ∧ a n = A082647 n - A067742 n := by
  sorry

end OMA.S_oeis_a131576
