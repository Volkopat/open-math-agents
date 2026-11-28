import Mathlib

/-!
# A120114: lcm(1, ..., 2n+4) / lcm(1, ..., 2n+2), and Mersenne primes

Source: https://oeis.org/A120114 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A120114, offset 0: a(n) = lcm(1, ..., 2n+4)/lcm(1, ..., 2n+2). Data
6, 5, 14, 3, 11, 13, 2, 17, 19, 1, 23, 5, 3, 29, 62, 1, 1, 37, 1, 41, 43, 1, 47, 7, 1, 53, 1, 1, ...
Entry A061346: odd numbers that are neither primes nor prime powers
(15, 21, 33, 35, 39, 45, ...).
Entry A083390: integers m such that 2m + 1 divides lcm(1, 3, 5, ..., 2m - 1)
(7, 10, 16, 17, 19, 22, ...).

Comments, conjectures from Davide Rotondo, Dec 02 2024:
Except for 2, if a(n) is even then a(n)/2 is a Mersenne prime.
If a(n)=1 or a(n)=2 then (n*2)+3 is in A061346, or also, or (n+1) is in A083390.

Formalization notes.
* `L m` is lcm(1, ..., m) (`Finset.lcm` on `Finset.Icc 1 m`), and `a n = L (2n+4) / L (2n+2)`
  with offset 0. The quotient is exact, so the division of natural numbers is the true quotient.
* First conjecture: if a(n) is even and a(n) is not 2, then a(n)/2 is a prime of the form
  2^k - 1 (a Mersenne prime).
* Second conjecture: the two alternatives name the same condition (A083390(j) =
  (A061346(j) - 1)/2), and `main` states both. Membership of 2n+3 in A061346 is: 2n+3 is odd,
  not a prime and not a prime power. Membership of m = n+1 in A083390 is: 2m+1 divides
  `oddLcm m` = lcm(1, 3, ..., 2m-1), the lcm of the first m odd numbers.
-/

namespace OMA.S_oeis_a120114

/-- lcm(1, 2, ..., m). -/
def L (m : ℕ) : ℕ := (Finset.Icc 1 m).lcm id

/-- A120114(n) = lcm(1, ..., 2n+4) / lcm(1, ..., 2n+2), offset 0. -/
def a (n : ℕ) : ℕ := L (2 * n + 4) / L (2 * n + 2)

/-- lcm(1, 3, 5, ..., 2m - 1), the lcm of the first m odd numbers. -/
def oddLcm (m : ℕ) : ℕ := (Finset.range m).lcm (fun i => 2 * i + 1)

/-- Rotondo's two conjectures on A120114. -/
theorem main : ∀ n : ℕ,
    (Even (a n) → a n ≠ 2 → (a n / 2).Prime ∧ ∃ k : ℕ, a n / 2 = 2 ^ k - 1) ∧
    (a n = 1 ∨ a n = 2 →
      (Odd (2 * n + 3) ∧ ¬ (2 * n + 3).Prime ∧ ¬ IsPrimePow (2 * n + 3)) ∧
      (2 * (n + 1) + 1) ∣ oddLcm (n + 1)) := by
  sorry

end OMA.S_oeis_a120114
