import Mathlib

/-!
# A305211: number of values of x^3 + y^3 modulo n

Source: https://oeis.org/A305211 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A305211 (Jack Zhang, May 27 2018), offset 1: a(n) is the number of possible values of
(x^3 + y^3) mod n, where x and y are any integers.
Data 1, 2, 3, 4, 5, 6, 5, 8, 5, 10, 11, 12, 13, 10, 15, 16, 17, 10, 19, 20, 15, 22, 23, 24, ...

Comments: Conjecture: keyword mult applies. Furthermore a procedure to find a(n) is as
follows: if n = 7k then n -> 5*n/7. if n = 9k then n-> 5*n/9. return(n).
- David A. Corneth, May 22 2020

Formalization notes.
* `a n` is the number of residues c modulo n of the form x^3 + y^3 (`Set.ncard` of a subset of
  `ZMod n`; the values of x^3 + y^3 modulo n depend only on x and y modulo n).
* The procedure says: a(n) = n * (5/7 if 7 divides n) * (5/9 if 9 divides n). The first part of
  `main` states this without division:
  a(n) * (7 if 7 | n, else 1) * (9 if 9 | n, else 1) = n * (5 if 7 | n, else 1) * (5 if 9 | n,
  else 1).
* "Keyword mult applies" says that a is multiplicative: a(m n) = a(m) a(n) for coprime m, n.
  This is the second part of `main`.
-/

namespace OMA.S_oeis_a305211

/-- A305211: the number of residues modulo n that are a sum of two cubes. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {c : ZMod n | ∃ x y : ZMod n, x ^ 3 + y ^ 3 = c}

/-- Conjecture of Corneth: the formula for a(n), and a is multiplicative. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n →
      a n * ((if 7 ∣ n then 7 else 1) * (if 9 ∣ n then 9 else 1))
        = n * ((if 7 ∣ n then 5 else 1) * (if 9 ∣ n then 5 else 1))) ∧
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → Nat.Coprime m n → a (m * n) = a m * a n) := by
  sorry

end OMA.S_oeis_a305211
