import Mathlib

/-!
# OEIS A175764: Layman's conjectures a(n) = 1 and a(n) = 9 for the iteration k -> (k^2+4)/d

Source: https://oeis.org/A175764 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (John W. Layman, Aug 30 2010), offset 1: Number of iterations of the mapping k->f(k) to reach
one of 2, 5, or 29, starting with k=n, and with f(k)=(k^2+4)/d, where d is the next-to-largest
divisor of k^2+4, or -1 if the sequence never reaches one of the required values. Comment: It
appears that a(n) is 1 whenever n>29 and n mod 10 is one of {0,1,2,4,6,8,9}. This has been verified
to n=5000. Also, it appears that a(n) is 9 whenever n mod 130 is one of {3,23,55,75,107,127}. This
has also been verified to n=5000. Are these conjectures easy to prove?

Formalization notes:
* The next-to-largest divisor of m >= 2 is its largest proper divisor; k^2 + 4 >= 4.
* a(n) = t means that t is the least number of iterations after which the orbit of n is at 2, 5
  or 29, as in the entry's PARI program (a(n) = 0 if n is one of them, else 1 + a(f(n))). Both
  conjectures assert a value t >= 1, so each is stated as: t is the least element of
  {t | f^[t](n) is 2, 5 or 29}; the value -1 plays no role.
* `main` is the conjunction of both conjectures of the comment.
* Controls: the definitions give f(13) = 173, f(173) = 37, f(37) = 1373, f(1373) = 1217,
  f(1217) = 97, f(97) = 9413, f(9413) = 89 and f(89) = 5, the orbit of the entry's example
  3 -> 13 -> 173 -> ... -> 5, which gives a(3) = 9.
-/

namespace OMA.S_oeis_a175764

/-- The next-to-largest divisor of `m`, i.e. its largest proper divisor. -/
def nextLargest (m : ℕ) : ℕ := (Nat.properDivisors m).sup id

/-- The map of the entry: `f(k) = (k^2+4)/d`, `d` the next-to-largest divisor of `k^2+4`. -/
def f (k : ℕ) : ℕ := (k ^ 2 + 4) / nextLargest (k ^ 2 + 4)

/-- The three values that end the count: 2, 5 and 29. -/
def Target (k : ℕ) : Prop := k = 2 ∨ k = 5 ∨ k = 29

/-- Layman's conjectures: a(n) = 1 for n > 29 with n mod 10 in {0, 1, 2, 4, 6, 8, 9}, and
a(n) = 9 for n mod 130 in {3, 23, 55, 75, 107, 127}. -/
theorem main :
    (∀ n : ℕ, 29 < n →
      (n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 4 ∨ n % 10 = 6 ∨ n % 10 = 8 ∨
        n % 10 = 9) →
      IsLeast {t : ℕ | Target (f^[t] n)} 1) ∧
    (∀ n : ℕ,
      (n % 130 = 3 ∨ n % 130 = 23 ∨ n % 130 = 55 ∨ n % 130 = 75 ∨ n % 130 = 107 ∨
        n % 130 = 127) →
      IsLeast {t : ℕ | Target (f^[t] n)} 9) := by
  sorry

end OMA.S_oeis_a175764
