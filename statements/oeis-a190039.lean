import Mathlib

/-!
# OEIS A190039: Barker's conjectures for nondecreasing arrangements of n+2 numbers in 0..7 with the last equal to 7 and each after the second equal to the sum of one or two of the preceding three

Source: https://oeis.org/A190039 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A190039 (R. H. Hardin, May 04 2011), offset 1: Number of nondecreasing arrangements of n+2 numbers in 0..7 with the last equal to 7 and each after the second equal to the sum of one or two of the preceding three.
Formula section:
Empirical: a(n) = 20*n - 60 for n>5.
Conjectures from Colin Barker, May 04 2018: (Start)
G.f.: x*(11 - 5*x - x^2 + 4*x^3 + 3*x^4 + 5*x^5 + 3*x^6) / (1 - x)^2.
a(n) = 2*a(n-1) - a(n-2) for n>7.
(End)

Formalization notes:
* An arrangement of n+2 numbers in 0..7 is a map x : Fin (n + 2) -> Fin 8; it is nondecreasing
  when x is monotone, and its last entry is x (n + 1) = 7.
* Each entry after the second, at position i >= 2 (counting from 0), must equal the entry at one
  of the positions i - 3, i - 2, i - 1 that exist, or the sum of the entries at two different such
  positions (`okAt`). Allowing the same entry twice in a sum gives other counts (11, 20, 31, ...),
  while this reading reproduces every listed term of the table A190041 (of which the entry is
  column 7) with length at most 12 and k at most 10, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^2 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 7, as an identity of integers.
* The definition reproduces the entry's data (11, 17, 22, 31, 43, 60, ... from n = 1, checked by
  direct enumeration for small n and against every listed term through the recursion of the
  proof).
-/

namespace OMA.S_oeis_a190039

open PowerSeries Finset

/-- Entry i of x is the entry at one of the (at most three) positions just before i, or the sum of
the entries at two different such positions. -/
def okAt {L N : ℕ} (x : Fin L → Fin N) (i : Fin L) : Prop :=
  ∃ j l : Fin L, j < i ∧ l < i ∧ (i : ℕ) ≤ j + 3 ∧ (i : ℕ) ≤ l + 3 ∧
    ((x i : ℕ) = x j ∨ (j ≠ l ∧ (x i : ℕ) = x j + x l))

/-- x is nondecreasing, its last entry is 7, and every entry after the second is the sum of one
or two of the preceding three entries. -/
def good {n : ℕ} (x : Fin (n + 2) → Fin 8) : Prop :=
  Monotone x ∧ (x (Fin.last (n + 1)) : ℕ) = 7 ∧ ∀ i : Fin (n + 2), 2 ≤ (i : ℕ) → okAt x i

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good okAt Monotone; infer_instance

/-- A190039: number of nondecreasing arrangements of n+2 numbers in 0..7 with the last equal to 7 and each after the second equal to the sum of one or two of the preceding three. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (n + 2) → Fin 8)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 2 =
      X * (11 - 5 * X - X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + 5 * X ^ 5 + 3 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  sorry

end OMA.S_oeis_a190039
