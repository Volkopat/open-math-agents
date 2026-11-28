import Mathlib

/-!
# OEIS A190038: Barker's conjectures for nondecreasing arrangements of n+2 numbers in 0..6 with the last equal to 6 and each after the second equal to the sum of one or two of the preceding three

Source: https://oeis.org/A190038 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A190038 (R. H. Hardin, May 04 2011), offset 1: Number of nondecreasing arrangements of n+2 numbers in 0..6 with the last equal to 6 and each after the second equal to the sum of one or two of the preceding three.
Formula section:
Empirical: a(n) = 4*n^2 - 8*n + 11 for n>5.
Conjectures from Colin Barker, May 04 2018: (Start)
G.f.: x*(10 - 12*x + 6*x^2 + x^3 + 3*x^4 + 2*x^5 - x^6 - x^7) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>8.
(End)

Formalization notes:
* An arrangement of n+2 numbers in 0..6 is a map x : Fin (n + 2) -> Fin 7; it is nondecreasing
  when x is monotone, and its last entry is x (n + 1) = 6.
* Each entry after the second, at position i >= 2 (counting from 0), must equal the entry at one
  of the positions i - 3, i - 2, i - 1 that exist, or the sum of the entries at two different such
  positions (`okAt`). Allowing the same entry twice in a sum gives other counts (15, 31, 58, ...),
  while this reading reproduces every listed term of the table A190041 (of which the entry is
  column 6) with length at most 12 and k at most 10, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^3 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 8, as an identity of integers.
* The definition reproduces the entry's data (10, 18, 30, 47, 72, 107, ... from n = 1, checked by
  direct enumeration for small n and against every listed term through the recursion of the
  proof).
-/

namespace OMA.S_oeis_a190038

open PowerSeries Finset

/-- Entry i of x is the entry at one of the (at most three) positions just before i, or the sum of
the entries at two different such positions. -/
def okAt {L N : ℕ} (x : Fin L → Fin N) (i : Fin L) : Prop :=
  ∃ j l : Fin L, j < i ∧ l < i ∧ (i : ℕ) ≤ j + 3 ∧ (i : ℕ) ≤ l + 3 ∧
    ((x i : ℕ) = x j ∨ (j ≠ l ∧ (x i : ℕ) = x j + x l))

/-- x is nondecreasing, its last entry is 6, and every entry after the second is the sum of one
or two of the preceding three entries. -/
def good {n : ℕ} (x : Fin (n + 2) → Fin 7) : Prop :=
  Monotone x ∧ (x (Fin.last (n + 1)) : ℕ) = 6 ∧ ∀ i : Fin (n + 2), 2 ≤ (i : ℕ) → okAt x i

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good okAt Monotone; infer_instance

/-- A190038: number of nondecreasing arrangements of n+2 numbers in 0..6 with the last equal to 6 and each after the second equal to the sum of one or two of the preceding three. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (n + 2) → Fin 7)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X * (10 - 12 * X + 6 * X ^ 2 + X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 - X ^ 6 - X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a190038
