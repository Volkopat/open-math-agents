import Mathlib

/-!
# OEIS A195609: Shevelev's three conjectures on partial sums of the odious numbers

Source: https://oeis.org/A195609 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Vladimir Shevelev, Sep 21 2011), offset 1: Numbers n such that
Sum_{i=1..n} A(i) = A(n)*A(n+1)/4, where A(n) = A000069(n).
Conjectures: 1) there are only 3 different first differences 1,4,6; 2) the sequence contains
either isolated series of terms, e.g., {9},{23},{33},{39},..., or series of 3 consecutive
integers, e.g., {3,4,5}, {15,16,17}, etc.; 3)the first terms m of every series satisfy the
condition A(m+1)-A(m-1)=5, where A(n)=A000069(n).

Formalization notes:
* `A n` is A000069(n) for n >= 1, the n-th odious number (odd binary digit sum), written as
  `Nat.nth` of the odious predicate at index n - 1, so `A 1 = 1`, `A 2 = 2`, `A 3 = 4`.
* `IsTerm n`: n >= 1 and the defining equation holds in the rationals (its right side can be a
  fraction).
* Conjecture 1: the set of first differences, the gaps m' - m between consecutive terms m < m'
  (no term strictly between them), is exactly {1, 4, 6}.
* Conjecture 2: every maximal block a, a+1, ..., b of consecutive integers that are all terms
  (a - 1 and b + 1 not terms) has 1 or 3 elements, that is b - a = 0 or b - a = 2.
* Conjecture 3: if m is a term and m - 1 is not (m is the first term of its block), then
  A(m+1) - A(m-1) = 5, computed in the integers. Every term is at least 3, so A(m-1) is a genuine
  value of A000069.
* `main` is the conjunction of the three conjectures.
* Controls proved in the proof file: the terms up to 17 are exactly 3, 4, 5, 9, 15, 16, 17, as
  in the entry's data.
-/

namespace OMA.S_oeis_a195609

/-- `A n` = A000069(n), n ≥ 1: the n-th number with odd binary digit sum (`A 1 = 1`). -/
noncomputable def A (n : ℕ) : ℕ := Nat.nth (fun k => (Nat.digits 2 k).sum % 2 = 1) (n - 1)

/-- `n` is a term of A195609. -/
def IsTerm (n : ℕ) : Prop :=
  1 ≤ n ∧ ((∑ i ∈ Finset.Icc 1 n, A i : ℕ) : ℚ) = ((A n * A (n + 1) : ℕ) : ℚ) / 4

/-- `d` is a first difference: the gap between two consecutive terms. -/
def IsFirstDiff (d : ℕ) : Prop :=
  ∃ m m', IsTerm m ∧ IsTerm m' ∧ m < m' ∧ (∀ j, m < j → j < m' → ¬ IsTerm j) ∧ d = m' - m

/-- Shevelev's three conjectures in A195609. -/
theorem main :
    {d | IsFirstDiff d} = {1, 4, 6} ∧
    (∀ a b, a ≤ b → (∀ j, a ≤ j → j ≤ b → IsTerm j) → ¬ IsTerm (a - 1) → ¬ IsTerm (b + 1) →
      b - a = 0 ∨ b - a = 2) ∧
    (∀ m, IsTerm m → ¬ IsTerm (m - 1) → (A (m + 1) : ℤ) - A (m - 1) = 5) := by
  sorry

end OMA.S_oeis_a195609
