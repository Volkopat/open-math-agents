import Mathlib

/-!
# A278988: a(n) is the number of words of length n over an alphabet of size 3 that are in standard order and which have the property that every letter that appears in the word is repeated.

Source: https://oeis.org/A278988
Credit: @ivillar

Status: open conjecture (Colin Barker, Nov 25 2017). The entry records, as conjectures:
* G.f.: x^2*(1 - 9*x + 34*x^2 - 71*x^3 + 100*x^4 - 97*x^5 + 52*x^6 - 12*x^7) /
  ((1 - x)^3*(1 - 2*x)^2*(1 - 3*x)).
* a(n) = (2*(3+3^n) - 3*(2+2^n)*n + 6*n^2) / 12 for n>3.
* a(n) = 10*a(n-1) - 40*a(n-2) + 82*a(n-3) - 91*a(n-4) + 52*a(n-5) - 12*a(n-6) for n>9.
This file states the closed form (for every n > 3) and the recurrence (for every n > 9).

Formalization notes:
* Offset 0, as in the entry (data: 0, 0, 1, 1, 4, 11, 41, 162, 610, 2165, ...).
* The alphabet is `{0, 1, 2}` (`Fin 3`) and a word of length n is a map `w : Fin n → Fin 3`.
  As in the companion entries (A278984 and following), a word is in standard order when each
  letter other than the first one, 0, is preceded somewhere in the word by the letter before it;
  equivalently the letters make their first appearances in the order 0, 1, 2 (so a nonempty
  word starts with 0). `Repeated w` says that every letter occurring in `w` occurs at least twice.
* With this reading the counts agree with the data for 1 ≤ n ≤ 12 (checked by exhaustive
  enumeration). For n = 0 the empty word would be counted, while the entry has a(0) = 0; the
  statements below only concern n > 3, so this convention does not matter here. For the same
  reason the g.f. (which encodes a(0) = 0) is not formalized.
* Both formulas are stated in `ℤ`; the division by 12 is exact.
-/

namespace OMA.S_oeis_a278988

/-- A word is in standard order: every occurrence of a letter `c ≠ 0` is preceded by an
occurrence of the letter `c - 1`. -/
def StdOrder {n : ℕ} (w : Fin n → Fin 3) : Prop :=
  ∀ i, w i ≠ 0 → ∃ j, j < i ∧ (w j : ℕ) + 1 = w i

/-- Every letter that appears in the word appears at least twice. -/
def Repeated {n : ℕ} (w : Fin n → Fin 3) : Prop :=
  ∀ c : Fin 3, (∃ i, w i = c) → 2 ≤ (Finset.univ.filter fun i => w i = c).card

/-- A278988(n): the number of words of length n over a 3-letter alphabet in standard order in
which every letter that appears is repeated. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Fin n → Fin 3 // StdOrder w ∧ Repeated w}

/-- Barker's conjectured closed form (n > 3) and recurrence (n > 9). -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = (2 * (3 + 3 ^ n) - 3 * (2 + 2 ^ n) * n + 6 * n ^ 2) / 12) ∧
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 10 * a (n - 1) - 40 * a (n - 2) + 82 * a (n - 3) -
      91 * a (n - 4) + 52 * a (n - 5) - 12 * a (n - 6)) := by
  sorry

end OMA.S_oeis_a278988
