import Mathlib

/-!
# A278989: a(n) is the number of words of length n over an alphabet of size 4 that are in standard order and which have the property that every letter that appears in the word is repeated.

Source: https://oeis.org/A278989
Credit: @ivillar

Status: open conjecture (Colin Barker, Nov 25 2017). The entry records, as conjectures:
* G.f.: x^2*(1 - 19*x + 159*x^2 - 776*x^3 + 2474*x^4 - 5498*x^5 + 8993*x^6 - 11471*x^7 +
  11815*x^8 - 9478*x^9 + 5348*x^10 - 1848*x^11 + 288*x^12) /
  ((1 - x)^4*(1 - 2*x)^3*(1 - 3*x)^2*(1 - 4*x)).
* a(n) = 20*a(n-1) - 175*a(n-2) + 882*a(n-3) - 2835*a(n-4) + 6072*a(n-5) - 8777*a(n-6) +
  8458*a(n-7) - 5204*a(n-8) + 1848*a(n-9) - 288*a(n-10) for n > 14.
This file formalizes the second one, the recurrence, for every n > 14 exactly as stated.

Formalization notes:
* Offset 0, as in the entry (data: 0, 0, 1, 1, 4, 11, 41, 162, 715, 3425, 16777, ...).
* The alphabet is `{0, 1, 2, 3}` (`Fin 4`) and a word of length n is a map `w : Fin n → Fin 4`.
  As in the companion entries (A278984 and following) and in the statement of A278988, a word
  is in standard order when each letter other than the first one, 0, is preceded somewhere in
  the word by the letter before it; equivalently the letters make their first appearances in
  the order 0, 1, 2, 3 (so a nonempty word starts with 0). `Repeated w` says that every letter
  occurring in `w` occurs at least twice.
* With this reading the counts agree with the data for 1 ≤ n ≤ 15. For n = 0 the empty word
  would be counted, while the entry has a(0) = 0; the recurrence for n > 14 only involves
  n >= 5, so this convention does not matter here. For the same reason the g.f. (which encodes
  a(0) = 0) is not formalized.
* The recurrence is stated in `ℤ`.
-/

namespace OMA.S_oeis_a278989

/-- A word is in standard order: every occurrence of a letter `c ≠ 0` is preceded by an
occurrence of the letter `c - 1`. -/
def StdOrder {n : ℕ} (w : Fin n → Fin 4) : Prop :=
  ∀ i, w i ≠ 0 → ∃ j, j < i ∧ (w j : ℕ) + 1 = w i

/-- Every letter that appears in the word appears at least twice. -/
def Repeated {n : ℕ} (w : Fin n → Fin 4) : Prop :=
  ∀ c : Fin 4, (∃ i, w i = c) → 2 ≤ (Finset.univ.filter fun i => w i = c).card

/-- A278989(n): the number of words of length n over a 4-letter alphabet in standard order in
which every letter that appears is repeated. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Fin n → Fin 4 // StdOrder w ∧ Repeated w}

/-- Barker's conjectured recurrence (n > 14). -/
theorem main :
    ∀ n : ℕ, 14 < n → (a n : ℤ) = 20 * a (n - 1) - 175 * a (n - 2) + 882 * a (n - 3) -
      2835 * a (n - 4) + 6072 * a (n - 5) - 8777 * a (n - 6) + 8458 * a (n - 7) -
      5204 * a (n - 8) + 1848 * a (n - 9) - 288 * a (n - 10) := by
  sorry

end OMA.S_oeis_a278989
