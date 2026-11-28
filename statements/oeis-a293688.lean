import Mathlib

/-!
# OEIS A293688: the partial sums of A002251 are (n + 1) A005206(n)

Source: https://oeis.org/A293688 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Enrique Navarrete, Oct 14 2017), offset 0: Partial sums of A002251.
a(n) = (n+1)*A005206(n) where A005206 is the Hofstadter G-sequence. [Apparently this is a
conjecture, rather than a theorem. - N. J. A. Sloane, Mar 03 2019]
Data: 0, 2, 3, 8, 15, 18, 28, 32, 45, 60, 66, 84, ...
A002251 (Michael Kleber), offset 0: Start with the nonnegative integers; then swap L(k) and U(k)
for all k >= 1, where L = A000201, U = A001950 (lower and upper Wythoff sequences).
A000201 (N. J. A. Sloane): Lower Wythoff sequence (a Beatty sequence): a(n) = floor(n*phi), where
phi = (1+sqrt(5))/2 = A001622. A001950 (N. J. A. Sloane): Upper Wythoff sequence (a Beatty
sequence): a(n) = floor(n*phi^2), where phi = (1+sqrt(5))/2.
A005206 (N. J. A. Sloane), offset 0: Hofstadter G-sequence: a(0) = 0; a(n) = n - a(a(n-1)) for
n > 0.

Formalization notes:
* `lowerW k` and `upperW k` are floor(k phi) and floor(k phi^2), with phi = `Real.goldenRatio`
  = (1 + sqrt 5)/2.
* `swapW` is A002251: a value L(k) with k >= 1 goes to U(k), a value U(k) with k >= 1 goes to L(k),
  and every other number (here only 0) is kept. `Classical.choose` picks the k, which is unique
  because L and U are strictly increasing; the two sets of values are disjoint (Rayleigh), so the
  second case is reached only for values that are not an L(k).
* `a n` is the partial sum A002251(0) + ... + A002251(n) (offset 0, as in the entry).
* `IsG G` states the definition of A005206: G(0) = 0 and G(n) = n - G(G(n-1)) for n > 0. These
  conditions determine G term by term (by induction G(k) <= k, so the nested argument is an earlier
  index), so `main` is stated for every function satisfying them.
-/

namespace OMA.S_oeis_a293688

/-- A000201: the lower Wythoff sequence floor(k phi). -/
noncomputable def lowerW (k : ℕ) : ℕ := ⌊(k : ℝ) * Real.goldenRatio⌋₊

/-- A001950: the upper Wythoff sequence floor(k phi^2). -/
noncomputable def upperW (k : ℕ) : ℕ := ⌊(k : ℝ) * Real.goldenRatio ^ 2⌋₊

open Classical in
/-- A002251: the nonnegative integers with L(k) and U(k) swapped for every k >= 1. -/
noncomputable def swapW (m : ℕ) : ℕ :=
  if h : ∃ k, 1 ≤ k ∧ lowerW k = m then upperW h.choose
  else if h' : ∃ k, 1 ≤ k ∧ upperW k = m then lowerW h'.choose else m

/-- A293688(n) = A002251(0) + ... + A002251(n). -/
noncomputable def a (n : ℕ) : ℕ := ∑ m ∈ Finset.range (n + 1), swapW m

/-- The definition of the Hofstadter G-sequence A005206: G(0) = 0 and G(n) = n - G(G(n-1)) for
n > 0. -/
def IsG (G : ℕ → ℕ) : Prop := G 0 = 0 ∧ ∀ n : ℕ, 1 ≤ n → G n = n - G (G (n - 1))

/-- The conjecture: a(n) = (n + 1) A005206(n). -/
theorem main : ∀ G : ℕ → ℕ, IsG G → ∀ n : ℕ, a n = (n + 1) * G n := by
  sorry

end OMA.S_oeis_a293688
