import Mathlib

/-!
# A020753: Successive increasing gaps between squarefree numbers

Source: https://oeis.org/A020753
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the size of the `n`-th record (increasing) gap between consecutive squarefree numbers
and A020754(n) its lower end: `(1, 1), (2, 3), (3, 7), (4, 47), …`. Conjecture (Thomas Ordowski,
OEIS, 2015): `a(n) ~ log(A020754(n)) / 2`.

## Encoding

* For a squarefree `s`, `gap s` is the distance to the next squarefree number.
* A record lower end is a squarefree `s` whose gap exceeds the gaps of all smaller squarefree
  numbers; `lowEnd n = Nat.nth IsRecord (n - 1)` (offset `1`) and `a n = gap (lowEnd n)`.
* `~` means the ratio `a(n) / (log(A020754(n)) / 2)` tends to `1`.
-/

namespace OMA.S_oeis_a020753

open Filter Topology

/-- Distance from `s` to the next squarefree number. -/
noncomputable def gap (s : ℕ) : ℕ := sInf {t : ℕ | s < t ∧ Squarefree t} - s

/-- `s` is the lower end of a record gap between squarefree numbers. -/
def IsRecord (s : ℕ) : Prop := Squarefree s ∧ ∀ t < s, Squarefree t → gap t < gap s

/-- A020754: lower end of the `n`-th record gap (offset `1`). -/
noncomputable def lowEnd (n : ℕ) : ℕ := Nat.nth IsRecord (n - 1)

/-- A020753: size of the `n`-th record gap. -/
noncomputable def a (n : ℕ) : ℕ := gap (lowEnd n)

theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / (Real.log (lowEnd n) / 2)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a020753
