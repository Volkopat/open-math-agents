import Mathlib

/-!
# A319658: minimal number of successive ON cells in the n-th generation of rule 30

Source: https://oeis.org/A319658 (conjectures in the formula section of the entry)

Entry (offset 1): a(n) is the minimal number of successive ON cells that appears in n-th
generation of rule-30 1D cellular automaton started from a single ON cell.
Conjectures: G.f.: 1/(1 - x) + 2 x + x^3 + x^5 + x^7 + x^13; for all n >= 15, a(n)=1.

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i
  is bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* `state 0` has the single ON cell 0 of Z, all other cells OFF; each step applies the rule to
  every cell. With the offset 1 of the entry, generation n is `state (n - 1)` (generation 1 is
  the initial single cell, so a(1) = 1 and a(2) = 3 as in the data).
* A block of successive ON cells is a maximal one: cells i, ..., i+L-1 (L >= 1) are ON and
  cells i-1 and i+L are OFF (`IsRun true t L`).
* `a n` is the least length of such a block in generation n (every generation has ON cells,
  so the set is nonempty for n >= 1; the value at n = 0 is irrelevant and never used).
* The g.f. in the entry has constant term 1 = a(1), i.e. it is written for the sequence
  re-indexed from 0 (a missing leading factor x for offset 1): it is the series
  Sum_(m >= 0) a(m+1) x^m. Since `1 - x` has constant term 1, the identity is stated after
  multiplying by `1 - X`, in the formal power series ring over the integers.
* Controls from the entry: a(1..) = 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1.
-/

namespace OMA.S_oeis_a319658

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `state t`: rule 30 after `t` steps from a single ON cell at 0 (generation t + 1). -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 30 (state t (i - 1)) (state t i) (state t (i + 1))

/-- `state t` has a maximal block of exactly `L >= 1` successive cells with value `v`. -/
def IsRun (v : Bool) (t L : ℕ) : Prop :=
  1 ≤ L ∧ ∃ i : ℤ, (∀ k : ℕ, k < L → state t (i + k) = v) ∧
    state t (i - 1) = !v ∧ state t (i + L) = !v

/-- A319658(n): the minimal length of a block of successive ON cells in generation n. -/
noncomputable def a (n : ℕ) : ℕ := sInf {L : ℕ | IsRun true (n - 1) L}

theorem main :
    mk (fun m => (a (m + 1) : ℤ)) * (1 - X) =
      1 + (2 * X + X ^ 3 + X ^ 5 + X ^ 7 + X ^ 13) * (1 - X) ∧
    ∀ n : ℕ, 15 ≤ n → a n = 1 := by
  sorry

end OMA.S_oeis_a319658
