import Mathlib

/-!
# A319610: minimal number of successive OFF cells in the n-th generation of rule 30

Source: https://oeis.org/A319610 (conjectures in the formula section of the entry)

Entry (offset 0): a(n) is the minimal number of successive OFF cells that appears in n-th
generation of rule-30 1D cellular automaton started from a single ON cell. OFF cells outside
the triangle of active cells are ignored.
Conjectures: G.f.: x (x + x/(1 - x) + x^3 + x^5 + x^7); for all n>=10, a(n)=1.

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i
  is bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Generation 0 has the single ON cell 0 of Z, all other cells OFF; each generation applies the
  rule to every cell.
* A block of successive OFF cells is a maximal one: cells i, ..., i+L-1 (L >= 1) are OFF and
  cells i-1 and i+L are ON (`IsRun false t L`). Being bounded by ON cells on both sides, such a
  block lies inside the triangle of active cells, and the unbounded OFF regions outside the
  triangle are not blocks, as the entry prescribes.
* `a n` is the least length of such a block in generation n, and 0 when there is none
  (`sInf` of the empty set of naturals is 0), matching a(0) = a(1) = 0 in the entry.
* Since `1 - x` has constant term 1, the g.f. identity A(x) = x (x + x/(1 - x) + x^3 + x^5 + x^7)
  for A(x) = Sum_(n >= 0) a(n) x^n is stated after multiplying by `1 - X`, in the formal power
  series ring over the integers.
* Controls from the entry: a(0..) = 0, 0, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1.
-/

namespace OMA.S_oeis_a319610

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Generation t of rule 30 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 30 (state t (i - 1)) (state t i) (state t (i + 1))

/-- Generation `t` has a maximal block of exactly `L >= 1` successive cells with value `v`. -/
def IsRun (v : Bool) (t L : ℕ) : Prop :=
  1 ≤ L ∧ ∃ i : ℤ, (∀ k : ℕ, k < L → state t (i + k) = v) ∧
    state t (i - 1) = !v ∧ state t (i + L) = !v

/-- A319610(n): the minimal length of a block of successive OFF cells in generation n. -/
noncomputable def a (n : ℕ) : ℕ := sInf {L : ℕ | IsRun false n L}

theorem main :
    mk (fun n => (a n : ℤ)) * (1 - X) = X * ((X + X ^ 3 + X ^ 5 + X ^ 7) * (1 - X) + X) ∧
    ∀ n : ℕ, 10 ≤ n → a n = 1 := by
  sorry

end OMA.S_oeis_a319610
