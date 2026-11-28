import Mathlib.Data.List.Permutation

/-!
# Semicircle spirals (OEIS A236754)

Source: Kival Ngaokrajang, https://oeis.org/A236754 and https://oeis.org/A236535
Credit: @LDJAI

Translate the unit-spaced centers to coordinates 0 through n-1. A list gives
their positions in order of use. This amounts to reading the positions of the
labels 1 through n in the source's diagram. Each labeled order is counted once,
including orders related by reversal, rotation or reflection.

A semicircle about c takes its entering endpoint x to 2*c-x, including the
case of zero radius. The initial radius is one. We take the starting endpoint
on the left, as in the A236754 program with pat = -1.
-/

namespace OMA.S_oeis_a236754

/-- Endpoint after using the indicated centers, in order, from x. -/
def traverse : List ℕ → ℤ → ℤ
  | [], x => x
  | c :: cs, x => traverse cs (2 * (c : ℤ) - x)

def start (cs : List ℕ) : ℤ := (cs.headD 0 : ℤ) - 1

/-- Endpoint after k complete repetitions of the center list. -/
def afterLaps (cs : List ℕ) (x : ℤ) : ℕ → ℤ
  | 0 => x
  | k + 1 => traverse cs (afterLaps cs x k)

/-- Return to the initial endpoint, next center and upper/lower semicircle phase. -/
def IsLoop (cs : List ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (k * cs.length) % 2 = 0 ∧ afterLaps cs (start cs) k = start cs

/-- Semicircle radii are unbounded. At position i, the entering endpoint is
obtained by traversing precisely the centers before i in the current lap. -/
def IsExpanded (cs : List ℕ) : Prop :=
  ∀ B : ℕ, ∃ k : ℕ, ∃ i : Fin cs.length,
    B < (traverse (cs.take i.val) (afterLaps cs (start cs) k) - (cs[i] : ℤ)).natAbs

/-- Count each labeled permutation of the n distinct centers that closes. -/
noncomputable def loopCount (n : ℕ) : ℕ := by
  classical
  exact ((List.range n).permutations.filter (fun cs => decide (IsLoop cs))).length

/-- A236754 has offset one, so the multiples of four start at four. -/
theorem main :
    (∀ n : ℕ, n % 2 = 1 →
      (∀ cs : List ℕ, cs.Perm (List.range n) → IsLoop cs) ∧ loopCount n = n.factorial) ∧
    (∀ n : ℕ, 0 < n → n % 4 = 0 →
      (∃ cs : List ℕ, cs.Perm (List.range n) ∧ IsLoop cs) ∧
      (∃ cs : List ℕ, cs.Perm (List.range n) ∧ IsExpanded cs)) := by
  sorry

end OMA.S_oeis_a236754
