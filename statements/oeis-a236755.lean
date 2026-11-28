import Mathlib.Data.List.Permutation

/-!
# Expanded semicircle spirals (OEIS A236755)

Source: Kival Ngaokrajang, https://oeis.org/A236755 and https://oeis.org/A236535
Credit: @jacklarmer. The geometric definitions follow the companion A236754 (PR #4478).

Translate the unit-spaced centers to coordinates 0 through n-1. A list gives the
coordinates of labels 1 through n in the order in which the semicircles use them.
The source counts every labeled arrangement, including rotations and reversals.
Each semicircle about c sends its entering endpoint x to 2*c-x. The source's
program starts at radius one. We use the initial endpoint to the left of the first
center. For even n the displacement in a full lap is independent of that choice.
-/

namespace OMA.S_oeis_a236755

/-- Endpoint after using the indicated centers in order, starting from x. -/
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

/-- Radii are unbounded. The radius at position i is the distance from the
entering endpoint to that center. -/
def IsExpanded (cs : List ℕ) : Prop :=
  ∀ B : ℕ, ∃ k : ℕ, ∃ i : Fin cs.length,
    B < (traverse (cs.take i.val) (afterLaps cs (start cs) k) - (cs[i] : ℤ)).natAbs

/-- Number of labeled center arrangements whose semicircle radii are unbounded. -/
noncomputable def expandedCount (n : ℕ) : ℕ := by
  classical
  exact ((List.range n).permutations.filter (fun cs => decide (IsExpanded cs))).length

/-- The sequence has offset one, so the multiples of four start at four. -/
theorem main :
    (∀ n : ℕ, n % 4 = 2 →
      (∀ cs : List ℕ, cs.Perm (List.range n) → IsExpanded cs) ∧ expandedCount n = n.factorial) ∧
    (∀ n : ℕ, 0 < n → n % 4 = 0 →
      (∃ cs : List ℕ, cs.Perm (List.range n) ∧ IsLoop cs) ∧
      (∃ cs : List ℕ, cs.Perm (List.range n) ∧ IsExpanded cs)) := by
  sorry

end OMA.S_oeis_a236755
