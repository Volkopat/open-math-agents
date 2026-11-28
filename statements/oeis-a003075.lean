import Mathlib

/-!
# OEIS A003075: minimal sorting networks for 13–16 inputs

Source: https://oeis.org/A003075
`a n` is the minimal number of comparators in an `n`-input sorting network:
0, 1, 3, 5, 9, 12, 16, 19, 25, 29, 35, 39 for `n = 1, …, 12`. It is conjectured that the
sequence continues 45, 51, 56, 60 (for `n = 13, 14, 15, 16`). `main` states these four values.

Conventions. A comparator network on `n` wires is a list of pairs `(i, j)` with `i < j`;
the comparator `(i, j)` replaces the values on wires `i` and `j` by their minimum and maximum
respectively. A sorting network turns every input `v : Fin n → ℕ` into a monotone output.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a003075

/-- Apply the comparator `(i, j)` to `v`. -/
def comparator {n : ℕ} (c : Fin n × Fin n) (v : Fin n → ℕ) : Fin n → ℕ :=
  fun k => if k = c.1 then min (v c.1) (v c.2)
    else if k = c.2 then max (v c.1) (v c.2) else v k

/-- Run a comparator network (comparators applied from the head of the list). -/
def run {n : ℕ} (L : List (Fin n × Fin n)) (v : Fin n → ℕ) : Fin n → ℕ :=
  L.foldl (fun w c => comparator c w) v

/-- `L` is a sorting network on `n` wires. -/
def IsSortingNetwork {n : ℕ} (L : List (Fin n × Fin n)) : Prop :=
  (∀ c ∈ L, c.1 < c.2) ∧ ∀ v : Fin n → ℕ, Monotone (run L v)

/-- The minimal size of a sorting network on `n` wires. -/
noncomputable def minSize (n : ℕ) : ℕ :=
  sInf {s | ∃ L : List (Fin n × Fin n), IsSortingNetwork L ∧ L.length = s}

theorem main :
    minSize 13 = 45 ∧ minSize 14 = 51 ∧ minSize 15 = 56 ∧ minSize 16 = 60 := by
  sorry

end OMA.S_oeis_a003075
