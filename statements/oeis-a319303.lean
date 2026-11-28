import Mathlib

/-!
# A319303: the value of the node of the Collatz tree encoded by the number n

Source: https://oeis.org/A319303 (claim in the comments of the entry)

Claim: If the Collatz conjecture is true, then this sequence contains all positive integers.

Conventions:
* The encoding is the procedure of the entry (and its PARI program): start at the root v = 1
  with r = n; while r > 0: decrement r; if v is a branching node other than 4 (v > 4 and
  v + 2 is a multiple of 6) then move to the child 2v if r is even and to the child (v-1)/3
  otherwise, and replace r by floor(r/2); else move to the only child 2v. a(n) (offset 0) is
  the value of the final node. `walk r v` runs this loop from node v with counter r.
* `collatz x` is the 3x+1 map (x/2 for even x, 3x+1 for odd x); the Collatz conjecture is the
  hypothesis that every positive integer has an iterate equal to 1.
-/

namespace OMA.S_oeis_a319303

/-- The Collatz (3x+1) map. -/
def collatz (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- The encoding loop of the entry, started at node v with counter r. -/
def walk : ℕ → ℕ → ℕ
  | 0, v => v
  | r + 1, v =>
    if 4 < v ∧ (v + 2) % 6 = 0 then
      (if r % 2 = 0 then walk (r / 2) (2 * v) else walk (r / 2) ((v - 1) / 3))
    else walk r (2 * v)
termination_by r => r
decreasing_by all_goals omega

/-- A319303(n): the node of the Collatz tree encoded by n. -/
def a (n : ℕ) : ℕ := walk n 1

theorem main : (∀ m : ℕ, 1 ≤ m → ∃ t, collatz^[t] m = 1) →
    ∀ m : ℕ, 1 ≤ m → ∃ n, a n = m := by
  sorry

end OMA.S_oeis_a319303
