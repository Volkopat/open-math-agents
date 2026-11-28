import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Basic

/-!
# The odd positions of the diagonal-sum square spiral

Sources: Alec Jones and Peter Kagey, OEIS A334745, https://oeis.org/A334745;
Kival Ngaokrajang, OEIS A247976, https://oeis.org/A247976, including
G. C. Greubel's row recurrence. OEIS Foundation, CC BY-SA 4.0.
Credit: @jatin6

Diagonal moves preserve checkerboard color, so the second seed at index 2
never contributes to an odd position. On the color containing the origin use
integer coordinates u=(x+y)/2, v=(x-y)/2. The square ring of radius r is
|u|+|v|=r. Its four diagonal neighbors become the ordinary four neighbors.
Each is on the preceding or following ring, so all earlier neighbors are on
the preceding ring. Reading the odd positions clockwise or counterclockwise
gives four successive quarter-turns of an edge, excluding its starting corner.

The target compares prefixes of the two flattened sequences. Through square
ring r there are 1+2*r*(r+1) odd positions. The first 2*r+1 triangular rows
contain at least this many entries, and these prefix lengths are unbounded.
-/

namespace OMA.S_oeis_a334745

def wave : ℕ → ℤ → ℤ → ℕ
  | 0, u, v => if u = 0 ∧ v = 0 then 1 else 0
  | r+1, u, v =>
    if u.natAbs + v.natAbs = r+1 then
      wave r (u-1) v + wave r (u+1) v + wave r u (v-1) + wave r u (v+1)
    else 0

def edge (r : ℕ) (q : ℤ → ℤ → ℕ) : List ℕ :=
  (List.range r).map fun j => q (j+1 : ℕ) (r-(j+1) : ℕ)

def spiral : ℕ → List ℕ
  | 0 => [1]
  | r+1 =>
    let f := wave (r+1)
    spiral r ++ edge (r+1) f ++ edge (r+1) (fun u v => f v (-u)) ++
      edge (r+1) (fun u v => f (-u) (-v)) ++ edge (r+1) (fun u v => f (-v) u)

-- The second half of an even source row copies the first half. Compute the
-- copied entry directly from the preceding row, so recursion is on rows.
def table : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, j =>
    let m := n+1
    if j = 0 then 1
    else if j+1 = m then (m+1)/2
    else if m % 2 = 1 then
      if j ≤ m/2 then table n j else table n (j-1) + table n j
    else
      let k := if j < m/2 then j else j-m/2
      if k = 0 then 1 else table n (k-1) + table n k

def rows : ℕ → List ℕ
  | 0 => []
  | n+1 => rows n ++ (List.range (n+1)).map (table (n+1))

theorem main : ∀ r : ℕ, (spiral r).IsPrefix (rows (2*r+1)) := by
  sorry

end OMA.S_oeis_a334745
