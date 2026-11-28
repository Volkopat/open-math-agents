import Mathlib

/-!
# Kurkov's dyadic prefix sum conjecture for OEIS A006014

A006014 starts at index 1; A379818 starts at index 0.
The conjecture follows the wording of the March 27, 2026 revision.

Sources:
* https://oeis.org/A006014
* https://oeis.org/A379818
* https://oeis.org/A025480
* https://oeis.org/A007814

The array-based definitions adapt the draft shared by @a17n.
-/

namespace OMA.S_oeis_a006014

open scoped BigOperators

def a025480 (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else a025480 (n / 2)
termination_by n
decreasing_by omega

/-- A006014 through index n, with an unused zero at index 0. -/
def firstTable : Nat -> Array Nat
  | 0 => #[0]
  | 1 => #[0, 1]
  | n + 2 =>
    let t := firstTable (n + 1)
    let conv := (Finset.range n).sum fun i =>
      t.getD (i + 1) 0 * t.getD (n - i) 0
    t.push ((n + 2) * t.getD (n + 1) 0 + conv)

/-- A379818 through index n. The exponent in the even case is A007814(k). -/
def secondTable : Nat -> Array Nat
  | 0 => #[1]
  | j + 1 =>
    let t := secondTable j
    let m := j + 1
    let k := m / 2
    if m % 2 = 1 then
      t.push (t.getD k 0)
    else
      let d := 2 ^ (k.factorization 2)
      t.push (t.getD k 0 + t.getD (k - d) 0 +
        t.getD (m - d) 0 + t.getD (a025480 (k - 1)) 0)

def a006014 (n : Nat) : Nat := (firstTable n).getD n 0

def a379818 (n : Nat) : Nat := (secondTable n).getD n 0

theorem main :
    forall n : Nat, 1 <= n ->
      a006014 n = (Finset.range (2 ^ (n - 1))).sum a379818 := by
  sorry

end OMA.S_oeis_a006014
