import Mathlib

/-!
# A329231: the most visits of one position in the grasshopper procedure

Source: https://oeis.org/A329231
Credit: @avivorly

A329231 (offset 1): The maximum number of times one reaches a single position during the grasshopper procedure.
The grasshopper procedure (the entry's comment, verbatim, shared with A329230): `n` positions are evenly spaced
around a circle, a grasshopper hops randomly to any position, after the `k`-th hop, the grasshopper looks clockwise
and counterclockwise `k` positions. If one of the positions has been visited less often then the other, it hops
there; if both positions have been visited an equal number of times, it hops `k` steps in the clockwise position.
A329230 is the number of steps it takes to reach all `n` positions; the entry's example for `n = 5` takes 10 steps
and ends with the visit counts `[2, 2, 2, 3, 1]`, so `A329231(5) = 3`.
Data: 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 3, 3, 3, 3, 1, 5, 2, ...

Conjectures (Peter Kagey, in the entry):
- C1: `a(n) = 1` if and only if `n = 3`, `n = 7`, or `n = 2^k` for some `k`.
- C2: The largest values of `n` for which `a(n) = 2, 3, 4, 5` respectively are `n = 18, 68, 381, 1972`.
- C3: If the second conjecture is true, then `2, 3, 4`, and `5` appear `2, 19, 87`, and `313` times respectively.
`main` is the conjunction `C1 ∧ C2 ∧ (C2 → C3)`. The entry's further conjecture (every integer greater than `1`
appears finitely often) is a separate claim and is not part of this statement.

Conventions:
- The positions are `0, 1, …, n - 1`; clockwise means increasing modulo `n`. Hop number `k` (`k = 1, 2, …`) has
  length `k`: from `cur` its clockwise target is `(cur + k) mod n` and its counterclockwise target is
  `(cur - k) mod n`, computed in `ℕ` as `(cur + (n - k mod n)) mod n`. It goes counterclockwise exactly when the
  counterclockwise target has strictly fewer visits, and clockwise otherwise (a tie, or both targets the same).
- The first, random, landing is on position `0`, and it counts as one visit. The rule commutes with rotations of
  the circle, so the visit counts of a run from another start are those of this run rotated, and `a(n)` does not
  depend on the start.
- `state n k` is (current position, visit counts) after `k` hops. The procedure stops at
  `stopHop n = sInf {k | AllVisited n k}`, the first `k` after which every position has been visited, so
  `A329230(n) = stopHop n + 1` counts the visits including the first landing; `a n` is the largest visit count at
  that moment. If the procedure never stopped, `sInf ∅ = 0` would give a junk value; the conjectures are about the
  entry's values, and this convention does not change any `a n` for which the procedure stops.
- Indices start at the entry's offset `1`: C1 is for `n ≥ 1` (`n = 1 = 2^0` is included), and C3 counts
  `{n | 1 ≤ n ∧ a n = v}`. In C2, `N` being the largest `n` with `a n = v` is `a N = v ∧ ∀ n > N, a n ≠ v`.
- C3 counts with `Set.ncard`; under the hypothesis C2 each of these sets lies in `[1, N]`, so it is finite and its
  `ncard` is the number of times `v` appears.
-/

namespace OMA.S_oeis_a329231

/-- One hop of length `j` on `n` positions from the state `s` = (current position, visit counts): clockwise target
`(cur + j) mod n`, counterclockwise target `(cur - j) mod n`; go counterclockwise if that target has strictly fewer
visits, clockwise otherwise; the new position gets one more visit. -/
def hop (n j : ℕ) (s : ℕ × (ℕ → ℕ)) : ℕ × (ℕ → ℕ) :=
  let cw := (s.1 + j) % n
  let ccw := (s.1 + (n - j % n)) % n
  let next := if s.2 ccw < s.2 cw then ccw else cw
  (next, Function.update s.2 next (s.2 next + 1))

/-- The state after `k` hops: the first landing is on position `0` (one visit), and hop number `k + 1` has length
`k + 1`. -/
def state (n : ℕ) : ℕ → ℕ × (ℕ → ℕ)
  | 0 => (0, fun p => if p = 0 then 1 else 0)
  | k + 1 => hop n (k + 1) (state n k)

/-- After `k` hops every one of the `n` positions has been visited. -/
def AllVisited (n k : ℕ) : Prop := ∀ p, p < n → 0 < (state n k).2 p

/-- The hop at which the procedure stops: the first `k` after which all positions have been visited
(`A329230(n) = stopHop n + 1`). -/
noncomputable def stopHop (n : ℕ) : ℕ := sInf {k | AllVisited n k}

/-- A329231: the maximum number of visits of a single position when the procedure stops. -/
noncomputable def a (n : ℕ) : ℕ := (Finset.range n).sup (state n (stopHop n)).2

/-- `N` is the largest index `n` with `a n = v`. -/
def LargestWith (v N : ℕ) : Prop := a N = v ∧ ∀ n, N < n → a n ≠ v

theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n = 3 ∨ n = 7 ∨ ∃ k : ℕ, n = 2 ^ k)) ∧
    (LargestWith 2 18 ∧ LargestWith 3 68 ∧ LargestWith 4 381 ∧ LargestWith 5 1972) ∧
    ((LargestWith 2 18 ∧ LargestWith 3 68 ∧ LargestWith 4 381 ∧ LargestWith 5 1972) →
      {n : ℕ | 1 ≤ n ∧ a n = 2}.ncard = 2 ∧ {n : ℕ | 1 ≤ n ∧ a n = 3}.ncard = 19 ∧
        {n : ℕ | 1 ≤ n ∧ a n = 4}.ncard = 87 ∧ {n : ℕ | 1 ≤ n ∧ a n = 5}.ncard = 313) := by
  sorry

end OMA.S_oeis_a329231
