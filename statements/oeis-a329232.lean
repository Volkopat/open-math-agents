import Mathlib

/-!
# A329232: counterclockwise steps in the grasshopper procedure

Source: https://oeis.org/A329232
Credit: @avivorly

A329232 (offset 1): The number of counterclockwise steps during the grasshopper procedure.
The grasshopper procedure (the entry's comment, verbatim, shared with A329230 and A329231): `n` positions are evenly
spaced around a circle, a grasshopper hops randomly to any position, after the `k`-th hop, the grasshopper looks
clockwise and counterclockwise `k` positions. If one of the positions has been visited less often then the other, it
hops there; if both positions have been visited an equal number of times, it hops `k` steps in the clockwise position.
The procedure runs until all `n` positions have been reached (A329230 is the number of steps that takes).
Data: 0, 0, 1, 0, 2, 3, 3, 0, 9, 6, 4, 5, 4, 5, 7, 0, 18, 10, ...

Conjecture (in the entry): `a(n) = 0` if and only if `n = 2^k`.

Conventions:
- `hop`, `state` and `AllVisited` are those of the A329231 statement. The positions are `0, 1, …, n - 1`; clockwise
  means increasing modulo `n`. Hop number `k` (`k = 1, 2, …`) has length `k`: from `cur` its clockwise target is
  `(cur + k) mod n` and its counterclockwise target is `(cur - k) mod n`, computed in `ℕ` as
  `(cur + (n - k mod n)) mod n`. It goes counterclockwise exactly when the counterclockwise target has strictly fewer
  visits, and clockwise otherwise (a tie, or both targets the same).
- The first, random, landing is on position `0`, and it counts as one visit. The rule commutes with rotations of the
  circle, so a run from another start is this run rotated, with the same hop directions, and `a(n)` does not depend on
  the start.
- `state n k` is (current position, visit counts) after `k` hops; `CCW n k` says that hop number `k + 1`, made from
  `state n k`, goes counterclockwise (the branch of `hop` that moves counterclockwise).
- Which hops `a(n)` counts, from the data: let `K` be the first `k` with `AllVisited n k` (every position has been
  reached after `K` hops; A329230(n) = `K + 1` counts the first landing as a step). The entry's values count the
  counterclockwise hops among the first A329230(n) hops, that is, among hops `1, …, K + 1`: the hop made from the
  state in which every position has just been reached is counted too. A computable twin of this count reproduces all
  2048 terms of the entry's b-file; stopping one hop earlier gives values smaller by `1` at 692 of them (first at
  `n = 34`: `14` instead of `15`).
- Since `AllVisited` is monotone in `k` (counts never decrease), hops `1, …, K + 1` are exactly the hops `j + 1`
  such that `¬ AllVisited n i` for every `i < j`. It is not known that the procedure stops for every `n`, so
  `a(n) = 0` is stated without a stopping time: every such hop goes clockwise,
  `∀ j, (∀ i, i < j → ¬ AllVisited n i) → ¬ CCW n j`. When the procedure stops this is literally `a(n) = 0`; no
  junk value enters.
- Indices start at the entry's offset `1`, so the conjecture is for `n ≥ 1` (`n = 1 = 2^0` is included).
-/

namespace OMA.S_oeis_a329232

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

/-- Hop number `k + 1`, made from the state after `k` hops, goes counterclockwise: its counterclockwise target has
strictly fewer visits than its clockwise target. -/
def CCW (n k : ℕ) : Prop :=
  (state n k).2 (((state n k).1 + (n - (k + 1) % n)) % n) < (state n k).2 (((state n k).1 + (k + 1)) % n)

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ((∀ j : ℕ, (∀ i : ℕ, i < j → ¬ AllVisited n i) → ¬ CCW n j) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a329232
