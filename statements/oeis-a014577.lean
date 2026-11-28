import Mathlib

/-!
# A014577: The regular paper-folding sequence (or dragon curve sequence). Alphabet {1,0}.

Source: https://oeis.org/A014577
Credit: @luciusacarr

The entry records the conjecture (Gary W. Adamson, Jun 04 2021): map the Heighway dragon to unit
steps in the complex plane (Right = 1, Left = -1, Up = i, Down = -i), with the 0th iterate being the
unit segment from (0,0) to (-1,0). The conjectured table of step directions of the n-th iterate is

    0   -1
    1   -1, i
    2   -1, i, 1, i
    3   -1, i, 1, i, 1, -i, 1, i
    4   -1, i, 1, i, 1, -i, 1, i, 1, -i, -1, -i, 1, -i, 1, i

and it appears that row n+1 is obtained by bringing down row n as its left half, and as its right
half row n again but with the signs of the first half of row n changed (e.g. row 3 is
(-1, i, 1, i) followed by (1, -i, 1, i)).

Reading of the source:
* `a` is A014577 with offset 0, defined by the recurrence given in the entry (Ralf Stephan):
  `a(4n) = 1`, `a(4n+2) = 0`, `a(2n+1) = a(n)`. Its terms 1, 1, 0, 1, 1, 0, 0, 1, ... are the
  turns of the dragon curve (1 = right turn, 0 = left turn).
* The dragon curve, started with the step `-1`, has step directions `dir 0 = -1` and
  `dir (k+1) = dir k * (-i)` if `a k = 1` (turn right), `dir k * i` if `a k = 0` (turn left).
  The n-th iterate consists of the first `2^n` steps, so row n is the list
  `dir 0, ..., dir (2^n - 1)`. Directions are Gaussian integers (`i = ⟨0, 1⟩`).
* The claim: the rows 0 to 4 are as in the table above, and for every n ≥ 1, row (n+1) equals
  row n, followed by the first half (2^(n-1) entries) of row n with signs changed, followed by
  the second half of row n. (For n = 0 the row has length 1 and has no halves, so the rule is
  stated from n = 1 on, which matches the example in the entry.)
-/

namespace OMA.S_oeis_a014577

/-- The regular paper-folding sequence A014577 (offset 0):
`a(4n) = 1`, `a(4n+2) = 0`, `a(2n+1) = a(n)`. -/
def a : ℕ → ℕ
  | n =>
    if n % 4 = 0 then 1
    else if n % 4 = 2 then 0
    else a (n / 2)
decreasing_by omega

/-- The Gaussian integer `i`. -/
def I : GaussianInt := ⟨0, 1⟩

/-- Direction of the k-th unit step of the dragon curve: the first step is `-1`, and after
step k the curve turns right (multiply by `-i`) if `a k = 1`, left (multiply by `i`) if `a k = 0`. -/
def dir : ℕ → GaussianInt
  | 0 => -1
  | k + 1 => dir k * (if a k = 1 then -I else I)

/-- Row n of the table: the 2^n step directions of the n-th iterate. -/
def row (n : ℕ) : List GaussianInt := (List.range (2 ^ n)).map dir

theorem main :
    row 0 = [-1] ∧
    row 1 = [-1, I] ∧
    row 2 = [-1, I, 1, I] ∧
    row 3 = [-1, I, 1, I, 1, -I, 1, I] ∧
    row 4 = [-1, I, 1, I, 1, -I, 1, I, 1, -I, -1, -I, 1, -I, 1, I] ∧
    ∀ n, 1 ≤ n →
      row (n + 1) = row n ++ ((row n).take (2 ^ (n - 1))).map (fun z => -z) ++
        (row n).drop (2 ^ (n - 1)) := by
  sorry

end OMA.S_oeis_a014577
