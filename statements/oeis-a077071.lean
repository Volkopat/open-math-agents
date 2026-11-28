import Mathlib

/-!
# A077071: Kurkov's balls-in-boxes conjecture

Source: https://oeis.org/A077071
Credit: @avivorly

A077071 (offset 0): Row sums of A077070.

A077070: Triangle read by rows: T(n,k) is the power of 2 in denominator of coefficients of Legendre
polynomials, where n >= 0 and 0 <= k <= n.

Conjecture (Mikhail Kurkov, Nov 24 2022, in A077071): given n balls, all of which are initially in the
first of n numbered boxes, a(n-1) is the number of steps of the following process required to move them
all to the last box. A step consists of first identifying j, the lowest numbered box which has at least
one ball. If it has only one ball then move it to box j+1; otherwise move half its balls rounded down to
box j+1 and (unless it's the first box) half its balls rounded down to box j-1.

Conventions:
- Row `m` of A077070 lists, for `0 ≤ k ≤ m`, the exponent of `2` in the denominator of the coefficient
  of `x^(2k)` in the Legendre polynomial `P_(2m)`, as in the entry's Maple, Mathematica and PARI
  programs (the odd coefficients of `P_(2m)` vanish). For example `P_2 = (3x^2 - 1)/2` gives the row
  `1, 1` and `P_4 = (35x^4 - 30x^2 + 3)/8` gives the row `3, 2, 3`.
- That coefficient is written by the classical closed form of the Legendre coefficients,
  `(-1)^(m-k) (2m+2k)! / (2^(2m) (m-k)! (m+k)! (2k)!)`, as a rational number `legendreCoeff m k`.
  (It is the case `N = 2m`, `j = m - k` of `P_N(x) = 2^(-N) Σ_j (-1)^j C(N,j) C(2N-2j,N) x^(N-2j)`.)
  `T m k` is `padicValNat 2` of its reduced denominator, and `a m` is the sum of row `m`.
- Boxes are numbered `0, 1, ..., n-1` (box `i` here is box `i+1` of the entry). A configuration is a
  function `c : ℕ → ℕ`, where `c i` is the number of balls in box `i`; the values at `i ≥ n` are never
  read by `step n` and are `0` along the process.
- `step n c` takes `j`, the lowest box among `0, ..., n-1` with at least one ball. If `j` is not the last
  box (`j + 1 < n`): with one ball, that ball moves to box `j+1`; with `b ≥ 2` balls and `j = 0`,
  `b / 2` (rounded down) balls move to box `1` and `b - b / 2` stay; with `b ≥ 2` balls and `j ≥ 1`,
  `b / 2` balls move to box `j+1`, `b / 2` balls move to box `j-1` (the box `i` with `i + 1 = j`), and
  `b - 2 * (b / 2)` stay. Hence a move only goes to a box `j+1 ≤ n-1` or `j-1 ≥ 0`, and no ball ever
  leaves the boxes `0, ..., n-1`.
- If the lowest nonempty box is the last box `n-1` (or no box holds a ball), then all balls are in the
  last box: the process is over, and `step n` returns the configuration unchanged.
- The start `start n` has `n` balls in box `0`; the target `target n` has `n` balls in box `n-1`.
  The number of steps required is the first time `t` with `(step n)^[t] (start n) = target n`:
  `main` says that the target is reached after `a (n-1)` steps and at no earlier time, for every
  `n ≥ 1` (for `n = 1` the start is already the target and `a 0 = 0`).
-/

namespace OMA.S_oeis_a077071

/-- The coefficient of `x^(2k)` in the Legendre polynomial `P_(2m)`, by the classical closed form
`(-1)^(m-k) (2m+2k)! / (2^(2m) (m-k)! (m+k)! (2k)!)`. -/
def legendreCoeff (m k : ℕ) : ℚ :=
  (-1) ^ (m - k) * ((2 * m + 2 * k).factorial : ℚ) /
    ((2 : ℚ) ^ (2 * m) * ((m - k).factorial : ℚ) * ((m + k).factorial : ℚ) *
      ((2 * k).factorial : ℚ))

/-- A077070: `T m k` is the exponent of `2` in the denominator of the coefficient of `x^(2k)` in
`P_(2m)`. -/
def T (m k : ℕ) : ℕ := padicValNat 2 (legendreCoeff m k).den

/-- A077071: the row sums of A077070. -/
def a (m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), T m k

/-- The start: all `n` balls in the first box (box `0`). -/
def start (n : ℕ) : ℕ → ℕ := fun i => if i = 0 then n else 0

/-- The target: all `n` balls in the last box (box `n - 1`). -/
def target (n : ℕ) : ℕ → ℕ := fun i => if i = n - 1 then n else 0

/-- One step of the process on the boxes `0, ..., n - 1`; `j` is the lowest nonempty box. -/
def step (n : ℕ) (c : ℕ → ℕ) : ℕ → ℕ :=
  if h : ∃ j, j < n ∧ c j ≠ 0 then
    let j := Nat.find h
    if j + 1 < n then
      if c j = 1 then
        fun i => if i = j then 0 else if i = j + 1 then c i + 1 else c i
      else if j = 0 then
        fun i => if i = 0 then c 0 - c 0 / 2 else if i = 1 then c i + c 0 / 2 else c i
      else
        fun i => if i = j then c j - 2 * (c j / 2)
          else if i = j + 1 ∨ i + 1 = j then c i + c j / 2 else c i
    else c
  else c

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (step n)^[a (n - 1)] (start n) = target n ∧
        ∀ t < a (n - 1), (step n)^[t] (start n) ≠ target n := by
  sorry

end OMA.S_oeis_a077071
