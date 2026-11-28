import Mathlib

/-!
# A381707: smallest unimodal Collatz glides modulo `2^(n+2)`, and the Rule 641 automaton (A283507)

Source: https://oeis.org/A381707
Credit: @avivorly

A381707 (David Dewan): smallest initial value for unimodal Collatz `(3x+1)/2` glide sequence that begins with exactly
`n` increases. A unimodal Collatz glide sequence is successive rises `x -> (3x+1)/2` followed by successive falls
`x -> x/2` until dropping below its starting `x`. (The entry's example: for `n = 3`, `a(3) = 23` has trajectory
`23 -> 35 -> 53 -> 80 -> 40 -> 20`, three increases and then decreases to below the initial value.)

A283507 (Robert Price): decimal representation of the x-axis, from the origin to the right edge, of the `n`-th stage of
growth of the two-dimensional cellular automaton defined by Rule 641, based on the 5-celled von Neumann neighborhood;
initialized with a single black (ON) cell at stage zero.

Conjecture (V. Barbera, Apr 20 2026, in A381707): `a(n) mod 2^(n+2) = A283507(n+1)`.

Conventions:
- `T` is the shortcut Collatz map on `ℕ`: `T x = (3x+1)/2` for odd `x` (a rise) and `T x = x/2` for even `x` (a fall).
- `UnimodalGlide n x`: the first `n` steps from `x` are rises (`T^[j] x` odd for `j < n`); for some `m` the next `m`
  steps are falls (`T^[j] x` even for `n ≤ j < n + m`), `T^[n+m] x < x`, and `x ≤ T^[j] x` for every `j < n + m` (the
  glide has not ended earlier). Then `m ≥ 1` holds automatically (`T^[0] x = x` is not `< x`, and the value after
  `n ≥ 1` rises exceeds `x`), so step `n` is a fall: the glide begins with exactly `n` increases.
- `A381707 n` is the least such `x` (`sInf`). For every `n ≥ 1` the set is non-empty (the proof shows it), so the
  `sInf` is attained. The offset is 1 (`a(1) = 5`).
- Rule 641 is Wolfram's outer-totalistic code on the von Neumann neighbourhood: the new state of a cell is bit
  `2 * s + c` of `641 = 2^0 + 2^7 + 2^9`, where `c ∈ {0, 1}` is the cell's state and `s` the number of ON cells among
  its 4 neighbours (as in the entry's Mathematica program: kernel `{{0,2,0},{2,1,2},{0,2,0}}` and `rule[[10 - #]]` of
  `IntegerDigits[641, 2, 10]`).
- The plane is infinite (`ℤ × ℤ`) and every cell updates at every stage; stage 0 has only `(0, 0)` ON. Since bit 0 of
  641 is set, the OFF background turns ON at stage 1 (the entry's program uses a cyclic grid, where the same happens).
- The readout of stage `n` is the row `y = 0` from the origin `x = 0` to the right edge `x = n`, read as a binary
  number with the origin as the most significant digit: `A283507 n = Σ_{i ≤ n} [cell (i, 0) is ON] 2^(n - i)`
  (offset 0; stage 3 reads OFF, OFF, ON, ON, which is `0011 = 3`).
-/

namespace OMA.S_oeis_a381707

/-- The shortcut Collatz map: `(3x+1)/2` for odd `x`, `x/2` for even `x`. -/
def T (x : ℕ) : ℕ := if x % 2 = 1 then (3 * x + 1) / 2 else x / 2

/-- `x` starts a unimodal glide with exactly `n` increases: `n` rises, then falls until the value first drops
below `x`. -/
def UnimodalGlide (n x : ℕ) : Prop :=
  (∀ j < n, T^[j] x % 2 = 1) ∧
    ∃ m : ℕ, (∀ j, n ≤ j → j < n + m → T^[j] x % 2 = 0) ∧ T^[n + m] x < x ∧
      ∀ j < n + m, x ≤ T^[j] x

/-- A381707: the smallest initial value of a unimodal glide with exactly `n` increases. -/
noncomputable def A381707 (n : ℕ) : ℕ := sInf {x : ℕ | UnimodalGlide n x}

/-- The number of ON cells among the 4 von Neumann neighbours of `p` in the configuration `f`. -/
def onNeighbours (f : ℤ × ℤ → Bool) (p : ℤ × ℤ) : ℕ :=
  (f (p.1 + 1, p.2)).toNat + (f (p.1 - 1, p.2)).toNat + (f (p.1, p.2 + 1)).toNat +
    (f (p.1, p.2 - 1)).toNat

/-- Stage `k` of Rule 641 grown from a single ON cell at the origin: the new state of a cell is bit `2 * s + c` of
641, with `c` its state and `s` its number of ON neighbours. -/
def stage : ℕ → ℤ × ℤ → Bool
  | 0 => fun p => decide (p = (0, 0))
  | k + 1 => fun p => Nat.testBit 641 (2 * onNeighbours (stage k) p + (stage k p).toNat)

/-- A283507: stage `n` on the x-axis from the origin (most significant digit) to `x = n`, read in binary. -/
def A283507 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), if stage n ((i : ℤ), 0) then 2 ^ (n - i) else 0

/-- Barbera's conjecture: `A381707(n) mod 2^(n+2) = A283507(n+1)` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → A381707 n % 2 ^ (n + 2) = A283507 (n + 1) := by
  sorry

end OMA.S_oeis_a381707
