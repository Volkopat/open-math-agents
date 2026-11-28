import Mathlib

/-!
# A120860: the first column of the fixed-j dispersion array for Q = 8

Source: https://oeis.org/A120860
Credit: @avivorly

A120860 is the square array `D(g,h)` (`g, h >= 1`), the fixed-j dispersion for `Q = 8`. Its formula section
defines it: Define `f(n) = 3*n + 2*floor(n*2^(1/2))`. `D(1,1) = 1`; `D(1,2) = f(1)`;
`D(1,h) = 6*D(1,h-1) - D(1,h-2)` for `h >= 3`. For arbitrary `g >= 1`, once row `g` is defined, define
`D(g+1,1)` = least positive integer not in rows `1, 2, ..., g`; `D(g+1,2) = f(D(g+1,1))`; and
`D(g+1,h) = 6*D(g+1,h-1) - D(g+1,h-2)` for `h >= 3`.

A187967: `a(n) = floor((n+k)*r) - floor(n*r) - floor(k*r)`, where `r = sqrt(2)`, `k = 2` (offset 1).
A098021: positions of 0's in A187967. A187968: positions of 1 in A187967.

Conjecture (from Petros Hadjicostas, Jul 08 2020, in the entry): It appears that the first column of the
dispersion array D is A187968. That is, the first column of D consists of those positive integers m such that
A187967(m) = 1; i.e., those m for which floor(sqrt(2)*m + 2*sqrt(2)) - floor(sqrt(2)*m) - floor(2*sqrt(2)) = 1.
Indeed, Clark Kimberling, the author of this sequence and of sequence A187968, conjectured that A187968 is the
complement of A098021, and that A098021 is the complement of the first column of array D here.

Conventions:
- `f n = 3 * n + 2 * ⌊n * √2⌋₊` (the natural-number floor; `n * √2 ≥ 0`).
- `row x` is the row of `D` that starts at `x`: `row x 1 = x`, `row x 2 = f x`, and
  `row x (h + 3) = 6 * row x (h + 2) - row x (h + 1)`. Index `0` is unused (value `0`). The subtraction is in `ℕ`;
  it never truncates on these rows, which increase (`6 * D(g,h-1) ≥ D(g,h-2)`).
- `rowStart g = D(g,1)` is the least positive integer not in rows `1, ..., g-1`: the `sInf` of the set of `m > 0`
  with `D(r,h) ≠ m` for all `1 ≤ r < g` and `h ≥ 1`. For `g = 1` the condition is empty and gives `D(1,1) = 1`, as
  in the entry, so one rule covers every row. This set is never empty (the proof shows it), so `sInf` is its least
  element.
- `D g h = row (rowStart g) h`; only `g, h ≥ 1` are used. The first column of `D` is `{D g 1 : g ≥ 1}`.
- `A187967 m` is the integer `⌊√2 * m + 2 * √2⌋ - ⌊√2 * m⌋ - ⌊2 * √2⌋`, exactly as printed in the conjecture
  (the %N formula of A187967 with `n = m`, `k = 2`), for `m ≥ 1`.
- A187968 = `{m ≥ 1 : A187967 m = 1}` and A098021 = `{m ≥ 1 : A187967 m = 0}` (their %N definitions); a complement
  is taken inside the positive integers.
- `main` has three conjuncts: (1) Hadjicostas's claim, the problem: `m ≥ 1` is in the first column iff
  `A187967 m = 1`; (2) Kimberling: A187968 is the complement of A098021, i.e. `A187967 m = 1 ↔ A187967 m ≠ 0` for
  `m ≥ 1` (equivalently, `A187967` takes only the values `0` and `1`); (3) Kimberling: A098021 is the complement of
  the first column, i.e. `A187967 m = 0` iff `m` is not in the first column, for `m ≥ 1`.
-/

namespace OMA.S_oeis_a120860

/-- `f(n) = 3*n + 2*floor(n*2^(1/2))` (A120860 %F). -/
noncomputable def f (n : ℕ) : ℕ := 3 * n + 2 * ⌊(n : ℝ) * Real.sqrt 2⌋₊

/-- The row of `D` that starts at `x`: entry `1` is `x`, entry `2` is `f x`, and entry `h ≥ 3` is
`6 * (entry h-1) - (entry h-2)`. Index `0` is unused. -/
noncomputable def row (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => x
  | 2 => f x
  | h + 3 => 6 * row x (h + 2) - row x (h + 1)

/-- `rowStart g = D(g,1)`: the least positive integer not in rows `1, ..., g-1` of `D`. -/
noncomputable def rowStart (g : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ r : ℕ, 1 ≤ r → r < g → ∀ h : ℕ, 1 ≤ h → row (rowStart r) h ≠ m}
termination_by g
decreasing_by omega

/-- The array `D(g,h)` of A120860 (`g, h ≥ 1`). -/
noncomputable def D (g h : ℕ) : ℕ := row (rowStart g) h

/-- A187967 (with `r = √2`, `k = 2`), written exactly as in the conjecture:
`floor(sqrt(2)*m + 2*sqrt(2)) - floor(sqrt(2)*m) - floor(2*sqrt(2))`. -/
noncomputable def A187967 (m : ℕ) : ℤ :=
  ⌊Real.sqrt 2 * (m : ℝ) + 2 * Real.sqrt 2⌋ - ⌊Real.sqrt 2 * (m : ℝ)⌋ - ⌊2 * Real.sqrt 2⌋

theorem main :
    (∀ m : ℕ, 1 ≤ m → ((∃ g : ℕ, 1 ≤ g ∧ D g 1 = m) ↔ A187967 m = 1)) ∧
    (∀ m : ℕ, 1 ≤ m → (A187967 m = 1 ↔ ¬ A187967 m = 0)) ∧
    (∀ m : ℕ, 1 ≤ m → (A187967 m = 0 ↔ ¬ ∃ g : ℕ, 1 ≤ g ∧ D g 1 = m)) := by
  sorry

end OMA.S_oeis_a120860
