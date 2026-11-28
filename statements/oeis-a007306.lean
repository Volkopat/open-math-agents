import Mathlib

/-!
# A007306: Denominators of Farey tree fractions

Source: https://oeis.org/A007306
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`1, 1, 2, 3, 3, 4, 5, 5, 4, 5, 7, 8, …` (offset `0`): denominators of the Farey tree (Stern–Brocot
subtree of `[0, 1]`), equivalently `a(0) = 1` and `a(n) = s(2n - 1)` for `n ≥ 1`, where `s` is
Stern's diatomic sequence A002487. Conjecture (OEIS): `a(n) = a(n-1) + b(n-1) - 2 (a(n-1) mod
b(n-1))` for `n > 1`, with `a(0) = a(1) = 1`, where `b(1) = 1` and `b(n) = a(n) - b(n-1)` for
`n > 1`.

## Encoding

* `stern` is Stern's diatomic sequence: `s(0) = 0`, `s(1) = 1`, `s(2m) = s(m)`,
  `s(2m+1) = s(m) + s(m+1)`.
* The pair `(a'(n), b(n))` of the conjectured recursion is computed in `ℤ` (`Int.emod`), starting
  from `(1, 1)` at `n = 1`; `main` says `a'(n) = a(n)` for all `n ≥ 1` (checked numerically for
  `n < 200`).
-/

namespace OMA.S_oeis_a007306

/-- Stern's diatomic sequence A002487. -/
def stern : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then stern ((n + 2) / 2) else stern ((n + 2) / 2) + stern ((n + 2) / 2 + 1)
decreasing_by all_goals omega

/-- A007306 (offset `0`). -/
def a (n : ℕ) : ℕ := if n = 0 then 1 else stern (2 * n - 1)

/-- `(a'(n+1), b(n+1))` of the conjectured recursion. -/
def ab : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | n + 1 =>
    let p := ab n
    let x := p.1 + p.2 - 2 * (p.1 % p.2)
    (x, x - p.2)

theorem main : ∀ n : ℕ, 1 ≤ n → (ab (n - 1)).1 = (a n : ℤ) := by
  sorry

end OMA.S_oeis_a007306
