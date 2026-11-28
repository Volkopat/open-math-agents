import Mathlib

/-!
# A109812

Source: https://oeis.org/A109812
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(1) = 1`; thereafter `a(n)` is the smallest positive integer not among the earlier terms such
that `a(n)` and `a(n-1)` have no common `1`-bits in binary. OEIS (David Broadhurst, 2022): it
appears that `a(n)/n` is bounded, and `n/a(n)` is unbounded.

## Encoding

* `terms k` is the list `[a(1), …, a(k+1)]`; the next term is the least `m ≥ 1` not in the list
  with `m &&& last = 0` (such `m` exist: large powers of two).
* `main` is the conjunction of the two observations: `a(n) ≤ C n` for some constant `C`, and
  `a(n) < n / C` happens for every `C > 0`.
-/

namespace OMA.S_oeis_a109812

/-- `[a(1), …, a(k+1)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [1]
  | k + 1 =>
    let L := terms k
    L ++ [sInf {m : ℕ | 1 ≤ m ∧ m ∉ L ∧ m &&& L.getLast! = 0}]

/-- `a n` (offset `1`). -/
noncomputable def a (n : ℕ) : ℕ := (terms (n - 1)).getD (n - 1) 0

theorem main :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → (a n : ℝ) ≤ C * n) ∧
      (∀ C : ℝ, 0 < C → ∃ n : ℕ, 1 ≤ n ∧ C * a n < n) := by
  sorry

end OMA.S_oeis_a109812
