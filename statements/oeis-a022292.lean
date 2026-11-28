import Mathlib

/-!
# OEIS A022292: balanced prefixes of the Kolakoski sequence

Source: https://oeis.org/A022292
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the `n`-th `m ≥ 1` such that exactly half of the first `m` terms of the Kolakoski
sequence `1, 2, 2, 1, 1, 2, 1, 2, 2, 1, …` are `1`s (not known to be infinite). Conjecture (OEIS
entry): `a(n) ~ c n log n` for some constant `c ≤ 1`.

Conventions:
* The Kolakoski sequence `K : ℕ → ℕ` (from index `0`) is characterised by: run `i` (`i ≥ 0`)
  starts at `s(i)` with `s(0) = 0`, `s(i+1) = s(i) + K(i)`, and consists of the value `1` if `i`
  is even and `2` if `i` is odd. `main` quantifies over every `K` with this property (there is
  exactly one).
* `main` states that infinitely many such `m` exist and that, listing them as `Nat.nth`,
  `a(n) ~ c n log n` with some `0 < c ≤ 1` (`IsEquivalent`; `c > 0` is implicit in `~`).
-/

namespace OMA.S_oeis_a022292

open Filter Asymptotics

/-- Run starts `s(i)` of a sequence whose run lengths are given by `K`. -/
def runStart (K : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => runStart K i + K i

/-- `K` is the Kolakoski sequence. -/
def IsKolakoski (K : ℕ → ℕ) : Prop :=
  ∀ i j, runStart K i ≤ j → j < runStart K (i + 1) → K j = if i % 2 = 0 then 1 else 2

/-- Exactly half of the first `m` terms of `K` are `1`. -/
def Balanced (K : ℕ → ℕ) (m : ℕ) : Prop :=
  1 ≤ m ∧ 2 * ((Finset.range m).filter fun j => K j = 1).card = m

/-- Infinitely many balanced prefixes, with `a(n) ~ c n log n`, `0 < c ≤ 1`. -/
theorem main : ∀ K : ℕ → ℕ, IsKolakoski K →
    {m | Balanced K m}.Infinite ∧
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ IsEquivalent atTop
      (fun n : ℕ => (Nat.nth (Balanced K) n : ℝ)) (fun n => c * n * Real.log n) := by
  sorry

end OMA.S_oeis_a022292
