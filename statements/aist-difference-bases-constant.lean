import Mathlib

/-!
# Asymptotic constant for difference bases of an interval

Source: https://arxiv.org/abs/2511.02864 (Problem 6.7, "Difference bases")
Credit: @eltociear (agent: Claude Code, model claude-opus-5-5)

The source: for a natural number `n`, `Δ(n)` is the size of the smallest set `B` of integers
such that every natural number from `1` to `n` is a difference of two elements of `B`.
Write `C(n) := Δ(n)² / n` and `C := inf_{n ≥ 1} C(n)`. Task: establish upper and lower bounds
on `C` that are as strong as possible. Rédei–Rényi showed that `C(n) → C`, so `C` is also the
limit. The source quotes the lower bound `2 + max_{0<φ<π} 2 sin φ / (φ + π) = 2.434…` (Leech)
and improves the upper bound `128² / 6166 = 2.6571…` to `2.6390`.

Modelling choices:
* The problem asks to "determine C" / find bounds as strong as possible, and the source gives no
  conjectured value. Statement files here cannot carry an answer placeholder, so `main` records
  the problem as the source sets it up: the convergence `C(n) → C` (Rédei–Rényi) together with
  the best bounds the source states. A proof of `main` therefore certifies the current state of
  knowledge; determining `C` itself is not expressible without a conjectured value.
* `B` ranges over finite sets of integers (`Finset ℤ`), with `{1, …, n} ⊆ B - B` (pointwise
  difference). Only finite sets matter, since the minimum is taken over sizes. `Δ(n)` is the
  `sInf` of the attainable sizes; the set is nonempty (`B = {0, …, n}` works).
* `C` is the infimum over `n ≥ 1` (the source writes `inf_{n ≥ 1}`), taken in `ℝ`.
* Upper bound: the source prints `2.6390`, but its construction (AlphaEvolve Repository of
  Problems, `experiments/difference_bases`: `L = {a·(89²+89+1) + b : a ∈ {0,1,4,6}, b ∈ B}`)
  has `|L| = 360` and covers exactly `1, …, 49109`, i.e. `C ≤ 360² / 49109 = 2.639027…`, which is
  slightly ABOVE the printed `2.6390`. The printed decimal is a truncation, so the statement uses
  the exact value `360² / 49109` that the construction proves.
* Lower bound: Leech's `2 + sup_{0<φ<π} 2 sin φ / (φ + π)`, written with `sSup` over the open
  interval (the maximum is attained, so `sSup` equals the source's `max`). The source mentions
  small later improvements (Bernshteyn–Tait) without numbers; they are not stated here.
-/

namespace OMA.S_aist_difference_bases_constant

open Filter Topology Set
open scoped Pointwise

/-- `Δ(n)`: the least size of a finite set `B ⊆ ℤ` with `{1, …, n} ⊆ B - B`. -/
noncomputable def Δ (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ B : Finset ℤ, B.card = k ∧ Finset.Icc (1 : ℤ) n ⊆ B - B}

/-- `C := inf_{n ≥ 1} Δ(n)² / n`. -/
noncomputable def C : ℝ :=
  ⨅ n : {n : ℕ // 1 ≤ n}, ((Δ n : ℝ) ^ 2 / (n : ℝ))

/-- Leech's lower bound `2 + max_{0<φ<π} 2 sin φ / (φ + π)`. -/
noncomputable def leechBound : ℝ :=
  2 + sSup ((fun φ : ℝ => 2 * Real.sin φ / (φ + Real.pi)) '' Ioo 0 Real.pi)

/-- The difference-bases constant: `Δ(n)²/n → C = inf_{n ≥ 1} Δ(n)²/n`, and
`2 + max_{0<φ<π} 2 sin φ / (φ + π) ≤ C ≤ 360² / 49109`. -/
theorem main :
    Tendsto (fun n : ℕ => (Δ n : ℝ) ^ 2 / (n : ℝ)) atTop (𝓝 C) ∧
      leechBound ≤ C ∧ C ≤ (360 : ℝ) ^ 2 / 49109 := by
  sorry

end OMA.S_aist_difference_bases_constant
