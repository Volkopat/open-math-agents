import Mathlib.Analysis.SpecificLimits.Basic

/-!
In A296768, pass k swaps the entry at k+1 with the entry indexed by the
sum of the old entries at k and k+1. The question concerns stabilization,
increase, omission of 2, and the limit sequence's growth.

Source: https://mathoverflow.net/questions/368162
Sequence: https://oeis.org/A296768
-/

namespace OMA.S_mo_368162

open Filter
open scoped Topology

def row : ℕ → ℕ → ℕ
  | 0 => id
  | k + 1 =>
    let b := row k
    let p := k + 2
    let q := b (k + 1) + b p
    fun i => if i = p then b q else if i = q then b p else b i

def a (n : ℕ) : ℕ := row (n - 1) n

theorem main :
    (∀ n : ℕ, 0 < n → ∀ k : ℕ, n - 1 ≤ k → row k n = a n) ∧
    StrictMono a ∧ (∀ n : ℕ, 0 < n → a n ≠ 2) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  sorry

end OMA.S_mo_368162
