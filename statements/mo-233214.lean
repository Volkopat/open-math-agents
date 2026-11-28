import Mathlib

/-!
# Repartition of 1's in the Chacon word

Source: https://mathoverflow.net/questions/233214 (CC BY-SA 4.0).

Let `B_0 = 0` and `B_{n+1} = B_n B_n 1 B_n` (the Chacon words); `B_{n+1}` extends `B_n`, giving an
infinite word `B_∞`, in which 1's have density `1/3`. The asker conjectures that for
`S = jℤ + k` (density `1/j`) or `S = {n | {nγ} ∈ [a, b)}` (density `b - a`, `0 ≤ a < b ≤ 1`, `γ ∈ (0,1)`
irrational),
`#{i | 1 ≤ i ≤ N, i ∈ S, B_∞(i) = 1} / N → d(S)/3` as `N → ∞`.

We state both cases of the conjecture.

Formalization notes:
* Letters are `Bool` (`true` is `1`); the words are any `B : ℕ → List Bool` with the recursion.
* `B_∞(i)` (1-indexed) is entry `i - 1` of `B i`: `B i` has `(3^(i+1) - 1)/2 ≥ i` letters and is a prefix
  of every later word.
* For `S = jℤ + k` it is enough to take `k : ℕ`; the condition is `i % j = k % j`.
* Checked on `B_11` (265720 letters): the ratio over `d(S)/3` is within 1% of `1` for `j = 2, 3, 5` and
  every `k`, and for `γ = (√5 - 1)/2`, `[a, b) = [0, 0.3)`.
-/

namespace OMA.S_mo_233214

/-- 1's of the Chacon word are equidistributed along arithmetic progressions and Bohr sets. -/
theorem main :
    ∀ B : ℕ → List Bool, B 0 = [false] → (∀ n, B (n + 1) = B n ++ B n ++ [true] ++ B n) →
    let b : ℕ → Bool := fun i => (B i).getD (i - 1) false
    (∀ j k : ℕ, 0 < j →
      Filter.Tendsto (fun N : ℕ =>
          (((Finset.Icc 1 N).filter (fun i : ℕ => i % j = k % j ∧ b i = true)).card : ℝ) / N)
        Filter.atTop (nhds (1 / (3 * j)))) ∧
    (∀ γ a c : ℝ, Irrational γ → 0 < γ → γ < 1 → 0 ≤ a → a < c → c ≤ 1 →
      Filter.Tendsto (fun N : ℕ =>
          (((Finset.Icc 1 N).filter (fun i : ℕ =>
            a ≤ Int.fract ((i : ℝ) * γ) ∧ Int.fract ((i : ℝ) * γ) < c ∧ b i = true)).card : ℝ) / N)
        Filter.atTop (nhds ((c - a) / 3))) := by
  sorry

end OMA.S_mo_233214
