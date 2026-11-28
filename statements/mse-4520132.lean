import Mathlib

/-!
# Every positive integer as $\lfloor \sqrt{\cdots\sqrt{4!\cdots!}} \rfloor$?

Source: https://math.stackexchange.com/questions/4520132
Credit: @SulkBash

## The problem (as the source states it)

A conjecture recalled from a puzzle column about expressing integers with fours: every positive
integer can be expressed as
$$\left\lfloor \underbrace{\sqrt{\cdots\sqrt{\,4\overbrace{!\cdots!}^{n\text{ factorials}}}}}_{m\text{ square roots}} \right\rfloor$$
for some non-negative (or was it positive?) integers $m$ and $n$, possibly in more than one
way. For instance, $5 = \lfloor\sqrt{\sqrt{\sqrt{\sqrt{\sqrt{4!!}}}}}\rfloor$.

The source asks whether any progress has been made on this conjecture. It is open.

## Formalization notes

* **Factorials.** `n` factorials applied to `4` is `Nat.factorial^[n] 4`, the sequence
  `4, 4! = 24, (4!)! = 24!, …`. The source's `4!!` is the iterated factorial `(4!)!`, not the
  double factorial: its example $5 = \lfloor (24!)^{1/32} \rfloor$ only works that way, since
  $\lfloor 8^{1/32} \rfloor = 1$.
* **Square roots and floor.** `m` square roots are `Real.sqrt^[m]`, applied to the factorial
  value cast to `ℝ`. The floor is taken once, outside all the roots, as in the source. It is
  `⌊·⌋₊` (`Nat.floor`), which equals the usual floor because the argument is nonnegative.
* **Range of `m` and `n`.** The source hesitates between non-negative and positive. We take
  non-negative, the reading the source states first.
  - The positive reading is a strictly stronger claim: it forbids `m = 0` and `n = 0`.
  - So a proof of the positive version also proves `main`, and a disproof of `main` also refutes
    the positive version.
* **Range of the target.** `k` ranges over the positive integers.
-/

namespace OMA.S_mse_4520132

/-- Every positive integer is the floor of some number of iterated square roots of some number of
iterated factorials of `4`. -/
theorem main :
    ∀ k : ℕ, 0 < k → ∃ m n : ℕ, ⌊Real.sqrt^[m] ((Nat.factorial^[n] 4 : ℕ) : ℝ)⌋₊ = k := by
  sorry

end OMA.S_mse_4520132
