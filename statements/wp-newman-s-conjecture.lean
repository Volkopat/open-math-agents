import Mathlib

/-!
# Newman's conjecture

Source: https://en.wikipedia.org/wiki/Newman's_conjecture
Credit: @shc261392

Newman's conjecture (1960): for any integers `m` and `r` with `0 ≤ r ≤ m - 1`, the partition
function satisfies `p(n) ≡ r (mod m)` for infinitely many non-negative integers `n`.

Reading used here:
* `p(n)` is the number of partitions of `n`, `Fintype.card (Nat.Partition n)` (so `p 0 = 1`).
* `m` is a positive integer (the range `0 ≤ r ≤ m - 1` is empty otherwise); `r < m`.
-/

namespace OMA.S_wp_newman_s_conjecture

theorem main :
    ∀ m r : ℕ, 0 < m → r < m →
      {n : ℕ | Fintype.card (Nat.Partition n) % m = r}.Infinite := by
  sorry

end OMA.S_wp_newman_s_conjecture
