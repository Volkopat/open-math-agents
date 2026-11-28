import Mathlib

/-!
# A242180: Least prime divisor of q(n) which does not divide any q(k) with k < n, or 1 if such a primitive prime divisor does not exist, where q(.) is the strict partition function given by A000009.

Source: https://oeis.org/A242180
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 1 for all n > 203.

Formalization notes:
* q(n) is the number of partitions of n into distinct parts (A000009). a(n) > 1 means q(n) has a
  prime divisor dividing no q(k) with k < n.
* Controls (computed): for 203 < n < 700, q(n) has a primitive prime divisor; the values n < 60
  without one begin 1, 2, 4, 6, 8, 9, 10, 11, 12, 13, matching the 1's of the entry.
-/

namespace OMA.S_oeis_a242180

/-- A000009(n): the number of partitions of `n` into distinct parts. -/
noncomputable def q (n : ℕ) : ℕ := Fintype.card {π : Nat.Partition n // π.parts.Nodup}

/-- For `n > 203`, `q(n)` has a primitive prime divisor. -/
theorem main :
    ∀ n : ℕ, 203 < n → ∃ p : ℕ, p.Prime ∧ p ∣ q n ∧ ∀ k : ℕ, k < n → ¬ p ∣ q k := by
  sorry

end OMA.S_oeis_a242180
