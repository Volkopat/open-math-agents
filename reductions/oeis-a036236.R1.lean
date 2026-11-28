import OMAStatements.S_oeis_a036236
import Mathlib

-- Reduction oeis-a036236.R1 of OEIS A036236 (Graham's question on 2^k mod k).
-- Credit: @marcusbuffett

/-!
# 2^k mod k = n: the powers of two, and the open rest

The conjecture: for every `n > 1` there are infinitely many `k` with `2 ^ k mod k = n`.

* `H1` (provable, elementary): every power of two `n = 2 ^ j`, `j ≥ 1`, is attained infinitely
  often. Write `j = 2 ^ v m` with `m` odd and take `k = j p` for a prime `p > 2 ^ j + j` with
  `p ≡ 1 (mod φ(m))` (Dirichlet). Then `2 ^ (jp) ≡ 2 ^ j` modulo `p` (Fermat), modulo `2 ^ v`
  (both sides vanish, `v ≤ j`) and modulo `m` (Euler, `φ(m) ∣ j (p - 1)`), hence modulo `jp`
  by the Chinese remainder theorem, and `2 ^ j < jp`.
* `H2` (open): every `n > 1` that is not a power of two is attained infinitely often.

This is a family of easy cases, not progress on the conjecture.
-/

namespace OMA.R_oeis_a036236_R1

/-- Powers of two: `2 ^ k mod k = 2 ^ j` for infinitely many `k`. -/
def H1 : Prop :=
  ∀ j : ℕ, 1 ≤ j → {k : ℕ | 0 < k ∧ 2 ^ k % k = 2 ^ j}.Infinite

/-- The open part: values `n > 1` that are not powers of two. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → (¬ ∃ j : ℕ, n = 2 ^ j) → {k : ℕ | 0 < k ∧ 2 ^ k % k = n}.Infinite

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a036236.main := by
  intro h1 h2 n hn
  by_cases hp : ∃ j : ℕ, n = 2 ^ j
  · obtain ⟨j, rfl⟩ := hp
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp at hn
      · exact h
    exact h1 j hj
  · exact h2 n hn hp

end OMA.R_oeis_a036236_R1
