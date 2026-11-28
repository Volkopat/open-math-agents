import OMAStatements.S_opg_strange_series
import Mathlib

-- Reduction opg-strange-series.R1 of The 3n+1 conjecture.
-- Credit: @marcusbuffett

/-!
# The 3n+1 conjecture from descent of every starting value

Classical reformulation (Terras 1976, Everett 1977; see Lagarias, *The 3x+1 problem and its
generalizations*, 1985): the conjecture holds as soon as every starting value `n > 1` has some
iterate below `n` (finite stopping time), by strong induction on `n`.

The descent is split by residue class modulo 32.

* `H1` (classical, elementary): descent for every `n > 1` outside the four classes
  `7, 15, 27, 31 (mod 32)`. Even `n` halve; `n = 4a + 1` reaches `3a + 1` in three steps;
  `n = 16a + 3` reaches `9a + 2` in six steps; `n = 32b + 11` and `n = 32b + 23` reach
  `27b + 10` and `27b + 20` in eight steps. This covers 28 of the 32 residue classes.
* `H2` (open core): descent for every `n > 1` in the classes `7, 15, 27, 31 (mod 32)`.

This is the standard residue-class (stopping time) reduction, not progress on the conjecture
itself: `H2` is still the full difficulty for one eighth of the integers.
-/

namespace OMA.R_opg_strange_series_R1

open OMA.S_opg_strange_series

/-- Descent outside the classes `7, 15, 27, 31 (mod 32)` (classical, elementary). -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n % 32 ≠ 7 → n % 32 ≠ 15 → n % 32 ≠ 27 → n % 32 ≠ 31 →
    ∃ k : ℕ, f^[k] n < n

/-- Descent inside the classes `7, 15, 27, 31 (mod 32)` (the open core). -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → (n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 27 ∨ n % 32 = 31) →
    ∃ k : ℕ, f^[k] n < n

lemma f_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ f n := by
  unfold f
  split_ifs <;> omega

lemma iterate_pos {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : 1 ≤ f^[k] n := by
  induction k generalizing n with
  | zero => simpa using hn
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (f_pos hn)

theorem main : H1 → H2 → type_of% @OMA.S_opg_strange_series.main := by
  intro h1 h2 n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge 1 n with hlt | hle
    · have hdesc : ∃ k : ℕ, f^[k] n < n := by
        by_cases hc : n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 27 ∨ n % 32 = 31
        · exact h2 n hlt hc
        · simp only [not_or] at hc
          exact h1 n hlt hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      obtain ⟨k, hk⟩ := hdesc
      obtain ⟨j, hj⟩ := ih (f^[k] n) hk (iterate_pos hn k)
      exact ⟨j + k, by rw [Function.iterate_add_apply, hj]⟩
    · exact ⟨0, by simp; omega⟩

end OMA.R_opg_strange_series_R1
