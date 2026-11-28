import Mathlib

/-!
# A116485: Number of permutations in S_n that avoid the pattern 12453 (or equivalently, 31245).

Source: https://oeis.org/A116485
Credit: @bnb9001

a(n) counts the permutations of {1, ..., n} with no subsequence order-isomorphic to 12453
(offset 0: 1, 1, 2, 6, 24, 119, 694, ...). A158423(n) (offset 5: 1, 26, 459, ...) counts the
permutations of {1, ..., n} containing the relative rank sequence 23145 at any spacing, that is,
containing the pattern 23145.

Conjecture (Benedict W. J. Irwin, 2016): a(n) + A158423(n) = n!. Doron Zeilberger and Yonah
Biers-Ariel note that the conjecture is true (23145 and 31245 are inverse patterns).

Permutations of `Fin n` and of `Fin 5` are used, so values are 0-based: 12453 is ![0, 1, 3, 4, 2].
An order embedding `Fin 5 ↪o Fin n` is a choice of positions `i_1 < ... < i_5`.
-/

namespace OMA.S_oeis_a116485

open Equiv Finset

/-- `π` contains the pattern `σ`: some positions `f 0 < ... < f (k-1)` carry values of `π` in the
same relative order as `σ`. -/
def Contains {n k : ℕ} (π : Perm (Fin n)) (σ : Perm (Fin k)) : Prop :=
  ∃ f : Fin k ↪o Fin n, ∀ i j, π (f i) < π (f j) ↔ σ i < σ j

/-- The pattern 12453. -/
def pat12453 : Perm (Fin 5) where
  toFun := ![0, 1, 3, 4, 2]
  invFun := ![0, 1, 4, 2, 3]
  left_inv := by decide
  right_inv := by decide

/-- The pattern 23145. -/
def pat23145 : Perm (Fin 5) where
  toFun := ![1, 2, 0, 3, 4]
  invFun := ![2, 0, 1, 3, 4]
  left_inv := by decide
  right_inv := by decide

open Classical in
/-- A116485: the number of permutations of `Fin n` avoiding 12453. -/
noncomputable def a (n : ℕ) : ℕ :=
  (univ.filter fun π : Perm (Fin n) => ¬ Contains π pat12453).card

open Classical in
/-- A158423: the number of permutations of `Fin n` containing 23145. -/
noncomputable def b (n : ℕ) : ℕ :=
  (univ.filter fun π : Perm (Fin n) => Contains π pat23145).card

/-- Irwin's conjecture, proved: `a(n) + A158423(n) = n!` (for `n` in the range of A158423). -/
theorem main : ∀ n : ℕ, 5 ≤ n → a n + b n = n.factorial := by
  sorry

end OMA.S_oeis_a116485
