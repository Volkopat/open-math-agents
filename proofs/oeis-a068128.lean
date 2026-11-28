import OMAStatements.S_oeis_a068128
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
Shortening of the n = 0 disproof in PR #10565, originally
written with Antigravity (gemini-4-hydrogen-xhigh). Replaces the custom
strong induction with Mathlib's nonzero last-digit theorem.
Statement formalization: the original S_oeis_a068128 module.
Source conjecture: Amarnath Murthy,
OEIS A068128, https://oeis.org/A068128. No new mathematical result claimed.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068128.main) := by
  intro h
  apply h 0
  apply (Set.finite_singleton 0).subset
  intro t ht
  change t = 0
  by_contra hn
  apply Nat.getLast_digit_ne_zero 10 hn
  exact List.sum_eq_zero_iff.mp ht.2 _ (List.getLast_mem _)
