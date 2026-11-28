import OMAStatements.S_oeis_a317023
import Mathlib

/-
A317023: the alternating row sums of T(n,k) = C(n,k) - C(k-1, n-k) are 1, 1, -1, 0, 1, -1, ...
(the sequence with t(n+3) = -t(n+2) - t(n+1)).

Let f(m) be the sum over j <= m of (-1)^j C(j, m-j), a signed diagonal sum of Pascal's triangle.
- f_rec: f(m+2) = -f(m+1) - f(m), by shifting the index and Pascal's rule.
- rowsum: for n + 1 >= 1 the alternating sum of C(n+1, k) vanishes, and the second part of the
  row sum is -f(n) after shifting the index, so the row sum is f(n).
- f and the target sequence shifted by one have the same initial values 1, -1 and recurrence.
-/

namespace OMA.P317023

open Finset

lemma f_rec (m : ℕ) :
    ∑ j ∈ range (m + 1 + 1 + 1), (-1 : ℤ) ^ j * (Nat.choose j (m + 1 + 1 - j) : ℤ) =
      -(∑ j ∈ range (m + 1 + 1), (-1 : ℤ) ^ j * (Nat.choose j (m + 1 - j) : ℤ)) -
        ∑ j ∈ range (m + 1), (-1 : ℤ) ^ j * (Nat.choose j (m - j) : ℤ) := by
  rw [Finset.sum_range_succ' _ (m + 1 + 1), Finset.sum_range_succ _ (m + 1),
    Finset.sum_range_succ _ (m + 1)]
  have hmain : ∀ i ∈ range (m + 1),
      (-1 : ℤ) ^ (i + 1) * (Nat.choose (i + 1) (m + 1 + 1 - (i + 1)) : ℤ) =
        -((-1 : ℤ) ^ i * (Nat.choose i (m + 1 - i) : ℤ)) -
          (-1 : ℤ) ^ i * (Nat.choose i (m - i) : ℤ) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [show m + 1 + 1 - (i + 1) = (m - i) + 1 by omega, show m + 1 - i = (m - i) + 1 by omega,
      Nat.choose_succ_succ]
    push_cast
    ring
  rw [Finset.sum_congr rfl hmain, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  simp only [Nat.sub_self, Nat.choose_zero_right, Nat.sub_zero, Nat.choose_zero_succ,
    Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, add_zero]
  ring

lemma rowsum (n : ℕ) :
    ∑ k ∈ range (n + 1 + 1), (-1 : ℤ) ^ k *
        (((n + 1).choose k : ℤ) - (if k = 0 then 0 else ((k - 1).choose (n + 1 - k) : ℤ))) =
      ∑ j ∈ range (n + 1), (-1 : ℤ) ^ j * (Nat.choose j (n - j) : ℤ) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [Int.alternating_sum_range_choose_of_ne (Nat.succ_ne_zero n),
    Finset.sum_range_succ' _ (n + 1)]
  have hterm : ∀ j ∈ range (n + 1),
      (-1 : ℤ) ^ (j + 1) * (if j + 1 = 0 then 0 else ((j + 1 - 1).choose (n + 1 - (j + 1)) : ℤ)) =
        -((-1 : ℤ) ^ j * (Nat.choose j (n - j) : ℤ)) := by
    intro j _
    rw [if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, Nat.add_sub_add_right, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  simp

lemma main' (entry : ℕ → ℕ → ℤ)
    (he : ∀ n k, entry n k =
      (n.choose k : ℤ) - (if k = 0 then 0 else ((k - 1).choose (n - k) : ℤ)))
    (target : ℕ → ℤ) (t0 : target 0 = 1) (t1 : target 1 = 1) (t2 : target 2 = -1)
    (t3 : ∀ n, target (n + 3) = -target (n + 2) - target (n + 1)) :
    ∀ n : ℕ, ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * entry n k = target n := by
  have t3' : ∀ n, target (n + 1 + 1 + 1) = -target (n + 1 + 1) - target (n + 1) := t3
  have hf : ∀ n, target (n + 1) =
      ∑ j ∈ range (n + 1), (-1 : ℤ) ^ j * (Nat.choose j (n - j) : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | _ | m
      · simp [t1]
      · simp [t2, Finset.sum_range_succ]
      · rw [t3' m, ih (m + 1) (by omega), ih m (by omega)]
        exact (f_rec m).symm
  intro n
  rcases n with _ | n
  · simp [he, t0]
  · rw [hf n]
    simp only [he]
    exact rowsum n

end OMA.P317023

theorem OMA.solution : type_of% @OMA.S_oeis_a317023.main :=
  OMA.P317023.main' OMA.S_oeis_a317023.entry (fun _ _ => rfl) OMA.S_oeis_a317023.target rfl rfl rfl
    (fun _ => rfl)
