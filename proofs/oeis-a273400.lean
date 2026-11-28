import OMAStatements.S_oeis_a273400
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open OMA.S_oeis_a273400

namespace OMA.OeisA273400

private lemma p0 (n : ℕ) (hn : 1 ≤ n) : 2 * catalan n ≤ catalan (n + 1) := by
  rw [catalan_succ]
  have hne : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hval
    omega
  have hsub : ({0, Fin.last n} : Finset (Fin (n + 1))) ⊆ Finset.univ := Finset.subset_univ _
  have hle :=
    Finset.sum_le_sum_of_subset (f := fun i : Fin (n + 1) => catalan i * catalan (n - i)) hsub
  rw [Finset.sum_pair hne] at hle
  simp only [Fin.val_zero, Nat.sub_zero, catalan_zero, one_mul, Fin.val_last, Nat.sub_self,
    mul_one] at hle
  simpa [two_mul] using hle

private lemma p1 (n : ℕ) : catalan n ≤ catalan (n + 1) := by
  cases n with
  | zero => simp [catalan_zero, catalan_one]
  | succ m =>
    have h := p0 (m + 1) (Nat.succ_pos m)
    omega

private lemma p2 : Monotone catalan :=
  monotone_nat_of_le_succ p1

private lemma p3 (n : ℕ) (hn : 1 ≤ n) : 2 ^ (n - 1) ≤ catalan n := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp [catalan_one]
    | succ k =>
      have h1 : 2 ^ k ≤ catalan (k + 1) := ih (Nat.succ_pos k)
      have h2 : 2 * catalan (k + 1) ≤ catalan (k + 2) :=
        p0 (k + 1) (Nat.succ_pos k)
      calc
        2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
        _ ≤ 2 * catalan (k + 1) := Nat.mul_le_mul_left 2 h1
        _ ≤ catalan (k + 2) := h2

private lemma p4 (m : ℕ) (hm : 6 ≤ m) : 4 * m + 1 ≤ 2 ^ (m - 1) := by
  induction m with
  | zero => omega
  | succ k ih =>
    by_cases hk : 6 ≤ k
    · have h1 := ih hk
      have hsub : k = (k - 1) + 1 := by omega
      calc
        4 * (k + 1) + 1 ≤ 2 * (4 * k + 1) := by omega
        _ ≤ 2 * 2 ^ (k - 1) := Nat.mul_le_mul_left 2 h1
        _ = 2 ^ ((k - 1) + 1) := by rw [← pow_succ']
        _ = 2 ^ k := by rw [← hsub]
    · have hk5 : k = 5 := by omega
      subst hk5
      decide

private lemma p5 (n : ℕ) (hn : 4 ≤ n) : 10 ^ catalan n ≤ a n := by
  have hc4 : 10 ≤ catalan 4 := by
    have h3 : catalan 3 = 5 := catalan_three
    have h : 2 * catalan 3 ≤ catalan 4 := p0 3 (by decide)
    omega
  have hm : 10 ≤ catalan n := le_trans hc4 (p2 hn)
  set m := catalan n
  have hcm : 4 * m + 1 ≤ catalan m :=
    le_trans (p4 m (by omega)) (p3 m (by omega))
  have hccm : 2 ^ (4 * m) ≤ catalan (catalan m) := by
    have h1 : 2 ^ (catalan m - 1) ≤ catalan (catalan m) :=
      p3 (catalan m) (by omega)
    exact le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)) h1
  have h10 : 10 ^ m ≤ 2 ^ (4 * m) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by decide : 10 ≤ 2 ^ 4) m
  exact le_trans h10 hccm

end OMA.OeisA273400

theorem OMA.solution : type_of% @OMA.S_oeis_a273400.main := by
  have hfin : ({0, 1, 2, 3} : Set ℕ).Finite :=
    (((Set.finite_singleton 3).insert 2).insert 1).insert 0
  refine hfin.subset ?_
  intro n hn
  change (Nat.digits 10 (a n)).length < catalan n at hn
  by_contra hmem
  have hge4 : 4 ≤ n := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    omega
  have h1 : 10 ^ catalan n ≤ a n := OMA.OeisA273400.p5 n hge4
  have h2 : a n < 10 ^ (Nat.digits 10 (a n)).length :=
    Nat.lt_base_pow_length_digits (by decide : 1 < 10)
  have h3 : 10 ^ (Nat.digits 10 (a n)).length ≤ 10 ^ catalan n :=
    Nat.pow_le_pow_right (by decide : 0 < 10) (le_of_lt hn)
  omega
