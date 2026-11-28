import OMAStatements.S_oeis_a000704
import Mathlib.Tactic

/-!
Proof of Mathar's recurrence for even involutions (OEIS A000704) by eliminating the
odd-involution sequence from the coupled recurrences for `a` and `b`.
-/

namespace OMA.A000704

open Finset OMA.S_oeis_a000704

private lemma succ_mul_choose (n k : ℕ) :
    (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [Nat.choose_eq_zero_of_lt (by omega : 1 < k + 2)]
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have h1 := ih k
      have h2 := ih (k + 1)
      have h3 : (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) :=
        Nat.choose_succ_succ n k
      have h4 : (n + 2).choose (k + 2) = (n + 1).choose (k + 1) + (n + 1).choose (k + 2) :=
        Nat.choose_succ_succ (n + 1) (k + 1)
      calc
        (n + 2) * (n + 1).choose (k + 1)
            = (n + 1) * (n.choose k + n.choose (k + 1)) + (n + 1).choose (k + 1) := by
              rw [← h3]; ring
        _ = (n + 1) * n.choose k + (n + 1) * n.choose (k + 1) + (n + 1).choose (k + 1) := by
              ring
        _ = (n + 1).choose (k + 1) * (k + 1) + (n + 1).choose (k + 2) * (k + 2) +
              (n + 1).choose (k + 1) := by rw [h1, h2]
        _ = ((n + 1).choose (k + 1) + (n + 1).choose (k + 2)) * (k + 2) := by ring
        _ = (n + 2).choose (k + 2) * (k + 2) := by rw [← h4]

private lemma matchings_zero (n : ℕ) : matchings n 0 = 1 := by
  have df0 : Nat.doubleFactorial 0 = 1 := rfl
  simp [matchings, df0]

private lemma matchings_eq_zero {n k : ℕ} (h : n < 2 * k) : matchings n k = 0 := by
  simp [matchings, Nat.choose_eq_zero_of_lt h]

private lemma matchings_rec (n k : ℕ) :
    matchings (n + 2) (k + 1) = matchings (n + 1) (k + 1) + (n + 1) * matchings n k := by
  cases k with
  | zero =>
    have df0 : Nat.doubleFactorial 0 = 1 := rfl
    have df1 : Nat.doubleFactorial 1 = 1 := rfl
    unfold matchings
    simp only [Nat.mul_zero, Nat.mul_one, Nat.choose_zero_right, df0, df1]
    rw [Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right]
    ring
  | succ m =>
    unfold matchings
    have h1 : 2 * (m + 1 + 1) = (2 * m + 3) + 1 := by omega
    have h2 : 2 * (m + 1) = 2 * m + 2 := by omega
    have h3 : 2 * (m + 1 + 1) - 1 = (2 * m + 1) + 2 := by omega
    have h4 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [h3, h4, h1, h2, Nat.choose_succ_succ (n + 1) (2 * m + 3),
      Nat.doubleFactorial_add_two (2 * m + 1)]
    have habs : (n + 1) * n.choose (2 * m + 2) = (n + 1).choose (2 * m + 3) * (2 * m + 3) :=
      succ_mul_choose n (2 * m + 2)
    have hrhs : (n + 1) * (n.choose (2 * m + 2) * (2 * m + 1).doubleFactorial) =
        ((n + 1) * n.choose (2 * m + 2)) * (2 * m + 1).doubleFactorial := by ring
    rw [hrhs, habs]
    ring

private lemma sum_range_eq_of_zero {f : ℕ → ℕ} {K M : ℕ} (hKM : K ≤ M)
    (hf : ∀ j, K ≤ j → f j = 0) : ∑ j ∈ range M, f j = ∑ j ∈ range K, f j := by
  induction M with
  | zero =>
    have hK : K = 0 := by omega
    subst hK
    rfl
  | succ M ih =>
    rcases eq_or_lt_of_le hKM with rfl | hlt
    · rfl
    · rw [Finset.sum_range_succ, hf M (by omega), add_zero]
      exact ih (by omega)

private def b (n : ℕ) : ℕ := ∑ j ∈ range (n + 1), matchings n (2 * j + 1)

private lemma a_eq_sum_ge {n M : ℕ} (hM : n / 4 + 1 ≤ M) :
    a n = ∑ j ∈ range M, matchings n (2 * j) := by
  unfold a
  exact (sum_range_eq_of_zero hM (fun j hj => matchings_eq_zero (by omega))).symm

private lemma b_eq_sum_ge {n M : ℕ} (hM : n + 1 ≤ M) :
    b n = ∑ j ∈ range M, matchings n (2 * j + 1) := by
  unfold b
  exact (sum_range_eq_of_zero hM (fun j hj => matchings_eq_zero (by omega))).symm

private lemma a_rec (n : ℕ) : a (n + 2) = a (n + 1) + (n + 1) * b n := by
  rw [a_eq_sum_ge (n := n + 2) (M := n + 3) (by omega)]
  rw [Finset.sum_range_succ', matchings_zero]
  have hterm : ∀ j : ℕ, matchings (n + 2) (2 * (j + 1)) =
      matchings (n + 1) (2 * (j + 1)) + (n + 1) * matchings n (2 * j + 1) := fun j => by
    have hk : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    rw [hk]
    exact matchings_rec n (2 * j + 1)
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have ha1 : (∑ x ∈ range (n + 2), matchings (n + 1) (2 * (x + 1))) + 1 = a (n + 1) := by
    have hm0 : matchings (n + 1) (2 * 0) = 1 := matchings_zero (n + 1)
    have hs := (Finset.sum_range_succ' (fun j => matchings (n + 1) (2 * j)) (n + 2)).symm
    have haeq : a (n + 1) = ∑ j ∈ range (n + 2 + 1), matchings (n + 1) (2 * j) :=
      a_eq_sum_ge (n := n + 1) (M := n + 2 + 1) (by omega)
    omega
  have hb0 : ∑ x ∈ range (n + 2), matchings n (2 * x + 1) = b n :=
    (b_eq_sum_ge (n := n) (M := n + 2) (by omega)).symm
  rw [hb0]
  omega

private lemma b_rec (n : ℕ) : b (n + 2) = b (n + 1) + (n + 1) * a n := by
  rw [b_eq_sum_ge (n := n + 2) (M := n + 3) (by omega)]
  have hterm : ∀ j : ℕ, matchings (n + 2) (2 * j + 1) =
      matchings (n + 1) (2 * j + 1) + (n + 1) * matchings n (2 * j) := fun j =>
    matchings_rec n (2 * j)
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    ← b_eq_sum_ge (n := n + 1) (M := n + 3) (by omega),
    ← a_eq_sum_ge (n := n) (M := n + 3) (by omega)]

private lemma main_aux (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℤ) - 3 * a (n - 1) + 3 * a (n - 2) - a (n - 3) -
      ((n : ℤ) - 1) * ((n : ℤ) - 3) * a (n - 4) +
        ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 5) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 5 := ⟨n - 5, by omega⟩
  have s1 : m + 5 - 1 = m + 4 := by omega
  have s2 : m + 5 - 2 = m + 3 := by omega
  have s3 : m + 5 - 3 = m + 2 := by omega
  have s4 : m + 5 - 4 = m + 1 := by omega
  have s5 : m + 5 - 5 = m := by omega
  simp only [s1, s2, s3, s4, s5]
  have ha5 : (a (m + 5) : ℤ) = (a (m + 4) : ℤ) + ((m : ℤ) + 4) * (b (m + 3) : ℤ) := by
    exact_mod_cast a_rec (m + 3)
  have ha4 : (a (m + 4) : ℤ) = (a (m + 3) : ℤ) + ((m : ℤ) + 3) * (b (m + 2) : ℤ) := by
    exact_mod_cast a_rec (m + 2)
  have ha3 : (a (m + 3) : ℤ) = (a (m + 2) : ℤ) + ((m : ℤ) + 2) * (b (m + 1) : ℤ) := by
    exact_mod_cast a_rec (m + 1)
  have hb3 : (b (m + 3) : ℤ) = (b (m + 2) : ℤ) + ((m : ℤ) + 2) * (a (m + 1) : ℤ) := by
    exact_mod_cast b_rec (m + 1)
  have hb2 : (b (m + 2) : ℤ) = (b (m + 1) : ℤ) + ((m : ℤ) + 1) * (a m : ℤ) := by
    exact_mod_cast b_rec m
  push_cast
  linear_combination ha5 - 2 * ha4 + ha3 + ((m : ℤ) + 4) * hb3 - ((m : ℤ) + 2) * hb2

end OMA.A000704

theorem OMA.solution : type_of% @OMA.S_oeis_a000704.main := OMA.A000704.main_aux
