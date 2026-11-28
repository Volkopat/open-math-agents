import OMAStatements.S_oeis_a005329
import Mathlib

/-!
Let `d` be the binomial transform of `a(n) = ∏_{i=1}^n (2^i - 1)`. Pascal's rule and
`a(j+1) = (2^(j+1) - 1) a(j)` give `d(k+1) = ∑_j C(k,j) 2^(j+1) a(j)`; together with
`∑_k C(n,k) C(k,j) y^(n-k) = C(n,j) (1+y)^(n-j)` this yields
`∑_k C(n,k) d(k+1) = 2^(n+1) d(n)`. Strong induction on the defining recurrence of A075271
then gives `2 b(n) = d(n+1)`, so A075272 is `d`, and binomial inversion (the same identity at
`y = -1`) recovers `a`.
-/

namespace A005329Proof

open OMA.S_oeis_a005329

open Finset

lemma choose_sum (n j : ℕ) (y : ℤ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℤ) * (k.choose j : ℤ) * y ^ (n - k) =
      (n.choose j : ℤ) * (1 + y) ^ (n - j) := by
  by_cases hj : n < j
  · rw [Nat.choose_eq_zero_of_lt hj]
    simp only [Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro k hk
    rw [mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega : k < j)]; simp
  · push Not at hj
    rw [show n + 1 = j + (n - j + 1) by omega, Finset.sum_range_add]
    have h0 : ∑ k ∈ range j, (n.choose k : ℤ) * (k.choose j : ℤ) * y ^ (n - k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [mem_range] at hk
      rw [Nat.choose_eq_zero_of_lt hk]; simp
    rw [h0, zero_add, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    have hc := Nat.choose_mul (n := n) (k := j + i) (s := j) (by omega)
    rw [show j + i - j = i by omega] at hc
    have hc' : ((n.choose (j + i) : ℕ) : ℤ) * ((j + i).choose j : ℕ) =
        (n.choose j : ℕ) * ((n - j).choose i : ℕ) := by exact_mod_cast hc
    rw [hc', one_pow, one_mul, show n - (j + i) = n - j - i by omega]
    ring

def d (n : ℕ) : ℤ := ∑ j ∈ range (n + 1), (n.choose j : ℤ) * a j

lemma a_succ (j : ℕ) : a (j + 1) = (2 ^ (j + 1) - 1) * a j := by
  unfold a
  rw [Finset.prod_Icc_succ_top (by omega)]; ring

lemma extend (k n : ℕ) (hk : k ≤ n) (g : ℕ → ℤ) :
    ∑ j ∈ range (k + 1), (k.choose j : ℤ) * g j = ∑ j ∈ range (n + 1), (k.choose j : ℤ) * g j := by
  apply Finset.sum_subset
  · intro x hx; simp at hx ⊢; omega
  · intro x _ hx
    simp at hx
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma d_succ (k : ℕ) : d (k + 1) = ∑ j ∈ range (k + 1), (k.choose j : ℤ) * (2 ^ (j + 1) * a j) := by
  unfold d
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib, Nat.choose_zero_right]
  have h1 : ∑ i ∈ range (k + 1), (k.choose (i + 1) : ℤ) * a (i + 1) + (1 : ℕ) * a 0 =
      ∑ i ∈ range (k + 1), (k.choose i : ℤ) * a i := by
    rw [Finset.sum_range_succ' (fun i => (k.choose i : ℤ) * a i)]
    simp only [Nat.choose_zero_right, Nat.cast_one]
    rw [Finset.sum_range_succ (fun i => (k.choose (i + 1) : ℤ) * a (i + 1)), Nat.choose_succ_self]
    simp
  have h2 : ∑ i ∈ range (k + 1), (k.choose i : ℤ) * a (i + 1) =
      ∑ i ∈ range (k + 1), (k.choose i : ℤ) * ((2 ^ (i + 1) - 1) * a i) := by
    apply Finset.sum_congr rfl; intro i _; rw [a_succ]
  rw [add_assoc, h1, h2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

lemma star (n : ℕ) : ∑ k ∈ range (n + 1), (n.choose k : ℤ) * d (k + 1) = 2 ^ (n + 1) * d n := by
  have : ∀ k ∈ range (n + 1), (n.choose k : ℤ) * d (k + 1) =
      ∑ j ∈ range (n + 1), (n.choose k : ℤ) * (k.choose j : ℤ) * (2 ^ (j + 1) * a j) := by
    intro k hk
    rw [mem_range] at hk
    rw [d_succ, extend k n (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  unfold d
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have hs := choose_sum n j 1
  simp only [one_pow, mul_one] at hs
  rw [← Finset.sum_mul, hs]
  have : (2 : ℤ) ^ (n + 1) = 2 ^ (j + 1) * 2 ^ (n - j) := by
    rw [← pow_add]; congr 1; omega
  rw [this]; norm_num; ring

lemma b_succ (n : ℕ) :
    b (n + 1) = 2 ^ (n + 2) * b n - ∑ k ∈ range (n + 1), ((n + 1).choose k : ℤ) * b k := by
  rw [b, Fin.sum_univ_eq_sum_range (fun k => ((n + 1).choose k : ℤ) * b k)]

lemma two_b (n : ℕ) : 2 * b n = d (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [b, d, a, Finset.sum_range_succ]
    · rw [b_succ]
      have hs := star (n + 1)
      rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at hs
      have hsum : ∑ k ∈ range (n + 1), ((n + 1).choose k : ℤ) * (2 * b k) =
          ∑ k ∈ range (n + 1), ((n + 1).choose k : ℤ) * d (k + 1) := by
        apply Finset.sum_congr rfl; intro k hk; rw [mem_range] at hk; rw [ih k (by omega)]
      have hb := ih n (by omega)
      have hS : 2 * ∑ k ∈ range (n + 1), ((n + 1).choose k : ℤ) * b k =
          ∑ k ∈ range (n + 1), ((n + 1).choose k : ℤ) * d (k + 1) := by
        rw [Finset.mul_sum, ← hsum]
        apply Finset.sum_congr rfl; intro k _; ring
      linear_combination (2 ^ (n + 2) : ℤ) * hb - hS - hs

lemma c_eq_d (k : ℕ) : c k = d k := by
  rcases k with _ | k
  · simp [c, d, a]
  · rw [c, two_b]

theorem solved : ∀ n : ℕ,
    a n = ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * c k := by
  intro n
  have : ∀ k ∈ range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * c k =
      ∑ j ∈ range (n + 1), (n.choose k : ℤ) * (k.choose j : ℤ) * (-1) ^ (n - k) * a j := by
    intro k hk
    rw [mem_range] at hk
    rw [c_eq_d, d, extend k n (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  have h2 : ∀ j ∈ range (n + 1), ∑ k ∈ range (n + 1), (n.choose k : ℤ) * (k.choose j : ℤ) *
      (-1) ^ (n - k) * a j = (n.choose j : ℤ) * 0 ^ (n - j) * a j := by
    intro j _
    rw [← Finset.sum_mul, choose_sum n j (-1)]; norm_num
  rw [Finset.sum_congr rfl h2, Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp
  · intro j hj
    rw [mem_range] at hj
    rw [zero_pow (by omega)]; simp
end A005329Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a005329.main := A005329Proof.solved
