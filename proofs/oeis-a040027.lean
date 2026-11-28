import OMAStatements.S_oeis_a040027

-- Problem: A040027: The Gould numbers.
-- Credit: @JeroHoyos (agent: claude-code, model claude-opus-5-5)
--
-- Idea: let c m = sum_{k<m} altFact k * S(m, k+1), so the target is a n = c (n+1).
-- Using S(m+1,k+1) = sum_i C(m,i) S(i,k) and sum_k (-1)^k k! S(i,k) = (-1)^i, one gets
-- c (m+1) = sum_{i<=m} C(m,i) c i + [m = 0], which is exactly the recurrence of a shifted by one.

namespace OMA.P_oeis_a040027

open OMA.S_oeis_a040027 Finset

theorem stir_binom : ∀ m k : ℕ, (Nat.stirlingSecond (m+1) (k+1) : ℤ) =
    ∑ i ∈ range (m+1), (m.choose i : ℤ) * (Nat.stirlingSecond i k : ℤ)
  | 0, k => by simp [Nat.stirlingSecond_succ_succ, Nat.stirlingSecond_zero_succ]
  | m+1, 0 => by
      rw [Finset.sum_range_succ']
      simp [Nat.stirlingSecond_succ_zero, Nat.stirlingSecond_one_right]
  | m+1, k+1 => by
      have h1 := stir_binom m (k+1)
      have h2 := stir_binom m k
      have h3 : ∑ i ∈ range (m+1), (m.choose (i+1) : ℤ) * (Nat.stirlingSecond (i+1) (k+1) : ℤ)
          = ∑ i ∈ range (m+1), (m.choose i : ℤ) * (Nat.stirlingSecond i (k+1) : ℤ) := by
        have := Finset.sum_range_succ' (fun i => (m.choose i : ℤ) * (Nat.stirlingSecond i (k+1) : ℤ)) (m+1)
        rw [Finset.sum_range_succ] at this
        simp [Nat.stirlingSecond_zero_succ] at this
        linarith
      have hL : (Nat.stirlingSecond (m+1+1) (k+1+1) : ℤ)
          = ((k:ℤ)+2) * Nat.stirlingSecond (m+1) (k+1+1) + Nat.stirlingSecond (m+1) (k+1) := by
        rw [Nat.stirlingSecond_succ_succ (m+1) (k+1)]; push_cast; ring
      have hP : ∀ i : ℕ, ((m+1).choose (i+1) : ℤ) * (Nat.stirlingSecond (i+1) (k+1) : ℤ)
          = (m.choose i : ℤ) * ((k:ℤ)+1) * (Nat.stirlingSecond i (k+1) : ℤ)
            + (m.choose i : ℤ) * (Nat.stirlingSecond i k : ℤ)
            + (m.choose (i+1) : ℤ) * (Nat.stirlingSecond (i+1) (k+1) : ℤ) := by
        intro i
        have hs' : (Nat.stirlingSecond (i+1) (k+1) : ℤ)
            = ((k:ℤ)+1) * Nat.stirlingSecond i (k+1) + Nat.stirlingSecond i k := by
          rw [Nat.stirlingSecond_succ_succ i k]; push_cast; ring
        rw [Nat.choose_succ_succ' m i]
        push_cast
        linear_combination (m.choose i : ℤ) * hs'
      rw [Finset.sum_range_succ', Finset.sum_congr rfl (fun i _ => hP i), Finset.sum_add_distrib,
        Finset.sum_add_distrib, h3, hL, h1, h2]
      simp only [Nat.stirlingSecond_zero_succ, Nat.cast_zero, mul_zero, add_zero]
      rw [show ∑ i ∈ range (m+1), (m.choose i : ℤ) * ((k:ℤ)+1) * (Nat.stirlingSecond i (k+1) : ℤ)
          = ((k:ℤ)+1) * ∑ i ∈ range (m+1), (m.choose i : ℤ) * (Nat.stirlingSecond i (k+1) : ℤ) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)]
      ring

theorem alt_stir : ∀ i : ℕ, ∑ k ∈ range (i+1), (-1 : ℤ) ^ k * (k.factorial : ℤ) * (Nat.stirlingSecond i k : ℤ) = (-1) ^ i
  | 0 => by simp
  | i+1 => by
      have ih := alt_stir i
      rw [Finset.sum_range_succ']
      have h3 : ∑ k ∈ range (i+1), (-1 : ℤ) ^ (k+1) * ((k+1).factorial : ℤ) * ((k:ℤ) + 1) * (Nat.stirlingSecond i (k+1) : ℤ)
          = ∑ k ∈ range (i+1), (-1 : ℤ) ^ k * (k.factorial : ℤ) * (k : ℤ) * (Nat.stirlingSecond i k : ℤ) := by
        have := Finset.sum_range_succ' (fun k => (-1 : ℤ) ^ k * (k.factorial : ℤ) * (k : ℤ) * (Nat.stirlingSecond i k : ℤ)) (i+1)
        rw [Finset.sum_range_succ, Nat.stirlingSecond_eq_zero_of_lt (by omega : i < i + 1)] at this
        push_cast at this
        simp at this
        linarith
      have h4 : ∀ k : ℕ, (-1 : ℤ) ^ (k+1) * ((k+1).factorial : ℤ) * (Nat.stirlingSecond (i+1) (k+1) : ℤ)
          = (-1 : ℤ) ^ (k+1) * ((k+1).factorial : ℤ) * ((k:ℤ) + 1) * (Nat.stirlingSecond i (k+1) : ℤ)
            - ((-1 : ℤ) ^ k * (k.factorial : ℤ) * (k : ℤ) * (Nat.stirlingSecond i k : ℤ)
               + (-1 : ℤ) ^ k * (k.factorial : ℤ) * (Nat.stirlingSecond i k : ℤ)) := by
        intro k
        rw [Nat.stirlingSecond_succ_succ i k, Nat.factorial_succ, pow_succ]
        push_cast
        ring
      rw [Finset.sum_congr rfl (fun k _ => h4 k), Finset.sum_sub_distrib, Finset.sum_add_distrib, h3, ih]
      simp [Nat.stirlingSecond_succ_zero]
      ring

theorem sum_shrink (f : ℕ → ℤ) (a b : ℕ) (h : a ≤ b) (hf : ∀ k, a ≤ k → f k = 0) :
    ∑ k ∈ range b, f k = ∑ k ∈ range a, f k := by
  refine (Finset.sum_subset (range_subset_range.mpr h) ?_).symm
  intro k _ hk
  simp only [mem_range, not_lt] at hk
  exact hf k hk

def c (m : ℕ) : ℤ := ∑ k ∈ range m, altFact k * (Nat.stirlingSecond m (k+1) : ℤ)

theorem telescope (i N : ℕ) :
    ∑ k ∈ range (N+1), altFact k * (Nat.stirlingSecond i k : ℤ)
      - ∑ k ∈ range N, altFact k * (Nat.stirlingSecond i (k+1) : ℤ)
      = ∑ k ∈ range (N+1), (-1 : ℤ) ^ k * (k.factorial : ℤ) * (Nat.stirlingSecond i k : ℤ) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (-1 : ℤ) ^ k * (k.factorial : ℤ) * _)]
  have : ∀ k : ℕ, altFact (k+1) = altFact k + (-1 : ℤ) ^ (k+1) * ((k+1).factorial : ℤ) := by
    intro k; unfold altFact; rw [Finset.sum_range_succ]
  simp only [this, add_mul, Finset.sum_add_distrib]
  simp [altFact]
  ring

theorem inner (m i : ℕ) (hi : i ≤ m) :
    ∑ k ∈ range (m+1), altFact k * (Nat.stirlingSecond i k : ℤ) = c i + (-1) ^ i := by
  have ht := telescope i m
  rw [sum_shrink (fun k => (-1 : ℤ) ^ k * (k.factorial : ℤ) * (Nat.stirlingSecond i k : ℤ)) (i+1) (m+1)
    (by omega) (fun k hk => by simp [Nat.stirlingSecond_eq_zero_of_lt (by omega : i < k)]), alt_stir,
    sum_shrink (fun k => altFact k * (Nat.stirlingSecond i (k+1) : ℤ)) i m hi
    (fun k hk => by simp [Nat.stirlingSecond_eq_zero_of_lt (by omega : i < k + 1)])] at ht
  unfold c
  linarith

theorem c_rec (m : ℕ) :
    c (m+1) = ∑ i ∈ range (m+1), (m.choose i : ℤ) * c i + if m = 0 then 1 else 0 := by
  have h : c (m+1) = ∑ i ∈ range (m+1), (m.choose i : ℤ) * (c i + (-1) ^ i) := by
    show ∑ k ∈ range (m+1), altFact k * (Nat.stirlingSecond (m+1) (k+1) : ℤ) = _
    simp only [stir_binom m, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← inner m i (by simp at hi; omega), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h, ← Int.alternating_sum_range_choose, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem c_zero : c 0 = 0 := by simp [c]

theorem c_one : c 1 = 1 := by simp [c, altFact, Nat.stirlingSecond_self]

theorem a_eq_c (n : ℕ) : a n = c (n+1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [a, c, altFact, Nat.stirlingSecond_self]
    | 1, _ => simp [a, c, altFact, Finset.sum_range_succ, Nat.stirlingSecond_self, Nat.stirlingSecond_one_right]
    | n+2, ih =>
      rw [a, c_rec, if_neg (by omega), Fin.sum_univ_eq_sum_range
        (fun j => if j = 0 then (0:ℤ) else ((n + 2).choose (j + 1) : ℤ) * a j) (n+2)]
      have e : ∀ j ∈ range (n+2), (if j = 0 then (0:ℤ) else ((n + 2).choose (j + 1) : ℤ) * a j)
          = (if j = 0 then (0:ℤ) else ((n + 2).choose (j + 1) : ℤ) * c (j+1)) := by
        intro j hj
        rw [ih j (by simp at hj; omega)]
      rw [Finset.sum_congr rfl e, Finset.sum_range_succ', Finset.sum_range_succ' _ (n+2),
        Finset.sum_range_succ' _ (n+1)]
      simp [c_zero, c_one]
      ring

end OMA.P_oeis_a040027

theorem OMA.solution : type_of% @OMA.S_oeis_a040027.main := by
  intro n
  exact OMA.P_oeis_a040027.a_eq_c n
