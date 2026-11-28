import OMAStatements.S_oeis_a376354
import Mathlib.Tactic

/-!
Each step either resets the terminal digit to zero or increases it by one. The terminal digit is at most two, so every three consecutive positions contain a zero.
-/

namespace ZeroGaps
open OMA.S_oeis_a376354

private theorem tri_succ (k : ℕ) : triangular (k+1) = triangular k + (k+1) := by
  unfold triangular
  have e : (k+1)*(k+1+1) = k*(k+1)+2*(k+1) := by ring
  rw [e]
  omega

private theorem tri_mono : Monotone triangular := by
  apply monotone_nat_of_le_succ
  intro k
  rw [tri_succ]
  omega

private theorem above_index (k : ℕ) : k < triangular (k+1) := by
  rw [tri_succ]
  omega

private theorem cutoff (n : ℕ) : n < triangular (Nat.sqrt (2*n)+1+1) := by
  let s := Nat.sqrt (2*n)
  have hs : 2*n < (s+1)*(s+1) := Nat.lt_succ_sqrt _
  change n < (s+1+1)*(s+1+1+1)/2
  have : 2*n+2 ≤ (s+1+1)*(s+1+1+1) := by nlinarith
  omega

private theorem stable (n k : ℕ) (hk : 1 ≤ k) (hn : n < triangular (k+1))
    (l : ℕ) (hl : k ≤ l) : descend n l = descend n k := by
  induction l, hl using Nat.le_induction with
  | base => rfl
  | succ l hl ih =>
    have ht := lt_of_lt_of_le hn (tri_mono (Nat.succ_le_succ hl))
    cases l with
    | zero => omega
    | succ j => simpa only [descend, Nat.mod_eq_of_lt ht] using ih

private theorem digit_at (n k : ℕ) (hk : 1 ≤ k) (hn : n < triangular (k+1)) :
    digit n = descend n k := by
  let l := max k (Nat.sqrt (2*n)+1)
  exact (stable n _ (by omega) (cutoff n) l (le_max_right ..)).symm.trans
    (stable n k hk hn l (le_max_left ..))

private theorem descend_zero (k : ℕ) : descend 0 k = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 | 1 => rfl
    | j+2 => simpa only [descend, Nat.zero_mod] using ih (j+1) (by omega)

private theorem descend_step (n k : ℕ) :
    descend (n+1) k = 0 ∨ descend (n+1) k = descend n k + 1 := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    match k with
    | 0 | 1 => exact Or.inr rfl
    | j+2 =>
      let t := triangular (j+2)
      have ht : 0 < t := lt_trans (by omega : 0 < j+1) (above_index (j+1))
      have hm := Nat.mod_lt n ht
      change descend ((n+1)%t) (j+1) = 0 ∨
        descend ((n+1)%t) (j+1) = descend (n%t) (j+1) + 1
      rw [Nat.add_mod n 1 t]
      by_cases h : n%t+1 < t
      · have ht1 : 1 < t := by omega
        rw [Nat.mod_eq_of_lt ht1, Nat.mod_eq_of_lt h]
        exact ih (j+1) (by omega) _
      · have ht1 : 1 < t := lt_of_le_of_lt (by omega : 1 ≤ j+1) (above_index (j+1))
        rw [Nat.mod_eq_of_lt ht1, show n%t+1=t by omega, Nat.mod_self, descend_zero]
        exact Or.inl rfl

private theorem digit_step (n : ℕ) : digit (n+1) = 0 ∨ digit (n+1) = digit n+1 := by
  have hs := above_index (n+2)
  rw [digit_at (n+1) (n+2) (by omega) (by omega), digit_at n (n+2) (by omega) (by omega)]
  exact descend_step n (n+2)

private theorem small_digit {n : ℕ} (hn : n ≤ 16) : digit n = descend n 6 :=
  digit_at n 6 (by decide) (lt_of_le_of_lt hn (by decide))

private theorem descend_bound (n k : ℕ) : descend n (k+2) ≤ 2 := by
  induction k generalizing n with
  | zero =>
    change n%3 ≤ 2
    omega
  | succ k ih => exact ih _

private theorem digit_bound (n : ℕ) : digit n ≤ 2 := by
  have h := above_index (n+2)
  rw [digit_at n (n+2) (by omega) (by omega)]
  exact descend_bound _ _

private theorem zero_within_three (n : ℕ) :
    digit (n+1) = 0 ∨ digit (n+2) = 0 ∨ digit (n+3) = 0 := by
  have h₁ := digit_step n
  have h₂ := digit_step (n+1)
  have h₃ := digit_step (n+2)
  have bound := digit_bound (n+3)
  change digit (n+2) = 0 ∨ digit (n+2) = digit (n+1)+1 at h₂
  change digit (n+3) = 0 ∨ digit (n+3) = digit (n+2)+1 at h₃
  rcases h₁ with e₁|e₁
  · exact Or.inl e₁
  rcases h₂ with e₂|e₂
  · exact Or.inr (Or.inl e₂)
  rcases h₃ with e₃|e₃
  · exact Or.inr (Or.inr e₃)
  omega

end ZeroGaps

open OMA.S_oeis_a376354 ZeroGaps

theorem OMA.solution : type_of% @OMA.S_oeis_a376354.main := by
  ext g
  constructor
  · rintro ⟨a, b, ⟨_, ha, _, _, between⟩, rfl⟩
    have upper : b ≤ a+3 := by
      by_contra! h
      have ne (j : ℕ) (hj : 1 ≤ j ∧ j ≤ 3) : digit (a+j) ≠ 0 :=
        between _ (Finset.mem_Ioo.mpr (by omega))
      rcases zero_within_three a with h|h|h
      · exact ne 1 (by omega) h
      · exact ne 2 (by omega) h
      · exact ne 3 (by omega) h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl|rfl|rfl)
    · refine ⟨9, 10, ⟨by decide, by decide, by rw [small_digit (by decide)]; decide, by rw [small_digit (by decide)]; decide, ?_⟩, rfl⟩
      intro j hj
      rw [Finset.mem_Ioo] at hj
      omega
    · refine ⟨13, 15, ⟨by decide, by decide, by rw [small_digit (by decide)]; decide, by rw [small_digit (by decide)]; decide, ?_⟩, rfl⟩
      intro j hj
      rw [Finset.mem_Ioo] at hj
      obtain rfl : j = 14 := by omega
      rw [small_digit (by decide)]
      decide
    · refine ⟨3, 6, ⟨by decide, by decide, by rw [small_digit (by decide)]; decide, by rw [small_digit (by decide)]; decide, ?_⟩, rfl⟩
      intro j hj
      rw [Finset.mem_Ioo] at hj
      obtain ⟨lo, hi⟩ := hj
      interval_cases j <;> rw [small_digit (by decide)] <;> decide
