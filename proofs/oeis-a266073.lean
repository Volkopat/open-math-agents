import OMAStatements.S_oeis_a266073
import Mathlib

-- Credit: @oh-meh
-- Rule 3 moves the unique black cell one step right every two generations.
open OMA.S_oeis_a266073

private theorem rows (k : ℕ) :
    (∀ i : ℤ, black (2*k) i = decide (i = k)) ∧
    (∀ i : ℤ, black (2*k+1) i = decide (i ≠ k ∧ i ≠ k+1)) := by
  induction k with
  | zero =>
    constructor
    · intro i
      rfl
    · intro i
      apply Bool.eq_iff_iff.mpr
      simp [black]
      omega
  | succ k ih =>
    have he (i : ℤ) : black (2*(k+1)) i = decide (i = (k+1 : ℕ)) := by
      rw [show 2*(k+1) = (2*k+1)+1 by omega, black]
      simp only [ih.2]
      apply Bool.eq_iff_iff.mpr
      simp
      omega
    refine ⟨he, ?_⟩
    intro i
    rw [black]
    simp only [he]
    apply Bool.eq_iff_iff.mpr
    simp
    omega

private theorem counts (k : ℕ) :
    whiteCount (2*k) = 4*(k : ℤ) ∧ whiteCount (2*k+1) = 2 := by
  constructor
  · have h : ((Finset.range (2*(2*k)+1)).filter
          (fun j : ℕ => black (2*k) ((j : ℤ) - (2*k : ℕ)) = false)) =
          (Finset.range (2*(2*k)+1)).erase (3*k) := by
      ext j
      simp [(rows k).1, Finset.mem_erase]
      omega
    unfold whiteCount
    rw [h, Finset.card_erase_of_mem (by simp; omega), Finset.card_range]
    omega
  · have h : ((Finset.range (2*(2*k+1)+1)).filter
          (fun j : ℕ => black (2*k+1) ((j : ℤ) - (2*k+1 : ℕ)) = false)) =
          {3*k+1, 3*k+2} := by
      ext j
      simp [(rows k).2]
      omega
    unfold whiteCount
    rw [h, Finset.card_pair (by omega)]
    rfl

private theorem formula (n : ℕ) :
    whiteCount n = (-1 : ℤ)^n * n + n - (-1 : ℤ)^n + 1 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show n = 2*k by omega, (counts k).1, pow_mul]
    push_cast
    norm_num
    ring
  · rw [show n = 2*k+1 by omega, (counts k).2, pow_succ, pow_mul]
    push_cast
    norm_num

private theorem recurrence (n : ℕ) (hn : 3 < n) :
    whiteCount n = 2 * whiteCount (n-2) - whiteCount (n-4) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ n by omega)
  simp only [formula]
  rw [show 4+k-2 = 2+k by omega, show 4+k-4 = k by omega, pow_add, pow_add]
  push_cast
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a266073.main := by
  exact ⟨formula, recurrence⟩
