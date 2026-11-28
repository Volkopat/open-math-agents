import OMAStatements.S_oeis_a324608
import Mathlib

open OMA.S_oeis_a324608

private theorem ones_double (n : ℕ) : ones (2*n) = ones n := by
  by_cases hn : n = 0
  · simp [hn, ones]
  · unfold ones
    rw [show 2*n = 0+2*n by omega, Nat.digits_add 2 (by decide) 0 n (by decide) (Or.inr hn)]
    simp

private theorem ones_double_succ (n : ℕ) : ones (2*n+1) = ones n + 1 := by
  unfold ones
  rw [show 2*n+1 = 1+2*n by omega, Nat.digits_add 2 (by decide) 1 n (by decide) (Or.inl (by decide))]
  simp

private theorem ones_succ_le (n : ℕ) : ones (n+1) ≤ ones n+1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hcases : n = 2*(n/2) ∨ n = 2*(n/2)+1 := by omega
    rcases hcases with he | ho
    · calc
        ones (n+1) = ones (2*(n/2)+1) := congrArg (fun x => ones (x+1)) he
        _ = ones (n/2)+1 := ones_double_succ _
        _ ≤ ones n+1 := le_of_eq (congrArg (· + 1) ((congrArg ones he).trans (ones_double _)).symm)
    · have hsmall : n/2 < n := by omega
      have ht : n+1 = 2*(n/2+1) := by omega
      have hnt : ones n = ones (n/2)+1 := by
        calc
          ones n = ones (2*(n/2)+1) := congrArg ones ho
          _ = _ := ones_double_succ _
      rw [ht, ones_double, hnt]
      have hh := ih (n/2) hsmall
      omega

private theorem nextBit_cases (q : List ℕ) :
    nextBit q = 0 ∨ nextBit q = 1 := by
  unfold nextBit
  split <;> simp_all

private theorem ones_transition (p b c : ℕ) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    ones (p+b) ≤ ones (2*p+b+c) := by
  rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
  · simp only [Nat.add_zero, ones_double, le_refl]
  · simp only [Nat.add_zero, ones_double_succ]
    omega
  · simpa only [Nat.add_zero, ones_double_succ] using ones_succ_le p
  · rw [show 2*p+1+1 = 2*(p+1) by omega, ones_double]

theorem OMA.solution : type_of% @OMA.S_oeis_a324608.main := by
  apply monotone_nat_of_le_succ
  intro n
  rcases n with _ | _ | n
  · decide +kernel
  · decide +kernel
  · change ones ((state n).1 + nextBit (state n).2) ≤
      ones ((state (n+1)).1 + nextBit (state (n+1)).2)
    have h : (state (n+1)).1 = 2*(state n).1 + nextBit (state n).2 := by rw [state]
    rw [h]
    exact ones_transition _ _ _ (nextBit_cases _) (nextBit_cases _)