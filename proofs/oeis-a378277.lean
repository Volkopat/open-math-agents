import OMAStatements.S_oeis_a378277

namespace OMA.P_oeis_a378277

open Nat

lemma cassini (m : ℕ) :
    ((fib (m + 1) : ℚ)) ^ 2 - (fib m : ℚ) * (fib (m + 2) : ℚ) = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : (fib (m + 2) : ℚ) = fib m + fib (m + 1) := by
      rw [fib_add_two]; push_cast; ring
    have h3 : (fib (m + 1 + 2) : ℚ) = fib m + 2 * fib (m + 1) := by
      rw [show m + 1 + 2 = (m + 1) + 2 by ring, fib_add_two, show m + 1 + 1 = m + 2 by ring,
        fib_add_two]
      push_cast; ring
    rw [show m + 1 + 1 = m + 2 by ring, h3, h2, pow_succ]
    rw [h2] at ih
    linear_combination (-1 : ℚ) * ih

lemma fib_pos' (m : ℕ) : (0 : ℚ) < fib (m + 1) := by
  exact_mod_cast fib_pos.mpr (by omega)

/-- The partial alternating sum over the subdiagonal entries. -/
lemma key (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (k + 1) / ((fib k : ℚ) * (fib (k + 2) : ℚ)) +
      (-1 : ℚ) ^ m / ((fib (m + 1) : ℚ) * (fib (m + 2) : ℚ)) =
      ((fib (m + 1) : ℚ) - fib m) / (fib (m + 2) : ℚ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ha := fib_pos' m
    have hb := fib_pos' (m + 1)
    have hc := fib_pos' (m + 2)
    have h2 : (fib (m + 2) : ℚ) = fib m + fib (m + 1) := by
      rw [fib_add_two]; push_cast; ring
    have h3 : (fib (m + 3) : ℚ) = fib m + 2 * fib (m + 1) := by
      rw [show m + 3 = (m + 1) + 2 by ring, fib_add_two, show m + 1 + 1 = m + 2 by ring,
        fib_add_two]
      push_cast; ring
    have hs := cassini m
    have e : ∑ k ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (k + 1) / ((fib k : ℚ) * (fib (k + 2) : ℚ)) =
        ((fib (m + 1) : ℚ) - fib m) / (fib (m + 2) : ℚ) -
          (-1 : ℚ) ^ m / ((fib (m + 1) : ℚ) * (fib (m + 2) : ℚ)) := by
      rw [← ih]; ring
    rw [e, show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring, h3, h2]
    rw [h2] at hs
    have hs' : (-1 : ℚ) ^ m = (fib (m + 1) : ℚ) ^ 2 - (fib m : ℚ) * ((fib m : ℚ) + fib (m + 1)) :=
      hs.symm
    have ha0 : (0 : ℚ) ≤ fib m := by positivity
    simp only [pow_succ]
    rw [hs']
    have hb' : (fib (m + 1) : ℚ) ≠ 0 := ne_of_gt ha
    have hc' : (fib m : ℚ) + fib (m + 1) ≠ 0 := by positivity
    have hd' : (fib m : ℚ) + 2 * fib (m + 1) ≠ 0 := by positivity
    field_simp
    ring

end OMA.P_oeis_a378277

theorem OMA.solution : type_of% @OMA.S_oeis_a378277.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_Icc_succ_top (by omega)]
  have hT : ∀ k ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (k + 1) / (OMA.S_oeis_a378277.T (m + 1) k : ℚ) =
      (-1 : ℚ) ^ (k + 1) / ((Nat.fib k : ℚ) * (Nat.fib (k + 2) : ℚ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    unfold OMA.S_oeis_a378277.T
    rw [if_neg (by omega)]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hT]
  have hk := OMA.P_oeis_a378277.key m
  unfold OMA.S_oeis_a378277.T OMA.S_oeis_a378277.fibSub2
  rw [if_pos rfl]
  rcases m with _ | m
  · simp
  · rw [if_neg (by omega), show m + 1 + 1 - 2 = m by omega]
    have h1 : (Nat.fib (m + 1 + 1) : ℚ) - Nat.fib (m + 1) = Nat.fib m := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [h1] at hk
    rw [← hk]
    push_cast
    rw [show m + 1 + 1 + 1 = m + 1 + 2 by ring, show (-1 : ℚ) ^ (m + 1 + 1 + 1) = (-1) ^ (m + 1) by
      rw [pow_succ, pow_succ]; ring]
