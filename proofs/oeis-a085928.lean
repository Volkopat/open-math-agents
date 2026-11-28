import OMAStatements.S_oeis_a085928

/-!
Two consecutive zero terms are impossible. After x, 0 with x positive,
the decimal concatenation is 10x, whose reversal has at most as many
digits as x and is therefore strictly smaller.
-/

namespace ConcatenationRecurrence

open OMA.S_oeis_a085928

private theorem concat_zero {x : ℕ} (hx : x ≠ 0) : concat10 x 0 = 10*x := by
  simp [concat10, digits10, hx, Nat.ofDigits_cons, Nat.ofDigits_digits]

private theorem reverse_trailing_zero {x : ℕ} (hx : x ≠ 0) : rev10 (10*x) < 10*x := by
  have hpos : 0 < x := by omega
  have hx10 : 10*x ≠ 0 := by positivity
  rw [rev10, digits10, if_neg hx10, Nat.digits_base_mul (by decide) hpos,
    Nat.ofDigits_reverse_zero_cons]
  have hb : Nat.ofDigits 10 (Nat.digits 10 x).reverse < 10^(Nat.digits 10 x).reverse.length :=
    Nat.ofDigits_lt_base_pow_length (by decide) (fun d hd =>
      Nat.digits_lt_base (by decide) (List.mem_reverse.mp hd))
  rw [List.length_reverse] at hb
  exact hb.trans_le (Nat.base_pow_length_digits_le 10 x (by decide) hx)

/-- Every pair of consecutive terms at positive indices contains a nonzero term. -/
theorem consecutive (n : ℕ) : a (n+1) ≠ 0 ∨ a (n+2) ≠ 0 := by
  induction n with
  | zero => exact Or.inl (by decide)
  | succ n ih =>
    by_cases hz : a (n+2) = 0
    · right
      have hx := ih.resolve_right (not_not_intro hz)
      change Int.natAbs ((concat10 (a (n+1)) (a (n+2)) : ℤ) -
        (rev10 (concat10 (a (n+1)) (a (n+2))) : ℤ)) ≠ 0
      rw [hz, concat_zero hx]
      have hrev := reverse_trailing_zero hx
      omega
    · exact Or.inl hz

end ConcatenationRecurrence

open OMA.S_oeis_a085928

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a085928.main) := by
  intro h
  obtain ⟨B, hb⟩ := h.bddAbove
  rcases ConcatenationRecurrence.consecutive B with h₁ | h₂
  · exact (by omega : ¬ B+1 ≤ B) (hb (show B+1 ∈ {n : ℕ | 1 ≤ n ∧ a n ≠ 0} from ⟨by omega, h₁⟩))
  · exact (by omega : ¬ B+2 ≤ B) (hb (show B+2 ∈ {n : ℕ | 1 ≤ n ∧ a n ≠ 0} from ⟨by omega, h₂⟩))
