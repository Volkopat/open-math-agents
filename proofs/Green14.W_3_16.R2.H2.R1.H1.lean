import OMAReductions.R_Green14_W_3_16_R2_H2_R1

/-! A reflection-symmetric coloring of the interval of length 236. -/

namespace Green16Palindrome

private def color (i : Nat) : Bool :=
  (20792044773536508121720047001436160 : Nat).testBit (min i (235 - i))

private def checks (length : Nat) (b : Bool) : Bool :=
  (List.range (235 / (length - 1))).all fun i =>
    (List.range (236 - (length-1)*(i+1))).all fun a =>
      (List.range length).any fun t => color (a+t*(i+1)) == b

private theorem witness {length a d : Nat} {b : Bool} (hl : 1 < length)
    (hd : 0 < d) (ha : a+(length-1)*d < 236) (check : checks length b = true) :
    ∃ t < length, color (a+t*d) = b := by
  have dLe : d ≤ 235 / (length-1) := (Nat.le_div_iff_mul_le (by omega)).2 (by
    rw [Nat.mul_comm]
    omega)
  have dEq : d - 1 + 1 = d := by omega
  have outer := List.all_eq_true.mp check (d-1) (List.mem_range.mpr (by omega))
  rw [dEq] at outer
  have inner := List.all_eq_true.mp outer a (List.mem_range.mpr (by omega))
  obtain ⟨t, ht, value⟩ := List.any_eq_true.mp inner
  exact ⟨t, List.mem_range.mp ht, by simpa using value⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem red : checks 3 false = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem blue : checks 16 true = true := by decide +kernel

theorem exists_coloring : OMA.R_Green14_W_3_16_R2_H2_R1.H1 := by
  refine ⟨color, ?_, ?_⟩
  · intro x hx
    change color (235 - x) = color x
    have h : 235 - (235 - x) = x := by omega
    simp only [color, h, Nat.min_comm]
  · intro b a d hd bound
    cases b
    · exact witness (by decide) hd bound red
    · exact witness (by decide) hd bound blue

end Green16Palindrome

theorem OMA.solution : OMA.R_Green14_W_3_16_R2_H2_R1.H1 :=
  Green16Palindrome.exists_coloring