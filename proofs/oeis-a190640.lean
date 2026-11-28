import OMAStatements.S_oeis_a190640

open OMA.S_oeis_a190640

namespace OMA.P_oeis_a190640

lemma digits_of_parent {p : ℕ} (h : CantorParent p) : ∀ d ∈ Nat.digits 3 p, d = 0 ∨ d = 2 := by
  induction h with
  | root => simp
  | @left p hp ih =>
    rcases Nat.eq_zero_or_pos p with rfl | hpos
    · simp
    · intro d hd
      have e : Nat.digits 3 (3 * p) = (3 * p) % 3 :: Nat.digits 3 ((3 * p) / 3) :=
        Nat.digits_def' (by norm_num) (by omega)
      rw [e, show (3 * p) % 3 = 0 by omega, show (3 * p) / 3 = p by omega] at hd
      rcases List.mem_cons.mp hd with h | h
      · left; exact h
      · exact ih d h
  | @right p hp ih =>
    intro d hd
    have e : Nat.digits 3 (3 * p + 2) = (3 * p + 2) % 3 :: Nat.digits 3 ((3 * p + 2) / 3) :=
      Nat.digits_def' (by norm_num) (by omega)
    rw [e, show (3 * p + 2) % 3 = 2 by omega, show (3 * p + 2) / 3 = p by omega] at hd
    rcases List.mem_cons.mp hd with h | h
    · right; exact h
    · exact ih d h

lemma parent_of_digits (q : ℕ) : (∀ d ∈ Nat.digits 3 q, d = 0 ∨ d = 2) → CantorParent q := by
  refine Nat.strong_induction_on q ?_
  intro q ih hq
  rcases Nat.eq_zero_or_pos q with rfl | hpos
  · exact CantorParent.root
  · have e : Nat.digits 3 q = q % 3 :: Nat.digits 3 (q / 3) := Nat.digits_def' (by norm_num) hpos
    rw [e] at hq
    have hhead : q % 3 = 0 ∨ q % 3 = 2 := hq (q % 3) (by simp)
    have htail : ∀ d ∈ Nat.digits 3 (q / 3), d = 0 ∨ d = 2 := fun d hd => hq d (by simp [hd])
    have hp : CantorParent (q / 3) := ih (q / 3) (by omega) htail
    rcases hhead with h0 | h2
    · have hq3 : q = 3 * (q / 3) := by omega
      rw [hq3]
      exact CantorParent.left hp
    · have hq3 : q = 3 * (q / 3) + 2 := by omega
      rw [hq3]
      exact CantorParent.right hp

lemma key (m : ℕ) : digitTerm (m + 1) ↔ gapNumerator m := by
  unfold digitTerm gapNumerator
  constructor
  · rintro ⟨h3, hd⟩
    refine ⟨(m + 1) / 3, ?_, by omega⟩
    apply parent_of_digits
    have e : Nat.digits 3 (m + 1) = (m + 1) % 3 :: Nat.digits 3 ((m + 1) / 3) :=
      Nat.digits_def' (by norm_num) (by omega)
    rw [e] at hd
    intro d hdm
    exact hd d (by simp [hdm])
  · rintro ⟨p, hp, rfl⟩
    refine ⟨by omega, ?_⟩
    have e : Nat.digits 3 (3 * p + 1 + 1) =
        (3 * p + 1 + 1) % 3 :: Nat.digits 3 ((3 * p + 1 + 1) / 3) :=
      Nat.digits_def' (by norm_num) (by omega)
    rw [e, show (3 * p + 1 + 1) % 3 = 2 by omega, show (3 * p + 1 + 1) / 3 = p by omega]
    intro d hd
    rcases List.mem_cons.mp hd with h | h
    · right; exact h
    · exact digits_of_parent hp d h

lemma not_digitTerm_zero : ¬ digitTerm 0 := by
  intro h
  unfold digitTerm at h
  exact absurd h.1 (by norm_num)

lemma count_shift [DecidablePred digitTerm] [DecidablePred gapNumerator] (m : ℕ) :
    Nat.count digitTerm (m + 1) = Nat.count gapNumerator m := by
  induction m with
  | zero =>
    rw [Nat.count_succ, Nat.count_zero, Nat.count_zero, if_neg not_digitTerm_zero]
  | succ m ih =>
    rw [Nat.count_succ, ih, Nat.count_succ]
    by_cases h : gapNumerator m
    · rw [if_pos h, if_pos ((key m).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((key m).1 h'))]

lemma parent_two_pow (N : ℕ) : CantorParent (2 * 3 ^ N) := by
  induction N with
  | zero => simpa using CantorParent.right CantorParent.root
  | succ N ih =>
    have e : 2 * 3 ^ (N + 1) = 3 * (2 * 3 ^ N) := by ring
    rw [e]
    exact CantorParent.left ih

lemma lt_three_pow (B : ℕ) : B < 3 ^ B := by
  induction B with
  | zero => norm_num
  | succ B ih => rw [pow_succ]; omega

lemma gap_infinite : (setOf gapNumerator).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hmem : gapNumerator (3 * (2 * 3 ^ B) + 1) := ⟨2 * 3 ^ B, parent_two_pow B, rfl⟩
  have hle : 3 * (2 * 3 ^ B) + 1 ≤ B := hB hmem
  have hlt := lt_three_pow B
  omega

end OMA.P_oeis_a190640

open OMA.P_oeis_a190640 in
theorem OMA.solution : type_of% @OMA.S_oeis_a190640.main := by
  classical
  intro i
  have hg := Nat.nth_mem_of_infinite gap_infinite i
  have hc := Nat.count_nth_of_infinite gap_infinite i
  have hd : digitTerm (Nat.nth gapNumerator i + 1) := (key _).2 hg
  have hcount : Nat.count digitTerm (Nat.nth gapNumerator i + 1) = i := by
    rw [count_shift, hc]
  calc Nat.nth digitTerm i
      = Nat.nth digitTerm (Nat.count digitTerm (Nat.nth gapNumerator i + 1)) := by rw [hcount]
    _ = Nat.nth gapNumerator i + 1 := Nat.nth_count hd
