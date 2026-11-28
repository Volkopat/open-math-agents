import OMAReductions.R_OeisA110854_conjecture_R1
import Mathlib

/-! Two overlapping prime blocks certify each even value independently of the parity of the initial prime index. -/

open OeisA110854

private theorem nextIndex {p q : ℕ} (hle : p ≤ q)
    (h : Nat.count (fun i => Nat.Prime (p + i)) (q - p) = 1) :
    Nat.count Nat.Prime q = Nat.count Nat.Prime p + 1 := by
  simpa only [Nat.add_sub_of_le hle, h] using (Nat.count_add Nat.Prime p (q - p))

private theorem gapIndex {p q : ℕ} (hle : p < q) (hp : p.Prime)
    (hn : ∀ i : ℕ, 0 < i → i < q - p → ¬ (p+i).Prime) :
    Nat.count Nat.Prime q = Nat.count Nat.Prime p + 1 := by
  apply nextIndex hle.le
  rw [Nat.count_eq_card_filter_range]
  have he : ((Finset.range (q-p)).filter fun i => (p+i).Prime) = {0} := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp [hp, Nat.sub_pos_of_lt hle]
    · simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, hi, iff_false]
      exact fun h => hn i (Nat.pos_of_ne_zero hi) h.1 h.2
  rw [he, Finset.card_singleton]

private theorem blockWitness {d p₀ p₁ p₂ p₃ p₄ : ℕ}
    (hp₀ : p₀.Prime) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime) (hp₄ : p₄.Prime)
    (h₀ : Nat.count Nat.Prime p₁ = Nat.count Nat.Prime p₀ + 1)
    (h₁ : Nat.count Nat.Prime p₂ = Nat.count Nat.Prime p₁ + 1)
    (h₂ : Nat.count Nat.Prime p₃ = Nat.count Nat.Prime p₂ + 1)
    (h₃ : Nat.count Nat.Prime p₄ = Nat.count Nat.Prime p₃ + 1)
    (hd₀ : d = ((p₃ : ℤ) - p₂ - p₁ + p₀).natAbs)
    (hd₁ : d = ((p₄ : ℤ) - p₃ - p₂ + p₁).natAbs) :
    ∃ n : ℕ, 0 < n ∧ d = (a n).natAbs := by
  let j := Nat.count Nat.Prime p₀
  have e₀ : Nat.nth Nat.Prime j = p₀ := Nat.nth_count hp₀
  have e₁ : Nat.nth Nat.Prime (j+1) = p₁ := by
    rw [show j+1 = Nat.count Nat.Prime p₁ by exact h₀.symm]
    exact Nat.nth_count hp₁
  have e₂ : Nat.nth Nat.Prime (j+2) = p₂ := by
    rw [show j+2 = Nat.count Nat.Prime p₂ by dsimp [j]; omega]
    exact Nat.nth_count hp₂
  have e₃ : Nat.nth Nat.Prime (j+3) = p₃ := by
    rw [show j+3 = Nat.count Nat.Prime p₃ by dsimp [j]; omega]
    exact Nat.nth_count hp₃
  have e₄ : Nat.nth Nat.Prime (j+4) = p₄ := by
    rw [show j+4 = Nat.count Nat.Prime p₄ by dsimp [j]; omega]
    exact Nat.nth_count hp₄
  by_cases hj : j % 2 = 0
  · let n := j / 2 + 1
    have hn : 0 < n := by dsimp [n]; omega
    refine ⟨n, hn, ?_⟩
    simp only [a, if_neg hn.ne']
    rw [show 2*n+2-1 = j+3 by dsimp [n]; omega, show 2*n+1-1 = j+2 by dsimp [n]; omega,
      show 2*n-1-1 = j by dsimp [n]; omega, show 2*n-1 = j+1 by dsimp [n]; omega,
      e₀, e₁, e₂, e₃]
    exact hd₀
  · let n := (j+1) / 2 + 1
    have hn : 0 < n := by dsimp [n]; omega
    refine ⟨n, hn, ?_⟩
    simp only [a, if_neg hn.ne']
    rw [show 2*n+2-1 = j+4 by dsimp [n]; omega, show 2*n+1-1 = j+3 by dsimp [n]; omega,
      show 2*n-1-1 = j+1 by dsimp [n]; omega, show 2*n-1 = j+2 by dsimp [n]; omega,
      e₁, e₂, e₃, e₄]
    exact hd₁

set_option maxHeartbeats 1000000 in
private theorem value0 : ∃ n : ℕ, 0 < n ∧ 0 = (a n).natAbs := by
  apply blockWitness (p₀ := 5) (p₁ := 7) (p₂ := 11) (p₃ := 13) (p₄ := 17)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value2 : ∃ n : ℕ, 0 < n ∧ 2 = (a n).natAbs := by
  apply blockWitness (p₀ := 67) (p₁ := 71) (p₂ := 73) (p₃ := 79) (p₄ := 83)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value4 : ∃ n : ℕ, 0 < n ∧ 4 = (a n).natAbs := by
  apply blockWitness (p₀ := 139) (p₁ := 149) (p₂ := 151) (p₃ := 157) (p₄ := 163)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value6 : ∃ n : ℕ, 0 < n ∧ 6 = (a n).natAbs := by
  apply blockWitness (p₀ := 397) (p₁ := 401) (p₂ := 409) (p₃ := 419) (p₄ := 421)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value8 : ∃ n : ℕ, 0 < n ∧ 8 = (a n).natAbs := by
  apply blockWitness (p₀ := 613) (p₁ := 617) (p₂ := 619) (p₃ := 631) (p₄ := 641)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value10 : ∃ n : ℕ, 0 < n ∧ 10 = (a n).natAbs := by
  apply blockWitness (p₀ := 1831) (p₁ := 1847) (p₂ := 1861) (p₃ := 1867) (p₄ := 1871)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value12 : ∃ n : ℕ, 0 < n ∧ 12 = (a n).natAbs := by
  apply blockWitness (p₀ := 2797) (p₁ := 2801) (p₂ := 2803) (p₃ := 2819) (p₄ := 2833)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value14 : ∃ n : ℕ, 0 < n ∧ 14 = (a n).natAbs := by
  apply blockWitness (p₀ := 27103) (p₁ := 27107) (p₂ := 27109) (p₃ := 27127) (p₄ := 27143)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value16 : ∃ n : ℕ, 0 < n ∧ 16 = (a n).natAbs := by
  apply blockWitness (p₀ := 23339) (p₁ := 23357) (p₂ := 23369) (p₃ := 23371) (p₄ := 23399)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value18 : ∃ n : ℕ, 0 < n ∧ 18 = (a n).natAbs := by
  apply blockWitness (p₀ := 40039) (p₁ := 40063) (p₂ := 40087) (p₃ := 40093) (p₄ := 40099)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value20 : ∃ n : ℕ, 0 < n ∧ 20 = (a n).natAbs := by
  apply blockWitness (p₀ := 23677) (p₁ := 23687) (p₂ := 23689) (p₃ := 23719) (p₄ := 23741)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value22 : ∃ n : ℕ, 0 < n ∧ 22 = (a n).natAbs := by
  apply blockWitness (p₀ := 16007) (p₁ := 16033) (p₂ := 16057) (p₃ := 16061) (p₄ := 16063)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value24 : ∃ n : ℕ, 0 < n ∧ 24 = (a n).natAbs := by
  apply blockWitness (p₀ := 78367) (p₁ := 78401) (p₂ := 78427) (p₃ := 78437) (p₄ := 78439)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value26 : ∃ n : ℕ, 0 < n ∧ 26 = (a n).natAbs := by
  apply blockWitness (p₀ := 44381) (p₁ := 44383) (p₂ := 44389) (p₃ := 44417) (p₄ := 44449)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value28 : ∃ n : ℕ, 0 < n ∧ 28 = (a n).natAbs := by
  apply blockWitness (p₀ := 278909) (p₁ := 278911) (p₂ := 278917) (p₃ := 278947) (p₄ := 278981)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value30 : ∃ n : ℕ, 0 < n ∧ 30 = (a n).natAbs := by
  apply blockWitness (p₀ := 210967) (p₁ := 211007) (p₂ := 211039) (p₃ := 211049) (p₄ := 211051)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
private theorem value32 : ∃ n : ℕ, 0 < n ∧ 32 = (a n).natAbs := by
  apply blockWitness (p₀ := 293483) (p₁ := 293507) (p₂ := 293543) (p₃ := 293599) (p₄ := 293603)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · refine gapIndex (by decide) (by norm_num) ?_
    intro i hi hj
    norm_num at hj
    interval_cases i <;> norm_num
  · decide
  · decide

set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_OeisA110854_conjecture_R1.H1 := by
  intro d hd h
  interval_cases d
  · exact value0
  · exact ⟨1, by decide, by simp [a_1]⟩
  · exact value2
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value4
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value6
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value8
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value10
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value12
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value14
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value16
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value18
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value20
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value22
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value24
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value26
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value28
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value30
  · rcases h with h | ⟨k, hk⟩ <;> omega
  · exact value32