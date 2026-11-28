import OMAStatements.S_oeis_a007306

namespace OMA.S_oeis_a007306

private theorem stern_even (m : ℕ) : stern (2*m) = stern m := by
  rcases eq_or_ne m 0 with rfl | hm
  · norm_num [stern]
  · rw [show 2*m=(2*m-2)+2 by omega, stern]
    simp [show ((2*m-2)+2)%2=0 by omega, show ((2*m-2)+2)/2=m by omega]

private theorem stern_odd (m : ℕ) : stern (2*m+1) = stern m+stern (m+1) := by
  rcases eq_or_ne m 0 with rfl | hm
  · norm_num [stern]
  · rw [show 2*m+1=(2*m-1)+2 by omega, stern]
    simp [show (2*m-1)%2≠0 by omega, show ((2*m-1)+2)/2=m by omega]

private theorem stern_pos (n : ℕ) (hn : 0 < n) : 0 < stern n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n=1
    · subst n
      simp [stern]
    by_cases he : n%2=0
    · obtain ⟨m,rfl⟩ : ∃ m,n=2*m := ⟨n/2, by omega⟩
      rw [stern_even]
      exact ih m (by omega) (by omega)
    · obtain ⟨m,rfl⟩ : ∃ m,n=2*m+1 := ⟨n/2, by omega⟩
      rw [stern_odd]
      have hp := ih (m+1) (by omega) (by omega)
      omega

private def f (n : ℕ) : ℤ := stern n

private theorem f_even (m : ℕ) : f (2*m) = f m := by
  simp only [f, stern_even]

private theorem f_odd (m : ℕ) : f (2*m+1) = f m+f (m+1) := by
  simp only [f, stern_odd, Nat.cast_add]

/-- The middle Stern value controls the remainder between its two neighbors. -/
private theorem advance (n : ℕ) (hn : 0 < n) :
    f (n+1) = f (n-1)+f n-2*(f (n-1)%f n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n%2=0
    · obtain ⟨m,rfl⟩ : ∃ m,n=2*m := ⟨n/2, by omega⟩
      have hh := ih m (by omega) (by omega)
      rw [show 2*m-1=2*(m-1)+1 by omega, f_odd (m-1),
        show m-1+1=m by omega, f_odd m, f_even m, Int.add_emod_right]
      linarith
    · obtain ⟨m,rfl⟩ : ∃ m,n=2*m+1 := ⟨n/2, by omega⟩
      rw [show 2*m+1+1=2*(m+1) by omega, show 2*m+1-1=2*m by omega,
        f_even (m+1), f_even m, f_odd m]
      have hnonneg : 0 ≤ f m := by dsimp [f]; positivity
      have hpos : 0 < f (m+1) := by
        change 0 < (stern (m+1) : ℤ)
        exact_mod_cast stern_pos (m+1) (by omega)
      rw [Int.emod_eq_of_lt hnonneg (by linarith)]
      ring

private theorem ab_values (k : ℕ) : ab k = (f k+f (k+1), f (k+1)) := by
  induction k with
  | zero => norm_num [ab,f,stern]
  | succ k ih =>
    rw [ab, ih]
    have h := advance (k+1) (by omega)
    simp only [Nat.add_sub_cancel, Int.add_emod_right] at h ⊢
    exact Prod.ext (by linarith) (by linarith)

end OMA.S_oeis_a007306

open OMA.S_oeis_a007306

theorem OMA.solution : type_of% @OMA.S_oeis_a007306.main := by
  intro n hn
  rw [ab_values, a, if_neg (by omega), show 2*n-1=2*(n-1)+1 by omega, stern_odd]
  simp [f]
