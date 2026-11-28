import OMAStatements.S_oeis_a077653

-- OEIS A077653, general conjecture of Benoit Cloitre.
-- Counterexample and proof by Youssef BERHAYLA (@Youssef000299) with the assistance of Codex.
namespace OMA.A077653Counterexample
open OMA.S_oeis_a077653

private abbrev u := seq 2 2 4

private theorem nextTerm (n : ℕ) (hn : 0 < n) :
    u (n+3) = |u (n+2) - u (n+1) - u n| := by
  cases n with
  | zero => omega
  | succ n => rfl

private def frame (i j : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ u n = 2 * (i : ℤ) ∧
    u (n+1) = 2 * (j : ℤ) ∧ u (n+2) = 2 * ((i : ℤ)+1)

private theorem transfer (i j : ℕ) (h : frame i (j+1)) : frame (i+1) j := by
  obtain ⟨n, hn, h0, h1, h2⟩ := h
  push_cast at h1
  have h3 := nextTerm n hn
  rw [h0, h1, h2] at h3
  have e3 : 2*((i : ℤ)+1) - 2*((j : ℤ)+1) - 2*i = -(2*j) := by omega
  rw [e3, abs_neg, abs_of_nonneg (by positivity)] at h3
  have h4 := nextTerm (n+1) (by omega)
  change u (n+4) = |u (n+3) - u (n+2) - u (n+1)| at h4
  rw [h1, h2, h3] at h4
  have e4 : 2*(j : ℤ) - 2*((i : ℤ)+1) - 2*(j+1) = -(2*(i+2)) := by omega
  rw [e4, abs_neg, abs_of_nonneg (by positivity)] at h4
  refine ⟨n+2, by omega, ?_, h3, ?_⟩
  · push_cast; exact h2
  · change u (n+4) = _
    push_cast
    omega

private theorem drain (i j : ℕ) (h : frame i j) : frame (i+j) 0 := by
  induction j generalizing i with
  | zero => simpa using h
  | succ j ih =>
    simpa only [Nat.add_assoc, Nat.add_comm 1 j] using ih (i+1) (transfer i j h)

private theorem restart (i : ℕ) (h : frame i 0) : frame 0 (i+1) := by
  obtain ⟨n, hn, h0, h1, h2⟩ := h
  have h3 := nextTerm n hn
  rw [h0,h1,h2] at h3
  refine ⟨n+1, by omega, by simpa using h1, by push_cast; exact h2, ?_⟩
  have he : 2*((i : ℤ)+1) - 2*(0:ℤ) - 2*i = 2 := by omega
  simp only [Nat.cast_zero] at h3
  rw [he] at h3
  exact h3

private theorem blocks (k : ℕ) : frame 0 (3+k) := by
  induction k with
  | zero => exact ⟨4, by decide, by decide, by decide, by decide⟩
  | succ k ih =>
    have h := restart _ (drain _ _ ih)
    simpa [Nat.add_assoc] using h

private theorem unbounded : ∀ B : ℤ, ∃ n : ℕ, 1 ≤ n ∧ B < u n := by
  intro B
  obtain ⟨n, hn, _, h, _⟩ := blocks B.natAbs
  refine ⟨n+1, by omega, ?_⟩
  rw [h]
  push_cast
  have := le_abs_self B
  have := abs_nonneg B
  omega

private theorem evenTerm (n : ℕ) : 2 ∣ u n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 | 3 => decide
    | k+4 =>
      change 2 ∣ |u (k+3) - u (k+2) - u (k+1)|
      have h := dvd_sub (dvd_sub (ih (k+3) (by omega)) (ih (k+2) (by omega)))
        (ih (k+1) (by omega))
      rcases le_total 0 (u (k+3) - u (k+2) - u (k+1)) with hp | hn
      · rwa [abs_of_nonneg hp]
      · simpa [abs_of_nonpos hn] using dvd_neg.mpr h

private theorem evenMax (n : ℕ) : (2 : ℤ) ∣ maxUpTo 2 2 4 n := by
  induction n with
  | zero => exact dvd_zero _
  | succ n ih =>
    change 2 ∣ max (maxUpTo 2 2 4 n) (u (n+1))
    rcases le_total (maxUpTo 2 2 4 n) (u (n+1)) with h | h
    · simpa [max_eq_right h] using evenTerm (n+1)
    · simpa [max_eq_left h] using ih

theorem refute : ¬ (type_of% @OMA.S_oeis_a077653.main) := by
  intro hall
  obtain ⟨N,C,h⟩ := hall 2 2 4 unbounded
  let t : ℕ := 2 * (N + C.natAbs + 1) + 1
  have := le_abs_self C
  have := abs_nonneg C
  have ht : (N : ℤ) + C < (t : ℤ) := by dsimp [t]; push_cast; omega
  have ht1 : (1 : ℤ) ≤ t := by dsimp [t]; push_cast; omega
  have hs : (t : ℤ) ≤ (t : ℤ)^2 := by nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ t) (by omega : (0:ℤ) ≤ (t:ℤ)-1)]
  let n := ((t : ℤ)^2 - C).toNat
  have hn : (n : ℤ) = (t : ℤ)^2 - C := Int.toNat_of_nonneg (by omega)
  have he := h n (by omega)
  have hr : (n : ℝ) + (C : ℝ) = (t : ℝ)^2 := by exact_mod_cast (show (n : ℤ) + C = (t : ℤ)^2 by omega)
  rw [hr, Real.sqrt_sq (by positivity), Int.floor_natCast] at he
  norm_num at he
  have hd := evenMax n
  rw [he] at hd
  dsimp [t] at hd
  push_cast at hd
  omega

end OMA.A077653Counterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a077653.main) := by
  exact OMA.A077653Counterexample.refute
