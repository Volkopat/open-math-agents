import OMAReductions.R_oeis_a331234_R1

namespace OMA.PellPrimeIndex

private def step (v : ℕ × ℕ) : ℕ × ℕ := (v.1 + 2 * v.2, v.1 + v.2)

private def pell (n : ℕ) : ℕ × ℕ := step^[n] (1, 0)

private theorem pell_succ (n : ℕ) : pell (n + 1) = step (pell n) :=
  Function.iterate_succ_apply' step n (1, 0)

private theorem pell_add (m n : ℕ) :
    pell (m + n) = ((pell m).1 * (pell n).1 + 2 * (pell m).2 * (pell n).2,
      (pell m).1 * (pell n).2 + (pell m).2 * (pell n).1) := by
  induction n with
  | zero => simp [show pell 0 = (1, 0) from rfl]
  | succ n ih =>
    rw [Nat.add_succ, pell_succ, ih, pell_succ]
    apply Prod.ext <;> dsimp [step] <;> ring

private theorem second_dvd (d k : ℕ) : (pell d).2 ∣ (pell (d * k)).2 := by
  induction k with
  | zero => change (pell d).2 ∣ 0; exact dvd_zero _
  | succ k ih =>
    rw [Nat.mul_succ, pell_add]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

private theorem first_pos (n : ℕ) : 0 < (pell n).1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [pell_succ]; dsimp [step]; omega

private theorem second_strict : StrictMono (fun n => (pell n).2) := by
  apply strictMono_nat_of_lt_succ
  intro n
  change (pell n).2 < (pell (n + 1)).2
  rw [pell_succ]
  dsimp [step]
  have := first_pos n
  omega

-- Multiplication by the inverse of 1 + √2 decreases the second coordinate.
private theorem generated (y x : ℕ)
    (h : x ^ 2 + 1 = 2 * y ^ 2 ∨ x ^ 2 = 2 * y ^ 2 + 1) :
    ∃ n, pell n = (x, y) := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases hy : y = 0
    · subst y
      have hx : x = 1 := by
        simp at h
        nlinarith
      subst x
      exact ⟨0, rfl⟩
    have hy1 : 1 ≤ y := by omega
    have ysq : 1 ≤ y ^ 2 := by
      simpa using Nat.pow_le_pow_left hy1 2
    have hlow : y ≤ x := by
      by_contra! hlt
      have hsq : x ^ 2 < y ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
      rcases h with h | h <;> omega
    have hhigh : x < 2 * y := by
      by_contra! hge
      have hsq : (2 * y) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hge 2
      rcases h with h | h <;> nlinarith
    let u := 2 * y - x
    let v := x - y
    have hu : (u : ℤ) = 2 * (y : ℤ) - (x : ℤ) := by
      dsimp [u]
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl
    have hv : (v : ℤ) = (x : ℤ) - (y : ℤ) := by
      exact Nat.cast_sub hlow
    have hnorm : (u : ℤ) ^ 2 - 2 * (v : ℤ) ^ 2 =
        -( (x : ℤ) ^ 2 - 2 * (y : ℤ) ^ 2) := by rw [hu, hv]; ring
    have hn : u ^ 2 + 1 = 2 * v ^ 2 ∨ u ^ 2 = 2 * v ^ 2 + 1 := by
      rcases h with h | h
      · right
        have hh : (x : ℤ) ^ 2 + 1 = 2 * (y : ℤ) ^ 2 := by exact_mod_cast h
        exact_mod_cast (show (u : ℤ) ^ 2 = 2 * (v : ℤ) ^ 2 + 1 by linarith)
      · left
        have hh : (x : ℤ) ^ 2 = 2 * (y : ℤ) ^ 2 + 1 := by exact_mod_cast h
        exact_mod_cast (show (u : ℤ) ^ 2 + 1 = 2 * (v : ℤ) ^ 2 by linarith)
    obtain ⟨n, hn⟩ := ih v (by dsimp [v]; omega) u hn
    refine ⟨n + 1, ?_⟩
    rw [pell_succ, hn]
    apply Prod.ext <;> dsimp [step, u, v] <;> omega

end OMA.PellPrimeIndex

open OMA.PellPrimeIndex in
theorem OMA.solution : OMA.R_oeis_a331234_R1.H1 := by
  intro x y _ hy hnorm
  obtain ⟨n, hn⟩ := generated y x (Or.inl hnorm)
  have hny : (pell n).2 = y := congrArg Prod.snd hn
  have hy2 := hy.two_le
  have hn2 : 2 ≤ n := by
    by_contra! h
    interval_cases n <;> norm_num [pell, step] at hny <;> omega
  refine ⟨n, ?_, hn⟩
  by_contra hp
  let d := n.minFac
  have hd : d.Prime := Nat.minFac_prime (by omega)
  have hdn : d ∣ n := Nat.minFac_dvd n
  have hlt : d < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdn) (fun h => hp (h ▸ hd))
  obtain ⟨k, hk⟩ := hdn
  have hdvd : (pell d).2 ∣ y := by rw [← hny, hk]; exact second_dvd d k
  have hd2 := hd.two_le
  have hgt : 1 < (pell d).2 := second_strict (show 1 < d by omega)
  have hlt' : (pell d).2 < y := hny ▸ second_strict hlt
  rcases (Nat.dvd_prime hy).mp hdvd with h | h <;> omega
