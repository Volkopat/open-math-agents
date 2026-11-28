import OMAStatements.S_oeis_a394666

-- Problem: A394666: a(n) = n! mod (2*n - 1).
-- Upstream: formal-conjectures statements/oeis-a394666.lean:0 (declaration OMA.S_oeis_a394666.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a prime 2n-1 > n cannot divide n!; n = 2..5 by computation; a composite odd
-- m = 2n-1 = d*e (d, e odd, so at least 3) has d*e | n! when d, e are distinct (both at most n),
-- and d*d | d*(2d) | n! when d = e (then d is at least 5, as m = 9 would give n = 5, so 2d is at most n).

open OMA.S_oeis_a394666 in
theorem OMA.solution : type_of% @OMA.S_oeis_a394666.main := by
  have key : ∀ d e n : ℕ, 0 < d → d < e → e ≤ n → d * e ∣ Nat.factorial n := by
    intro d e n hd hde hen
    have h1 : d ∣ Nat.factorial (e - 1) := Nat.dvd_factorial hd (by omega)
    have h2 : Nat.factorial (e - 1) * e = Nat.factorial e := by
      rw [mul_comm]
      exact Nat.mul_factorial_pred (by omega)
    have h3 : d * e ∣ Nat.factorial e := by
      rw [← h2]
      exact mul_dvd_mul_right h1 e
    exact h3.trans (Nat.factorial_dvd_factorial hen)
  intro n hn
  unfold a
  constructor
  · intro h0
    have hdvd : 2 * n - 1 ∣ Nat.factorial n := Nat.dvd_of_mod_eq_zero h0
    refine ⟨?_, ?_⟩
    · by_contra hle
      have hle' : n ≤ 5 := by omega
      interval_cases n <;> exact absurd h0 (by decide)
    · intro hp
      have := (Nat.Prime.dvd_factorial hp).mp hdvd
      omega
  · rintro ⟨h5, hnp⟩
    apply Nat.mod_eq_zero_of_dvd
    obtain ⟨d, ⟨e, he⟩, hd2, hdm⟩ := Nat.exists_dvd_of_not_prime2 (by omega : 2 ≤ 2 * n - 1) hnp
    have hdo : ¬ 2 ∣ d := by
      intro h2
      have h2' : 2 ∣ 2 * n - 1 := by
        rw [he]
        exact Dvd.dvd.mul_right h2 e
      omega
    have heo : ¬ 2 ∣ e := by
      intro h2
      have h2' : 2 ∣ 2 * n - 1 := by
        rw [he]
        exact Dvd.dvd.mul_left h2 d
      omega
    have he2 : 2 ≤ e := by
      by_contra hlt
      have hle : d * e ≤ d * 1 := Nat.mul_le_mul_left d (by omega)
      omega
    have hd3 : 3 ≤ d := by omega
    have he3 : 3 ≤ e := by omega
    have hA : 3 * e ≤ d * e := Nat.mul_le_mul_right e hd3
    have hB : d * 3 ≤ d * e := Nat.mul_le_mul_left d he3
    rw [he]
    rcases Nat.lt_trichotomy d e with hlt | heq | hgt
    · exact key d e n (by omega) hlt (by omega)
    · subst heq
      have hd4 : 4 ≤ d := by
        by_contra h3
        have h3' : d = 3 := by omega
        subst h3'
        omega
      have hC : 4 * d ≤ d * d := Nat.mul_le_mul_right d hd4
      have hdd : d * d ∣ d * (2 * d) := mul_dvd_mul_left d (dvd_mul_left d 2)
      exact hdd.trans (key d (2 * d) n (by omega) (by omega) (by omega))
    · rw [mul_comm]
      exact key e d n (by omega) hgt (by omega)