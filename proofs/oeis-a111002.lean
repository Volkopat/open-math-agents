import OMAStatements.S_oeis_a111002

-- Problem: A111002: a(n) = gcd(f(n), f(n+1)) where f(n) = n^4 + n^2 + 1.
-- Upstream: formal-conjectures statements/oeis-a111002.lean:0 (declaration OMA.S_oeis_a111002.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: f(n) = (n^2+n+1)(n^2-n+1), f(n+1) = (n^2+n+1)(n^2+3n+3), and gcd(n^2-n+1, n^2+3n+3) divides 14, is odd, and is 7 exactly when n = 3 (mod 7); so a(n) = (n^2+n+1)*(7 or 1) with period 7 in the factor, and the recurrence is a third difference of a quadratic.

open OMA.S_oeis_a111002 in
theorem OMA.solution : type_of% @OMA.S_oeis_a111002.main := by
  have key : ∀ x : ZMod 7, (x ^ 2 - x + 1 = 0 ∧ x ^ 2 + 3 * x + 3 = 0) ↔ x = 3 := by decide
  have hc : ∀ n : ℕ, a n = (n ^ 2 + n + 1) * (if n % 7 = 3 then 7 else 1) := by
    intro n
    have hle : n ≤ n ^ 2 := by
      rw [sq]
      exact Nat.le_mul_self n
    have hf1 : f n = (n ^ 2 + n + 1) * (n ^ 2 - n + 1) := by
      unfold f
      zify [hle]
      ring
    have hf2 : f (n + 1) = (n ^ 2 + n + 1) * (n ^ 2 + 3 * n + 3) := by
      unfold f
      ring
    have hgB := Nat.gcd_dvd_left (n ^ 2 - n + 1) (n ^ 2 + 3 * n + 3)
    have hgC := Nat.gcd_dvd_right (n ^ 2 - n + 1) (n ^ 2 + 3 * n + 3)
    have h14 : Nat.gcd (n ^ 2 - n + 1) (n ^ 2 + 3 * n + 3) ∣ 14 := by
      have hB := Int.natCast_dvd_natCast.mpr hgB
      have hC := Int.natCast_dvd_natCast.mpr hgC
      push_cast [Nat.cast_sub hle] at hB hC
      have h := dvd_sub (dvd_mul_of_dvd_right hB (2 * (n : ℤ) + 5))
        (dvd_mul_of_dvd_right hC (2 * (n : ℤ) - 3))
      rw [show (2 * (n : ℤ) + 5) * ((n : ℤ) ^ 2 - n + 1)
          - (2 * (n : ℤ) - 3) * ((n : ℤ) ^ 2 + 3 * n + 3) = 14 by ring] at h
      exact_mod_cast h
    have hoddB : ¬ 2 ∣ n ^ 2 - n + 1 := by
      have heq : n ^ 2 - n + 1 = n * (n - 1) + 1 := by
        rw [Nat.mul_sub_one, sq]
      rw [heq, Nat.dvd_add_right (Nat.even_mul_pred_self n).two_dvd]
      decide
    have h7 : (7 ∣ n ^ 2 - n + 1 ∧ 7 ∣ n ^ 2 + 3 * n + 3) ↔ n % 7 = 3 := by
      rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff]
      push_cast [Nat.cast_sub hle]
      rw [key]
      constructor
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast] at hv
        exact hv
      · intro h
        exact (ZMod.natCast_mod n 7).symm.trans (congrArg (Nat.cast : ℕ → ZMod 7) h)
    have hmem : Nat.gcd (n ^ 2 - n + 1) (n ^ 2 + 3 * n + 3) ∈ Nat.divisors 14 :=
      Nat.mem_divisors.mpr ⟨h14, by norm_num⟩
    rw [show Nat.divisors 14 = {1, 2, 7, 14} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    unfold a
    rw [hf1, hf2, Nat.gcd_mul_left]
    rcases hmem with h | h | h | h
    · have hn : ¬ n % 7 = 3 := by
        intro hn
        have h7g := Nat.dvd_gcd (h7.mpr hn).1 (h7.mpr hn).2
        rw [h] at h7g
        omega
      rw [h, if_neg hn]
    · exfalso
      rw [h] at hgB
      exact hoddB hgB
    · rw [h, if_pos (h7.mp ⟨h ▸ hgB, h ▸ hgC⟩)]
    · exfalso
      rw [h] at hgB
      exact hoddB (dvd_trans ⟨7, by norm_num⟩ hgB)
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 21 := ⟨n - 21, by omega⟩
  rw [show m + 21 - 7 = m + 14 by omega, show m + 21 - 14 = m + 7 by omega,
    show m + 21 - 21 = m by omega, hc (m + 21), hc (m + 14), hc (m + 7), hc m,
    show (m + 21) % 7 = m % 7 by omega, show (m + 14) % 7 = m % 7 by omega,
    show (m + 7) % 7 = m % 7 by omega]
  split_ifs <;> push_cast <;> ring
