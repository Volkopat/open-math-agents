import OMAStatements.S_oeis_a246776

-- Problem: A246776: a(n) = floor(prime(n)^(1+1/n)) - prime(n+1).
-- Upstream: formal-conjectures statements/oeis-a246776.lean:0 (declaration OMA.S_oeis_a246776.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with P = prime(n) < Q = prime(n+1) and n >= 1, raising to the power n+1 gives
-- Q^(1/(n+1)) < P^(1/n) iff Q < P^(1+1/n). Equality Q = P^(1+1/n) is impossible (it would give
-- Q^n = P^(n+1), so P | Q), hence Q < P^(1+1/n) iff Q <= P^(1+1/n) iff a(n) >= 0. The step n = 1
-- holds anyway (a(1) = 4 - 3), and strict decrease on n >= 1 follows from the steps.

open OMA.S_oeis_a246776 in
theorem OMA.solution : type_of% @OMA.S_oeis_a246776.main := by
  have hinf := Nat.infinite_setOfPred_prime
  have hpr : ∀ n : ℕ, (prime n).Prime := fun n => Nat.prime_nth_prime (n - 1)
  have hlt : ∀ n : ℕ, 1 ≤ n → prime n < prime (n + 1) := by
    intro n hn
    unfold prime
    rw [show n + 1 - 1 = n - 1 + 1 by omega]
    exact Nat.nth_strictMono hinf (by omega)
  have key : ∀ P Q n : ℕ, P.Prime → Q.Prime → P < Q → 1 ≤ n →
      ((Q : ℝ) ^ (1 / ((n : ℝ) + 1)) < (P : ℝ) ^ (1 / (n : ℝ)) ↔
        (Q : ℤ) ≤ ⌊(P : ℝ) ^ (1 + 1 / (n : ℝ))⌋) := by
    intro P Q n hPp hQp hPQ hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hz : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hP0 : (0 : ℝ) < P := Nat.cast_pos.mpr hPp.pos
    have hQ0 : (0 : ℝ) < Q := Nat.cast_pos.mpr hQp.pos
    have e1 : ((Q : ℝ) ^ (1 / ((n : ℝ) + 1))) ^ ((n : ℝ) + 1) = Q := by
      rw [← Real.rpow_mul hQ0.le, one_div_mul_cancel hz.ne', Real.rpow_one]
    have e2 : ((P : ℝ) ^ (1 / (n : ℝ))) ^ ((n : ℝ) + 1) = (P : ℝ) ^ (1 + 1 / (n : ℝ)) := by
      rw [← Real.rpow_mul hP0.le, mul_add, one_div_mul_cancel hn0.ne', mul_one]
    have hne : (Q : ℝ) ≠ (P : ℝ) ^ (1 + 1 / (n : ℝ)) := by
      intro h
      have h2 : (Q : ℝ) ^ n = (P : ℝ) ^ (n + 1) := by
        rw [h, ← Real.rpow_natCast ((P : ℝ) ^ (1 + 1 / (n : ℝ))) n, ← Real.rpow_mul hP0.le,
          add_mul, one_mul, one_div_mul_cancel hn0.ne', ← Nat.cast_add_one, Real.rpow_natCast]
      have h3 : Q ^ n = P ^ (n + 1) := by exact_mod_cast h2
      have h4 : P ∣ Q ^ n := by
        rw [h3]
        exact dvd_pow_self P (by omega)
      have h5 := (Nat.prime_dvd_prime_iff_eq hPp hQp).mp (hPp.dvd_of_dvd_pow h4)
      omega
    rw [Int.le_floor, ← Real.rpow_lt_rpow_iff (Real.rpow_nonneg hQ0.le _)
      (Real.rpow_nonneg hP0.le _) hz, e1, e2]
    push_cast
    constructor
    · intro h
      exact h.le
    · intro h
      exact lt_of_le_of_ne h hne
  have hstep : ∀ n : ℕ, 1 ≤ n →
      ((prime (n + 1) : ℝ) ^ (1 / ((n + 1 : ℕ) : ℝ)) < (prime n : ℝ) ^ (1 / (n : ℝ)) ↔
        0 ≤ a n) := by
    intro n hn
    have h := key (prime n) (prime (n + 1)) n (hpr n) (hpr (n + 1)) (hlt n hn) hn
    unfold a
    rw [sub_nonneg, Nat.cast_add_one]
    exact h
  have ha1 : 0 ≤ a 1 := by
    have h2 : (Nat.nth Nat.Prime (1 - 1) : ℝ) ^ (1 + 1 / ((1 : ℕ) : ℝ)) = 4 := by
      rw [Nat.sub_self, Nat.nth_prime_zero_eq_two, Nat.cast_one, div_one,
        show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have h3 : Nat.nth Nat.Prime (1 + 1 - 1) = 3 := by
      rw [Nat.add_sub_cancel, Nat.nth_prime_one_eq_three]
    unfold a prime
    rw [h2, h3]
    norm_num
  have hmono : ∀ f : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → f (n + 1) < f n) → StrictAntiOn f (Set.Ici 1) := by
    intro f hs x hx y _hy hxy
    have hx1 : 1 ≤ x := Set.mem_Ici.mp hx
    have hg : StrictAnti (fun m : ℕ => f (m + 1)) :=
      strictAnti_nat_of_succ_lt (fun m => hs (m + 1) (by omega))
    have h1 : f (y - 1 + 1) < f (x - 1 + 1) := hg (show x - 1 < y - 1 by omega)
    rw [show y - 1 + 1 = y by omega, show x - 1 + 1 = x by omega] at h1
    exact h1
  constructor
  · intro hF n hn
    have h := hF (Set.mem_Ici.mpr (show 1 ≤ n by omega)) (Set.mem_Ici.mpr (show 1 ≤ n + 1 by omega))
      (show n < n + 1 by omega)
    exact (hstep n (by omega)).mp h
  · intro hA
    apply hmono
    intro n hn
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · exact (hstep n hn).mpr (hA n h1)
    · obtain rfl : n = 1 := by omega
      exact (hstep 1 le_rfl).mpr ha1
