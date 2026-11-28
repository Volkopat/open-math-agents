import OMAStatements.S_oeis_a235089

-- Problem: A235089: a(n)*Pi is the total length of irregular spiral (center points: 2, 1, 3, 4) after n rotations.
-- Upstream: formal-conjectures statements/oeis-a235089.lean:0 (declaration OMA.S_oeis_a235089.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (as in the entry, where Sela Fried shows Barker's conjectures): by induction,
-- a(n) = 5n - 2 (n mod 2) for all n (the steps alternate 7 and 3). Every claim is then linear
-- arithmetic with n mod 2, n div 2 and k mod 10 (omega), except (-1)^n (a parity split) and the g.f.
-- (comparing coefficients).

namespace N10A235089

open OMA.S_oeis_a235089

theorem a_succ2 (n : ℕ) : a (n + 2) = a (n + 1) + (if (n + 2) % 2 = 0 then 7 else 3) := rfl

theorem a_closed (n : ℕ) : a (n + 1) = 5 * (n + 1) - 2 * ((n + 1) % 2) := by
  induction n with
  | zero => decide
  | succ k ih =>
    show a (k + 2) = 5 * (k + 1 + 1) - 2 * ((k + 1 + 1) % 2)
    rw [a_succ2 k, ih]
    rcases Nat.mod_two_eq_zero_or_one (k + 2) with h | h
    · rw [if_pos h]
      omega
    · rw [if_neg (show ¬ ((k + 2) % 2 = 0) by omega)]
      omega

theorem hc (n : ℕ) : a n = 5 * n - 2 * (n % 2) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_closed m

end N10A235089

open OMA.S_oeis_a235089 N10A235089 in
theorem OMA.solution : type_of% @OMA.S_oeis_a235089.main := by
  refine ⟨⟨fun n hn => ?_, fun k => ⟨?_, ?_⟩⟩, fun n hn => ?_, fun n hn => ?_, ?_, fun n hn => ?_⟩
  · have h1 := hc n
    have h2 := hc (n + 1)
    omega
  · rintro ⟨n, hn, rfl⟩
    rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
    · have h1 := hc (2 * j)
      have h2 : a (2 * j) = 10 * j := by omega
      rw [h2]
      omega
    · have h1 := hc (2 * j + 1)
      have h2 : a (2 * j + 1) = 10 * j + 3 := by omega
      rw [h2]
      omega
  · rintro ⟨hk, h | h⟩
    · refine ⟨k / 5, by omega, ?_⟩
      have h1 := hc (k / 5)
      omega
    · refine ⟨(k + 2) / 5, by omega, ?_⟩
      have h1 := hc ((k + 2) / 5)
      omega
  · have h1 := hc n
    rcases Nat.even_or_odd n with he | ho
    · have h2 := Nat.even_iff.mp he
      rw [he.neg_one_pow]
      omega
    · have h2 := Nat.odd_iff.mp ho
      rw [ho.neg_one_pow]
      omega
  · have h1 := hc n
    have h2 := hc (n - 1)
    have h3 := hc (n - 2)
    have h4 := hc (n - 3)
    omega
  · have hq : ∀ m : ℕ, (a (m + 3) : ℚ) = (a (m + 2) : ℚ) + (a (m + 1) : ℚ) - (a m : ℚ) := by
      intro m
      have h1 := hc (m + 3)
      have h2 := hc (m + 2)
      have h3 := hc (m + 1)
      have h4 := hc m
      have hz : (a (m + 3) : ℤ) = (a (m + 2) : ℤ) + (a (m + 1) : ℤ) - (a m : ℤ) := by
        omega
      have hz' := congrArg (fun z : ℤ => (z : ℚ)) hz
      push_cast at hz'
      linear_combination hz'
    have q1 : (a 1 : ℚ) = 3 := by
      have h : a 1 = 3 := rfl
      exact_mod_cast h
    have q2 : (a 2 : ℚ) = 10 := by
      have h : a 2 = 10 := by decide
      exact_mod_cast h
    obtain ⟨A, hA⟩ : ∃ A : PowerSeries ℚ,
        A = PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) := ⟨_, rfl⟩
    rw [← hA]
    have cA : ∀ m, PowerSeries.coeff m A = if m = 0 then (0 : ℚ) else (a m : ℚ) := by
      intro m
      rw [hA, PowerSeries.coeff_mk]
    have cA' : ∀ m, PowerSeries.coeff m A = (a m : ℚ) := by
      intro m
      rw [cA]
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        rw [if_pos rfl]
        have h0 : a 0 = 0 := rfl
        rw [h0, Nat.cast_zero]
      · rw [if_neg (show ¬ (m = 0) by omega)]
    have h3 : (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat _ 3
    have h7 : (PowerSeries.C (7 : ℚ) : PowerSeries ℚ) = 7 := map_ofNat _ 7
    have e : A * ((PowerSeries.X - 1) ^ 2 * (PowerSeries.X + 1)) =
        A - A * PowerSeries.X ^ 1 - A * PowerSeries.X ^ 2 + A * PowerSeries.X ^ 3 := by
      ring
    have e2 : (PowerSeries.X * (7 * PowerSeries.X + 3) : PowerSeries ℚ) =
        PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 2 := by
      rw [h3, h7]
      ring
    refine e.trans (Eq.trans ?_ e2.symm)
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul]
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m <;> simp only [PowerSeries.coeff_mul_X_pow', cA, PowerSeries.coeff_X_pow] <;>
        norm_num [q1, q2]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      have t1 : PowerSeries.coeff (k + 3) (A * PowerSeries.X ^ 1) = (a (k + 2) : ℚ) := by
        rw [show k + 3 = k + 2 + 1 by omega, PowerSeries.coeff_mul_X_pow, cA']
      have t2 : PowerSeries.coeff (k + 3) (A * PowerSeries.X ^ 2) = (a (k + 1) : ℚ) := by
        rw [show k + 3 = k + 1 + 2 by omega, PowerSeries.coeff_mul_X_pow, cA']
      have t3 : PowerSeries.coeff (k + 3) (A * PowerSeries.X ^ 3) = (a k : ℚ) := by
        rw [PowerSeries.coeff_mul_X_pow, cA']
      have u1 : PowerSeries.coeff (k + 3) (PowerSeries.X ^ 1 : PowerSeries ℚ) = 0 := by
        rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 3 = 1) by omega)]
      have u2 : PowerSeries.coeff (k + 3) (PowerSeries.X ^ 2 : PowerSeries ℚ) = 0 := by
        rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 3 = 2) by omega)]
      rw [cA' (k + 3), t1, t2, t3, u1, u2, hq k]
      ring
  · have h1 := hc n
    omega
