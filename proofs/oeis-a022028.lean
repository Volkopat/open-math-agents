import OMAStatements.S_oeis_a022028

-- Problem: A022028: Define the sequence T(a(0),a(1)) by a(n+2) is the greatest integer such that a(n+2)/a(n+1) < a(n+1)/a(n) for n >= 0. This is T(2,32).
-- Upstream: formal-conjectures statements/oeis-a022028.lean:0 (declaration OMA.S_oeis_a022028.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let b be the linear sequence 2, 32, 511, b(n+3) = 16 b(n+2) - 8 b(n), and
-- D(n) = b(n+1)^2 - b(n) b(n+2). Then D(n+3) = 128 D(n+1) + 64 D(n) (a polynomial identity), and
-- D(0), D(1), D(2) = 2, 1, 256, so D(n) > 0; with b(n+1) >= 15 b(n) an induction gives D(n) <= b(n).
-- But 0 < D(n) <= b(n) says exactly that b(n+2) = ceiling(b(n+1)^2/b(n)) - 1, so a = b. The g.f.
-- follows by comparing coefficients.

open OMA.S_oeis_a022028 in
theorem OMA.solution : type_of% @OMA.S_oeis_a022028.main := by
  obtain ⟨b, hb0, hb1, hb2, hbr⟩ : ∃ b : ℕ → ℤ, b 0 = 2 ∧ b 1 = 32 ∧ b 2 = 511 ∧
      ∀ n, b (n + 3) = 16 * b (n + 2) - 8 * b n :=
    ⟨fun n => (Nat.rec (motive := fun _ => ℤ × ℤ × ℤ) ((2, 32, 511) : ℤ × ℤ × ℤ)
      (fun _ p => (p.2.1, p.2.2, 16 * p.2.2 - 8 * p.1)) n).1, rfl, rfl, rfl, fun _ => rfl⟩
  have inv : ∀ n, 0 < b n ∧ 15 * b n ≤ b (n + 1) ∧ 15 * b (n + 1) ≤ b (n + 2) ∧
      0 < b (n + 1) ^ 2 - b n * b (n + 2) ∧ b (n + 1) ^ 2 - b n * b (n + 2) ≤ b n ∧
      0 < b (n + 2) ^ 2 - b (n + 1) * b (n + 3) ∧
      b (n + 2) ^ 2 - b (n + 1) * b (n + 3) ≤ b (n + 1) ∧
      0 < b (n + 3) ^ 2 - b (n + 2) * b (n + 4) ∧
      b (n + 3) ^ 2 - b (n + 2) * b (n + 4) ≤ b (n + 2) := by
    intro n
    induction n with
    | zero =>
      have h3 : b 3 = 16 * b 2 - 8 * b 0 := hbr 0
      have h4 : b 4 = 16 * b 3 - 8 * b 1 := hbr 1
      norm_num [h4, h3, hb0, hb1, hb2]
    | succ k ih =>
      obtain ⟨p0, p1, p2, q0, q0', q1, q1', q2, q2'⟩ := ih
      have r5 : b (k + 5) = 16 * b (k + 4) - 8 * b (k + 2) := hbr (k + 2)
      have r4 : b (k + 4) = 16 * b (k + 3) - 8 * b (k + 1) := hbr (k + 1)
      have r3 : b (k + 3) = 16 * b (k + 2) - 8 * b k := hbr k
      have hD : b (k + 4) ^ 2 - b (k + 3) * b (k + 5) =
          128 * (b (k + 2) ^ 2 - b (k + 1) * b (k + 3)) + 64 * (b (k + 1) ^ 2 - b k * b (k + 2)) := by
        rw [r5, r4, r3]
        ring
      show 0 < b (k + 1) ∧ 15 * b (k + 1) ≤ b (k + 2) ∧ 15 * b (k + 2) ≤ b (k + 3) ∧
        0 < b (k + 2) ^ 2 - b (k + 1) * b (k + 3) ∧
        b (k + 2) ^ 2 - b (k + 1) * b (k + 3) ≤ b (k + 1) ∧
        0 < b (k + 3) ^ 2 - b (k + 2) * b (k + 4) ∧
        b (k + 3) ^ 2 - b (k + 2) * b (k + 4) ≤ b (k + 2) ∧
        0 < b (k + 4) ^ 2 - b (k + 3) * b (k + 5) ∧
        b (k + 4) ^ 2 - b (k + 3) * b (k + 5) ≤ b (k + 3)
      refine ⟨by linarith, p2, by linarith, q1, q1', q2, q2', by linarith, by linarith⟩
  have ceil_lem : ∀ x y k : ℤ, 0 < y → k * y < x → x ≤ (k + 1) * y →
      ⌈(x : ℚ) / (y : ℚ)⌉ - 1 = k := by
    intro x y k hy h1 h2
    have hy' : (0 : ℚ) < y := by exact_mod_cast hy
    have h1' : (k : ℚ) * y < x := by exact_mod_cast h1
    have h2' : (x : ℚ) ≤ ((k : ℚ) + 1) * y := by exact_mod_cast h2
    have hc : ⌈(x : ℚ) / (y : ℚ)⌉ = k + 1 := by
      rw [Int.ceil_eq_iff]
      constructor
      · rw [lt_div_iff₀ hy']
        push_cast
        linarith
      · rw [div_le_iff₀ hy']
        push_cast
        linarith
    omega
  have ha : ∀ n, a n = b n ∧ a (n + 1) = b (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨(rfl : a 0 = 2).trans hb0.symm, (rfl : a 1 = 32).trans hb1.symm⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨p0, -, -, q0, q0', -⟩ := inv k
      show ⌈((a (k + 1) : ℚ) ^ 2 / (a k : ℚ))⌉ - 1 = b (k + 2)
      rw [ih.1, ih.2]
      have h := ceil_lem (b (k + 1) ^ 2) (b k) (b (k + 2)) p0 (by linarith) (by linarith)
      push_cast at h
      exact h
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 3 = m by omega, (ha (m + 3)).1,
      (ha (m + 2)).1, (ha m).1]
    exact hbr m
  · have hrec : ∀ m, (a (m + 3) : ℚ) = 16 * (a (m + 2) : ℚ) - 8 * (a m : ℚ) := by
      intro m
      rw [(ha (m + 3)).1, (ha (m + 2)).1, (ha m).1]
      exact_mod_cast hbr m
    have a0 : (a 0 : ℚ) = 2 := by
      have h : a 0 = 2 := (ha 0).1.trans hb0
      exact_mod_cast h
    have a1 : (a 1 : ℚ) = 32 := by
      have h : a 1 = 32 := (ha 1).1.trans hb1
      exact_mod_cast h
    have a2 : (a 2 : ℚ) = 511 := by
      have h : a 2 = 511 := (ha 2).1.trans hb2
      exact_mod_cast h
    have e : PowerSeries.mk (fun n => (a n : ℚ)) *
        (8 * PowerSeries.X ^ 3 - 16 * PowerSeries.X + 1) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
          + PowerSeries.mk (fun n => (a n : ℚ)) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16]
      ring
    have e2 : -(PowerSeries.X ^ 2 - 2 : PowerSeries ℚ) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 - PowerSeries.X ^ 2 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m
      · norm_num [a0]
      · norm_num [a0, a1]
      · norm_num [a1, a2]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      rw [if_pos (show 3 ≤ k + 3 by omega), if_pos (show 1 ≤ k + 3 by omega),
        if_neg (show ¬ (k + 3 = 0) by omega), if_neg (show ¬ (k + 3 = 2) by omega),
        show k + 3 - 3 = k by omega, show k + 3 - 1 = k + 2 by omega, hrec k]
      ring
