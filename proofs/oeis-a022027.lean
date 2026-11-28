import OMAStatements.S_oeis_a022027

-- Problem: A022027: Define the sequence T(a(0),a(1)) by a(n+2) is the greatest integer such that a(n+2)/a(n+1) < a(n+1)/a(n) for n >= 0. This is T(2,16).
-- Upstream: formal-conjectures statements/oeis-a022027.lean:0 (declaration OMA.S_oeis_a022027.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let b be the linear sequence 2, 16, 127, b(n+3) = 8 b(n+2) - 4 b(n), and
-- D(n) = b(n+1)^2 - b(n) b(n+2). Then D(n+3) = 32 D(n+1) + 16 D(n) (a polynomial identity), and
-- D(0), D(1), D(2) = 2, 1, 64, so D(n) > 0; with b(n+1) >= 7 b(n) an induction gives D(n) <= b(n).
-- But 0 < D(n) <= b(n) says exactly that b(n+2) = ceiling(b(n+1)^2/b(n)) - 1, so a = b. The g.f.
-- follows by comparing coefficients.

open OMA.S_oeis_a022027 in
theorem OMA.solution : type_of% @OMA.S_oeis_a022027.main := by
  obtain ⟨b, hb0, hb1, hb2, hbr⟩ : ∃ b : ℕ → ℤ, b 0 = 2 ∧ b 1 = 16 ∧ b 2 = 127 ∧
      ∀ n, b (n + 3) = 8 * b (n + 2) - 4 * b n :=
    ⟨fun n => (Nat.rec (motive := fun _ => ℤ × ℤ × ℤ) ((2, 16, 127) : ℤ × ℤ × ℤ)
      (fun _ p => (p.2.1, p.2.2, 8 * p.2.2 - 4 * p.1)) n).1, rfl, rfl, rfl, fun _ => rfl⟩
  have inv : ∀ n, 0 < b n ∧ 7 * b n ≤ b (n + 1) ∧ 7 * b (n + 1) ≤ b (n + 2) ∧
      0 < b (n + 1) ^ 2 - b n * b (n + 2) ∧ b (n + 1) ^ 2 - b n * b (n + 2) ≤ b n ∧
      0 < b (n + 2) ^ 2 - b (n + 1) * b (n + 3) ∧
      b (n + 2) ^ 2 - b (n + 1) * b (n + 3) ≤ b (n + 1) ∧
      0 < b (n + 3) ^ 2 - b (n + 2) * b (n + 4) ∧
      b (n + 3) ^ 2 - b (n + 2) * b (n + 4) ≤ b (n + 2) := by
    intro n
    induction n with
    | zero =>
      have h3 : b 3 = 8 * b 2 - 4 * b 0 := hbr 0
      have h4 : b 4 = 8 * b 3 - 4 * b 1 := hbr 1
      norm_num [h4, h3, hb0, hb1, hb2]
    | succ k ih =>
      obtain ⟨p0, p1, p2, q0, q0', q1, q1', q2, q2'⟩ := ih
      have r5 : b (k + 5) = 8 * b (k + 4) - 4 * b (k + 2) := hbr (k + 2)
      have r4 : b (k + 4) = 8 * b (k + 3) - 4 * b (k + 1) := hbr (k + 1)
      have r3 : b (k + 3) = 8 * b (k + 2) - 4 * b k := hbr k
      have hD : b (k + 4) ^ 2 - b (k + 3) * b (k + 5) =
          32 * (b (k + 2) ^ 2 - b (k + 1) * b (k + 3)) + 16 * (b (k + 1) ^ 2 - b k * b (k + 2)) := by
        rw [r5, r4, r3]
        ring
      show 0 < b (k + 1) ∧ 7 * b (k + 1) ≤ b (k + 2) ∧ 7 * b (k + 2) ≤ b (k + 3) ∧
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
    | zero => exact ⟨(rfl : a 0 = 2).trans hb0.symm, (rfl : a 1 = 16).trans hb1.symm⟩
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
  · have hrec : ∀ m, (a (m + 3) : ℚ) = 8 * (a (m + 2) : ℚ) - 4 * (a m : ℚ) := by
      intro m
      rw [(ha (m + 3)).1, (ha (m + 2)).1, (ha m).1]
      exact_mod_cast hbr m
    have a0 : (a 0 : ℚ) = 2 := by
      have h : a 0 = 2 := (ha 0).1.trans hb0
      exact_mod_cast h
    have a1 : (a 1 : ℚ) = 16 := by
      have h : a 1 = 16 := (ha 1).1.trans hb1
      exact_mod_cast h
    have a2 : (a 2 : ℚ) = 127 := by
      have h : a 2 = 127 := (ha 2).1.trans hb2
      exact_mod_cast h
    have e : PowerSeries.mk (fun n => (a n : ℚ)) *
        (4 * PowerSeries.X ^ 3 - 8 * PowerSeries.X + 1) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
          + PowerSeries.mk (fun n => (a n : ℚ)) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8]
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
