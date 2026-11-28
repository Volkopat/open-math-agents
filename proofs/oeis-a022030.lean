import OMAStatements.S_oeis_a022030

-- Problem: A022030: For even n, a(n+2) is the greatest integer such that a(n+2)/a(n+1) < a(n+1)/a(n); for odd n, the least integer such that a(n+2)/a(n+1) > a(n+1)/a(n); a(0) = 4, a(1) = 16.
-- Upstream: formal-conjectures statements/oeis-a022030.lean:0 (declaration OMA.S_oeis_a022030.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea. Barker's part: b is the linear sequence 4, 16, 63, 249, b(n+4) = 4b(n+3) - b(n+1) + b(n),
-- D(n) = b(n+1)^2 - b(n)b(n+2) and G(n) = (-1)^n D(n). G satisfies a linear recurrence of order 6, and
-- multiplying it by 10x^4 + 30x^2 + 5x + 2 gives 10G(n+10) = 145G(n+7) + 58G(n+6) + 465G(n+5) + G(n+4)
-- + 15G(n+3) + 24G(n+2) + 5G(n+1) + 2G(n) with nonnegative coefficients; with 39b(n) <= 10b(n+1) this
-- carries 0 < G(n) <= b(n) from n..n+9 to n+10. That is the window of the mixed rule (0 < D <= b for even
-- n, -b <= D < 0 for odd n), so a = b. Hasler's part: t' is the linear sequence 4, 16, 63,
-- t'(n+3) = 4t'(n+2) - t'(n); its D satisfies D(n+3) = 4D(n+1) + D(n), so 0 < D(n) <= t'(n) by
-- induction, which is the window of the original rule, so t = t'. The g.f.s follow by comparing
-- coefficients.

namespace P1A022030

/-- Barker's linear sequence as 4-tuples. -/
def bt : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (4, 16, 63, 249)
  | n + 1 => ((bt n).2.1, (bt n).2.2.1, (bt n).2.2.2,
      4 * (bt n).2.2.2 - (bt n).2.1 + (bt n).1)

/-- b(n). -/
def b (n : ℕ) : ℤ := (bt n).1

theorem b_rec (n : ℕ) : b (n + 4) = 4 * b (n + 3) - b (n + 1) + b n := rfl

theorem b_grow (n : ℕ) : 0 < b n ∧ 39 * b n ≤ 10 * b (n + 1) ∧ 39 * b (n + 1) ≤ 10 * b (n + 2) ∧
    39 * b (n + 2) ≤ 10 * b (n + 3) := by
  induction n with
  | zero => decide
  | succ k ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    have r : b (k + 4) = 4 * b (k + 3) - b (k + 1) + b k := b_rec k
    show 0 < b (k + 1) ∧ 39 * b (k + 1) ≤ 10 * b (k + 2) ∧ 39 * b (k + 2) ≤ 10 * b (k + 3) ∧
      39 * b (k + 3) ≤ 10 * b (k + 4)
    refine ⟨by omega, h2, h3, by omega⟩

theorem b_step (n : ℕ) : 0 < b n ∧ 39 * b n ≤ 10 * b (n + 1) :=
  ⟨(b_grow n).1, (b_grow n).2.1⟩

/-- D(n) = b(n+1)^2 - b(n) b(n+2). -/
def D (n : ℕ) : ℤ := b (n + 1) ^ 2 - b n * b (n + 2)

/-- G(n) = (-1)^n D(n). -/
def G (n : ℕ) : ℤ := (-1) ^ n * D n

theorem D_rec (n : ℕ) : D (n + 6) = D n - 3 * D (n + 2) - 15 * D (n + 3) + 3 * D (n + 4) := by
  have e0 : D n = b (n + 1) ^ 2 - b n * b (n + 2) := rfl
  have e2 : D (n + 2) = b (n + 3) ^ 2 - b (n + 2) * b (n + 4) := rfl
  have e3 : D (n + 3) = b (n + 4) ^ 2 - b (n + 3) * b (n + 5) := rfl
  have e4 : D (n + 4) = b (n + 5) ^ 2 - b (n + 4) * b (n + 6) := rfl
  have e6 : D (n + 6) = b (n + 7) ^ 2 - b (n + 6) * b (n + 8) := rfl
  have h8 : b (n + 8) = 4 * b (n + 7) - b (n + 5) + b (n + 4) := b_rec (n + 4)
  have h7 : b (n + 7) = 4 * b (n + 6) - b (n + 4) + b (n + 3) := b_rec (n + 3)
  have h6 : b (n + 6) = 4 * b (n + 5) - b (n + 3) + b (n + 2) := b_rec (n + 2)
  have h5 : b (n + 5) = 4 * b (n + 4) - b (n + 2) + b (n + 1) := b_rec (n + 1)
  have h4 : b (n + 4) = 4 * b (n + 3) - b (n + 1) + b n := b_rec n
  rw [e0, e2, e3, e4, e6, h8, h7, h6, h5, h4]
  ring

theorem G_rec (n : ℕ) : G (n + 6) = G n - 3 * G (n + 2) + 15 * G (n + 3) + 3 * G (n + 4) := by
  unfold G
  rw [D_rec n]
  ring

theorem G_mul (n : ℕ) : 10 * G (n + 10) = 145 * G (n + 7) + 58 * G (n + 6) + 465 * G (n + 5) +
    G (n + 4) + 15 * G (n + 3) + 24 * G (n + 2) + 5 * G (n + 1) + 2 * G n := by
  have r0 : G (n + 6) = G n - 3 * G (n + 2) + 15 * G (n + 3) + 3 * G (n + 4) := G_rec n
  have r1 : G (n + 7) = G (n + 1) - 3 * G (n + 3) + 15 * G (n + 4) + 3 * G (n + 5) := G_rec (n + 1)
  have r2 : G (n + 8) = G (n + 2) - 3 * G (n + 4) + 15 * G (n + 5) + 3 * G (n + 6) := G_rec (n + 2)
  have r4 : G (n + 10) = G (n + 4) - 3 * G (n + 6) + 15 * G (n + 7) + 3 * G (n + 8) :=
    G_rec (n + 4)
  linear_combination 10 * r4 + 30 * r2 + 5 * r1 + 2 * r0

theorem G_win (n : ℕ) : ∀ j, j < 10 → 0 < G (n + j) ∧ G (n + j) ≤ b (n + j) := by
  induction n with
  | zero => decide
  | succ k ih =>
    intro j hj
    rcases Nat.lt_or_ge j 9 with h | h
    · have e : k + 1 + j = k + (j + 1) := by omega
      rw [e]
      exact ih (j + 1) (by omega)
    · obtain rfl : j = 9 := by omega
      have g0 : 0 < G k ∧ G k ≤ b k := ih 0 (by omega)
      have g1 : 0 < G (k + 1) ∧ G (k + 1) ≤ b (k + 1) := ih 1 (by omega)
      have g2 : 0 < G (k + 2) ∧ G (k + 2) ≤ b (k + 2) := ih 2 (by omega)
      have g3 : 0 < G (k + 3) ∧ G (k + 3) ≤ b (k + 3) := ih 3 (by omega)
      have g4 : 0 < G (k + 4) ∧ G (k + 4) ≤ b (k + 4) := ih 4 (by omega)
      have g5 : 0 < G (k + 5) ∧ G (k + 5) ≤ b (k + 5) := ih 5 (by omega)
      have g6 : 0 < G (k + 6) ∧ G (k + 6) ≤ b (k + 6) := ih 6 (by omega)
      have g7 : 0 < G (k + 7) ∧ G (k + 7) ≤ b (k + 7) := ih 7 (by omega)
      have s0 : 0 < b k ∧ 39 * b k ≤ 10 * b (k + 1) := b_step k
      have s1 : 0 < b (k + 1) ∧ 39 * b (k + 1) ≤ 10 * b (k + 2) := b_step (k + 1)
      have s2 : 0 < b (k + 2) ∧ 39 * b (k + 2) ≤ 10 * b (k + 3) := b_step (k + 2)
      have s3 : 0 < b (k + 3) ∧ 39 * b (k + 3) ≤ 10 * b (k + 4) := b_step (k + 3)
      have s4 : 0 < b (k + 4) ∧ 39 * b (k + 4) ≤ 10 * b (k + 5) := b_step (k + 4)
      have s5 : 0 < b (k + 5) ∧ 39 * b (k + 5) ≤ 10 * b (k + 6) := b_step (k + 5)
      have s6 : 0 < b (k + 6) ∧ 39 * b (k + 6) ≤ 10 * b (k + 7) := b_step (k + 6)
      have s7 : 0 < b (k + 7) ∧ 39 * b (k + 7) ≤ 10 * b (k + 8) := b_step (k + 7)
      have s8 : 0 < b (k + 8) ∧ 39 * b (k + 8) ≤ 10 * b (k + 9) := b_step (k + 8)
      have s9 : 0 < b (k + 9) ∧ 39 * b (k + 9) ≤ 10 * b (k + 10) := b_step (k + 9)
      have hm := G_mul k
      show 0 < G (k + 10) ∧ G (k + 10) ≤ b (k + 10)
      constructor
      · linarith [g0.1, g1.1, g2.1, g3.1, g4.1, g5.1, g6.1, g7.1]
      · linarith [g0.2, g1.2, g2.2, g3.2, g4.2, g5.2, g6.2, g7.2, s0.1, s1.2, s2.2, s3.2, s4.2,
          s5.2, s6.2, s7.2, s8.2, s9.2, s0.2]

theorem window (n : ℕ) : 0 < b n ∧ (n % 2 = 0 → 0 < D n ∧ D n ≤ b n) ∧
    (n % 2 = 1 → -b n ≤ D n ∧ D n < 0) := by
  have hg : 0 < G n ∧ G n ≤ b n := G_win n 0 (by omega)
  have hb : 0 < b n := (b_grow n).1
  refine ⟨hb, fun h => ?_, fun h => ?_⟩
  · have he : Even n := Nat.even_iff.mpr h
    have e : G n = D n := by
      unfold G
      rw [he.neg_one_pow, one_mul]
    rw [e] at hg
    exact hg
  · have ho : Odd n := Nat.odd_iff.mpr h
    have e : G n = -D n := by
      unfold G
      rw [ho.neg_one_pow, neg_one_mul]
    rw [e] at hg
    constructor
    · linarith [hg.2]
    · linarith [hg.1]

/-- Hasler's linear sequence as triples. -/
def tt : ℕ → ℤ × ℤ × ℤ
  | 0 => (4, 16, 63)
  | n + 1 => ((tt n).2.1, (tt n).2.2, 4 * (tt n).2.2 - (tt n).1)

/-- t'(n). -/
def tb (n : ℕ) : ℤ := (tt n).1

theorem tb_rec (n : ℕ) : tb (n + 3) = 4 * tb (n + 2) - tb n := rfl

theorem tinv (n : ℕ) : 0 < tb n ∧ 3 * tb n ≤ tb (n + 1) ∧ 3 * tb (n + 1) ≤ tb (n + 2) ∧
    0 < tb (n + 1) ^ 2 - tb n * tb (n + 2) ∧ tb (n + 1) ^ 2 - tb n * tb (n + 2) ≤ tb n ∧
    0 < tb (n + 2) ^ 2 - tb (n + 1) * tb (n + 3) ∧
    tb (n + 2) ^ 2 - tb (n + 1) * tb (n + 3) ≤ tb (n + 1) ∧
    0 < tb (n + 3) ^ 2 - tb (n + 2) * tb (n + 4) ∧
    tb (n + 3) ^ 2 - tb (n + 2) * tb (n + 4) ≤ tb (n + 2) := by
  induction n with
  | zero => decide
  | succ k ih =>
    obtain ⟨p0, p1, p2, q0, q0', q1, q1', q2, q2'⟩ := ih
    have r5 : tb (k + 5) = 4 * tb (k + 4) - tb (k + 2) := tb_rec (k + 2)
    have r4 : tb (k + 4) = 4 * tb (k + 3) - tb (k + 1) := tb_rec (k + 1)
    have r3 : tb (k + 3) = 4 * tb (k + 2) - tb k := tb_rec k
    have hD : tb (k + 4) ^ 2 - tb (k + 3) * tb (k + 5) =
        4 * (tb (k + 2) ^ 2 - tb (k + 1) * tb (k + 3)) + (tb (k + 1) ^ 2 - tb k * tb (k + 2)) := by
      rw [r5, r4, r3]
      ring
    show 0 < tb (k + 1) ∧ 3 * tb (k + 1) ≤ tb (k + 2) ∧ 3 * tb (k + 2) ≤ tb (k + 3) ∧
      0 < tb (k + 2) ^ 2 - tb (k + 1) * tb (k + 3) ∧
      tb (k + 2) ^ 2 - tb (k + 1) * tb (k + 3) ≤ tb (k + 1) ∧
      0 < tb (k + 3) ^ 2 - tb (k + 2) * tb (k + 4) ∧
      tb (k + 3) ^ 2 - tb (k + 2) * tb (k + 4) ≤ tb (k + 2) ∧
      0 < tb (k + 4) ^ 2 - tb (k + 3) * tb (k + 5) ∧
      tb (k + 4) ^ 2 - tb (k + 3) * tb (k + 5) ≤ tb (k + 3)
    refine ⟨by linarith, p2, by linarith, q1, q1', q2, q2', by linarith, by linarith⟩

theorem ceil1_lem (x y m : ℤ) (hy : 0 < y) (h1 : 0 < x - y * m) (h2 : x - y * m ≤ y) :
    ⌈(x : ℚ) / (y : ℚ)⌉ - 1 = m := by
  have hy' : (0 : ℚ) < y := by exact_mod_cast hy
  have h1' : (0 : ℚ) < (x : ℚ) - (y : ℚ) * (m : ℚ) := by exact_mod_cast h1
  have h2' : (x : ℚ) - (y : ℚ) * (m : ℚ) ≤ (y : ℚ) := by exact_mod_cast h2
  have hc : ⌈(x : ℚ) / (y : ℚ)⌉ = m + 1 := by
    rw [Int.ceil_eq_iff]
    constructor
    · rw [lt_div_iff₀ hy']
      push_cast
      linarith
    · rw [div_le_iff₀ hy']
      push_cast
      linarith
  omega

theorem floor1_lem (x y m : ℤ) (hy : 0 < y) (h1 : -y ≤ x - y * m) (h2 : x - y * m < 0) :
    ⌊(x : ℚ) / (y : ℚ)⌋ + 1 = m := by
  have hy' : (0 : ℚ) < y := by exact_mod_cast hy
  have h1' : -(y : ℚ) ≤ (x : ℚ) - (y : ℚ) * (m : ℚ) := by exact_mod_cast h1
  have h2' : (x : ℚ) - (y : ℚ) * (m : ℚ) < 0 := by exact_mod_cast h2
  have hc : ⌊(x : ℚ) / (y : ℚ)⌋ = m - 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hy']
      push_cast
      linarith
    · rw [div_lt_iff₀ hy']
      push_cast
      linarith
  omega

end P1A022030

open OMA.S_oeis_a022030 P1A022030 in
theorem OMA.solution : type_of% @OMA.S_oeis_a022030.main := by
  have ha : ∀ n, a n = b n ∧ a (n + 1) = b (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨hp, hev, hod⟩ := window k
      show (if k % 2 = 0 then ⌈((a (k + 1) : ℚ) ^ 2 / (a k : ℚ))⌉ - 1
          else ⌊((a (k + 1) : ℚ) ^ 2 / (a k : ℚ))⌋ + 1) = b (k + 2)
      rw [ih.1, ih.2]
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · rw [if_pos h]
        obtain ⟨d1, d2⟩ := hev h
        have e := ceil1_lem (b (k + 1) ^ 2) (b k) (b (k + 2)) hp d1 d2
        push_cast at e
        exact e
      · rw [if_neg (show ¬ (k % 2 = 0) by omega)]
        obtain ⟨d1, d2⟩ := hod h
        have e := floor1_lem (b (k + 1) ^ 2) (b k) (b (k + 2)) hp d1 d2
        push_cast at e
        exact e
  have ht : ∀ n, t n = tb n ∧ t (n + 1) = tb (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨hp, -, -, d1, d2, -⟩ := tinv k
      show ⌈((t (k + 1) : ℚ) ^ 2 / (t k : ℚ))⌉ - 1 = tb (k + 2)
      rw [ih.1, ih.2]
      have e := ceil1_lem (tb (k + 1) ^ 2) (tb k) (tb (k + 2)) hp d1 d2
      push_cast at e
      exact e
  have hrec : ∀ m, (a (m + 4) : ℚ) = 4 * (a (m + 3) : ℚ) - (a (m + 1) : ℚ) + (a m : ℚ) := by
    intro m
    rw [(ha (m + 4)).1, (ha (m + 3)).1, (ha (m + 1)).1, (ha m).1]
    exact_mod_cast b_rec m
  have hrecT : ∀ m, (t (m + 3) : ℚ) = 4 * (t (m + 2) : ℚ) - (t m : ℚ) := by
    intro m
    rw [(ht (m + 3)).1, (ht (m + 2)).1, (ht m).1]
    exact_mod_cast tb_rec m
  have a0 : (a 0 : ℚ) = 4 := by
    have h : a 0 = 4 := (ha 0).1.trans rfl
    exact_mod_cast h
  have a1 : (a 1 : ℚ) = 16 := by
    have h : a 1 = 16 := (ha 1).1.trans rfl
    exact_mod_cast h
  have a2 : (a 2 : ℚ) = 63 := by
    have h : a 2 = 63 := (ha 2).1.trans rfl
    exact_mod_cast h
  have a3 : (a 3 : ℚ) = 249 := by
    have h : a 3 = 249 := (ha 3).1.trans rfl
    exact_mod_cast h
  have t0 : (t 0 : ℚ) = 4 := by
    have h : t 0 = 4 := (ht 0).1.trans rfl
    exact_mod_cast h
  have t1 : (t 1 : ℚ) = 16 := by
    have h : t 1 = 16 := (ht 1).1.trans rfl
    exact_mod_cast h
  have t2 : (t 2 : ℚ) = 63 := by
    have h : t 2 = 63 := (ht 2).1.trans rfl
    exact_mod_cast h
  refine ⟨fun n hn => ?_, ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega,
      (ha (m + 4)).1, (ha (m + 3)).1, (ha (m + 1)).1, (ha m).1]
    exact b_rec m
  · have e : PowerSeries.mk (fun n => (a n : ℚ)) *
        (1 - 4 * PowerSeries.X + PowerSeries.X ^ 3 - PowerSeries.X ^ 4) =
        PowerSeries.mk (fun n => (a n : ℚ))
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
          + PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3
          - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
      ring
    have e2 : (4 - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℚ) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 + PowerSeries.X ^ 3 - PowerSeries.X ^ 2 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m
      · norm_num [a0]
      · norm_num [a0, a1]
      · norm_num [a1, a2]
      · norm_num [a0, a2, a3]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      rw [if_pos (show 1 ≤ k + 4 by omega), if_pos (show 3 ≤ k + 4 by omega),
        if_pos (show 4 ≤ k + 4 by omega), if_neg (show ¬ (k + 4 = 0) by omega),
        if_neg (show ¬ (k + 4 = 2) by omega), if_neg (show ¬ (k + 4 = 3) by omega),
        show k + 4 - 1 = k + 3 by omega, show k + 4 - 3 = k + 1 by omega,
        show k + 4 - 4 = k by omega, hrec k]
      ring
  · have e : PowerSeries.mk (fun n => (t n : ℚ)) * (1 - 4 * PowerSeries.X + PowerSeries.X ^ 3) =
        PowerSeries.mk (fun n => (t n : ℚ))
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 *
            (PowerSeries.mk (fun n => (t n : ℚ)) * PowerSeries.X ^ 1)
          + PowerSeries.mk (fun n => (t n : ℚ)) * PowerSeries.X ^ 3 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
      ring
    have e2 : (4 - PowerSeries.X ^ 2 : PowerSeries ℚ) =
        -PowerSeries.X ^ 2 + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m
      · norm_num [t0]
      · norm_num [t0, t1]
      · norm_num [t1, t2]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      rw [if_pos (show 1 ≤ k + 3 by omega), if_pos (show 3 ≤ k + 3 by omega),
        if_neg (show ¬ (k + 3 = 0) by omega), if_neg (show ¬ (k + 3 = 2) by omega),
        show k + 3 - 1 = k + 2 by omega, show k + 3 - 3 = k by omega, hrecT k]
      ring
