import OMAStatements.S_oeis_a021008

-- Problem: A021008: Pisot sequence P(5,11), a(0)=5, a(1)=11, a(n+1) is the nearest integer to a(n)^2/a(n-1).
-- Upstream: formal-conjectures statements/oeis-a021008.lean:0 (declaration OMA.S_oeis_a021008.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let b be the linear sequence 5, 11, 24, 52, b(n+4) = 3b(n+3) - 2b(n+2) + b(n), and
-- D(n) = b(n+1)^2 - b(n)b(n+2). D satisfies its own linear recurrence of order 6 (a polynomial
-- identity). A positive definite quadratic form V with V(C y) <= (13/6)^2 V(y) for the companion map C
-- of that recurrence, D(n)^2 <= c V and growth b(n+1) >= (13/6) b(n) + 1 give by induction from
-- n = 22 on: V(D(n..n+5)) <= 204 b(n)^2, hence |2 D(n)| < b(n) (as c 61 / 50000 * 204 < 1/4); for n < 22 it
-- is checked directly. But -b(n) < 2 D(n) <= b(n) says b(n+2) = ceiling(b(n+1)^2/b(n) - 1/2), so a = b,
-- and the recurrence and the g.f. follow (the g.f. by comparing coefficients).

namespace P1A021008

/-- The linear sequence 5, 11, 24, 52, ... as 4-tuples (b(n), b(n+1), b(n+2), b(n+3)). -/
def bt : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (5, 11, 24, 52)
  | n + 1 => ((bt n).2.1, (bt n).2.2.1, (bt n).2.2.2,
      3 * (bt n).2.2.2 - 2 * (bt n).2.2.1 + (bt n).1)

/-- b(n). -/
def b (n : ℕ) : ℤ := (bt n).1

theorem b_rec (n : ℕ) : b (n + 4) = 3 * b (n + 3) - 2 * b (n + 2) + b n := rfl

theorem bq_rec (n : ℕ) :
    (b (n + 4) : ℚ) = 3 * (b (n + 3) : ℚ) - 2 * (b (n + 2) : ℚ) + (b n : ℚ) := by
  exact_mod_cast b_rec n

/-- D(n) = b(n+1)^2 - b(n) b(n+2), in ℚ. -/
def Dq (n : ℕ) : ℚ := (b (n + 1) : ℚ) ^ 2 - (b n : ℚ) * (b (n + 2) : ℚ)

theorem Dq_rec (n : ℕ) :
    Dq (n + 6) = Dq n + 2 * Dq (n + 1) + Dq (n + 2) - 5 * Dq (n + 3) - Dq (n + 4) + 2 * Dq (n + 5) := by
  have e0 : Dq (n) = (b (n + 1) : ℚ) ^ 2 - (b (n) : ℚ) * (b (n + 2) : ℚ) := rfl
  have e1 : Dq (n + 1) = (b (n + 2) : ℚ) ^ 2 - (b (n + 1) : ℚ) * (b (n + 3) : ℚ) := rfl
  have e2 : Dq (n + 2) = (b (n + 3) : ℚ) ^ 2 - (b (n + 2) : ℚ) * (b (n + 4) : ℚ) := rfl
  have e3 : Dq (n + 3) = (b (n + 4) : ℚ) ^ 2 - (b (n + 3) : ℚ) * (b (n + 5) : ℚ) := rfl
  have e4 : Dq (n + 4) = (b (n + 5) : ℚ) ^ 2 - (b (n + 4) : ℚ) * (b (n + 6) : ℚ) := rfl
  have e5 : Dq (n + 5) = (b (n + 6) : ℚ) ^ 2 - (b (n + 5) : ℚ) * (b (n + 7) : ℚ) := rfl
  have e6 : Dq (n + 6) = (b (n + 7) : ℚ) ^ 2 - (b (n + 6) : ℚ) * (b (n + 8) : ℚ) := rfl
  have h8 : (b (n + 8) : ℚ) = 3 * (b (n + 7) : ℚ) - 2 * (b (n + 6) : ℚ) + (b (n + 4) : ℚ) :=
    bq_rec (n + 4)
  have h7 : (b (n + 7) : ℚ) = 3 * (b (n + 6) : ℚ) - 2 * (b (n + 5) : ℚ) + (b (n + 3) : ℚ) :=
    bq_rec (n + 3)
  have h6 : (b (n + 6) : ℚ) = 3 * (b (n + 5) : ℚ) - 2 * (b (n + 4) : ℚ) + (b (n + 2) : ℚ) :=
    bq_rec (n + 2)
  have h5 : (b (n + 5) : ℚ) = 3 * (b (n + 4) : ℚ) - 2 * (b (n + 3) : ℚ) + (b (n + 1) : ℚ) :=
    bq_rec (n + 1)
  have h4 : (b (n + 4) : ℚ) = 3 * (b (n + 3) : ℚ) - 2 * (b (n + 2) : ℚ) + (b (n) : ℚ) :=
    bq_rec n
  rw [e0, e1, e2, e3, e4, e5, e6, h8, h7, h6, h5, h4]
  ring

/-- The quadratic form. -/
def V (y0 y1 y2 y3 y4 y5 : ℚ) : ℚ :=
  1624 * y0 ^ 2 + 2292 * y0 * y1 - 4934 * y0 * y2 - 1196 * y0 * y3 + 2142 * y0 * y4 - 948 * y0 *
    y5 + 4568 * y1 ^ 2 - 6366 * y1 * y2 - 4796 * y1 * y3 + 4882 * y1 * y4 - 1646 * y1 * y5 + 10000 *
    y2 ^ 2 + 5010 * y2 * y3 - 8390 * y2 * y4 + 4058 * y2 * y5 + 2364 * y3 ^ 2 - 4426 * y3 * y4 +
    1634 * y3 * y5 + 2572 * y4 ^ 2 - 2134 * y4 * y5 + 480 * y5 ^ 2

theorem lyap (y0 y1 y2 y3 y4 y5 y6 : ℚ) (h : y6 = y0 + 2 * y1 + y2 - 5 * y3 - y4 + 2 * y5) :
    V y1 y2 y3 y4 y5 y6 ≤ 169 / 36 * V y0 y1 y2 y3 y4 y5 := by
  subst h
  have e : 169 / 36 * V y0 y1 y2 y3 y4 y5 - V y1 y2 y3 y4 y5 (y0 + 2 * y1 + y2 - 5 * y3 - y4 + 2 * y5) =
      64294 / 9 * (y0 + 88089 / 128588 * y1 - 404575 / 257176 * y2 - 43853 / 128588 * y3 + 168867 / 257176 * y4 - 38127 / 128588 * y5) ^ 2 +
      38060347295 / 2314584 * (y1 - 33467541549 / 76120694590 * y2 - 4050202427 / 7612069459 * y3 + 35624911489 / 76120694590 * y4 - 5373263131 / 38060347295 * y5) ^ 2 +
      10360557896621303 / 456724167540 * (y2 + 4821922754102725 / 31081673689863909 * y3 - 10539945577028879 / 31081673689863909 * y4 + 12288182584540969 / 62163347379727818 * y5) ^ 2 +
      3754659651224530478425 / 1118940252835100724 * (y3 - 2564599213679604524888 / 3754659651224530478425 * y4 + 1754778056320608390637 / 7509319302449060956850 * y5) ^ 2 +
      564174485571665879976317 / 67583873722041548611650 * (y4 - 470056796283426178983883 / 1128348971143331759952634 * y5) ^ 2 +
      99523780903753824724208791 / 40620562961159943358294824 * (y5) ^ 2 := by
    unfold V
    ring
  have hs : 0 ≤ 64294 / 9 * (y0 + 88089 / 128588 * y1 - 404575 / 257176 * y2 - 43853 / 128588 * y3 + 168867 / 257176 * y4 - 38127 / 128588 * y5) ^ 2 +
      38060347295 / 2314584 * (y1 - 33467541549 / 76120694590 * y2 - 4050202427 / 7612069459 * y3 + 35624911489 / 76120694590 * y4 - 5373263131 / 38060347295 * y5) ^ 2 +
      10360557896621303 / 456724167540 * (y2 + 4821922754102725 / 31081673689863909 * y3 - 10539945577028879 / 31081673689863909 * y4 + 12288182584540969 / 62163347379727818 * y5) ^ 2 +
      3754659651224530478425 / 1118940252835100724 * (y3 - 2564599213679604524888 / 3754659651224530478425 * y4 + 1754778056320608390637 / 7509319302449060956850 * y5) ^ 2 +
      564174485571665879976317 / 67583873722041548611650 * (y4 - 470056796283426178983883 / 1128348971143331759952634 * y5) ^ 2 +
      99523780903753824724208791 / 40620562961159943358294824 * (y5) ^ 2 := by
    positivity
  linarith

theorem dbound (y0 y1 y2 y3 y4 y5 : ℚ) : y0 ^ 2 ≤ 61 / 50000 * V y0 y1 y2 y3 y4 y5 := by
  have e : 61 / 50000 * V y0 y1 y2 y3 y4 y5 - y0 ^ 2 =
      6133 / 6250 * (y0 + 34953 / 24532 * y1 - 150487 / 49064 * y2 - 18239 / 24532 * y3 + 65331 / 49064 * y4 - 14457 / 24532 * y5) ^ 2 +
      2196184159 / 613300000 * (y1 + 8143695 / 72006038 * y2 - 18962921 / 36003019 * y3 + 22447949 / 72006038 * y4 - 1811057 / 36003019 * y5) ^ 2 +
      5261572283801 / 1800150950000 * (y2 + 30447237109 / 86255283341 * y3 - 36491369683 / 86255283341 * y4 + 42617937221 / 172510566682 * y5) ^ 2 +
      169761785271681 / 172510566682000 * (y3 - 9953832182888 / 13914900432105 * y4 + 10229975435067 / 46383001440350 * y5) ^ 2 +
      1621048632210821 / 69574502160525000 * (y4 - 169225898033361 / 265745677411610 * y5) ^ 2 +
      3225961144279271 / 66436419352902500000 * (y5) ^ 2 := by
    unfold V
    ring
  have hs : 0 ≤ 6133 / 6250 * (y0 + 34953 / 24532 * y1 - 150487 / 49064 * y2 - 18239 / 24532 * y3 + 65331 / 49064 * y4 - 14457 / 24532 * y5) ^ 2 +
      2196184159 / 613300000 * (y1 + 8143695 / 72006038 * y2 - 18962921 / 36003019 * y3 + 22447949 / 72006038 * y4 - 1811057 / 36003019 * y5) ^ 2 +
      5261572283801 / 1800150950000 * (y2 + 30447237109 / 86255283341 * y3 - 36491369683 / 86255283341 * y4 + 42617937221 / 172510566682 * y5) ^ 2 +
      169761785271681 / 172510566682000 * (y3 - 9953832182888 / 13914900432105 * y4 + 10229975435067 / 46383001440350 * y5) ^ 2 +
      1621048632210821 / 69574502160525000 * (y4 - 169225898033361 / 265745677411610 * y5) ^ 2 +
      3225961144279271 / 66436419352902500000 * (y5) ^ 2 := by
    positivity
  linarith

set_option maxRecDepth 20000 in
theorem early : ∀ n, n < 22 → 0 < b n ∧ -b n < 2 * (b (n + 1) ^ 2 - b n * b (n + 2)) ∧
    2 * (b (n + 1) ^ 2 - b n * b (n + 2)) ≤ b n := by
  decide

set_option maxRecDepth 20000 in
theorem base_vals : b 22 = 138205538 ∧ b 23 = 301111747 ∧ b 24 = 656039443 ∧ b 25 = 1429328995 ∧ b 26 = 3114113637 ∧
    b 27 = 6784794668 ∧ b 28 = 14782196173 ∧ b 29 = 32206328178 := by
  decide

theorem invar (n : ℕ) (hn : 22 ≤ n) : 0 < (b n : ℚ) ∧ 13 / 6 * (b n : ℚ) + 1 ≤ (b (n + 1) : ℚ) ∧
    V (Dq n) (Dq (n + 1)) (Dq (n + 2)) (Dq (n + 3)) (Dq (n + 4)) (Dq (n + 5)) ≤ 204 * (b n : ℚ) ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base =>
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := base_vals
    show 0 < (b 22 : ℚ) ∧ 13 / 6 * (b 22 : ℚ) + 1 ≤ (b 23 : ℚ) ∧
      V
        ((b 23 : ℚ) ^ 2 - (b 22 : ℚ) * (b 24 : ℚ))
        ((b 24 : ℚ) ^ 2 - (b 23 : ℚ) * (b 25 : ℚ))
        ((b 25 : ℚ) ^ 2 - (b 24 : ℚ) * (b 26 : ℚ))
        ((b 26 : ℚ) ^ 2 - (b 25 : ℚ) * (b 27 : ℚ))
        ((b 27 : ℚ) ^ 2 - (b 26 : ℚ) * (b 28 : ℚ))
        ((b 28 : ℚ) ^ 2 - (b 27 : ℚ) * (b 29 : ℚ))
        ≤
        204 * (b 22 : ℚ) ^ 2
    rw [v0, v1, v2, v3, v4, v5, v6, v7]
    unfold V
    norm_num
  | succ k _ ih =>
    obtain ⟨hp, hg, hV⟩ := ih
    have hd := dbound (Dq k) (Dq (k + 1)) (Dq (k + 2)) (Dq (k + 3)) (Dq (k + 4)) (Dq (k + 5))
    have hsq0 : 4 * Dq k ^ 2 < (b k : ℚ) ^ 2 := by linarith [pow_pos hp 2]
    have hsq : (2 * Dq k) ^ 2 < (b k : ℚ) ^ 2 := by
      have e2 : (2 * Dq k) ^ 2 = 4 * Dq k ^ 2 := by ring
      rw [e2]
      exact hsq0
    obtain ⟨-, hw2⟩ := abs_lt_of_sq_lt_sq' hsq hp.le
    have hp1 : 0 < (b (k + 1) : ℚ) := by linarith
    have eD : Dq k = (b (k + 1) : ℚ) ^ 2 - (b k : ℚ) * (b (k + 2) : ℚ) := rfl
    have key : (b k : ℚ) * ((b (k + 2) : ℚ) - (13 / 6 * (b (k + 1) : ℚ) + 1)) =
        ((b (k + 1) : ℚ) - 13 / 6 * (b k : ℚ) - 1) * (b (k + 1) : ℚ) + ((b (k + 1) : ℚ) - (b k : ℚ)) -
          Dq k := by
      rw [eD]
      ring
    have hm : 0 ≤ ((b (k + 1) : ℚ) - 13 / 6 * (b k : ℚ) - 1) * (b (k + 1) : ℚ) :=
      mul_nonneg (by linarith) hp1.le
    have hkey : 0 < (b k : ℚ) * ((b (k + 2) : ℚ) - (13 / 6 * (b (k + 1) : ℚ) + 1)) := by
      rw [key]
      linarith
    have hg1 : 13 / 6 * (b (k + 1) : ℚ) + 1 ≤ (b (k + 2) : ℚ) := by
      have h5 := pos_of_mul_pos_right hkey hp.le
      linarith
    have hsq1 : 169 / 36 * (b k : ℚ) ^ 2 ≤ (b (k + 1) : ℚ) ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℚ) ≤ (b (k + 1) : ℚ) - 13 / 6 * (b k : ℚ) by linarith)
        (show (0 : ℚ) ≤ (b (k + 1) : ℚ) + 13 / 6 * (b k : ℚ) by linarith)]
    have hL := lyap (Dq k) (Dq (k + 1)) (Dq (k + 2)) (Dq (k + 3)) (Dq (k + 4)) (Dq (k + 5)) (Dq (k + 6)) (Dq_rec k)
    show 0 < (b (k + 1) : ℚ) ∧ 13 / 6 * (b (k + 1) : ℚ) + 1 ≤ (b (k + 2) : ℚ) ∧
      V (Dq (k + 1)) (Dq (k + 2)) (Dq (k + 3)) (Dq (k + 4)) (Dq (k + 5)) (Dq (k + 6)) ≤ 204 * (b (k + 1) : ℚ) ^ 2
    refine ⟨hp1, hg1, ?_⟩
    linarith

theorem window (n : ℕ) : 0 < b n ∧ -b n < 2 * (b (n + 1) ^ 2 - b n * b (n + 2)) ∧
    2 * (b (n + 1) ^ 2 - b n * b (n + 2)) ≤ b n := by
  rcases Nat.lt_or_ge n 22 with hn | hn
  · exact early n hn
  · obtain ⟨hp, -, hV⟩ := invar n hn
    have hd := dbound (Dq n) (Dq (n + 1)) (Dq (n + 2)) (Dq (n + 3)) (Dq (n + 4)) (Dq (n + 5))
    have hsq0 : 4 * Dq n ^ 2 < (b n : ℚ) ^ 2 := by linarith [pow_pos hp 2]
    have hsq : (2 * Dq n) ^ 2 < (b n : ℚ) ^ 2 := by
      have e2 : (2 * Dq n) ^ 2 = 4 * Dq n ^ 2 := by ring
      rw [e2]
      exact hsq0
    obtain ⟨hw1, hw2⟩ := abs_lt_of_sq_lt_sq' hsq hp.le
    have eD : Dq n = (b (n + 1) : ℚ) ^ 2 - (b n : ℚ) * (b (n + 2) : ℚ) := rfl
    rw [eD] at hw1 hw2
    refine ⟨by exact_mod_cast hp, by exact_mod_cast hw1, by exact_mod_cast hw2.le⟩

theorem ceil_lem (x y m : ℤ) (hy : 0 < y) (h1 : -y < 2 * (x - y * m)) (h2 : 2 * (x - y * m) ≤ y) :
    ⌈(x : ℚ) / (y : ℚ) - 1 / 2⌉ = m := by
  have hy' : (0 : ℚ) < y := by exact_mod_cast hy
  have h1' : -(y : ℚ) < 2 * ((x : ℚ) - (y : ℚ) * (m : ℚ)) := by exact_mod_cast h1
  have h2' : 2 * ((x : ℚ) - (y : ℚ) * (m : ℚ)) ≤ (y : ℚ) := by exact_mod_cast h2
  rw [Int.ceil_eq_iff]
  constructor
  · have h3 : (m : ℚ) - 1 / 2 < (x : ℚ) / (y : ℚ) := by
      rw [lt_div_iff₀ hy']
      linarith
    linarith
  · have h3 : (x : ℚ) / (y : ℚ) ≤ (m : ℚ) + 1 / 2 := by
      rw [div_le_iff₀ hy']
      linarith
    linarith

end P1A021008

open OMA.S_oeis_a021008 P1A021008 in
theorem OMA.solution : type_of% @OMA.S_oeis_a021008.main := by
  have ha : ∀ n, a n = b n ∧ a (n + 1) = b (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨hp, h1, h2⟩ := window k
      show ⌈((a (k + 1) : ℚ) ^ 2 / (a k : ℚ)) - 1 / 2⌉ = b (k + 2)
      rw [ih.1, ih.2]
      have h := ceil_lem (b (k + 1) ^ 2) (b k) (b (k + 2)) hp h1 h2
      push_cast at h
      exact h
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega,
      (ha (m + 4)).1, (ha (m + 3)).1, (ha (m + 2)).1, (ha m).1]
    exact b_rec m
  · have hrec : ∀ m, (a (m + 4) : ℚ) = 3 * (a (m + 3) : ℚ) - 2 * (a (m + 2) : ℚ) + (a m : ℚ) := by
      intro m
      rw [(ha (m + 4)).1, (ha (m + 3)).1, (ha (m + 2)).1, (ha m).1]
      exact bq_rec m
    have a0 : (a 0 : ℚ) = 5 := by
      have h : a 0 = 5 := (ha 0).1.trans rfl
      exact_mod_cast h
    have a1 : (a 1 : ℚ) = 11 := by
      have h : a 1 = 11 := (ha 1).1.trans rfl
      exact_mod_cast h
    have a2 : (a 2 : ℚ) = 24 := by
      have h : a 2 = 24 := (ha 2).1.trans rfl
      exact_mod_cast h
    have a3 : (a 3 : ℚ) = 52 := by
      have h : a 3 = 52 := (ha 3).1.trans rfl
      exact_mod_cast h
    have e : PowerSeries.mk (fun n => (a n : ℚ)) *
        (-PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 2 - 3 * PowerSeries.X + 1) =
        PowerSeries.mk (fun n => (a n : ℚ))
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
          - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
      ring
    have e2 : (2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 2 - 4 * PowerSeries.X + 5 : PowerSeries ℚ) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 2
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * PowerSeries.X ^ 1
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m
      · norm_num [a0]
      · norm_num [a0, a1]
      · norm_num [a0, a1, a2]
      · norm_num [a1, a2, a3]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      rw [if_pos (show 1 ≤ k + 4 by omega), if_pos (show 2 ≤ k + 4 by omega),
        if_pos (show 4 ≤ k + 4 by omega), if_pos (show 3 ≤ k + 4 by omega),
        if_neg (show ¬ (k + 4 - 3 = 0) by omega), if_neg (show ¬ (k + 4 = 2) by omega),
        if_pos (show 1 ≤ k + 4 by omega), if_neg (show ¬ (k + 4 - 1 = 0) by omega),
        if_neg (show ¬ (k + 4 = 0) by omega), show k + 4 - 1 = k + 3 by omega,
        show k + 4 - 2 = k + 2 by omega, show k + 4 - 4 = k by omega, hrec k]
      ring
