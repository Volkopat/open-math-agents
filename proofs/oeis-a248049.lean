import OMAStatements.S_oeis_a248049
import Mathlib

namespace A248049Proof

open Filter Topology

private lemma frame_pos (n : ℕ) :
    0 < (OMA.S_oeis_a248049.frame n).1 ∧
    0 < (OMA.S_oeis_a248049.frame n).2.1 ∧
    0 < (OMA.S_oeis_a248049.frame n).2.2.1 ∧
    0 < (OMA.S_oeis_a248049.frame n).2.2.2 := by
  induction n with
  | zero =>
    simp [OMA.S_oeis_a248049.frame]
  | succ n ih =>
    rcases ih with ⟨hw, hx, hy, hz⟩
    dsimp [OMA.S_oeis_a248049.frame]
    refine ⟨hx, hy, hz, ?_⟩
    positivity

private lemma term_pos (n : ℕ) : 0 < OMA.S_oeis_a248049.term n := by
  rw [OMA.S_oeis_a248049.term]
  exact_mod_cast (frame_pos n).1

private lemma term_rec (n : ℕ) :
    OMA.S_oeis_a248049.term (n + 4) =
      (OMA.S_oeis_a248049.term (n + 1) + OMA.S_oeis_a248049.term (n + 2)) *
      (OMA.S_oeis_a248049.term (n + 2) + OMA.S_oeis_a248049.term (n + 3)) /
      OMA.S_oeis_a248049.term n := by
  have h1 : OMA.S_oeis_a248049.term (n + 1) = ((OMA.S_oeis_a248049.frame n).2.1 : ℝ) := by
    simp [OMA.S_oeis_a248049.term, OMA.S_oeis_a248049.frame]
  have h2 : OMA.S_oeis_a248049.term (n + 2) = ((OMA.S_oeis_a248049.frame n).2.2.1 : ℝ) := by
    simp [OMA.S_oeis_a248049.term, OMA.S_oeis_a248049.frame]
  have h3 : OMA.S_oeis_a248049.term (n + 3) = ((OMA.S_oeis_a248049.frame n).2.2.2 : ℝ) := by
    simp [OMA.S_oeis_a248049.term, OMA.S_oeis_a248049.frame]
  have h4 : OMA.S_oeis_a248049.term (n + 4) =
      ((((OMA.S_oeis_a248049.frame n).2.1 + (OMA.S_oeis_a248049.frame n).2.2.1) *
        ((OMA.S_oeis_a248049.frame n).2.2.1 + (OMA.S_oeis_a248049.frame n).2.2.2) /
        (OMA.S_oeis_a248049.frame n).1 : ℚ) : ℝ) := by
    simp [OMA.S_oeis_a248049.term, OMA.S_oeis_a248049.frame]
  rw [h4, h1, h2, h3, OMA.S_oeis_a248049.term]
  push_cast
  rfl

private noncomputable def L (n : ℕ) : ℝ := Real.log (OMA.S_oeis_a248049.term n)

private noncomputable def d (n : ℕ) : ℝ := L (n + 1) - L n

private noncomputable def eps (n : ℕ) : ℝ :=
  Real.log (1 + OMA.S_oeis_a248049.term (n + 1) / OMA.S_oeis_a248049.term (n + 2)) +
  Real.log (1 + OMA.S_oeis_a248049.term (n + 2) / OMA.S_oeis_a248049.term (n + 3))

private lemma eps_pos (n : ℕ) : 0 < eps n := by
  have h1 : 0 < OMA.S_oeis_a248049.term (n + 1) / OMA.S_oeis_a248049.term (n + 2) :=
    div_pos (term_pos _) (term_pos _)
  have h2 : 0 < OMA.S_oeis_a248049.term (n + 2) / OMA.S_oeis_a248049.term (n + 3) :=
    div_pos (term_pos _) (term_pos _)
  exact add_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))

private lemma L_rec (n : ℕ) : L (n + 4) - L (n + 3) - L (n + 2) + L n = eps n := by
  have h0 : 0 < OMA.S_oeis_a248049.term n := term_pos n
  have h2 : 0 < OMA.S_oeis_a248049.term (n + 2) := term_pos (n + 2)
  have h3 : 0 < OMA.S_oeis_a248049.term (n + 3) := term_pos (n + 3)
  have ha : OMA.S_oeis_a248049.term (n + 4) =
      (OMA.S_oeis_a248049.term (n + 2) * OMA.S_oeis_a248049.term (n + 3) /
        OMA.S_oeis_a248049.term n) *
      (1 + OMA.S_oeis_a248049.term (n + 1) / OMA.S_oeis_a248049.term (n + 2)) *
      (1 + OMA.S_oeis_a248049.term (n + 2) / OMA.S_oeis_a248049.term (n + 3)) := by
    rw [term_rec n]
    field_simp
    ring
  have hf1 : 0 < 1 + OMA.S_oeis_a248049.term (n + 1) / OMA.S_oeis_a248049.term (n + 2) := by
    have := term_pos (n + 1); positivity
  have hf2 : 0 < 1 + OMA.S_oeis_a248049.term (n + 2) / OMA.S_oeis_a248049.term (n + 3) := by
    positivity
  have hL4 : L (n + 4) = L (n + 2) + L (n + 3) - L n + eps n := by
    rw [L, ha, Real.log_mul (by positivity) hf2.ne',
      Real.log_mul (by positivity) hf1.ne',
      Real.log_div (by positivity) h0.ne',
      Real.log_mul h2.ne' h3.ne']
    simp only [L, eps]
    ring
  linarith

private lemma d_rec (n : ℕ) : d (n + 1) + d n + eps n = d (n + 3) := by
  have h := L_rec n
  simp only [d] at *
  linarith

private lemma eps_le_exp (n : ℕ) : eps n ≤ Real.exp (-d (n + 1)) + Real.exp (-d (n + 2)) := by
  have h1 : Real.log (1 + OMA.S_oeis_a248049.term (n + 1) / OMA.S_oeis_a248049.term (n + 2)) ≤
      OMA.S_oeis_a248049.term (n + 1) / OMA.S_oeis_a248049.term (n + 2) := by
    have := Real.log_le_sub_one_of_pos
      (show 0 < 1 + OMA.S_oeis_a248049.term (n + 1) / OMA.S_oeis_a248049.term (n + 2) by
        have := term_pos (n + 1); have := term_pos (n + 2); positivity)
    linarith
  have h2 : Real.log (1 + OMA.S_oeis_a248049.term (n + 2) / OMA.S_oeis_a248049.term (n + 3)) ≤
      OMA.S_oeis_a248049.term (n + 2) / OMA.S_oeis_a248049.term (n + 3) := by
    have := Real.log_le_sub_one_of_pos
      (show 0 < 1 + OMA.S_oeis_a248049.term (n + 2) / OMA.S_oeis_a248049.term (n + 3) by
        have := term_pos (n + 2); have := term_pos (n + 3); positivity)
    linarith
  have he (k : ℕ) : Real.exp (-d k) = OMA.S_oeis_a248049.term k / OMA.S_oeis_a248049.term (k + 1) := by
    rw [d, neg_sub, Real.exp_sub, L, L, Real.exp_log (term_pos k), Real.exp_log (term_pos (k + 1))]
  rw [he (n + 1), he (n + 2)]
  exact add_le_add h1 h2

private lemma frame_12 :
    OMA.S_oeis_a248049.frame 12 =
      (219429008298500, 31064340573760168675, 206377779224083011749949745,
        245390990689739612867279321757020455) := by
  have f0 : OMA.S_oeis_a248049.frame 0 = (2, 1, 1, 1) := rfl
  have f1 : OMA.S_oeis_a248049.frame 1 = (1, 1, 1, 2) := by
    rw [OMA.S_oeis_a248049.frame, f0]; norm_num
  have f2 : OMA.S_oeis_a248049.frame 2 = (1, 1, 2, 6) := by
    rw [OMA.S_oeis_a248049.frame, f1]; norm_num
  have f3 : OMA.S_oeis_a248049.frame 3 = (1, 2, 6, 24) := by
    rw [OMA.S_oeis_a248049.frame, f2]; norm_num
  have f4 : OMA.S_oeis_a248049.frame 4 = (2, 6, 24, 240) := by
    rw [OMA.S_oeis_a248049.frame, f3]; norm_num
  have f5 : OMA.S_oeis_a248049.frame 5 = (6, 24, 240, 3960) := by
    rw [OMA.S_oeis_a248049.frame, f4]; norm_num
  have f6 : OMA.S_oeis_a248049.frame 6 = (24, 240, 3960, 184800) := by
    rw [OMA.S_oeis_a248049.frame, f5]; norm_num
  have f7 : OMA.S_oeis_a248049.frame 7 = (240, 3960, 184800, 33033000) := by
    rw [OMA.S_oeis_a248049.frame, f6]; norm_num
  have f8 : OMA.S_oeis_a248049.frame 8 = (3960, 184800, 33033000, 26125799700) := by
    rw [OMA.S_oeis_a248049.frame, f7]; norm_num
  have f9 : OMA.S_oeis_a248049.frame 9 = (184800, 33033000, 26125799700, 219429008298500) := by
    rw [OMA.S_oeis_a248049.frame, f8]; norm_num
  have f10 : OMA.S_oeis_a248049.frame 10 =
      (33033000, 26125799700, 219429008298500, 31064340573760168675) := by
    rw [OMA.S_oeis_a248049.frame, f9]; norm_num
  have f11 : OMA.S_oeis_a248049.frame 11 =
      (26125799700, 219429008298500, 31064340573760168675, 206377779224083011749949745) := by
    rw [OMA.S_oeis_a248049.frame, f10]; norm_num
  rw [OMA.S_oeis_a248049.frame, f11]; norm_num

private lemma term_12 : OMA.S_oeis_a248049.term 12 = 219429008298500 := by
  rw [OMA.S_oeis_a248049.term, frame_12]; norm_num

private lemma term_13 : OMA.S_oeis_a248049.term 13 = 31064340573760168675 := by
  rw [OMA.S_oeis_a248049.term, OMA.S_oeis_a248049.frame, frame_12]; norm_num

private lemma term_14 : OMA.S_oeis_a248049.term 14 = 206377779224083011749949745 := by
  rw [OMA.S_oeis_a248049.term, OMA.S_oeis_a248049.frame, OMA.S_oeis_a248049.frame, frame_12]
  norm_num

private lemma term_15 : OMA.S_oeis_a248049.term 15 = 245390990689739612867279321757020455 := by
  rw [OMA.S_oeis_a248049.term, OMA.S_oeis_a248049.frame, OMA.S_oeis_a248049.frame,
    OMA.S_oeis_a248049.frame, frame_12]
  norm_num

private lemma d_12_ge : 11 ≤ d 12 := by
  have hratio : (2 : ℝ) ^ (17 : ℕ) ≤ OMA.S_oeis_a248049.term 13 / OMA.S_oeis_a248049.term 12 := by
    rw [term_12, term_13]; norm_num
  have hlog : ((17 : ℕ) : ℝ) * Real.log 2 ≤ d 12 := by
    have hd : d 12 = Real.log (OMA.S_oeis_a248049.term 13 / OMA.S_oeis_a248049.term 12) := by
      rw [d, L, L, Real.log_div (term_pos 13).ne' (term_pos 12).ne']
    rw [hd, ← Real.log_pow]
    exact Real.log_le_log (by positivity) hratio
  norm_num at hlog
  linarith [Real.log_two_gt_d9]

private lemma d_13_ge : 15 ≤ d 13 := by
  have hratio : (2 : ℝ) ^ (22 : ℕ) ≤ OMA.S_oeis_a248049.term 14 / OMA.S_oeis_a248049.term 13 := by
    rw [term_13, term_14]; norm_num
  have hlog : ((22 : ℕ) : ℝ) * Real.log 2 ≤ d 13 := by
    have hd : d 13 = Real.log (OMA.S_oeis_a248049.term 14 / OMA.S_oeis_a248049.term 13) := by
      rw [d, L, L, Real.log_div (term_pos 14).ne' (term_pos 13).ne']
    rw [hd, ← Real.log_pow]
    exact Real.log_le_log (by positivity) hratio
  norm_num at hlog
  linarith [Real.log_two_gt_d9]

private lemma d_14_ge : 20 ≤ d 14 := by
  have hratio : (2 : ℝ) ^ (30 : ℕ) ≤ OMA.S_oeis_a248049.term 15 / OMA.S_oeis_a248049.term 14 := by
    rw [term_14, term_15]; norm_num
  have hlog : ((30 : ℕ) : ℝ) * Real.log 2 ≤ d 14 := by
    have hd : d 14 = Real.log (OMA.S_oeis_a248049.term 15 / OMA.S_oeis_a248049.term 14) := by
      rw [d, L, L, Real.log_div (term_pos 15).ne' (term_pos 14).ne']
    rw [hd, ← Real.log_pow]
    exact Real.log_le_log (by positivity) hratio
  norm_num at hlog
  linarith [Real.log_two_gt_d9]

private lemma d_geom (m : ℕ) : 11 * (5 / 4 : ℝ) ^ m ≤ d (12 + m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => simpa using d_12_ge
    | 1 =>
      have := d_13_ge
      norm_num at *
      linarith
    | 2 =>
      have := d_14_ge
      norm_num at *
      linarith
    | m + 3 =>
      have hm0 := ih m (by omega)
      have hm1 := ih (m + 1) (by omega)
      have hrec := d_rec (12 + m)
      have heps := eps_pos (12 + m)
      have hpow : (11 : ℝ) * (5 / 4 : ℝ) ^ (m + 3) ≤
          11 * (5 / 4 : ℝ) ^ (m + 1) + 11 * (5 / 4 : ℝ) ^ m := by
        have hp : 0 ≤ (5 / 4 : ℝ) ^ m := by positivity
        nlinarith [show (5 / 4 : ℝ) ^ (m + 3) = (125 / 64 : ℝ) * (5 / 4 : ℝ) ^ m by ring,
          show (5 / 4 : ℝ) ^ (m + 1) = (5 / 4 : ℝ) * (5 / 4 : ℝ) ^ m by ring]
      have hidx1 : 12 + m + 1 = 12 + (m + 1) := by omega
      have hidx3 : 12 + m + 3 = 12 + (m + 3) := by omega
      rw [hidx1, hidx3] at hrec
      linarith

private lemma pow_five_fourths_ge (j : ℕ) : 1 + (j : ℝ) / 4 ≤ (5 / 4 : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    calc
      1 + ((j : ℝ) + 1) / 4 ≤ (1 + (j : ℝ) / 4) * (5 / 4) := by nlinarith
      _ ≤ (5 / 4 : ℝ) ^ j * (5 / 4) := by gcongr
      _ = (5 / 4 : ℝ) ^ (j + 1) := by ring

private lemma eps_12_bound : eps 12 ≤ 3 / 10 ^ 7 := by
  have h1 : Real.log (1 + OMA.S_oeis_a248049.term 13 / OMA.S_oeis_a248049.term 14) ≤
      OMA.S_oeis_a248049.term 13 / OMA.S_oeis_a248049.term 14 := by
    have := Real.log_le_sub_one_of_pos
      (show 0 < 1 + OMA.S_oeis_a248049.term 13 / OMA.S_oeis_a248049.term 14 by
        have := term_pos 13; have := term_pos 14; positivity)
    linarith
  have h2 : Real.log (1 + OMA.S_oeis_a248049.term 14 / OMA.S_oeis_a248049.term 15) ≤
      OMA.S_oeis_a248049.term 14 / OMA.S_oeis_a248049.term 15 := by
    have := Real.log_le_sub_one_of_pos
      (show 0 < 1 + OMA.S_oeis_a248049.term 14 / OMA.S_oeis_a248049.term 15 by
        have := term_pos 14; have := term_pos 15; positivity)
    linarith
  have hnum : OMA.S_oeis_a248049.term 13 / OMA.S_oeis_a248049.term 14 +
      OMA.S_oeis_a248049.term 14 / OMA.S_oeis_a248049.term 15 ≤ 3 / 10 ^ 7 := by
    rw [term_13, term_14, term_15]
    norm_num
  exact (add_le_add h1 h2).trans hnum

private lemma exp_neg_17_lt : Real.exp (-17) < 5 / 10 ^ 8 := by
  have hexp : (2718 / 1000 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpow : ((2718 / 1000 : ℝ) ^ 17) < (Real.exp 1) ^ 17 := by gcongr
  have h17 : Real.exp 17 = (Real.exp 1) ^ 17 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [Real.exp_neg, h17, inv_lt_comm₀ (by positivity) (by positivity)]
  exact lt_trans (by norm_num) hpow

private lemma exp_neg_4_lt : Real.exp (-4) < 1 / 2 := by
  have hexp : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpow : (2 : ℝ) ^ 4 < (Real.exp 1) ^ 4 := by gcongr
  have h4 : Real.exp 4 = (Real.exp 1) ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [Real.exp_neg, h4, inv_lt_comm₀ (by positivity) (by positivity)]
  exact lt_trans (by norm_num) hpow

private lemma eps_tail_bound (j : ℕ) : eps (13 + j) ≤ (1 / 10 ^ 7 : ℝ) * (1 / 2) ^ j := by
  have hd1 : 17 + 4 * (j : ℝ) ≤ d (13 + j + 1) := by
    have hidx : 13 + j + 1 = 12 + (j + 2) := by omega
    rw [hidx]
    refine le_trans ?_ (d_geom (j + 2))
    have hp := pow_five_fourths_ge j
    have h1 : (5 / 4 : ℝ) ^ (j + 2) = (25 / 16 : ℝ) * (5 / 4 : ℝ) ^ j := by ring
    rw [h1]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hd2 : 17 + 4 * (j : ℝ) ≤ d (13 + j + 2) := by
    have hidx : 13 + j + 2 = 12 + (j + 3) := by omega
    rw [hidx]
    refine le_trans ?_ (d_geom (j + 3))
    have hp := pow_five_fourths_ge j
    have h1 : (5 / 4 : ℝ) ^ (j + 3) = (125 / 64 : ℝ) * (5 / 4 : ℝ) ^ j := by ring
    rw [h1]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hexp_eq : Real.exp (-(17 + 4 * (j : ℝ))) = Real.exp (-17) * (Real.exp (-4)) ^ j := by
    have hj : -(17 + 4 * (j : ℝ)) = -17 + (j : ℝ) * (-4) := by ring
    rw [hj, Real.exp_add, Real.exp_nat_mul]
  have h1 : Real.exp (-d (13 + j + 1)) ≤ Real.exp (-17) * (Real.exp (-4)) ^ j := by
    rw [← hexp_eq]
    exact Real.exp_le_exp.mpr (neg_le_neg hd1)
  have h2 : Real.exp (-d (13 + j + 2)) ≤ Real.exp (-17) * (Real.exp (-4)) ^ j := by
    rw [← hexp_eq]
    exact Real.exp_le_exp.mpr (neg_le_neg hd2)
  have hsum : eps (13 + j) ≤ 2 * Real.exp (-17) * (Real.exp (-4)) ^ j := by
    linarith [eps_le_exp (13 + j)]
  have hpow_le : (Real.exp (-4)) ^ j ≤ (1 / 2 : ℝ) ^ j :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_4_lt.le j
  calc
    eps (13 + j) ≤ 2 * Real.exp (-17) * (Real.exp (-4)) ^ j := hsum
    _ ≤ 2 * (5 / 10 ^ 8) * (1 / 2 : ℝ) ^ j := by
      gcongr
      exact exp_neg_17_lt.le
    _ = (1 / 10 ^ 7 : ℝ) * (1 / 2) ^ j := by ring

private lemma c_bounds {c : ℝ} (hc1 : 1 < c) (hc3 : c ^ 3 = c + 1) :
    1.32471795 < c ∧ c < 1.32471796 := by
  have h1 : 1.32471795 < c := by
    by_contra h
    push Not at h
    have hpos : 0 < c ^ 2 + c * 1.32471795 + 1.32471795 ^ 2 - 1 := by nlinarith
    have hdiff : c ^ 3 - c - 1 - ((1.32471795 : ℝ) ^ 3 - 1.32471795 - 1) =
        (c - 1.32471795) * (c ^ 2 + c * 1.32471795 + 1.32471795 ^ 2 - 1) := by ring
    have hval : (1.32471795 : ℝ) ^ 3 - 1.32471795 - 1 < 0 := by norm_num
    nlinarith
  have h2 : c < 1.32471796 := by
    by_contra h
    push Not at h
    have hpos : 0 < c ^ 2 + c * 1.32471796 + 1.32471796 ^ 2 - 1 := by nlinarith
    have hdiff : c ^ 3 - c - 1 - ((1.32471796 : ℝ) ^ 3 - 1.32471796 - 1) =
        (c - 1.32471796) * (c ^ 2 + c * 1.32471796 + 1.32471796 ^ 2 - 1) := by ring
    have hval : (0 : ℝ) < (1.32471796 : ℝ) ^ 3 - 1.32471796 - 1 := by norm_num
    nlinarith
  exact ⟨h1, h2⟩

private lemma log_approx_helper (Lval C x : ℝ) (hx : |x| < 1)
    (hx3 : |x| ^ (2 + 1) / (1 - |x|) ≤ 1 / 10 ^ 7)
    (hlog : Real.log (1 - x) = Lval - C) :
    |Lval - (C - (x + x ^ 2 / 2))| ≤ 1 / 10 ^ 7 := by
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  have hsum : (∑ i ∈ Finset.range 2, x ^ (i + 1) / ((i : ℝ) + 1)) = x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ]; ring
  rw [hsum, hlog] at h
  have h1 : Lval - (C - (x + x ^ 2 / 2)) = (x + x ^ 2 / 2) + (Lval - C) := by ring
  rw [h1]
  exact h.trans hx3

private lemma log_5_bounds : (1.6094379123 : ℝ) < Real.log 5 ∧ Real.log 5 < 1.6094379126 := by
  have h := Real.log_five_near_10
  rw [abs_sub_le_iff] at h
  constructor <;> linarith

private lemma L12_bounds : 33.022049 < L 12 ∧ L 12 < 33.022051 := by
  have h := log_approx_helper (L 12) (43 * Real.log 2 + 2 * Real.log 5)
    ((473317256700 : ℝ) / 219902325555200) (by norm_num) (by norm_num) (by
      have hrat : 1 - (473317256700 : ℝ) / 219902325555200 =
          OMA.S_oeis_a248049.term 12 / (2 ^ 43 * 5 ^ 2) := by
        rw [term_12]; norm_num
      rw [hrat, Real.log_div (term_pos 12).ne' (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      simp only [L]; ring)
  have hrat_bnd : (0.00215470 : ℝ) < (473317256700 : ℝ) / 219902325555200 +
      ((473317256700 : ℝ) / 219902325555200) ^ 2 / 2 ∧
      (473317256700 : ℝ) / 219902325555200 +
      ((473317256700 : ℝ) / 219902325555200) ^ 2 / 2 < 0.00215473 := by
    constructor <;> norm_num
  rw [abs_sub_le_iff] at h
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_5_bounds.1, log_5_bounds.2]

private lemma L13_bounds : 44.882591 < L 13 ∧ L 13 < 44.882593 := by
  have h := log_approx_helper (L 13) (60 * Real.log 2 + 3 * Real.log 3)
    ((64540050624699677 : ℝ) / 31128880624384868352) (by norm_num) (by norm_num) (by
      have hrat : 1 - (64540050624699677 : ℝ) / 31128880624384868352 =
          OMA.S_oeis_a248049.term 13 / (2 ^ 60 * 3 ^ 3) := by
        rw [term_13]; norm_num
      rw [hrat, Real.log_div (term_pos 13).ne' (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      simp only [L]; ring)
  have hrat_bnd : (0.00207546 : ℝ) < (64540050624699677 : ℝ) / 31128880624384868352 +
      ((64540050624699677 : ℝ) / 31128880624384868352) ^ 2 / 2 ∧
      (64540050624699677 : ℝ) / 31128880624384868352 +
      ((64540050624699677 : ℝ) / 31128880624384868352) ^ 2 / 2 < 0.00207548 := by
    constructor <;> norm_num
  rw [abs_sub_le_iff] at h
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9,
    Real.log_three_lt_d9]

private lemma L14_bounds : 60.591749 < L 14 ∧ L 14 < 60.591752 := by
  have h := log_approx_helper (L 14) (89 * Real.log 2 - Real.log 3)
    ((-163318029558897800287123 : ℝ) / 618970019642690137449562112) (by norm_num) (by norm_num) (by
      have hrat : 1 - (-163318029558897800287123 : ℝ) / 618970019642690137449562112 =
          (OMA.S_oeis_a248049.term 14 * 3) / (2 ^ 89) := by
        rw [term_14]; norm_num
      rw [hrat, Real.log_div (by have := term_pos 14; positivity) (by positivity),
        Real.log_mul (term_pos 14).ne' (by positivity), Real.log_pow]
      simp only [L]; ring)
  have hrat_bnd : (-0.00026382 : ℝ) < (-163318029558897800287123 : ℝ) / 618970019642690137449562112 +
      ((-163318029558897800287123 : ℝ) / 618970019642690137449562112) ^ 2 / 2 ∧
      (-163318029558897800287123 : ℝ) / 618970019642690137449562112 +
      ((-163318029558897800287123 : ℝ) / 618970019642690137449562112) ^ 2 / 2 < -0.00026380 := by
    constructor <;> norm_num
  rw [abs_sub_le_iff] at h
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9,
    Real.log_three_lt_d9]

private lemma L15_bounds : 81.488160 < L 15 ∧ L 15 < 81.488162 := by
  have h := log_approx_helper (L 15) (120 * Real.log 2 - 3 * Real.log 3 + Real.log 5)
    ((20583230301609817102493613962170595 : ℝ) / 6646139978924579364519035301401722880)
    (by norm_num) (by norm_num) (by
      have hrat : 1 - (20583230301609817102493613962170595 : ℝ) /
          6646139978924579364519035301401722880 =
          (OMA.S_oeis_a248049.term 15 * 3 ^ 3) / (2 ^ 120 * 5) := by
        rw [term_15]; norm_num
      rw [hrat, Real.log_div (by have := term_pos 15; positivity) (by positivity),
        Real.log_mul (term_pos 15).ne' (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      simp only [L]; ring)
  have hrat_bnd : (0.00310180 : ℝ) < (20583230301609817102493613962170595 : ℝ) /
      6646139978924579364519035301401722880 +
      ((20583230301609817102493613962170595 : ℝ) / 6646139978924579364519035301401722880) ^ 2 / 2 ∧
      (20583230301609817102493613962170595 : ℝ) / 6646139978924579364519035301401722880 +
      ((20583230301609817102493613962170595 : ℝ) /
        6646139978924579364519035301401722880) ^ 2 / 2 < 0.00310184 := by
    constructor <;> norm_num
  rw [abs_sub_le_iff] at h
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9,
    Real.log_three_lt_d9, log_5_bounds.1, log_5_bounds.2]

private lemma lyapunov_tendsto_zero {β : ℝ} (hβ1 : 1 / 4 < β) (hβ2 : β < 1 / 2)
    (z η : ℕ → ℝ) (hrec : ∀ n, z (n + 2) + z (n + 1) + β * z n = η n)
    (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto z atTop (𝓝 0) := by
  let Q : ℝ → ℝ → ℝ := fun x y => β * x ^ 2 + x * y + y ^ 2
  have hQ_nonneg : ∀ x y, (4 * β - 1) * y ^ 2 ≤ 4 * β * Q x y := fun x y => by
    have : 4 * β * Q x y - (4 * β - 1) * y ^ 2 = (2 * β * x + y) ^ 2 := by
      simp only [Q]; ring
    nlinarith [sq_nonneg (2 * β * x + y)]
  have hQ_step : ∀ n, Q (z (n + 1)) (z (n + 2)) ≤ (3 / 4) * Q (z n) (z (n + 1)) + 3 * (η n) ^ 2 := by
    intro n
    have hz : z (n + 2) = -β * z n - z (n + 1) + η n := by linarith [hrec n]
    rw [hz]
    have hkey : 4 * β * ((1 / 4) * Q (z n) (z (n + 1)) + 4 * β * (η n) ^ 2 +
        η n * (2 * β * z n + z (n + 1))) =
        (β * z n + z (n + 1) / 2 + 4 * β * η n) ^ 2 + (β - 1 / 4) * (z (n + 1)) ^ 2 := by
      simp only [Q]; ring
    have hkey2 : 0 ≤ (1 / 4) * Q (z n) (z (n + 1)) + 4 * β * (η n) ^ 2 +
        η n * (2 * β * z n + z (n + 1)) := by
      have hrhs : 0 ≤ (β * z n + z (n + 1) / 2 + 4 * β * η n) ^ 2 + (β - 1 / 4) * (z (n + 1)) ^ 2 := by
        nlinarith [sq_nonneg (β * z n + z (n + 1) / 2 + 4 * β * η n), sq_nonneg (z (n + 1))]
      nlinarith
    have hQdiff : Q (z (n + 1)) (-β * z n - z (n + 1) + η n) =
        β * Q (z n) (z (n + 1)) - η n * (2 * β * z n + z (n + 1)) + (η n) ^ 2 := by
      simp only [Q]; ring
    have hQ0 : 0 ≤ Q (z n) (z (n + 1)) := by
      have := hQ_nonneg (z n) (z (n + 1))
      nlinarith [sq_nonneg (z (n + 1))]
    nlinarith [sq_nonneg (η n)]
  have hQ_lim : Tendsto (fun n => Q (z n) (z (n + 1))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hη2 : Tendsto (fun n => 3 * (η n) ^ 2) atTop (𝓝 0) := by
      simpa using (hη.pow 2).const_mul 3
    rw [Metric.tendsto_atTop] at hη2
    obtain ⟨N, hN⟩ := hη2 (ε / 8) (by positivity)
    have hbound : ∀ m, Q (z (N + m)) (z (N + m + 1)) ≤
        (3 / 4 : ℝ) ^ m * Q (z N) (z (N + 1)) + ε / 2 := by
      intro m
      induction m with
      | zero => simp; linarith
      | succ m ih =>
        have hs := hQ_step (N + m)
        have hηb : 3 * (η (N + m)) ^ 2 ≤ ε / 8 := by
          have := hN (N + m) (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
          exact this.le
        have hidx : N + (m + 1) = N + m + 1 := by omega
        rw [hidx]
        calc
          Q (z (N + m + 1)) (z (N + m + 1 + 1))
              ≤ (3 / 4) * Q (z (N + m)) (z (N + m + 1)) + 3 * (η (N + m)) ^ 2 := hs
          _ ≤ (3 / 4) * ((3 / 4 : ℝ) ^ m * Q (z N) (z (N + 1)) + ε / 2) + ε / 8 := by linarith
          _ = (3 / 4 : ℝ) ^ (m + 1) * Q (z N) (z (N + 1)) + ε / 2 := by ring
    have hpow0 : Tendsto (fun m : ℕ => (3 / 4 : ℝ) ^ m * Q (z N) (z (N + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const
        (Q (z N) (z (N + 1)))
    rw [Metric.tendsto_atTop] at hpow0
    obtain ⟨M, hM⟩ := hpow0 (ε / 2) (by positivity)
    refine ⟨N + M, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hadd : N + M + m = N + (M + m) := by omega
    rw [hadd]
    have hQ0 : 0 ≤ Q (z (N + (M + m))) (z (N + (M + m) + 1)) := by
      have := hQ_nonneg (z (N + (M + m))) (z (N + (M + m) + 1))
      nlinarith [sq_nonneg (z (N + (M + m) + 1))]
    have hQN : 0 ≤ Q (z N) (z (N + 1)) := by
      have := hQ_nonneg (z N) (z (N + 1))
      nlinarith [sq_nonneg (z (N + 1))]
    have hm' := hM (M + m) (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hm'
    have hb := hbound (M + m)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hQ0]
    linarith
  have hz1 : Tendsto (fun n => z (n + 1)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n => (z (n + 1)) ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_)
        (by simpa using hQ_lim.const_mul (4 * β / (4 * β - 1)))
      have hpos : 0 < 4 * β - 1 := by linarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      nlinarith [hQ_nonneg (z n) (z (n + 1))]
    rw [Metric.tendsto_atTop] at hsq ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hsq (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)] at this
    rw [Real.dist_eq, sub_zero]
    exact abs_lt.mpr (abs_lt_of_sq_lt_sq' this hε.le)
  rwa [tendsto_add_atTop_iff_nat 1] at hz1

private lemma cesaro_geom_tendsto_zero {c : ℝ} (hc1 : 1 < c) (u : ℕ → ℝ)
    (hz : Tendsto (fun n => (u (n + 1) - u n) / c ^ n) atTop (𝓝 0)) :
    Tendsto (fun n => u n / c ^ n) atTop (𝓝 0) := by
  let z : ℕ → ℝ := fun n => (u (n + 1) - u n) / c ^ n
  have hsum : ∀ n, u n = u 0 + ∑ k ∈ Finset.range n, z k * c ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih]
      have hc0 : c ^ n ≠ 0 := pow_ne_zero n (by linarith)
      simp only [z]
      field_simp
      ring
  have hinv : 0 < 1 - 1 / c := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hc1
  rw [Metric.tendsto_atTop] at hz ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hz (ε * (1 - 1 / c) / 2) (by positivity)
  let C : ℝ := |u 0| + ∑ k ∈ Finset.range N, |u (k + 1) - u k|
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hpow0 : Tendsto (fun n : ℕ => C / c ^ n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ hc1)).const_mul C
  rw [Metric.tendsto_atTop] at hpow0
  obtain ⟨M, hM⟩ := hpow0 (ε / 2) (by positivity)
  refine ⟨max N M, fun n hn => ?_⟩
  have hNn : N ≤ n := le_of_max_le_left hn
  have hMn : M ≤ n := le_of_max_le_right hn
  have hcpos : 0 < c ^ n := by positivity
  have hu_split : u n / c ^ n =
      (u 0 + ∑ k ∈ Finset.range N, (u (k + 1) - u k)) / c ^ n +
      ∑ k ∈ Finset.Ico N n, z k / c ^ (n - k) := by
    rw [hsum n, ← Finset.sum_range_add_sum_Ico _ hNn]
    have h1 : ∑ k ∈ Finset.range N, z k * c ^ k = ∑ k ∈ Finset.range N, (u (k + 1) - u k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : c ^ k ≠ 0 := pow_ne_zero k (by linarith)
      simp only [z]
      field_simp
    have h2 : (∑ k ∈ Finset.Ico N n, z k * c ^ k) / c ^ n =
        ∑ k ∈ Finset.Ico N n, z k / c ^ (n - k) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := (Finset.mem_Ico.mp hk).2.le
      have hpow : c ^ n = c ^ (n - k) * c ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hkn]
      have hck : c ^ k ≠ 0 := pow_ne_zero k (by linarith)
      have hcnk : c ^ (n - k) ≠ 0 := pow_ne_zero (n - k) (by linarith)
      rw [hpow]
      field_simp
    rw [h1, ← add_assoc, add_div, h2]
  have hpart1 : |(u 0 + ∑ k ∈ Finset.range N, (u (k + 1) - u k)) / c ^ n| < ε / 2 := by
    rw [abs_div, abs_of_pos hcpos]
    have hle : |u 0 + ∑ k ∈ Finset.range N, (u (k + 1) - u k)| ≤ C :=
      (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    have hM' := hM n hMn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hC hcpos.le)] at hM'
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right hle hcpos.le) hM'
  have hpart2 : |∑ k ∈ Finset.Ico N n, z k / c ^ (n - k)| ≤ ε / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ Finset.Ico N n,
        |z k / c ^ (n - k)| ≤ (ε * (1 - 1 / c) / 2) * (1 / c) ^ (n - k) := by
      intro k hk
      have hNk : N ≤ k := (Finset.mem_Ico.mp hk).1
      have hzk : |z k| < ε * (1 - 1 / c) / 2 := by
        have := hN k hNk
        rw [Real.dist_eq, sub_zero] at this
        exact this
      rw [abs_div, abs_of_pos (by positivity : 0 < c ^ (n - k)), one_div, inv_pow, ← div_eq_mul_inv,
        ← one_div c]
      exact div_le_div_of_nonneg_right hzk.le (by positivity)
    have hsum_le : ∑ k ∈ Finset.Ico N n, |z k / c ^ (n - k)| ≤
        (ε * (1 - 1 / c) / 2) * ∑ k ∈ Finset.Ico N n, (1 / c) ^ (n - k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    have hgeom_sum : ∑ k ∈ Finset.Ico N n, (1 / c) ^ (n - k) ≤ 1 / (1 - 1 / c) := by
      have hinj : ∑ k ∈ Finset.Ico N n, (1 / c) ^ (n - k) =
          ∑ j ∈ Finset.range (n - N), (1 / c) ^ (j + 1) := by
        refine Finset.sum_bij (fun k _ => n - k - 1) ?_ ?_ ?_ ?_
        · intro k hk
          rw [Finset.mem_Ico] at hk
          rw [Finset.mem_range]
          omega
        · intro k₁ hk₁ k₂ hk₂ heq
          rw [Finset.mem_Ico] at hk₁ hk₂
          omega
        · intro j hj
          rw [Finset.mem_range] at hj
          refine ⟨n - (j + 1), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro k hk
          rw [Finset.mem_Ico] at hk
          congr 1
          omega
      rw [hinj]
      have hle1 : ∑ j ∈ Finset.range (n - N), (1 / c) ^ (j + 1) ≤
          ∑ j ∈ Finset.range (n - N), (1 / c) ^ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [pow_succ]
        exact mul_le_of_le_one_right (by positivity) (by rw [div_le_one (by linarith)]; exact hc1.le)
      have hne : (1 / c : ℝ) ≠ 1 := by
        rw [ne_eq, div_eq_one_iff_eq (by linarith)]; exact hc1.ne
      have hgeom := geom_sum_eq hne (n - N)
      have hgeom_le : ∑ j ∈ Finset.range (n - N), (1 / c) ^ j ≤ 1 / (1 - 1 / c) := by
        rw [hgeom, ← neg_div_neg_eq, neg_sub, neg_sub]
        exact div_le_div_of_nonneg_right (by linarith [show 0 ≤ (1 / c) ^ (n - N) by positivity])
          hinv.le
      exact hle1.trans hgeom_le
    refine hsum_le.trans ?_
    have hmul_eq : (ε * (1 - 1 / c) / 2) * (1 / (1 - 1 / c)) = ε / 2 := by
      have : 1 - 1 / c ≠ 0 := hinv.ne'
      field_simp
      exact div_self (by linarith : c - 1 ≠ 0)
    calc
      (ε * (1 - 1 / c) / 2) * ∑ k ∈ Finset.Ico N n, (1 / c) ^ (n - k)
          ≤ (ε * (1 - 1 / c) / 2) * (1 / (1 - 1 / c)) := by gcongr
      _ = ε / 2 := hmul_eq
  rw [Real.dist_eq, sub_zero, hu_split]
  have := (abs_add_le _ _).trans_lt (add_lt_add_of_lt_of_le hpart1 hpart2)
  linarith

private lemma mul_lt_mul_pos {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hab : a < b) (hcd : c < d) :
    a * c < b * d :=
  mul_lt_mul' hab.le hcd hc.le (ha.trans hab)

end A248049Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a248049.main := by
  intro c hc1 hc3
  have hc_bnd := A248049Proof.c_bounds hc1 hc3
  let b : ℕ → ℝ := fun n =>
    A248049Proof.L (n + 3) + (c - 1) * A248049Proof.L (n + 2) +
    (c ^ 2 - c - 1) * A248049Proof.L (n + 1) + (1 - c ^ 2) * A248049Proof.L n
  have hb_step : ∀ n, b (n + 1) - c * b n = A248049Proof.eps n := fun n => by
    have hL := A248049Proof.L_rec n
    simp only [b]
    calc
      A248049Proof.L (n + 1 + 3) + (c - 1) * A248049Proof.L (n + 1 + 2) +
          (c ^ 2 - c - 1) * A248049Proof.L (n + 1 + 1) +
          (1 - c ^ 2) * A248049Proof.L (n + 1) -
          c * (A248049Proof.L (n + 3) + (c - 1) * A248049Proof.L (n + 2) +
            (c ^ 2 - c - 1) * A248049Proof.L (n + 1) + (1 - c ^ 2) * A248049Proof.L n)
          = (A248049Proof.L (n + 4) - A248049Proof.L (n + 3) -
              A248049Proof.L (n + 2) + A248049Proof.L n) +
            (c ^ 3 - c - 1) * (A248049Proof.L n - A248049Proof.L (n + 1)) := by ring
      _ = A248049Proof.eps n := by rw [hL, hc3]; ring
  have hb_div : ∀ n, b (n + 1) / c ^ (n + 1) - b n / c ^ n =
      A248049Proof.eps n / c ^ (n + 1) := fun n => by
    have hc0 : c ≠ 0 := by linarith
    have h := hb_step n
    rw [pow_succ]
    field_simp
    linarith
  have hb_sum : ∀ m, b (12 + m) / c ^ (12 + m) =
      b 12 / c ^ 12 + ∑ j ∈ Finset.range m, A248049Proof.eps (12 + j) / c ^ (12 + j + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hidx : 12 + (m + 1) = (12 + m) + 1 := by omega
      calc
        b (12 + (m + 1)) / c ^ (12 + (m + 1))
            = b ((12 + m) + 1) / c ^ ((12 + m) + 1) := by rw [hidx]
        _ = b (12 + m) / c ^ (12 + m) + A248049Proof.eps (12 + m) / c ^ (12 + m + 1) := by
            linarith [hb_div (12 + m)]
        _ = b 12 / c ^ 12 +
              (∑ j ∈ Finset.range m, A248049Proof.eps (12 + j) / c ^ (12 + j + 1) +
                A248049Proof.eps (12 + m) / c ^ (12 + m + 1)) := by
            rw [ih]; ring
        _ = b 12 / c ^ 12 +
              ∑ j ∈ Finset.range (m + 1), A248049Proof.eps (12 + j) / c ^ (12 + j + 1) := by
            rw [Finset.sum_range_succ]
  let s : ℕ → ℝ := fun m => b (12 + m) / c ^ (12 + m)
  have hs_mono : Monotone s := by
    refine monotone_nat_of_le_succ fun m => ?_
    simp only [s]
    have hidx : 12 + (m + 1) = (12 + m) + 1 := by omega
    rw [hidx]
    have := hb_div (12 + m)
    have he := A248049Proof.eps_pos (12 + m)
    have hcpos : 0 < c ^ (12 + m + 1) := by positivity
    linarith [div_pos he hcpos]
  have hsum_tail : ∀ m, ∑ j ∈ Finset.range m, A248049Proof.eps (12 + j) / c ^ (12 + j + 1) ≤
      5 / 10 ^ 7 := by
    intro m
    cases m with
    | zero => norm_num
    | succ m =>
      rw [Finset.sum_range_succ']
      have h0 : A248049Proof.eps (12 + 0) / c ^ (12 + 0 + 1) ≤ 3 / 10 ^ 7 := by
        have hc_ge : (1 : ℝ) ≤ c ^ (12 + 0 + 1) := one_le_pow₀ hc1.le
        exact (div_le_self (A248049Proof.eps_pos 12).le hc_ge).trans A248049Proof.eps_12_bound
      have hrest : ∑ j ∈ Finset.range m, A248049Proof.eps (12 + (j + 1)) / c ^ (12 + (j + 1) + 1) ≤
          2 / 10 ^ 7 := by
        have hle1 : ∑ j ∈ Finset.range m, A248049Proof.eps (12 + (j + 1)) / c ^ (12 + (j + 1) + 1) ≤
            ∑ j ∈ Finset.range m, (1 / 10 ^ 7 : ℝ) * (1 / 2) ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hidx : 12 + (j + 1) = 13 + j := by omega
          rw [hidx]
          have hc_ge : (1 : ℝ) ≤ c ^ (13 + j + 1) := one_le_pow₀ hc1.le
          have hdiv : A248049Proof.eps (13 + j) / c ^ (13 + j + 1) ≤ A248049Proof.eps (13 + j) :=
            div_le_self (A248049Proof.eps_pos _).le hc_ge
          exact hdiv.trans (A248049Proof.eps_tail_bound j)
        have hgeom : ∑ j ∈ Finset.range m, (1 / 10 ^ 7 : ℝ) * (1 / 2) ^ j ≤ 2 / 10 ^ 7 := by
          rw [← Finset.mul_sum, geom_sum_eq (by norm_num)]
          have hsub : ((1 / 2 : ℝ) ^ m - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℝ) ^ m) := by ring
          rw [hsub]
          have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
          linarith
        exact hle1.trans hgeom
      linarith
  have hs_bdd : BddAbove (Set.range s) := by
    refine ⟨b 12 / c ^ 12 + 5 / 10 ^ 7, ?_⟩
    rintro _ ⟨m, rfl⟩
    simp only [s]
    rw [hb_sum m]
    linarith [hsum_tail m]
  let M : ℝ := ⨆ m, s m
  have hs_tendsto : Filter.Tendsto s Filter.atTop (nhds M) :=
    tendsto_atTop_ciSup hs_mono hs_bdd
  have hb_tendsto : Filter.Tendsto (fun n => b n / c ^ n) Filter.atTop (nhds M) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 12]
    simpa only [s, Nat.add_comm 12] using hs_tendsto
  have hM_ge : b 12 / c ^ 12 ≤ M := le_ciSup hs_bdd 0
  have hM_le : M ≤ b 12 / c ^ 12 + 5 / 10 ^ 7 := by
    refine ciSup_le fun m => ?_
    simp only [s]
    rw [hb_sum m]
    linarith [hsum_tail m]
  let p : ℝ := 4 + 2 * c - 3 * c ^ 2
  have hp_gt : 1.38 < p := by
    simp only [p]
    nlinarith only [hc_bnd.1, hc_bnd.2]
  let K : ℝ := M / p
  let u : ℕ → ℝ := fun n => A248049Proof.L n - K * c ^ n
  let w : ℕ → ℝ := fun n => u (n + 1) - u n
  let z : ℕ → ℝ := fun n => w n / c ^ n
  let β : ℝ := (c ^ 2 - 1) / c ^ 2
  have hβ_eq : β = 1 / (c + 1) := by
    have hc0 : c ≠ 0 := by linarith
    have hc1' : c + 1 ≠ 0 := by linarith
    simp only [β]
    field_simp
    nlinarith only [hc3]
  have hβ1 : 1 / 4 < β := by
    rw [hβ_eq, lt_div_iff₀ (by linarith)]
    linarith only [hc_bnd.2]
  have hβ2 : β < 1 / 2 := by
    rw [hβ_eq, div_lt_iff₀ (by linarith)]
    linarith only [hc_bnd.1]
  have hK_id : c ^ 3 + (c - 1) * c ^ 2 + (c ^ 2 - c - 1) * c + (1 - c ^ 2) = p := by
    simp only [p]
    linear_combination 3 * hc3
  have hw_rec : ∀ n, w (n + 2) + c * w (n + 1) + (c ^ 2 - 1) * w n = b n - M * c ^ n := by
    intro n
    have h1 : w (n + 2) + c * w (n + 1) + (c ^ 2 - 1) * w n =
        u (n + 3) + (c - 1) * u (n + 2) + (c ^ 2 - c - 1) * u (n + 1) + (1 - c ^ 2) * u n := by
      simp only [w]
      ring
    rw [h1]
    have h2 : u (n + 3) + (c - 1) * u (n + 2) + (c ^ 2 - c - 1) * u (n + 1) + (1 - c ^ 2) * u n =
        b n - K * c ^ n * (c ^ 3 + (c - 1) * c ^ 2 + (c ^ 2 - c - 1) * c + (1 - c ^ 2)) := by
      simp only [u, b]
      ring
    rw [h2, hK_id]
    have hp0 : p ≠ 0 := by linarith
    simp only [K]
    field_simp
  have hz_rec : ∀ n, z (n + 2) + z (n + 1) + β * z n = (b n / c ^ n - M) / c ^ 2 := by
    intro n
    have hc0 : c ≠ 0 := by linarith
    have h := hw_rec n
    simp only [z, β]
    rw [show c ^ (n + 2) = c ^ n * c ^ 2 by ring, show c ^ (n + 1) = c ^ n * c by ring]
    field_simp
    linarith
  have hη : Filter.Tendsto (fun n => (b n / c ^ n - M) / c ^ 2) Filter.atTop (nhds 0) := by
    simpa using (hb_tendsto.sub_const M).div_const (c ^ 2)
  have hz_lim : Filter.Tendsto z Filter.atTop (nhds 0) :=
    A248049Proof.lyapunov_tendsto_zero hβ1 hβ2 z _ hz_rec hη
  have hu_lim : Filter.Tendsto (fun n => u n / c ^ n) Filter.atTop (nhds 0) :=
    A248049Proof.cesaro_geom_tendsto_zero hc1 u hz_lim
  have hL_lim : Filter.Tendsto (fun n => A248049Proof.L n / c ^ n) Filter.atTop (nhds K) := by
    have heq : (fun n => A248049Proof.L n / c ^ n) = (fun n => u n / c ^ n + K) := by
      ext n
      have hcn : c ^ n ≠ 0 := pow_ne_zero n (by linarith)
      simp only [u]
      field_simp
      ring
    rw [heq]
    simpa using hu_lim.add_const K
  refine ⟨K, hL_lim, ?_⟩
  have hL12 := A248049Proof.L12_bounds
  have hL13 := A248049Proof.L13_bounds
  have hL14 := A248049Proof.L14_bounds
  have hL15 := A248049Proof.L15_bounds
  have hc2_lo : 1.75487764 < c ^ 2 := by
    have : (1.32471795 : ℝ) ^ 2 < c ^ 2 := by gcongr; exact hc_bnd.1
    linarith only [this, show (1.75487764 : ℝ) < (1.32471795 : ℝ) ^ 2 by norm_num]
  have hc2_hi : c ^ 2 < 1.75487768 := by
    have : c ^ 2 < (1.32471796 : ℝ) ^ 2 := by gcongr; exact hc_bnd.2
    linarith only [this, show (1.32471796 : ℝ) ^ 2 < (1.75487768 : ℝ) by norm_num]
  have ht1_lo : 19.675228 < (c - 1) * A248049Proof.L 14 := by
    have hmul := A248049Proof.mul_lt_mul_pos (by norm_num) (by norm_num)
      (by linarith only [hc_bnd.1] : (0.32471795 : ℝ) < c - 1) hL14.1
    exact lt_trans (by norm_num) hmul
  have ht1_hi : (c - 1) * A248049Proof.L 14 < 19.675231 := by
    have hmul := A248049Proof.mul_lt_mul_pos (by linarith only [hc_bnd.1]) (by linarith only [hL14.1])
      (by linarith only [hc_bnd.2] : c - 1 < (0.32471796 : ℝ)) hL14.2
    exact lt_trans hmul (by norm_num)
  have ht2_lo : -25.575912 < (c ^ 2 - c - 1) * A248049Proof.L 13 := by
    have hmul := A248049Proof.mul_lt_mul_pos (by linarith only [hc2_hi, hc_bnd.1])
      (by linarith only [hL13.1])
      (by linarith only [hc2_lo, hc_bnd.2] : 1 + c - c ^ 2 < (0.56984032 : ℝ)) hL13.2
    have h1 : (1 + c - c ^ 2) * A248049Proof.L 13 < 25.575912 := lt_trans hmul (by norm_num)
    linarith only [h1]
  have ht2_hi : (c ^ 2 - c - 1) * A248049Proof.L 13 < -25.575907 := by
    have hmul := A248049Proof.mul_lt_mul_pos (by norm_num) (by norm_num)
      (by linarith only [hc2_hi, hc_bnd.1] : (0.56984027 : ℝ) < 1 + c - c ^ 2) hL13.1
    have h1 : 25.575907 < (1 + c - c ^ 2) * A248049Proof.L 13 := lt_trans (by norm_num) hmul
    linarith only [h1]
  have ht3_lo : -24.927610 < (1 - c ^ 2) * A248049Proof.L 12 := by
    have hmul := A248049Proof.mul_lt_mul_pos (by linarith only [hc2_lo]) (by linarith only [hL12.1])
      (by linarith only [hc2_hi] : c ^ 2 - 1 < (0.75487768 : ℝ)) hL12.2
    have h1 : (c ^ 2 - 1) * A248049Proof.L 12 < 24.927610 := lt_trans hmul (by norm_num)
    linarith only [h1]
  have ht3_hi : (1 - c ^ 2) * A248049Proof.L 12 < -24.927606 := by
    have hmul := A248049Proof.mul_lt_mul_pos (by norm_num) (by norm_num)
      (by linarith only [hc2_lo] : (0.75487764 : ℝ) < c ^ 2 - 1) hL12.1
    have h1 : 24.927606 < (c ^ 2 - 1) * A248049Proof.L 12 := lt_trans (by norm_num) hmul
    linarith only [h1]
  have hb12_lo : 50.659866 < b 12 := by
    simp only [b]
    linarith only [hL15.1, ht1_lo, ht2_lo, ht3_lo]
  have hb12_hi : b 12 < 50.659880 := by
    simp only [b]
    linarith only [hL15.2, ht1_hi, ht2_hi, ht3_hi]
  have hc12_eq : c ^ 12 = (c + 1) ^ 4 := by
    calc
      c ^ 12 = (c ^ 3) ^ 4 := by ring
      _ = (c + 1) ^ 4 := by rw [hc3]
  have hc12_lo : (29.206604 : ℝ) < c ^ 12 := by
    rw [hc12_eq]
    have : (1.32471795 + 1 : ℝ) ^ 4 < (c + 1) ^ 4 := by gcongr; exact hc_bnd.1
    linarith only [this, show (29.206604 : ℝ) < (1.32471795 + 1 : ℝ) ^ 4 by norm_num]
  have hc12_hi : c ^ 12 < (29.206607 : ℝ) := by
    rw [hc12_eq]
    have : (c + 1) ^ 4 < (1.32471796 + 1 : ℝ) ^ 4 := by gcongr; exact hc_bnd.2
    linarith only [this, show (1.32471796 + 1 : ℝ) ^ 4 < (29.206607 : ℝ) by norm_num]
  have hp_exact_lo : 1.384802 < p := by
    simp only [p]
    linarith only [hc_bnd.1, hc2_hi]
  have hp_exact_hi : p < 1.384804 := by
    simp only [p]
    linarith only [hc_bnd.2, hc2_lo]
  have hc12p_lo : 40.44536 < c ^ 12 * p := by
    have hmul := A248049Proof.mul_lt_mul_pos (by norm_num) (by norm_num) hc12_lo hp_exact_lo
    exact lt_trans (by norm_num) hmul
  have hc12p_hi : c ^ 12 * p < 40.44543 := by
    have hmul := A248049Proof.mul_lt_mul_pos (by linarith only [hc12_lo])
      (by linarith only [hp_exact_lo]) hc12_hi hp_exact_hi
    exact lt_trans hmul (by norm_num)
  have hK_lo : 1.252545 ≤ K := by
    have hKge : b 12 / (c ^ 12 * p) ≤ K := by
      simp only [K]
      rw [← div_div]
      exact div_le_div_of_nonneg_right hM_ge (by positivity)
    have hmul : b 12 ≤ K * (c ^ 12 * p) := by
      rwa [div_le_iff₀ (by positivity)] at hKge
    have hcmp : (1.252545 : ℝ) * (c ^ 12 * p) ≤ K * (c ^ 12 * p) := by
      linarith only [hb12_lo, hc12p_hi, hmul,
        show (1.252545 : ℝ) * 40.44543 < 50.659866 by norm_num]
    exact le_of_mul_le_mul_right hcmp (by positivity)
  have hK_hi : K < 1.252555 := by
    have hKle : K ≤ (b 12 / c ^ 12 + 5 / 10 ^ 7) / p := by
      simp only [K]
      exact div_le_div_of_nonneg_right hM_le (by positivity)
    have hKle2 : K ≤ (b 12 + 5 / 10 ^ 7 * c ^ 12) / (c ^ 12 * p) := by
      refine hKle.trans_eq ?_
      have hc120 : c ^ 12 ≠ 0 := by positivity
      have hp0 : p ≠ 0 := by linarith
      field_simp
    have hmul : K * (c ^ 12 * p) ≤ b 12 + 5 / 10 ^ 7 * c ^ 12 := by
      rwa [le_div_iff₀ (by positivity)] at hKle2
    have hcmp : K * (c ^ 12 * p) < (1.252555 : ℝ) * (c ^ 12 * p) := by
      linarith only [hb12_hi, hc12_hi, hc12p_lo, hmul,
        show (50.659880 : ℝ) + 5 / 10 ^ 7 * 29.206607 < 1.252555 * 40.44536 by norm_num]
    exact lt_of_mul_lt_mul_right hcmp (by positivity)
  exact ⟨hK_lo, hK_hi⟩
