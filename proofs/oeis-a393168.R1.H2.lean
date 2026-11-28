import OMAReductions.R_oeis_a393168_R1

-- Step oeis-a393168.R1.H2: hypothesis H2 of reduction oeis-a393168.R1
-- Credit: @minimumnz

namespace OMA.P_oeis_a393168_R1_H2
open OMA.S_oeis_a393168

/-!
## Overview

For every `s` in the 73-element squarefree list and every `t > 1` with `6563 < s * t^2` and
`2 ≤ (s * t^2) % 4` (which forces `t` odd), we prove `IsRepresentable (s * t^2)`.

The core mechanism is conjugation of an integral binary quadratic form `Q = [[A, B], [B, C]]`
of determinant `-s` (`A * C - B^2 = -s`, `A` and `C` odd, `C > 0`) by an integer matrix
`M = [[a, 1], [c, d]]` of determinant `t` (`a * d - c = t`, with `a, d` even).
Then `M^T Q M = [[U, X], [X, V]]` has `U, V` odd and `U * V - X^2 = -s * t^2`, so
`s * t^2 = X^2 + ((U - V) / 2)^2 - ((U + V) / 2)^2`.
Thus `IsRepresentable (s * t^2)` follows whenever `X^2 ≤ s * t^2` and `(|U| + |V|)^2 ≤ 4 * s * t^2`.

For each `s`, we prove:
1. An **exact integer tail certificate** covering all `t` above a small threshold `tMaxFin`
   (corresponding to `m ≥ m0 ≤ 269`), by splitting `i / m` into 8 rational strips with denominator
   `D = 4096` and bounding `C * U = W^2 - s * a^2` and `C * X = W * (B + C * d) - s * a`.
2. A **finite bisection certificate** covering all odd `t ≤ tMaxFin` with `6563 < s * t^2`,
   using interval checks on fixed `(a, d)` buckets with recursive bisection and leaf checks
   via two forms `P1, P2`, small-offset factorizations, and 3 explicit witnesses.
-/

private lemma odd_of_mod_four_ge_two {s t : ℕ} (h : 2 ≤ (s * t ^ 2) % 4) : t % 2 = 1 := by
  by_contra ht
  have he : t % 2 = 0 := by omega
  obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k := ⟨t / 2, by omega⟩
  have h4 : 4 ∣ s * (2 * k) ^ 2 := ⟨s * k ^ 2, by ring⟩
  have h0 : (s * (2 * k) ^ 2) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
  omega

/-- Core determinant identity: if `A * C - B^2 = -s` with `A, C` odd, `a, d` even, `t` odd,
and `X^2 ≤ s * t^2` and `(|U| + |V|)^2 ≤ 4 * s * t^2`, then `IsRepresentable (s * t^2)`. -/
private lemma matrix_repr (s t : ℕ) (A B C a d : ℤ)
    (hdet : A * C - B ^ 2 = -(s : ℤ))
    (hA : A % 2 ≠ 0) (hC : C % 2 ≠ 0)
    (ha : a % 2 = 0) (hd : d % 2 = 0) (ht : t % 2 = 1)
    (hX : (A * a + B * (a * d + (a * d - (t : ℤ))) + C * (a * d - (t : ℤ)) * d) ^ 2 ≤
          ((s * t ^ 2 : ℕ) : ℤ))
    (hUV : (|A * a ^ 2 + 2 * B * a * (a * d - (t : ℤ)) + C * (a * d - (t : ℤ)) ^ 2| +
            |A + 2 * B * d + C * d ^ 2|) ^ 2 ≤ 4 * ((s * t ^ 2 : ℕ) : ℤ)) :
    IsRepresentable (s * t ^ 2) := by
  set c : ℤ := a * d - (t : ℤ)
  set U : ℤ := A * a ^ 2 + 2 * B * a * c + C * c ^ 2
  set V : ℤ := A + 2 * B * d + C * d ^ 2
  set X : ℤ := A * a + B * (a * d + c) + C * c * d
  have hdet_id : U * V - X ^ 2 = (A * C - B ^ 2) * (a * d - c) ^ 2 := by
    dsimp [U, V, X]; ring
  have hadc : a * d - c = (t : ℤ) := by dsimp [c]; ring
  have hUVX : X ^ 2 - U * V = ((s * t ^ 2 : ℕ) : ℤ) := by
    rw [hadc, hdet] at hdet_id
    push_cast
    linarith
  have hc_odd : c % 2 = 1 := by
    have h1 : (a * d) % 2 = 0 := by rw [Int.mul_emod, ha]; simp
    have h2 : (t : ℤ) % 2 = 1 := by exact_mod_cast ht
    dsimp [c]; omega
  have hU_odd : U % 2 = 1 := by
    have ha2 : a ^ 2 % 2 = 0 := by rw [sq, Int.mul_emod, ha]; simp
    have h1 : (A * a ^ 2) % 2 = 0 := by rw [Int.mul_emod, ha2]; simp
    have h2 : (2 * B * a * c) % 2 = 0 := by
      have : 2 * B * a * c = 2 * (B * a * c) := by ring
      rw [this]; omega
    have hC1 : C % 2 = 1 := by omega
    have hc2 : c ^ 2 % 2 = 1 := by rw [sq, Int.mul_emod, hc_odd]; simp
    have h3 : (C * c ^ 2) % 2 = 1 := by rw [Int.mul_emod, hC1, hc2]; simp
    dsimp [U]; omega
  have hV_odd : V % 2 = 1 := by
    have hA1 : A % 2 = 1 := by omega
    have h2 : (2 * B * d) % 2 = 0 := by
      have : 2 * B * d = 2 * (B * d) := by ring
      rw [this]; omega
    have hd2 : d ^ 2 % 2 = 0 := by rw [sq, Int.mul_emod, hd]; simp
    have h3 : (C * d ^ 2) % 2 = 0 := by rw [Int.mul_emod, hd2]; simp
    dsimp [V]; omega
  let y : ℤ := (U - V) / 2
  let z : ℤ := (U + V) / 2
  have hy2 : 2 * y = U - V := by dsimp [y]; omega
  have hz2 : 2 * z = U + V := by dsimp [z]; omega
  have h4y : 4 * y ^ 2 ≤ (|U| + |V|) ^ 2 := by
    have h1 : |2 * y| ≤ |U| + |V| := by
      rw [hy2]
      calc |U - V| = |U + (-V)| := by ring_nf
        _ ≤ |U| + |-V| := abs_add_le U (-V)
        _ = |U| + |V| := by rw [abs_neg]
    have h2 : (2 * y) ^ 2 ≤ (|U| + |V|) ^ 2 := by
      nlinarith [sq_abs (2 * y), abs_nonneg (2 * y)]
    linarith
  have h4z : 4 * z ^ 2 ≤ (|U| + |V|) ^ 2 := by
    have h1 : |2 * z| ≤ |U| + |V| := by
      rw [hz2]
      exact abs_add_le U V
    have h2 : (2 * z) ^ 2 ≤ (|U| + |V|) ^ 2 := by
      nlinarith [sq_abs (2 * z), abs_nonneg (2 * z)]
    linarith
  refine ⟨X, y, z, hX, by linarith, by linarith, ?_⟩
  have hyz : 4 * (y ^ 2 - z ^ 2) = -4 * (U * V) := by
    linear_combination (2 * y + U - V) * hy2 - (2 * z + U + V) * hz2
  linarith

private lemma abs_le_max_of_mem_Icc {x lo hi : ℤ} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    |x| ≤ max |lo| |hi| := by
  rw [abs_le]
  constructor
  · have : -max |lo| |hi| ≤ -|lo| := neg_le_neg (le_max_left _ _)
    have : -|lo| ≤ lo := neg_abs_le lo
    linarith
  · have : hi ≤ |hi| := le_abs_self hi
    have : |hi| ≤ max |lo| |hi| := le_max_right _ _
    linarith

private lemma sq_mem_Icc_of_mem_Icc {x lo hi : ℤ} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    (if lo ≤ 0 ∧ 0 ≤ hi then (0 : ℤ) else min (lo ^ 2) (hi ^ 2)) ≤ x ^ 2 ∧
    x ^ 2 ≤ (max |lo| |hi|) ^ 2 := by
  constructor
  · split_ifs with h0
    · exact sq_nonneg x
    · rcases lt_or_ge 0 lo with hpos | hle
      · have : lo ^ 2 ≤ x ^ 2 := by nlinarith
        exact (min_le_left _ _).trans this
      · have hneg : hi < 0 := by omega
        have : hi ^ 2 ≤ x ^ 2 := by nlinarith
        exact (min_le_right _ _).trans this
  · have h1 := abs_le_max_of_mem_Icc hlo hhi
    nlinarith [sq_abs x, abs_nonneg x]

/-! ### Exact Integer Tail Box Verifier -/

private def D_SCALE : ℤ := 4096

private def checkBoxInt (s u : ℕ) (A B C ln : ℤ) (m0 p0 p1 : ℤ) : Bool :=
  let D := D_SCALE
  let a_lo := (u : ℤ) * (D + p0)
  let a_hi := (u : ℤ) * (D + p1)
  let d_lo := D - p1
  let d_hi := D - p0
  let q_m0 := (2 * D + m0 - 1) / m0
  let c_err := 4 * (u : ℤ) * (2 * p1 + q_m0)
  let c4_lo := D * ln - c_err
  let c4_hi := D * ln + c_err
  let Ba_lo := if 0 ≤ B then 4 * B * a_lo else 4 * B * a_hi
  let Ba_hi := if 0 ≤ B then 4 * B * a_hi else 4 * B * a_lo
  let W4_lo := Ba_lo + C * c4_lo
  let W4_hi := Ba_hi + C * c4_hi
  let W4_abs := max |W4_lo| |W4_hi|
  let W4_sq_hi := W4_abs * W4_abs
  let W4_sq_lo := if W4_lo ≤ 0 ∧ 0 ≤ W4_hi then 0 else min (W4_lo * W4_lo) (W4_hi * W4_hi)
  let CU16_lo := W4_sq_lo - 16 * (s : ℤ) * a_hi * a_hi
  let CU16_hi := W4_sq_hi - 16 * (s : ℤ) * a_lo * a_lo
  let CU16_abs := max |CU16_lo| |CU16_hi|
  let V16_abs := 16 * C * d_hi * d_hi +
    (32 * |B| * D * d_hi + m0 - 1) / m0 +
    (16 * |A| * D * D + m0 * m0 - 1) / (m0 * m0)
  let rem_c := max 0 (-(4 * (u : ℤ) + ln + 1))
  let t_num := 4 * (u : ℤ) * m0 - (8 * (u : ℤ) + max 0 ln) - (rem_c + m0 - 1) / m0
  let lhs_uv := m0 * (CU16_abs + C * V16_abs)
  let rhs_uv := 64 * (s : ℤ) * D ^ 4 * C * C * t_num * t_num
  let b_err := (|B| * D + m0 - 1) / m0
  let Bd_lo := C * d_lo - b_err
  let Bd_hi := C * d_hi + b_err
  let P_lo := min (min (W4_lo * Bd_lo) (W4_lo * Bd_hi)) (min (W4_hi * Bd_lo) (W4_hi * Bd_hi))
  let P_hi := max (max (W4_lo * Bd_lo) (W4_lo * Bd_hi)) (max (W4_hi * Bd_lo) (W4_hi * Bd_hi))
  let sa_hi := (4 * D * (s : ℤ) * a_hi + m0 - 1) / m0
  let CX4_abs := max |P_lo - sa_hi| |P_hi|
  let lhs_x := m0 * CX4_abs
  let rhs_x := (s : ℤ) * D ^ 4 * C * C * t_num * t_num
  decide (0 ≤ d_lo) &&
  decide (0 < t_num) &&
  decide (lhs_uv * lhs_uv ≤ rhs_uv) &&
  decide (lhs_x * lhs_x ≤ rhs_x)

private lemma ceil_div_mul_ge {N m0 m : ℤ} (hm0 : 0 < m0) (hm : m0 ≤ m) (hN : 0 ≤ N) :
    N ≤ ((N + m0 - 1) / m0) * m := by
  have h1 : N ≤ ((N + m0 - 1) / m0) * m0 := by
    have hmod := Int.emod_add_mul_ediv (N + m0 - 1) m0
    have hlt := Int.emod_lt_of_pos (N + m0 - 1) hm0
    nlinarith
  have hq : 0 ≤ (N + m0 - 1) / m0 := Int.ediv_nonneg (by linarith) (le_of_lt hm0)
  nlinarith

private lemma mul_mem_Icc {x y x0 x1 y0 y1 : ℤ}
    (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hy0 : y0 ≤ y) (hy1 : y ≤ y1) :
    min (min (x0 * y0) (x0 * y1)) (min (x1 * y0) (x1 * y1)) ≤ x * y ∧
    x * y ≤ max (max (x0 * y0) (x0 * y1)) (max (x1 * y0) (x1 * y1)) := by
  have hx_between : (x - x0) * (x1 - x) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  have hlin : ∀ z : ℤ, min (x0 * z) (x1 * z) ≤ x * z ∧ x * z ≤ max (x0 * z) (x1 * z) := by
    intro z
    rcases le_total 0 z with hz | hz
    · constructor
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (by nlinarith : x * z ≤ x1 * z).trans (le_max_right _ _)
    · constructor
      · exact (min_le_right _ _).trans (by nlinarith)
      · exact (by nlinarith : x * z ≤ x0 * z).trans (le_max_left _ _)
  have hlin_y : ∀ w : ℤ, min (w * y0) (w * y1) ≤ w * y ∧ w * y ≤ max (w * y0) (w * y1) := by
    intro w
    rcases le_total 0 w with hw | hw
    · constructor
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (by nlinarith : w * y ≤ w * y1).trans (le_max_right _ _)
    · constructor
      · exact (min_le_right _ _).trans (by nlinarith)
      · exact (by nlinarith : w * y ≤ w * y0).trans (le_max_left _ _)
  constructor
  · have h1 := (hlin y).1
    have h2 := (hlin_y x0).1
    have h3 := (hlin_y x1).1
    exact le_trans (min_le_min h2 h3) h1
  · have h1 := (hlin y).2
    have h2 := (hlin_y x0).2
    have h3 := (hlin_y x1).2
    exact le_trans h1 (max_le_max h2 h3)

set_option maxHeartbeats 1200000 in
private lemma checkBoxInt_sound (s u : ℕ) (A B C ln m0 p0 p1 : ℤ)
    (hdet : A * C - B ^ 2 = -(s : ℤ))
    (hA : A % 2 ≠ 0) (hC : C % 2 ≠ 0) (hCpos : 0 < C)
    (hm0 : 0 < m0) (hu : 0 < u) (hp0 : 0 ≤ p0)
    (hbox : checkBoxInt s u A B C ln m0 p0 p1 = true)
    (t : ℕ) (ht : t % 2 = 1) (m i : ℤ)
    (hm : m0 ≤ m) (hi0 : 0 ≤ i)
    (hpar : (m - i) % 2 = 0)
    (hi_lo : p0 * m ≤ D_SCALE * i) (hi_hi : D_SCALE * i ≤ p1 * m)
    (hc_bd : |4 * ((u : ℤ) * (m + i) * (m - i) - (t : ℤ)) - ln * m| ≤ 4 * (u : ℤ) * (2 * i + 2))
    (ht_lo : 4 * (u : ℤ) * (m - 1) ^ 2 - ln * (m - 1) + 1 ≤ 4 * (t : ℤ)) :
    IsRepresentable (s * t ^ 2) := by
  unfold checkBoxInt at hbox
  set D := D_SCALE
  have hDpos : (0 : ℤ) < D := by decide
  set a_lo := (u : ℤ) * (D + p0)
  set a_hi := (u : ℤ) * (D + p1)
  set d_lo := D - p1
  set d_hi := D - p0
  set q_m0 := (2 * D + m0 - 1) / m0
  set c_err := 4 * (u : ℤ) * (2 * p1 + q_m0)
  set c4_lo := D * ln - c_err
  set c4_hi := D * ln + c_err
  set Ba_lo := if 0 ≤ B then 4 * B * a_lo else 4 * B * a_hi
  set Ba_hi := if 0 ≤ B then 4 * B * a_hi else 4 * B * a_lo
  set W4_lo := Ba_lo + C * c4_lo
  set W4_hi := Ba_hi + C * c4_hi
  set W4_abs := max |W4_lo| |W4_hi|
  set W4_sq_hi := W4_abs * W4_abs
  set W4_sq_lo := if W4_lo ≤ 0 ∧ 0 ≤ W4_hi then 0 else min (W4_lo * W4_lo) (W4_hi * W4_hi)
  set CU16_lo := W4_sq_lo - 16 * (s : ℤ) * a_hi * a_hi
  set CU16_hi := W4_sq_hi - 16 * (s : ℤ) * a_lo * a_lo
  set CU16_abs := max |CU16_lo| |CU16_hi|
  set V16_abs := 16 * C * d_hi * d_hi +
    (32 * |B| * D * d_hi + m0 - 1) / m0 +
    (16 * |A| * D * D + m0 * m0 - 1) / (m0 * m0)
  set rem_c := max 0 (-(4 * (u : ℤ) + ln + 1))
  set t_num := 4 * (u : ℤ) * m0 - (8 * (u : ℤ) + max 0 ln) - (rem_c + m0 - 1) / m0
  set lhs_uv := m0 * (CU16_abs + C * V16_abs)
  set rhs_uv := 64 * (s : ℤ) * D ^ 4 * C * C * t_num * t_num
  set b_err := (|B| * D + m0 - 1) / m0
  set Bd_lo := C * d_lo - b_err
  set Bd_hi := C * d_hi + b_err
  set P_lo := min (min (W4_lo * Bd_lo) (W4_lo * Bd_hi)) (min (W4_hi * Bd_lo) (W4_hi * Bd_hi))
  set P_hi := max (max (W4_lo * Bd_lo) (W4_lo * Bd_hi)) (max (W4_hi * Bd_lo) (W4_hi * Bd_hi))
  set sa_hi := (4 * D * (s : ℤ) * a_hi + m0 - 1) / m0
  set CX4_abs := max |P_lo - sa_hi| |P_hi|
  set lhs_x := m0 * CX4_abs
  set rhs_x := (s : ℤ) * D ^ 4 * C * C * t_num * t_num
  have hbox' : (decide (0 ≤ d_lo) && decide (0 < t_num) &&
      decide (lhs_uv * lhs_uv ≤ rhs_uv) && decide (lhs_x * lhs_x ≤ rhs_x)) = true := hbox
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbox'
  rcases hbox' with ⟨⟨⟨hd_lo_nn, ht_num_pos⟩, huv_ok⟩, hx_ok⟩
  clear hbox
  -- Now establish all actual bounds on a, d, c, W, U, V, X
  have hm_pos : 0 < m := by linarith
  set a : ℤ := (u : ℤ) * (m + i)
  set d : ℤ := m - i
  set c : ℤ := a * d - (t : ℤ)
  have ha_even : a % 2 = 0 := by
    have hmi : (m + i) % 2 = 0 := by omega
    dsimp [a]; rw [Int.mul_emod, hmi]; simp
  have ha_lo : a_lo * m ≤ D * a := by
    dsimp [a_lo, a]
    have : (u : ℤ) * (D * m + p0 * m) ≤ (u : ℤ) * (D * m + D * i) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have ha_hi : D * a ≤ a_hi * m := by
    dsimp [a_hi, a]
    have : (u : ℤ) * (D * m + D * i) ≤ (u : ℤ) * (D * m + p1 * m) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have ha_nn : 0 ≤ D * a := by
    have : 0 ≤ a_lo := by dsimp [a_lo]; positivity
    nlinarith
  have hd_lo_b : d_lo * m ≤ D * d := by dsimp [d_lo, d]; linarith
  have hd_hi_b : D * d ≤ d_hi * m := by dsimp [d_hi, d]; linarith
  have hd_nn : 0 ≤ D * d := by nlinarith
  have h2D : 2 * D ≤ q_m0 * m := ceil_div_mul_ge hm0 hm (by dsimp [D, D_SCALE]; omega)
  have hc4_bd : |4 * D * c - D * ln * m| ≤ c_err * m := by
    have h1 : |4 * D * c - D * ln * m| = D * |4 * c - ln * m| := by
      rw [show 4 * D * c - D * ln * m = D * (4 * c - ln * m) by ring,
          abs_mul, abs_of_pos hDpos]
    rw [h1]
    have h2 : D * |4 * c - ln * m| ≤ D * (4 * (u : ℤ) * (2 * i + 2)) :=
      mul_le_mul_of_nonneg_left hc_bd (le_of_lt hDpos)
    have h3 : D * (4 * (u : ℤ) * (2 * i + 2)) = 4 * (u : ℤ) * (2 * (D * i) + 2 * D) := by ring
    have h4 : 2 * (D * i) + 2 * D ≤ (2 * p1 + q_m0) * m := by linarith
    have h5 : 4 * (u : ℤ) * (2 * (D * i) + 2 * D) ≤ 4 * (u : ℤ) * ((2 * p1 + q_m0) * m) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    dsimp [c_err]; linarith
  have hc4_lo : c4_lo * m ≤ 4 * D * c := by
    have := (abs_le.mp hc4_bd).1
    dsimp [c4_lo]; linarith
  have hc4_hi : 4 * D * c ≤ c4_hi * m := by
    have := (abs_le.mp hc4_bd).2
    dsimp [c4_hi]; linarith
  set W : ℤ := B * a + C * c
  have hW_lo : W4_lo * m ≤ 4 * D * W := by
    have hBa : Ba_lo * m ≤ 4 * B * (D * a) := by
      dsimp [Ba_lo]; split_ifs with hB <;> nlinarith
    have hCc : C * c4_lo * m ≤ C * (4 * D * c) := by nlinarith
    have : 4 * D * W = 4 * B * (D * a) + C * (4 * D * c) := by dsimp [W]; ring
    dsimp [W4_lo]; linarith
  have hW_hi : 4 * D * W ≤ W4_hi * m := by
    have hBa : 4 * B * (D * a) ≤ Ba_hi * m := by
      dsimp [Ba_hi]; split_ifs with hB <;> nlinarith
    have hCc : C * (4 * D * c) ≤ C * c4_hi * m := by nlinarith
    have : 4 * D * W = 4 * B * (D * a) + C * (4 * D * c) := by dsimp [W]; ring
    dsimp [W4_hi]; linarith
  -- Bound (4*D*W)^2
  have hWsq : W4_sq_lo * m ^ 2 ≤ (4 * D * W) ^ 2 ∧ (4 * D * W) ^ 2 ≤ W4_sq_hi * m ^ 2 := by
    have h := sq_mem_Icc_of_mem_Icc hW_lo hW_hi
    constructor
    · refine le_trans ?_ h.1
      dsimp [W4_sq_lo]
      by_cases h0 : W4_lo ≤ 0 ∧ 0 ≤ W4_hi
      · have h1 : W4_lo * m ≤ 0 ∧ 0 ≤ W4_hi * m :=
          ⟨mul_nonpos_of_nonpos_of_nonneg h0.1 (le_of_lt hm_pos),
           mul_nonneg h0.2 (le_of_lt hm_pos)⟩
        simp [h0, h1]
      · have h1 : ¬ (W4_lo * m ≤ 0 ∧ 0 ≤ W4_hi * m) := fun h1 =>
          h0 ⟨nonpos_of_mul_nonpos_left h1.1 hm_pos,
              nonneg_of_mul_nonneg_left h1.2 hm_pos⟩
        simp only [h0, h1, ↓reduceIte]
        have hL : W4_lo * W4_lo * m ^ 2 = (W4_lo * m) ^ 2 := by ring
        have hR : W4_hi * W4_hi * m ^ 2 = (W4_hi * m) ^ 2 := by ring
        rcases min_cases (W4_lo * W4_lo) (W4_hi * W4_hi) with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩
        · rw [hm1, hL]
          exact le_min le_rfl (by rw [← hL, ← hR]; exact mul_le_mul_of_nonneg_right hm2 (sq_nonneg m))
        · rw [hm1, hR]
          exact le_min (by rw [← hL, ← hR]; exact mul_le_mul_of_nonneg_right (le_of_lt hm2) (sq_nonneg m)) le_rfl
    · refine le_trans h.2 ?_
      have habs : max |W4_lo * m| |W4_hi * m| = W4_abs * m := by
        rw [abs_mul, abs_mul, abs_of_pos hm_pos]
        dsimp [W4_abs]
        exact (max_mul_of_nonneg |W4_lo| |W4_hi| (le_of_lt hm_pos)).symm
      rw [habs]
      dsimp [W4_sq_hi]; ring_nf; exact le_rfl
  -- Bound 16*D^2*C*U
  set U : ℤ := A * a ^ 2 + 2 * B * a * c + C * c ^ 2
  set V : ℤ := A + 2 * B * d + C * d ^ 2
  set X : ℤ := A * a + B * (a * d + c) + C * c * d
  have hCU_id : 16 * D ^ 2 * C * U = (4 * D * W) ^ 2 - 16 * (s : ℤ) * (D * a) ^ 2 := by
    dsimp [U, W]; linear_combination 16 * D ^ 2 * a ^ 2 * hdet
  have hCU_abs : |16 * D ^ 2 * C * U| ≤ CU16_abs * m ^ 2 := by
    have ha_lo_nn : 0 ≤ a_lo * m := by
      have : 0 ≤ a_lo := by dsimp [a_lo]; positivity
      exact mul_nonneg this (le_of_lt hm_pos)
    have hlo : CU16_lo * m ^ 2 ≤ 16 * D ^ 2 * C * U := by
      rw [hCU_id]; dsimp [CU16_lo]
      have hsq : (D * a) ^ 2 ≤ (a_hi * m) ^ 2 := by nlinarith only [ha_nn, ha_hi]
      have hmul : 16 * (s : ℤ) * (D * a) ^ 2 ≤ 16 * (s : ℤ) * (a_hi * m) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have hrew : 16 * (s : ℤ) * a_hi * a_hi * m ^ 2 = 16 * (s : ℤ) * (a_hi * m) ^ 2 := by ring
      linarith only [hWsq.1, hmul, hrew]
    have hhi : 16 * D ^ 2 * C * U ≤ CU16_hi * m ^ 2 := by
      rw [hCU_id]; dsimp [CU16_hi]
      have hsq : (a_lo * m) ^ 2 ≤ (D * a) ^ 2 := by nlinarith only [ha_lo_nn, ha_lo]
      have hmul : 16 * (s : ℤ) * (a_lo * m) ^ 2 ≤ 16 * (s : ℤ) * (D * a) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have hrew : 16 * (s : ℤ) * a_lo * a_lo * m ^ 2 = 16 * (s : ℤ) * (a_lo * m) ^ 2 := by ring
      linarith only [hWsq.2, hmul, hrew]
    have h := abs_le_max_of_mem_Icc hlo hhi
    have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
    have hmax : max |CU16_lo * m ^ 2| |CU16_hi * m ^ 2| = CU16_abs * m ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hm2]
      dsimp [CU16_abs]; exact (max_mul_of_nonneg _ _ hm2).symm
    exact h.trans hmax.le
  -- Bound 16*D^2*|V|
  have hV_abs : |16 * D ^ 2 * V| ≤ V16_abs * m ^ 2 := by
    have hVid : 16 * D ^ 2 * V = 16 * C * (D * d) ^ 2 + 32 * B * D * (D * d) + 16 * A * D ^ 2 := by
      dsimp [V]; ring
    rw [hVid]
    have h1 : |16 * C * (D * d) ^ 2 + 32 * B * D * (D * d) + 16 * A * D ^ 2| ≤
        |16 * C * (D * d) ^ 2| + |32 * B * D * (D * d)| + |16 * A * D ^ 2| := by
      have ha := abs_add_le (16 * C * (D * d) ^ 2 + 32 * B * D * (D * d)) (16 * A * D ^ 2)
      have hb := abs_add_le (16 * C * (D * d) ^ 2) (32 * B * D * (D * d))
      linarith only [ha, hb]
    have ht1 : |16 * C * (D * d) ^ 2| ≤ 16 * C * d_hi * d_hi * m ^ 2 := by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hCpos)) (sq_nonneg (D * d)))]
      have hsq : (D * d) ^ 2 ≤ (d_hi * m) ^ 2 := by nlinarith only [hd_nn, hd_hi_b]
      have hmul : 16 * C * (D * d) ^ 2 ≤ 16 * C * (d_hi * m) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num) (le_of_lt hCpos))
      have hrew : 16 * C * d_hi * d_hi * m ^ 2 = 16 * C * (d_hi * m) ^ 2 := by ring
      linarith only [hmul, hrew]
    have hd_hi_nn : 0 ≤ d_hi := nonneg_of_mul_nonneg_left (le_trans hd_nn hd_hi_b) hm_pos
    have ht2 : |32 * B * D * (D * d)| ≤ ((32 * |B| * D * d_hi + m0 - 1) / m0) * m ^ 2 := by
      have ha1 : |32 * B * D * (D * d)| = 32 * |B| * D * (D * d) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 32),
            abs_of_pos hDpos, abs_of_nonneg hd_nn]
      rw [ha1]
      have ha2 : 32 * |B| * D * (D * d) ≤ (32 * |B| * D * d_hi) * m := by
        have hnn : 0 ≤ 32 * |B| * D := by positivity
        have hmul := mul_le_mul_of_nonneg_left hd_hi_b hnn
        linarith only [hmul]
      have ha3 := ceil_div_mul_ge hm0 hm (by positivity : 0 ≤ 32 * |B| * D * d_hi)
      have ha4 := mul_le_mul_of_nonneg_right ha3 (le_of_lt hm_pos)
      have hrew : ((32 * |B| * D * d_hi + m0 - 1) / m0) * m * m =
          ((32 * |B| * D * d_hi + m0 - 1) / m0) * m ^ 2 := by ring
      linarith only [ha2, ha4, hrew]
    have ht3 : |16 * A * D ^ 2| ≤ ((16 * |A| * D * D + m0 * m0 - 1) / (m0 * m0)) * m ^ 2 := by
      have ha1 : |16 * A * D ^ 2| = 16 * |A| * D * D := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 16),
            abs_of_nonneg (sq_nonneg D)]; ring
      rw [ha1]
      have hm2 : m0 * m0 ≤ m ^ 2 := by nlinarith only [hm0, hm]
      exact ceil_div_mul_ge (by positivity : 0 < m0 * m0) hm2 (by positivity)
    dsimp [V16_abs]
    linarith only [h1, ht1, ht2, ht3]
  -- Lower bound on 4 * m0 * t
  have ht_m0 : t_num * m ^ 2 ≤ 4 * m0 * (t : ℤ) := by
    have h1 : 4 * (u : ℤ) * m ^ 2 - (8 * (u : ℤ) + ln) * m + (4 * (u : ℤ) + ln + 1) ≤ 4 * (t : ℤ) := by
      linarith only [ht_lo]
    have h2 : (8 * (u : ℤ) + ln) * m ≤ (8 * (u : ℤ) + max 0 ln) * m :=
      mul_le_mul_of_nonneg_right (by linarith only [le_max_right (0 : ℤ) ln]) (le_of_lt hm_pos)
    have h3 : -(4 * (u : ℤ) + ln + 1) ≤ rem_c := le_max_right _ _
    have h4 : rem_c * m0 ≤ ((rem_c + m0 - 1) / m0) * m ^ 2 := by
      have h4a := ceil_div_mul_ge hm0 hm (le_max_left 0 _ : 0 ≤ rem_c)
      have h4b := mul_le_mul_of_nonneg_right h4a (le_of_lt hm0)
      have h4c : 0 ≤ (rem_c + m0 - 1) / m0 := Int.ediv_nonneg (by linarith only [le_max_left (0 : ℤ) (-(4 * (u : ℤ) + ln + 1)), hm0]) (le_of_lt hm0)
      have h4d : ((rem_c + m0 - 1) / m0) * m * m0 ≤ ((rem_c + m0 - 1) / m0) * m ^ 2 := by
        have : m * m0 ≤ m ^ 2 := by nlinarith only [hm, hm_pos]
        have := mul_le_mul_of_nonneg_left this h4c
        linarith only [this]
      linarith only [h4b, h4d]
    have h5 : (8 * (u : ℤ) + max 0 ln) * m0 * m ≤ (8 * (u : ℤ) + max 0 ln) * m ^ 2 := by
      have hnn : 0 ≤ 8 * (u : ℤ) + max 0 ln := by linarith only [le_max_left (0 : ℤ) ln, hu]
      have : m0 * m ≤ m ^ 2 := by nlinarith only [hm, hm_pos]
      have := mul_le_mul_of_nonneg_left this hnn
      linarith only [this]
    have h1m := mul_le_mul_of_nonneg_left h1 (le_of_lt hm0)
    have h2m := mul_le_mul_of_nonneg_left h2 (le_of_lt hm0)
    have h3m := mul_le_mul_of_nonneg_right h3 (le_of_lt hm0)
    dsimp [t_num]; linarith only [h1m, h2m, h3m, h4, h5]
  -- Deduce (|U| + |V|)^2 ≤ 4 * s * t^2
  have hUV_final : (|U| + |V|) ^ 2 ≤ 4 * ((s * t ^ 2 : ℕ) : ℤ) := by
    have hmul : (16 * D ^ 2 * C * m0) * (|U| + |V|) ≤ lhs_uv * m ^ 2 := by
      have hU1 : 16 * D ^ 2 * C * |U| = |16 * D ^ 2 * C * U| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 16 * D ^ 2 * C)]
      have hV1 : 16 * D ^ 2 * |V| = |16 * D ^ 2 * V| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 16 * D ^ 2)]
      have hC_V := mul_le_mul_of_nonneg_left hV_abs (le_of_lt hCpos)
      rw [← hV1] at hC_V
      rw [← hU1] at hCU_abs
      have hsum : 16 * D ^ 2 * C * (|U| + |V|) ≤ (CU16_abs + C * V16_abs) * m ^ 2 := by
        have hL : 16 * D ^ 2 * C * (|U| + |V|) = 16 * D ^ 2 * C * |U| + C * (16 * D ^ 2 * |V|) := by ring
        have hR : (CU16_abs + C * V16_abs) * m ^ 2 = CU16_abs * m ^ 2 + C * (V16_abs * m ^ 2) := by ring
        linarith only [hCU_abs, hC_V, hL, hR]
      have hsum_m := mul_le_mul_of_nonneg_left hsum (le_of_lt hm0)
      dsimp [lhs_uv]; linarith only [hsum_m]
    have hsq1 : ((16 * D ^ 2 * C * m0) * (|U| + |V|)) ^ 2 ≤ (lhs_uv * m ^ 2) ^ 2 := by
      have hL_nn : 0 ≤ (16 * D ^ 2 * C * m0) * (|U| + |V|) := by positivity
      nlinarith only [hL_nn, hmul]
    have hsq2 : (lhs_uv * m ^ 2) ^ 2 ≤ 64 * (s : ℤ) * D ^ 4 * C * C * (t_num * m ^ 2) ^ 2 := by
      have h1 : (lhs_uv * m ^ 2) ^ 2 = (lhs_uv * lhs_uv) * m ^ 4 := by ring
      have h2 : 64 * (s : ℤ) * D ^ 4 * C * C * (t_num * m ^ 2) ^ 2 = rhs_uv * m ^ 4 := by
        dsimp [rhs_uv]; ring
      have hm4 : 0 ≤ m ^ 4 := by positivity
      have h3 := mul_le_mul_of_nonneg_right huv_ok hm4
      linarith only [h1, h2, h3]
    have hsq3 : 64 * (s : ℤ) * D ^ 4 * C * C * (t_num * m ^ 2) ^ 2 ≤
        64 * (s : ℤ) * D ^ 4 * C * C * (4 * m0 * (t : ℤ)) ^ 2 := by
      have htnn : 0 ≤ t_num * m ^ 2 := mul_nonneg (le_of_lt ht_num_pos) (sq_nonneg m)
      have htsq : (t_num * m ^ 2) ^ 2 ≤ (4 * m0 * (t : ℤ)) ^ 2 := by nlinarith only [htnn, ht_m0]
      exact mul_le_mul_of_nonneg_left htsq
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg s))
          (pow_nonneg (le_of_lt hDpos) 4)) (le_of_lt hCpos)) (le_of_lt hCpos))
    have hK_pos : 0 < (16 * D ^ 2 * C * m0) ^ 2 :=
      sq_pos_of_pos (mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hDpos)) hCpos) hm0)
    have hfinal : (16 * D ^ 2 * C * m0) ^ 2 * (|U| + |V|) ^ 2 ≤
        (16 * D ^ 2 * C * m0) ^ 2 * (4 * ((s * t ^ 2 : ℕ) : ℤ)) := by
      push_cast
      have hL : (16 * D ^ 2 * C * m0) ^ 2 * (|U| + |V|) ^ 2 =
          ((16 * D ^ 2 * C * m0) * (|U| + |V|)) ^ 2 := by ring
      have hR : (16 * D ^ 2 * C * m0) ^ 2 * (4 * ((s : ℤ) * (t : ℤ) ^ 2)) =
          64 * (s : ℤ) * D ^ 4 * C * C * (4 * m0 * (t : ℤ)) ^ 2 := by ring
      linarith only [hsq1, hsq2, hsq3, hL, hR]
    exact le_of_mul_le_mul_left hfinal hK_pos
  -- Deduce X^2 ≤ s * t^2
  have hX_final : X ^ 2 ≤ ((s * t ^ 2 : ℕ) : ℤ) := by
    have hCX_id : 4 * D ^ 2 * C * X = (4 * D * W) * (C * (D * d) + B * D) - 4 * D * (s : ℤ) * (D * a) := by
      dsimp [X, W]; linear_combination 4 * D ^ 2 * a * hdet
    have hBD_err : |B * D| ≤ b_err * m := by
      have : |B * D| = |B| * D := by rw [abs_mul, abs_of_pos hDpos]
      rw [this]
      exact ceil_div_mul_ge hm0 hm (by positivity)
    have hBd_lo : Bd_lo * m ≤ C * (D * d) + B * D := by
      have h1 := (abs_le.mp hBD_err).1
      have h2 := mul_le_mul_of_nonneg_left hd_lo_b (le_of_lt hCpos)
      dsimp [Bd_lo]; linarith only [h1, h2]
    have hBd_hi : C * (D * d) + B * D ≤ Bd_hi * m := by
      have h1 := (abs_le.mp hBD_err).2
      have h2 := mul_le_mul_of_nonneg_left hd_hi_b (le_of_lt hCpos)
      dsimp [Bd_hi]; linarith only [h1, h2]
    have hprod := mul_mem_Icc hW_lo hW_hi hBd_lo hBd_hi
    have hP_lo : P_lo * m ^ 2 ≤ (4 * D * W) * (C * (D * d) + B * D) := by
      refine le_trans ?_ hprod.1
      have h1 : (W4_lo * m) * (Bd_lo * m) = (W4_lo * Bd_lo) * m ^ 2 := by ring
      have h2 : (W4_lo * m) * (Bd_hi * m) = (W4_lo * Bd_hi) * m ^ 2 := by ring
      have h3 : (W4_hi * m) * (Bd_lo * m) = (W4_hi * Bd_lo) * m ^ 2 := by ring
      have h4 : (W4_hi * m) * (Bd_hi * m) = (W4_hi * Bd_hi) * m ^ 2 := by ring
      rw [h1, h2, h3, h4]
      dsimp [P_lo]
      have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
      rw [← min_mul_of_nonneg _ _ hm2, ← min_mul_of_nonneg _ _ hm2, ← min_mul_of_nonneg _ _ hm2]
    have hP_hi : (4 * D * W) * (C * (D * d) + B * D) ≤ P_hi * m ^ 2 := by
      refine le_trans hprod.2 ?_
      have h1 : (W4_lo * m) * (Bd_lo * m) = (W4_lo * Bd_lo) * m ^ 2 := by ring
      have h2 : (W4_lo * m) * (Bd_hi * m) = (W4_lo * Bd_hi) * m ^ 2 := by ring
      have h3 : (W4_hi * m) * (Bd_lo * m) = (W4_hi * Bd_lo) * m ^ 2 := by ring
      have h4 : (W4_hi * m) * (Bd_hi * m) = (W4_hi * Bd_hi) * m ^ 2 := by ring
      rw [h1, h2, h3, h4]
      dsimp [P_hi]
      have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
      rw [← max_mul_of_nonneg _ _ hm2, ← max_mul_of_nonneg _ _ hm2, ← max_mul_of_nonneg _ _ hm2]
    have hsa_nn : 0 ≤ 4 * D * (s : ℤ) * (D * a) := by positivity
    have ha_hi_nn : 0 ≤ a_hi := nonneg_of_mul_nonneg_left (le_trans ha_nn ha_hi) hm_pos
    have hsa_ub : 4 * D * (s : ℤ) * (D * a) ≤ sa_hi * m ^ 2 := by
      have h1 : 4 * D * (s : ℤ) * (D * a) ≤ (4 * D * (s : ℤ) * a_hi) * m := by
        have hmul := mul_le_mul_of_nonneg_left ha_hi (by positivity : 0 ≤ 4 * D * (s : ℤ))
        linarith only [hmul]
      have h2 := ceil_div_mul_ge hm0 hm (by positivity : 0 ≤ 4 * D * (s : ℤ) * a_hi)
      have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt hm_pos)
      have hrew : sa_hi * m * m = sa_hi * m ^ 2 := by ring
      linarith only [h1, h3, hrew]
    have hCX_lo : (P_lo - sa_hi) * m ^ 2 ≤ 4 * D ^ 2 * C * X := by
      rw [hCX_id]; linarith only [hP_lo, hsa_ub]
    have hCX_hi : 4 * D ^ 2 * C * X ≤ P_hi * m ^ 2 := by
      rw [hCX_id]; linarith only [hP_hi, hsa_nn]
    have hCX_abs : |4 * D ^ 2 * C * X| ≤ CX4_abs * m ^ 2 := by
      have h := abs_le_max_of_mem_Icc hCX_lo hCX_hi
      have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
      have hmax : max |(P_lo - sa_hi) * m ^ 2| |P_hi * m ^ 2| = CX4_abs * m ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hm2]
        dsimp [CX4_abs]; exact (max_mul_of_nonneg _ _ hm2).symm
      exact h.trans hmax.le
    have hmul : |4 * D ^ 2 * C * m0 * X| ≤ lhs_x * m ^ 2 := by
      have h1 : |4 * D ^ 2 * C * m0 * X| = m0 * |4 * D ^ 2 * C * X| := by
        rw [show 4 * D ^ 2 * C * m0 * X = m0 * (4 * D ^ 2 * C * X) by ring,
            abs_mul, abs_of_pos hm0]
      have h2 := mul_le_mul_of_nonneg_left hCX_abs (le_of_lt hm0)
      rw [h1]; dsimp [lhs_x]; linarith only [h2]
    have hsq1 : (4 * D ^ 2 * C * m0 * X) ^ 2 ≤ (lhs_x * m ^ 2) ^ 2 := by
      rw [← sq_abs (4 * D ^ 2 * C * m0 * X)]
      nlinarith only [abs_nonneg (4 * D ^ 2 * C * m0 * X), hmul]
    have hsq2 : (lhs_x * m ^ 2) ^ 2 ≤ (s : ℤ) * D ^ 4 * C * C * (t_num * m ^ 2) ^ 2 := by
      have h1 : (lhs_x * m ^ 2) ^ 2 = (lhs_x * lhs_x) * m ^ 4 := by ring
      have h2 : (s : ℤ) * D ^ 4 * C * C * (t_num * m ^ 2) ^ 2 = rhs_x * m ^ 4 := by
        dsimp [rhs_x]; ring
      have h3 := mul_le_mul_of_nonneg_right hx_ok (by positivity : 0 ≤ m ^ 4)
      linarith only [h1, h2, h3]
    have hsq3 : (s : ℤ) * D ^ 4 * C * C * (t_num * m ^ 2) ^ 2 ≤
        (s : ℤ) * D ^ 4 * C * C * (4 * m0 * (t : ℤ)) ^ 2 := by
      have htnn : 0 ≤ t_num * m ^ 2 := mul_nonneg (le_of_lt ht_num_pos) (sq_nonneg m)
      have htsq : (t_num * m ^ 2) ^ 2 ≤ (4 * m0 * (t : ℤ)) ^ 2 := by nlinarith only [htnn, ht_m0]
      exact mul_le_mul_of_nonneg_left htsq
        (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg s)
          (pow_nonneg (le_of_lt hDpos) 4)) (le_of_lt hCpos)) (le_of_lt hCpos))
    have hK_pos : 0 < (4 * D ^ 2 * C * m0) ^ 2 :=
      sq_pos_of_pos (mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hDpos)) hCpos) hm0)
    have hfinal : (4 * D ^ 2 * C * m0) ^ 2 * X ^ 2 ≤
        (4 * D ^ 2 * C * m0) ^ 2 * ((s * t ^ 2 : ℕ) : ℤ) := by
      push_cast
      have hL : (4 * D ^ 2 * C * m0) ^ 2 * X ^ 2 = (4 * D ^ 2 * C * m0 * X) ^ 2 := by ring
      have hR : (4 * D ^ 2 * C * m0) ^ 2 * ((s : ℤ) * (t : ℤ) ^ 2) =
          (s : ℤ) * D ^ 4 * C * C * (4 * m0 * (t : ℤ)) ^ 2 := by ring
      linarith only [hsq1, hsq2, hsq3, hL, hR]
    exact le_of_mul_le_mul_left hfinal hK_pos
  exact matrix_repr s t A B C a d hdet hA hC ha_even hpar ht
    (by simpa [X, c] using hX_final) (by simpa [U, V, c] using hUV_final)

private def checkTail (s u : ℕ) (A B C ln m0 p_max : ℤ) : Bool :=
  let D := D_SCALE
  let neg_ln := max 0 (-ln)
  decide (0 < m0) &&
  decide (0 < u) &&
  decide (0 < C) &&
  decide (A * C - B ^ 2 = -(s : ℤ)) &&
  decide (A % 2 ≠ 0) &&
  decide (C % 2 ≠ 0) &&
  decide (ln ≤ 4 * (u : ℤ) * (m0 - 1)) &&
  decide (D ≤ p_max * m0) &&
  decide (p_max ≤ D) &&
  decide (D * D * (8 * (u : ℤ) * m0 + neg_ln) ≤ 4 * (u : ℤ) * (p_max * m0 - D) ^ 2) &&
  decide (D * D ≤ p_max * (p_max * m0 - D)) &&
  (List.range 8).all fun k =>
    let p0 := (p_max * (k : ℤ)) / 8
    let p1 := (p_max * ((k : ℤ) + 1) + 7) / 8
    checkBoxInt s u A B C ln m0 p0 p1

set_option maxHeartbeats 1200000 in
private lemma checkTail_sound (s u : ℕ) (A B C ln m0 p_max : ℤ)
    (hcheck : checkTail s u A B C ln m0 p_max = true)
    (t : ℕ) (ht : t % 2 = 1)
    (ht_big : 4 * (u : ℤ) * (m0 - 1) ^ 2 - ln * (m0 - 1) < 4 * (t : ℤ)) :
    IsRepresentable (s * t ^ 2) := by
  unfold checkTail at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm0_pos, hu_pos⟩, hC_pos⟩, hdet⟩, hA_odd⟩, hC_odd⟩, hln_le⟩,
      hpD⟩, hp_leD⟩, hquad0⟩, hderiv0⟩, hstrips⟩
  -- Find least natural number m ≥ 1 with 4*u*m^2 - ln*m ≥ 4*t
  have hex : ∃ m : ℕ, 4 * (t : ℤ) ≤ 4 * (u : ℤ) * (m : ℤ) ^ 2 - ln * (m : ℤ) := by
    refine ⟨(t + 1) + Int.toNat (max 0 ln) + 1, ?_⟩
    set M : ℤ := ((t + 1 + Int.toNat (max 0 ln) + 1 : ℕ) : ℤ)
    have hM1 : (t : ℤ) + 1 ≤ M := by omega
    have hM2 : ln ≤ M := by omega
    have hu1 : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu_pos
    nlinarith
  classical
  let mN : ℕ := Nat.find hex
  have hmN_spec : 4 * (t : ℤ) ≤ 4 * (u : ℤ) * (mN : ℤ) ^ 2 - ln * (mN : ℤ) := Nat.find_spec hex
  have hmN_ge : m0 ≤ (mN : ℤ) := by
    by_contra hlt
    push Not at hlt
    have hm1 : (mN : ℤ) ≤ m0 - 1 := by omega
    have hm_nn : (0 : ℤ) ≤ (mN : ℤ) := Nat.cast_nonneg mN
    -- 4*u*x^2 - ln*x <= 4*u*(m0-1)^2 - ln*(m0-1) for 0 <= x <= m0-1 since ln <= 4*u*(m0-1)
    have hmono : 4 * (u : ℤ) * (mN : ℤ) ^ 2 - ln * (mN : ℤ) ≤
        4 * (u : ℤ) * (m0 - 1) ^ 2 - ln * (m0 - 1) := by
      have hdiff : (4 * (u : ℤ) * (m0 - 1) ^ 2 - ln * (m0 - 1)) -
          (4 * (u : ℤ) * (mN : ℤ) ^ 2 - ln * (mN : ℤ)) =
          ((m0 - 1) - (mN : ℤ)) * (4 * (u : ℤ) * ((m0 - 1) + (mN : ℤ)) - ln) := by ring
      have hf1 : 0 ≤ (m0 - 1) - (mN : ℤ) := by linarith
      have hf2 : 0 ≤ 4 * (u : ℤ) * ((m0 - 1) + (mN : ℤ)) - ln := by nlinarith
      nlinarith
    linarith
  have hmN_pos : 0 < mN := by omega
  have hmN_prev : 4 * (u : ℤ) * ((mN : ℤ) - 1) ^ 2 - ln * ((mN : ℤ) - 1) < 4 * (t : ℤ) := by
    have hlt : mN - 1 < mN := by omega
    have hnot := Nat.find_min hex hlt
    push Not at hnot
    have hcast : ((mN - 1 : ℕ) : ℤ) = (mN : ℤ) - 1 := by omega
    rwa [hcast] at hnot
  set m : ℤ := (mN : ℤ)
  have ht_lo : 4 * (u : ℤ) * (m - 1) ^ 2 - ln * (m - 1) + 1 ≤ 4 * (t : ℤ) := by omega
  set r_sc : ℤ := 4 * (u : ℤ) * m ^ 2 - ln * m - 4 * (t : ℤ)
  have hr_nn : 0 ≤ r_sc := by dsimp [r_sc]; linarith
  have hr_ub : r_sc < 8 * (u : ℤ) * m + max 0 (-ln) := by
    have h1 : r_sc < 4 * (u : ℤ) * (2 * m - 1) - ln := by dsimp [r_sc]; linarith
    have h2 : -ln ≤ max 0 (-ln) := le_max_right _ _
    nlinarith
  let rN : ℕ := Int.toNat r_sc
  have hrN_eq : (rN : ℤ) = r_sc := Int.toNat_of_nonneg hr_nn
  let i0N : ℕ := Nat.sqrt (rN / (4 * u))
  have hi0_lo : 4 * (u : ℤ) * (i0N : ℤ) ^ 2 ≤ r_sc := by
    have h1 : i0N * i0N ≤ rN / (4 * u) := Nat.sqrt_le _
    have h2 : 4 * u * (i0N * i0N) ≤ rN := by
      calc 4 * u * (i0N * i0N) ≤ 4 * u * (rN / (4 * u)) := Nat.mul_le_mul_left _ h1
        _ ≤ rN := Nat.mul_div_le rN (4 * u)
    have h3 : (4 * (u : ℤ)) * ((i0N : ℤ) * (i0N : ℤ)) ≤ (rN : ℤ) := by exact_mod_cast h2
    rw [hrN_eq] at h3; linarith [sq (i0N : ℤ)]
  have hi0_hi : r_sc < 4 * (u : ℤ) * ((i0N : ℤ) + 1) ^ 2 := by
    have h1 : rN / (4 * u) < (i0N + 1) * (i0N + 1) := Nat.lt_succ_sqrt _
    have h2 : rN < 4 * u * ((i0N + 1) * (i0N + 1)) := by
      have := Nat.div_add_mod rN (4 * u)
      have := Nat.mod_lt rN (by omega : 0 < 4 * u)
      nlinarith
    have h3 : (rN : ℤ) < 4 * (u : ℤ) * (((i0N : ℤ) + 1) * ((i0N : ℤ) + 1)) := by exact_mod_cast h2
    rw [hrN_eq] at h3; linarith [sq ((i0N : ℤ) + 1)]
  -- Pick i of same parity as mN closest to i0N
  let iN : ℕ :=
    if i0N % 2 = mN % 2 then i0N
    else if 1 ≤ i0N ∧ r_sc ≤ 4 * (u : ℤ) * ((i0N : ℤ) ^ 2 + 1) then i0N - 1
    else i0N + 1
  set i : ℤ := (iN : ℤ)
  have hi_nn : 0 ≤ i := Nat.cast_nonneg iN
  have hi_le : i ≤ (i0N : ℤ) + 1 := by dsimp [i, iN]; split_ifs <;> omega
  have hpar : (m - i) % 2 = 0 := by
    have : iN % 2 = mN % 2 := by dsimp [iN]; split_ifs <;> omega
    dsimp [m, i]; omega
  have hc_bd : |4 * ((u : ℤ) * (m + i) * (m - i) - (t : ℤ)) - ln * m| ≤ 4 * (u : ℤ) * (2 * i + 2) := by
    have hid : 4 * ((u : ℤ) * (m + i) * (m - i) - (t : ℤ)) - ln * m = r_sc - 4 * (u : ℤ) * i ^ 2 := by
      dsimp [r_sc]; ring
    rw [hid, abs_le]
    dsimp [i, iN]
    split_ifs with h1 h2
    · constructor <;> nlinarith
    · have hcast : ((i0N - 1 : ℕ) : ℤ) = (i0N : ℤ) - 1 := by omega
      rw [hcast]
      constructor <;> nlinarith
    · push_cast
      by_cases hi0z : i0N = 0
      · rw [hi0z] at hi0_lo hi0_hi ⊢; simp at hi0_lo hi0_hi ⊢; constructor <;> nlinarith
      · have hgt : 4 * (u : ℤ) * ((i0N : ℤ) ^ 2 + 1) < r_sc := by
          by_contra hle; push Not at hle
          exact h2 ⟨by omega, hle⟩
        constructor <;> nlinarith
  -- Show D * i <= p_max * m
  have hD_pos : (0 : ℤ) < D_SCALE := by decide
  have hp_pos : 0 < p_max := by nlinarith
  have hi_upper : D_SCALE * i ≤ p_max * m := by
    have hpmD : 0 ≤ p_max * m - D_SCALE := by nlinarith
    have hquad_m : D_SCALE ^ 2 * (8 * (u : ℤ) * m + max 0 (-ln)) ≤
        4 * (u : ℤ) * (p_max * m - D_SCALE) ^ 2 := by
      have hdiff : 4 * (u : ℤ) * (p_max * m - D_SCALE) ^ 2 -
          D_SCALE ^ 2 * (8 * (u : ℤ) * m + max 0 (-ln)) =
          (4 * (u : ℤ) * (p_max * m0 - D_SCALE) ^ 2 -
            D_SCALE ^ 2 * (8 * (u : ℤ) * m0 + max 0 (-ln))) +
          4 * (u : ℤ) * (m - m0) *
            (p_max ^ 2 * (m - m0) + 2 * (p_max * (p_max * m0 - D_SCALE) - D_SCALE ^ 2)) := by ring
      have hsqD : D_SCALE * D_SCALE = D_SCALE ^ 2 := (sq D_SCALE).symm
      rw [hsqD] at hquad0 hderiv0
      have h1 : 0 ≤ 4 * (u : ℤ) * (p_max * m0 - D_SCALE) ^ 2 -
          D_SCALE ^ 2 * (8 * (u : ℤ) * m0 + max 0 (-ln)) := by linarith
      have h2 : 0 ≤ p_max * (p_max * m0 - D_SCALE) - D_SCALE ^ 2 := by linarith
      have h3 : 0 ≤ m - m0 := by linarith
      have h4 : 0 ≤ p_max ^ 2 * (m - m0) + 2 * (p_max * (p_max * m0 - D_SCALE) - D_SCALE ^ 2) := by
        nlinarith [sq_nonneg p_max]
      have h5 : 0 ≤ 4 * (u : ℤ) * (m - m0) *
          (p_max ^ 2 * (m - m0) + 2 * (p_max * (p_max * m0 - D_SCALE) - D_SCALE ^ 2)) :=
        mul_nonneg (mul_nonneg (by positivity) h3) h4
      linarith
    have hDi0_sq : (D_SCALE * (i0N : ℤ)) ^ 2 ≤ (p_max * m - D_SCALE) ^ 2 := by
      have h1 : 4 * (u : ℤ) * (D_SCALE * (i0N : ℤ)) ^ 2 = D_SCALE ^ 2 * (4 * (u : ℤ) * (i0N : ℤ) ^ 2) := by ring
      have h2 : D_SCALE ^ 2 * (4 * (u : ℤ) * (i0N : ℤ) ^ 2) ≤ D_SCALE ^ 2 * (8 * (u : ℤ) * m + max 0 (-ln)) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg D_SCALE)
      have h3 : 4 * (u : ℤ) * (D_SCALE * (i0N : ℤ)) ^ 2 ≤ 4 * (u : ℤ) * (p_max * m - D_SCALE) ^ 2 := by linarith
      exact le_of_mul_le_mul_left h3 (by positivity : (0 : ℤ) < 4 * (u : ℤ))
    have hDi0 : D_SCALE * (i0N : ℤ) ≤ p_max * m - D_SCALE := by nlinarith
    nlinarith
  -- Locate strip k in 0..7 such that p0 * m <= D_SCALE * i <= p1 * m
  have hm_pos : 0 < m := by linarith
  have hpm_pos : 0 < p_max * m := mul_pos hp_pos hm_pos
  let kZ : ℤ := min 7 ((8 * D_SCALE * i) / (p_max * m))
  have hk_nn : 0 ≤ kZ := by
    dsimp [kZ]
    exact le_min (by omega) (Int.ediv_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hD_pos)) hi_nn) (le_of_lt hpm_pos))
  have hk_lt : kZ < 8 := by dsimp [kZ]; exact lt_of_le_of_lt (min_le_left _ _) (by omega)
  let kN : ℕ := Int.toNat kZ
  have hkN_eq : (kN : ℤ) = kZ := Int.toNat_of_nonneg hk_nn
  have hkN_lt : kN < 8 := by omega
  have hstrip := hstrips kN hkN_lt
  rw [hkN_eq] at hstrip
  have hp0_nn : 0 ≤ (p_max * kZ) / 8 := Int.ediv_nonneg (mul_nonneg (le_of_lt hp_pos) hk_nn) (by omega)
  have hlo_strip : ((p_max * kZ) / 8) * m ≤ D_SCALE * i := by
    have h1 : kZ * (p_max * m) ≤ 8 * D_SCALE * i := by
      have h1a : kZ ≤ (8 * D_SCALE * i) / (p_max * m) := min_le_right _ _
      have h1b : ((8 * D_SCALE * i) / (p_max * m)) * (p_max * m) ≤ 8 * D_SCALE * i := by
        have hmod := Int.emod_add_mul_ediv (8 * D_SCALE * i) (p_max * m)
        have hnn := Int.emod_nonneg (8 * D_SCALE * i) (ne_of_gt hpm_pos)
        linarith
      exact le_trans (mul_le_mul_of_nonneg_right h1a (le_of_lt hpm_pos)) h1b
    have h2 : 8 * ((p_max * kZ) / 8) ≤ p_max * kZ := by omega
    have h3 : 8 * (((p_max * kZ) / 8) * m) ≤ 8 * (D_SCALE * i) := by
      calc 8 * (((p_max * kZ) / 8) * m) = (8 * ((p_max * kZ) / 8)) * m := by ring
        _ ≤ (p_max * kZ) * m := mul_le_mul_of_nonneg_right h2 (le_of_lt hm_pos)
        _ = kZ * (p_max * m) := by ring
        _ ≤ 8 * D_SCALE * i := h1
        _ = 8 * (D_SCALE * i) := by ring
    linarith
  have hhi_strip : D_SCALE * i ≤ ((p_max * (kZ + 1) + 7) / 8) * m := by
    have h1 : 8 * D_SCALE * i ≤ (kZ + 1) * (p_max * m) := by
      dsimp [kZ]
      rcases min_cases (7 : ℤ) ((8 * D_SCALE * i) / (p_max * m)) with ⟨heq, _⟩ | ⟨heq, _⟩
      · rw [heq]; linarith [hi_upper]
      · rw [heq]
        have hmod := Int.emod_add_mul_ediv (8 * D_SCALE * i) (p_max * m)
        have hlt := Int.emod_lt_of_pos (8 * D_SCALE * i) hpm_pos
        linarith
    have h2 : p_max * (kZ + 1) ≤ 8 * ((p_max * (kZ + 1) + 7) / 8) := by omega
    have h3 : 8 * (D_SCALE * i) ≤ 8 * (((p_max * (kZ + 1) + 7) / 8) * m) := by
      calc 8 * (D_SCALE * i) = 8 * D_SCALE * i := by ring
        _ ≤ (kZ + 1) * (p_max * m) := h1
        _ = (p_max * (kZ + 1)) * m := by ring
        _ ≤ (8 * ((p_max * (kZ + 1) + 7) / 8)) * m := mul_le_mul_of_nonneg_right h2 (le_of_lt hm_pos)
        _ = 8 * (((p_max * (kZ + 1) + 7) / 8) * m) := by ring
    linarith
  exact checkBoxInt_sound s u A B C ln m0 _ _ hdet hA_odd hC_odd hC_pos hm0_pos hu_pos
    hp0_nn hstrip t ht m i hmN_ge hi_nn hpar hlo_strip hhi_strip hc_bd ht_lo

/-! ### Finite Bisection + Leaf Verifier -/

private def checkTInterval (s : ℕ) (A B C a d : ℤ) (t_lo t_hi : ℕ) : Bool :=
  if t_lo == 0 then false else
  let c_lo := a * d - (t_hi : ℤ)
  let c_hi := a * d - (t_lo : ℤ)
  let W_lo := B * a + C * c_lo
  let W_hi := B * a + C * c_hi
  let W_max := max |W_lo| |W_hi|
  let W_sq_min := if W_lo ≤ 0 ∧ 0 ≤ W_hi then 0 else min (W_lo * W_lo) (W_hi * W_hi)
  let W_sq_max := W_max * W_max
  let CU_abs := max |W_sq_min - (s : ℤ) * a * a| |W_sq_max - (s : ℤ) * a * a|
  let V := A + 2 * B * d + C * d * d
  let tmin : ℤ := (t_lo : ℤ)
  if (CU_abs + C * |V|) ^ 2 > 4 * C * C * (s : ℤ) * tmin * tmin then false else
  let Bd := B + C * d
  let CX_abs := max |W_lo * Bd - (s : ℤ) * a| |W_hi * Bd - (s : ℤ) * a|
  decide (CX_abs * CX_abs ≤ C * C * (s : ℤ) * tmin * tmin)

set_option maxHeartbeats 1200000 in
private lemma checkTInterval_sound (s : ℕ) (A B C a d : ℤ) (t_lo t_hi : ℕ)
    (hdet : A * C - B ^ 2 = -(s : ℤ))
    (hA : A % 2 ≠ 0) (hC : C % 2 ≠ 0) (hCpos : 0 < C)
    (ha : a % 2 = 0) (hd : d % 2 = 0)
    (hok : checkTInterval s A B C a d t_lo t_hi = true)
    (t : ℕ) (ht_lo : t_lo ≤ t) (ht_hi : t ≤ t_hi) (ht : t % 2 = 1) :
    IsRepresentable (s * t ^ 2) := by
  unfold checkTInterval at hok
  dsimp only at hok
  by_cases h0 : (t_lo == 0) = true
  · simp [h0] at hok
  simp only [h0, Bool.false_eq_true, ↓reduceIte] at hok
  set c_lo := a * d - (t_hi : ℤ)
  set c_hi := a * d - (t_lo : ℤ)
  set W_lo := B * a + C * c_lo
  set W_hi := B * a + C * c_hi
  set W_max := max |W_lo| |W_hi|
  set W_sq_min := if W_lo ≤ 0 ∧ 0 ≤ W_hi then 0 else min (W_lo * W_lo) (W_hi * W_hi)
  set W_sq_max := W_max * W_max
  set CU_abs := max |W_sq_min - (s : ℤ) * a * a| |W_sq_max - (s : ℤ) * a * a|
  set V := A + 2 * B * d + C * d * d
  set tmin : ℤ := (t_lo : ℤ)
  by_cases huv_bad : (CU_abs + C * |V|) ^ 2 > 4 * C * C * (s : ℤ) * tmin * tmin
  · simp [huv_bad] at hok
  simp only [huv_bad, ↓reduceIte] at hok
  have huv_ok : (CU_abs + C * |V|) ^ 2 ≤ 4 * C * C * (s : ℤ) * tmin * tmin := by linarith
  set Bd := B + C * d
  set CX_abs := max |W_lo * Bd - (s : ℤ) * a| |W_hi * Bd - (s : ℤ) * a|
  have hx_ok : CX_abs * CX_abs ≤ C * C * (s : ℤ) * tmin * tmin := of_decide_eq_true hok
  set c : ℤ := a * d - (t : ℤ)
  set W : ℤ := B * a + C * c
  set U : ℤ := A * a ^ 2 + 2 * B * a * c + C * c ^ 2
  set X : ℤ := A * a + B * (a * d + c) + C * c * d
  have hW_lo : W_lo ≤ W := by dsimp [W_lo, W, c_lo, c]; nlinarith
  have hW_hi : W ≤ W_hi := by dsimp [W_hi, W, c_hi, c]; nlinarith
  have hWsq := sq_mem_Icc_of_mem_Icc hW_lo hW_hi
  have hCU_id : C * U = W ^ 2 - (s : ℤ) * a * a := by
    dsimp [U, W]; linear_combination a ^ 2 * hdet
  have hCU_bd : |C * U| ≤ CU_abs := by
    rw [hCU_id]
    have h1 : W_sq_min - (s : ℤ) * a * a ≤ W ^ 2 - (s : ℤ) * a * a := by
      have hmin : W_sq_min ≤ W ^ 2 := by
        dsimp [W_sq_min]
        have := hWsq.1
        simp only [sq] at this ⊢
        exact this
      linarith
    have h2 : W ^ 2 - (s : ℤ) * a * a ≤ W_sq_max - (s : ℤ) * a * a := by
      have hmax : W ^ 2 ≤ W_sq_max := by
        dsimp [W_sq_max, W_max]
        have := hWsq.2
        simp only [sq] at this ⊢
        exact this
      linarith
    exact abs_le_max_of_mem_Icc h1 h2
  have hCX_id : C * X = W * Bd - (s : ℤ) * a := by
    dsimp [X, W, Bd]; linear_combination a * hdet
  have hCX_bd : |C * X| ≤ CX_abs := by
    rw [hCX_id]
    rcases le_total 0 Bd with hBd | hBd
    · exact abs_le_max_of_mem_Icc (x := W * Bd - (s : ℤ) * a) (by nlinarith) (by nlinarith)
    · have h := abs_le_max_of_mem_Icc (x := W * Bd - (s : ℤ) * a)
        (lo := W_hi * Bd - (s : ℤ) * a) (hi := W_lo * Bd - (s : ℤ) * a)
        (by nlinarith) (by nlinarith)
      rwa [max_comm] at h
  have ht_sq : tmin * tmin ≤ (t : ℤ) ^ 2 := by
    have h1 : tmin ≤ (t : ℤ) := by dsimp [tmin]; exact_mod_cast ht_lo
    have h2 : 0 ≤ tmin := by dsimp [tmin]; exact Nat.cast_nonneg t_lo
    nlinarith
  have hC2_pos : 0 < C ^ 2 := sq_pos_of_pos hCpos
  have hUV : (|U| + |V|) ^ 2 ≤ 4 * ((s * t ^ 2 : ℕ) : ℤ) := by
    have h1 : C * (|U| + |V|) ≤ CU_abs + C * |V| := by
      have : C * |U| = |C * U| := by rw [abs_mul, abs_of_pos hCpos]
      linarith
    have h2 : (C * (|U| + |V|)) ^ 2 ≤ (CU_abs + C * |V|) ^ 2 := by
      have : 0 ≤ C * (|U| + |V|) := by positivity
      nlinarith
    have h3 : 4 * C * C * (s : ℤ) * tmin * tmin ≤ 4 * C ^ 2 * ((s * t ^ 2 : ℕ) : ℤ) := by
      push_cast; nlinarith [show 0 ≤ 4 * C ^ 2 * (s : ℤ) by positivity]
    have h4 : C ^ 2 * (|U| + |V|) ^ 2 ≤ C ^ 2 * (4 * ((s * t ^ 2 : ℕ) : ℤ)) := by
      have hL : C ^ 2 * (|U| + |V|) ^ 2 = (C * (|U| + |V|)) ^ 2 := by ring
      linarith
    exact le_of_mul_le_mul_left h4 hC2_pos
  have hX : X ^ 2 ≤ ((s * t ^ 2 : ℕ) : ℤ) := by
    have h1 : (C * X) ^ 2 ≤ CX_abs * CX_abs := by
      rw [← sq_abs (C * X)]
      nlinarith [abs_nonneg (C * X)]
    have h2 : C * C * (s : ℤ) * tmin * tmin ≤ C ^ 2 * ((s * t ^ 2 : ℕ) : ℤ) := by
      push_cast; nlinarith [show 0 ≤ C ^ 2 * (s : ℤ) by positivity]
    have h3 : C ^ 2 * X ^ 2 ≤ C ^ 2 * ((s * t ^ 2 : ℕ) : ℤ) := by
      have hL : C ^ 2 * X ^ 2 = (C * X) ^ 2 := by ring
      linarith
    exact le_of_mul_le_mul_left h3 hC2_pos
  exact matrix_repr s t A B C a d hdet hA hC ha hd ht
    (by simpa [X, c] using hX) (by simpa [U, V, c, sq, mul_assoc] using hUV)

private def checkSingleAD (s : ℕ) (A B C a d : ℤ) (t : ℕ) : Bool :=
  let c : ℤ := a * d - (t : ℤ)
  let U := A * a ^ 2 + 2 * B * a * c + C * c ^ 2
  let V := A + 2 * B * d + C * d ^ 2
  let X := A * a + B * (a * d + c) + C * c * d
  let k : ℤ := ((s * t ^ 2 : ℕ) : ℤ)
  decide (X ^ 2 ≤ k) && decide ((|U| + |V|) ^ 2 ≤ 4 * k)

private lemma checkSingleAD_sound (s : ℕ) (A B C a d : ℤ)
    (hdet : A * C - B ^ 2 = -(s : ℤ))
    (hA : A % 2 ≠ 0) (hC : C % 2 ≠ 0)
    (ha : a % 2 = 0) (hd : d % 2 = 0)
    (t : ℕ) (ht : t % 2 = 1)
    (hok : checkSingleAD s A B C a d t = true) :
    IsRepresentable (s * t ^ 2) := by
  unfold checkSingleAD at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact matrix_repr s t A B C a d hdet hA hC ha hd ht hok.1 hok.2

private def evalMatrixOne (s u : ℕ) (A B C ln : ℤ) (t : ℕ) : Bool :=
  let disc := Int.toNat (ln * ln + 64 * (u : ℤ) * (t : ℤ))
  let m_init := max 1 (Int.toNat ((ln + (Nat.sqrt disc : ℤ)) / (8 * (u : ℤ))))
  let m :=
    if 4 * (u : ℤ) * (m_init : ℤ) ^ 2 - ln * (m_init : ℤ) ≥ 4 * (t : ℤ) then m_init
    else if 4 * (u : ℤ) * ((m_init + 1 : ℕ) : ℤ) ^ 2 - ln * ((m_init + 1 : ℕ) : ℤ) ≥ 4 * (t : ℤ) then m_init + 1
    else m_init + 2
  let r_sc := 4 * (u : ℤ) * (m : ℤ) ^ 2 - ln * (m : ℤ) - 4 * (t : ℤ)
  if r_sc < 0 then false else
  let i0 := Nat.sqrt (Int.toNat r_sc / (4 * u))
  let i :=
    if i0 % 2 = m % 2 then i0
    else if 1 ≤ i0 ∧ r_sc ≤ 4 * (u : ℤ) * ((i0 : ℤ) ^ 2 + 1) then i0 - 1
    else i0 + 1
  let a : ℤ := (u : ℤ) * ((m : ℤ) + (i : ℤ))
  let d : ℤ := (m : ℤ) - (i : ℤ)
  checkSingleAD s A B C a d t

private lemma evalMatrixOne_sound (s u : ℕ) (A B C ln : ℤ)
    (hdet : A * C - B ^ 2 = -(s : ℤ))
    (hA : A % 2 ≠ 0) (hC : C % 2 ≠ 0)
    (t : ℕ) (ht : t % 2 = 1)
    (hok : evalMatrixOne s u A B C ln t = true) :
    IsRepresentable (s * t ^ 2) := by
  unfold evalMatrixOne at hok
  dsimp only at hok
  set disc := Int.toNat (ln * ln + 64 * (u : ℤ) * (t : ℤ))
  set m_init := max 1 (Int.toNat ((ln + (Nat.sqrt disc : ℤ)) / (8 * (u : ℤ))))
  set m :=
    if 4 * (u : ℤ) * (m_init : ℤ) ^ 2 - ln * (m_init : ℤ) ≥ 4 * (t : ℤ) then m_init
    else if 4 * (u : ℤ) * ((m_init + 1 : ℕ) : ℤ) ^ 2 - ln * ((m_init + 1 : ℕ) : ℤ) ≥ 4 * (t : ℤ) then m_init + 1
    else m_init + 2
  set r_sc := 4 * (u : ℤ) * (m : ℤ) ^ 2 - ln * (m : ℤ) - 4 * (t : ℤ)
  by_cases hneg : r_sc < 0
  · simp [hneg] at hok
  simp only [hneg, ↓reduceIte] at hok
  set i0 := Nat.sqrt (Int.toNat r_sc / (4 * u))
  set i :=
    if i0 % 2 = m % 2 then i0
    else if 1 ≤ i0 ∧ r_sc ≤ 4 * (u : ℤ) * ((i0 : ℤ) ^ 2 + 1) then i0 - 1
    else i0 + 1
  have hpar : i % 2 = m % 2 := by dsimp [i]; split_ifs <;> omega
  have ha : ((u : ℤ) * ((m : ℤ) + (i : ℤ))) % 2 = 0 := by
    have hmi : ((m : ℤ) + (i : ℤ)) % 2 = 0 := by omega
    rw [Int.mul_emod, hmi]; simp
  have hd : ((m : ℤ) - (i : ℤ)) % 2 = 0 := by omega
  exact checkSingleAD_sound s A B C _ _ hdet hA hC ha hd t ht hok

private def checkOffset (k : ℕ) : Bool :=
  let r := Nat.sqrt k
  (List.range 32).any fun delta =>
    if r < delta then false else
    let a := r - delta
    let rem := k - a * a
    if rem % 2 = 1 then
      (List.range 32).any fun j =>
        let d := 2 * j + 1
        decide (rem % d = 0) && decide (rem / d + d ≤ 2 * r)
    else if rem % 4 = 0 then
      let q := rem / 4
      (List.range 31).any fun j =>
        let d := j + 1
        decide (q % d = 0) && decide (q / d + d ≤ r) && decide (d ≤ q / d)
    else false

private lemma checkOffset_sound (k : ℕ) (hok : checkOffset k = true) : IsRepresentable k := by
  unfold checkOffset at hok
  dsimp only at hok
  obtain ⟨delta, _, hdelta⟩ := List.any_eq_true.mp hok
  set r := Nat.sqrt k
  have hr2 : r * r ≤ k := Nat.sqrt_le k
  by_cases hlt : r < delta
  · simp [hlt] at hdelta
  simp only [hlt, ↓reduceIte] at hdelta
  set a := r - delta
  have ha_le : a ≤ r := Nat.sub_le _ _
  have ha2 : a * a ≤ k := (Nat.mul_self_le_mul_self ha_le).trans hr2
  set rem := k - a * a
  by_cases hodd : rem % 2 = 1
  · simp only [hodd, ↓reduceIte] at hdelta
    obtain ⟨j, _, hj⟩ := List.any_eq_true.mp hdelta
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    set d := 2 * j + 1
    set u := rem / d
    have hdu : d * u = rem := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hj.1)
    have hu_odd : u % 2 = 1 := by
      have h1 : (d * u) % 2 = 1 := by rw [hdu]; exact hodd
      have h2 : (d * u) % 2 = ((d % 2) * (u % 2)) % 2 := Nat.mul_mod d u 2
      have hd1 : d % 2 = 1 := by dsimp [d]; omega
      rw [h2, hd1, one_mul, Nat.mod_mod] at h1
      exact h1
    have hk_eq : k = a * a + u * d := by
      have : u * d = rem := by rw [mul_comm]; exact hdu
      omega
    let y : ℤ := ((u : ℤ) + (d : ℤ)) / 2
    let z : ℤ := ((u : ℤ) - (d : ℤ)) / 2
    have hy2 : 2 * y = (u : ℤ) + (d : ℤ) := by dsimp [y]; omega
    have hz2 : 2 * z = (u : ℤ) - (d : ℤ) := by dsimp [z]; omega
    have hr2Z : (r : ℤ) ^ 2 ≤ (k : ℤ) := by exact_mod_cast (by simpa [sq] using hr2)
    have hbd (w : ℤ) (h1 : -(r : ℤ) ≤ w) (h2 : w ≤ (r : ℤ)) : w ^ 2 ≤ (k : ℤ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ (r : ℤ) + w by omega)]
    have hud_le : (u : ℤ) + (d : ℤ) ≤ 2 * (r : ℤ) := by exact_mod_cast hj.2
    have hu_nn : (0 : ℤ) ≤ (u : ℤ) := Nat.cast_nonneg u
    have hd_nn : (0 : ℤ) ≤ (d : ℤ) := Nat.cast_nonneg d
    refine ⟨(a : ℤ), y, z, hbd _ (by omega) (by exact_mod_cast ha_le),
      hbd _ (by omega) (by omega), hbd _ (by omega) (by omega), ?_⟩
    have hkz : (k : ℤ) = (a : ℤ) ^ 2 + (u : ℤ) * (d : ℤ) := by
      have : (k : ℤ) = (a : ℤ) * (a : ℤ) + (u : ℤ) * (d : ℤ) := by exact_mod_cast hk_eq
      linarith [sq (a : ℤ)]
    have hyz : (u : ℤ) * (d : ℤ) = y ^ 2 - z ^ 2 := by
      have : (2 * y) ^ 2 - (2 * z) ^ 2 = 4 * ((u : ℤ) * (d : ℤ)) := by rw [hy2, hz2]; ring
      linarith
    linarith
  · simp only [hodd, ↓reduceIte] at hdelta
    by_cases hfour : rem % 4 = 0
    · simp only [hfour, ↓reduceIte] at hdelta
      obtain ⟨j, _, hj⟩ := List.any_eq_true.mp hdelta
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
      set d := j + 1
      set q := rem / 4
      set u := q / d
      have hq4 : 4 * q = rem := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hfour)
      have hdu : d * u = q := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hj.1.1)
      have hk_eq : k = a * a + 4 * (d * u) := by omega
      have hbd (w : ℕ) (hw : w ≤ r) : (w : ℤ) ^ 2 ≤ (k : ℤ) := by
        have : w * w ≤ k := (Nat.mul_self_le_mul_self hw).trans hr2
        exact_mod_cast (by simpa [sq] using this)
      refine ⟨(a : ℤ), ((u + d : ℕ) : ℤ), ((u - d : ℕ) : ℤ), hbd a ha_le,
        hbd (u + d) hj.1.2, hbd (u - d) (by omega), ?_⟩
      have hkz : (k : ℤ) = (a : ℤ) ^ 2 + 4 * ((d : ℤ) * (u : ℤ)) := by
        have : (k : ℤ) = (a : ℤ) * (a : ℤ) + 4 * ((d : ℤ) * (u : ℤ)) := by exact_mod_cast hk_eq
        linarith [sq (a : ℤ)]
      have hsub : ((u - d : ℕ) : ℤ) = (u : ℤ) - (d : ℤ) := by omega
      push_cast
      rw [hsub, hkz]
      ring
    · simp [hfour] at hdelta

private structure Entry where
  s : ℕ
  u1 : ℕ
  A1 : ℤ
  B1 : ℤ
  C1 : ℤ
  ln1 : ℤ
  m0 : ℤ
  pmax : ℤ
  u2 : ℕ
  A2 : ℤ
  B2 : ℤ
  C2 : ℤ
  ln2 : ℤ
  u3 : ℕ
  A3 : ℤ
  B3 : ℤ
  C3 : ℤ
  ln3 : ℤ

private def checkLeaf (e : Entry) (t : ℕ) : Bool :=
  evalMatrixOne e.s e.u1 e.A1 e.B1 e.C1 e.ln1 t ||
  evalMatrixOne e.s e.u2 e.A2 e.B2 e.C2 e.ln2 t ||
  evalMatrixOne e.s e.u3 e.A3 e.B3 e.C3 e.ln3 t ||
  checkOffset (e.s * t ^ 2)

private lemma checkLeaf_sound (e : Entry)
    (hdet1 : e.A1 * e.C1 - e.B1 ^ 2 = -(e.s : ℤ))
    (hA1 : e.A1 % 2 ≠ 0) (hC1 : e.C1 % 2 ≠ 0)
    (hdet2 : e.A2 * e.C2 - e.B2 ^ 2 = -(e.s : ℤ))
    (hA2 : e.A2 % 2 ≠ 0) (hC2 : e.C2 % 2 ≠ 0)
    (hdet3 : e.A3 * e.C3 - e.B3 ^ 2 = -(e.s : ℤ))
    (hA3 : e.A3 % 2 ≠ 0) (hC3 : e.C3 % 2 ≠ 0)
    (t : ℕ) (ht : t % 2 = 1) (hok : checkLeaf e t = true) :
    IsRepresentable (e.s * t ^ 2) := by
  unfold checkLeaf at hok
  simp only [Bool.or_eq_true] at hok
  rcases hok with ((h1 | h2) | h3) | h4
  · exact evalMatrixOne_sound e.s e.u1 e.A1 e.B1 e.C1 e.ln1 hdet1 hA1 hC1 t ht h1
  · exact evalMatrixOne_sound e.s e.u2 e.A2 e.B2 e.C2 e.ln2 hdet2 hA2 hC2 t ht h2
  · exact evalMatrixOne_sound e.s e.u3 e.A3 e.B3 e.C3 e.ln3 hdet3 hA3 hC3 t ht h3
  · exact checkOffset_sound (e.s * t ^ 2) h4

private def checkLeafRange (e : Entry) (t_lo t_hi : ℕ) : Bool :=
  (List.range (t_hi + 1 - t_lo)).all fun j =>
    let t := t_lo + j
    if t % 2 = 1 then checkLeaf e t else true

private lemma checkLeafRange_sound (e : Entry)
    (hdet1 : e.A1 * e.C1 - e.B1 ^ 2 = -(e.s : ℤ))
    (hA1 : e.A1 % 2 ≠ 0) (hC1 : e.C1 % 2 ≠ 0)
    (hdet2 : e.A2 * e.C2 - e.B2 ^ 2 = -(e.s : ℤ))
    (hA2 : e.A2 % 2 ≠ 0) (hC2 : e.C2 % 2 ≠ 0)
    (hdet3 : e.A3 * e.C3 - e.B3 ^ 2 = -(e.s : ℤ))
    (hA3 : e.A3 % 2 ≠ 0) (hC3 : e.C3 % 2 ≠ 0)
    (t_lo t_hi : ℕ) (hok : checkLeafRange e t_lo t_hi = true)
    (t : ℕ) (hlo : t_lo ≤ t) (hhi : t ≤ t_hi) (ht : t % 2 = 1) :
    IsRepresentable (e.s * t ^ 2) := by
  unfold checkLeafRange at hok
  have hm := List.all_eq_true.mp hok (t - t_lo) (List.mem_range.mpr (by omega))
  have hadd : t_lo + (t - t_lo) = t := by omega
  simp only [hadd, ht, ↓reduceIte] at hm
  exact checkLeaf_sound e hdet1 hA1 hC1 hdet2 hA2 hC2 hdet3 hA3 hC3 t ht hm

private def checkLeafRangeAD (e : Entry) (a d : ℤ) (t_lo t_hi : ℕ) : Bool :=
  (List.range (t_hi + 1 - t_lo)).all fun j =>
    let t := t_lo + j
    if t % 2 = 1 then
      checkSingleAD e.s e.A1 e.B1 e.C1 a d t ||
      evalMatrixOne e.s e.u2 e.A2 e.B2 e.C2 e.ln2 t ||
      evalMatrixOne e.s e.u3 e.A3 e.B3 e.C3 e.ln3 t ||
      checkOffset (e.s * t ^ 2)
    else true

private lemma checkLeafRangeAD_sound (e : Entry) (a d : ℤ)
    (hdet1 : e.A1 * e.C1 - e.B1 ^ 2 = -(e.s : ℤ))
    (hA1 : e.A1 % 2 ≠ 0) (hC1 : e.C1 % 2 ≠ 0)
    (hdet2 : e.A2 * e.C2 - e.B2 ^ 2 = -(e.s : ℤ))
    (hA2 : e.A2 % 2 ≠ 0) (hC2 : e.C2 % 2 ≠ 0)
    (hdet3 : e.A3 * e.C3 - e.B3 ^ 2 = -(e.s : ℤ))
    (hA3 : e.A3 % 2 ≠ 0) (hC3 : e.C3 % 2 ≠ 0)
    (ha : a % 2 = 0) (hd : d % 2 = 0)
    (t_lo t_hi : ℕ) (hok : checkLeafRangeAD e a d t_lo t_hi = true)
    (t : ℕ) (hlo : t_lo ≤ t) (hhi : t ≤ t_hi) (ht : t % 2 = 1) :
    IsRepresentable (e.s * t ^ 2) := by
  unfold checkLeafRangeAD at hok
  have hm := List.all_eq_true.mp hok (t - t_lo) (List.mem_range.mpr (by omega))
  have hadd : t_lo + (t - t_lo) = t := by omega
  simp only [hadd, ht, ↓reduceIte, Bool.or_eq_true] at hm
  rcases hm with ((h1 | h2) | h3) | h4
  · exact checkSingleAD_sound e.s e.A1 e.B1 e.C1 a d hdet1 hA1 hC1 ha hd t ht h1
  · exact evalMatrixOne_sound e.s e.u2 e.A2 e.B2 e.C2 e.ln2 hdet2 hA2 hC2 t ht h2
  · exact evalMatrixOne_sound e.s e.u3 e.A3 e.B3 e.C3 e.ln3 hdet3 hA3 hC3 t ht h3
  · exact checkOffset_sound (e.s * t ^ 2) h4

private def verifyTRange (e : Entry) (a d : ℤ) : ℕ → ℕ → ℕ → Bool
  | 0, t_lo, t_hi => checkLeafRangeAD e a d t_lo t_hi
  | fuel + 1, t_lo, t_hi =>
    if t_hi < t_lo then true
    else if checkTInterval e.s e.A1 e.B1 e.C1 a d t_lo t_hi then true
    else if t_hi - t_lo ≤ 4 then checkLeafRangeAD e a d t_lo t_hi
    else
      let mid := (t_lo + t_hi) / 2
      verifyTRange e a d fuel t_lo mid && verifyTRange e a d fuel (mid + 1) t_hi

private lemma verifyTRange_sound (e : Entry) (a d : ℤ)
    (hdet1 : e.A1 * e.C1 - e.B1 ^ 2 = -(e.s : ℤ))
    (hA1 : e.A1 % 2 ≠ 0) (hC1 : e.C1 % 2 ≠ 0) (hC1pos : 0 < e.C1)
    (hdet2 : e.A2 * e.C2 - e.B2 ^ 2 = -(e.s : ℤ))
    (hA2 : e.A2 % 2 ≠ 0) (hC2 : e.C2 % 2 ≠ 0)
    (hdet3 : e.A3 * e.C3 - e.B3 ^ 2 = -(e.s : ℤ))
    (hA3 : e.A3 % 2 ≠ 0) (hC3 : e.C3 % 2 ≠ 0)
    (ha : a % 2 = 0) (hd : d % 2 = 0) :
    ∀ (fuel t_lo t_hi : ℕ), verifyTRange e a d fuel t_lo t_hi = true →
    ∀ t : ℕ, t_lo ≤ t → t ≤ t_hi → t % 2 = 1 → IsRepresentable (e.s * t ^ 2)
  | 0, t_lo, t_hi, hok, t, hlo, hhi, ht =>
      checkLeafRangeAD_sound e a d hdet1 hA1 hC1 hdet2 hA2 hC2 hdet3 hA3 hC3 ha hd t_lo t_hi hok t hlo hhi ht
  | fuel + 1, t_lo, t_hi, hok, t, hlo, hhi, ht => by
      unfold verifyTRange at hok
      split_ifs at hok with h1 h2 h3
      · omega
      · exact checkTInterval_sound e.s e.A1 e.B1 e.C1 a d t_lo t_hi hdet1 hA1 hC1 hC1pos ha hd h2 t hlo hhi ht
      · exact checkLeafRangeAD_sound e a d hdet1 hA1 hC1 hdet2 hA2 hC2 hdet3 hA3 hC3 ha hd t_lo t_hi hok t hlo hhi ht
      · simp only [Bool.and_eq_true] at hok
        by_cases hmid : t ≤ (t_lo + t_hi) / 2
        · exact verifyTRange_sound e a d hdet1 hA1 hC1 hC1pos hdet2 hA2 hC2 hdet3 hA3 hC3 ha hd fuel t_lo _ hok.1 t hlo hmid ht
        · exact verifyTRange_sound e a d hdet1 hA1 hC1 hC1pos hdet2 hA2 hC2 hdet3 hA3 hC3 ha hd fuel _ t_hi hok.2 t (by omega) hhi ht

/-- Cover `[t_lo, cur]` by stepping `i` up by 2 (same parity as `m`), using `(a, d) = (u*(m+i), m-i)`. -/
private def coverM (e : Entry) (m : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, t_lo, cur =>
    if cur < t_lo then true else checkLeafRange e t_lo cur
  | steps + 1, i, t_lo, cur =>
    if cur < t_lo then true
    else
      let r_hi : ℤ := 4 * (e.u1 : ℤ) * ((i + 1 : ℕ) : ℤ) ^ 2
      let next_lo := max t_lo (Int.toNat ((4 * (e.u1 : ℤ) * (m : ℤ) ^ 2 - e.ln1 * (m : ℤ) - r_hi + 3) / 4))
      let a : ℤ := (e.u1 : ℤ) * ((m : ℤ) + (i : ℤ))
      let d : ℤ := (m : ℤ) - (i : ℤ)
      let ok_here :=
        if next_lo ≤ cur then verifyTRange e a d 16 next_lo cur else true
      let next_cur := next_lo - 1
      ok_here && (if next_lo = 0 then true else coverM e m steps (i + 2) t_lo next_cur)

private lemma coverM_sound (e : Entry) (m : ℕ)
    (hdet1 : e.A1 * e.C1 - e.B1 ^ 2 = -(e.s : ℤ))
    (hA1 : e.A1 % 2 ≠ 0) (hC1 : e.C1 % 2 ≠ 0) (hC1pos : 0 < e.C1)
    (hdet2 : e.A2 * e.C2 - e.B2 ^ 2 = -(e.s : ℤ))
    (hA2 : e.A2 % 2 ≠ 0) (hC2 : e.C2 % 2 ≠ 0)
    (hdet3 : e.A3 * e.C3 - e.B3 ^ 2 = -(e.s : ℤ))
    (hA3 : e.A3 % 2 ≠ 0) (hC3 : e.C3 % 2 ≠ 0) :
    ∀ (steps i t_lo cur : ℕ), i % 2 = m % 2 → coverM e m steps i t_lo cur = true →
    ∀ t : ℕ, t_lo ≤ t → t ≤ cur → t % 2 = 1 → IsRepresentable (e.s * t ^ 2)
  | 0, i, t_lo, cur, _, hok, t, hlo, hhi, ht => by
      unfold coverM at hok
      split_ifs at hok with hlt
      · omega
      · exact checkLeafRange_sound e hdet1 hA1 hC1 hdet2 hA2 hC2 hdet3 hA3 hC3 t_lo cur hok t hlo hhi ht
  | steps + 1, i, t_lo, cur, hpar, hok, t, hlo, hhi, ht => by
      unfold coverM at hok
      split_ifs at hok with hlt
      · omega
      · simp only [Bool.and_eq_true] at hok
        set r_hi : ℤ := 4 * (e.u1 : ℤ) * ((i + 1 : ℕ) : ℤ) ^ 2
        set next_lo := max t_lo (Int.toNat ((4 * (e.u1 : ℤ) * (m : ℤ) ^ 2 - e.ln1 * (m : ℤ) - r_hi + 3) / 4))
        by_cases hge : next_lo ≤ t
        · have hle : next_lo ≤ cur := le_trans hge hhi
          have h1 := hok.1
          simp only [hle, ↓reduceIte] at h1
          have ha : ((e.u1 : ℤ) * ((m : ℤ) + (i : ℤ))) % 2 = 0 := by
            have hmi : ((m : ℤ) + (i : ℤ)) % 2 = 0 := by omega
            rw [Int.mul_emod, hmi]; simp
          have hd : ((m : ℤ) - (i : ℤ)) % 2 = 0 := by omega
          exact verifyTRange_sound e _ _ hdet1 hA1 hC1 hC1pos hdet2 hA2 hC2 hdet3 hA3 hC3 ha hd 16 next_lo cur h1 t hge hhi ht
        · have hne : next_lo ≠ 0 := by omega
          have h2 := hok.2
          simp only [hne, ↓reduceIte] at h2
          exact coverM_sound e m hdet1 hA1 hC1 hC1pos hdet2 hA2 hC2 hdet3 hA3 hC3 steps (i + 2) t_lo (next_lo - 1)
            (by omega) h2 t hlo (by omega) ht

/-- Cover `[t_lo_global, cur]` by stepping `m` down from `m0 - 1` to `1`. -/
private def coverAllM (e : Entry) : ℕ → ℕ → ℕ → Bool
  | 0, t_lo, cur => if cur < t_lo then true else checkLeafRange e t_lo cur
  | m + 1, t_lo, cur =>
    if cur < t_lo then true
    else
      let m' := m + 1
      let next_lo := max t_lo (Int.toNat ((4 * (e.u1 : ℤ) * (m : ℤ) ^ 2 - e.ln1 * (m : ℤ)) / 4 + 1))
      let r_max := max 0 (4 * (e.u1 : ℤ) * (m' : ℤ) ^ 2 - e.ln1 * (m' : ℤ) - 4 * (next_lo : ℤ))
      let steps := Nat.sqrt (Int.toNat r_max / (4 * e.u1)) / 2 + 2
      let ok_m := if next_lo ≤ cur then coverM e m' steps (m' % 2) next_lo cur else true
      ok_m && (if next_lo = 0 then true else coverAllM e m t_lo (next_lo - 1))

private lemma coverAllM_sound (e : Entry)
    (hdet1 : e.A1 * e.C1 - e.B1 ^ 2 = -(e.s : ℤ))
    (hA1 : e.A1 % 2 ≠ 0) (hC1 : e.C1 % 2 ≠ 0) (hC1pos : 0 < e.C1)
    (hdet2 : e.A2 * e.C2 - e.B2 ^ 2 = -(e.s : ℤ))
    (hA2 : e.A2 % 2 ≠ 0) (hC2 : e.C2 % 2 ≠ 0)
    (hdet3 : e.A3 * e.C3 - e.B3 ^ 2 = -(e.s : ℤ))
    (hA3 : e.A3 % 2 ≠ 0) (hC3 : e.C3 % 2 ≠ 0) :
    ∀ (m t_lo cur : ℕ), coverAllM e m t_lo cur = true →
    ∀ t : ℕ, t_lo ≤ t → t ≤ cur → t % 2 = 1 → IsRepresentable (e.s * t ^ 2)
  | 0, t_lo, cur, hok, t, hlo, hhi, ht => by
      unfold coverAllM at hok
      split_ifs at hok with hlt
      · omega
      · exact checkLeafRange_sound e hdet1 hA1 hC1 hdet2 hA2 hC2 hdet3 hA3 hC3 t_lo cur hok t hlo hhi ht
  | m + 1, t_lo, cur, hok, t, hlo, hhi, ht => by
      unfold coverAllM at hok
      split_ifs at hok with hlt
      · omega
      · simp only [Bool.and_eq_true] at hok
        set m' := m + 1
        set next_lo := max t_lo (Int.toNat ((4 * (e.u1 : ℤ) * (m : ℤ) ^ 2 - e.ln1 * (m : ℤ)) / 4 + 1))
        by_cases hge : next_lo ≤ t
        · have hle : next_lo ≤ cur := le_trans hge hhi
          have h1 := hok.1
          simp only [hle, ↓reduceIte] at h1
          exact coverM_sound e m' hdet1 hA1 hC1 hC1pos hdet2 hA2 hC2 hdet3 hA3 hC3 _ (m' % 2) next_lo cur (by omega) h1 t hge hhi ht
        · have hne : next_lo ≠ 0 := by omega
          have h2 := hok.2
          simp only [hne, ↓reduceIte] at h2
          exact coverAllM_sound e hdet1 hA1 hC1 hC1pos hdet2 hA2 hC2 hdet3 hA3 hC3 m t_lo (next_lo - 1) h2 t hlo (by omega) ht

private def verifyEntry (e : Entry) : Bool :=
  let t_min := max 3 (Nat.sqrt (6563 / e.s) + 1)
  let t_max_fin := Int.toNat ((4 * (e.u1 : ℤ) * (e.m0 - 1) ^ 2 - e.ln1 * (e.m0 - 1)) / 4)
  checkTail e.s e.u1 e.A1 e.B1 e.C1 e.ln1 e.m0 e.pmax &&
  decide (e.A2 * e.C2 - e.B2 ^ 2 = -(e.s : ℤ)) &&
  decide (e.A2 % 2 ≠ 0) &&
  decide (e.C2 % 2 ≠ 0) &&
  decide (e.A3 * e.C3 - e.B3 ^ 2 = -(e.s : ℤ)) &&
  decide (e.A3 % 2 ≠ 0) &&
  decide (e.C3 % 2 ≠ 0) &&
  coverAllM e (Int.toNat (e.m0 - 1)) t_min t_max_fin

private lemma verifyEntry_sound (e : Entry) (hok : verifyEntry e = true)
    (t : ℕ) (ht1 : 1 < t) (h6563 : 6563 < e.s * t ^ 2) (ht : t % 2 = 1) :
    IsRepresentable (e.s * t ^ 2) := by
  unfold verifyEntry at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨⟨⟨htail, hdet2⟩, hA2⟩, hC2⟩, hdet3⟩, hA3⟩, hC3⟩, hfin⟩
  set t_min := max 3 (Nat.sqrt (6563 / e.s) + 1)
  set t_max_fin := Int.toNat ((4 * (e.u1 : ℤ) * (e.m0 - 1) ^ 2 - e.ln1 * (e.m0 - 1)) / 4)
  have ht_ge_min : t_min ≤ t := by
    dsimp [t_min]
    apply max_le (by omega)
    by_contra hlt
    push Not at hlt
    have h1 : t ≤ Nat.sqrt (6563 / e.s) := by omega
    have h2 : t * t ≤ 6563 / e.s := (Nat.mul_self_le_mul_self h1).trans (Nat.sqrt_le _)
    have h3 : e.s * (t * t) ≤ e.s * (6563 / e.s) := Nat.mul_le_mul_left _ h2
    have h4 : e.s * (6563 / e.s) ≤ 6563 := Nat.mul_div_le 6563 e.s
    have h5 : e.s * t ^ 2 ≤ 6563 := by rw [sq]; omega
    omega
  by_cases hle : t ≤ t_max_fin
  · have htail' := htail
    unfold checkTail at htail'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htail'
    rcases htail' with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hC1pos⟩, hdet1⟩, hA1⟩, hC1⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
    exact coverAllM_sound e hdet1 hA1 hC1 hC1pos hdet2 hA2 hC2 hdet3 hA3 hC3 _ t_min t_max_fin hfin t ht_ge_min hle ht
  · have hbig : 4 * (e.u1 : ℤ) * (e.m0 - 1) ^ 2 - e.ln1 * (e.m0 - 1) < 4 * (t : ℤ) := by
      have hgt : t_max_fin < t := by omega
      have : (4 * (e.u1 : ℤ) * (e.m0 - 1) ^ 2 - e.ln1 * (e.m0 - 1)) / 4 < (t : ℤ) := by
        dsimp [t_max_fin] at hgt; omega
      omega
    exact checkTail_sound e.s e.u1 e.A1 e.B1 e.C1 e.ln1 e.m0 e.pmax htail t ht hbig

/-! ### The 73-Entry Parameter Table & Chunked Kernel Verification -/

private def allEntries : List Entry := [
  ⟨3, 1, -3, 0, 1, -6, 97, 633, 1, -1, 0, 3, -2, 1, -1, 0, 3, 2⟩,
  ⟨6, 1, 1, 3, 3, -2, 138, 524, 1, 1, 3, 3, -7, 2, 15, 9, 5, -17⟩,
  ⟨11, 1, 5, 6, 5, -7, 269, 369, 1, 1, 4, 5, -5, 2, 5, 6, 5, -6⟩,
  ⟨15, 1, -5, 0, 3, -4, 96, 636, 1, -3, 0, 5, -2, 1, -3, 0, 5, 2⟩,
  ⟨22, 1, -7, 1, 3, 4, 84, 681, 1, -3, 1, 7, -3, 1, -7, 1, 3, -6⟩,
  ⟨35, 1, -7, 0, 5, 4, 101, 617, 1, -5, 0, 7, -3, 1, -5, 0, 7, 3⟩,
  ⟨38, 2, 17, 15, 11, -15, 245, 388, 2, -1, 5, 13, -6, 2, 31, 21, 13, -16⟩,
  ⟨42, 1, 1, 7, 7, -2, 98, 628, 1, 29, 19, 11, -9, 1, 3, 9, 13, -5⟩,
  ⟨55, 1, -11, 0, 5, -5, 88, 667, 1, -3, 4, 13, -3, 1, 3, 10, 15, -5⟩,
  ⟨59, 1, 1, 8, 5, -2, 88, 665, 1, -5, 2, 11, -3, 1, -11, 2, 5, 3⟩,
  ⟨66, 1, -13, 1, 5, 5, 97, 631, 1, -5, 1, 13, -2, 1, 5, 11, 11, -6⟩,
  ⟨78, 1, -11, 1, 7, -5, 110, 592, 1, -7, 1, 11, -3, 1, -11, 1, 7, 3⟩,
  ⟨83, 2, 1, 10, 17, -8, 241, 391, 2, -1, 8, 19, -6, 1, 29, 24, 17, -8⟩,
  ⟨87, 1, -29, 0, 3, -11, 211, 420, 1, 13, 16, 13, -7, 1, 1, 10, 13, -5⟩,
  ⟨95, 1, -13, 2, 7, -6, 86, 675, 1, -7, 2, 13, -3, 1, 7, 16, 23, -5⟩,
  ⟨110, 1, 1, 11, 11, -2, 107, 599, 1, -5, 5, 17, -3, 1, -5, 5, 17, 1⟩,
  ⟨118, 1, -9, 1, 13, 2, 88, 665, 1, -9, 1, 13, -3, 1, -13, 1, 9, 3⟩,
  ⟨123, 1, -17, 2, 7, 4, 102, 614, 1, 3, 12, 7, -2, 1, -1, 10, 23, -4⟩,
  ⟨131, 1, -23, 4, 5, 5, 96, 634, 1, 5, 14, 13, -2, 1, -19, 6, 5, 2⟩,
  ⟨143, 1, -13, 0, 11, -3, 103, 612, 1, -13, 0, 11, 3, 1, -11, 0, 13, -3⟩,
  ⟨187, 1, -17, 0, 11, -4, 84, 683, 1, -11, 0, 17, -3, 1, -19, 4, 9, -6⟩,
  ⟨210, 1, -19, 1, 11, 4, 84, 681, 1, -7, 7, 23, -3, 1, -23, 7, 7, 2⟩,
  ⟨222, 1, -17, 1, 13, -4, 80, 701, 1, -13, 1, 17, -3, 1, -13, 1, 17, 2⟩,
  ⟨227, 2, 1, 16, 29, -2, 228, 402, 3, 73, 64, 53, -17, 3, 29, 42, 53, -12⟩,
  ⟨255, 1, -17, 0, 15, -3, 96, 636, 1, 3, 18, 23, -5, 1, -5, 10, 31, -3⟩,
  ⟨262, 1, -29, 1, 9, -7, 88, 668, 1, -11, 3, 23, -3, 1, 41, 37, 27, -8⟩,
  ⟨266, 1, 5, 19, 19, -7, 98, 630, 1, 1, 17, 23, -5, 1, -5, 11, 29, -4⟩,
  ⟨278, 1, -23, 5, 11, 3, 97, 631, 1, -11, 5, 23, -3, 1, 1, 17, 11, -2⟩,
  ⟨299, 1, -13, 0, 23, -2, 97, 632, 1, -23, 0, 13, -4, 1, 29, 32, 25, -7⟩,
  ⟨303, 1, 21, 24, 13, -4, 90, 658, 1, 1, 18, 21, -6, 1, 13, 28, 37, -5⟩,
  ⟨323, 1, -29, 2, 11, 5, 85, 677, 1, -11, 2, 29, -2, 1, -19, 0, 17, 3⟩,
  ⟨326, 1, -25, 1, 13, -5, 85, 679, 1, 13, 25, 23, -7, 1, 29, 35, 31, -7⟩,
  ⟨395, 1, -17, 2, 23, 2, 91, 653, 1, -17, 2, 23, -3, 1, 67, 44, 23, -5⟩,
  ⟨402, 1, 3, 21, 13, -2, 90, 657, 1, -13, 5, 29, -3, 1, -29, 5, 13, 3⟩,
  ⟨447, 2, 1, 22, 37, -2, 234, 397, 1, 61, 52, 37, -8, 1, -3, 18, 41, 0⟩,
  ⟨483, 1, -23, 0, 21, -3, 91, 654, 1, 3, 24, 31, -5, 2, 67, 58, 43, -14⟩,
  ⟨502, 1, 27, 31, 17, -4, 89, 662, 1, 1, 23, 27, -6, 1, 17, 37, 51, -5⟩,
  ⟨551, 1, -29, 0, 19, -4, 82, 692, 1, -11, 10, 41, -3, 1, -37, 12, 11, 2⟩,
  ⟨563, 1, -43, 2, 13, 6, 86, 673, 1, 1, 24, 13, -2, 1, -17, 6, 31, -3⟩,
  ⟨590, 1, -31, 1, 19, 4, 84, 681, 1, -19, 1, 31, -3, 1, 1, 25, 35, -5⟩,
  ⟨618, 1, -21, 3, 29, 2, 88, 665, 1, -21, 3, 29, -3, 1, 83, 55, 29, -5⟩,
  ⟨635, 2, 1, 26, 41, -2, 236, 395, 1, 61, 56, 41, -8, 1, 1, 26, 41, -5⟩,
  ⟨678, 1, 3, 27, 17, -2, 90, 657, 1, -17, 7, 37, -3, 1, -37, 7, 17, 3⟩,
  ⟨755, 1, -43, 14, 13, 3, 91, 653, 1, 1, 28, 29, -7, 1, -13, 14, 43, -4⟩,
  ⟨838, 1, -31, 1, 27, 3, 93, 645, 1, -27, 1, 31, -3, 2, 31, 61, 93, -7⟩,
  ⟨843, 1, 3, 30, 19, -2, 92, 650, 1, -19, 8, 41, -3, 2, 59, 90, 123, -8⟩,
  ⟨902, 1, -53, 1, 17, 6, 95, 638, 1, -17, 1, 53, -2, 1, -47, 3, 19, 4⟩,
  ⟨930, 1, -47, 15, 15, 3, 90, 657, 1, 3, 33, 53, -5, 1, -15, 15, 47, -4⟩,
  ⟨942, 1, -47, 7, 19, 4, 88, 665, 1, -21, 9, 41, -3, 1, 1, 31, 19, -2⟩,
  ⟨1003, 1, -37, 2, 27, -4, 85, 679, 1, -21, 4, 47, -3, 1, -43, 10, 21, 2⟩,
  ⟨1007, 1, -53, 0, 19, 6, 86, 673, 1, -19, 0, 53, -2, 1, -53, 0, 19, -5⟩,
  ⟨1034, 1, -41, 3, 25, -5, 108, 597, 1, -25, 3, 41, -3, 1, 1, 33, 55, -5⟩,
  ⟨1091, 1, -43, 4, 25, -5, 89, 663, 1, 25, 46, 41, -7, 1, 101, 92, 73, -7⟩,
  ⟨1162, 1, -43, 1, 27, 4, 84, 681, 1, -27, 1, 43, -3, 1, -53, 7, 21, -6⟩,
  ⟨1190, 1, -41, 1, 29, -4, 80, 701, 1, -29, 1, 41, -3, 1, 1, 35, 35, -7⟩,
  ⟨1295, 1, -37, 0, 35, -3, 87, 670, 1, 89, 82, 61, -8, 1, -35, 0, 37, 3⟩,
  ⟨1326, 1, 43, 49, 25, -4, 91, 654, 1, -25, 1, 53, -2, 1, 5, 39, 39, -7⟩,
  ⟨1482, 1, -59, 19, 19, 3, 90, 657, 1, -31, 5, 47, -3, 2, 47, 89, 137, -7⟩,
  ⟨1523, 1, -49, 2, 31, 4, 93, 645, 1, -31, 2, 49, -3, 1, 7, 44, 59, -5⟩,
  ⟨1770, 1, -61, 1, 29, -5, 89, 663, 1, -17, 23, 73, -3, 1, 1, 43, 79, -4⟩,
  ⟨1790, 1, 5, 45, 47, -7, 98, 630, 1, 1, 43, 59, -5, 1, -13, 29, 73, -4⟩,
  ⟨2067, 1, 1, 46, 49, -7, 93, 648, 1, -39, 0, 53, -3, 1, 127, 110, 79, -8⟩,
  ⟨2103, 1, -39, 6, 53, -3, 86, 674, 1, 3, 48, 67, -5, 2, 53, 100, 149, -8⟩,
  ⟨2407, 1, -71, 8, 33, 4, 88, 665, 1, -31, 12, 73, -3, 1, 3, 50, 31, -2⟩,
  ⟨2483, 1, -41, 8, 59, -3, 85, 678, 1, -59, 8, 41, 3, 2, 59, 110, 163, -8⟩,
  ⟨2598, 1, -49, 1, 53, -3, 86, 674, 1, 31, 67, 61, -7, 1, 151, 129, 93, -8⟩,
  ⟨2782, 1, -73, 9, 37, -6, 84, 684, 1, 107, 107, 81, -8, 1, -47, 3, 59, -3⟩,
  ⟨3422, 1, -79, 5, 43, 4, 88, 665, 1, -29, 29, 89, -4, 1, -89, 29, 29, 2⟩,
  ⟨3495, 1, -73, 8, 47, -5, 87, 671, 1, -47, 8, 73, -3, 2, -35, 10, 97, -4⟩,
  ⟨4686, 1, -83, 11, 55, -5, 81, 697, 1, -31, 37, 107, -4, 1, -107, 37, 31, 2⟩,
  ⟨5447, 1, -89, 14, 59, 3, 85, 677, 1, -59, 14, 89, -3, 2, 89, 164, 241, -8⟩,
  ⟨5727, 1, -101, 24, 51, 3, 84, 681, 1, -51, 24, 101, -3, 1, 167, 160, 119, -8⟩,
  ⟨6563, 1, -119, 16, 53, 4, 83, 686, 1, -53, 16, 119, -3, 2, -49, 12, 131, -4⟩
]

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_0 :
    ((allEntries.drop 0).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_1 :
    ((allEntries.drop 5).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_2 :
    ((allEntries.drop 10).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_3 :
    ((allEntries.drop 15).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_4 :
    ((allEntries.drop 20).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_5 :
    ((allEntries.drop 25).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_6 :
    ((allEntries.drop 30).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_7 :
    ((allEntries.drop 35).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_8 :
    ((allEntries.drop 40).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_9 :
    ((allEntries.drop 45).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_10 :
    ((allEntries.drop 50).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_11 :
    ((allEntries.drop 55).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_12 :
    ((allEntries.drop 60).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_13 :
    ((allEntries.drop 65).take 5).all verifyEntry = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem verify_chunk_14 :
    ((allEntries.drop 70).take 3).all verifyEntry = true := by
  decide +kernel

private theorem verify_all_entries : allEntries.all verifyEntry = true := by
  rw [List.all_eq_true]
  intro e he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  have hchk (lo len : ℕ) (h : ((allEntries.drop lo).take len).all verifyEntry = true)
      (h1 : lo ≤ k) (h2 : k < lo + len) : verifyEntry allEntries[k] = true := by
    have hmem : allEntries[k] ∈ (allEntries.drop lo).take len := by
      rw [List.mem_iff_getElem]
      refine ⟨k - lo, by simp; omega, ?_⟩
      simp [Nat.add_sub_of_le h1]
    exact List.all_eq_true.mp h _ hmem
  by_cases hc0 : k < 5
  · exact hchk 0 5 verify_chunk_0 (by omega) hc0
  by_cases hc1 : k < 10
  · exact hchk 5 5 verify_chunk_1 (by omega) hc1
  by_cases hc2 : k < 15
  · exact hchk 10 5 verify_chunk_2 (by omega) hc2
  by_cases hc3 : k < 20
  · exact hchk 15 5 verify_chunk_3 (by omega) hc3
  by_cases hc4 : k < 25
  · exact hchk 20 5 verify_chunk_4 (by omega) hc4
  by_cases hc5 : k < 30
  · exact hchk 25 5 verify_chunk_5 (by omega) hc5
  by_cases hc6 : k < 35
  · exact hchk 30 5 verify_chunk_6 (by omega) hc6
  by_cases hc7 : k < 40
  · exact hchk 35 5 verify_chunk_7 (by omega) hc7
  by_cases hc8 : k < 45
  · exact hchk 40 5 verify_chunk_8 (by omega) hc8
  by_cases hc9 : k < 50
  · exact hchk 45 5 verify_chunk_9 (by omega) hc9
  by_cases hc10 : k < 55
  · exact hchk 50 5 verify_chunk_10 (by omega) hc10
  by_cases hc11 : k < 60
  · exact hchk 55 5 verify_chunk_11 (by omega) hc11
  by_cases hc12 : k < 65
  · exact hchk 60 5 verify_chunk_12 (by omega) hc12
  by_cases hc13 : k < 70
  · exact hchk 65 5 verify_chunk_13 (by omega) hc13
  exact hchk 70 3 verify_chunk_14 (by omega) (by simp [allEntries] at hk; omega)

private theorem s_list_eq :
    allEntries.map Entry.s =
    ([3, 6, 11, 15, 22, 35, 38, 42, 55, 59, 66, 78, 83, 87, 95, 110, 118, 123, 131, 143, 187, 210,
      222, 227, 255, 262, 266, 278, 299, 303, 323, 326, 395, 402, 447, 483, 502, 551, 563, 590, 618,
      635, 678, 755, 838, 843, 902, 930, 942, 1003, 1007, 1034, 1091, 1162, 1190, 1295, 1326, 1482,
      1523, 1770, 1790, 2067, 2103, 2407, 2483, 2598, 2782, 3422, 3495, 4686, 5447, 5727, 6563] : List ℕ) := by
  decide

end OMA.P_oeis_a393168_R1_H2

theorem OMA.solution : OMA.R_oeis_a393168_R1.H2 := by
  intro s t hs ht1 h6563 hcond
  rw [← OMA.P_oeis_a393168_R1_H2.s_list_eq, List.mem_map] at hs
  obtain ⟨e, he_mem, rfl⟩ := hs
  have hok := List.all_eq_true.mp OMA.P_oeis_a393168_R1_H2.verify_all_entries e he_mem
  have ht_odd : t % 2 = 1 := OMA.P_oeis_a393168_R1_H2.odd_of_mod_four_ge_two hcond.1
  exact OMA.P_oeis_a393168_R1_H2.verifyEntry_sound e hok t ht1 h6563 ht_odd
