import OMAStatements.S_mo_392283
import Mathlib

-- Problem: Collisions of nonhomogeneous cubics on the integer lattice (mo-392283)
-- Credit: @kintonc

namespace ProofMO392283

/-! ## Elementary Polynomial Sign and Non-Square Lemmas -/

lemma exists_pos_of_poly4 (a4 a3 a2 a1 a0 : ℤ) (ha4 : 0 < a4) :
    ∃ N : ℤ, 0 < N ∧ ∀ n : ℤ, N ≤ n → 0 < a4 * n ^ 4 + a3 * n ^ 3 + a2 * n ^ 2 + a1 * n + a0 := by
  refine ⟨|a3| + |a2| + |a1| + |a0| + 1, by positivity, fun n hn => ?_⟩
  have h1 : 1 ≤ n := by linarith [abs_nonneg a3, abs_nonneg a2, abs_nonneg a1, abs_nonneg a0]
  have hn_pos : 0 < n := by omega
  have h3 : -(|a3| * n ^ 3) ≤ a3 * n ^ 3 := by
    have := neg_abs_le a3
    nlinarith [pow_pos hn_pos 3]
  have h2 : -(|a2| * n ^ 2) ≤ a2 * n ^ 2 := by
    have := neg_abs_le a2
    nlinarith [pow_pos hn_pos 2]
  have h1' : -(|a1| * n) ≤ a1 * n := by
    have := neg_abs_le a1
    nlinarith
  have h0 : -|a0| ≤ a0 := neg_abs_le a0
  have hN : |a3| * n ^ 3 + |a2| * n ^ 2 + |a1| * n + |a0| < n ^ 4 := by
    have h2a : |a2| * n ^ 2 ≤ |a2| * n ^ 3 := by
      have : n ^ 2 ≤ n ^ 3 := by nlinarith [sq_nonneg n]
      exact mul_le_mul_of_nonneg_left this (abs_nonneg a2)
    have h1a : |a1| * n ≤ |a1| * n ^ 3 := by
      have : n ≤ n ^ 3 := by nlinarith [sq_nonneg n]
      exact mul_le_mul_of_nonneg_left this (abs_nonneg a1)
    have h0a : |a0| ≤ |a0| * n ^ 3 := by
      have : 1 ≤ n ^ 3 := by nlinarith [sq_nonneg n]
      calc |a0| = |a0| * 1 := (mul_one _).symm
      _ ≤ |a0| * n ^ 3 := mul_le_mul_of_nonneg_left this (abs_nonneg a0)
    have hsum : (|a3| + |a2| + |a1| + |a0| + 1) * n ^ 3 ≤ n * n ^ 3 :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    linarith [pow_pos hn_pos 3]
  nlinarith [pow_pos hn_pos 4]

lemma exists_pos_of_poly2 (a2 a1 a0 : ℤ) (ha2 : 0 < a2) :
    ∃ N : ℤ, 0 < N ∧ ∀ n : ℤ, N ≤ n → 0 < a2 * n ^ 2 + a1 * n + a0 := by
  refine ⟨|a1| + |a0| + 1, by positivity, fun n hn => ?_⟩
  have h1 : 1 ≤ n := by linarith [abs_nonneg a1, abs_nonneg a0]
  have h1' : -(|a1| * n) ≤ a1 * n := by
    have := neg_abs_le a1
    nlinarith
  have h0 : -|a0| ≤ a0 := neg_abs_le a0
  have hN : |a1| * n + |a0| < n ^ 2 := by nlinarith [abs_nonneg a0, abs_nonneg a1]
  nlinarith [sq_nonneg n]

lemma exists_non_square_quadratic (A B C : ℤ) (hA : 0 < A) (hDelta : B ^ 2 - 4 * A * C ≠ 0)
    (M : ℤ) :
    ∃ m : ℤ, M ≤ m ∧ 0 < A * m ^ 2 + B * m + C ∧ ¬ IsSquare (A * m ^ 2 + B * m + C).toNat := by
  obtain ⟨M1, _, hpos⟩ := exists_pos_of_poly2 A B C hA
  by_contra hAll
  push Not at hAll
  have hsq : ∀ m : ℤ, max M M1 ≤ m → ∃ s : ℤ, 0 ≤ s ∧ s ^ 2 = A * m ^ 2 + B * m + C := by
    intro m hm
    have hm1 : M1 ≤ m := le_trans (le_max_right _ _) hm
    have hDpos : 0 < A * m ^ 2 + B * m + C := hpos m hm1
    have hIsSq := hAll m (le_trans (le_max_left _ _) hm) hDpos
    rcases hIsSq with ⟨k, hk⟩
    refine ⟨(k : ℤ), Int.natCast_nonneg k, ?_⟩
    have hcast : ((A * m ^ 2 + B * m + C).toNat : ℤ) = A * m ^ 2 + B * m + C :=
      Int.toNat_of_nonneg (le_of_lt hDpos)
    calc
      ((k : ℤ) ^ 2) = ((k * k : ℕ) : ℤ) := by push_cast; ring
      _ = ((A * m ^ 2 + B * m + C).toNat : ℤ) := by rw [← hk]
      _ = A * m ^ 2 + B * m + C := hcast
  by_cases hAsq : ∃ k : ℤ, A = k ^ 2
  · rcases hAsq with ⟨k, rfl⟩
    have hk_nz : k ≠ 0 := by intro h0; subst h0; simp at hA
    let m := max (max M M1) (|B ^ 2 - 4 * k ^ 2 * C| + |B| + 1)
    obtain ⟨s, hs0, hs⟩ := hsq m (le_max_left _ _)
    have hm_big : |B ^ 2 - 4 * k ^ 2 * C| + |B| + 1 ≤ m := le_max_right _ _
    have hm_pos : 0 < m := by
      linarith [abs_nonneg (B ^ 2 - 4 * k ^ 2 * C), abs_nonneg B]
    have hk2 : 1 ≤ k ^ 2 := by nlinarith [Int.one_le_abs hk_nz, sq_abs k]
    have hX_pos : 0 < 2 * k ^ 2 * m + B := by
      have hm_le : m ≤ k ^ 2 * m := by nlinarith
      linarith [neg_abs_le B, abs_nonneg (B ^ 2 - 4 * k ^ 2 * C)]
    have hid : (2 * k ^ 2 * m + B) ^ 2 - (2 * k * s) ^ 2 = B ^ 2 - 4 * k ^ 2 * C := by
      calc
        (2 * k ^ 2 * m + B) ^ 2 - (2 * k * s) ^ 2
            = (2 * k ^ 2 * m + B) ^ 2 - 4 * k ^ 2 * s ^ 2 := by ring
        _ = (2 * k ^ 2 * m + B) ^ 2 - 4 * k ^ 2 * (k ^ 2 * m ^ 2 + B * m + C) := by rw [hs]
        _ = B ^ 2 - 4 * k ^ 2 * C := by ring
    let X := 2 * k ^ 2 * m + B
    let Y := |2 * k * s|
    have hXY : X ^ 2 - Y ^ 2 = B ^ 2 - 4 * k ^ 2 * C := by
      have hY2 : Y ^ 2 = (2 * k * s) ^ 2 := sq_abs _
      linarith
    have hne : X ≠ Y := by
      intro heq
      rw [heq, sub_self] at hXY
      exact hDelta hXY.symm
    have hdiff_ge : 1 ≤ |X - Y| := Int.one_le_abs (sub_ne_zero.mpr hne)
    have hsum_ge : X ≤ X + Y := le_add_of_nonneg_right (abs_nonneg _)
    have hprod : (X + Y) * |X - Y| = |X ^ 2 - Y ^ 2| := by
      have hpos_sum : 0 ≤ X + Y := le_of_lt (lt_of_lt_of_le hX_pos hsum_ge)
      calc
        (X + Y) * |X - Y| = |X + Y| * |X - Y| := by rw [abs_of_nonneg hpos_sum]
        _ = |(X + Y) * (X - Y)| := (abs_mul _ _).symm
        _ = |X ^ 2 - Y ^ 2| := by ring_nf
    have hge : X ≤ |B ^ 2 - 4 * k ^ 2 * C| := by
      have h1 : X ≤ (X + Y) * |X - Y| := by nlinarith
      rw [hprod, hXY] at h1
      exact h1
    have hm_le : m ≤ k ^ 2 * m := by nlinarith
    linarith [neg_abs_le B]
  · have hA2 : 2 ≤ A := by
      by_contra hlt
      have hA1 : A = 1 := by omega
      exact hAsq ⟨1, by omega⟩
    let K1 : ℤ := 4 * A * |A + B| + 4 * A ^ 3 + 4 * |B| * A ^ 2 + 4 * |C| * A ^ 2
    let K2 : ℤ := (|A + B| + A ^ 2) ^ 2 + 4 * |C| * A ^ 2
    obtain ⟨M2, _, hM2⟩ := exists_pos_of_poly2 (A - 1) B C (by omega)
    let m := max (max M M1) (max M2 (|A + B| + K1 + K2 + 10))
    have hm1 : max M M1 ≤ m := le_max_left _ _
    have hm_big : |A + B| + K1 + K2 + 10 ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
    have hm_M2 : M2 ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
    have hK1_nn : 0 ≤ K1 := by positivity
    have hK2_nn : 0 ≤ K2 := by positivity
    have hm_pos : 0 < m := by linarith [abs_nonneg (A + B)]
    obtain ⟨s0, hs0_nn, hs0⟩ := hsq m hm1
    obtain ⟨s1, hs1_nn, hs1⟩ := hsq (m + 1) (by omega)
    let d := s1 - s0
    have hs_diff : s1 ^ 2 - s0 ^ 2 = 2 * A * m + A + B := by
      rw [hs1, hs0]; ring
    have hs_diff_pos : 0 < s1 ^ 2 - s0 ^ 2 := by
      rw [hs_diff]
      have : -|A + B| ≤ A + B := neg_abs_le _
      nlinarith
    have hd_pos : 1 ≤ d := by
      have hmul : 0 < (s1 - s0) * (s1 + s0) := by nlinarith
      have hlt : 0 < s1 - s0 := by
        by_contra hle
        have hle' : s1 - s0 ≤ 0 := by omega
        nlinarith
      omega
    have hm_le_s0 : m ≤ s0 := by
      have hpos' : 0 < (A - 1) * m ^ 2 + B * m + C := hM2 m hm_M2
      have hsq_le : m ^ 2 ≤ s0 ^ 2 := by linarith
      nlinarith
    have hm_le_s1 : m ≤ s1 := by
      have : s0 < s1 := by omega
      omega
    have hd_le_A : d ≤ A := by
      have hprod : d * (s1 + s0) = 2 * A * m + A + B := by
        dsimp [d]; linarith [hs_diff]
      have h2m : 2 * m ≤ s1 + s0 := by omega
      have hAB : A + B ≤ |A + B| := le_abs_self _
      have hlt : 2 * A * m + A + B < (2 * A + 2) * m := by
        nlinarith [abs_nonneg (A + B)]
      have hmul : d * (2 * m) < (2 * A + 2) * m := by
        calc
          d * (2 * m) ≤ d * (s1 + s0) := by nlinarith
          _ = 2 * A * m + A + B := hprod
          _ < (2 * A + 2) * m := hlt
      have : d < A + 1 := by nlinarith
      omega
    have h2ds : 2 * d * s0 = 2 * A * m + A + B - d ^ 2 := by
      have : s1 = s0 + d := by dsimp [d]; ring
      rw [this] at hs_diff
      linarith
    have hsq_eq : 4 * d ^ 2 * (A * m ^ 2 + B * m + C) = (2 * A * m + A + B - d ^ 2) ^ 2 := by
      calc
        4 * d ^ 2 * (A * m ^ 2 + B * m + C) = (2 * d * s0) ^ 2 := by rw [← hs0]; ring
        _ = (2 * A * m + A + B - d ^ 2) ^ 2 := by rw [h2ds]
    have hpoly : 4 * A * (d ^ 2 - A) * m ^ 2 =
        4 * A * (A + B - d ^ 2) * m - 4 * d ^ 2 * B * m + (A + B - d ^ 2) ^ 2 - 4 * d ^ 2 * C := by
      have hid : 4 * A * (d ^ 2 - A) * m ^ 2 -
          (4 * A * (A + B - d ^ 2) * m - 4 * d ^ 2 * B * m + (A + B - d ^ 2) ^ 2 - 4 * d ^ 2 * C) =
          4 * d ^ 2 * (A * m ^ 2 + B * m + C) - (2 * A * m + A + B - d ^ 2) ^ 2 := by
        ring
      rw [hsq_eq, sub_self] at hid
      linarith
    have hd2_ne : d ^ 2 - A ≠ 0 := by
      intro h0
      exact hAsq ⟨d, by linarith⟩
    have hlhs : 4 * A * m ^ 2 ≤ |4 * A * (d ^ 2 - A) * m ^ 2| := by
      have h1 : 1 ≤ |d ^ 2 - A| := Int.one_le_abs hd2_ne
      rw [abs_mul, abs_mul, abs_of_pos (by omega : 0 < 4 * A), abs_of_nonneg (sq_nonneg m)]
      calc
        4 * A * m ^ 2 = (4 * A * m ^ 2) * 1 := (mul_one _).symm
        _ ≤ (4 * A * m ^ 2) * |d ^ 2 - A| := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 4 * A * |d ^ 2 - A| * m ^ 2 := by ring
    have hd2_le : d ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by linarith only [hd_pos]) hd_le_A 2
    have hABd : |A + B - d ^ 2| ≤ |A + B| + A ^ 2 := by
      have t := abs_sub (A + B) (d ^ 2)
      rw [abs_of_nonneg (sq_nonneg d)] at t
      linarith only [t, hd2_le]
    have hrhs : |4 * A * (A + B - d ^ 2) * m - 4 * d ^ 2 * B * m + (A + B - d ^ 2) ^ 2 - 4 * d ^ 2 * C|
        ≤ K1 * m + K2 := by
      have h4A_pos : 0 < 4 * A := by linarith only [hA2]
      have h1 : |4 * A * (A + B - d ^ 2) * m| ≤ 4 * A * |A + B| * m + 4 * A ^ 3 * m := by
        rw [abs_mul, abs_mul, abs_of_pos h4A_pos, abs_of_pos hm_pos]
        calc 4 * A * |A + B - d ^ 2| * m
            ≤ 4 * A * (|A + B| + A ^ 2) * m :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hABd (le_of_lt h4A_pos)) (le_of_lt hm_pos)
          _ = 4 * A * |A + B| * m + 4 * A ^ 3 * m := by ring
      have h2 : |4 * d ^ 2 * B * m| ≤ 4 * |B| * A ^ 2 * m := by
        rw [abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) (sq_nonneg d)), abs_of_pos hm_pos]
        calc 4 * d ^ 2 * |B| * m
            ≤ 4 * A ^ 2 * |B| * m :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hd2_le]) (abs_nonneg B)) (le_of_lt hm_pos)
          _ = 4 * |B| * A ^ 2 * m := by ring
      have h3 : |(A + B - d ^ 2) ^ 2| ≤ (|A + B| + A ^ 2) ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hABd 2
      have h4 : |4 * d ^ 2 * C| ≤ 4 * |C| * A ^ 2 := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) (sq_nonneg d))]
        calc 4 * d ^ 2 * |C| ≤ 4 * A ^ 2 * |C| := mul_le_mul_of_nonneg_right (by linarith only [hd2_le]) (abs_nonneg C)
          _ = 4 * |C| * A ^ 2 := by ring
      have htri1 : |4 * A * (A + B - d ^ 2) * m - 4 * d ^ 2 * B * m + (A + B - d ^ 2) ^ 2 - 4 * d ^ 2 * C|
          ≤ |4 * A * (A + B - d ^ 2) * m| + |4 * d ^ 2 * B * m| + |(A + B - d ^ 2) ^ 2| + |4 * d ^ 2 * C| := by
        have t1 := abs_sub (4 * A * (A + B - d ^ 2) * m - 4 * d ^ 2 * B * m + (A + B - d ^ 2) ^ 2) (4 * d ^ 2 * C)
        have t2 := abs_add_le (4 * A * (A + B - d ^ 2) * m - 4 * d ^ 2 * B * m) ((A + B - d ^ 2) ^ 2)
        have t3 := abs_sub (4 * A * (A + B - d ^ 2) * m) (4 * d ^ 2 * B * m)
        linarith only [t1, t2, t3]
      have hC_m : 0 ≤ 4 * |C| * A ^ 2 * m :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg C)) (sq_nonneg A)) (le_of_lt hm_pos)
      have hK_eq : (4 * A * |A + B| * m + 4 * A ^ 3 * m) + 4 * |B| * A ^ 2 * m + (|A + B| + A ^ 2) ^ 2 +
          4 * |C| * A ^ 2 + 4 * |C| * A ^ 2 * m = K1 * m + K2 := by
        dsimp [K1, K2]; ring
      linarith only [h1, h2, h3, h4, htri1, hC_m, hK_eq]
    have hcontra : 4 * A * m ^ 2 ≤ K1 * m + K2 := by
      calc
        4 * A * m ^ 2 ≤ |4 * A * (d ^ 2 - A) * m ^ 2| := hlhs
        _ = |4 * A * (A + B - d ^ 2) * m - 4 * d ^ 2 * B * m + (A + B - d ^ 2) ^ 2 - 4 * d ^ 2 * C| := by rw [hpoly]
        _ ≤ K1 * m + K2 := hrhs
    have h1 : K1 * m + K2 ≤ (K1 + K2) * m := by
      have : K2 ≤ K2 * m := le_mul_of_one_le_right hK2_nn (by linarith only [hm_pos])
      linarith only [this]
    have h2 : (K1 + K2) * m < m * m :=
      mul_lt_mul_of_pos_right (by linarith only [hm_big, abs_nonneg (A + B)]) hm_pos
    have h3 : m * m < 4 * A * m ^ 2 := by
      have hm2_pos : 0 < m ^ 2 := sq_pos_of_pos hm_pos
      have h4A : 1 < 4 * A := by linarith only [hA2]
      calc m * m = 1 * m ^ 2 := by ring
        _ < (4 * A) * m ^ 2 := mul_lt_mul_of_pos_right h4A hm2_pos
    linarith only [hcontra, h1, h2, h3]

/-! ## Cubic Polynomial Structure over ℤ -/

structure CubicZ where
  c3 : ℤ
  c2 : ℤ
  c1 : ℤ
  c0 : ℤ
  q2 : ℤ
  q1 : ℤ
  q0 : ℤ
  l1 : ℤ
  l0 : ℤ
  e0 : ℤ

namespace CubicZ

def eval (f : CubicZ) (x y : ℤ) : ℤ :=
  f.c3 * x ^ 3 + f.c2 * x ^ 2 * y + f.c1 * x * y ^ 2 + f.c0 * y ^ 3 +
  f.q2 * x ^ 2 + f.q1 * x * y + f.q0 * y ^ 2 + f.l1 * x + f.l0 * y + f.e0

def F (f : CubicZ) (x y : ℤ) : ℤ :=
  f.c3 * x ^ 3 + f.c2 * x ^ 2 * y + f.c1 * x * y ^ 2 + f.c0 * y ^ 3

def fx (f : CubicZ) (x y : ℤ) : ℤ :=
  3 * f.c3 * x ^ 2 + 2 * f.c2 * x * y + f.c1 * y ^ 2 + 2 * f.q2 * x + f.q1 * y + f.l1

def fy (f : CubicZ) (x y : ℤ) : ℤ :=
  f.c2 * x ^ 2 + 2 * f.c1 * x * y + 3 * f.c0 * y ^ 2 + f.q1 * x + 2 * f.q0 * y + f.l0

def Fx (f : CubicZ) (x y : ℤ) : ℤ :=
  3 * f.c3 * x ^ 2 + 2 * f.c2 * x * y + f.c1 * y ^ 2

def Fy (f : CubicZ) (x y : ℤ) : ℤ :=
  f.c2 * x ^ 2 + 2 * f.c1 * x * y + 3 * f.c0 * y ^ 2

def fxx (f : CubicZ) (x y : ℤ) : ℤ := 6 * f.c3 * x + 2 * f.c2 * y + 2 * f.q2
def fxy (f : CubicZ) (x y : ℤ) : ℤ := 2 * f.c2 * x + 2 * f.c1 * y + f.q1
def fyy (f : CubicZ) (x y : ℤ) : ℤ := 2 * f.c1 * x + 6 * f.c0 * y + 2 * f.q0

def Fxx (f : CubicZ) (x y : ℤ) : ℤ := 6 * f.c3 * x + 2 * f.c2 * y
def Fxy (f : CubicZ) (x y : ℤ) : ℤ := 2 * f.c2 * x + 2 * f.c1 * y
def Fyy (f : CubicZ) (x y : ℤ) : ℤ := 2 * f.c1 * x + 6 * f.c0 * y

def detHf (f : CubicZ) (x y : ℤ) : ℤ := f.fxx x y * f.fyy x y - (f.fxy x y) ^ 2
def detHF (f : CubicZ) (x y : ℤ) : ℤ := f.Fxx x y * f.Fyy x y - (f.Fxy x y) ^ 2

def H0 (f : CubicZ) : ℤ := 3 * f.c3 * f.c1 - f.c2 ^ 2
def H1 (f : CubicZ) : ℤ := 9 * f.c3 * f.c0 - f.c2 * f.c1
def H2 (f : CubicZ) : ℤ := 3 * f.c2 * f.c0 - f.c1 ^ 2

def Av (f : CubicZ) (vx vy : ℤ) : ℤ := 3 * f.c3 * vx + f.c2 * vy
def Bv (f : CubicZ) (vx vy : ℤ) : ℤ := 2 * f.c2 * vx + 2 * f.c1 * vy
def Cv (f : CubicZ) (vx vy : ℤ) : ℤ := f.c1 * vx + 3 * f.c0 * vy

def qv (f : CubicZ) (vx vy u1 u2 : ℤ) : ℤ :=
  f.Av vx vy * u1 ^ 2 + f.Bv vx vy * u1 * u2 + f.Cv vx vy * u2 ^ 2

def discQv (f : CubicZ) (vx vy : ℤ) : ℤ :=
  (f.Bv vx vy) ^ 2 - 4 * f.Av vx vy * f.Cv vx vy

lemma detHF_eq (f : CubicZ) (x y : ℤ) :
    f.detHF x y = 4 * (f.H0 * x ^ 2 + f.H1 * x * y + f.H2 * y ^ 2) := by
  dsimp [detHF, Fxx, Fxy, Fyy, H0, H1, H2]
  ring

lemma qv_eq (f : CubicZ) (vx vy u1 u2 : ℤ) :
    f.qv vx vy u1 u2 = vx * f.Fx u1 u2 + vy * f.Fy u1 u2 := by
  dsimp [qv, Av, Bv, Cv, Fx, Fy]
  ring

lemma diff_eval_symm (f : CubicZ) (px py vx vy : ℤ) :
    f.eval (px + vx) (py + vy) - f.eval (px - vx) (py - vy) =
      2 * (vx * f.fx px py + vy * f.fy px py + f.F vx vy) := by
  dsimp [eval, fx, fy, F]
  ring

lemma diff_eval_pell (f : CubicZ) (px py ux uy vx vy x y : ℤ) :
    f.eval (px + x * ux + y * vx) (py + x * uy + y * vy) -
    f.eval (px + x * ux - y * vx) (py + x * uy - y * vy) =
      2 * y * ((vx * f.fx px py + vy * f.fy px py) +
        ((f.fxx px py * vx + f.fxy px py * vy) * ux +
         (f.fxy px py * vx + f.fyy px py * vy) * uy) * x +
        f.qv vx vy ux uy * x ^ 2 + f.F vx vy * y ^ 2) := by
  dsimp [eval, fx, fy, fxx, fxy, fyy, qv, Av, Bv, Cv, F]
  ring

end CubicZ

/-! ## Case 1: Non-vanishing Hessian -/

lemma case1_collision (f : CubicZ)
    (hH : f.H0 ≠ 0 ∨ f.H1 ≠ 0 ∨ f.H2 ≠ 0) :
    ∃ x1 y1 x2 y2 : ℤ, (x1 ≠ x2 ∨ y1 ≠ y2) ∧ f.eval x1 y1 = f.eval x2 y2 := by
  have hp0 : ∃ px py : ℤ, (px ≠ 0 ∨ py ≠ 0) ∧ f.detHF px py ≠ 0 := by
    by_cases h0 : f.H0 ≠ 0
    · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      rw [f.detHF_eq]; simp; exact h0
    · by_cases h2 : f.H2 ≠ 0
      · refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
        rw [f.detHF_eq]; simp; exact h2
      · have h1 : f.H1 ≠ 0 := by
          rcases hH with h | h | h
          · exact absurd h h0
          · exact h
          · exact absurd h h2
        refine ⟨1, 1, Or.inl one_ne_zero, ?_⟩
        rw [f.detHF_eq]
        have hH0 : f.H0 = 0 := not_not.mp h0
        have hH2 : f.H2 = 0 := not_not.mp h2
        simp [hH0, hH2]
        exact h1
  rcases hp0 with ⟨px, py, hp0_nz, hdet0⟩
  let v0x := f.Fy px py
  let v0y := -f.Fx px py
  have hv0_nz : v0x ≠ 0 ∨ v0y ≠ 0 := by
    by_contra h0
    push Not at h0
    have hFx : f.Fx px py = 0 := by dsimp [v0y] at h0; omega
    have hFy : f.Fy px py = 0 := h0.1
    have he1 : f.Fxx px py * px + f.Fxy px py * py = 2 * f.Fx px py := by
      dsimp [CubicZ.Fxx, CubicZ.Fxy, CubicZ.Fx]; ring
    have he2 : f.Fxy px py * px + f.Fyy px py * py = 2 * f.Fy px py := by
      dsimp [CubicZ.Fxy, CubicZ.Fyy, CubicZ.Fy]; ring
    rw [hFx, mul_zero] at he1
    rw [hFy, mul_zero] at he2
    have hpx : f.detHF px py * px =
        f.Fyy px py * (f.Fxx px py * px + f.Fxy px py * py) -
        f.Fxy px py * (f.Fxy px py * px + f.Fyy px py * py) := by
      dsimp [CubicZ.detHF]; ring
    have hpy : f.detHF px py * py =
        f.Fxx px py * (f.Fxy px py * px + f.Fyy px py * py) -
        f.Fxy px py * (f.Fxx px py * px + f.Fxy px py * py) := by
      dsimp [CubicZ.detHF]; ring
    rw [he1, he2, mul_zero, mul_zero, sub_self] at hpx hpy
    rcases mul_eq_zero.mp hpx with hd | hx
    · exact hdet0 hd
    · rcases mul_eq_zero.mp hpy with hd | hy
      · exact hdet0 hd
      · rcases hp0_nz with h | h <;> contradiction
  have hDelta0 : 0 < f.discQv v0x v0y := by
    have hq0 : f.qv v0x v0y px py = 0 := by
      rw [f.qv_eq]; dsimp [v0x, v0y]; ring
    let L1 := 2 * f.Av v0x v0y * px + f.Bv v0x v0y * py
    let L2 := f.Bv v0x v0y * px + 2 * f.Cv v0x v0y * py
    have hL1 : L1 = f.Fxx px py * v0x + f.Fxy px py * v0y := by
      dsimp [L1, CubicZ.Av, CubicZ.Bv, CubicZ.Fxx, CubicZ.Fxy]; ring
    have hL2 : L2 = f.Fxy px py * v0x + f.Fyy px py * v0y := by
      dsimp [L2, CubicZ.Bv, CubicZ.Cv, CubicZ.Fxy, CubicZ.Fyy]; ring
    have hL_nz : L1 ≠ 0 ∨ L2 ≠ 0 := by
      by_contra h0
      push Not at h0
      have hvx : f.detHF px py * v0x = f.Fyy px py * L1 - f.Fxy px py * L2 := by
        rw [hL1, hL2]; dsimp [CubicZ.detHF]; ring
      have hvy : f.detHF px py * v0y = f.Fxx px py * L2 - f.Fxy px py * L1 := by
        rw [hL1, hL2]; dsimp [CubicZ.detHF]; ring
      rw [h0.1, h0.2, mul_zero, mul_zero, sub_self] at hvx hvy
      rcases mul_eq_zero.mp hvx with hd | hx
      · exact hdet0 hd
      · rcases mul_eq_zero.mp hvy with hd | hy
        · exact hdet0 hd
        · rcases hv0_nz with h | h <;> contradiction
    have hid : L1 ^ 2 + L2 ^ 2 - (px ^ 2 + py ^ 2) * f.discQv v0x v0y =
        4 * (f.Av v0x v0y + f.Cv v0x v0y) * f.qv v0x v0y px py := by
      dsimp [L1, L2, CubicZ.discQv, CubicZ.qv]; ring
    rw [hq0, mul_zero] at hid
    have hL_pos : 0 < L1 ^ 2 + L2 ^ 2 := by
      rcases hL_nz with h | h <;> positivity
    have hp_pos : 0 < px ^ 2 + py ^ 2 := by
      rcases hp0_nz with h | h <;> positivity
    nlinarith
  -- Scale by n : ℤ
  let pnx (n : ℤ) := n * px
  let pny (n : ℤ) := n * py
  let vnx (n : ℤ) := f.fy (pnx n) (pny n)
  let vny (n : ℤ) := -f.fx (pnx n) (pny n)
  -- Express (vnx n)^2 + (vny n)^2, (detHf (pnx n) (pny n))^2, and discQv (vnx n) (vny n) as deg-4 polys
  let v1x := f.q1 * px + 2 * f.q0 * py
  let v1y := -(2 * f.q2 * px + f.q1 * py)
  have hvnx : ∀ n, vnx n = v0x * n ^ 2 + v1x * n + f.l0 := by
    intro n; dsimp [vnx, pnx, pny, v0x, v1x, CubicZ.fy, CubicZ.Fy]; ring
  have hvny : ∀ n, vny n = v0y * n ^ 2 + v1y * n - f.l1 := by
    intro n; dsimp [vny, pnx, pny, v0y, v1y, CubicZ.fx, CubicZ.Fx]; ring
  let va4 := v0x ^ 2 + v0y ^ 2
  let va3 := 2 * v0x * v1x + 2 * v0y * v1y
  let va2 := v1x ^ 2 + 2 * v0x * f.l0 + v1y ^ 2 - 2 * v0y * f.l1
  let va1 := 2 * v1x * f.l0 - 2 * v1y * f.l1
  let va0 := f.l0 ^ 2 + f.l1 ^ 2
  have hv_poly : ∀ n, (vnx n) ^ 2 + (vny n) ^ 2 =
      va4 * n ^ 4 + va3 * n ^ 3 + va2 * n ^ 2 + va1 * n + va0 := by
    intro n; rw [hvnx, hvny]; dsimp [va4, va3, va2, va1, va0]; ring
  have hva4_pos : 0 < va4 := by
    rcases hv0_nz with h | h <;> dsimp [va4] <;> positivity
  obtain ⟨N1, _, hN1⟩ := exists_pos_of_poly4 va4 va3 va2 va1 va0 hva4_pos
  -- detHf (pnx n) (pny n) as deg-2 poly
  let d2 := f.detHF px py
  let d1 := f.Fxx px py * (2 * f.q0) + (2 * f.q2) * f.Fyy px py - 2 * f.Fxy px py * f.q1
  let d0 := 4 * f.q2 * f.q0 - f.q1 ^ 2
  have hdet_poly : ∀ n, f.detHf (pnx n) (pny n) = d2 * n ^ 2 + d1 * n + d0 := by
    intro n
    dsimp [CubicZ.detHf, CubicZ.fxx, CubicZ.fxy, CubicZ.fyy, pnx, pny,
      d2, d1, d0, CubicZ.detHF, CubicZ.Fxx, CubicZ.Fxy, CubicZ.Fyy]
    ring
  obtain ⟨N2, _, hN2⟩ := exists_pos_of_poly4 (d2 ^ 2) (2 * d2 * d1) (d1 ^ 2 + 2 * d2 * d0) (2 * d1 * d0) (d0 ^ 2)
    (sq_pos_of_ne_zero hdet0)
  -- discQv (vnx n) (vny n) as deg-4 poly
  let qA2 := f.Av v0x v0y
  let qA1 := f.Av v1x v1y
  let qA0 := f.Av f.l0 (-f.l1)
  let qB2 := f.Bv v0x v0y
  let qB1 := f.Bv v1x v1y
  let qB0 := f.Bv f.l0 (-f.l1)
  let qC2 := f.Cv v0x v0y
  let qC1 := f.Cv v1x v1y
  let qC0 := f.Cv f.l0 (-f.l1)
  let da4 := qB2 ^ 2 - 4 * qA2 * qC2
  let da3 := 2 * qB2 * qB1 - 4 * qA2 * qC1 - 4 * qA1 * qC2
  let da2 := qB1 ^ 2 + 2 * qB2 * qB0 - 4 * qA2 * qC0 - 4 * qA1 * qC1 - 4 * qA0 * qC2
  let da1 := 2 * qB1 * qB0 - 4 * qA1 * qC0 - 4 * qA0 * qC1
  let da0 := qB0 ^ 2 - 4 * qA0 * qC0
  have hdisc_poly : ∀ n, f.discQv (vnx n) (vny n) =
      da4 * n ^ 4 + da3 * n ^ 3 + da2 * n ^ 2 + da1 * n + da0 := by
    intro n
    have hAv : f.Av (vnx n) (vny n) = qA2 * n ^ 2 + qA1 * n + qA0 := by
      rw [hvnx, hvny]; dsimp [CubicZ.Av, qA2, qA1, qA0]; ring
    have hBv : f.Bv (vnx n) (vny n) = qB2 * n ^ 2 + qB1 * n + qB0 := by
      rw [hvnx, hvny]; dsimp [CubicZ.Bv, qB2, qB1, qB0]; ring
    have hCv : f.Cv (vnx n) (vny n) = qC2 * n ^ 2 + qC1 * n + qC0 := by
      rw [hvnx, hvny]; dsimp [CubicZ.Cv, qC2, qC1, qC0]; ring
    dsimp [CubicZ.discQv]
    rw [hAv, hBv, hCv]
    dsimp [da4, da3, da2, da1, da0]
    ring
  have hda4_pos : 0 < da4 := hDelta0
  obtain ⟨N3, _, hN3⟩ := exists_pos_of_poly4 da4 da3 da2 da1 da0 hda4_pos
  let n := max N1 (max N2 N3)
  let px' := pnx n
  let py' := pny n
  let vx := vnx n
  let vy := vny n
  have hv_sq_pos : 0 < vx ^ 2 + vy ^ 2 := by
    rw [hv_poly]; exact hN1 n (le_max_left _ _)
  have hv_nz : vx ≠ 0 ∨ vy ≠ 0 := by
    by_contra h0; push Not at h0
    rw [h0.1, h0.2] at hv_sq_pos; norm_num at hv_sq_pos
  have hdir0 : vx * f.fx px' py' + vy * f.fy px' py' = 0 := by
    dsimp [vx, vy, vnx, vny, px', py']; ring
  have hdet_nz : f.detHf px' py' ≠ 0 := by
    intro h0
    have hsq0 : (f.detHf px' py') ^ 2 = 0 := by rw [h0]; ring
    have hpos : 0 < (f.detHf px' py') ^ 2 := by
      have := hN2 n (le_trans (le_max_left _ _) (le_max_right _ _))
      rw [hdet_poly]
      linarith
    linarith
  have hdisc_pos : 0 < f.discQv vx vy := by
    rw [hdisc_poly]; exact hN3 n (le_trans (le_max_right _ _) (le_max_right _ _))
  let c := f.F vx vy
  by_cases hc : c = 0
  · refine ⟨px' + vx, py' + vy, px' - vx, py' - vy, ?_, ?_⟩
    · rcases hv_nz with h | h
      · left; omega
      · right; omega
    · have := f.diff_eval_symm px' py' vx vy
      rw [hdir0, show f.F vx vy = c from rfl, hc] at this
      omega
  · -- Subcase 1b: c ≠ 0
    let A := f.Av vx vy
    let B := f.Bv vx vy
    let C := f.Cv vx vy
    have hdisc_ABC : 0 < B ^ 2 - 4 * A * C := hdisc_pos
    have hw0 : ∃ w0x w0y : ℤ, c * f.qv vx vy w0x w0y < 0 := by
      by_cases hA : A = 0
      · have hB_nz : B ≠ 0 := by
          intro hB0
          rw [hA, hB0] at hdisc_ABC; norm_num at hdisc_ABC
        have hcB_nz : c * B ≠ 0 := mul_ne_zero hc hB_nz
        rcases lt_or_gt_of_ne hcB_nz with hneg | hpos
        · refine ⟨|C| + 1, 1, ?_⟩
          have hq : f.qv vx vy (|C| + 1) 1 = B * (|C| + 1) + C := by
            dsimp [CubicZ.qv]; rw [show f.Av vx vy = A from rfl, hA]; ring
          rw [hq]
          have h1 : c * (B * (|C| + 1) + C) = (c * B) * (|C| + 1) + c * C := by ring
          have h2 : c * C ≤ |c| * |C| := by
            calc c * C ≤ |c * C| := le_abs_self _
            _ = |c| * |C| := abs_mul _ _
          have h3 : |c| * |C| ≤ (-(c * B)) * |C| := by
            have h4 : |c| ≤ -(c * B) := by
              have hcb : |c * B| = -(c * B) := abs_of_neg hneg
              have hB1 : 1 ≤ |B| := Int.one_le_abs hB_nz
              rw [← hcb, abs_mul]
              nlinarith [abs_nonneg c]
            nlinarith [abs_nonneg C]
          nlinarith
        · refine ⟨-(|C| + 1), 1, ?_⟩
          have hq : f.qv vx vy (-(|C| + 1)) 1 = B * (-(|C| + 1)) + C := by
            dsimp [CubicZ.qv]; rw [show f.Av vx vy = A from rfl, hA]; ring
          rw [hq]
          have h1 : c * (B * (-(|C| + 1)) + C) = -(c * B) * (|C| + 1) + c * C := by ring
          have h2 : c * C ≤ |c| * |C| := by
            calc c * C ≤ |c * C| := le_abs_self _
            _ = |c| * |C| := abs_mul _ _
          have h3 : |c| * |C| ≤ (c * B) * |C| := by
            have h4 : |c| ≤ c * B := by
              have hcb : |c * B| = c * B := abs_of_pos hpos
              have hB1 : 1 ≤ |B| := Int.one_le_abs hB_nz
              rw [← hcb, abs_mul]
              nlinarith [abs_nonneg c]
            nlinarith [abs_nonneg C]
          nlinarith
      · have hq1 : f.qv vx vy 1 0 = A := by
          dsimp [CubicZ.qv]; ring
        have hq2 : 4 * A * f.qv vx vy (-B) (2 * A) = -(B ^ 2 - 4 * A * C) * (2 * A) ^ 2 := by
          dsimp [CubicZ.qv]; change 4 * A * (A * (-B) ^ 2 + B * (-B) * (2 * A) + C * (2 * A) ^ 2) = _; ring
        have hneg_prod : (c * f.qv vx vy 1 0) * (c * f.qv vx vy (-B) (2 * A)) < 0 := by
          rw [hq1]
          have : 4 * (c * A) * (c * f.qv vx vy (-B) (2 * A)) =
              c ^ 2 * (4 * A * f.qv vx vy (-B) (2 * A)) := by ring
          rw [hq2] at this
          have h4pos : 0 < c ^ 2 * ((B ^ 2 - 4 * A * C) * (2 * A) ^ 2) := by
            have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
            have hA2 : 0 < (2 * A) ^ 2 := sq_pos_of_ne_zero (by omega)
            positivity
          nlinarith
        by_cases h1 : c * f.qv vx vy 1 0 < 0
        · exact ⟨1, 0, h1⟩
        · refine ⟨-B, 2 * A, ?_⟩
          nlinarith
    rcases hw0 with ⟨w0x, w0y, hw0_neg⟩
    let lx := f.fxx px' py' * vx + f.fxy px' py' * vy
    let ly := f.fxy px' py' * vx + f.fyy px' py' * vy
    let ell (u1 u2 : ℤ) := lx * u1 + ly * u2
    have hl_nz : lx ≠ 0 ∨ ly ≠ 0 := by
      by_contra h0; push Not at h0
      have hvx : f.detHf px' py' * vx = f.fyy px' py' * lx - f.fxy px' py' * ly := by
        dsimp [CubicZ.detHf, lx, ly]; ring
      have hvy : f.detHf px' py' * vy = f.fxx px' py' * ly - f.fxy px' py' * lx := by
        dsimp [CubicZ.detHf, lx, ly]; ring
      rw [h0.1, h0.2, mul_zero, mul_zero, sub_self] at hvx hvy
      rcases mul_eq_zero.mp hvx with hd | hx
      · exact hdet_nz hd
      · rcases mul_eq_zero.mp hvy with hd | hy
        · exact hdet_nz hd
        · rcases hv_nz with h | h <;> contradiction
    have hw : ∃ wx wy : ℤ, c * f.qv vx vy wx wy < 0 ∧ ell wx wy ≠ 0 := by
      by_cases h0 : ell w0x w0y ≠ 0
      · exact ⟨w0x, w0y, hw0_neg, h0⟩
      · have h0' : ell w0x w0y = 0 := not_not.mp h0
        have he : ∃ ex ey : ℤ, ell ex ey ≠ 0 := by
          rcases hl_nz with hx | hy
          · exact ⟨1, 0, by dsimp [ell]; omega⟩
          · exact ⟨0, 1, by dsimp [ell]; omega⟩
        rcases he with ⟨ex, ey, he_nz⟩
        let a2 := -(c * f.qv vx vy w0x w0y)
        let a1 := -(c * (2 * A * w0x * ex + B * (w0x * ey + w0y * ex) + 2 * C * w0y * ey))
        let a0 := -(c * f.qv vx vy ex ey)
        obtain ⟨K, _, hK⟩ := exists_pos_of_poly2 a2 a1 a0 (by dsimp [a2]; linarith)
        refine ⟨K * w0x + ex, K * w0y + ey, ?_, ?_⟩
        · have hid : -(c * f.qv vx vy (K * w0x + ex) (K * w0y + ey)) =
              a2 * K ^ 2 + a1 * K + a0 := by
            dsimp [a2, a1, a0, CubicZ.qv, A, B, C]; ring
          have := hK K (le_refl K)
          linarith
        · have hid : ell (K * w0x + ex) (K * w0y + ey) = K * ell w0x w0y + ell ex ey := by
            dsimp [ell]; ring
          rw [hid, h0', mul_zero, zero_add]
          exact he_nz
    rcases hw with ⟨wx, wy, hw_neg, hell_nz⟩
    have hw_nz : wx ^ 2 + wy ^ 2 ≠ 0 := by
      intro h0
      have hwx : wx = 0 := by nlinarith [sq_nonneg wx, sq_nonneg wy]
      have hwy : wy = 0 := by nlinarith [sq_nonneg wx, sq_nonneg wy]
      apply hell_nz
      dsimp [ell]; rw [hwx, hwy]; ring
    let u0x := -wy
    let u0y := wx
    let umx (m : ℤ) := m * wx + u0x
    let umy (m : ℤ) := m * wy + u0y
    let A' := -c * f.qv vx vy wx wy
    let B' := -c * (2 * A * wx * u0x + B * (wx * u0y + wy * u0x) + 2 * C * wy * u0y)
    let C' := -c * f.qv vx vy u0x u0y
    have hA'_pos : 0 < A' := by dsimp [A']; linarith
    have hDisc' : B' ^ 2 - 4 * A' * C' ≠ 0 := by
      have hid : B' ^ 2 - 4 * A' * C' =
          c ^ 2 * (B ^ 2 - 4 * A * C) * (wx * u0y - wy * u0x) ^ 2 := by
        dsimp [A', B', C', CubicZ.qv, A, B, C]; ring
      rw [hid]
      have hdet_uw : wx * u0y - wy * u0x = wx ^ 2 + wy ^ 2 := by dsimp [u0x, u0y]; ring
      rw [hdet_uw]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hc) (ne_of_gt hdisc_ABC)) (pow_ne_zero 2 hw_nz)
    let M := |ell u0x u0y| + 1
    obtain ⟨m, hmM, hDm_pos, hDm_nsq⟩ := exists_non_square_quadratic A' B' C' hA'_pos hDisc' M
    have hDm_eq : A' * m ^ 2 + B' * m + C' = -c * f.qv vx vy (umx m) (umy m) := by
      dsimp [A', B', C', umx, umy, CubicZ.qv, A, B, C]; ring
    let b := ell (umx m) (umy m)
    have hb_nz : b ≠ 0 := by
      have hid : b = m * ell wx wy + ell u0x u0y := by
        dsimp [b, ell, umx, umy]; ring
      intro hb0
      have h1 : |m| * |ell wx wy| = |ell u0x u0y| := by
        rw [← abs_mul]
        have : m * ell wx wy = -ell u0x u0y := by linarith
        rw [this, abs_neg]
      have h2 : 1 ≤ |ell wx wy| := Int.one_le_abs hell_nz
      have h3 : |ell u0x u0y| + 1 ≤ |m| := by
        have hm_pos' : 0 ≤ m := by linarith [abs_nonneg (ell u0x u0y)]
        rw [abs_of_nonneg hm_pos']
        exact hmM
      nlinarith [abs_nonneg m, abs_nonneg (ell wx wy), abs_nonneg (ell u0x u0y)]
    let a := f.qv vx vy (umx m) (umy m)
    let D := -a * c
    have hD_pos : 0 < D := by dsimp [D, a]; linarith [hDm_eq]
    have hD_nsq : ¬ IsSquare D.toNat := by
      have : D = A' * m ^ 2 + B' * m + C' := by dsimp [D, a]; linarith [hDm_eq]
      rw [this]; exact hDm_nsq
    have hD_nsqZ : ¬ IsSquare D := by
      rintro ⟨k, hk⟩
      apply hD_nsq
      refine ⟨k.natAbs, ?_⟩
      have hcast : ((k.natAbs * k.natAbs : ℕ) : ℤ) = (D.toNat : ℤ) := by
        push_cast
        rw [← sq, sq_abs, sq, ← hk, Int.toNat_of_nonneg (le_of_lt hD_pos)]
      exact (Int.ofNat.inj hcast).symm
    obtain ⟨U, V, hPellZ, hV_nz⟩ := Pell.exists_of_not_isSquare hD_pos hD_nsqZ
    have hU_nz : U ≠ 0 := by
      intro hU0
      rw [hU0] at hPellZ
      have : D * V ^ 2 = -1 := by linarith
      have : 0 ≤ D * V ^ 2 := mul_nonneg (le_of_lt hD_pos) (sq_nonneg V)
      linarith
    let x := -b * c * V ^ 2
    let y := b * U * V
    have hy_nz : y ≠ 0 := mul_ne_zero (mul_ne_zero hb_nz hU_nz) hV_nz
    refine ⟨px' + x * umx m + y * vx, py' + x * umy m + y * vy,
      px' + x * umx m - y * vx, py' + x * umy m - y * vy, ?_, ?_⟩
    · rcases hv_nz with h | h
      · left
        have : y * vx ≠ 0 := mul_ne_zero hy_nz h
        omega
      · right
        have : y * vy ≠ 0 := mul_ne_zero hy_nz h
        omega
    · have hdiff := f.diff_eval_pell px' py' (umx m) (umy m) vx vy x y
      have hmain : b * x + a * x ^ 2 + c * y ^ 2 = 0 := by
        calc
          b * x + a * x ^ 2 + c * y ^ 2
              = b ^ 2 * c * V ^ 2 * (U ^ 2 - (-a * c) * V ^ 2 - 1) := by
                dsimp [x, y]; ring
          _ = b ^ 2 * c * V ^ 2 * (U ^ 2 - D * V ^ 2 - 1) := rfl
          _ = 0 := by rw [hPellZ]; ring
      have h1 : vx * f.fx px' py' + vy * f.fy px' py' +
          ((f.fxx px' py' * vx + f.fxy px' py' * vy) * umx m +
           (f.fxy px' py' * vx + f.fyy px' py' * vy) * umy m) * x +
          f.qv vx vy (umx m) (umy m) * x ^ 2 + f.F vx vy * y ^ 2 = 0 := by
        rw [hdir0, zero_add]
        change b * x + a * x ^ 2 + c * y ^ 2 = 0
        exact hmain
      rw [h1, mul_zero] at hdiff
      omega

/-! ## Case 2: Vanishing Hessian -/

lemma reduced_cubic_collision (A b1 b0 C3 d2 d1 d0 : ℤ) (_hC3 : C3 ≠ 0) :
    ∃ x1 y1 x2 y2 : ℤ, (x1 ≠ x2 ∨ y1 ≠ y2) ∧
      A * y1 ^ 2 + (b1 * x1 + b0) * y1 + (C3 * x1 ^ 3 + d2 * x1 ^ 2 + d1 * x1 + d0) =
      A * y2 ^ 2 + (b1 * x2 + b0) * y2 + (C3 * x2 ^ 3 + d2 * x2 ^ 2 + d1 * x2 + d0) := by
  by_cases hb0 : b0 = 0
  · refine ⟨0, 1, 0, -1, Or.inr (by omega), ?_⟩
    rw [hb0]; ring
  · by_cases hA : A = 0
    · let z := C3 * b0 ^ 2 + d2 * b0 + d1
      refine ⟨b0, 0, 0, z, Or.inl hb0, ?_⟩
      rw [hA]; dsimp [z]; ring
    · let X := 8 * A * b0
      let z := 4 * A * C3 * X ^ 2 + (4 * A * d2 - b1 ^ 2) * X + (4 * A * d1 - 2 * b1 * b0)
      let y := -z - 4 * b1 * b0
      have hX_nz : X ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hA) hb0
      refine ⟨X, y, 0, z, Or.inl hX_nz, ?_⟩
      have hid : 4 * A * (
          (A * y ^ 2 + (b1 * X + b0) * y + (C3 * X ^ 3 + d2 * X ^ 2 + d1 * X + d0)) -
          (A * z ^ 2 + (b1 * 0 + b0) * z + (C3 * 0 ^ 3 + d2 * 0 ^ 2 + d1 * 0 + d0))) = 0 := by
        dsimp [y, z, X]; ring
      rcases mul_eq_zero.mp hid with h4A | hdiff
      · exact absurd h4A (mul_ne_zero (by norm_num) hA)
      · omega

lemma case2_collision (f : CubicZ)
    (hc_nz : f.c3 ≠ 0 ∨ f.c2 ≠ 0 ∨ f.c1 ≠ 0 ∨ f.c0 ≠ 0)
    (hH0 : f.H0 = 0) (hH1 : f.H1 = 0) (hH2 : f.H2 = 0) :
    ∃ x1 y1 x2 y2 : ℤ, (x1 ≠ x2 ∨ y1 ≠ y2) ∧ f.eval x1 y1 = f.eval x2 y2 := by
  by_cases hc3 : f.c3 = 0
  · have hc2 : f.c2 = 0 := by
      have : 3 * f.c3 * f.c1 - f.c2 ^ 2 = 0 := hH0
      rw [hc3] at this; nlinarith
    have hc1 : f.c1 = 0 := by
      have : 3 * f.c2 * f.c0 - f.c1 ^ 2 = 0 := hH2
      rw [hc2] at this; nlinarith
    have hc0 : f.c0 ≠ 0 := by
      rcases hc_nz with h | h | h | h
      · exact absurd hc3 h
      · exact absurd hc2 h
      · exact absurd hc1 h
      · exact h
    obtain ⟨X1, Y1, X2, Y2, hne, heq⟩ :=
      reduced_cubic_collision f.q2 (-f.q1) f.l1 (-f.c0) f.q0 (-f.l0) f.e0 (neg_ne_zero.mpr hc0)
    refine ⟨Y1, -X1, Y2, -X2, ?_, ?_⟩
    · rcases hne with h | h
      · right; omega
      · left; omega
    · have he1 : f.eval Y1 (-X1) =
          f.q2 * Y1 ^ 2 + (-f.q1 * X1 + f.l1) * Y1 + (-f.c0 * X1 ^ 3 + f.q0 * X1 ^ 2 + -f.l0 * X1 + f.e0) := by
        dsimp [CubicZ.eval]; rw [hc3, hc2, hc1]; ring
      have he2 : f.eval Y2 (-X2) =
          f.q2 * Y2 ^ 2 + (-f.q1 * X2 + f.l1) * Y2 + (-f.c0 * X2 ^ 3 + f.q0 * X2 ^ 2 + -f.l0 * X2 + f.e0) := by
        dsimp [CubicZ.eval]; rw [hc3, hc2, hc1]; ring
      rw [he1, he2]; exact heq
  · let g : ℤ := (Int.gcd (3 * f.c3) f.c2 : ℤ)
    have hg_pos : 0 < g := by
      have hne : Int.gcd (3 * f.c3) f.c2 ≠ 0 := by
        intro h0
        have h3c3 : 3 * f.c3 = 0 := Int.gcd_eq_zero_iff.mp h0 |>.1
        omega
      dsimp [g]; omega
    let r := (3 * f.c3) / g
    let s := f.c2 / g
    have hr_mul : r * g = 3 * f.c3 := by
      dsimp [r, g]
      exact Int.ediv_mul_cancel (Int.gcd_dvd_left (3 * f.c3) f.c2)
    have hs_mul : s * g = f.c2 := by
      dsimp [s, g]
      exact Int.ediv_mul_cancel (Int.gcd_dvd_right (3 * f.c3) f.c2)
    have hr_nz : r ≠ 0 := by
      intro hr0; rw [hr0, zero_mul] at hr_mul; omega
    let v := Int.gcdA (3 * f.c3) f.c2
    let u := -Int.gcdB (3 * f.c3) f.c2
    have hbez : r * v - s * u = 1 := by
      have hgcd := Int.gcd_eq_gcd_ab (3 * f.c3) f.c2
      have h1 : g * 1 = g * (r * v - s * u) := by
        calc g * 1 = (Int.gcd (3 * f.c3) f.c2 : ℤ) := by dsimp [g]; ring
        _ = (3 * f.c3) * Int.gcdA (3 * f.c3) f.c2 + f.c2 * Int.gcdB (3 * f.c3) f.c2 := hgcd
        _ = (r * g) * v + (s * g) * (-u) := by rw [hr_mul, hs_mul]; dsimp [u]; ring
        _ = g * (r * v - s * u) := by ring
      exact mul_left_cancel₀ (ne_of_gt hg_pos) h1.symm
    have hrc2 : r * f.c2 = 3 * f.c3 * s := by
      have h1 : g * (r * f.c2) = g * (3 * f.c3 * s) := by
        calc g * (r * f.c2) = (r * g) * f.c2 := by ring
        _ = (3 * f.c3) * (s * g) := by rw [hr_mul, hs_mul]
        _ = g * (3 * f.c3 * s) := by ring
      exact mul_left_cancel₀ (ne_of_gt hg_pos) h1
    have hrc1 : r ^ 2 * f.c1 = 3 * f.c3 * s ^ 2 := by
      have hH0' : 3 * f.c3 * f.c1 = f.c2 ^ 2 := by dsimp [CubicZ.H0] at hH0; linarith
      have h1 : (3 * f.c3) * (r ^ 2 * f.c1) = (3 * f.c3) * (3 * f.c3 * s ^ 2) := by
        calc (3 * f.c3) * (r ^ 2 * f.c1) = r ^ 2 * (3 * f.c3 * f.c1) := by ring
        _ = (r * f.c2) ^ 2 := by rw [hH0']; ring
        _ = (3 * f.c3 * s) ^ 2 := by rw [hrc2]
        _ = (3 * f.c3) * (3 * f.c3 * s ^ 2) := by ring
      exact mul_left_cancel₀ (by omega) h1
    have hrc0 : r ^ 3 * f.c0 = f.c3 * s ^ 3 := by
      have hH1' : 9 * f.c3 * f.c0 = f.c2 * f.c1 := by dsimp [CubicZ.H1] at hH1; linarith
      have h1 : (9 * f.c3) * (r ^ 3 * f.c0) = (9 * f.c3) * (f.c3 * s ^ 3) := by
        calc (9 * f.c3) * (r ^ 3 * f.c0) = r ^ 3 * (9 * f.c3 * f.c0) := by ring
        _ = (r * f.c2) * (r ^ 2 * f.c1) := by rw [hH1']; ring
        _ = (3 * f.c3 * s) * (3 * f.c3 * s ^ 2) := by rw [hrc2, hrc1]
        _ = (9 * f.c3) * (f.c3 * s ^ 3) := by ring
      exact mul_left_cancel₀ (by omega) h1
    have hr3F : ∀ x y : ℤ, r ^ 3 * f.F x y = f.c3 * (r * x + s * y) ^ 3 := by
      intro x y
      dsimp [CubicZ.F]
      calc r ^ 3 * (f.c3 * x ^ 3 + f.c2 * x ^ 2 * y + f.c1 * x * y ^ 2 + f.c0 * y ^ 3)
          = f.c3 * (r * x) ^ 3 + (r * f.c2) * (r * x) ^ 2 * y + (r ^ 2 * f.c1) * (r * x) * y ^ 2 + (r ^ 3 * f.c0) * y ^ 3 := by ring
      _ = f.c3 * (r * x) ^ 3 + (3 * f.c3 * s) * (r * x) ^ 2 * y + (3 * f.c3 * s ^ 2) * (r * x) * y ^ 2 + (f.c3 * s ^ 3) * y ^ 3 := by
          rw [hrc2, hrc1, hrc0]
      _ = f.c3 * (r * x + s * y) ^ 3 := by ring
    let A := r ^ 3 * (f.q2 * s ^ 2 - f.q1 * r * s + f.q0 * r ^ 2)
    let b1 := r ^ 3 * (-2 * f.q2 * v * s + f.q1 * (v * r + u * s) - 2 * f.q0 * u * r)
    let b0 := r ^ 3 * (-f.l1 * s + f.l0 * r)
    let C3 := f.c3
    let d2 := r ^ 3 * (f.q2 * v ^ 2 - f.q1 * v * u + f.q0 * u ^ 2)
    let d1 := r ^ 3 * (f.l1 * v - f.l0 * u)
    let d0 := r ^ 3 * f.e0
    have htrans : ∀ X Y : ℤ, r ^ 3 * f.eval (v * X - s * Y) (-u * X + r * Y) =
        A * Y ^ 2 + (b1 * X + b0) * Y + (C3 * X ^ 3 + d2 * X ^ 2 + d1 * X + d0) := by
      intro X Y
      have hFpart : r ^ 3 * f.F (v * X - s * Y) (-u * X + r * Y) = f.c3 * X ^ 3 := by
        rw [hr3F]
        have : r * (v * X - s * Y) + s * (-u * X + r * Y) = (r * v - s * u) * X := by ring
        rw [this, hbez, one_mul]
      have hrest : f.eval (v * X - s * Y) (-u * X + r * Y) = f.F (v * X - s * Y) (-u * X + r * Y) +
          (f.q2 * (v * X - s * Y) ^ 2 + f.q1 * (v * X - s * Y) * (-u * X + r * Y) +
           f.q0 * (-u * X + r * Y) ^ 2 + f.l1 * (v * X - s * Y) + f.l0 * (-u * X + r * Y) + f.e0) := by
        dsimp [CubicZ.eval, CubicZ.F]; ring
      rw [hrest, mul_add, hFpart]
      dsimp [A, b1, b0, C3, d2, d1, d0]
      ring
    obtain ⟨X1, Y1, X2, Y2, hne, heq⟩ :=
      reduced_cubic_collision A b1 b0 C3 d2 d1 d0 hc3
    refine ⟨v * X1 - s * Y1, -u * X1 + r * Y1, v * X2 - s * Y2, -u * X2 + r * Y2, ?_, ?_⟩
    · by_contra h0; push Not at h0
      have hX : X1 = X2 := by
        have h1 : r * (v * X1 - s * Y1) + s * (-u * X1 + r * Y1) =
            r * (v * X2 - s * Y2) + s * (-u * X2 + r * Y2) := by rw [h0.1, h0.2]
        have hl : r * (v * X1 - s * Y1) + s * (-u * X1 + r * Y1) = (r * v - s * u) * X1 := by ring
        have hr : r * (v * X2 - s * Y2) + s * (-u * X2 + r * Y2) = (r * v - s * u) * X2 := by ring
        rw [hl, hr, hbez, one_mul, one_mul] at h1
        exact h1
      have hY : Y1 = Y2 := by
        have h1 : u * (v * X1 - s * Y1) + v * (-u * X1 + r * Y1) =
            u * (v * X2 - s * Y2) + v * (-u * X2 + r * Y2) := by rw [h0.1, h0.2]
        have hl : u * (v * X1 - s * Y1) + v * (-u * X1 + r * Y1) = (r * v - s * u) * Y1 := by ring
        have hr : u * (v * X2 - s * Y2) + v * (-u * X2 + r * Y2) = (r * v - s * u) * Y2 := by ring
        rw [hl, hr, hbez, one_mul, one_mul] at h1
        exact h1
      rcases hne with h | h <;> contradiction
    · have h1 : r ^ 3 * f.eval (v * X1 - s * Y1) (-u * X1 + r * Y1) =
          r ^ 3 * f.eval (v * X2 - s * Y2) (-u * X2 + r * Y2) := by
        rw [htrans, htrans]; exact heq
      exact mul_left_cancel₀ (pow_ne_zero 3 hr_nz) h1

lemma cubic_collision (f : CubicZ) (hc_nz : f.c3 ≠ 0 ∨ f.c2 ≠ 0 ∨ f.c1 ≠ 0 ∨ f.c0 ≠ 0) :
    ∃ x1 y1 x2 y2 : ℤ, (x1 ≠ x2 ∨ y1 ≠ y2) ∧ f.eval x1 y1 = f.eval x2 y2 := by
  by_cases hH : f.H0 ≠ 0 ∨ f.H1 ≠ 0 ∨ f.H2 ≠ 0
  · exact case1_collision f hH
  · push Not at hH
    exact case2_collision f hc_nz hH.1 hH.2.1 hH.2.2

/-! ## Extracting Integer Cubic from `MvPolynomial (Fin 2) ℚ` -/

noncomputable def denom (p : MvPolynomial (Fin 2) ℚ) : ℕ :=
  ∏ m ∈ p.support, (p.coeff m).den

lemma denom_pos (p : MvPolynomial (Fin 2) ℚ) : 0 < denom p := by
  dsimp [denom]
  exact Finset.prod_pos fun m _ => Rat.den_pos (p.coeff m)

noncomputable def intCoeff (p : MvPolynomial (Fin 2) ℚ) (i j : ℕ) : ℤ :=
  let m : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j
  if _hm : m ∈ p.support then
    (p.coeff m).num * ((∏ m' ∈ p.support.erase m, (p.coeff m').den : ℕ) : ℤ)
  else 0

lemma intCoeff_cast (p : MvPolynomial (Fin 2) ℚ) (i j : ℕ) :
    (intCoeff p i j : ℚ) =
      (denom p : ℚ) * p.coeff (Finsupp.single 0 i + Finsupp.single 1 j) := by
  dsimp [intCoeff]
  set m : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j
  split_ifs with hm
  · have hprod : denom p = (p.coeff m).den * ∏ m' ∈ p.support.erase m, (p.coeff m').den := by
      dsimp [denom]
      exact (Finset.mul_prod_erase p.support (fun m' => (p.coeff m').den) hm).symm
    push_cast
    rw [hprod]
    push_cast
    have hrat : ((p.coeff m).den : ℚ) * p.coeff m = ((p.coeff m).num : ℚ) := by
      rw [mul_comm]
      exact Rat.mul_den_eq_num (p.coeff m)
    calc
      ((p.coeff m).num : ℚ) * (∏ m' ∈ p.support.erase m, ((p.coeff m').den : ℚ))
          = ((p.coeff m).den : ℚ) * p.coeff m * (∏ m' ∈ p.support.erase m, ((p.coeff m').den : ℚ)) := by
            rw [hrat]
      _ = ((p.coeff m).den : ℚ) * (∏ m' ∈ p.support.erase m, ((p.coeff m').den : ℚ)) * p.coeff m := by
            ring
  · have h0 : p.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
    rw [h0, mul_zero, Int.cast_zero]

noncomputable def toCubicZ (p : MvPolynomial (Fin 2) ℚ) : CubicZ :=
  { c3 := intCoeff p 3 0
    c2 := intCoeff p 2 1
    c1 := intCoeff p 1 2
    c0 := intCoeff p 0 3
    q2 := intCoeff p 2 0
    q1 := intCoeff p 1 1
    q0 := intCoeff p 0 2
    l1 := intCoeff p 1 0
    l0 := intCoeff p 0 1
    e0 := intCoeff p 0 0 }

lemma fin2_finsupp_eq (m : Fin 2 →₀ ℕ) :
    m = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
  ext i
  fin_cases i <;> simp

lemma fin2_finsupp_sum (m : Fin 2 →₀ ℕ) :
    m.sum (fun _ e => e) = m 0 + m 1 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp [Fin.sum_univ_two]

lemma eval_toCubicZ (p : MvPolynomial (Fin 2) ℚ) (hp : p.totalDegree = 3) (x y : ℤ) :
    (denom p : ℚ) * OMA.S_mo_392283.latticeValue p ![x, y] = ((toCubicZ p).eval x y : ℚ) := by
  dsimp [OMA.S_mo_392283.latticeValue]
  rw [MvPolynomial.eval_eq', Finset.mul_sum]
  have hterm : ∀ m ∈ p.support,
      (denom p : ℚ) * (p.coeff m * ∏ i : Fin 2, ((![x, y] i : ℤ) : ℚ) ^ m i) =
      (intCoeff p (m 0) (m 1) : ℚ) * (x : ℚ) ^ m 0 * (y : ℚ) ^ m 1 := by
    intro m _
    have hprod : (∏ i : Fin 2, ((![x, y] i : ℤ) : ℚ) ^ m i) = (x : ℚ) ^ m 0 * (y : ℚ) ^ m 1 := by
      simp [Fin.prod_univ_two]
    rw [hprod, ← mul_assoc]
    have hm_c : p.coeff m = p.coeff (Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1)) := by
      congr 1; exact fin2_finsupp_eq m
    rw [hm_c, ← intCoeff_cast]
    ring
  rw [Finset.sum_congr rfl hterm]
  let S : Finset (ℕ × ℕ) := (Finset.range 4 ×ˢ Finset.range 4).filter (fun ij => ij.1 + ij.2 ≤ 3)
  have hsub : p.support.image (fun m : Fin 2 →₀ ℕ => (m 0, m 1)) ⊆ S := by
    intro ij hij
    rcases Finset.mem_image.mp hij with ⟨m, hm, rfl⟩
    have hdeg : m.sum (fun _ e => e) ≤ 3 := by
      rw [← hp]
      exact Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ e => e) hm
    rw [fin2_finsupp_sum] at hdeg
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  have hinj : Set.InjOn (fun m : Fin 2 →₀ ℕ => (m 0, m 1)) p.support := by
    intro m1 _ m2 _ heq
    have h0 : m1 0 = m2 0 := congrArg Prod.fst heq
    have h1 : m1 1 = m2 1 := congrArg Prod.snd heq
    rw [fin2_finsupp_eq m1, fin2_finsupp_eq m2, h0, h1]
  have hsum1 : ∑ m ∈ p.support, (intCoeff p (m 0) (m 1) : ℚ) * (x : ℚ) ^ m 0 * (y : ℚ) ^ m 1 =
      ∑ ij ∈ p.support.image (fun m : Fin 2 →₀ ℕ => (m 0, m 1)),
        (intCoeff p ij.1 ij.2 : ℚ) * (x : ℚ) ^ ij.1 * (y : ℚ) ^ ij.2 := by
    symm
    exact Finset.sum_image (fun m1 hm1 m2 hm2 heq => hinj hm1 hm2 heq)
  rw [hsum1]
  have hzero : ∀ ij ∈ S, ij ∉ p.support.image (fun m : Fin 2 →₀ ℕ => (m 0, m 1)) →
      (intCoeff p ij.1 ij.2 : ℚ) * (x : ℚ) ^ ij.1 * (y : ℚ) ^ ij.2 = 0 := by
    intro ij _ hij
    have hm_not : Finsupp.single 0 ij.1 + Finsupp.single 1 ij.2 ∉ p.support := by
      intro hm
      apply hij
      refine Finset.mem_image.mpr ⟨Finsupp.single 0 ij.1 + Finsupp.single 1 ij.2, hm, ?_⟩
      ext <;> simp
    have hic : intCoeff p ij.1 ij.2 = 0 := by
      simp only [intCoeff, dif_neg hm_not]
    rw [hic, Int.cast_zero, zero_mul, zero_mul]
  rw [Finset.sum_subset hsub hzero]
  have hS_eval : S = {(3, 0), (2, 1), (1, 2), (0, 3), (2, 0), (1, 1), (0, 2), (1, 0), (0, 1), (0, 0)} := by
    decide
  rw [hS_eval]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  dsimp [toCubicZ, CubicZ.eval]
  push_cast
  ring

lemma toCubicZ_cubic_nz (p : MvPolynomial (Fin 2) ℚ) (hp : p.totalDegree = 3) :
    let f := toCubicZ p
    f.c3 ≠ 0 ∨ f.c2 ≠ 0 ∨ f.c1 ≠ 0 ∨ f.c0 ≠ 0 := by
  have hne_empty : p.support.Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    have hd : p.totalDegree = 0 := by
      dsimp [MvPolynomial.totalDegree]
      rw [h0, Finset.sup_empty, bot_eq_zero']
    omega
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup p.support hne_empty (fun s : Fin 2 →₀ ℕ => s.sum fun _ e => e)
  have hdeg3 : m 0 + m 1 = 3 := by
    dsimp [MvPolynomial.totalDegree] at hp
    rw [← fin2_finsupp_sum, ← hmax]
    exact hp
  have hic_nz : intCoeff p (m 0) (m 1) ≠ 0 := by
    intro h0
    have hcast := intCoeff_cast p (m 0) (m 1)
    rw [h0, Int.cast_zero] at hcast
    rw [← fin2_finsupp_eq] at hcast
    have hd_nz : (denom p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (denom_pos p))
    have hc_nz : p.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    exact mul_ne_zero hd_nz hc_nz hcast.symm
  dsimp [toCubicZ]
  have hm0 : m 0 ≤ 3 := by omega
  interval_cases h0 : m 0
  · have h1 : m 1 = 3 := by omega
    rw [h1] at hic_nz
    exact Or.inr (Or.inr (Or.inr hic_nz))
  · have h1 : m 1 = 2 := by omega
    rw [h1] at hic_nz
    exact Or.inr (Or.inr (Or.inl hic_nz))
  · have h1 : m 1 = 1 := by omega
    rw [h1] at hic_nz
    exact Or.inr (Or.inl hic_nz)
  · have h1 : m 1 = 0 := by omega
    rw [h1] at hic_nz
    exact Or.inl hic_nz

end ProofMO392283

theorem OMA.solution : type_of% @OMA.S_mo_392283.main := by
  intro p hp _ _
  obtain ⟨x1, y1, x2, y2, hne, heq⟩ :=
    ProofMO392283.cubic_collision (ProofMO392283.toCubicZ p) (ProofMO392283.toCubicZ_cubic_nz p hp)
  refine ⟨![x1, y1], ![x2, y2], ?_, ?_⟩
  · intro hvec
    have hx : x1 = x2 := congrFun hvec 0
    have hy : y1 = y2 := congrFun hvec 1
    rcases hne with h | h <;> contradiction
  · have hd_nz : (ProofMO392283.denom p : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (ne_of_gt (ProofMO392283.denom_pos p))
    have h1 := ProofMO392283.eval_toCubicZ p hp x1 y1
    have h2 := ProofMO392283.eval_toCubicZ p hp x2 y2
    have heqQ : ((ProofMO392283.toCubicZ p).eval x1 y1 : ℚ) =
        ((ProofMO392283.toCubicZ p).eval x2 y2 : ℚ) := by exact_mod_cast heq
    have hmul : (ProofMO392283.denom p : ℚ) * OMA.S_mo_392283.latticeValue p ![x1, y1] =
        (ProofMO392283.denom p : ℚ) * OMA.S_mo_392283.latticeValue p ![x2, y2] := by
      rw [h1, h2, heqQ]
    exact mul_left_cancel₀ hd_nz hmul
