import OMAReductions.R_OeisA160324_conjecture2_R1_H2_R1
import Mathlib

/-! Legendre three-squares theorem and Cauchy lemma, self-contained on Mathlib. Route: Nathanson, Additive Number Theory: The Classical Bases, chapter 1. -/

/-! ## A_Easy -/

namespace ThreeSquares

/-- Squares of integers are 0, 1 or 4 modulo 8. -/
theorem sq_mod_eight (x : ℤ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨
      x % 8 = 6 ∨ x % 8 = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

/-- The square of an integer is 0 mod 4 if the integer is even and 1 mod 4 otherwise. -/
theorem sq_mod_four (x : ℤ) : (x % 2 = 0 ∧ x ^ 2 % 4 = 0) ∨ (x % 2 = 1 ∧ x ^ 2 % 4 = 1) := by
  have h : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases h with h | h | h | h
  · left; refine ⟨by omega, ?_⟩; simp [pow_two, Int.mul_emod, h]
  · right; refine ⟨by omega, ?_⟩; simp [pow_two, Int.mul_emod, h]
  · left; refine ⟨by omega, ?_⟩; simp [pow_two, Int.mul_emod, h]
  · right; refine ⟨by omega, ?_⟩; simp [pow_two, Int.mul_emod, h]

/-- If a sum of three squares is divisible by 4 then all three numbers are even. -/
theorem even_of_sum_three_sq_mod_four (x y z : ℤ) (h : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0) :
    x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 := by
  rcases sq_mod_four x with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
  rcases sq_mod_four y with ⟨hy, hy'⟩ | ⟨hy, hy'⟩ <;>
  rcases sq_mod_four z with ⟨hz, hz'⟩ | ⟨hz, hz'⟩ <;>
  omega

theorem not_sum_three_sq_of_form (a b : ℕ) (x y z : ℤ) :
    x ^ 2 + y ^ 2 + z ^ 2 ≠ ((4 ^ a * (8 * b + 7) : ℕ) : ℤ) := by
  induction a generalizing x y z with
  | zero =>
    intro h
    push_cast at h
    rcases sq_mod_eight x with hx | hx | hx <;>
    rcases sq_mod_eight y with hy | hy | hy <;>
    rcases sq_mod_eight z with hz | hz | hz <;>
    omega
  | succ a ih =>
    intro h
    have h4 : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0 := by
      rw [h]; push_cast
      have : (4 : ℤ) ^ (a + 1) * (8 * (b : ℤ) + 7) = 4 * (4 ^ a * (8 * (b : ℤ) + 7)) := by ring
      rw [this]; omega
    obtain ⟨hx, hy, hz⟩ := even_of_sum_three_sq_mod_four x y z h4
    obtain ⟨x', rfl⟩ : ∃ x', x = 2 * x' := ⟨x / 2, by omega⟩
    obtain ⟨y', rfl⟩ : ∃ y', y = 2 * y' := ⟨y / 2, by omega⟩
    obtain ⟨z', rfl⟩ : ∃ z', z = 2 * z' := ⟨z / 2, by omega⟩
    apply ih x' y' z'
    push_cast at h ⊢
    have h' : (4 : ℤ) ^ (a + 1) * (8 * (b : ℤ) + 7) = 4 * (4 ^ a * (8 * (b : ℤ) + 7)) := by ring
    rw [h'] at h
    linarith

theorem sum_three_sq_four_mul (n : ℤ) :
    (∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n) → ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 4 * n := by
  rintro ⟨x, y, z, rfl⟩
  exact ⟨2 * x, 2 * y, 2 * z, by ring⟩

theorem exists_form_decomp (n : ℕ) (hn : 0 < n) : ∃ a m : ℕ, n = 4 ^ a * m ∧ m % 4 ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n % 4 = 0
    · obtain ⟨a, m, hk, hm⟩ := ih (n / 4) (by omega) (by omega)
      refine ⟨a + 1, m, ?_, hm⟩
      rw [pow_succ, mul_assoc, mul_comm 4 m, ← mul_assoc, ← hk]
      omega
    · exact ⟨0, n, by simp, h⟩

end ThreeSquares

/-! ## B_Forms -/

namespace ThreeSquares

/-! Binary forms A x^2 + 2 B x y + C y^2 and their reduction. -/

/-- Value of the binary form at the vector (p, r). -/
def bA (A B C p r : ℤ) : ℤ := A * p ^ 2 + 2 * B * p * r + C * r ^ 2

/-- Value of the associated bilinear form at (p, r), (q, s). -/
def bB (A B C p q r s : ℤ) : ℤ := A * p * q + B * (p * s + q * r) + C * r * s

/-- The binary form is properly equivalent to a reduced one. -/
def BRed (A B C : ℤ) : Prop :=
  ∃ p q r s : ℤ, p * s - q * r = 1 ∧ 0 < bA A B C p r ∧
    -bA A B C p r ≤ 2 * bB A B C p q r s ∧
    2 * bB A B C p q r s ≤ bA A B C p r ∧ bA A B C p r ≤ bA A B C q s

theorem BRed.comp {A B C A1 B1 C1 : ℤ} (p q r s : ℤ) (hd : p * s - q * r = 1)
    (hA : A1 = bA A B C p r) (hB : B1 = bB A B C p q r s) (hC : C1 = bA A B C q s)
    (h : BRed A1 B1 C1) : BRed A B C := by
  obtain ⟨p', q', r', s', hd', h1, h2, h3, h4⟩ := h
  have eA : bA A1 B1 C1 p' r' = bA A B C (p * p' + q * r') (r * p' + s * r') := by
    subst hA hB hC; simp only [bA, bB]; ring
  have eB : bB A1 B1 C1 p' q' r' s' =
      bB A B C (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s') := by
    subst hA hB hC; simp only [bA, bB]; ring
  have eC : bA A1 B1 C1 q' s' = bA A B C (p * q' + q * s') (r * q' + s * s') := by
    subst hA hB hC; simp only [bA, bB]; ring
  rw [eA] at h1 h2 h3 h4
  rw [eB] at h2 h3
  rw [eC] at h4
  refine ⟨_, _, _, _, ?_, h1, h2, h3, h4⟩
  have e : (p * p' + q * r') * (r * q' + s * s') - (p * q' + q * s') * (r * p' + s * r') =
      (p * s - q * r) * (p' * s' - q' * r') := by ring
  rw [e, hd, hd']; norm_num

theorem round_exists (a b : ℤ) (ha : 0 < a) :
    ∃ k : ℤ, -a ≤ 2 * (b - k * a) ∧ 2 * (b - k * a) ≤ a := by
  have h1 := Int.emod_nonneg (2 * b + a) (show 2 * a ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos (2 * b + a) (show 0 < 2 * a by omega)
  have h3 := Int.emod_add_mul_ediv (2 * b + a) (2 * a)
  refine ⟨(2 * b + a) / (2 * a), ?_, ?_⟩ <;> nlinarith

theorem bred : ∀ n : ℕ, ∀ A B C : ℤ, A ≤ n → 0 < A → 0 < A * C - B ^ 2 → BRed A B C := by
  intro n
  induction n with
  | zero =>
    intro A B C h1 h2 _
    exfalso
    omega
  | succ n ih =>
    intro A B C hn hA hD
    obtain ⟨k, hk1, hk2⟩ := round_exists A B hA
    obtain ⟨B1, hB1⟩ : ∃ B1, B1 = B - k * A := ⟨_, rfl⟩
    obtain ⟨C1, hC1⟩ : ∃ C1, C1 = A * k ^ 2 - 2 * B * k + C := ⟨_, rfl⟩
    rw [← hB1] at hk1 hk2
    have hD1 : A * C1 - B1 ^ 2 = A * C - B ^ 2 := by subst hB1 hC1; ring
    have key : BRed A B1 C1 := by
      by_cases hc : A ≤ C1
      · have e1 : bA A B1 C1 1 0 = A := by simp only [bA]; ring
        have e2 : bB A B1 C1 1 0 0 1 = B1 := by simp only [bB]; ring
        have e3 : bA A B1 C1 0 1 = C1 := by simp only [bA]; ring
        refine ⟨1, 0, 0, 1, by ring, ?_, ?_, ?_, ?_⟩
        · rw [e1]; exact hA
        · rw [e1, e2]; exact hk1
        · rw [e1, e2]; exact hk2
        · rw [e1, e3]; exact hc
      · have hC1pos : 0 < C1 := by
          by_contra h
          rw [not_lt] at h
          nlinarith [mul_nonneg hA.le (neg_nonneg.mpr h), sq_nonneg B1]
        have hD2 : 0 < C1 * A - (-B1) ^ 2 := by
          have : C1 * A - (-B1) ^ 2 = A * C1 - B1 ^ 2 := by ring
          linarith
        have h := ih C1 (-B1) A (by omega) hC1pos hD2
        refine BRed.comp 0 (-1) 1 0 (by ring) ?_ ?_ ?_ h <;> simp only [bA, bB] <;> ring
    refine BRed.comp 1 (-k) 0 1 (by ring) ?_ ?_ ?_ key
    · simp only [bA]; ring
    · simp only [bB]; rw [hB1]; ring
    · simp only [bA]; rw [hC1]; ring

theorem bred_bound (A B C : ℤ) (hA : 0 < A) (hD : 0 < A * C - B ^ 2) :
    ∃ p q r s : ℤ, p * s - q * r = 1 ∧ 0 < bA A B C p r ∧
      -bA A B C p r ≤ 2 * bB A B C p q r s ∧
      2 * bB A B C p q r s ≤ bA A B C p r ∧ bA A B C p r ≤ bA A B C q s ∧
      bA A B C p r * bA A B C q s - bB A B C p q r s ^ 2 = A * C - B ^ 2 := by
  obtain ⟨p, q, r, s, hd, h⟩ := bred A.toNat A B C (Int.self_le_toNat A) hA hD
  refine ⟨p, q, r, s, hd, h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
  have e : bA A B C p r * bA A B C q s - bB A B C p q r s ^ 2 =
      (A * C - B ^ 2) * (p * s - q * r) ^ 2 := by simp only [bA, bB]; ring
  rw [e, hd]; ring

theorem aux_bound (A B C D : ℤ) (hpos : 0 < A) (hl : -A ≤ 2 * B) (hu : 2 * B ≤ A)
    (hle : A ≤ C) (hdet : A * C - B ^ 2 = D) : 3 * A ^ 2 ≤ 4 * D := by
  have e1 : 0 ≤ (A - 2 * B) * (A + 2 * B) := mul_nonneg (by linarith) (by linarith)
  have e2 : A * A ≤ A * C := mul_le_mul_of_nonneg_left hle hpos.le
  nlinarith

theorem aux_lt (a c22 c12 A : ℤ) (hge : 2 ≤ a) (hminor : c22 * a - c12 ^ 2 = A)
    (hpos : 0 < A) (hbound : 3 * A ^ 2 ≤ 4 * a) (hk1 : -a ≤ 2 * c12) (hk2 : 2 * c12 ≤ a) :
    c22 < a := by
  by_contra h
  rw [not_lt] at h
  have e0 : 0 ≤ (a - 2 * c12) * (a + 2 * c12) := mul_nonneg (by linarith) (by linarith)
  have e2 : a * a ≤ c22 * a := mul_le_mul_of_nonneg_right h (by linarith)
  have e3 : 3 * a ^ 2 ≤ 4 * A := by nlinarith
  have e3' : 2 * a ≤ a * a := mul_le_mul_of_nonneg_right hge (by linarith)
  have e4 : 3 * a ≤ 2 * A := by nlinarith
  have e5 : 9 * A ^ 2 ≤ 8 * A := by linarith
  have e6 : 0 ≤ A * (A - 1) := mul_nonneg hpos.le (by linarith)
  nlinarith

/-! Ternary forms. -/

/-- The ternary quadratic form with the given coefficients. -/
def tform (a11 a12 a13 a22 a23 a33 x y z : ℤ) : ℤ :=
  a11 * x ^ 2 + a22 * y ^ 2 + a33 * z ^ 2 + 2 * a12 * x * y + 2 * a13 * x * z + 2 * a23 * y * z

/-- The function is a sum of three squares of integer linear forms. -/
def IsSum3 (f : ℤ → ℤ → ℤ → ℤ) : Prop :=
  ∃ u11 u12 u13 u21 u22 u23 u31 u32 u33 : ℤ, ∀ x y z : ℤ,
    f x y z = (u11 * x + u12 * y + u13 * z) ^ 2 + (u21 * x + u22 * y + u23 * z) ^ 2 +
      (u31 * x + u32 * y + u33 * z) ^ 2

theorem IsSum3.of_subst {f g : ℤ → ℤ → ℤ → ℤ} (m11 m12 m13 m21 m22 m23 m31 m32 m33 : ℤ)
    (hfg : ∀ x y z : ℤ, f x y z = g (m11 * x + m12 * y + m13 * z)
      (m21 * x + m22 * y + m23 * z) (m31 * x + m32 * y + m33 * z))
    (h : IsSum3 g) : IsSum3 f := by
  obtain ⟨u11, u12, u13, u21, u22, u23, u31, u32, u33, hu⟩ := h
  refine ⟨u11 * m11 + u12 * m21 + u13 * m31, u11 * m12 + u12 * m22 + u13 * m32,
    u11 * m13 + u12 * m23 + u13 * m33, u21 * m11 + u22 * m21 + u23 * m31,
    u21 * m12 + u22 * m22 + u23 * m32, u21 * m13 + u22 * m23 + u23 * m33,
    u31 * m11 + u32 * m21 + u33 * m31, u31 * m12 + u32 * m22 + u33 * m32,
    u31 * m13 + u32 * m23 + u33 * m33, ?_⟩
  intro x y z
  rw [hfg, hu]
  ring

/-- The case of leading coefficient one. -/
theorem tern_one (a12 a13 a22 a23 a33 : ℤ) (h2 : 0 < a22 - a12 ^ 2)
    (h3 : a22 * a33 + 2 * a12 * a13 * a23 - a23 ^ 2 - a22 * a13 ^ 2 - a33 * a12 ^ 2 = 1) :
    IsSum3 (tform 1 a12 a13 a22 a23 a33) := by
  have hD : (a22 - a12 ^ 2) * (a33 - a13 ^ 2) - (a23 - a12 * a13) ^ 2 = 1 := by
    linear_combination h3
  obtain ⟨p, q, r, s, hd, hpos, hl, hu, hle, hdet⟩ :=
    bred_bound (a22 - a12 ^ 2) (a23 - a12 * a13) (a33 - a13 ^ 2) h2 (by rw [hD]; norm_num)
  rw [hD] at hdet
  obtain ⟨A', hA'⟩ : ∃ A', A' = bA (a22 - a12 ^ 2) (a23 - a12 * a13) (a33 - a13 ^ 2) p r :=
    ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ :
      ∃ B', B' = bB (a22 - a12 ^ 2) (a23 - a12 * a13) (a33 - a13 ^ 2) p q r s := ⟨_, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C', C' = bA (a22 - a12 ^ 2) (a23 - a12 * a13) (a33 - a13 ^ 2) q s :=
    ⟨_, rfl⟩
  rw [← hA'] at hpos hl hu hdet hle
  rw [← hB'] at hl hu hdet
  rw [← hC'] at hle hdet
  have hA1 : A' = 1 := by nlinarith
  subst hA1
  have hB0 : B' = 0 := by omega
  subst hB0
  have hC1 : C' = 1 := by linarith
  subst hC1
  simp only [bA, bB] at hA' hB' hC'
  refine ⟨1, a12, a13, 0, s, -q, 0, -r, p, ?_⟩
  intro x y z
  simp only [tform]
  linear_combination
    (-((a22 - a12 ^ 2) * y ^ 2 + 2 * (a23 - a12 * a13) * y * z + (a33 - a13 ^ 2) * z ^ 2) *
      (p * s - q * r + 1)) * hd - (s * y - q * z) ^ 2 * hA' -
      2 * (s * y - q * z) * (-r * y + p * z) * hB' - (-r * y + p * z) ^ 2 * hC'

theorem tern : ∀ n : ℕ, ∀ a11 a12 a13 a22 a23 a33 : ℤ, a11 ≤ n → 0 < a11 →
    0 < a11 * a22 - a12 ^ 2 →
    a11 * a22 * a33 + 2 * a12 * a13 * a23 - a11 * a23 ^ 2 - a22 * a13 ^ 2 - a33 * a12 ^ 2 = 1 →
    IsSum3 (tform a11 a12 a13 a22 a23 a33) := by
  intro n
  induction n with
  | zero =>
    intro a11 a12 a13 a22 a23 a33 h0 h1 _ _
    exfalso
    omega
  | succ n ih =>
    intro a11 a12 a13 a22 a23 a33 hn h1 h2 h3
    by_cases hone : a11 = 1
    · subst hone
      exact tern_one a12 a13 a22 a23 a33 (by linarith) (by linarith)
    have hge : 2 ≤ a11 := by omega
    have hD : (a11 * a22 - a12 ^ 2) * (a11 * a33 - a13 ^ 2) - (a11 * a23 - a12 * a13) ^ 2 =
        a11 := by linear_combination a11 * h3
    obtain ⟨p, q, r, s, hd, hpos, hl, hu, hle, hdet⟩ :=
      bred_bound (a11 * a22 - a12 ^ 2) (a11 * a23 - a12 * a13) (a11 * a33 - a13 ^ 2) h2
        (by rw [hD]; exact h1)
    rw [hD] at hdet
    obtain ⟨b12, hb12⟩ : ∃ b12, b12 = a12 * p + a13 * r := ⟨_, rfl⟩
    obtain ⟨b13, hb13⟩ : ∃ b13, b13 = a12 * q + a13 * s := ⟨_, rfl⟩
    obtain ⟨b22, hb22⟩ : ∃ b22, b22 = a22 * p ^ 2 + 2 * a23 * p * r + a33 * r ^ 2 := ⟨_, rfl⟩
    obtain ⟨b23, hb23⟩ : ∃ b23, b23 = a22 * p * q + a23 * (p * s + q * r) + a33 * r * s :=
      ⟨_, rfl⟩
    obtain ⟨b33, hb33⟩ : ∃ b33, b33 = a22 * q ^ 2 + 2 * a23 * q * s + a33 * s ^ 2 := ⟨_, rfl⟩
    obtain ⟨k, hk1, hk2⟩ := round_exists a11 b12 h1
    obtain ⟨c12, hc12⟩ : ∃ c12, c12 = b12 - k * a11 := ⟨_, rfl⟩
    obtain ⟨c22, hc22⟩ : ∃ c22, c22 = b22 - 2 * k * b12 + k ^ 2 * a11 := ⟨_, rfl⟩
    obtain ⟨c23, hc23⟩ : ∃ c23, c23 = b23 - k * b13 := ⟨_, rfl⟩
    rw [← hc12] at hk1 hk2
    obtain ⟨A', hA'⟩ :
        ∃ A', A' = bA (a11 * a22 - a12 ^ 2) (a11 * a23 - a12 * a13) (a11 * a33 - a13 ^ 2) p r :=
      ⟨_, rfl⟩
    obtain ⟨B', hB'⟩ : ∃ B', B' =
        bB (a11 * a22 - a12 ^ 2) (a11 * a23 - a12 * a13) (a11 * a33 - a13 ^ 2) p q r s :=
      ⟨_, rfl⟩
    obtain ⟨C', hC'⟩ :
        ∃ C', C' = bA (a11 * a22 - a12 ^ 2) (a11 * a23 - a12 * a13) (a11 * a33 - a13 ^ 2) q s :=
      ⟨_, rfl⟩
    rw [← hA'] at hpos hl hu hdet hle
    rw [← hB'] at hl hu hdet
    rw [← hC'] at hle hdet
    have hbound : 3 * A' ^ 2 ≤ 4 * a11 := aux_bound A' B' C' a11 hpos hl hu hle hdet
    have hminor : c22 * a11 - c12 ^ 2 = A' := by
      rw [hA']; subst hc12 hc22 hb12 hb22; simp only [bA]; ring
    have hc22pos : 0 < c22 := by
      by_contra h
      rw [not_lt] at h
      have e1 := mul_nonneg h1.le (neg_nonneg.mpr h)
      have e2 := sq_nonneg c12
      clear ih hdet hD hb12 hb13 hb22 hb23 hb33 hc12 hc22 hc23 hA' hB' hC'
      nlinarith
    have hlt : c22 < a11 := aux_lt a11 c22 c12 A' hge hminor hpos hbound hk1 hk2
    have hdet3 : c22 * a11 * b33 + 2 * c12 * c23 * b13 - c22 * b13 ^ 2 - a11 * c23 ^ 2 -
        b33 * c12 ^ 2 = 1 := by
      have e : c22 * a11 * b33 + 2 * c12 * c23 * b13 - c22 * b13 ^ 2 - a11 * c23 ^ 2 -
          b33 * c12 ^ 2 =
          (a11 * a22 * a33 + 2 * a12 * a13 * a23 - a11 * a23 ^ 2 - a22 * a13 ^ 2 -
            a33 * a12 ^ 2) * (p * s - q * r) ^ 2 := by
        subst hc12 hc22 hc23 hb12 hb13 hb22 hb23 hb33; ring
      rw [e, h3, hd]; norm_num
    have hIH := ih c22 c12 c23 a11 b13 b33 (by omega) hc22pos (by rw [hminor]; exact hpos) hdet3
    refine IsSum3.of_subst 0 s (-q) 1 (k * s) (-(k * q)) 0 (-r) p ?_ hIH
    intro x y z
    subst hc12 hc22 hc23 hb12 hb13 hb22 hb23 hb33
    simp only [tform]
    linear_combination
      (-(a22 * y ^ 2 + a33 * z ^ 2 + 2 * a23 * y * z) * (p * s - q * r + 1) -
        2 * a12 * x * y - 2 * a13 * x * z) * hd

theorem forms_main (a11 a12 a13 a22 a23 a33 : ℤ) (h1 : 0 < a11) (h2 : 0 < a11 * a22 - a12 ^ 2)
    (h3 : a11 * a22 * a33 + 2 * a12 * a13 * a23 - a11 * a23 ^ 2 - a22 * a13 ^ 2 - a33 * a12 ^ 2 = 1) :
    ∃ u11 u12 u13 u21 u22 u23 u31 u32 u33 : ℤ, ∀ x y z : ℤ,
      a11 * x ^ 2 + a22 * y ^ 2 + a33 * z ^ 2 + 2 * a12 * x * y + 2 * a13 * x * z + 2 * a23 * y * z =
        (u11 * x + u12 * y + u13 * z) ^ 2 + (u21 * x + u22 * y + u23 * z) ^ 2 + (u31 * x + u32 * y + u33 * z) ^ 2 :=
  tern a11.toNat a11 a12 a13 a22 a23 a33 (Int.self_le_toNat a11) h1 h2 h3

end ThreeSquares

/-! ## C_Arith -/

namespace ThreeSquares

open scoped NumberTheorySymbols

/-- If the Jacobi symbol of `-d` at a prime `p` is one, then `-d` is a square mod `p`. -/
lemma exists_sq_of_jacobi (p d : ℕ) (hp : p.Prime) (h : J(-(d : ℤ) | p) = 1) :
    ∃ b : ℤ, (p : ℤ) ∣ b ^ 2 + d := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  have h0 : ((-(d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff p _).mpr h0] at h
    exact absurd h (by norm_num)
  obtain ⟨x, hx⟩ := (legendreSym.eq_one_iff p h0).mp h
  refine ⟨(x.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast at hx ⊢
  rw [ZMod.natCast_zmod_val]
  linear_combination -hx

/-- Splitting off the sign. -/
lemma jacobi_neg (p d : ℕ) : J(-(d : ℤ) | p) = J(-1 | p) * J((d : ℤ) | p) := by
  rw [← jacobiSym.mul_left, neg_one_mul]

/-- First reciprocity computation: `p` and `d` both `1` mod `4`, `p = -1` mod `d`. -/
lemma jacobi_case_one (p d : ℕ) (hp4 : p % 4 = 1) (hd4 : d % 4 = 1) (hdvd : d ∣ p + 1) :
    J(-(d : ℤ) | p) = 1 := by
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  have h1 : J(-1 | p) = 1 := by
    rw [jacobiSym.at_neg_one hpodd, ZMod.χ₄_nat_one_mod_four hp4]
  have h2 : J((d : ℤ) | p) = J((p : ℤ) | d) :=
    jacobiSym.quadratic_reciprocity_one_mod_four hd4 hpodd
  have h3 : J((p : ℤ) | d) = J(-1 | d) := by
    apply jacobiSym.mod_left'
    refine Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd ?_)
    have e : (p : ℤ) - -1 = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e]
    exact Int.natCast_dvd_natCast.mpr hdvd
  have h4 : J(-1 | d) = 1 := by
    rw [jacobiSym.at_neg_one hdodd, ZMod.χ₄_nat_one_mod_four hd4]
  rw [jacobi_neg, h1, h2, h3, h4]; rfl

/-- If `2 p = -1` mod `d` and `d` is `1` or `3` mod `8`, then `p` has Jacobi symbol one at `d`. -/
lemma jacobi_p_d (p d : ℕ) (hd8 : d % 8 = 1 ∨ d % 8 = 3) (hdvd : d ∣ 2 * p + 1) :
    J((p : ℤ) | d) = 1 := by
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  have h3 : J(2 * (p : ℤ) | d) = J(-1 | d) := by
    apply jacobiSym.mod_left'
    refine Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd ?_)
    have e : 2 * (p : ℤ) - -1 = ((2 * p + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e]
    exact Int.natCast_dvd_natCast.mpr hdvd
  rw [jacobiSym.mul_left, jacobiSym.at_two hdodd, jacobiSym.at_neg_one hdodd,
    ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four] at h3
  rcases hd8 with h | h
  · have h2 : d % 2 = 1 := by omega
    have h4 : d % 4 = 1 := by omega
    simpa [h, h2, h4] using h3
  · have h2 : d % 2 = 1 := by omega
    have h4 : d % 4 = 3 := by omega
    simpa [h, h2, h4] using h3

/-- Second reciprocity computation. -/
lemma jacobi_case_two (p d : ℕ)
    (hres : (p % 4 = 1 ∧ (d % 8 = 1 ∨ d % 8 = 3)) ∨ (p % 4 = 3 ∧ d % 8 = 3))
    (hdvd : d ∣ 2 * p + 1) : J(-(d : ℤ) | p) = 1 := by
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hdodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hpd : J((p : ℤ) | d) = 1 := jacobi_p_d p d (by omega) hdvd
  rw [jacobi_neg, jacobiSym.at_neg_one hpodd]
  rcases hres with ⟨hp4, -⟩ | ⟨hp4, hd8⟩
  · rw [ZMod.χ₄_nat_one_mod_four hp4,
      ← jacobiSym.quadratic_reciprocity_one_mod_four hp4 hdodd, hpd]; rfl
  · have hd4 : d % 4 = 3 := by omega
    rw [ZMod.χ₄_nat_three_mod_four hp4,
      jacobiSym.quadratic_reciprocity_three_mod_four hd4 hp4, hpd]; rfl

/-- Dirichlet in the shape we need. -/
lemma exists_prime_in_progression (N r : ℕ) (hN : 0 < N) (hr : r.Coprime (4 * N))
    (hlt : r < 4 * N) : ∃ p j : ℕ, p.Prime ∧ p = 4 * N * j + r := by
  obtain ⟨p, -, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 0 (q := 4 * N) (a := r) (by omega) hr
  refine ⟨p, p / (4 * N), hp, ?_⟩
  have h1 := Nat.div_add_mod p (4 * N)
  have h2 : p % (4 * N) = r := by
    have : p % (4 * N) = r % (4 * N) := hmod
    rw [this, Nat.mod_eq_of_lt hlt]
  rw [h2] at h1
  exact h1.symm

/-- Coprimality from a linear relation. -/
lemma coprime_four_mul (N r a b : ℕ) (hodd : r % 2 = 1) (h : a * r + 1 = b * N) :
    r.Coprime (4 * N) := by
  apply Nat.Coprime.mul_right
  · have : Nat.Coprime r (2 ^ 2) :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hodd))
    simpa using this
  · have hg1 : Nat.gcd r N ∣ a * r := Dvd.dvd.mul_left (Nat.gcd_dvd_left r N) a
    have hg2 : Nat.gcd r N ∣ a * r + 1 := by
      rw [h]; exact Dvd.dvd.mul_left (Nat.gcd_dvd_right r N) b
    exact Nat.dvd_one.mp ((Nat.dvd_add_right hg1).mp hg2)

/-- Lifting a root mod an odd `p` to a root mod `2 p`. -/
lemma lift_two (p d : ℕ) (hp2 : p % 2 = 1) (hd : d % 2 = 1) (b0 : ℤ)
    (h : (p : ℤ) ∣ b0 ^ 2 + d) : ∃ b : ℤ, (2 * p : ℤ) ∣ b ^ 2 + d := by
  obtain ⟨b, hb2, hb⟩ : ∃ b : ℤ, b % 2 = 1 ∧ (p : ℤ) ∣ b ^ 2 + d := by
    rcases Int.emod_two_eq_zero_or_one b0 with h0 | h1
    · refine ⟨b0 + p, by omega, ?_⟩
      have : (b0 + p) ^ 2 + (d : ℤ) = (b0 ^ 2 + d) + p * (2 * b0 + p) := by ring
      rw [this]
      exact dvd_add h (dvd_mul_right _ _)
    · exact ⟨b0, h1, h⟩
  refine ⟨b, ?_⟩
  have hcop : IsCoprime (2 : ℤ) (p : ℤ) := by
    have : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hp2)
    exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
  apply hcop.mul_dvd _ hb
  obtain ⟨k, hk⟩ : ∃ k : ℤ, b = 2 * k + 1 := ⟨b / 2, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (d : ℤ) = 2 * m + 1 := ⟨(d : ℤ) / 2, by omega⟩
  exact ⟨2 * k ^ 2 + 2 * k + m + 1, by rw [hk, hm]; ring⟩

/-- The odd case, uniformly in the auxiliary data. -/
lemma arith_odd (N r c : ℕ) (hN : 2 ≤ N) (hrel : 2 * r + 1 = c * N) (hc : c % 2 = 1)
    (hres : (r % 4 = 1 ∧ (c % 8 = 1 ∨ c % 8 = 3)) ∨ (r % 4 = 3 ∧ c % 8 = 3))
    (hlt : r < 4 * N) :
    ∃ d b : ℤ, 0 < d ∧ 0 < d * N - 1 ∧ (d * N - 1) ∣ b ^ 2 + d := by
  have hcop : r.Coprime (4 * N) := coprime_four_mul N r 2 c (by omega) hrel
  obtain ⟨p, j, hp, hpeq⟩ := exists_prime_in_progression N r (by omega) hcop hlt
  have hp4 : p % 4 = r % 4 := by
    rw [hpeq, mul_assoc, Nat.mul_add_mod]
  have hdN : (8 * j + c) * N = 2 * p + 1 := by
    rw [hpeq]; linear_combination -hrel
  have hd8 : (8 * j + c) % 8 = c % 8 := by rw [Nat.mul_add_mod]
  have hjac : J(-((8 * j + c : ℕ) : ℤ) | p) = 1 :=
    jacobi_case_two p (8 * j + c) (by omega) ⟨N, hdN.symm⟩
  obtain ⟨b0, hb0⟩ := exists_sq_of_jacobi p (8 * j + c) hp hjac
  obtain ⟨b, hb⟩ := lift_two p (8 * j + c) (by omega) (by omega) b0 hb0
  have hdN' : (((8 * j + c : ℕ) : ℤ)) * N - 1 = 2 * p := by
    have : (((8 * j + c) * N : ℕ) : ℤ) = ((2 * p + 1 : ℕ) : ℤ) := by rw [hdN]
    push_cast at this ⊢
    linarith
  refine ⟨((8 * j + c : ℕ) : ℤ), b, ?_, ?_, ?_⟩
  · have : 0 < 8 * j + c := by omega
    exact_mod_cast this
  · rw [hdN']
    have := hp.pos
    positivity
  · rw [hdN']; exact hb

/-- The case `N = 2` mod `4`. -/
lemma arith_even (N : ℕ) (hN : N % 4 = 2) :
    ∃ d b : ℤ, 0 < d ∧ 0 < d * N - 1 ∧ (d * N - 1) ∣ b ^ 2 + d := by
  obtain ⟨r, rfl⟩ : ∃ r, N = r + 1 := ⟨N - 1, by omega⟩
  have hcop : r.Coprime (4 * (r + 1)) := coprime_four_mul (r + 1) r 1 1 (by omega) (by ring)
  obtain ⟨p, j, hp, hpeq⟩ := exists_prime_in_progression (r + 1) r (by omega) hcop (by omega)
  have hp4 : p % 4 = 1 := by
    rw [hpeq, mul_assoc, Nat.mul_add_mod]; omega
  have hdN : (4 * j + 1) * (r + 1) = p + 1 := by
    rw [hpeq]; ring
  have hjac : J(-((4 * j + 1 : ℕ) : ℤ) | p) = 1 :=
    jacobi_case_one p (4 * j + 1) hp4 (by omega) ⟨r + 1, hdN.symm⟩
  obtain ⟨b, hb⟩ := exists_sq_of_jacobi p (4 * j + 1) hp hjac
  have hdN' : (((4 * j + 1 : ℕ) : ℤ)) * ((r + 1 : ℕ) : ℤ) - 1 = p := by
    have : (((4 * j + 1) * (r + 1) : ℕ) : ℤ) = ((p + 1 : ℕ) : ℤ) := by rw [hdN]
    push_cast at this ⊢
    linarith
  refine ⟨((4 * j + 1 : ℕ) : ℤ), b, ?_, ?_, ?_⟩
  · have : 0 < 4 * j + 1 := by omega
    exact_mod_cast this
  · rw [hdN']
    exact_mod_cast hp.pos
  · rw [hdN']; exact hb

theorem arith_main (n : ℤ) (hn : 2 ≤ n) (h4 : n % 4 ≠ 0) (h8 : n % 8 ≠ 7) :
    ∃ d b : ℤ, 0 < d ∧ 0 < d * n - 1 ∧ (d * n - 1) ∣ b ^ 2 + d := by
  lift n to ℕ using by omega
  have hN : 2 ≤ n := by exact_mod_cast hn
  have hcases : n % 4 = 2 ∨ n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 := by omega
  rcases hcases with h | h | h | h
  · exact arith_even n h
  · exact arith_odd n ((3 * n - 1) / 2) 3 hN (by omega) (by omega) (by omega) (by omega)
  · exact arith_odd n ((n - 1) / 2) 1 hN (by omega) (by omega) (by omega) (by omega)
  · exact arith_odd n ((3 * n - 1) / 2) 3 hN (by omega) (by omega) (by omega) (by omega)

end ThreeSquares

/-! ## D_Main -/

namespace ThreeSquares


/-- A nonnegative integer that is not divisible by 4 and not 7 mod 8 is a sum of three squares. -/
theorem sum_three_sq_of_good (n : ℤ) (hn : 0 ≤ n) (h4 : n % 4 ≠ 0) (h8 : n % 8 ≠ 7) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  rcases lt_or_ge n 2 with hlt | hge
  · have h1 : n = 1 := by omega
    exact ⟨1, 0, 0, by rw [h1]; norm_num⟩
  · obtain ⟨d, b, hd, hdn, a11, ha11⟩ := arith_main n hge h4 h8
    have hpos : 0 < a11 := by
      have hb : 0 < b ^ 2 + d := by positivity
      rw [ha11] at hb
      by_contra hneg
      have : (d * n - 1) * a11 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hdn.le (not_lt.mp hneg)
      linarith
    obtain ⟨u11, u12, u13, u21, u22, u23, u31, u32, u33, hU⟩ :=
      forms_main a11 b 1 (d * n - 1) 0 n hpos
        (by
          have e : a11 * (d * n - 1) - b ^ 2 = d := by linear_combination (-1 : ℤ) * ha11
          rw [e]; exact hd) (by linear_combination (-n) * ha11)
    refine ⟨u13, u23, u33, ?_⟩
    have := hU 0 0 1
    linear_combination -this

/-- Legendre's three-squares theorem. -/
theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (n : ℤ)) ↔ ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
  constructor
  · rintro ⟨x, y, z, h⟩ ⟨a, b, rfl⟩
    exact not_sum_three_sq_of_form a b x y z h
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, 0, 0, by norm_num⟩
    · obtain ⟨a, m, rfl, hm4⟩ := exists_form_decomp n hn
      have hm8 : m % 8 ≠ 7 := by
        intro h7
        exact h ⟨a, m / 8, by congr 1; omega⟩
      have hm : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (m : ℤ) :=
        sum_three_sq_of_good m (by positivity) (by omega) (by omega)
      clear h hn
      induction a with
      | zero => simpa using hm
      | succ a ih =>
        have := sum_three_sq_four_mul _ ih
        have e : ((4 ^ (a + 1) * m : ℕ) : ℤ) = 4 * ((4 ^ a * m : ℕ) : ℤ) := by
          push_cast; ring
        rw [e]
        exact this

/-- Legendre's three-squares theorem, with natural number summands. -/
theorem sum_three_squares_nat_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
  rw [← sum_three_squares_iff]
  constructor
  · rintro ⟨x, y, z, h⟩
    exact ⟨x, y, z, by exact_mod_cast h⟩
  · rintro ⟨x, y, z, h⟩
    refine ⟨x.natAbs, y.natAbs, z.natAbs, ?_⟩
    zify
    simpa [sq_abs] using h

/-- Squares modulo 8, together with the parity information. -/
theorem sq_mod_eight_parity (x : ℤ) :
    (x ^ 2 % 8 = 0 ∧ x % 2 = 0) ∨ (x ^ 2 % 8 = 1 ∧ x % 2 = 1) ∨ (x ^ 2 % 8 = 4 ∧ x % 2 = 0) := by
  have h : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨
      x % 8 = 6 ∨ x % 8 = 7 := by omega
  have h2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> rcases h2 with h2 | h2 <;>
    first
      | omega
      | (simp [pow_two, Int.mul_emod, h, h2])

/-- A natural number that is 3 mod 8 is a sum of three odd squares. -/
theorem sum_three_odd_squares (n : ℕ) (h : n % 8 = 3) :
    ∃ x y z : ℕ, Odd x ∧ Odd y ∧ Odd z ∧ x ^ 2 + y ^ 2 + z ^ 2 = n := by
  obtain ⟨x, y, z, hxyz⟩ := sum_three_sq_of_good (n : ℤ) (by positivity) (by omega) (by omega)
  have key : x % 2 = 1 ∧ y % 2 = 1 ∧ z % 2 = 1 := by
    rcases sq_mod_eight_parity x with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
    rcases sq_mod_eight_parity y with ⟨hy, hy'⟩ | ⟨hy, hy'⟩ | ⟨hy, hy'⟩ <;>
    rcases sq_mod_eight_parity z with ⟨hz, hz'⟩ | ⟨hz, hz'⟩ | ⟨hz, hz'⟩ <;>
    omega
  obtain ⟨hx, hy, hz⟩ := key
  refine ⟨x.natAbs, y.natAbs, z.natAbs, ?_, ?_, ?_, ?_⟩
  · rw [Int.natAbs_odd, Int.odd_iff]; exact hx
  · rw [Int.natAbs_odd, Int.odd_iff]; exact hy
  · rw [Int.natAbs_odd, Int.odd_iff]; exact hz
  · zify
    simpa [sq_abs] using hxyz

/-- Cauchy's lemma. -/
theorem cauchy_lemma (a b : ℕ) (ha : Odd a) (hb : Odd b) (h1 : b ^ 2 < 4 * a)
    (h2 : 3 * a < b ^ 2 + 2 * b + 4) :
    ∃ s t u v : ℕ, a = s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 ∧ b = s + t + u + v := by
  have ha' : a % 2 = 1 := Nat.odd_iff.mp ha
  have hb' : b % 2 = 1 := Nat.odd_iff.mp hb
  have hb8 : b ^ 2 % 8 = 1 := by
    have h : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by omega
    rcases h with h | h | h | h <;> simp [pow_two, Nat.mul_mod, h]
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := sum_three_odd_squares (4 * a - b ^ 2) (by omega)
  have hx' : x % 2 = 1 := Nat.odd_iff.mp hx
  have hy' : y % 2 = 1 := Nat.odd_iff.mp hy
  have hz' : z % 2 = 1 := Nat.odd_iff.mp hz
  -- the identity over the integers
  have hI : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = 4 * (a : ℤ) - (b : ℤ) ^ 2 := by
    have : x ^ 2 + y ^ 2 + z ^ 2 + b ^ 2 = 4 * a := by omega
    have : ((x ^ 2 + y ^ 2 + z ^ 2 + b ^ 2 : ℕ) : ℤ) = ((4 * a : ℕ) : ℤ) := by rw [this]
    push_cast at this
    linarith
  -- choose the sign of z
  obtain ⟨w, hw2, hwodd, hwle, hwge, hw4⟩ : ∃ w : ℤ, w ^ 2 = (z : ℤ) ^ 2 ∧ w % 2 = 1 ∧
      w ≤ z ∧ -(z : ℤ) ≤ w ∧ ((b : ℤ) + x + y + w) % 4 = 0 := by
    by_cases hc : ((b : ℤ) + x + y + z) % 4 = 0
    · exact ⟨z, rfl, by omega, le_refl _, by omega, hc⟩
    · exact ⟨-z, by ring, by omega, by omega, le_refl _, by omega⟩
  -- the bound x + y + z < b + 4
  have hbound : (x : ℤ) + y + z < b + 4 := by
    have h2' : 3 * (a : ℤ) < (b : ℤ) ^ 2 + 2 * b + 4 := by exact_mod_cast h2
    have hsq : ((x : ℤ) + y + z) ^ 2 < ((b : ℤ) + 4) ^ 2 := by
      nlinarith [sq_nonneg ((x : ℤ) - y), sq_nonneg ((x : ℤ) - z), sq_nonneg ((y : ℤ) - z)]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  obtain ⟨s, hs⟩ : ∃ s : ℤ, (b : ℤ) + x + y + w = 4 * s := ⟨((b : ℤ) + x + y + w) / 4, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (b : ℤ) + x - y - w = 4 * t := ⟨((b : ℤ) + x - y - w) / 4, by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : ℤ, (b : ℤ) - x + y - w = 4 * u := ⟨((b : ℤ) - x + y - w) / 4, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v : ℤ, (b : ℤ) - x - y + w = 4 * v := ⟨((b : ℤ) - x - y + w) / 4, by omega⟩
  have hs0 : 0 ≤ s := by omega
  have ht0 : 0 ≤ t := by omega
  have hu0 : 0 ≤ u := by omega
  have hv0 : 0 ≤ v := by omega
  have hsum : (b : ℤ) = s + t + u + v := by omega
  have hsq : (a : ℤ) = s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 := by
    have e : 16 * (s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2) = 16 * (a : ℤ) := by
      have : (4 * s) ^ 2 + (4 * t) ^ 2 + (4 * u) ^ 2 + (4 * v) ^ 2 = 16 * (a : ℤ) := by
        rw [← hs, ← ht, ← hu, ← hv]
        linear_combination 4 * hI + 4 * hw2
      linarith
    linarith
  lift s to ℕ using hs0
  lift t to ℕ using ht0
  lift u to ℕ using hu0
  lift v to ℕ using hv0
  exact ⟨s, t, u, v, by exact_mod_cast hsq, by exact_mod_cast hsum⟩

end ThreeSquares

namespace OMA.Sun160324

open OeisA160324

/-- `Rep ks n`: `n` is a sum of polygonal numbers, one of each order in the list `ks`. -/
def Rep : List ℕ → ℕ → Prop
  | [], n => n = 0
  | k :: ks, n => ∃ x n', n = polygonalNumber k x + n' ∧ Rep ks n'

lemma Rep_nil (n : ℕ) : Rep [] n ↔ n = 0 := Iff.rfl

lemma Rep_cons (k : ℕ) (ks : List ℕ) (n : ℕ) :
    Rep (k :: ks) n ↔ ∃ x n', n = polygonalNumber k x + n' ∧ Rep ks n' := Iff.rfl

lemma Rep.cons (k x : ℕ) {ks : List ℕ} {n : ℕ} (h : Rep ks n) :
    Rep (k :: ks) (polygonalNumber k x + n) :=
  (Rep_cons k ks _).2 ⟨x, n, rfl, h⟩

lemma Rep.perm {l1 l2 : List ℕ} (h : l1.Perm l2) : ∀ n, Rep l1 n → Rep l2 n := by
  induction h with
  | nil => intro n h; exact h
  | cons k _ ih =>
    intro n hn
    obtain ⟨x, n', rfl, h'⟩ := (Rep_cons _ _ _).1 hn
    exact Rep.cons k x (ih n' h')
  | swap a b l =>
    intro n hn
    obtain ⟨x, n', rfl, h'⟩ := (Rep_cons _ _ _).1 hn
    obtain ⟨y, n'', rfl, h''⟩ := (Rep_cons _ _ _).1 h'
    have := Rep.cons a y (Rep.cons b x h'')
    have e : polygonalNumber b x + (polygonalNumber a y + n'') =
        polygonalNumber a y + (polygonalNumber b x + n'') := by omega
    rw [e]; exact this
  | trans _ _ ih1 ih2 => intro n hn; exact ih2 n (ih1 n hn)

lemma Rep.ofFn : ∀ (k : ℕ) (f : Fin k → ℕ) (n : ℕ), Rep (List.ofFn f) n →
    ∃ x : Fin k → ℕ, n = ∑ i : Fin k, polygonalNumber (f i) (x i) := by
  intro k
  induction k with
  | zero =>
    intro f n h
    rw [List.ofFn_zero, Rep_nil] at h
    exact ⟨fun _ => 0, by simp [h]⟩
  | succ k ih =>
    intro f n h
    rw [List.ofFn_succ, Rep_cons] at h
    obtain ⟨x, n', rfl, h'⟩ := h
    obtain ⟨y, hy⟩ := ih _ _ h'
    refine ⟨Fin.cons x y, ?_⟩
    rw [Fin.sum_univ_succ, hy]
    simp

/-! Bit masks: bit `n` of `maskOf N X ks` is set only if `Rep ks n`. -/

def orShifts (k M : ℕ) : ℕ → ℕ
  | 0 => M
  | x + 1 => orShifts k M x ||| (M <<< polygonalNumber k (x + 1))

lemma orShifts_testBit (k M : ℕ) : ∀ (X n : ℕ), (orShifts k M X).testBit n = true →
    ∃ x, polygonalNumber k x ≤ n ∧ M.testBit (n - polygonalNumber k x) = true := by
  intro X
  induction X with
  | zero =>
    intro n h
    exact ⟨0, by simp [polygonalNumber], by simpa [polygonalNumber, orShifts] using h⟩
  | succ X ih =>
    intro n h
    rw [orShifts, Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ih n h
    · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨X + 1, h.1, h.2⟩

def maskOf (N X : ℕ) : List ℕ → ℕ
  | [] => 1
  | k :: ks => orShifts k (maskOf N X ks) X % 2 ^ N

lemma maskOf_sound (N X : ℕ) : ∀ (ks : List ℕ) (n : ℕ),
    (maskOf N X ks).testBit n = true → Rep ks n := by
  intro ks
  induction ks with
  | nil =>
    intro n h
    rw [Rep_nil]
    exact Nat.testBit_one_eq_true_iff_self_eq_zero.1 h
  | cons k ks ih =>
    intro n h
    rw [maskOf, Nat.testBit_mod_two_pow, Bool.and_eq_true] at h
    obtain ⟨x, hx, hx'⟩ := orShifts_testBit _ _ _ _ h.2
    have := Rep.cons k x (ih _ hx')
    have e : polygonalNumber k x + (n - polygonalNumber k x) = n := by omega
    rwa [e] at this

lemma maskOf_full (N X : ℕ) (ks : List ℕ) (h : maskOf N X ks = 2 ^ N - 1) :
    ∀ n, n < N → Rep ks n := by
  intro n hn
  apply maskOf_sound N X
  rw [h, Nat.testBit_two_pow_sub_one]
  simpa using hn

def foldMask (C M : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => foldMask C M i ||| ((M >>> (i * C)) % 2 ^ C)

lemma foldMask_testBit (C M : ℕ) : ∀ (T ρ : ℕ), (foldMask C M T).testBit ρ = true →
    ∃ i, M.testBit (i * C + ρ) = true := by
  intro T
  induction T with
  | zero => intro ρ h; simp [foldMask] at h
  | succ T ih =>
    intro ρ h
    rw [foldMask, Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ih ρ h
    · rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, Nat.testBit_shiftRight] at h
      exact ⟨T, h.2⟩

lemma cover_of_fold (C R X T : ℕ) (rem : List ℕ)
    (h : foldMask C (maskOf (R + 1) X rem % 2 ^ (R + 1)) T = 2 ^ C - 1) :
    ∀ ρ, ρ < C → ∃ r, r ≤ R ∧ Rep rem r ∧ r % C = ρ := by
  intro ρ hρ
  have h1 : (foldMask C (maskOf (R + 1) X rem % 2 ^ (R + 1)) T).testBit ρ = true := by
    rw [h, Nat.testBit_two_pow_sub_one]; simpa using hρ
  obtain ⟨i, hi⟩ := foldMask_testBit _ _ _ _ h1
  rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
  refine ⟨i * C + ρ, by omega, maskOf_sound _ _ _ _ hi.2, ?_⟩
  rw [Nat.mul_add_mod_of_lt hρ]

/-! Arithmetic of the pairing argument. -/

lemma tri (x : ℕ) : 2 * (x * (x - 1) / 2) + x = x ^ 2 := by
  have h : 2 * (x * (x - 1) / 2) = x * (x - 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self x)
  rw [h]
  cases x with
  | zero => rfl
  | succ x => simp; ring

lemma pair_sum (C k k' x : ℕ) (h : (k - 2) + (k' - 2) = C) :
    polygonalNumber k x + polygonalNumber k' x = C * (x * (x - 1) / 2) + 2 * x := by
  unfold polygonalNumber
  rw [← h]; ring

lemma choose_b (C R Y N0 n : ℕ) (hC : 16 ≤ C) (hY15 : 15 ≤ Y)
    (hY : 15 * C * Y + 27 * C + 24 * R ≤ C * Y * Y)
    (hN : 5 * C * Y + 9 * C + 8 * R ≤ 2 * N0) (hn : N0 ≤ n) :
    ∃ j : ℕ, 6 * n ≤ C * ((2 * j + 1) * (2 * j)) ∧ C * (2 * j + 1) ^ 2 + 8 * R ≤ 8 * n := by
  classical
  have hex : ∃ j : ℕ, 6 * n ≤ C * ((2 * j + 1) * (2 * j)) := ⟨n, by
    have h1 : 16 * (1 * (2 * n)) ≤ C * ((2 * n + 1) * (2 * n)) :=
      Nat.mul_le_mul hC (Nat.mul_le_mul_right _ (by omega))
    omega⟩
  have hmin := fun j => Nat.find_min hex (m := j)
  have hspec := Nat.find_spec hex
  generalize Nat.find hex = j0 at hmin hspec
  rcases j0 with _ | j
  · exfalso; simp at hspec; subst hspec; omega
  · refine ⟨j + 1, hspec, ?_⟩
    have h1 : C * ((2 * j + 1) * (2 * j)) < 6 * n := by
      have := hmin j (by omega); omega
    by_contra hcon
    rw [not_le] at hcon
    have e : C * (2 * (j + 1) + 1) ^ 2 = C * ((2 * j + 1) * (2 * j)) + 5 * (C * (2 * j)) + 9 * C := by
      ring
    have e2 : C * ((2 * j + 1) * (2 * j)) = C * (2 * j) * (2 * j) + C * (2 * j) := by ring
    have h2 : 2 * n < 5 * (C * (2 * j)) + 9 * C + 8 * R := by omega
    rcases Nat.lt_or_ge (2 * j) Y with hlt | hge
    · have : C * (2 * j) ≤ C * Y := Nat.mul_le_mul_left C hlt.le
      have e3 : 5 * C * Y = 5 * (C * Y) := by ring
      omega
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
      have e3 : C * (2 * j) * (2 * j) = C * Y * Y + C * d * (2 * Y + d) := by rw [hd]; ring
      have e4 : C * (2 * j) = C * Y + C * d := by rw [hd]; ring
      have e5 : C * d * 15 ≤ C * d * (2 * Y + d) := Nat.mul_le_mul_left _ (by omega)
      have e6 : 15 * C * Y = 15 * (C * Y) := by ring
      omega

theorem big (C R Y N0 k1 k1' k2 k2' k3 k3' k4 k4' : ℕ) (rem : List ℕ)
    (hk1 : (k1 - 2) + (k1' - 2) = C) (hk2 : (k2 - 2) + (k2' - 2) = C)
    (hk3 : (k3 - 2) + (k3' - 2) = C) (hk4 : (k4 - 2) + (k4' - 2) = C)
    (hC : 16 ≤ C) (hY15 : 15 ≤ Y)
    (hY : 15 * C * Y + 27 * C + 24 * R ≤ C * Y * Y)
    (hN : 5 * C * Y + 9 * C + 8 * R ≤ 2 * N0)
    (hcover : ∀ ρ, ρ < C → ∃ r, r ≤ R ∧ Rep rem r ∧ r % C = ρ)
    (n : ℕ) (hn : N0 ≤ n) :
    Rep ([k1, k1', k2, k2', k3, k3', k4, k4'] ++ rem) n := by
  obtain ⟨j, hj1, hj2⟩ := choose_b C R Y N0 n hC hY15 hY hN hn
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * j + 1 := ⟨_, rfl⟩
  rw [← hb] at hj1 hj2
  have hCb : 16 * b ≤ C * b := Nat.mul_le_mul_right b hC
  have hbb : C * b ≤ C * b ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul_left C (Nat.le_mul_self b)
  have hsq : C * b ^ 2 = C * (b * (2 * j)) + C * b := by rw [hb]; ring
  obtain ⟨r, hrR, hrep, hrmod⟩ := hcover ((n - 2 * b) % C) (Nat.mod_lt _ (by omega))
  have hdvd : C ∣ (n - 2 * b) - r :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hrmod.symm)
  obtain ⟨q, hq⟩ := hdvd
  have hnq : n = C * q + 2 * b + r := by omega
  have hbodd : Odd b := ⟨j, hb⟩
  have haodd : Odd (b + 2 * q) := by
    rw [Nat.odd_iff] at hbodd ⊢; omega
  have c1 : b ^ 2 < 4 * (b + 2 * q) := by
    apply Nat.lt_of_mul_lt_mul_left (a := C)
    have e : C * (4 * (b + 2 * q)) = 4 * (C * b) + 8 * (C * q) := by ring
    omega
  have c2 : 3 * (b + 2 * q) < b ^ 2 + 2 * b + 4 := by
    apply Nat.lt_of_mul_lt_mul_left (a := C)
    have e : C * (3 * (b + 2 * q)) = 3 * (C * b) + 6 * (C * q) := by ring
    have e' : C * (b ^ 2 + 2 * b + 4) = C * b ^ 2 + 2 * (C * b) + 4 * C := by ring
    omega
  obtain ⟨s, t, u, v, ha, hbs⟩ := ThreeSquares.cauchy_lemma (b + 2 * q) b haodd hbodd c1 c2
  have hT : s * (s - 1) / 2 + t * (t - 1) / 2 + u * (u - 1) / 2 + v * (v - 1) / 2 = q := by
    have := tri s; have := tri t; have := tri u; have := tri v
    omega
  have key := Rep.cons k1 s (Rep.cons k1' s (Rep.cons k2 t (Rep.cons k2' t
    (Rep.cons k3 u (Rep.cons k3' u (Rep.cons k4 v (Rep.cons k4' v hrep)))))))
  have hval : polygonalNumber k1 s + (polygonalNumber k1' s + (polygonalNumber k2 t +
      (polygonalNumber k2' t + (polygonalNumber k3 u + (polygonalNumber k3' u +
      (polygonalNumber k4 v + (polygonalNumber k4' v + r))))))) = n := by
    have p1 := pair_sum C k1 k1' s hk1
    have p2 := pair_sum C k2 k2' t hk2
    have p3 := pair_sum C k3 k3' u hk3
    have p4 := pair_sum C k4 k4' v hk4
    have e : C * q = C * (s * (s - 1) / 2) + C * (t * (t - 1) / 2) + C * (u * (u - 1) / 2)
        + C * (v * (v - 1) / 2) := by rw [← hT]; ring
    omega
  rw [hval] at key
  exact key

/-! The certificate for one dimension `m`. -/

def pairs (m : ℕ) : List ℕ :=
  [m + 1, 2 * m, m + 2, 2 * m - 1, m + 3, 2 * m - 2, m + 4, 2 * m - 3]

def rest (m : ℕ) : List ℕ := List.range' (m + 5) (m - 8)

def chk (m : ℕ) : Bool :=
  (List.range' (m + 1) m).isPerm (pairs m ++ rest m) &&
  (foldMask (3 * m - 3) (maskOf (16 * m + 1) 4 (rest m) % 2 ^ (16 * m + 1)) 7
      == 2 ^ (3 * m - 3) - 1) &&
  (maskOf (265 * m) 7 (List.range' (m + 1) m) == 2 ^ (265 * m) - 1)

lemma ofFn_eq (m : ℕ) : List.ofFn (fun i : Fin m => m + (i : ℕ) + 1) = List.range' (m + 1) m := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_range']
    omega

theorem of_chk (m : ℕ) (hm : 12 ≤ m) (h : chk m = true) (n : ℕ) :
    ∃ x : Fin m → ℕ, n = ∑ i : Fin m, polygonalNumber (m + (i : ℕ) + 1) (x i) := by
  apply Rep.ofFn m (fun i : Fin m => m + (i : ℕ) + 1) n
  rw [ofFn_eq]
  unfold chk at h
  rw [Bool.and_eq_true, Bool.and_eq_true, List.isPerm_iff, beq_iff_eq, beq_iff_eq] at h
  obtain ⟨⟨hperm, hcov⟩, hsmall⟩ := h
  rcases Nat.lt_or_ge n (265 * m) with hlt | hge
  · exact maskOf_full _ _ _ hsmall n hlt
  · apply Rep.perm hperm.symm
    exact big (3 * m - 3) (16 * m) 25 (265 * m) _ _ _ _ _ _ _ _ (rest m)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (cover_of_fold _ _ _ _ _ hcov) n hge

theorem all_chk : ∀ m : ℕ, 12 ≤ m → m < 66 → chk m = true := by
  intro m h1 h2
  interval_cases m <;> decide +kernel

end OMA.Sun160324

theorem OMA.solution : OMA.R_OeisA160324_conjecture2_R1_H2_R1.H2 := by
  intro m hm hlt n
  exact OMA.Sun160324.of_chk m hm (OMA.Sun160324.all_chk m hm hlt) n
