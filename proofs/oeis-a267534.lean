import OMAStatements.S_oeis_a267534
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

namespace OMA.A267534Proof

open OMA.S_oeis_a267534 PowerSeries

def stp (p : ℕ × ℕ) : ℕ × ℕ := (p.2, (p.1 + p.2) % 32)

def lm : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | k+1 => stp (lm k)

lemma lucas_lm (n : ℕ) : (lucasPair n).1 % 32 = (lm n).1 % 32 ∧
    (lucasPair n).2 % 32 = (lm n).2 % 32 := by
  induction n with
  | zero => simp [lucasPair, lm]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [lucasPair, lm, stp]
    refine ⟨h2, ?_⟩
    omega

lemma lm_period (n : ℕ) : lm (n + 48) = lm n := by
  induction n with
  | zero => decide +kernel
  | succ k ih =>
    show stp (lm (k + 48)) = stp (lm k)
    rw [ih]

lemma lm_mod (n : ℕ) : lm n = lm (n % 48) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 48
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 48 := ⟨n - 48, by omega⟩
      rw [lm_period, ih m (by omega), Nat.add_mod_right]

lemma table : ∀ r, r < 48 → (lm r).1 % 8 ≠ 0 ∧
    (((lm r).1 % 8 = 7 ∨ (lm r).1 % 32 = 28) ↔
      (r % 24 = 4 ∨ r % 24 = 8 ∨ r % 24 = 11 ∨ r % 24 = 16 ∨ r % 24 = 20 ∨ r % 24 = 21 ∨
        r % 24 = 23)) := by
  decide +kernel

lemma form_iff (L : ℕ) (h0 : L % 8 ≠ 0) :
    (∃ a b : ℕ, L = 4 ^ a * (8 * b + 7)) ↔ (L % 8 = 7 ∨ L % 32 = 28) := by
  constructor
  · rintro ⟨a, b, h⟩
    rcases a with _ | _ | a
    · left; simp at h; omega
    · right; simp at h; omega
    · exfalso
      have e : L = 16 * (4 ^ a * (8 * b + 7)) := by rw [h]; ring
      generalize 4 ^ a * (8 * b + 7) = t at e
      omega
  · rintro (h | h)
    · exact ⟨0, L / 8, by simp; omega⟩
    · exact ⟨1, L / 32, by simp; omega⟩

lemma bad_iff (n : ℕ) : badIndex n ↔
    (n % 24 = 4 ∨ n % 24 = 8 ∨ n % 24 = 11 ∨ n % 24 = 16 ∨ n % 24 = 20 ∨ n % 24 = 21 ∨
        n % 24 = 23) := by
  have hl := (lucas_lm n).1
  rw [lm_mod n] at hl
  have ht := table (n % 48) (Nat.mod_lt _ (by norm_num))
  have e : n % 48 % 24 = n % 24 := by omega
  rw [e] at ht
  obtain ⟨t0, t1⟩ := ht
  unfold badIndex
  rw [ThreeSquares.sum_three_squares_iff, not_not, form_iff _ (by omega), ← t1]
  omega

def c : ℕ → ℕ
  | 0 => 4
  | 1 => 8
  | 2 => 11
  | 3 => 16
  | 4 => 20
  | 5 => 21
  | _ => 23

def f (k : ℕ) : ℕ := 24 * (k / 7) + c (k % 7)

lemma c_cases (r : ℕ) (hr : r < 7) : c r < 24 ∧
    (c r = 4 ∨ c r = 8 ∨ c r = 11 ∨ c r = 16 ∨ c r = 20 ∨ c r = 21 ∨ c r = 23) := by
  interval_cases r <;> simp [c]

lemma c_step (r : ℕ) (hr : r < 6) : c r < c (r + 1) := by
  interval_cases r <;> simp [c]

lemma f_strict : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold f
  have h1 : ((k+1)/7 = k/7 ∧ (k+1)%7 = k%7+1 ∧ k % 7 < 6) ∨
      ((k+1)/7 = k/7+1 ∧ (k+1)%7 = 0 ∧ k%7 = 6) := by omega
  rcases h1 with ⟨a, b, d⟩ | ⟨a, b, d⟩
  · rw [a, b]
    have := c_step _ d
    omega
  · rw [a, b, d]
    simp only [c]
    omega

lemma f_bad (k : ℕ) : badIndex (f k) := by
  rw [bad_iff]
  have h := c_cases (k % 7) (Nat.mod_lt _ (by norm_num))
  have e : f k % 24 = c (k % 7) := by unfold f; omega
  rw [e]
  exact h.2

lemma bad_f (n : ℕ) (h : badIndex n) : ∃ k, f k = n := by
  rw [bad_iff] at h
  have key : ∀ r, r < 7 → n % 24 = c r → ∃ k, f k = n := by
    intro r hr hc
    refine ⟨7 * (n / 24) + r, ?_⟩
    unfold f
    have a : (7 * (n / 24) + r) / 7 = n / 24 := by omega
    have b : (7 * (n / 24) + r) % 7 = r := by omega
    rw [a, b]
    omega
  rcases h with h | h | h | h | h | h | h
  · exact key 0 (by norm_num) h
  · exact key 1 (by norm_num) h
  · exact key 2 (by norm_num) h
  · exact key 3 (by norm_num) h
  · exact key 4 (by norm_num) h
  · exact key 5 (by norm_num) h
  · exact key 6 (by norm_num) h

lemma range_f : Set.range f = Set.ofPred badIndex := by
  ext n
  constructor
  · rintro ⟨k, rfl⟩
    exact f_bad k
  · intro h
    exact bad_f n h

lemma term_eq : term = f := by
  have hinf : (Set.ofPred badIndex).Infinite := by
    rw [← range_f]
    exact Set.infinite_range_of_injective f_strict.injective
  have h1 : StrictMono (Nat.nth badIndex) := Nat.nth_strictMono hinf
  have h2 : Set.range (Nat.nth badIndex) = Set.range f := by
    rw [Nat.range_nth_of_infinite hinf, range_f]
  exact (StrictMono.range_inj h1 f_strict).1 h2

lemma f_add (k : ℕ) : f (k + 7) = f k + 24 := by
  unfold f
  have a : (k + 7) / 7 = k / 7 + 1 := by omega
  have b : (k + 7) % 7 = k % 7 := by omega
  rw [a, b]
  ring

lemma series_id :
    (X * PowerSeries.mk (fun k => (f k : ℤ))) *
      ((1-X)^2*(1+X+X^2+X^3+X^4+X^5+X^6)) =
      X*(2+X)*(2+X+X^2+2*X^3+X^4+X^6) := by
  set A : PowerSeries ℤ := PowerSeries.mk (fun k => (f k : ℤ)) with hA
  have hL : (X * A) * ((1-X)^2*(1+X+X^2+X^3+X^4+X^5+X^6)) =
      A * X ^ 1 - A * X ^ 2 - A * X ^ 8 + A * X ^ 9 := by ring
  have hR : (X*(2+X)*(2+X+X^2+2*X^3+X^4+X^6) : PowerSeries ℤ) =
      C 4 * X ^ 1 + C 4 * X ^ 2 + C 3 * X ^ 3 + C 5 * X ^ 4 + C 4 * X ^ 5
        + C 1 * X ^ 6 + C 2 * X ^ 7 + C 1 * X ^ 8 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  by_cases hn : n < 10
  · interval_cases n <;> simp [f, c]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    have e1 : f (m + 9) = f (m + 2) + 24 := f_add (m + 2)
    have e2 : f (m + 8) = f (m + 1) + 24 := f_add (m + 1)
    simp [e1, e2]

end OMA.A267534Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267534.main := by
  rw [OMA.A267534Proof.term_eq]
  refine ⟨OMA.A267534Proof.series_id, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  have e1 := OMA.A267534Proof.f_add (m + 1)
  have e2 := OMA.A267534Proof.f_add m
  have a1 : m + 9 - 1 = m + 8 := by omega
  have a2 : m + 9 - 2 = m + 7 := by omega
  have a3 : m + 9 - 8 = m + 1 := by omega
  have a4 : m + 9 - 9 = m := by omega
  rw [a1, a2, a3, a4, show m + 8 = m + 1 + 7 from rfl, e1, e2]
  push_cast
  ring
