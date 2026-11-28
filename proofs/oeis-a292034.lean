import OMAStatements.S_oeis_a292034
import Mathlib

-- Problem: OEIS A292034, a(n) = round(lambda(6) alpha(6)^n). Conjectures of Colin Barker:
-- a(n) = 6a(n-1) - 6a(n-2) + 6a(n-3) - a(n-4) for n > 4, with the terms 1, 6, 29, 144.
-- Statement: statements/oeis-a292034.lean (declaration OMA.S_oeis_a292034.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let t = sqrt(20), s1 = (6 + t)/2, s2 = (6 - t)/2 (the roots of s^2 - 6s + 4), and
-- U(s, 0) = 2, U(s, 1) = s, U(s, n+2) = s U(s, n+1) - U(s, n). For s = s1, s2 the sequence
-- U(s, .) satisfies the recurrence of order 4, so the integer sequence c of the recurrence
-- (c = 0, 1, 6, 29, ...) has c(n) t = U(s1, n) - U(s2, n) (lemma c_formula).
-- The number x = alpha(6) = (6 + t + w)/4 with w^2 = 40 + 12 t has x + 1/x = s1 and x > 5, so
-- U(s1, n) = x^n + x^(-n). The quantity U(n+1)^2 - s U(n+1) U(n) + U(n)^2 = 4 - s^2 is
-- constant, so |U(s2, n)| <= 2 because s2^2 < 4. Thus
-- lambda x^n - c(n) = (U(s2, n) - x^(-n))/t has absolute value at most (2 + 1/5)/t < 1/2
-- for n >= 1, and a(n) = c(n).

namespace OMA.A292034

open OMA.S_oeis_a292034

/-- The integer sequence of the recurrence. -/
def c : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 29
  | n + 4 => 6 * c (n + 3) - 6 * c (n + 2) + 6 * c (n + 1) - c n

/-- The sequence U(0) = 2, U(1) = s, U(n+2) = s U(n+1) - U(n). -/
noncomputable def U (s : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => s
  | n + 2 => s * U s (n + 1) - U s n

lemma U_quartic (s : ℝ) (hs : s ^ 2 - 6 * s + 4 = 0) (n : ℕ) :
    U s (n + 4) = 6 * U s (n + 3) - 6 * U s (n + 2) + 6 * U s (n + 1) - U s n := by
  have h4 : U s (n + 4) = s * U s (n + 3) - U s (n + 2) := rfl
  have h3 : U s (n + 3) = s * U s (n + 2) - U s (n + 1) := rfl
  have h2 : U s (n + 2) = s * U s (n + 1) - U s n := rfl
  rw [h4, h3]
  have : U s n = s * U s (n + 1) - U s (n + 2) := by rw [h2]; ring
  rw [this]
  linear_combination (U s (n + 2)) * hs

/-- The bound |U(n)| ≤ 2 for |s| < 2. -/
lemma U_bound (s : ℝ) (hs : s ^ 2 < 4) (n : ℕ) : U s n ^ 2 ≤ 4 := by
  have inv : ∀ m, U s (m + 1) ^ 2 - s * U s (m + 1) * U s m + U s m ^ 2 = 4 - s ^ 2 := by
    intro m
    induction m with
    | zero =>
      show s ^ 2 - s * s * 2 + 2 ^ 2 = 4 - s ^ 2
      ring
    | succ m ih =>
      have h2 : U s (m + 1 + 1) = s * U s (m + 1) - U s m := rfl
      rw [h2]
      linear_combination ih
  have h := inv n
  nlinarith [sq_nonneg (U s (n + 1) - s * U s n / 2), sq_nonneg (U s n)]

lemma U_pow (s x : ℝ) (hx : x ≠ 0) (h : x + x⁻¹ = s) (n : ℕ) :
    U s n = x ^ n + (x⁻¹) ^ n ∧ U s (n + 1) = x ^ (n + 1) + (x⁻¹) ^ (n + 1) := by
  induction n with
  | zero =>
    refine ⟨by simp [U]; norm_num, by simp [U]; exact h.symm⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have h2 : U s (n + 1 + 1) = s * U s (n + 1) - U s n := rfl
    rw [h2, ih.1, ih.2, ← h]
    have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
    have e1 : x ^ (n + 1 + 1) = x * x ^ (n + 1) := by ring
    have e2 : (x⁻¹) ^ (n + 1 + 1) = x⁻¹ * (x⁻¹) ^ (n + 1) := by ring
    have e3 : x⁻¹ * x ^ (n + 1) = x ^ n := by
      rw [pow_succ]
      calc x⁻¹ * (x ^ n * x) = (x * x⁻¹) * x ^ n := by ring
        _ = x ^ n := by rw [hxx, one_mul]
    have e4 : x * (x⁻¹) ^ (n + 1) = (x⁻¹) ^ n := by
      rw [pow_succ]
      calc x * ((x⁻¹) ^ n * x⁻¹) = (x * x⁻¹) * (x⁻¹) ^ n := by ring
        _ = (x⁻¹) ^ n := by rw [hxx, one_mul]
    rw [e1, e2]
    linear_combination e3 + e4

section main
variable (t : ℝ) (ht0 : 0 < t) (ht2 : t ^ 2 = 20)
include ht0 ht2

lemma c_formula (n : ℕ) :
    ((c n : ℝ) * t = U ((6 + t) / 2) n - U ((6 - t) / 2) n) ∧
    ((c (n + 1) : ℝ) * t = U ((6 + t) / 2) (n + 1) - U ((6 - t) / 2) (n + 1)) ∧
    ((c (n + 2) : ℝ) * t = U ((6 + t) / 2) (n + 2) - U ((6 - t) / 2) (n + 2)) ∧
    ((c (n + 3) : ℝ) * t = U ((6 + t) / 2) (n + 3) - U ((6 - t) / 2) (n + 3)) := by
  have hs1 : ((6 + t) / 2) ^ 2 - 6 * ((6 + t) / 2) + 4 = 0 := by nlinarith
  have hs2 : ((6 - t) / 2) ^ 2 - 6 * ((6 - t) / 2) + 4 = 0 := by nlinarith
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [c, U]
    · simp [c, U]; ring
    · simp only [c, U]; push_cast; nlinarith
    · simp only [c, U]; push_cast; nlinarith
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    refine ⟨h1, h2, h3, ?_⟩
    have hc : c (n + 1 + 3) = 6 * c (n + 3) - 6 * c (n + 2) + 6 * c (n + 1) - c n := rfl
    rw [show n + 1 + 3 = n + 4 from rfl] at hc ⊢
    rw [hc, U_quartic _ hs1 n, U_quartic _ hs2 n]
    push_cast
    linear_combination 6 * h3 - 6 * h2 + 6 * h1 - h0

end main

lemma core (t w x : ℝ) (ht2 : t ^ 2 = 20) (ht0 : 0 < t) (hw0 : 0 ≤ w) (hw2 : w ^ 2 = 40 + 12 * t)
    (hal : x = (6 + t + w) / 4) (n : ℕ) (hn : 1 ≤ n) : round (1 / t * x ^ n) = c n := by
  have htl : 4.4 < t := by nlinarith
  have htu : t < 4.5 := by nlinarith
  have hquad : x ^ 2 - (6 + t) / 2 * x + 1 = 0 := by rw [hal]; nlinarith
  have hx5 : 5 < x := by
    have h1 : (6 + t) / 4 ≤ x := by rw [hal]; linarith
    by_contra hcon
    push Not at hcon
    nlinarith
  have hx0 : x ≠ 0 := by linarith
  have hinv : x + x⁻¹ = (6 + t) / 2 := by
    field_simp
    nlinarith
  have hxinv : x⁻¹ < 1 / 5 := by
    rw [inv_lt_comm₀ (by linarith) (by norm_num)]
    simpa using hx5
  have hxinv0 : 0 < x⁻¹ := inv_pos.mpr (by linarith)
  -- the formula
  have hc := (c_formula t ht0 ht2 n).1
  rw [(U_pow _ x hx0 hinv n).1] at hc
  have hb := U_bound ((6 - t) / 2) (by nlinarith) n
  have hpow : (x⁻¹) ^ n ≤ 1 / 5 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 : (x⁻¹) ^ m ≤ 1 := pow_le_one₀ hxinv0.le (by linarith)
    rw [pow_succ]
    nlinarith [pow_nonneg hxinv0.le m]
  have hpow0 : 0 ≤ (x⁻¹) ^ n := pow_nonneg hxinv0.le n
  have hv : |U ((6 - t) / 2) n| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [abs_le] at hv
  rw [round_eq_iff, Set.mem_Ico]
  have key : 1 / t * x ^ n = (c n : ℝ) + (U ((6 - t) / 2) n - (x⁻¹) ^ n) / t := by
    have hxn : x ^ n = (c n : ℝ) * t + (U ((6 - t) / 2) n - (x⁻¹) ^ n) := by linarith
    rw [hxn]
    generalize (U ((6 - t) / 2) n - (x⁻¹) ^ n) = D
    field_simp
  rw [key]
  have hd : |(U ((6 - t) / 2) n - (x⁻¹) ^ n) / t| < 1 / 2 := by
    rw [abs_div, abs_of_pos ht0, div_lt_iff₀ ht0, abs_lt]
    constructor <;> nlinarith
  rw [abs_lt] at hd
  constructor <;> linarith [hd.1, hd.2]

theorem a_eq_c (n : ℕ) (hn : 1 ≤ n) : a n = c n := by
  have h20 : ((6 - 4) * 6 + 8 : ℝ) = 20 := by norm_num
  have ht2 : (√((6 - 4) * 6 + 8 : ℝ)) ^ 2 = 20 := by rw [h20]; exact Real.sq_sqrt (by norm_num)
  have ht0 : 0 < √((6 - 4) * 6 + 8 : ℝ) := by rw [h20]; exact Real.sqrt_pos.mpr (by norm_num)
  have hpos : (0 : ℝ) ≤ 6 * (6 + √((6 - 4) * 6 + 8 : ℝ) - 2) - 4 := by nlinarith
  have hw2 : (√2 * √(6 * (6 + √((6 - 4) * 6 + 8 : ℝ) - 2) - 4)) ^ 2
      = 40 + 12 * √((6 - 4) * 6 + 8 : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hpos]
    ring
  exact core _ _ _ ht2 ht0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hw2 rfl n hn

theorem result : a 1 = 1 ∧ a 2 = 6 ∧ a 3 = 29 ∧ a 4 = 144 ∧
    ∀ n : ℕ, 4 < n → a n = 6 * a (n - 1) - 6 * a (n - 2) + 6 * a (n - 3) - a (n - 4) := by
  refine ⟨a_eq_c 1 le_rfl, a_eq_c 2 (by norm_num), a_eq_c 3 (by norm_num),
    a_eq_c 4 (by norm_num), ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [a_eq_c _ (by omega), a_eq_c _ (by omega), a_eq_c _ (by omega), a_eq_c _ (by omega),
    a_eq_c _ (by omega)]
  show c (m + 1 + 4) = 6 * c (m + 1 + 3) - 6 * c (m + 1 + 2) + 6 * c (m + 1 + 1) - c (m + 1)
  rfl

end OMA.A292034

theorem OMA.solution : type_of% @OMA.S_oeis_a292034.main := OMA.A292034.result
