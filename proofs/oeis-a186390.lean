import OMAStatements.S_oeis_a186390
import Mathlib.Tactic

/-!
# Proof of `oeis-a186390`

Proves Chai Wah Wu's order-7 linear recurrence and generating function for A186390, the adjusted
joint rank sequence of `f(i) = 6 * i` and `g(j) = j * (j + 1) / 2`.

1. For every `n ≥ 1`, the count of `i ∈ [1, g n]` with `6 * i < g n` equals `(g n - 1) / 6`,
   so `a n = n + (n * (n + 1) / 2 - 1) / 6` (and `a 0 = 0`).
2. Writing `n = 12 * q + r` (`0 ≤ r < 12`), `a n` is an explicit quadratic quasipolynomial
   of period `12` (`(1 - X)^3 * (1 + X^2) * (1 + X + X^2)` annihilates it for `n > 7`).
3. Checking the initial coefficients `n ≤ 7` directly gives the generating function identity.
-/

namespace OMA.A186390Proof

open OMA.S_oeis_a186390 Finset PowerSeries

private lemma card_lt_six (m : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc 1 m).filter (fun i => 6 * i < m)).card = (m - 1) / 6 := by
  have heq : (Finset.Icc 1 m).filter (fun i => 6 * i < m) = Finset.Icc 1 ((m - 1) / 6) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro ⟨⟨h1, _⟩, hlt⟩
      exact ⟨h1, by omega⟩
    · intro ⟨h1, h2⟩
      exact ⟨⟨h1, by omega⟩, by omega⟩
  rw [heq, Nat.card_Icc]
  omega

private lemma a_zero : a 0 = 0 := by decide

private lemma a_formula (n : ℕ) (hn : 1 ≤ n) :
    a n = (n : ℤ) + (((n * (n + 1) / 2 - 1) / 6 : ℕ) : ℤ) := by
  unfold a f g
  have hg : 1 ≤ n * (n + 1) / 2 := by
    have h2 : 2 ≤ n * (n + 1) := by nlinarith
    omega
  rw [card_lt_six _ hg]

private lemma g_mod12 (q r : ℕ) :
    (12 * q + r) * (12 * q + r + 1) / 2 = 72 * q ^ 2 + 12 * q * r + 6 * q + r * (r + 1) / 2 := by
  have h1 : (12 * q + r) * (12 * q + r + 1) =
      2 * (72 * q ^ 2 + 12 * q * r + 6 * q) + r * (r + 1) := by ring
  rw [h1, Nat.mul_add_div (by decide : 0 < 2)]

private lemma a_quasi (q r : ℕ) (hpos : 1 ≤ 12 * q + r) :
    a (12 * q + r) =
      12 * (q : ℤ) ^ 2 + (2 * (r : ℤ) + 13) * (q : ℤ) + (r : ℤ) +
        if r = 0 then -1 else ((((r * (r + 1) / 2 - 1) / 6 : ℕ) : ℤ)) := by
  rw [a_formula (12 * q + r) hpos, g_mod12]
  by_cases hr0 : r = 0
  · subst hr0
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_mul, Nat.zero_div, ↓reduceIte]
    have hq : 1 ≤ q := by omega
    have hdiv : (72 * q ^ 2 + 6 * q - 1) / 6 = 12 * q ^ 2 + q - 1 := by
      have hsub : 72 * q ^ 2 + 6 * q - 1 = 6 * (12 * q ^ 2 + q - 1) + 5 := by
        have : 1 ≤ 12 * q ^ 2 + q := by nlinarith
        omega
      rw [hsub]
      omega
    rw [hdiv]
    have hge : 1 ≤ 12 * q ^ 2 + q := by nlinarith
    have hcast : ((12 * q ^ 2 + q - 1 : ℕ) : ℤ) = 12 * (q : ℤ) ^ 2 + (q : ℤ) - 1 := by
      have := Nat.cast_sub hge (R := ℤ)
      push_cast at this ⊢
      linarith
    rw [hcast]
    push_cast
    ring
  · rw [if_neg hr0]
    have hr_pos : 1 ≤ r := by omega
    have hr1 : 1 ≤ r * (r + 1) / 2 := by
      have : 2 ≤ r * (r + 1) := by nlinarith
      omega
    have h6 : 72 * q ^ 2 + 12 * q * r + 6 * q = 6 * (12 * q ^ 2 + 2 * q * r + q) := by ring
    have hsub : 72 * q ^ 2 + 12 * q * r + 6 * q + r * (r + 1) / 2 - 1 =
        6 * (12 * q ^ 2 + 2 * q * r + q) + (r * (r + 1) / 2 - 1) := by omega
    rw [hsub, Nat.mul_add_div (by decide : 0 < 6)]
    push_cast
    ring

private lemma a_rec (n : ℕ) (hn : 7 < n) :
    a n = 2 * a (n - 1) - 2 * a (n - 2) + 3 * a (n - 3) - 3 * a (n - 4) +
      2 * a (n - 5) - 2 * a (n - 6) + a (n - 7) := by
  have h1 : 1 ≤ n := by omega
  have h2 : 1 ≤ n - 1 := by omega
  have h3 : 1 ≤ n - 2 := by omega
  have h4 : 1 ≤ n - 3 := by omega
  have h5 : 1 ≤ n - 4 := by omega
  have h6 : 1 ≤ n - 5 := by omega
  have h7 : 1 ≤ n - 6 := by omega
  have h8 : 1 ≤ n - 7 := by omega
  set q := (n - 7) / 12
  set r := (n - 7) % 12
  have hr : r < 12 := Nat.mod_lt _ (by decide)
  have hn_eq : n - 7 = 12 * q + r := (Nat.div_add_mod (n - 7) 12).symm
  have e0 : n = 12 * q + (r + 7) := by omega
  have e1 : n - 1 = 12 * q + (r + 6) := by omega
  have e2 : n - 2 = 12 * q + (r + 5) := by omega
  have e3 : n - 3 = 12 * q + (r + 4) := by omega
  have e4 : n - 4 = 12 * q + (r + 3) := by omega
  have e5 : n - 5 = 12 * q + (r + 2) := by omega
  have e6 : n - 6 = 12 * q + (r + 1) := by omega
  have e7 : n - 7 = 12 * q + r := hn_eq
  rw [e1, e2, e3, e4, e5, e6, e7, e0]
  rw [a_quasi q (r + 7) (by omega), a_quasi q (r + 6) (by omega),
    a_quasi q (r + 5) (by omega), a_quasi q (r + 4) (by omega),
    a_quasi q (r + 3) (by omega), a_quasi q (r + 2) (by omega),
    a_quasi q (r + 1) (by omega), a_quasi q r (by omega)]
  interval_cases r <;> norm_num <;> ring

private lemma a_init :
    a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧ a 4 = 5 ∧ a 5 = 7 ∧ a 6 = 9 ∧ a 7 = 11 := by
  decide +kernel

private lemma gf_form :
    (X - 1) ^ 3 * (X ^ 2 + 1) * (X ^ 2 + X + 1) * PowerSeries.mk a =
      (X * (X ^ 6 - X ^ 2 - 1) : PowerSeries ℤ) := by
  let S := PowerSeries.mk a
  change _ * S = _
  have hlhs : ((X - 1) ^ 3 * (X ^ 2 + 1) * (X ^ 2 + X + 1) : PowerSeries ℤ) * S =
      -S + C 2 * (S * X ^ 1) - C 2 * (S * X ^ 2) + C 3 * (S * X ^ 3) - C 3 * (S * X ^ 4) +
        C 2 * (S * X ^ 5) - C 2 * (S * X ^ 6) + S * X ^ 7 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X * (X ^ 6 - X ^ 2 - 1) : PowerSeries ℤ) = X ^ 7 - X ^ 3 - X ^ 1 := by ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, S, coeff_mk]
  by_cases h8 : n ≤ 7
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := a_init
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7]
  · have hn : 7 < n := by omega
    simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 1 by omega)]
    linarith [a_rec n hn]

theorem result : type_of% @OMA.S_oeis_a186390.main := ⟨a_rec, gf_form⟩

end OMA.A186390Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a186390.main := OMA.A186390Proof.result
