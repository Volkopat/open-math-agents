import OMAStatements.S_oeis_a227054
import Mathlib

namespace OMA.A227054Proof

open OMA.S_oeis_a227054

/-- Twice a triangular number. -/
lemma two_T (k : ℕ) : 2 * T k = k * (k + 1) := by
  show 2 * (k * (k + 1) / 2) = k * (k + 1)
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd

/-- The product form of `n * T k = T j`. -/
lemma T_eq_of (n k j : ℕ) (h : n * (k * (k + 1)) = j * (j + 1)) : n * T k = T j := by
  have h1 := two_T k
  have h2 := two_T j
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
  calc 2 * (n * T k) = n * (2 * T k) := by ring
    _ = n * (k * (k + 1)) := by rw [h1]
    _ = j * (j + 1) := h
    _ = 2 * T j := h2.symm

/-- A witness shows that `a(n) ≠ 0`. -/
lemma not_zero_of (n k j : ℕ) (hk : 1 ≤ k) (h : n * T k = T j) : ¬ IsZero n := by
  intro hz
  exact hz ⟨k, j, hk, h⟩

/-- One step of the bound: a solution of `x^2 + y^2 - 2 s x y = 1` with `x > y ≥ 1` has `x > 5 y`. -/
lemma descA (x y s : ℤ) (hs : 3 ≤ s) (hy : 1 ≤ y) (hxy : y < x)
    (h : x ^ 2 + y ^ 2 - 2 * s * x * y = 1) : 5 * y + 1 ≤ x := by
  have hx : 0 < x := by linarith
  have hf : x * (2 * s * y - x) = y ^ 2 - 1 := by linear_combination (-1 : ℤ) * h
  have hf2 : 2 * s * y - x < y := by
    by_contra hc
    have h3 : x * y ≤ x * (2 * s * y - x) := mul_le_mul_of_nonneg_left (not_lt.mp hc) hx.le
    have h4 : y * y < x * y := mul_lt_mul_of_pos_right hxy (by linarith)
    nlinarith
  have h5 : 3 * y ≤ s * y := mul_le_mul_of_nonneg_right hs (by linarith)
  nlinarith

/-- Vieta descent: `(x, y)` with `y ≥ 2` gives the smaller solution `(y, 2 s y - x)`. -/
lemma descB (x y s : ℤ) (hy : 2 ≤ y) (hxy : y < x)
    (h : x ^ 2 + y ^ 2 - 2 * s * x * y = 1) :
    1 ≤ 2 * s * y - x ∧ 2 * s * y - x < y ∧
      y ^ 2 + (2 * s * y - x) ^ 2 - 2 * s * y * (2 * s * y - x) = 1 := by
  have hx : 0 < x := by linarith
  have hf : x * (2 * s * y - x) = y ^ 2 - 1 := by linear_combination (-1 : ℤ) * h
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc
    have hc' : 2 * s * y - x ≤ 0 := by
      have := not_le.mp hc
      linarith
    have h3 : x * (2 * s * y - x) ≤ x * 0 := mul_le_mul_of_nonneg_left hc' hx.le
    nlinarith
  · by_contra hc
    have h3 : x * y ≤ x * (2 * s * y - x) := mul_le_mul_of_nonneg_left (not_lt.mp hc) hx.le
    have h4 : y * y < x * y := mul_lt_mul_of_pos_right hxy (by linarith)
    nlinarith
  · linear_combination h

/-- The solutions of `m^2 + d^2 - 2 s m d = 1` with `1 ≤ d < m` and `s ≥ 3` have `m = 2 s` or `m ≥ 31`. -/
lemma core (m d s : ℤ) (hs : 3 ≤ s) (hd : 1 ≤ d) (hdm : d < m)
    (h : m ^ 2 + d ^ 2 - 2 * s * m * d = 1) : m = 2 * s ∨ 31 ≤ m := by
  rcases eq_or_lt_of_le hd with hd1 | hd2
  · left
    subst hd1
    have h0 : m * (m - 2 * s) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h0 with h0 | h0
    · linarith
    · linarith
  · right
    have hd2' : 2 ≤ d := by linarith
    obtain ⟨he1, he2, he3⟩ := descB m d s hd2' hdm h
    have h6 : 5 * (2 * s * d - m) + 1 ≤ d := descA d (2 * s * d - m) s hs he1 he2 he3
    have h7 : 5 * d + 1 ≤ m := descA m d s hs hd hdm h
    linarith

/-- A square `m * m` with `2 ≤ m ≤ 30` and `m` not of the form `4 i + 2` with `i ≥ 1` is a zero. -/
lemma zero_sq (n m : ℕ) (hn : n = m * m) (h2 : 2 ≤ m) (h30 : m ≤ 30) (hmod : m % 4 ≠ 2 ∨ m = 2) :
    IsZero n := by
  intro hex
  obtain ⟨k, j, hk, h⟩ := hex
  subst hn
  have h1 := two_T k
  have h2' := two_T j
  have hN : m * m * (k * (k + 1)) = j * (j + 1) := by
    rw [← h1, ← h2', ← h]
    ring
  have hZ : (m : ℤ) * m * ((k : ℤ) * ((k : ℤ) + 1)) = (j : ℤ) * ((j : ℤ) + 1) := by
    exact_mod_cast hN
  have hm2 : (2 : ℤ) ≤ m := by exact_mod_cast h2
  have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hdiff : ((m : ℤ) * (2 * k + 1) - (2 * j + 1)) * ((m : ℤ) * (2 * k + 1) + (2 * j + 1))
      = (m : ℤ) ^ 2 - 1 := by
    linear_combination 4 * hZ
  have hpos : (0 : ℤ) < (m : ℤ) * (2 * k + 1) + (2 * j + 1) := by positivity
  have hd1 : (1 : ℤ) ≤ (m : ℤ) * (2 * k + 1) - (2 * j + 1) := by
    by_contra hc
    have hc' : (m : ℤ) * (2 * k + 1) - (2 * j + 1) ≤ 0 := by
      have := not_le.mp hc
      linarith
    have h3 : ((m : ℤ) * (2 * k + 1) - (2 * j + 1)) * ((m : ℤ) * (2 * k + 1) + (2 * j + 1))
        ≤ 0 * ((m : ℤ) * (2 * k + 1) + (2 * j + 1)) := mul_le_mul_of_nonneg_right hc' hpos.le
    nlinarith
  have hdm : (m : ℤ) * (2 * k + 1) - (2 * j + 1) < m := by
    by_contra hc
    have h3 : (m : ℤ) * ((m : ℤ) * (2 * k + 1) + (2 * j + 1))
        ≤ ((m : ℤ) * (2 * k + 1) - (2 * j + 1)) * ((m : ℤ) * (2 * k + 1) + (2 * j + 1)) :=
      mul_le_mul_of_nonneg_right (not_lt.mp hc) hpos.le
    have h4 : (0 : ℤ) ≤ (m : ℤ) * m * k := by positivity
    have h5 : (0 : ℤ) ≤ (m : ℤ) * j := by positivity
    nlinarith
  have key : (m : ℤ) ^ 2 + ((m : ℤ) * (2 * k + 1) - (2 * j + 1)) ^ 2
      - 2 * (2 * (k : ℤ) + 1) * m * ((m : ℤ) * (2 * k + 1) - (2 * j + 1)) = 1 := by
    linear_combination (-4 : ℤ) * hZ
  rcases core (m : ℤ) ((m : ℤ) * (2 * k + 1) - (2 * j + 1)) (2 * (k : ℤ) + 1) (by linarith) hd1 hdm key
    with h5 | h5
  · omega
  · omega

/-- Every listed value is a zero. -/
lemma zero_of_L (n : ℕ) (h : n ∈ L) : IsZero n := by
  simp only [L, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact zero_sq n 2 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 3 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 4 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 5 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 7 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 8 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 9 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 11 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 12 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 13 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 15 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 16 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 17 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 19 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 20 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 21 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 23 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 24 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 25 (by omega) (by omega) (by omega) (by omega)
  · exact zero_sq n 27 (by omega) (by omega) (by omega) (by omega)

/-- Non-squares are not zeros (Pell, with the squared solution to fix parities). -/
lemma notzero_nonsq (n : ℕ) (hn : 1 ≤ n) (hsq : ¬ IsSquare (n : ℤ)) : ¬ IsZero n := by
  obtain ⟨x, y, hxy, hy0⟩ := Pell.exists_of_not_isSquare (by exact_mod_cast hn : (0 : ℤ) < n) hsq
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy0
  have hy1 : 1 ≤ y ^ 2 := by linarith
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have ha : 0 ≤ |x| := abs_nonneg x
  have hb : 0 ≤ |y| := abs_nonneg y
  have hab : |x| ^ 2 - (n : ℤ) * |y| ^ 2 = 1 := by rw [sq_abs, sq_abs]; exact hxy
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = n * |y| ^ 2 + |x| * |y| :=
    ⟨(n * |y| ^ 2 + |x| * |y|).toNat, Int.toNat_of_nonneg (by positivity)⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = n * |y| ^ 2 + n * (|x| * |y|) :=
    ⟨(n * |y| ^ 2 + n * (|x| * |y|)).toNat, Int.toNat_of_nonneg (by positivity)⟩
  have hk1 : 1 ≤ k := by
    have e1 : (1 : ℤ) ≤ n * |y| ^ 2 := by
      rw [sq_abs]
      nlinarith
    have e2 : (0 : ℤ) ≤ |x| * |y| := mul_nonneg ha hb
    have e3 : (1 : ℤ) ≤ k := by rw [hk]; linarith
    exact_mod_cast e3
  have hZ : (n : ℤ) * ((k : ℤ) * ((k : ℤ) + 1)) = (j : ℤ) * ((j : ℤ) + 1) := by
    rw [hk, hj]
    linear_combination ((n : ℤ) - (n : ℤ) ^ 2) * |y| ^ 2 * hab
  have hN : n * (k * (k + 1)) = j * (j + 1) := by exact_mod_cast hZ
  exact not_zero_of n k j hk1 (T_eq_of n k j hN)

/-- Every unlisted `n` with `1 ≤ n ≤ 729` is not a zero. -/
lemma notzero_of_notL (n : ℕ) (h1 : 1 ≤ n) (h729 : n ≤ 729) (hL : n ∉ L) : ¬ IsZero n := by
  by_cases hsq : IsSquare (n : ℤ)
  · obtain ⟨r, hr⟩ := hsq
    obtain ⟨a, ha⟩ : ∃ a : ℕ, n = a * a := by
      rcases le_total 0 r with h0 | h0
      · lift r to ℕ using h0
        exact ⟨r, by exact_mod_cast hr⟩
      · obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = -r :=
          ⟨(-r).toNat, Int.toNat_of_nonneg (by linarith)⟩
        refine ⟨t, ?_⟩
        have e : (n : ℤ) = t * t := by rw [ht, hr]; ring
        exact_mod_cast e
    subst ha
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0
        omega
      · exact h0
    have ha27 : a ≤ 27 := by nlinarith
    interval_cases a
    · exact not_zero_of _ 1 1 le_rfl (by decide)
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact not_zero_of _ 1 8 le_rfl (by decide)
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact not_zero_of _ 2 24 (by norm_num) (by decide)
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact not_zero_of _ 3 48 (by norm_num) (by decide)
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact not_zero_of _ 4 80 (by norm_num) (by decide)
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact not_zero_of _ 5 120 (by norm_num) (by decide)
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact (hL (by simp [L])).elim
    · exact not_zero_of _ 6 168 (by norm_num) (by decide)
    · exact (hL (by simp [L])).elim
  · exact notzero_nonsq n h1 hsq

end OMA.A227054Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a227054.main := by
  intro n hn1 hn729
  constructor
  · intro hz
    by_contra hL
    exact OMA.A227054Proof.notzero_of_notL n hn1 hn729 hL hz
  · intro hL
    exact OMA.A227054Proof.zero_of_L n hL
