import OMAStatements.S_oeis_a211481
import Mathlib

/-!
Credit: @ivillar
Proof: w = n - 2x - 3y is determined by (x, y), so a(n) counts the pairs (x, y) in [-n, n]^2
with 0 <= s = 2x + 3y <= 2n. The pairs with 2x + 3y = s are (3t - s, s - 2t) with t = x + y;
for s <= n the admissible t form the interval [-floor((n-s)/3), floor((n+s)/3)], and for s > n
the interval [ceil((s-n)/2), floor((n+s)/3)]. Summing over s gives
a(n) = F(3n+1) + floor(n/3) + 2n + 1 - B(n) with F(m) = Sum_{j<m} floor(j/3) and
B(n) = Sum_{i<n} floor((i+2)/2). Since F(3k+4) = F(3k+1) + 3k + 1, floor((k+3)/3) =
floor(k/3) + 1 and B(k+2) = B(k) + k + 2, the recurrence (denominator (1-x)(1-x^2)(1-x^3)) holds,
and with the first six terms the g.f.
-/

namespace OMAA211481Helpers
open PowerSeries OMA.S_oeis_a211481

/-- The pairs (x, y) in [-n, n]^2 with 0 ≤ 2x + 3y ≤ 2n. -/
noncomputable def P (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun p => 0 ≤ 2 * p.1 + 3 * p.2 ∧ 2 * p.1 + 3 * p.2 ≤ 2 * n)

theorem a_eq_P (n : ℕ) : a n = (P n).card := by
  unfold a P
  exact Finset.card_bij' (fun t _ => (t.2.1, t.2.2))
    (fun p _ => ((n : ℤ) - 2 * p.1 - 3 * p.2, p.1, p.2))
    (fun t ht => by
      obtain ⟨w, x, y⟩ := t
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢
      omega)
    (fun p hp => by
      obtain ⟨x, y⟩ := p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      omega)
    (fun t ht => by
      obtain ⟨w, x, y⟩ := t
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht
      exact Prod.ext (by dsimp only; omega) rfl)
    (fun p _ => rfl)

/-- The fiber size over s = 2x + 3y. -/
def g (n : ℕ) (s : ℤ) : ℤ :=
  if s ≤ n then ((n : ℤ) + s) / 3 + ((n : ℤ) - s) / 3 + 1
  else ((n : ℤ) + s) / 3 - (s - n + 1) / 2 + 1

theorem fiber_card (n : ℕ) (s : ℤ) (hs1 : 0 ≤ s) (hs2 : s ≤ 2 * n) :
    (((P n).filter (fun p => 2 * p.1 + 3 * p.2 = s)).card : ℤ) = g n s := by
  unfold g
  split_ifs with h
  · have hc : ((P n).filter (fun p => 2 * p.1 + 3 * p.2 = s)).card =
        (Finset.Icc (-(((n : ℤ) - s) / 3)) (((n : ℤ) + s) / 3)).card := by
      exact Finset.card_bij' (fun p _ => p.1 + p.2) (fun t _ => (3 * t - s, s - 2 * t))
        (fun p hp => by
          obtain ⟨x, y⟩ := p
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
          omega)
        (fun t ht => by
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢
          omega)
        (fun p hp => by
          obtain ⟨x, y⟩ := p
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
          exact Prod.ext (by dsimp only; omega) (by dsimp only; omega))
        (fun t _ => by dsimp only; ring)
    rw [hc, Int.card_Icc]
    omega
  · have hc : ((P n).filter (fun p => 2 * p.1 + 3 * p.2 = s)).card =
        (Finset.Icc ((s - n + 1) / 2) (((n : ℤ) + s) / 3)).card := by
      exact Finset.card_bij' (fun p _ => p.1 + p.2) (fun t _ => (3 * t - s, s - 2 * t))
        (fun p hp => by
          obtain ⟨x, y⟩ := p
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
          omega)
        (fun t ht => by
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢
          omega)
        (fun p hp => by
          obtain ⟨x, y⟩ := p
          simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
          exact Prod.ext (by dsimp only; omega) (by dsimp only; omega))
        (fun t _ => by dsimp only; ring)
    rw [hc, Int.card_Icc]
    omega

/-- F(m) = Sum_{j<m} floor(j/3). -/
def F (m : ℕ) : ℤ := ∑ j ∈ Finset.range m, ((j : ℤ) / 3)

/-- B(n) = Sum_{i<n} floor((i+2)/2). -/
def B (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, (((i : ℤ) + 2) / 2)

theorem P_sum (n : ℕ) : ((P n).card : ℤ) = ∑ k ∈ Finset.range (2 * n + 1), g n k := by
  have hmaps : ∀ p ∈ P n, 2 * p.1 + 3 * p.2 ∈ Finset.Icc (0 : ℤ) (2 * n) := by
    rintro ⟨x, y⟩ hp
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    omega
  have hf := Finset.card_eq_sum_card_fiberwise hmaps
  have hf' : ((P n).card : ℤ) = ∑ s ∈ Finset.Icc (0 : ℤ) (2 * n),
      (((P n).filter (fun p => 2 * p.1 + 3 * p.2 = s)).card : ℤ) := by
    rw [hf]
    push_cast
    rfl
  rw [hf', Finset.sum_congr rfl (fun s hs => fiber_card n s
    (by simp only [Finset.mem_Icc] at hs; omega) (by simp only [Finset.mem_Icc] at hs; omega))]
  exact Finset.sum_nbij' (fun s => s.toNat) (fun k => (k : ℤ))
    (fun s hs => by simp only [Finset.mem_Icc, Finset.mem_range] at hs ⊢; omega)
    (fun k hk => by simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega)
    (fun s hs => by simp only [Finset.mem_Icc] at hs; omega)
    (fun k _ => by simp)
    (fun s hs => by simp only [Finset.mem_Icc] at hs; rw [Int.toNat_of_nonneg (by omega)])

theorem a_closed (n : ℕ) :
    (a n : ℤ) = F (3 * n + 1) + (n : ℤ) / 3 + 2 * n + 1 - B n := by
  rw [a_eq_P, P_sum, show 2 * n + 1 = (n + 1) + n by ring, Finset.sum_range_add]
  have h1 : ∑ k ∈ Finset.range (n + 1), g n k =
      ∑ k ∈ Finset.range (n + 1), (((n + k : ℕ) : ℤ) / 3) +
        ∑ k ∈ Finset.range (n + 1), (((n + 1 - 1 - k : ℕ) : ℤ) / 3) + (n + 1) := by
    rw [← Finset.sum_add_distrib]
    have : ∑ k ∈ Finset.range (n + 1), g n k = ∑ k ∈ Finset.range (n + 1),
        ((((n + k : ℕ) : ℤ) / 3 + ((n + 1 - 1 - k : ℕ) : ℤ) / 3) + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      unfold g
      rw [if_pos (by omega), show n + 1 - 1 - k = n - k by omega,
        Nat.cast_sub (show k ≤ n by omega)]
      push_cast
      ring
    rw [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    push_cast
    ring
  have h2 : ∑ k ∈ Finset.range n, g n ((n + 1 + k : ℕ) : ℤ) =
      ∑ k ∈ Finset.range n, (((2 * n + 1 + k : ℕ) : ℤ) / 3) - B n + n := by
    unfold B
    rw [← Finset.sum_sub_distrib]
    have : ∑ k ∈ Finset.range n, g n ((n + 1 + k : ℕ) : ℤ) = ∑ k ∈ Finset.range n,
        ((((2 * n + 1 + k : ℕ) : ℤ) / 3 - ((k : ℤ) + 2) / 2) + 1) := by
      apply Finset.sum_congr rfl
      intro k _
      unfold g
      rw [if_neg (by push_cast; omega)]
      push_cast
      ring_nf
    rw [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    push_cast
    ring
  rw [h1, h2, Finset.sum_range_reflect (fun k => ((k : ℕ) : ℤ) / 3) (n + 1)]
  have e1 : ∑ k ∈ Finset.range (n + 1), (((n + k : ℕ) : ℤ) / 3) = F (2 * n + 1) - F n := by
    unfold F
    rw [← Finset.sum_range_add_sum_Ico _ (show n ≤ 2 * n + 1 by omega),
      Finset.sum_Ico_eq_sum_range, show 2 * n + 1 - n = n + 1 by omega]
    ring
  have e2 : ∑ k ∈ Finset.range n, (((2 * n + 1 + k : ℕ) : ℤ) / 3) =
      F (3 * n + 1) - F (2 * n + 1) := by
    unfold F
    rw [← Finset.sum_range_add_sum_Ico _ (show 2 * n + 1 ≤ 3 * n + 1 by omega),
      Finset.sum_Ico_eq_sum_range, show 3 * n + 1 - (2 * n + 1) = n by omega]
    ring
  have e3 : ∑ k ∈ Finset.range (n + 1), (((k : ℕ) : ℤ) / 3) = F n + (n : ℤ) / 3 := by
    unfold F
    rw [Finset.sum_range_succ]
  rw [e1, e2, e3]
  ring

theorem hF (k : ℕ) : F (3 * (k + 1) + 1) = F (3 * k + 1) + 3 * k + 1 := by
  unfold F
  rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  omega

theorem hB (k : ℕ) : B (k + 2) = B k + k + 2 := by
  unfold B
  rw [show k + 2 = k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  omega

theorem rec (m : ℕ) : (a (m + 6) : ℤ) = a (m + 5) + a (m + 4) - a (m + 2) - a (m + 1) +
    a m := by
  rw [a_closed, a_closed, a_closed, a_closed, a_closed, a_closed]
  have f1 : F (3 * (m + 1) + 1) = F (3 * m + 1) + 3 * (m : ℤ) + 1 := by
    have := hF m; linarith
  have f2 : F (3 * (m + 2) + 1) = F (3 * (m + 1) + 1) + 3 * ((m : ℤ) + 1) + 1 := by
    have := hF (m + 1); push_cast at this; linarith
  have f3 : F (3 * (m + 3) + 1) = F (3 * (m + 2) + 1) + 3 * ((m : ℤ) + 2) + 1 := by
    have := hF (m + 2); push_cast at this; linarith
  have f4 : F (3 * (m + 4) + 1) = F (3 * (m + 3) + 1) + 3 * ((m : ℤ) + 3) + 1 := by
    have := hF (m + 3); push_cast at this; linarith
  have f5 : F (3 * (m + 5) + 1) = F (3 * (m + 4) + 1) + 3 * ((m : ℤ) + 4) + 1 := by
    have := hF (m + 4); push_cast at this; linarith
  have f6 : F (3 * (m + 6) + 1) = F (3 * (m + 5) + 1) + 3 * ((m : ℤ) + 5) + 1 := by
    have := hF (m + 5); push_cast at this; linarith
  have b2 : B (m + 2) = B m + m + 2 := by have := hB m; linarith
  have b3 : B (m + 3) = B (m + 1) + m + 3 := by have := hB (m + 1); push_cast at this; linarith
  have b4 : B (m + 4) = B (m + 2) + m + 4 := by have := hB (m + 2); push_cast at this; linarith
  have b5 : B (m + 5) = B (m + 3) + m + 5 := by have := hB (m + 3); push_cast at this; linarith
  have b6 : B (m + 6) = B (m + 4) + m + 6 := by have := hB (m + 4); push_cast at this; linarith
  push_cast
  omega

theorem coeff_mk_mul_X_pow (f : ℕ → ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_at (f : ℕ → ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * X ^ k) = f j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

end OMAA211481Helpers

open PowerSeries OMAA211481Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a211481.main := by
  have hrec : ∀ n : ℕ, 5 < n → (OMA.S_oeis_a211481.a n : ℤ) =
      OMA.S_oeis_a211481.a (n - 1) + OMA.S_oeis_a211481.a (n - 2) -
        OMA.S_oeis_a211481.a (n - 4) - OMA.S_oeis_a211481.a (n - 5) +
          OMA.S_oeis_a211481.a (n - 6) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega,
      show m + 6 - 6 = m by omega]
    exact rec m
  refine ⟨?_, hrec⟩
  set f : ℕ → ℤ := fun n => (OMA.S_oeis_a211481.a n : ℤ) with hfdef
  ext n
  have hD : ((X - 1) ^ 3 * (X + 1) * (X ^ 2 + X + 1) : PowerSeries ℤ) =
      X ^ 6 - X ^ 5 - X ^ 4 + X ^ 2 + X ^ 1 - X ^ 0 := by
    ring
  have hN : (-(3 * X ^ 4 + 5 * X ^ 3 + 4 * X ^ 2 + 2 * X + 1) : PowerSeries ℤ) =
      -(C 3 * X ^ 4) - C 5 * X ^ 3 - C 4 * X ^ 2 - C 2 * X ^ 1 - X ^ 0 := by
    rw [map_ofNat C 3, map_ofNat C 5, map_ofNat C 4, map_ofNat C 2]; ring
  rw [hD, hN]
  have v0 : f 0 = 1 := by
    simp only [hfdef, a_closed, F, B]; norm_num [Finset.sum_range_succ]
  have v1 : f 1 = 3 := by
    simp only [hfdef, a_closed, F, B]; norm_num [Finset.sum_range_succ]
  have v2 : f 2 = 8 := by
    simp only [hfdef, a_closed, F, B]; norm_num [Finset.sum_range_succ]
  have v3 : f 3 = 16 := by
    simp only [hfdef, a_closed, F, B]; norm_num [Finset.sum_range_succ]
  have v4 : f 4 = 26 := by
    simp only [hfdef, a_closed, F, B]; norm_num [Finset.sum_range_succ]
  have v5 : f 5 = 38 := by
    simp only [hfdef, a_closed, F, B]; norm_num [Finset.sum_range_succ]
  rcases Nat.lt_or_ge n 6 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, map_neg, coeff_mk_mul_X_pow, coeff_C_mul,
      coeff_X_pow]
    interval_cases n
    · norm_num [v0]
    · norm_num [v0, v1]
    · norm_num [v0, v1, v2]
    · norm_num [v1, v2, v3]
    · norm_num [v0, v2, v3, v4]
    · norm_num [v0, v1, v3, v4, v5]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub, map_neg]
    rw [coeff_at f (m + 6) 6 m (by omega), coeff_at f (m + 6) 5 (m + 1) (by omega),
      coeff_at f (m + 6) 4 (m + 2) (by omega), coeff_at f (m + 6) 2 (m + 4) (by omega),
      coeff_at f (m + 6) 1 (m + 5) (by omega), coeff_at f (m + 6) 0 (m + 6) (by omega),
      coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow,
      coeff_X_pow, coeff_X_pow, coeff_X_pow, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hr := rec m
    simp only [hfdef]
    linear_combination -hr
