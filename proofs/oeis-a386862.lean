import OMAStatements.S_oeis_a386862
import Mathlib

namespace OMA.T386862

open Finset OMA.S_oeis_a386862

/-- Shifting a factorial. -/
lemma fsh (E : ℕ) : ∀ j : ℕ, ((E + j).factorial : ℚ)
    = (∏ i ∈ Finset.range j, ((E : ℚ) + (i : ℚ) + 1)) * (E.factorial : ℚ)
  | 0 => by simp
  | j + 1 => by
    rw [show E + (j + 1) = (E + j) + 1 from rfl, Nat.factorial_succ, Finset.prod_range_succ]
    push_cast
    rw [fsh E j]
    ring

/-- The summand in factorial form, as a function of k and t = n - k. -/
noncomputable def Φ (k t : ℕ) : ℚ :=
  (1 : ℚ) ^ k * (2 : ℚ) ^ t * ((2 * k + 2 * t + 1).factorial : ℚ)
    / (((k).factorial : ℚ) * ((k + 2 * t + 1).factorial : ℚ)) * ((k + 2 * t).factorial : ℚ)
    / (((t).factorial : ℚ) * ((k + t).factorial : ℚ))
    * ((1 * ((k : ℚ) + (t : ℚ))) / (1 * (k : ℚ) + 2 * (t : ℚ)))

/-- The summand of the sequence. -/
def F (n k : ℕ) : ℤ :=
  (1 : ℤ) ^ k * (2 : ℤ) ^ (n - k) * ((2 * n + 1).choose k : ℤ) * ((2 * n - k - 1).choose (n - k) : ℤ)

lemma a_eq (n : ℕ) : a n = ∑ k ∈ Finset.range (n + 1), F n k := by
  unfold a
  apply Finset.sum_congr rfl
  intro k _
  unfold F
  ring

lemma F_eq (k t : ℕ) (hkt : 1 ≤ k + t) : (F (k + t) k : ℚ) = Φ k t := by
  have h1 : ((2 * (k + t) + 1).choose k : ℚ)
      = ((2 * k + 2 * t + 1).factorial : ℚ) / ((k.factorial : ℚ) * ((k + 2 * t + 1).factorial : ℚ)) := by
    rw [Nat.cast_choose ℚ (by omega : k ≤ 2 * (k + t) + 1)]
    rw [show 2 * (k + t) + 1 - k = k + 2 * t + 1 from by omega,
      show 2 * (k + t) + 1 = 2 * k + 2 * t + 1 from by ring]
  have hC : 1 ≤ k + 2 * t := by omega
  have hD : 1 ≤ k + t := by omega
  have fC : (((k + 2 * t).factorial : ℕ) : ℚ) = ((k + 2 * t : ℕ) : ℚ) * (((k + 2 * t - 1).factorial : ℕ) : ℚ) := by
    rw [← Nat.mul_factorial_pred (by omega : k + 2 * t ≠ 0)]
    push_cast
    ring
  have fD : (((k + t).factorial : ℕ) : ℚ) = ((k + t : ℕ) : ℚ) * (((k + t - 1).factorial : ℕ) : ℚ) := by
    rw [← Nat.mul_factorial_pred (by omega : k + t ≠ 0)]
    push_cast
    ring
  have h2 : ((2 * (k + t) - k - 1).choose t : ℚ)
      = (((k + 2 * t - 1).factorial : ℕ) : ℚ) / ((t.factorial : ℚ) * (((k + t - 1).factorial : ℕ) : ℚ)) := by
    rw [show 2 * (k + t) - k - 1 = k + 2 * t - 1 from by omega]
    rw [Nat.cast_choose ℚ (by omega : t ≤ k + 2 * t - 1)]
    rw [show k + 2 * t - 1 - t = k + t - 1 from by omega]
  have hCq : (((k + 2 * t : ℕ) : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hDq : (((k + t : ℕ) : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hC1 : ((((k + 2 * t - 1).factorial : ℕ) : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hD1 : ((((k + t - 1).factorial : ℕ) : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk1 : ((k.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have ht1 : ((t.factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hB1 : (((k + 2 * t + 1).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfac : ((1 * ((k : ℚ) + (t : ℚ))) / (1 * (k : ℚ) + 2 * (t : ℚ)))
      = ((k + t : ℕ) : ℚ) / ((k + 2 * t : ℕ) : ℚ) := by
    push_cast
    ring
  unfold F Φ
  push_cast [Nat.add_sub_cancel_left]
  rw [h1, h2]
  rw [fC, fD]
  have hfac' := hfac
  push_cast at hfac' hCq hDq ⊢
  rw [hfac']
  field_simp


set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- The certificate, as a rational function of x = m and y = k (with n = m + 3). -/
noncomputable def Rc (x y : ℚ) : ℚ :=
  (-(32096 : ℚ) * x ^ (8 : ℕ) * y + (96816 : ℚ) * x ^ (7 : ℕ) * y ^ (2 : ℕ) - (494864 : ℚ) * x ^ (7
      : ℕ) * y - (122544 : ℚ) * x ^ (6 : ℕ) * y ^ (3 : ℕ) + (1291344 : ℚ) * x ^ (6 : ℕ) * y ^ (2
      : ℕ) - (3197768 : ℚ) * x ^ (6 : ℕ) * y + (83720 : ℚ) * x ^ (5 : ℕ) * y ^ (4 : ℕ) -
      (1371160 : ℚ) * x ^ (5 : ℕ) * y ^ (3 : ℕ) + (7057124 : ℚ) * x ^ (5 : ℕ) * y ^ (2 : ℕ) -
      (11245580 : ℚ) * x ^ (5 : ℕ) * y - (32910 : ℚ) * x ^ (4 : ℕ) * y ^ (5 : ℕ) + (751120 : ℚ)
      * x ^ (4 : ℕ) * y ^ (4 : ℕ) - (6094346 : ℚ) * x ^ (4 : ℕ) * y ^ (3 : ℕ) + (20375896 : ℚ) *
      x ^ (4 : ℕ) * y ^ (2 : ℕ) - (23393480 : ℚ) * x ^ (4 : ℕ) * y + (7263 : ℚ) * x ^ (3 : ℕ) *
      y ^ (6 : ℕ) - (220185 : ℚ) * x ^ (3 : ℕ) * y ^ (5 : ℕ) + (2555379 : ℚ) * x ^ (3 : ℕ) * y ^
      (4 : ℕ) - (13706775 : ℚ) * x ^ (3 : ℕ) * y ^ (3 : ℕ) + (33395514 : ℚ) * x ^ (3 : ℕ) * y ^
      (2 : ℕ) - (29295524 : ℚ) * x ^ (3 : ℕ) * y - (788 : ℚ) * x ^ (2 : ℕ) * y ^ (7 : ℕ) +
      (31667 : ℚ) * x ^ (2 : ℕ) * y ^ (6 : ℕ) - (515047 : ℚ) * x ^ (2 : ℕ) * y ^ (5 : ℕ) +
      (4096923 : ℚ) * x ^ (2 : ℕ) * y ^ (4 : ℕ) - (16367965 : ℚ) * x ^ (2 : ℕ) * y ^ (3 : ℕ) +
      (30898466 : ℚ) * x ^ (2 : ℕ) * y ^ (2 : ℕ) - (21421464 : ℚ) * x ^ (2 : ℕ) * y + (27 : ℚ) *
      x * y ^ (8 : ℕ) - (1602 : ℚ) * x * y ^ (7 : ℕ) + (39916 : ℚ) * x * y ^ (6 : ℕ) - (490546 :
      ℚ) * x * y ^ (5 : ℕ) + (3056649 : ℚ) * x * y ^ (4 : ℕ) - (9722836 : ℚ) * x * y ^ (3 : ℕ) +
      (14738656 : ℚ) * x * y ^ (2 : ℕ) - (8214984 : ℚ) * x * y - (292 : ℚ) * y ^ (7 : ℕ) +
      (12320 : ℚ) * y ^ (6 : ℕ) - (148680 : ℚ) * y ^ (5 : ℕ) + (801664 : ℚ) * y ^ (4 : ℕ) -
      (2113892 : ℚ) * y ^ (3 : ℕ) + (2596704 : ℚ) * y ^ (2 : ℕ) - (1147824 : ℚ) * y)
    / (16 * (x + 3) * (2 * x + 5) * (2 * x + 7) * (2 * x - y + 5) * (2 * x - y + 4) * (2 * x - y + 3) * (2 * x - y + 2) * (2 * x - y + 1))

/-- The telescoping term. -/
noncomputable def Gf (m k : ℕ) : ℚ := Rc m k * Φ k (m + 3 - k)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma RcAA (k t : ℕ) : Rc ((k + t + 1 : ℕ) : ℚ) ((k + 2 : ℕ) : ℚ)
    = (-(512 : ℚ) * (k : ℚ) ^ (9 : ℕ) - (7120 : ℚ) * (k : ℚ) ^ (8 : ℕ) * (t : ℚ) - (15776 : ℚ) * (k :
      ℚ) ^ (8 : ℕ) - (42971 : ℚ) * (k : ℚ) ^ (7 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (194105 : ℚ) * (k :
      ℚ) ^ (7 : ℕ) * (t : ℚ) - (210566 : ℚ) * (k : ℚ) ^ (7 : ℕ) - (146873 : ℚ) * (k : ℚ) ^ (6 :
      ℕ) * (t : ℚ) ^ (3 : ℕ) - (1016727 : ℚ) * (k : ℚ) ^ (6 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (2251558
      : ℚ) * (k : ℚ) ^ (6 : ℕ) * (t : ℚ) - (1589304 : ℚ) * (k : ℚ) ^ (6 : ℕ) - (310630 : ℚ) * (k
      : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (2940621 : ℚ) * (k : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (3 : ℕ)
      - (10003211 : ℚ) * (k : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (14443920 : ℚ) * (k : ℚ) ^ (5 :
      ℕ) * (t : ℚ) - (7436412 : ℚ) * (k : ℚ) ^ (5 : ℕ) - (415784 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t :
      ℚ) ^ (5 : ℕ) - (5082140 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (23738755 : ℚ) * (k
      : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (3 : ℕ) - (52836541 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (2 :
      ℕ) - (55817982 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) - (22267872 : ℚ) * (k : ℚ) ^ (4 : ℕ) -
      (343520 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (6 : ℕ) - (5280392 : ℚ) * (k : ℚ) ^ (3 : ℕ) *
      (t : ℚ) ^ (5 : ℕ) - (32083766 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (98624887 :
      ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (3 : ℕ) - (161393654 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ)
      ^ (2 : ℕ) - (132715515 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) - (42547318 : ℚ) * (k : ℚ) ^ (3
      : ℕ) - (159952 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (7 : ℕ) - (3114160 : ℚ) * (k : ℚ) ^ (2
      : ℕ) * (t : ℚ) ^ (6 : ℕ) - (24155788 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (5 : ℕ) -
      (97578460 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (222228832 : ℚ) * (k : ℚ) ^ (2 :
      ℕ) * (t : ℚ) ^ (3 : ℕ) - (284905492 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (2 : ℕ) -
      (189466844 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) - (49983016 : ℚ) * (k : ℚ) ^ (2 : ℕ) -
      (32096 : ℚ) * (k : ℚ) * (t : ℚ) ^ (8 : ℕ) - (877904 : ℚ) * (k : ℚ) * (t : ℚ) ^ (7 : ℕ) -
      (8966808 : ℚ) * (k : ℚ) * (t : ℚ) ^ (6 : ℕ) - (47217276 : ℚ) * (k : ℚ) * (t : ℚ) ^ (5 : ℕ)
      - (143145308 : ℚ) * (k : ℚ) * (t : ℚ) ^ (4 : ℕ) - (257751688 : ℚ) * (k : ℚ) * (t : ℚ) ^ (3
      : ℕ) - (269284164 : ℚ) * (k : ℚ) * (t : ℚ) ^ (2 : ℕ) - (148507276 : ℚ) * (k : ℚ) * (t : ℚ)
      - (32752648 : ℚ) * (k : ℚ) - (64192 : ℚ) * (t : ℚ) ^ (8 : ℕ) - (1116000 : ℚ) * (t : ℚ) ^
      (7 : ℕ) - (8225136 : ℚ) * (t : ℚ) ^ (6 : ℕ) - (33401992 : ℚ) * (t : ℚ) ^ (5 : ℕ) -
      (81272824 : ℚ) * (t : ℚ) ^ (4 : ℕ) - (120467064 : ℚ) * (t : ℚ) ^ (3 : ℕ) - (105243448 : ℚ)
      * (t : ℚ) ^ (2 : ℕ) - (48912032 : ℚ) * (t : ℚ) - (9091488 : ℚ))
      / (16 * ((k : ℚ) + (t : ℚ) + 4) * (2 * (k : ℚ) + 2 * (t : ℚ) + 7) * (2 * (k : ℚ) + 2 * (t : ℚ) + 9) * ((k : ℚ) + 2 * (t : ℚ) + 5) * ((k : ℚ) + 2 * (t : ℚ) + 4) * ((k : ℚ) + 2 * (t : ℚ) + 3) * ((k : ℚ) + 2 * (t : ℚ) + 2) * ((k : ℚ) + 2 * (t : ℚ) + 1)) := by
  have e : (16 * (((k + t + 1 : ℕ) : ℚ) + 3) * (2 * ((k + t + 1 : ℕ) : ℚ) + 5) * (2 * ((k + t + 1 : ℕ) : ℚ) + 7) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 2 : ℕ) : ℚ) + 5) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 2 : ℕ) : ℚ) + 4) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 2 : ℕ) : ℚ) + 3) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 2 : ℕ) : ℚ) + 2) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 2 : ℕ) : ℚ) + 1) : ℚ) = 16 * ((k : ℚ) + (t : ℚ) + 4) * (2 * (k : ℚ) + 2 * (t : ℚ) + 7) * (2 * (k : ℚ) + 2 * (t : ℚ) + 9) * ((k : ℚ) + 2 * (t : ℚ) + 5) * ((k : ℚ) + 2 * (t : ℚ) + 4) * ((k : ℚ) + 2 * (t : ℚ) + 3) * ((k : ℚ) + 2 * (t : ℚ) + 2) * ((k : ℚ) + 2 * (t : ℚ) + 1) := by
    push_cast
    ring
  have hpos : (16 * ((k : ℚ) + (t : ℚ) + 4) * (2 * (k : ℚ) + 2 * (t : ℚ) + 7) * (2 * (k : ℚ) + 2 * (t : ℚ) + 9) * ((k : ℚ) + 2 * (t : ℚ) + 5) * ((k : ℚ) + 2 * (t : ℚ) + 4) * ((k : ℚ) + 2 * (t : ℚ) + 3) * ((k : ℚ) + 2 * (t : ℚ) + 2) * ((k : ℚ) + 2 * (t : ℚ) + 1) : ℚ) ≠ 0 := by positivity
  have horig : (16 * (((k + t + 1 : ℕ) : ℚ) + 3) * (2 * ((k + t + 1 : ℕ) : ℚ) + 5) * (2 * ((k + t + 1 : ℕ) : ℚ) + 7) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 2 : ℕ) : ℚ) + 5) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 2 : ℕ) : ℚ) + 4) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 2 : ℕ) : ℚ) + 3) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 2 : ℕ) : ℚ) + 2) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 2 : ℕ) : ℚ) + 1) : ℚ) ≠ 0 := by
    rw [e]
    exact hpos
  unfold Rc
  rw [div_eq_div_iff horig hpos]
  push_cast
  ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma RcBA (k t : ℕ) : Rc ((k + t + 1 : ℕ) : ℚ) ((k + 1 : ℕ) : ℚ)
    = (-(512 : ℚ) * (k : ℚ) ^ (9 : ℕ) - (7120 : ℚ) * (k : ℚ) ^ (8 : ℕ) * (t : ℚ) - (18288 : ℚ) * (k :
      ℚ) ^ (8 : ℕ) - (42971 : ℚ) * (k : ℚ) ^ (7 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (223087 : ℚ) * (k :
      ℚ) ^ (7 : ℕ) * (t : ℚ) - (282906 : ℚ) * (k : ℚ) ^ (7 : ℕ) - (146873 : ℚ) * (k : ℚ) ^ (6 :
      ℕ) * (t : ℚ) ^ (3 : ℕ) - (1156549 : ℚ) * (k : ℚ) ^ (6 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (2964662
      : ℚ) * (k : ℚ) ^ (6 : ℕ) * (t : ℚ) - (2469048 : ℚ) * (k : ℚ) ^ (6 : ℕ) - (310630 : ℚ) * (k
      : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (3301903 : ℚ) * (k : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (3 : ℕ)
      - (12847169 : ℚ) * (k : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (21643206 : ℚ) * (k : ℚ) ^ (5 :
      ℕ) * (t : ℚ) - (13290840 : ℚ) * (k : ℚ) ^ (5 : ℕ) - (415784 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t
      : ℚ) ^ (5 : ℕ) - (5607910 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (29512545 : ℚ) *
      (k : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (3 : ℕ) - (75615421 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (2
      : ℕ) - (94122404 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) - (45422772 : ℚ) * (k : ℚ) ^ (4 : ℕ) -
      (343520 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (6 : ℕ) - (5678376 : ℚ) * (k : ℚ) ^ (3 : ℕ) *
      (t : ℚ) ^ (5 : ℕ) - (38100586 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (132627601 :
      ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (3 : ℕ) - (252159292 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ)
      ^ (2 : ℕ) - (247753947 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) - (98039758 : ℚ) * (k : ℚ) ^ (3
      : ℕ) - (159952 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (7 : ℕ) - (3203264 : ℚ) * (k : ℚ) ^ (2
      : ℕ) * (t : ℚ) ^ (6 : ℕ) - (26669908 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (5 : ℕ) -
      (119612602 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (311801874 : ℚ) * (k : ℚ) ^ (2 :
      ℕ) * (t : ℚ) ^ (3 : ℕ) - (471799302 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (2 : ℕ) -
      (383079286 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) - (128520996 : ℚ) * (k : ℚ) ^ (2 : ℕ) -
      (32096 : ℚ) * (k : ℚ) * (t : ℚ) ^ (8 : ℕ) - (814768 : ℚ) * (k : ℚ) * (t : ℚ) ^ (7 : ℕ) -
      (8573736 : ℚ) * (k : ℚ) * (t : ℚ) ^ (6 : ℕ) - (49213404 : ℚ) * (k : ℚ) * (t : ℚ) ^ (5 : ℕ)
      - (169195416 : ℚ) * (k : ℚ) * (t : ℚ) ^ (4 : ℕ) - (357438372 : ℚ) * (k : ℚ) * (t : ℚ) ^ (3
      : ℕ) - (453406528 : ℚ) * (k : ℚ) * (t : ℚ) ^ (2 : ℕ) - (315668624 : ℚ) * (k : ℚ) * (t : ℚ)
      - (92283072 : ℚ) * (k : ℚ) - (32096 : ℚ) * (t : ℚ) ^ (8 : ℕ) - (654816 : ℚ) * (t : ℚ) ^ (7
      : ℕ) - (5713992 : ℚ) * (t : ℚ) ^ (6 : ℕ) - (27806088 : ℚ) * (t : ℚ) ^ (5 : ℕ) - (82386120
      : ℚ) * (t : ℚ) ^ (4 : ℕ) - (151906584 : ℚ) * (t : ℚ) ^ (3 : ℕ) - (169884688 : ℚ) * (t : ℚ)
      ^ (2 : ℕ) - (105115392 : ℚ) * (t : ℚ) - (27465984 : ℚ))
      / (16 * ((k : ℚ) + (t : ℚ) + 4) * (2 * (k : ℚ) + 2 * (t : ℚ) + 7) * (2 * (k : ℚ) + 2 * (t : ℚ) + 9) * ((k : ℚ) + 2 * (t : ℚ) + 6) * ((k : ℚ) + 2 * (t : ℚ) + 5) * ((k : ℚ) + 2 * (t : ℚ) + 4) * ((k : ℚ) + 2 * (t : ℚ) + 3) * ((k : ℚ) + 2 * (t : ℚ) + 2)) := by
  have e : (16 * (((k + t + 1 : ℕ) : ℚ) + 3) * (2 * ((k + t + 1 : ℕ) : ℚ) + 5) * (2 * ((k + t + 1 : ℕ) : ℚ) + 7) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ) + 5) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ) + 4) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ) + 3) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ) + 2) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ) + 1) : ℚ) = 16 * ((k : ℚ) + (t : ℚ) + 4) * (2 * (k : ℚ) + 2 * (t : ℚ) + 7) * (2 * (k : ℚ) + 2 * (t : ℚ) + 9) * ((k : ℚ) + 2 * (t : ℚ) + 6) * ((k : ℚ) + 2 * (t : ℚ) + 5) * ((k : ℚ) + 2 * (t : ℚ) + 4) * ((k : ℚ) + 2 * (t : ℚ) + 3) * ((k : ℚ) + 2 * (t : ℚ) + 2) := by
    push_cast
    ring
  have hpos : (16 * ((k : ℚ) + (t : ℚ) + 4) * (2 * (k : ℚ) + 2 * (t : ℚ) + 7) * (2 * (k : ℚ) + 2 * (t : ℚ) + 9) * ((k : ℚ) + 2 * (t : ℚ) + 6) * ((k : ℚ) + 2 * (t : ℚ) + 5) * ((k : ℚ) + 2 * (t : ℚ) + 4) * ((k : ℚ) + 2 * (t : ℚ) + 3) * ((k : ℚ) + 2 * (t : ℚ) + 2) : ℚ) ≠ 0 := by positivity
  have horig : (16 * (((k + t + 1 : ℕ) : ℚ) + 3) * (2 * ((k + t + 1 : ℕ) : ℚ) + 5) * (2 * ((k + t + 1 : ℕ) : ℚ) + 7) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ) + 5) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ) + 4) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ) + 3) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ) + 2) * (2 * ((k + t + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ) + 1) : ℚ) ≠ 0 := by
    rw [e]
    exact hpos
  unfold Rc
  rw [div_eq_div_iff horig hpos]
  push_cast
  ring

lemma interiorA_phi0 (k t : ℕ) : Φ (k + 1) (t)
    = (1 : ℚ) ^ (k + 1) * (2 : ℚ) ^ (t) * ((2 * k + 2 * t + 3).factorial : ℚ)
      / (((k + 1).factorial : ℚ) * ((k + 2 * t + 1 + 1).factorial : ℚ)) * ((k + 2 * t + 1).factorial : ℚ)
      / (((t).factorial : ℚ) * ((k + t + 1).factorial : ℚ))
      * (((k : ℚ) + (t : ℚ) + 1) / ((k : ℚ) + 2 * (t : ℚ) + 1)) := by
  unfold Φ
  have e0 : 2 * (k + 1) + 2 * t + 1 = 2 * k + 2 * t + 3 := by ring
  have e1 : (k + 1) + 2 * t + 1 = k + 2 * t + 1 + 1 := by ring
  have e2 : (k + 1) + 2 * t = k + 2 * t + 1 := by ring
  have e3 : (k + 1) + t = k + t + 1 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try push_cast
  try ring

lemma interiorA_phi1 (k t : ℕ) : Φ (k + 1) (t + 1)
    = (1 : ℚ) ^ (k + 1) * (2 : ℚ) ^ (t + 1) * ((2 * k + 2 * t + 3 + 2).factorial : ℚ)
      / (((k + 1).factorial : ℚ) * ((k + 2 * t + 1 + 3).factorial : ℚ)) * ((k + 2 * t + 1 + 2).factorial : ℚ)
      / (((t + 1).factorial : ℚ) * ((k + t + 1 + 1).factorial : ℚ))
      * (((k : ℚ) + (t : ℚ) + 2) / ((k : ℚ) + 2 * (t : ℚ) + 3)) := by
  unfold Φ
  have e0 : 2 * (k + 1) + 2 * (t + 1) + 1 = 2 * k + 2 * t + 3 + 2 := by ring
  have e1 : (k + 1) + 2 * (t + 1) + 1 = k + 2 * t + 1 + 3 := by ring
  have e2 : (k + 1) + 2 * (t + 1) = k + 2 * t + 1 + 2 := by ring
  have e3 : (k + 1) + (t + 1) = k + t + 1 + 1 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try push_cast
  try ring

lemma interiorA_phi2 (k t : ℕ) : Φ (k + 1) (t + 2)
    = (1 : ℚ) ^ (k + 1) * (2 : ℚ) ^ (t + 2) * ((2 * k + 2 * t + 3 + 4).factorial : ℚ)
      / (((k + 1).factorial : ℚ) * ((k + 2 * t + 1 + 5).factorial : ℚ)) * ((k + 2 * t + 1 + 4).factorial : ℚ)
      / (((t + 2).factorial : ℚ) * ((k + t + 1 + 2).factorial : ℚ))
      * (((k : ℚ) + (t : ℚ) + 3) / ((k : ℚ) + 2 * (t : ℚ) + 5)) := by
  unfold Φ
  have e0 : 2 * (k + 1) + 2 * (t + 2) + 1 = 2 * k + 2 * t + 3 + 4 := by ring
  have e1 : (k + 1) + 2 * (t + 2) + 1 = k + 2 * t + 1 + 5 := by ring
  have e2 : (k + 1) + 2 * (t + 2) = k + 2 * t + 1 + 4 := by ring
  have e3 : (k + 1) + (t + 2) = k + t + 1 + 2 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try push_cast
  try ring

lemma interiorA_phi3 (k t : ℕ) : Φ (k + 1) (t + 3)
    = (1 : ℚ) ^ (k + 1) * (2 : ℚ) ^ (t + 3) * ((2 * k + 2 * t + 3 + 6).factorial : ℚ)
      / (((k + 1).factorial : ℚ) * ((k + 2 * t + 1 + 7).factorial : ℚ)) * ((k + 2 * t + 1 + 6).factorial : ℚ)
      / (((t + 3).factorial : ℚ) * ((k + t + 1 + 3).factorial : ℚ))
      * (((k : ℚ) + (t : ℚ) + 4) / ((k : ℚ) + 2 * (t : ℚ) + 7)) := by
  unfold Φ
  have e0 : 2 * (k + 1) + 2 * (t + 3) + 1 = 2 * k + 2 * t + 3 + 6 := by ring
  have e1 : (k + 1) + 2 * (t + 3) + 1 = k + 2 * t + 1 + 7 := by ring
  have e2 : (k + 1) + 2 * (t + 3) = k + 2 * t + 1 + 6 := by ring
  have e3 : (k + 1) + (t + 3) = k + t + 1 + 3 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try push_cast
  try ring

lemma interiorA_phi4 (k t : ℕ) : Φ (k + 2) (t + 2)
    = (1 : ℚ) ^ (k + 2) * (2 : ℚ) ^ (t + 2) * ((2 * k + 2 * t + 3 + 6).factorial : ℚ)
      / (((k + 1 + 1).factorial : ℚ) * ((k + 2 * t + 1 + 6).factorial : ℚ)) * ((k + 2 * t + 1 + 5).factorial : ℚ)
      / (((t + 2).factorial : ℚ) * ((k + t + 1 + 3).factorial : ℚ))
      * (((k : ℚ) + (t : ℚ) + 4) / ((k : ℚ) + 2 * (t : ℚ) + 6)) := by
  unfold Φ
  have e0 : 2 * (k + 2) + 2 * (t + 2) + 1 = 2 * k + 2 * t + 3 + 6 := by ring
  have e1 : (k + 2) + 2 * (t + 2) + 1 = k + 2 * t + 1 + 6 := by ring
  have e2 : (k + 2) + 2 * (t + 2) = k + 2 * t + 1 + 5 := by ring
  have e3 : (k + 2) + (t + 2) = k + t + 1 + 3 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try push_cast
  try ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma interiorA (k t : ℕ) :
    (-324 * (k : ℚ) - 324 * (t : ℚ) - 810) * Φ (k + 1) (t) + (-669 * (k : ℚ) - 669 * (t : ℚ) - 1107)
      * Φ (k + 1) (t + 1) + (-38 * (k : ℚ) - 38 * (t : ℚ) - 208) * Φ (k + 1) (t + 2) + (8 * (k :
      ℚ) + 8 * (t : ℚ) + 32) * Φ (k + 1) (t + 3)
    = (-(512 : ℚ) * (k : ℚ) ^ (9 : ℕ) - (7120 : ℚ) * (k : ℚ) ^ (8 : ℕ) * (t : ℚ) - (15776 : ℚ) * (k :
      ℚ) ^ (8 : ℕ) - (42971 : ℚ) * (k : ℚ) ^ (7 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (194105 : ℚ) * (k :
      ℚ) ^ (7 : ℕ) * (t : ℚ) - (210566 : ℚ) * (k : ℚ) ^ (7 : ℕ) - (146873 : ℚ) * (k : ℚ) ^ (6 :
      ℕ) * (t : ℚ) ^ (3 : ℕ) - (1016727 : ℚ) * (k : ℚ) ^ (6 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (2251558
      : ℚ) * (k : ℚ) ^ (6 : ℕ) * (t : ℚ) - (1589304 : ℚ) * (k : ℚ) ^ (6 : ℕ) - (310630 : ℚ) * (k
      : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (2940621 : ℚ) * (k : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (3 : ℕ)
      - (10003211 : ℚ) * (k : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (14443920 : ℚ) * (k : ℚ) ^ (5 :
      ℕ) * (t : ℚ) - (7436412 : ℚ) * (k : ℚ) ^ (5 : ℕ) - (415784 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t :
      ℚ) ^ (5 : ℕ) - (5082140 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (23738755 : ℚ) * (k
      : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (3 : ℕ) - (52836541 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (2 :
      ℕ) - (55817982 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) - (22267872 : ℚ) * (k : ℚ) ^ (4 : ℕ) -
      (343520 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (6 : ℕ) - (5280392 : ℚ) * (k : ℚ) ^ (3 : ℕ) *
      (t : ℚ) ^ (5 : ℕ) - (32083766 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (98624887 :
      ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (3 : ℕ) - (161393654 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ)
      ^ (2 : ℕ) - (132715515 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) - (42547318 : ℚ) * (k : ℚ) ^ (3
      : ℕ) - (159952 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (7 : ℕ) - (3114160 : ℚ) * (k : ℚ) ^ (2
      : ℕ) * (t : ℚ) ^ (6 : ℕ) - (24155788 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (5 : ℕ) -
      (97578460 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (222228832 : ℚ) * (k : ℚ) ^ (2 :
      ℕ) * (t : ℚ) ^ (3 : ℕ) - (284905492 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (2 : ℕ) -
      (189466844 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) - (49983016 : ℚ) * (k : ℚ) ^ (2 : ℕ) -
      (32096 : ℚ) * (k : ℚ) * (t : ℚ) ^ (8 : ℕ) - (877904 : ℚ) * (k : ℚ) * (t : ℚ) ^ (7 : ℕ) -
      (8966808 : ℚ) * (k : ℚ) * (t : ℚ) ^ (6 : ℕ) - (47217276 : ℚ) * (k : ℚ) * (t : ℚ) ^ (5 : ℕ)
      - (143145308 : ℚ) * (k : ℚ) * (t : ℚ) ^ (4 : ℕ) - (257751688 : ℚ) * (k : ℚ) * (t : ℚ) ^ (3
      : ℕ) - (269284164 : ℚ) * (k : ℚ) * (t : ℚ) ^ (2 : ℕ) - (148507276 : ℚ) * (k : ℚ) * (t : ℚ)
      - (32752648 : ℚ) * (k : ℚ) - (64192 : ℚ) * (t : ℚ) ^ (8 : ℕ) - (1116000 : ℚ) * (t : ℚ) ^
      (7 : ℕ) - (8225136 : ℚ) * (t : ℚ) ^ (6 : ℕ) - (33401992 : ℚ) * (t : ℚ) ^ (5 : ℕ) -
      (81272824 : ℚ) * (t : ℚ) ^ (4 : ℕ) - (120467064 : ℚ) * (t : ℚ) ^ (3 : ℕ) - (105243448 : ℚ)
      * (t : ℚ) ^ (2 : ℕ) - (48912032 : ℚ) * (t : ℚ) - (9091488 : ℚ))
      / (16 * ((k : ℚ) + (t : ℚ) + 4) * (2 * (k : ℚ) + 2 * (t : ℚ) + 7) * (2 * (k : ℚ) + 2 * (t : ℚ) + 9) * ((k : ℚ) + 2 * (t : ℚ) + 5) * ((k : ℚ) + 2 * (t : ℚ) + 4) * ((k : ℚ) + 2 * (t : ℚ) + 3) * ((k : ℚ) + 2 * (t : ℚ) + 2) * ((k : ℚ) + 2 * (t : ℚ) + 1)) * Φ (k + 2) (t + 2)
      - (-(512 : ℚ) * (k : ℚ) ^ (9 : ℕ) - (7120 : ℚ) * (k : ℚ) ^ (8 : ℕ) * (t : ℚ) - (18288 : ℚ) * (k :
      ℚ) ^ (8 : ℕ) - (42971 : ℚ) * (k : ℚ) ^ (7 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (223087 : ℚ) * (k :
      ℚ) ^ (7 : ℕ) * (t : ℚ) - (282906 : ℚ) * (k : ℚ) ^ (7 : ℕ) - (146873 : ℚ) * (k : ℚ) ^ (6 :
      ℕ) * (t : ℚ) ^ (3 : ℕ) - (1156549 : ℚ) * (k : ℚ) ^ (6 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (2964662
      : ℚ) * (k : ℚ) ^ (6 : ℕ) * (t : ℚ) - (2469048 : ℚ) * (k : ℚ) ^ (6 : ℕ) - (310630 : ℚ) * (k
      : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (3301903 : ℚ) * (k : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (3 : ℕ)
      - (12847169 : ℚ) * (k : ℚ) ^ (5 : ℕ) * (t : ℚ) ^ (2 : ℕ) - (21643206 : ℚ) * (k : ℚ) ^ (5 :
      ℕ) * (t : ℚ) - (13290840 : ℚ) * (k : ℚ) ^ (5 : ℕ) - (415784 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t
      : ℚ) ^ (5 : ℕ) - (5607910 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (29512545 : ℚ) *
      (k : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (3 : ℕ) - (75615421 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) ^ (2
      : ℕ) - (94122404 : ℚ) * (k : ℚ) ^ (4 : ℕ) * (t : ℚ) - (45422772 : ℚ) * (k : ℚ) ^ (4 : ℕ) -
      (343520 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (6 : ℕ) - (5678376 : ℚ) * (k : ℚ) ^ (3 : ℕ) *
      (t : ℚ) ^ (5 : ℕ) - (38100586 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (132627601 :
      ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) ^ (3 : ℕ) - (252159292 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ)
      ^ (2 : ℕ) - (247753947 : ℚ) * (k : ℚ) ^ (3 : ℕ) * (t : ℚ) - (98039758 : ℚ) * (k : ℚ) ^ (3
      : ℕ) - (159952 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (7 : ℕ) - (3203264 : ℚ) * (k : ℚ) ^ (2
      : ℕ) * (t : ℚ) ^ (6 : ℕ) - (26669908 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (5 : ℕ) -
      (119612602 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (4 : ℕ) - (311801874 : ℚ) * (k : ℚ) ^ (2 :
      ℕ) * (t : ℚ) ^ (3 : ℕ) - (471799302 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) ^ (2 : ℕ) -
      (383079286 : ℚ) * (k : ℚ) ^ (2 : ℕ) * (t : ℚ) - (128520996 : ℚ) * (k : ℚ) ^ (2 : ℕ) -
      (32096 : ℚ) * (k : ℚ) * (t : ℚ) ^ (8 : ℕ) - (814768 : ℚ) * (k : ℚ) * (t : ℚ) ^ (7 : ℕ) -
      (8573736 : ℚ) * (k : ℚ) * (t : ℚ) ^ (6 : ℕ) - (49213404 : ℚ) * (k : ℚ) * (t : ℚ) ^ (5 : ℕ)
      - (169195416 : ℚ) * (k : ℚ) * (t : ℚ) ^ (4 : ℕ) - (357438372 : ℚ) * (k : ℚ) * (t : ℚ) ^ (3
      : ℕ) - (453406528 : ℚ) * (k : ℚ) * (t : ℚ) ^ (2 : ℕ) - (315668624 : ℚ) * (k : ℚ) * (t : ℚ)
      - (92283072 : ℚ) * (k : ℚ) - (32096 : ℚ) * (t : ℚ) ^ (8 : ℕ) - (654816 : ℚ) * (t : ℚ) ^ (7
      : ℕ) - (5713992 : ℚ) * (t : ℚ) ^ (6 : ℕ) - (27806088 : ℚ) * (t : ℚ) ^ (5 : ℕ) - (82386120
      : ℚ) * (t : ℚ) ^ (4 : ℕ) - (151906584 : ℚ) * (t : ℚ) ^ (3 : ℕ) - (169884688 : ℚ) * (t : ℚ)
      ^ (2 : ℕ) - (105115392 : ℚ) * (t : ℚ) - (27465984 : ℚ))
      / (16 * ((k : ℚ) + (t : ℚ) + 4) * (2 * (k : ℚ) + 2 * (t : ℚ) + 7) * (2 * (k : ℚ) + 2 * (t : ℚ) + 9) * ((k : ℚ) + 2 * (t : ℚ) + 6) * ((k : ℚ) + 2 * (t : ℚ) + 5) * ((k : ℚ) + 2 * (t : ℚ) + 4) * ((k : ℚ) + 2 * (t : ℚ) + 3) * ((k : ℚ) + 2 * (t : ℚ) + 2)) * Φ (k + 1) (t + 3) := by
  have g0 : (((2 * k + 2 * t + 3) + 2).factorial : ℚ) = (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 2) * (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 1) * (((2 * k + 2 * t + 3).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * k + 2 * t + 3) 2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g1 : (((2 * k + 2 * t + 3) + 4).factorial : ℚ) = (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 4) * (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 3) * (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 2) * (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 1) * (((2 * k + 2 * t + 3).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * k + 2 * t + 3) 4]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g2 : (((2 * k + 2 * t + 3) + 6).factorial : ℚ) = (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 6) * (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 5) * (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 4) * (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 3) * (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 2) * (((2 * k + 2 * t + 3 : ℕ) : ℚ) + 1) * (((2 * k + 2 * t + 3).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * k + 2 * t + 3) 6]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g3 : (((k + 1) + 1).factorial : ℚ) = (((k + 1 : ℕ) : ℚ) + 1) * (((k + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (k + 1) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g4 : (((k + 2 * t + 1) + 1).factorial : ℚ) = (((k + 2 * t + 1 : ℕ) : ℚ) + 1) * (((k + 2 * t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (k + 2 * t + 1) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g5 : (((k + 2 * t + 1) + 2).factorial : ℚ) = (((k + 2 * t + 1 : ℕ) : ℚ) + 2) * (((k + 2 * t + 1 : ℕ) : ℚ) + 1) * (((k + 2 * t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (k + 2 * t + 1) 2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g6 : (((k + 2 * t + 1) + 3).factorial : ℚ) = (((k + 2 * t + 1 : ℕ) : ℚ) + 3) * (((k + 2 * t + 1 : ℕ) : ℚ) + 2) * (((k + 2 * t + 1 : ℕ) : ℚ) + 1) * (((k + 2 * t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (k + 2 * t + 1) 3]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g7 : (((k + 2 * t + 1) + 4).factorial : ℚ) = (((k + 2 * t + 1 : ℕ) : ℚ) + 4) * (((k + 2 * t + 1 : ℕ) : ℚ) + 3) * (((k + 2 * t + 1 : ℕ) : ℚ) + 2) * (((k + 2 * t + 1 : ℕ) : ℚ) + 1) * (((k + 2 * t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (k + 2 * t + 1) 4]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g8 : (((k + 2 * t + 1) + 5).factorial : ℚ) = (((k + 2 * t + 1 : ℕ) : ℚ) + 5) * (((k + 2 * t + 1 : ℕ) : ℚ) + 4) * (((k + 2 * t + 1 : ℕ) : ℚ) + 3) * (((k + 2 * t + 1 : ℕ) : ℚ) + 2) * (((k + 2 * t + 1 : ℕ) : ℚ) + 1) * (((k + 2 * t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (k + 2 * t + 1) 5]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g9 : (((k + 2 * t + 1) + 6).factorial : ℚ) = (((k + 2 * t + 1 : ℕ) : ℚ) + 6) * (((k + 2 * t + 1 : ℕ) : ℚ) + 5) * (((k + 2 * t + 1 : ℕ) : ℚ) + 4) * (((k + 2 * t + 1 : ℕ) : ℚ) + 3) * (((k + 2 * t + 1 : ℕ) : ℚ) + 2) * (((k + 2 * t + 1 : ℕ) : ℚ) + 1) * (((k + 2 * t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (k + 2 * t + 1) 6]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g10 : (((k + 2 * t + 1) + 7).factorial : ℚ) = (((k + 2 * t + 1 : ℕ) : ℚ) + 7) * (((k + 2 * t + 1 : ℕ) : ℚ) + 6) * (((k + 2 * t + 1 : ℕ) : ℚ) + 5) * (((k + 2 * t + 1 : ℕ) : ℚ) + 4) * (((k + 2 * t + 1 : ℕ) : ℚ) + 3) * (((k + 2 * t + 1 : ℕ) : ℚ) + 2) * (((k + 2 * t + 1 : ℕ) : ℚ) + 1) * (((k + 2 * t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (k + 2 * t + 1) 7]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g11 : (((k + t + 1) + 1).factorial : ℚ) = (((k + t + 1 : ℕ) : ℚ) + 1) * (((k + t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (k + t + 1) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g12 : (((k + t + 1) + 2).factorial : ℚ) = (((k + t + 1 : ℕ) : ℚ) + 2) * (((k + t + 1 : ℕ) : ℚ) + 1) * (((k + t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (k + t + 1) 2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g13 : (((k + t + 1) + 3).factorial : ℚ) = (((k + t + 1 : ℕ) : ℚ) + 3) * (((k + t + 1 : ℕ) : ℚ) + 2) * (((k + t + 1 : ℕ) : ℚ) + 1) * (((k + t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (k + t + 1) 3]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g14 : (((t) + 1).factorial : ℚ) = (((t : ℕ) : ℚ) + 1) * (((t).factorial : ℕ) : ℚ) := by
    rw [fsh (t) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g15 : (((t) + 2).factorial : ℚ) = (((t : ℕ) : ℚ) + 2) * (((t : ℕ) : ℚ) + 1) * (((t).factorial : ℕ) : ℚ) := by
    rw [fsh (t) 2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g16 : (((t) + 3).factorial : ℚ) = (((t : ℕ) : ℚ) + 3) * (((t : ℕ) : ℚ) + 2) * (((t : ℕ) : ℚ) + 1) * (((t).factorial : ℕ) : ℚ) := by
    rw [fsh (t) 3]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  rw [interiorA_phi0, interiorA_phi1, interiorA_phi2, interiorA_phi3, interiorA_phi4]
  rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16]
  have hf0 : (((2 * k + 2 * t + 3).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf1 : (((k + 2 * t + 1).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : (((k + t + 1).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf3 : (((k + 1).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf4 : (((t).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast
  field_simp
  ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma stepvA (k t : ℕ) :
    (-324 * (k : ℚ) - 324 * (t : ℚ) - 810) * Φ (k + 1) (t) + (-669 * (k : ℚ) - 669 * (t : ℚ) - 1107)
      * Φ (k + 1) (t + 1) + (-38 * (k : ℚ) - 38 * (t : ℚ) - 208) * Φ (k + 1) (t + 2) + (8 * (k :
      ℚ) + 8 * (t : ℚ) + 32) * Φ (k + 1) (t + 3)
    = Gf (k + t + 1) (k + 2) - Gf (k + t + 1) (k + 1) := by
  have h := interiorA k t
  unfold Gf
  rw [show k + t + 1 + 3 - (k + 2) = t + 2 from by omega,
    show k + t + 1 + 3 - (k + 1) = t + 3 from by omega]
  rw [RcAA k t, RcBA k t]
  exact h

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma RcAB (t : ℕ) : Rc ((t + 1 : ℕ) : ℚ) ((1 : ℕ) : ℚ)
    = (-32096 * (t : ℚ) ^ 8 - 654816 * (t : ℚ) ^ 7 - 5713992 * (t : ℚ) ^ 6 - 27806088 * (t : ℚ) ^ 5 -
      82386120 * (t : ℚ) ^ 4 - 151906584 * (t : ℚ) ^ 3 - 169884688 * (t : ℚ) ^ 2 - 105115392 *
      (t : ℚ) - 27465984)
      / (16 * ((t : ℚ) + 4) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 9) * (2 * (t : ℚ) + 6) * (2 * (t : ℚ) + 5) * (2 * (t : ℚ) + 4) * (2 * (t : ℚ) + 3) * (2 * (t : ℚ) + 2)) := by
  have e : (16 * (((t + 1 : ℕ) : ℚ) + 3) * (2 * ((t + 1 : ℕ) : ℚ) + 5) * (2 * ((t + 1 : ℕ) : ℚ) + 7) * (2 * ((t + 1 : ℕ) : ℚ) - ((1 : ℕ) : ℚ) + 5) * (2 * ((t + 1 : ℕ) : ℚ) - ((1 : ℕ) : ℚ) + 4) * (2 * ((t + 1 : ℕ) : ℚ) - ((1 : ℕ) : ℚ) + 3) * (2 * ((t + 1 : ℕ) : ℚ) - ((1 : ℕ) : ℚ) + 2) * (2 * ((t + 1 : ℕ) : ℚ) - ((1 : ℕ) : ℚ) + 1) : ℚ) = 16 * ((t : ℚ) + 4) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 9) * (2 * (t : ℚ) + 6) * (2 * (t : ℚ) + 5) * (2 * (t : ℚ) + 4) * (2 * (t : ℚ) + 3) * (2 * (t : ℚ) + 2) := by
    push_cast
    ring
  have hpos : (16 * ((t : ℚ) + 4) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 9) * (2 * (t : ℚ) + 6) * (2 * (t : ℚ) + 5) * (2 * (t : ℚ) + 4) * (2 * (t : ℚ) + 3) * (2 * (t : ℚ) + 2) : ℚ) ≠ 0 := by positivity
  have horig : (16 * (((t + 1 : ℕ) : ℚ) + 3) * (2 * ((t + 1 : ℕ) : ℚ) + 5) * (2 * ((t + 1 : ℕ) : ℚ) + 7) * (2 * ((t + 1 : ℕ) : ℚ) - ((1 : ℕ) : ℚ) + 5) * (2 * ((t + 1 : ℕ) : ℚ) - ((1 : ℕ) : ℚ) + 4) * (2 * ((t + 1 : ℕ) : ℚ) - ((1 : ℕ) : ℚ) + 3) * (2 * ((t + 1 : ℕ) : ℚ) - ((1 : ℕ) : ℚ) + 2) * (2 * ((t + 1 : ℕ) : ℚ) - ((1 : ℕ) : ℚ) + 1) : ℚ) ≠ 0 := by
    rw [e]
    exact hpos
  unfold Rc
  rw [div_eq_div_iff horig hpos]
  push_cast
  ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma RcBB (t : ℕ) : Rc ((t + 1 : ℕ) : ℚ) ((0 : ℕ) : ℚ)
    = (0)
      / (16 * ((t : ℚ) + 4) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 9) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 6) * (2 * (t : ℚ) + 5) * (2 * (t : ℚ) + 4) * (2 * (t : ℚ) + 3)) := by
  have e : (16 * (((t + 1 : ℕ) : ℚ) + 3) * (2 * ((t + 1 : ℕ) : ℚ) + 5) * (2 * ((t + 1 : ℕ) : ℚ) + 7) * (2 * ((t + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) + 5) * (2 * ((t + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) + 4) * (2 * ((t + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) + 3) * (2 * ((t + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) + 2) * (2 * ((t + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) + 1) : ℚ) = 16 * ((t : ℚ) + 4) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 9) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 6) * (2 * (t : ℚ) + 5) * (2 * (t : ℚ) + 4) * (2 * (t : ℚ) + 3) := by
    push_cast
    ring
  have hpos : (16 * ((t : ℚ) + 4) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 9) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 6) * (2 * (t : ℚ) + 5) * (2 * (t : ℚ) + 4) * (2 * (t : ℚ) + 3) : ℚ) ≠ 0 := by positivity
  have horig : (16 * (((t + 1 : ℕ) : ℚ) + 3) * (2 * ((t + 1 : ℕ) : ℚ) + 5) * (2 * ((t + 1 : ℕ) : ℚ) + 7) * (2 * ((t + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) + 5) * (2 * ((t + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) + 4) * (2 * ((t + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) + 3) * (2 * ((t + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) + 2) * (2 * ((t + 1 : ℕ) : ℚ) - ((0 : ℕ) : ℚ) + 1) : ℚ) ≠ 0 := by
    rw [e]
    exact hpos
  unfold Rc
  rw [div_eq_div_iff horig hpos]
  push_cast
  ring

lemma interiorB_phi0 (t : ℕ) : Φ (0) (t + 1)
    = (1 : ℚ) ^ (0) * (2 : ℚ) ^ (t + 1) * ((2 * t + 2 + 1).factorial : ℚ)
      / ((1 : ℚ) * ((2 * t + 2 + 1).factorial : ℚ)) * ((2 * t + 2).factorial : ℚ)
      / (((t + 1).factorial : ℚ) * ((t + 1).factorial : ℚ))
      * (((t : ℚ) + 1) / (2 * (t : ℚ) + 2)) := by
  unfold Φ
  have e0 : 2 * 0 + 2 * (t + 1) + 1 = 2 * t + 2 + 1 := by ring
  have e1 : 0 + 2 * (t + 1) + 1 = 2 * t + 2 + 1 := by ring
  have e2 : 0 + 2 * (t + 1) = 2 * t + 2 := by ring
  have e3 : 0 + (t + 1) = t + 1 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try rw [show (0 : ℕ).factorial = 1 from rfl]
  try push_cast
  try ring

lemma interiorB_phi1 (t : ℕ) : Φ (0) (t + 2)
    = (1 : ℚ) ^ (0) * (2 : ℚ) ^ (t + 2) * ((2 * t + 2 + 3).factorial : ℚ)
      / ((1 : ℚ) * ((2 * t + 2 + 3).factorial : ℚ)) * ((2 * t + 2 + 2).factorial : ℚ)
      / (((t + 1 + 1).factorial : ℚ) * ((t + 1 + 1).factorial : ℚ))
      * (((t : ℚ) + 2) / (2 * (t : ℚ) + 4)) := by
  unfold Φ
  have e0 : 2 * 0 + 2 * (t + 2) + 1 = 2 * t + 2 + 3 := by ring
  have e1 : 0 + 2 * (t + 2) + 1 = 2 * t + 2 + 3 := by ring
  have e2 : 0 + 2 * (t + 2) = 2 * t + 2 + 2 := by ring
  have e3 : 0 + (t + 2) = t + 1 + 1 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try rw [show (0 : ℕ).factorial = 1 from rfl]
  try push_cast
  try ring

lemma interiorB_phi2 (t : ℕ) : Φ (0) (t + 3)
    = (1 : ℚ) ^ (0) * (2 : ℚ) ^ (t + 3) * ((2 * t + 2 + 5).factorial : ℚ)
      / ((1 : ℚ) * ((2 * t + 2 + 5).factorial : ℚ)) * ((2 * t + 2 + 4).factorial : ℚ)
      / (((t + 1 + 2).factorial : ℚ) * ((t + 1 + 2).factorial : ℚ))
      * (((t : ℚ) + 3) / (2 * (t : ℚ) + 6)) := by
  unfold Φ
  have e0 : 2 * 0 + 2 * (t + 3) + 1 = 2 * t + 2 + 5 := by ring
  have e1 : 0 + 2 * (t + 3) + 1 = 2 * t + 2 + 5 := by ring
  have e2 : 0 + 2 * (t + 3) = 2 * t + 2 + 4 := by ring
  have e3 : 0 + (t + 3) = t + 1 + 2 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try rw [show (0 : ℕ).factorial = 1 from rfl]
  try push_cast
  try ring

lemma interiorB_phi3 (t : ℕ) : Φ (0) (t + 4)
    = (1 : ℚ) ^ (0) * (2 : ℚ) ^ (t + 4) * ((2 * t + 2 + 7).factorial : ℚ)
      / ((1 : ℚ) * ((2 * t + 2 + 7).factorial : ℚ)) * ((2 * t + 2 + 6).factorial : ℚ)
      / (((t + 1 + 3).factorial : ℚ) * ((t + 1 + 3).factorial : ℚ))
      * (((t : ℚ) + 4) / (2 * (t : ℚ) + 8)) := by
  unfold Φ
  have e0 : 2 * 0 + 2 * (t + 4) + 1 = 2 * t + 2 + 7 := by ring
  have e1 : 0 + 2 * (t + 4) + 1 = 2 * t + 2 + 7 := by ring
  have e2 : 0 + 2 * (t + 4) = 2 * t + 2 + 6 := by ring
  have e3 : 0 + (t + 4) = t + 1 + 3 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try rw [show (0 : ℕ).factorial = 1 from rfl]
  try push_cast
  try ring

lemma interiorB_phi4 (t : ℕ) : Φ (1) (t + 3)
    = (1 : ℚ) ^ (1) * (2 : ℚ) ^ (t + 3) * ((2 * t + 2 + 7).factorial : ℚ)
      / ((1 : ℚ) * ((2 * t + 2 + 6).factorial : ℚ)) * ((2 * t + 2 + 5).factorial : ℚ)
      / (((t + 1 + 2).factorial : ℚ) * ((t + 1 + 3).factorial : ℚ))
      * (((t : ℚ) + 4) / (2 * (t : ℚ) + 7)) := by
  unfold Φ
  have e0 : 2 * 1 + 2 * (t + 3) + 1 = 2 * t + 2 + 7 := by ring
  have e1 : 1 + 2 * (t + 3) + 1 = 2 * t + 2 + 6 := by ring
  have e2 : 1 + 2 * (t + 3) = 2 * t + 2 + 5 := by ring
  have e3 : 1 + (t + 3) = t + 1 + 3 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try rw [show (1 : ℕ).factorial = 1 from rfl]
  try push_cast
  try ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma interiorB (t : ℕ) :
    (-324 * (t : ℚ) - 810) * Φ (0) (t + 1) + (-669 * (t : ℚ) - 1107) * Φ (0) (t + 2) + (-38 * (t :
      ℚ) - 208) * Φ (0) (t + 3) + (8 * (t : ℚ) + 32) * Φ (0) (t + 4)
    = (-32096 * (t : ℚ) ^ 8 - 654816 * (t : ℚ) ^ 7 - 5713992 * (t : ℚ) ^ 6 - 27806088 * (t : ℚ) ^ 5 -
      82386120 * (t : ℚ) ^ 4 - 151906584 * (t : ℚ) ^ 3 - 169884688 * (t : ℚ) ^ 2 - 105115392 *
      (t : ℚ) - 27465984)
      / (16 * ((t : ℚ) + 4) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 9) * (2 * (t : ℚ) + 6) * (2 * (t : ℚ) + 5) * (2 * (t : ℚ) + 4) * (2 * (t : ℚ) + 3) * (2 * (t : ℚ) + 2)) * Φ (1) (t + 3)
      - (0)
      / (16 * ((t : ℚ) + 4) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 9) * (2 * (t : ℚ) + 7) * (2 * (t : ℚ) + 6) * (2 * (t : ℚ) + 5) * (2 * (t : ℚ) + 4) * (2 * (t : ℚ) + 3)) * Φ (0) (t + 4) := by
  have g0 : (((2 * t + 2) + 1).factorial : ℚ) = (((2 * t + 2 : ℕ) : ℚ) + 1) * (((2 * t + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * t + 2) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g1 : (((2 * t + 2) + 2).factorial : ℚ) = (((2 * t + 2 : ℕ) : ℚ) + 2) * (((2 * t + 2 : ℕ) : ℚ) + 1) * (((2 * t + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * t + 2) 2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g2 : (((2 * t + 2) + 3).factorial : ℚ) = (((2 * t + 2 : ℕ) : ℚ) + 3) * (((2 * t + 2 : ℕ) : ℚ) + 2) * (((2 * t + 2 : ℕ) : ℚ) + 1) * (((2 * t + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * t + 2) 3]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g3 : (((2 * t + 2) + 4).factorial : ℚ) = (((2 * t + 2 : ℕ) : ℚ) + 4) * (((2 * t + 2 : ℕ) : ℚ) + 3) * (((2 * t + 2 : ℕ) : ℚ) + 2) * (((2 * t + 2 : ℕ) : ℚ) + 1) * (((2 * t + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * t + 2) 4]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g4 : (((2 * t + 2) + 5).factorial : ℚ) = (((2 * t + 2 : ℕ) : ℚ) + 5) * (((2 * t + 2 : ℕ) : ℚ) + 4) * (((2 * t + 2 : ℕ) : ℚ) + 3) * (((2 * t + 2 : ℕ) : ℚ) + 2) * (((2 * t + 2 : ℕ) : ℚ) + 1) * (((2 * t + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * t + 2) 5]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g5 : (((2 * t + 2) + 6).factorial : ℚ) = (((2 * t + 2 : ℕ) : ℚ) + 6) * (((2 * t + 2 : ℕ) : ℚ) + 5) * (((2 * t + 2 : ℕ) : ℚ) + 4) * (((2 * t + 2 : ℕ) : ℚ) + 3) * (((2 * t + 2 : ℕ) : ℚ) + 2) * (((2 * t + 2 : ℕ) : ℚ) + 1) * (((2 * t + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * t + 2) 6]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g6 : (((2 * t + 2) + 7).factorial : ℚ) = (((2 * t + 2 : ℕ) : ℚ) + 7) * (((2 * t + 2 : ℕ) : ℚ) + 6) * (((2 * t + 2 : ℕ) : ℚ) + 5) * (((2 * t + 2 : ℕ) : ℚ) + 4) * (((2 * t + 2 : ℕ) : ℚ) + 3) * (((2 * t + 2 : ℕ) : ℚ) + 2) * (((2 * t + 2 : ℕ) : ℚ) + 1) * (((2 * t + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * t + 2) 7]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g7 : (((t + 1) + 1).factorial : ℚ) = (((t + 1 : ℕ) : ℚ) + 1) * (((t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (t + 1) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g8 : (((t + 1) + 2).factorial : ℚ) = (((t + 1 : ℕ) : ℚ) + 2) * (((t + 1 : ℕ) : ℚ) + 1) * (((t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (t + 1) 2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g9 : (((t + 1) + 3).factorial : ℚ) = (((t + 1 : ℕ) : ℚ) + 3) * (((t + 1 : ℕ) : ℚ) + 2) * (((t + 1 : ℕ) : ℚ) + 1) * (((t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (t + 1) 3]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  rw [interiorB_phi0, interiorB_phi1, interiorB_phi2, interiorB_phi3, interiorB_phi4]
  rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9]
  have hf0 : (((2 * t + 2).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf1 : (((t + 1).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast
  field_simp
  ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma stepvB (t : ℕ) :
    (-324 * (t : ℚ) - 810) * Φ (0) (t + 1) + (-669 * (t : ℚ) - 1107) * Φ (0) (t + 2) + (-38 * (t :
      ℚ) - 208) * Φ (0) (t + 3) + (8 * (t : ℚ) + 32) * Φ (0) (t + 4)
    = Gf (t + 1) (1) - Gf (t + 1) (0) := by
  have h := interiorB t
  unfold Gf
  rw [show t + 1 + 3 - (1) = t + 3 from by omega,
    show t + 1 + 3 - 0 = t + 4 from by omega]
  rw [RcAB t, RcBB t]
  exact h

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma RcM (m : ℕ) : Rc ((m + 1 : ℕ) : ℚ) ((m + 1 + 1 : ℕ) : ℚ)
    = (-512 * (m : ℚ) ^ 9 - 15776 * (m : ℚ) ^ 8 - 210566 * (m : ℚ) ^ 7 - 1589304 * (m : ℚ) ^ 6 -
      7436412 * (m : ℚ) ^ 5 - 22267872 * (m : ℚ) ^ 4 - 42547318 * (m : ℚ) ^ 3 - 49983016 * (m :
      ℚ) ^ 2 - 32752648 * (m : ℚ) - 9091488)
      / (16 * ((m : ℚ) + 4) * (2 * (m : ℚ) + 7) * (2 * (m : ℚ) + 9) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1)) := by
  have e : (16 * (((m + 1 : ℕ) : ℚ) + 3) * (2 * ((m + 1 : ℕ) : ℚ) + 5) * (2 * ((m + 1 : ℕ) : ℚ) + 7) * (2 * ((m + 1 : ℕ) : ℚ) - ((m + 1 + 1 : ℕ) : ℚ) + 5) * (2 * ((m + 1 : ℕ) : ℚ) - ((m + 1 + 1 : ℕ) : ℚ) + 4) * (2 * ((m + 1 : ℕ) : ℚ) - ((m + 1 + 1 : ℕ) : ℚ) + 3) * (2 * ((m + 1 : ℕ) : ℚ) - ((m + 1 + 1 : ℕ) : ℚ) + 2) * (2 * ((m + 1 : ℕ) : ℚ) - ((m + 1 + 1 : ℕ) : ℚ) + 1) : ℚ) = 16 * ((m : ℚ) + 4) * (2 * (m : ℚ) + 7) * (2 * (m : ℚ) + 9) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) := by
    push_cast
    ring
  have hpos : (16 * ((m : ℚ) + 4) * (2 * (m : ℚ) + 7) * (2 * (m : ℚ) + 9) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) : ℚ) ≠ 0 := by positivity
  have horig : (16 * (((m + 1 : ℕ) : ℚ) + 3) * (2 * ((m + 1 : ℕ) : ℚ) + 5) * (2 * ((m + 1 : ℕ) : ℚ) + 7) * (2 * ((m + 1 : ℕ) : ℚ) - ((m + 1 + 1 : ℕ) : ℚ) + 5) * (2 * ((m + 1 : ℕ) : ℚ) - ((m + 1 + 1 : ℕ) : ℚ) + 4) * (2 * ((m + 1 : ℕ) : ℚ) - ((m + 1 + 1 : ℕ) : ℚ) + 3) * (2 * ((m + 1 : ℕ) : ℚ) - ((m + 1 + 1 : ℕ) : ℚ) + 2) * (2 * ((m + 1 : ℕ) : ℚ) - ((m + 1 + 1 : ℕ) : ℚ) + 1) : ℚ) ≠ 0 := by
    rw [e]
    exact hpos
  unfold Rc
  rw [div_eq_div_iff horig hpos]
  push_cast
  ring

lemma boundary_phi0 (m : ℕ) : Φ (m + 2) (2)
    = (1 : ℚ) ^ (m + 2) * (2 : ℚ) ^ (2) * ((2 * m + 5 + 4).factorial : ℚ)
      / (((m + 2).factorial : ℚ) * ((m + 2 + 5).factorial : ℚ)) * ((m + 2 + 4).factorial : ℚ)
      / ((2 : ℚ) * ((m + 2 + 2).factorial : ℚ))
      * (((m : ℚ) + 4) / ((m : ℚ) + 6)) := by
  unfold Φ
  have e0 : 2 * (m + 2) + 2 * 2 + 1 = 2 * m + 5 + 4 := by ring
  have e1 : (m + 2) + 2 * 2 + 1 = m + 2 + 5 := by ring
  have e2 : (m + 2) + 2 * 2 = m + 2 + 4 := by ring
  have e3 : (m + 2) + 2 = m + 2 + 2 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try rw [show (2 : ℕ).factorial = 2 from rfl]
  try push_cast
  try ring

lemma boundary_phi1 (m : ℕ) : Φ (m + 2) (0)
    = (1 : ℚ) ^ (m + 2) * (2 : ℚ) ^ (0) * ((2 * m + 5).factorial : ℚ)
      / (((m + 2).factorial : ℚ) * ((m + 2 + 1).factorial : ℚ)) * ((m + 2).factorial : ℚ)
      / ((1 : ℚ) * ((m + 2).factorial : ℚ))
      * (((m : ℚ) + 2) / ((m : ℚ) + 2)) := by
  unfold Φ
  have e0 : 2 * (m + 2) + 2 * 0 + 1 = 2 * m + 5 := by ring
  have e1 : (m + 2) + 2 * 0 + 1 = m + 2 + 1 := by ring
  have e2 : (m + 2) + 2 * 0 = m + 2 := by ring
  have e3 : (m + 2) + 0 = m + 2 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try rw [show (0 : ℕ).factorial = 1 from rfl]
  try push_cast
  try ring

lemma boundary_phi2 (m : ℕ) : Φ (m + 2) (1)
    = (1 : ℚ) ^ (m + 2) * (2 : ℚ) ^ (1) * ((2 * m + 5 + 2).factorial : ℚ)
      / (((m + 2).factorial : ℚ) * ((m + 2 + 3).factorial : ℚ)) * ((m + 2 + 2).factorial : ℚ)
      / ((1 : ℚ) * ((m + 2 + 1).factorial : ℚ))
      * (((m : ℚ) + 3) / ((m : ℚ) + 4)) := by
  unfold Φ
  have e0 : 2 * (m + 2) + 2 * 1 + 1 = 2 * m + 5 + 2 := by ring
  have e1 : (m + 2) + 2 * 1 + 1 = m + 2 + 3 := by ring
  have e2 : (m + 2) + 2 * 1 = m + 2 + 2 := by ring
  have e3 : (m + 2) + 1 = m + 2 + 1 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try rw [show (1 : ℕ).factorial = 1 from rfl]
  try push_cast
  try ring

lemma boundary_phi3 (m : ℕ) : Φ (m + 3) (0)
    = (1 : ℚ) ^ (m + 3) * (2 : ℚ) ^ (0) * ((2 * m + 5 + 2).factorial : ℚ)
      / (((m + 2 + 1).factorial : ℚ) * ((m + 2 + 2).factorial : ℚ)) * ((m + 2 + 1).factorial : ℚ)
      / ((1 : ℚ) * ((m + 2 + 1).factorial : ℚ))
      * (((m : ℚ) + 3) / ((m : ℚ) + 3)) := by
  unfold Φ
  have e0 : 2 * (m + 3) + 2 * 0 + 1 = 2 * m + 5 + 2 := by ring
  have e1 : (m + 3) + 2 * 0 + 1 = m + 2 + 2 := by ring
  have e2 : (m + 3) + 2 * 0 = m + 2 + 1 := by ring
  have e3 : (m + 3) + 0 = m + 2 + 1 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try rw [show (0 : ℕ).factorial = 1 from rfl]
  try push_cast
  try ring

lemma boundary_phi4 (m : ℕ) : Φ (m + 3) (1)
    = (1 : ℚ) ^ (m + 3) * (2 : ℚ) ^ (1) * ((2 * m + 5 + 4).factorial : ℚ)
      / (((m + 2 + 1).factorial : ℚ) * ((m + 2 + 4).factorial : ℚ)) * ((m + 2 + 3).factorial : ℚ)
      / ((1 : ℚ) * ((m + 2 + 2).factorial : ℚ))
      * (((m : ℚ) + 4) / ((m : ℚ) + 5)) := by
  unfold Φ
  have e0 : 2 * (m + 3) + 2 * 1 + 1 = 2 * m + 5 + 4 := by ring
  have e1 : (m + 3) + 2 * 1 + 1 = m + 2 + 4 := by ring
  have e2 : (m + 3) + 2 * 1 = m + 2 + 3 := by ring
  have e3 : (m + 3) + 1 = m + 2 + 2 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try rw [show (1 : ℕ).factorial = 1 from rfl]
  try push_cast
  try ring

lemma boundary_phi5 (m : ℕ) : Φ (m + 4) (0)
    = (1 : ℚ) ^ (m + 4) * (2 : ℚ) ^ (0) * ((2 * m + 5 + 4).factorial : ℚ)
      / (((m + 2 + 2).factorial : ℚ) * ((m + 2 + 3).factorial : ℚ)) * ((m + 2 + 2).factorial : ℚ)
      / ((1 : ℚ) * ((m + 2 + 2).factorial : ℚ))
      * (((m : ℚ) + 4) / ((m : ℚ) + 4)) := by
  unfold Φ
  have e0 : 2 * (m + 4) + 2 * 0 + 1 = 2 * m + 5 + 4 := by ring
  have e1 : (m + 4) + 2 * 0 + 1 = m + 2 + 3 := by ring
  have e2 : (m + 4) + 2 * 0 = m + 2 + 2 := by ring
  have e3 : (m + 4) + 0 = m + 2 + 2 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  try rw [show (0 : ℕ).factorial = 1 from rfl]
  try push_cast
  try ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma boundary (m : ℕ) :
    (-512 * (m : ℚ) ^ 9 - 15776 * (m : ℚ) ^ 8 - 210566 * (m : ℚ) ^ 7 - 1589304 * (m : ℚ) ^ 6 -
      7436412 * (m : ℚ) ^ 5 - 22267872 * (m : ℚ) ^ 4 - 42547318 * (m : ℚ) ^ 3 - 49983016 * (m :
      ℚ) ^ 2 - 32752648 * (m : ℚ) - 9091488)
      / (16 * ((m : ℚ) + 4) * (2 * (m : ℚ) + 7) * (2 * (m : ℚ) + 9) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1)) * Φ (m + 2) 2
      + ((-669 * (m : ℚ) - 1107) * Φ (m + 2) 0 + (-38 * (m : ℚ) - 208) * Φ (m + 2) 1 + (-38 * (m : ℚ) -
      208) * Φ (m + 3) 0 + (8 * (m : ℚ) + 32) * Φ (m + 2) 2 + (8 * (m : ℚ) + 32) * Φ (m + 3) 1 +
      (8 * (m : ℚ) + 32) * Φ (m + 4) 0) = 0 := by
  have g0 : (((2 * m + 5) + 2).factorial : ℚ) = (((2 * m + 5 : ℕ) : ℚ) + 2) * (((2 * m + 5 : ℕ) : ℚ) + 1) * (((2 * m + 5).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * m + 5) 2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g1 : (((2 * m + 5) + 4).factorial : ℚ) = (((2 * m + 5 : ℕ) : ℚ) + 4) * (((2 * m + 5 : ℕ) : ℚ) + 3) * (((2 * m + 5 : ℕ) : ℚ) + 2) * (((2 * m + 5 : ℕ) : ℚ) + 1) * (((2 * m + 5).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * m + 5) 4]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g2 : (((m + 2) + 1).factorial : ℚ) = (((m + 2 : ℕ) : ℚ) + 1) * (((m + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (m + 2) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g3 : (((m + 2) + 2).factorial : ℚ) = (((m + 2 : ℕ) : ℚ) + 2) * (((m + 2 : ℕ) : ℚ) + 1) * (((m + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (m + 2) 2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g4 : (((m + 2) + 3).factorial : ℚ) = (((m + 2 : ℕ) : ℚ) + 3) * (((m + 2 : ℕ) : ℚ) + 2) * (((m + 2 : ℕ) : ℚ) + 1) * (((m + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (m + 2) 3]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g5 : (((m + 2) + 4).factorial : ℚ) = (((m + 2 : ℕ) : ℚ) + 4) * (((m + 2 : ℕ) : ℚ) + 3) * (((m + 2 : ℕ) : ℚ) + 2) * (((m + 2 : ℕ) : ℚ) + 1) * (((m + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (m + 2) 4]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g6 : (((m + 2) + 5).factorial : ℚ) = (((m + 2 : ℕ) : ℚ) + 5) * (((m + 2 : ℕ) : ℚ) + 4) * (((m + 2 : ℕ) : ℚ) + 3) * (((m + 2 : ℕ) : ℚ) + 2) * (((m + 2 : ℕ) : ℚ) + 1) * (((m + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (m + 2) 5]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  rw [boundary_phi0, boundary_phi1, boundary_phi2, boundary_phi3, boundary_phi4, boundary_phi5]
  rw [g0, g1, g2, g3, g4, g5, g6]
  have hf0 : (((2 * m + 5).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf1 : (((m + 2).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast
  field_simp
  ring

lemma split0 (m : ℕ) : ((a (m + 1) : ℤ) : ℚ)
    = ∑ k ∈ Finset.range (m + 1 + 1), Φ k (m + 1 - k + 0) := by
  have hmain : ∀ k ∈ Finset.range (m + 1 + 1), (F (m + 1) k : ℚ) = Φ k (m + 1 - k + 0) := by
    intro k hk
    have hk' : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := F_eq k (m + 1 - k + 0) (by omega)
    rw [show k + (m + 1 - k + 0) = m + 1 from by omega] at h
    exact h
  rw [a_eq]
  push_cast
  exact Finset.sum_congr rfl hmain

lemma split1 (m : ℕ) : ((a (m + 2) : ℤ) : ℚ)
    = ∑ k ∈ Finset.range (m + 1 + 1), Φ k (m + 1 - k + 1) + (Φ (m + 2) 0) := by
  have hmain : ∀ k ∈ Finset.range (m + 1 + 1), (F (m + 2) k : ℚ) = Φ k (m + 1 - k + 1) := by
    intro k hk
    have hk' : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := F_eq k (m + 1 - k + 1) (by omega)
    rw [show k + (m + 1 - k + 1) = m + 2 from by omega] at h
    exact h
  have q1 : (F (m + 2) (m + 1 + 1 + 0) : ℚ) = Φ (m + 2) 0 := by
    have h := F_eq (m + 2) 0 (by omega)
    rw [show m + 2 + 0 = m + 2 from by ring] at h
    rw [show m + 1 + 1 + 0 = m + 2 from by ring]
    exact h
  rw [a_eq, show m + 2 + 1 = (m + 1 + 1) + 1 from by ring, Finset.sum_range_add]
  push_cast
  rw [Finset.sum_congr rfl hmain]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, q1]

lemma split2 (m : ℕ) : ((a (m + 3) : ℤ) : ℚ)
    = ∑ k ∈ Finset.range (m + 1 + 1), Φ k (m + 1 - k + 2) + (Φ (m + 2) 1 + Φ (m + 3) 0) := by
  have hmain : ∀ k ∈ Finset.range (m + 1 + 1), (F (m + 3) k : ℚ) = Φ k (m + 1 - k + 2) := by
    intro k hk
    have hk' : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := F_eq k (m + 1 - k + 2) (by omega)
    rw [show k + (m + 1 - k + 2) = m + 3 from by omega] at h
    exact h
  have q1 : (F (m + 3) (m + 1 + 1 + 0) : ℚ) = Φ (m + 2) 1 := by
    have h := F_eq (m + 2) 1 (by omega)
    rw [show m + 2 + 1 = m + 3 from by ring] at h
    rw [show m + 1 + 1 + 0 = m + 2 from by ring]
    exact h
  have q2 : (F (m + 3) (m + 1 + 1 + 1) : ℚ) = Φ (m + 3) 0 := by
    have h := F_eq (m + 3) 0 (by omega)
    rw [show m + 3 + 0 = m + 3 from by ring] at h
    rw [show m + 1 + 1 + 1 = m + 3 from by ring]
    exact h
  rw [a_eq, show m + 3 + 1 = (m + 1 + 1) + 2 from by ring, Finset.sum_range_add]
  push_cast
  rw [Finset.sum_congr rfl hmain]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, q1, q2]

lemma split3 (m : ℕ) : ((a (m + 4) : ℤ) : ℚ)
    = ∑ k ∈ Finset.range (m + 1 + 1), Φ k (m + 1 - k + 3) + (Φ (m + 2) 2 + Φ (m + 3) 1 + Φ (m + 4) 0) := by
  have hmain : ∀ k ∈ Finset.range (m + 1 + 1), (F (m + 4) k : ℚ) = Φ k (m + 1 - k + 3) := by
    intro k hk
    have hk' : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := F_eq k (m + 1 - k + 3) (by omega)
    rw [show k + (m + 1 - k + 3) = m + 4 from by omega] at h
    exact h
  have q1 : (F (m + 4) (m + 1 + 1 + 0) : ℚ) = Φ (m + 2) 2 := by
    have h := F_eq (m + 2) 2 (by omega)
    rw [show m + 2 + 2 = m + 4 from by ring] at h
    rw [show m + 1 + 1 + 0 = m + 2 from by ring]
    exact h
  have q2 : (F (m + 4) (m + 1 + 1 + 1) : ℚ) = Φ (m + 3) 1 := by
    have h := F_eq (m + 3) 1 (by omega)
    rw [show m + 3 + 1 = m + 4 from by ring] at h
    rw [show m + 1 + 1 + 1 = m + 3 from by ring]
    exact h
  have q3 : (F (m + 4) (m + 1 + 1 + 2) : ℚ) = Φ (m + 4) 0 := by
    have h := F_eq (m + 4) 0 (by omega)
    rw [show m + 4 + 0 = m + 4 from by ring] at h
    rw [show m + 1 + 1 + 2 = m + 4 from by ring]
    exact h
  rw [a_eq, show m + 4 + 1 = (m + 1 + 1) + 3 from by ring, Finset.sum_range_add]
  push_cast
  rw [Finset.sum_congr rfl hmain]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, q1, q2, q3]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma step (m k : ℕ) (hk : k ≤ m) (hm : 1 ≤ m) :
    (-324 * (m : ℚ) - 486) * Φ k (m - k + 0) + (-669 * (m : ℚ) - 438) * Φ k (m - k + 1) + (-38 * (m
      : ℚ) - 170) * Φ k (m - k + 2) + (8 * (m : ℚ) + 24) * Φ k (m - k + 3)
    = Gf m (k + 1) - Gf m k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have h := stepvB (m - 1)
    rw [show m - 1 + 1 = m from by omega] at h
    have ec : (((m - 1 : ℕ) : ℚ)) = (m : ℚ) - 1 := by
      rw [Nat.cast_sub hm]
      simp
    try rw [ec] at h
    rw [show m - 0 + 0 = m from by omega]
    rw [show m - 0 + 1 = m - 1 + 2 from by omega]
    rw [show m - 0 + 2 = m - 1 + 3 from by omega]
    rw [show m - 0 + 3 = m - 1 + 4 from by omega]
    rw [show (0 : ℕ) + 1 = 1 from rfl]
    linear_combination h
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h := stepvA k' (m - (k' + 1))
    rw [show k' + (m - (k' + 1)) + 1 = m from by omega] at h
    have ec : (((m - (k' + 1) : ℕ) : ℚ)) = (m : ℚ) - ((k' : ℚ) + 1) := by
      rw [Nat.cast_sub hk]
      push_cast
      ring
    try rw [ec] at h
    try simp only [Nat.add_zero]
    rw [show k' + 1 + 1 = k' + 2 from rfl]
    linear_combination h


lemma Gf_zero (m : ℕ) : Gf m 0 = 0 := by
  unfold Gf Rc
  simp

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
lemma main_q (m : ℕ) :
    (-324 * (m : ℚ) - 810) * ((a (m + 1) : ℤ) : ℚ) + (-669 * (m : ℚ) - 1107) * ((a (m + 2) : ℤ) : ℚ)
      + (-38 * (m : ℚ) - 208) * ((a (m + 3) : ℤ) : ℚ) + (8 * (m : ℚ) + 32) * ((a (m + 4) : ℤ) :
      ℚ) = 0 := by
  have hsum : ∑ k ∈ Finset.range (m + 1 + 1), ((-324 * (m : ℚ) - 810) * Φ k (m + 1 - k + 0) + (-669 * (m : ℚ) - 1107) * Φ k (m + 1 - k + 1) + (-38 * (m : ℚ) - 208) * Φ k (m + 1 - k + 2) + (8 * (m : ℚ) + 32) * Φ k (m + 1 - k + 3))
      = Gf (m + 1) (m + 1 + 1) - Gf (m + 1) 0 := by
    rw [← Finset.sum_range_sub (Gf (m + 1)) (m + 1 + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    have hs := step (m + 1) k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) (by omega)
    push_cast at hs ⊢
    linear_combination hs
  have hb := boundary m
  have hz := Gf_zero (m + 1)
  have hG : Gf (m + 1) (m + 1 + 1) = Rc ((m + 1 : ℕ) : ℚ) ((m + 1 + 1 : ℕ) : ℚ) * Φ (m + 2) 2 := by
    unfold Gf
    rw [show m + 1 + 3 - (m + 1 + 1) = 2 from by omega]
  have hR := RcM m
  rw [split0, split1, split2, split3]
  have hdist : (-324 * (m : ℚ) - 810) * ∑ k ∈ Finset.range (m + 1 + 1), Φ k (m + 1 - k + 0) + (-669 * (m : ℚ) -
      1107) * ∑ k ∈ Finset.range (m + 1 + 1), Φ k (m + 1 - k + 1) + (-38 * (m : ℚ) - 208) * ∑ k
      ∈ Finset.range (m + 1 + 1), Φ k (m + 1 - k + 2) + (8 * (m : ℚ) + 32) * ∑ k ∈ Finset.range
      (m + 1 + 1), Φ k (m + 1 - k + 3)
      = ∑ k ∈ Finset.range (m + 1 + 1), ((-324 * (m : ℚ) - 810) * Φ k (m + 1 - k + 0) + (-669 * (m : ℚ) - 1107) * Φ k (m + 1 - k + 1) + (-38 * (m : ℚ) - 208) * Φ k (m + 1 - k + 2) + (8 * (m : ℚ) + 32) * Φ k (m + 1 - k + 3)) := by
    simp only [Finset.mul_sum, Finset.sum_add_distrib]
  linear_combination hdist + hsum - hz + hG + (Φ (m + 2) 2) * hR + hb

end OMA.T386862

theorem OMA.solution : type_of% @OMA.S_oeis_a386862.main := by
  intro n hn
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · have hn' : n = 3 := by omega
    subst hn'
    decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h := OMA.T386862.main_q m
    have t1 : m + 4 - 1 = m + 3 := by omega
    have t2 : m + 4 - 2 = m + 2 := by omega
    have t3 : m + 4 - 3 = m + 1 := by omega
    simp only [t1, t2, t3]
    apply Int.cast_injective (α := ℚ)
    push_cast
    linear_combination h
