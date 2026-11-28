import OMAStatements.S_oeis_a262115
import Mathlib

/-!
# A262115: proof of Barker's recurrence (after Robert Israel)

Credit: @ivillar

Write the base as b = 7K + d. The row length depends only on d (1, 1, 3, 6, 3, 6, 2 for
d = 0, ..., 6), so the rows 7Q + 2, ..., 7Q + 8 always fill 22 consecutive entries, and entry
22Q + r (r < 22) of the concatenation is a fixed digit of the base 7Q + 2 + j. Each digit
floor(b^k / 7) mod b is a linear function alpha*K + beta of K, checked by the explicit division
identity b^k = (b^k mod 7) + (alpha*K + beta + b * P(K)) * 7 with P(K) = floor(b^(k-1) / 7) written
as a polynomial in K. Linear functions of Q satisfy f(Q) = 2 f(Q - 1) - f(Q - 2).
-/

namespace PA262115
open OMA.S_oeis_a262115

theorem dig0_1 (K : ℕ) (hK : 1 ≤ K) : digit (7 * K) 1 = 1 * K + 0 := by
  unfold digit
  rw [show (7 * K) ^ 1 = 0 + (1 * K + 0 + (7 * K) * (0)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 0 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig1_1 (K : ℕ) : digit (7 * K + 1) 1 = 1 * K + 0 := by
  unfold digit
  rw [show (7 * K + 1) ^ 1 = 1 + (1 * K + 0 + (7 * K + 1) * (0)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 1 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig2_1 (K : ℕ) : digit (7 * K + 2) 1 = 1 * K + 0 := by
  unfold digit
  rw [show (7 * K + 2) ^ 1 = 2 + (1 * K + 0 + (7 * K + 2) * (0)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 2 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig2_2 (K : ℕ) : digit (7 * K + 2) 2 = 2 * K + 0 := by
  unfold digit
  rw [show (7 * K + 2) ^ 2 = 4 + (2 * K + 0 + (7 * K + 2) * (1 * K)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 4 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig2_3 (K : ℕ) : digit (7 * K + 2) 3 = 4 * K + 1 := by
  unfold digit
  rw [show (7 * K + 2) ^ 3 = 1 + (4 * K + 1 + (7 * K + 2) * (4 * K + 7 * K ^ 2)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 1 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig3_1 (K : ℕ) : digit (7 * K + 3) 1 = 1 * K + 0 := by
  unfold digit
  rw [show (7 * K + 3) ^ 1 = 3 + (1 * K + 0 + (7 * K + 3) * (0)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 3 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig3_2 (K : ℕ) : digit (7 * K + 3) 2 = 3 * K + 1 := by
  unfold digit
  rw [show (7 * K + 3) ^ 2 = 2 + (3 * K + 1 + (7 * K + 3) * (1 * K)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 2 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig3_3 (K : ℕ) : digit (7 * K + 3) 3 = 2 * K + 0 := by
  unfold digit
  rw [show (7 * K + 3) ^ 3 = 6 + (2 * K + 0 + (7 * K + 3) * (1 + 6 * K + 7 * K ^ 2)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 6 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig3_4 (K : ℕ) : digit (7 * K + 3) 4 = 6 * K + 2 := by
  unfold digit
  rw [show (7 * K + 3) ^ 4 = 4 + (6 * K + 2 + (7 * K + 3) * (3 + 27 * K + 63 * K ^ 2 + 49 * K ^ 3)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 4 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig3_5 (K : ℕ) : digit (7 * K + 3) 5 = 4 * K + 1 := by
  unfold digit
  rw [show (7 * K + 3) ^ 5 = 5 + (4 * K + 1 + (7 * K + 3) * (11 + 108 * K + 378 * K ^ 2 + 588 * K ^ 3 + 343 * K ^ 4)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 5 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig3_6 (K : ℕ) : digit (7 * K + 3) 6 = 5 * K + 2 := by
  unfold digit
  rw [show (7 * K + 3) ^ 6 = 1 + (5 * K + 2 + (7 * K + 3) * (34 + 405 * K + 1890 * K ^ 2 + 4410 * K ^ 3 + 5145 * K ^ 4 + 2401 * K ^ 5)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 1 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig4_1 (K : ℕ) : digit (7 * K + 4) 1 = 1 * K + 0 := by
  unfold digit
  rw [show (7 * K + 4) ^ 1 = 4 + (1 * K + 0 + (7 * K + 4) * (0)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 4 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig4_2 (K : ℕ) : digit (7 * K + 4) 2 = 4 * K + 2 := by
  unfold digit
  rw [show (7 * K + 4) ^ 2 = 2 + (4 * K + 2 + (7 * K + 4) * (1 * K)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 2 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig4_3 (K : ℕ) : digit (7 * K + 4) 3 = 2 * K + 1 := by
  unfold digit
  rw [show (7 * K + 4) ^ 3 = 1 + (2 * K + 1 + (7 * K + 4) * (2 + 8 * K + 7 * K ^ 2)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 1 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig5_1 (K : ℕ) : digit (7 * K + 5) 1 = 1 * K + 0 := by
  unfold digit
  rw [show (7 * K + 5) ^ 1 = 5 + (1 * K + 0 + (7 * K + 5) * (0)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 5 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig5_2 (K : ℕ) : digit (7 * K + 5) 2 = 5 * K + 3 := by
  unfold digit
  rw [show (7 * K + 5) ^ 2 = 4 + (5 * K + 3 + (7 * K + 5) * (1 * K)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 4 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig5_3 (K : ℕ) : digit (7 * K + 5) 3 = 4 * K + 2 := by
  unfold digit
  rw [show (7 * K + 5) ^ 3 = 6 + (4 * K + 2 + (7 * K + 5) * (3 + 10 * K + 7 * K ^ 2)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 6 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig5_4 (K : ℕ) : digit (7 * K + 5) 4 = 6 * K + 4 := by
  unfold digit
  rw [show (7 * K + 5) ^ 4 = 2 + (6 * K + 4 + (7 * K + 5) * (17 + 75 * K + 105 * K ^ 2 + 49 * K ^ 3)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 2 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig5_5 (K : ℕ) : digit (7 * K + 5) 5 = 2 * K + 1 := by
  unfold digit
  rw [show (7 * K + 5) ^ 5 = 3 + (2 * K + 1 + (7 * K + 5) * (89 + 500 * K + 1050 * K ^ 2 + 980 * K ^ 3 + 343 * K ^ 4)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 3 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig5_6 (K : ℕ) : digit (7 * K + 5) 6 = 3 * K + 2 := by
  unfold digit
  rw [show (7 * K + 5) ^ 6 = 1 + (3 * K + 2 + (7 * K + 5) * (446 + 3125 * K + 8750 * K ^ 2 + 12250 * K ^ 3 + 8575 * K ^ 4 + 2401 * K ^ 5)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 1 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig6_1 (K : ℕ) : digit (7 * K + 6) 1 = 1 * K + 0 := by
  unfold digit
  rw [show (7 * K + 6) ^ 1 = 6 + (1 * K + 0 + (7 * K + 6) * (0)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 6 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem dig6_2 (K : ℕ) : digit (7 * K + 6) 2 = 6 * K + 5 := by
  unfold digit
  rw [show (7 * K + 6) ^ 2 = 1 + (6 * K + 5 + (7 * K + 6) * (1 * K)) * 7 by ring,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 7), show 1 / 7 = 0 by norm_num, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem ord2 : orderOf (2 : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm h0 => ?_⟩
  interval_cases m
  all_goals decide

theorem ord3 : orderOf (3 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm h0 => ?_⟩
  interval_cases m
  all_goals decide

theorem ord4 : orderOf (4 : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm h0 => ?_⟩
  interval_cases m
  all_goals decide

theorem ord5 : orderOf (5 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm h0 => ?_⟩
  interval_cases m
  all_goals decide

theorem ord6 : orderOf (6 : ZMod 7) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm h0 => ?_⟩
  interval_cases m
  all_goals decide


theorem len0 (b : ℕ) (h : b % 7 = 0) : len b = 1 := by
  unfold len; rw [if_pos h]

theorem len1 (b : ℕ) (h : b % 7 = 1) : len b = 1 := by
  unfold len
  rw [if_neg (by omega), ← ZMod.natCast_mod, h, Nat.cast_one, orderOf_one]

theorem len2 (b : ℕ) (h : b % 7 = 2) : len b = 3 := by
  unfold len
  rw [if_neg (by omega), ← ZMod.natCast_mod, h]
  exact ord2

theorem len3 (b : ℕ) (h : b % 7 = 3) : len b = 6 := by
  unfold len
  rw [if_neg (by omega), ← ZMod.natCast_mod, h]
  exact ord3

theorem len4 (b : ℕ) (h : b % 7 = 4) : len b = 3 := by
  unfold len
  rw [if_neg (by omega), ← ZMod.natCast_mod, h]
  exact ord4

theorem len5 (b : ℕ) (h : b % 7 = 5) : len b = 6 := by
  unfold len
  rw [if_neg (by omega), ← ZMod.natCast_mod, h]
  exact ord5

theorem len6 (b : ℕ) (h : b % 7 = 6) : len b = 2 := by
  unfold len
  rw [if_neg (by omega), ← ZMod.natCast_mod, h]
  exact ord6


theorem row_2 (Q : ℕ) : row (7 * Q + 2) = [1 * Q + 0, 2 * Q + 0, 4 * Q + 1] := by
  unfold row
  rw [len2 _ (by omega)]
  simp [List.range_succ, dig2_1, dig2_2, dig2_3]

theorem row_3 (Q : ℕ) : row (7 * Q + 3) = [1 * Q + 0, 3 * Q + 1, 2 * Q + 0, 6 * Q + 2, 4 * Q + 1, 5 * Q + 2] := by
  unfold row
  rw [len3 _ (by omega)]
  simp [List.range_succ, dig3_1, dig3_2, dig3_3, dig3_4, dig3_5, dig3_6]

theorem row_4 (Q : ℕ) : row (7 * Q + 4) = [1 * Q + 0, 4 * Q + 2, 2 * Q + 1] := by
  unfold row
  rw [len4 _ (by omega)]
  simp [List.range_succ, dig4_1, dig4_2, dig4_3]

theorem row_5 (Q : ℕ) : row (7 * Q + 5) = [1 * Q + 0, 5 * Q + 3, 4 * Q + 2, 6 * Q + 4, 2 * Q + 1, 3 * Q + 2] := by
  unfold row
  rw [len5 _ (by omega)]
  simp [List.range_succ, dig5_1, dig5_2, dig5_3, dig5_4, dig5_5, dig5_6]

theorem row_6 (Q : ℕ) : row (7 * Q + 6) = [1 * Q + 0, 6 * Q + 5] := by
  unfold row
  rw [len6 _ (by omega)]
  simp [List.range_succ, dig6_1, dig6_2]

theorem row_7 (Q : ℕ) : row (7 * Q + 7) = [1 * (Q + 1) + 0] := by
  unfold row
  rw [len0 _ (by omega)]
  rw [show 7 * Q + 7 = 7 * (Q + 1) by ring]
  simp [List.range_succ, dig0_1 (Q + 1) (by omega)]

theorem row_8 (Q : ℕ) : row (7 * Q + 8) = [1 * (Q + 1) + 0] := by
  unfold row
  rw [len1 _ (by omega)]
  rw [show 7 * Q + 8 = 7 * (Q + 1) + 1 by ring]
  simp [List.range_succ, dig1_1]


theorem len_pos (b : ℕ) : 1 ≤ len b := by
  have h := Nat.mod_lt b (show 0 < 7 by norm_num)
  interval_cases hb : b % 7
  · rw [len0 b hb]
  · rw [len1 b hb]
  · rw [len2 b hb]; norm_num
  · rw [len3 b hb]; norm_num
  · rw [len4 b hb]; norm_num
  · rw [len5 b hb]; norm_num
  · rw [len6 b hb]; norm_num

/-- The concatenation of the rows `2, ..., N + 1`. -/
noncomputable def F (N : ℕ) : List ℕ := ((List.range N).map fun i => row (i + 2)).flatten

theorem F_add (N M : ℕ) :
    F (N + M) = F N ++ ((List.range M).map fun i => row (N + i + 2)).flatten := by
  unfold F
  rw [List.range_add, List.map_append, List.flatten_append, List.map_map]
  rfl

theorem F_len (N : ℕ) : N ≤ (F N).length := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [F_add, List.length_append]
    simp only [List.range_one, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    have := len_pos (N + 0 + 2)
    simp only [row, List.length_map, List.length_range] at this ⊢
    omega

/-- The 22 entries of the rows `7Q + 2, ..., 7Q + 8`. -/
def BL (Q : ℕ) : List ℕ := [1 * Q + 0, 2 * Q + 0, 4 * Q + 1, 1 * Q + 0, 3 * Q + 1, 2 * Q + 0, 6 * Q + 2, 4 * Q + 1, 5 * Q + 2, 1 * Q + 0, 4 * Q + 2, 2 * Q + 1, 1 * Q + 0, 5 * Q + 3, 4 * Q + 2, 6 * Q + 4, 2 * Q + 1, 3 * Q + 2, 1 * Q + 0, 6 * Q + 5, 1 * (Q + 1) + 0, 1 * (Q + 1) + 0]

theorem block (Q : ℕ) : ((List.range 7).map fun i => row (7 * Q + i + 2)).flatten = BL Q := by
  rw [show (List.range 7) = [0, 1, 2, 3, 4, 5, 6] from rfl]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [show 7 * Q + 0 + 2 = 7 * Q + 2 from rfl, show 7 * Q + 1 + 2 = 7 * Q + 3 from rfl,
    show 7 * Q + 2 + 2 = 7 * Q + 4 from rfl, show 7 * Q + 3 + 2 = 7 * Q + 5 from rfl,
    show 7 * Q + 4 + 2 = 7 * Q + 6 from rfl, show 7 * Q + 5 + 2 = 7 * Q + 7 from rfl,
    show 7 * Q + 6 + 2 = 7 * Q + 8 from rfl, row_2, row_3, row_4, row_5, row_6, row_7, row_8]
  rfl

theorem F_len7 (Q : ℕ) : (F (7 * Q)).length = 22 * Q := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    rw [show 7 * (Q + 1) = 7 * Q + 7 by ring, F_add, List.length_append, ih, block]
    simp [BL]
    ring

theorem a_formula (Q r : ℕ) (hr : r < 22) : a (22 * Q + r + 2) = (BL Q).getD r 0 := by
  have h1 : a (22 * Q + r + 2) = (F (22 * Q + r + 2)).getD (22 * Q + r) 0 := rfl
  have hlen := F_len (22 * Q + r + 2)
  rw [h1, ← List.getD_append _
      (((List.range (7 * Q + 7)).map fun i => row (22 * Q + r + 2 + i + 2)).flatten) 0 _
      (by omega), ← F_add, show 22 * Q + r + 2 + (7 * Q + 7) = 7 * Q + 7 + (22 * Q + r + 2) by ring,
    F_add, F_add, block, List.append_assoc,
    List.getD_append_right _ _ _ _ (by rw [F_len7]; omega), F_len7,
    show 22 * Q + r - 22 * Q = r by omega, List.getD_append _ _ _ _ (by simp [BL]; omega)]

end PA262115

theorem OMA.solution : type_of% @OMA.S_oeis_a262115.main := by
  intro n hn
  obtain ⟨P, r, hr, rfl⟩ : ∃ P r, r < 22 ∧ n = 22 * (P + 2) + r + 2 :=
    ⟨(n - 2) / 22 - 2, (n - 2) % 22, Nat.mod_lt _ (by norm_num), by omega⟩
  rw [show 22 * (P + 2) + r + 2 - 22 = 22 * (P + 1) + r + 2 by omega,
    show 22 * (P + 2) + r + 2 - 44 = 22 * P + r + 2 by omega, PA262115.a_formula _ _ hr,
    PA262115.a_formula _ _ hr, PA262115.a_formula _ _ hr]
  interval_cases r <;> simp [PA262115.BL] <;> omega
