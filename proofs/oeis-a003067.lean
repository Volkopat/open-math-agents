import OMAStatements.S_oeis_a003067

-- Problem: A003067, Plouffe's conjectured g.f. (z^2+2+z^9+z^5)/(z-1)^2 is wrong.
-- Credit: @ShoQo
-- Proof: compute the sequence exactly (with its running product) up to a(21): a(19) = 79,
-- a(20) = 84, a(21) = 90. The coefficient of X^20 in (sum a(n+1) X^n) * (X - 1)^2 is
-- a(21) - 2 a(20) + a(19) = 1, while X^2 + 2 + X^9 + X^5 has coefficient 0 there.

open OMA.S_oeis_a003067 PowerSeries

namespace OMA_A003067_Proof

lemma round_val (x : ℚ) (z : ℤ) (h1 : (z : ℚ) - 1 / 2 ≤ x) (h2 : x < z + 1 / 2) : round x = z := by
  rw [round_eq, Int.floor_eq_iff]; constructor <;> linarith

lemma st_0 : st 0 = (2, 1 / 2) := by rw [st]

lemma st_1 : st 1 = (4, (3 / 8 : ℚ)) := by
  have hr : round ((2 : ℚ) + 1 / (1 / 2 : ℚ)) = 4 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (1 : ℕ) = 0 + 1 from rfl, st, st_0]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_2 : st 2 = (7, (9 / 28 : ℚ)) := by
  have hr : round ((4 : ℚ) + 1 / (3 / 8 : ℚ)) = 7 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (2 : ℕ) = 1 + 1 from rfl, st, st_1]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_3 : st 3 = (10, (81 / 280 : ℚ)) := by
  have hr : round ((7 : ℚ) + 1 / (9 / 28 : ℚ)) = 10 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (3 : ℕ) = 2 + 1 from rfl, st, st_2]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_4 : st 4 = (13, (243 / 910 : ℚ)) := by
  have hr : round ((10 : ℚ) + 1 / (81 / 280 : ℚ)) = 13 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (4 : ℕ) = 3 + 1 from rfl, st, st_3]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_5 : st 5 = (17, (1944 / 7735 : ℚ)) := by
  have hr : round ((13 : ℚ) + 1 / (243 / 910 : ℚ)) = 17 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (5 : ℕ) = 4 + 1 from rfl, st, st_4]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_6 : st 6 = (21, (2592 / 10829 : ℚ)) := by
  have hr : round ((17 : ℚ) + 1 / (1944 / 7735 : ℚ)) = 21 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (6 : ℕ) = 5 + 1 from rfl, st, st_5]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_7 : st 7 = (25, (62208 / 270725 : ℚ)) := by
  have hr : round ((21 : ℚ) + 1 / (2592 / 10829 : ℚ)) = 25 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (7 : ℕ) = 6 + 1 from rfl, st, st_6]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_8 : st 8 = (29, (248832 / 1121575 : ℚ)) := by
  have hr : round ((25 : ℚ) + 1 / (62208 / 270725 : ℚ)) = 29 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (8 : ℕ) = 7 + 1 from rfl, st, st_7]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_9 : st 9 = (34, (4105728 / 19066775 : ℚ)) := by
  have hr : round ((29 : ℚ) + 1 / (248832 / 1121575 : ℚ)) = 34 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (9 : ℕ) = 8 + 1 from rfl, st, st_8]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_10 : st 10 = (39, (52005888 / 247868075 : ℚ)) := by
  have hr : round ((34 : ℚ) + 1 / (4105728 / 19066775 : ℚ)) = 39 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (10 : ℕ) = 9 + 1 from rfl, st, st_9]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_11 : st 11 = (44, (50823936 / 247868075 : ℚ)) := by
  have hr : round ((39 : ℚ) + 1 / (52005888 / 247868075 : ℚ)) = 44 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (11 : ℕ) = 10 + 1 from rfl, st, st_10]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_12 : st 12 = (49, (2439548928 / 12145535675 : ℚ)) := by
  have hr : round ((44 : ℚ) + 1 / (50823936 / 247868075 : ℚ)) = 49 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (12 : ℕ) = 11 + 1 from rfl, st, st_11]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_13 : st 13 = (54, (2394372096 / 12145535675 : ℚ)) := by
  have hr : round ((49 : ℚ) + 1 / (2439548928 / 12145535675 : ℚ)) = 54 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (13 : ℕ) = 12 + 1 from rfl, st, st_12]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_14 : st 14 = (59, (4788744192 / 24709882925 : ℚ)) := by
  have hr : round ((54 : ℚ) + 1 / (2394372096 / 12145535675 : ℚ)) = 59 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (14 : ℕ) = 13 + 1 from rfl, st, st_13]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_15 : st 15 = (64, (673417152 / 3529983275 : ℚ)) := by
  have hr : round ((59 : ℚ) + 1 / (4788744192 / 24709882925 : ℚ)) = 64 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (15 : ℕ) = 14 + 1 from rfl, st, st_14]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_16 : st 16 = (69, (897889536 / 4775859725 : ℚ)) := by
  have hr : round ((64 : ℚ) + 1 / (673417152 / 3529983275 : ℚ)) = 69 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (16 : ℕ) = 15 + 1 from rfl, st, st_15]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_17 : st 17 = (74, (32772968064 / 176706809825 : ℚ)) := by
  have hr : round ((69 : ℚ) + 1 / (897889536 / 4775859725 : ℚ)) = 74 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (17 : ℕ) = 16 + 1 from rfl, st, st_16]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_18 : st 18 = (79, (196637808384 / 1073833690475 : ℚ)) := by
  have hr : round ((74 : ℚ) + 1 / (32772968064 / 176706809825 : ℚ)) = 79 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (18 : ℕ) = 17 + 1 from rfl, st, st_17]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_19 : st 19 = (84, (1360078174656 / 7516835833325 : ℚ)) := by
  have hr : round ((79 : ℚ) + 1 / (196637808384 / 1073833690475 : ℚ)) = 84 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (19 : ℕ) = 18 + 1 from rfl, st, st_18]
  simp only [Int.cast_ofNat, hr]
  norm_num

lemma st_20 : st 20 = (90, (6724830974688 / 37584179166625 : ℚ)) := by
  have hr : round ((84 : ℚ) + 1 / (1360078174656 / 7516835833325 : ℚ)) = 90 := round_val _ _ (by norm_num) (by norm_num)
  rw [show (20 : ℕ) = 19 + 1 from rfl, st, st_19]
  simp only [Int.cast_ofNat, hr]
  norm_num

end OMA_A003067_Proof

open OMA_A003067_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a003067.main := by
  intro h
  have hc := congrArg (coeff 20) h
  have e : (mk (fun n => (a (n + 1) : ℚ)) * (X - 1) ^ 2 : ℚ⟦X⟧) =
      mk (fun n => (a (n + 1) : ℚ)) * X ^ 2 - 2 • (mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) +
        mk (fun n => (a (n + 1) : ℚ)) := by ring
  rw [e] at hc
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_mk, coeff_X_pow, coeff_one] at hc
  rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from (map_ofNat C 2).symm, coeff_C] at hc
  norm_num [a, st_18, st_19, st_20] at hc
