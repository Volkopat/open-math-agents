import OMAStatements.S_mo_433111

open scoped BigOperators

namespace Mo433111Proof

private def xBlocks : List (List Nat) := [
  [237600, 415800, 166320, 184800, 110880, 138600, 83160, 103950, 66528, 79200, 50400, 61600, 39600, 55440, 34650, 46200],
  [30800, 37800, 26400, 29700, 22176, 23760, 19800, 21600, 17325, 18900, 15840, 16800, 15400, 15120, 13860, 12600],
  [11880, 11550, 10080, 9900, 8800, 7920, 7425, 6930, 6160, 5544, 5400, 4400, 4158, 3465, 3168, 2640],
  [2772, 1980, 2475, 1386, 2200, 864, 2100, 480, 2160, 189, 2400, 63, 2800, 44, 3300, 36],
  [3960, 50, 4620, 75, 5280, 108, 5775, 112, 6048, 100, 6600, 80, 7200, 110, 7700, 99],
  [8400, 150, 9450, 672, 10395, 1800, 10800, 3696, 9240, 4950, 7560, 5040, 5940, 4320, 4725, 3600],
  [3850, 3150, 3080, 2970, 2520, 2464, 2310, 2016, 1925, 1890, 1760, 1680, 1575, 1584, 1440, 1485],
  [1260, 1350, 1188, 1232, 1100, 1155, 1008, 1050, 924, 900, 840, 792, 756, 660, 693, 528],
  [630, 495, 525, 440, 450, 432, 400, 396, 352, 360, 308, 330, 275, 297, 220, 280],
  [176, 264, 132, 240, 90, 252, 55, 270, 28, 288, 7, 315, 2, 350, 4, 385],
  [3, 420, 1, 462, 5, 504, 6, 540, 9, 594, 42, 600, 66, 550, 40, 560],
  [14, 616, 10, 675, 15, 720, 11, 770, 8, 825, 12, 880, 16, 945, 27, 990],
  [35, 1056, 33, 1120, 30, 1200, 18, 1320, 24, 1400, 22, 1512, 25, 1650, 20, 1848],
  [21, 2079, 32, 2376, 45, 2700, 48, 3024, 54, 3360, 60, 3780, 77, 4200, 56, 4752],
  [72, 5600, 70, 6300, 88, 7392, 96, 8316, 84, 9504, 105, 11088, 120, 12320, 168, 13200],
  [126, 14850, 135, 16632, 140, 18480, 154, 20790, 160, 23100, 180, 25200, 144, 27720, 165, 30240],
  [210, 33264, 231, 36960, 225, 41580, 175, 47520, 300, 51975, 336, 59400, 224, 69300, 800, 75600],
  [216, 92400, 200, 118800, 700, 151200, 378, 207900, 198, 332640, 1080, 554400, 1540, 1663200, 277200, 831600]
]

private def pBlocks : List (List Nat) := [
  [4082, 11843, 5625, 7408, 5000, 7408, 4879, 7134, 5134, 7072, 4981, 6482, 4396, 6858, 4500, 6735],
  [4798, 6738, 5090, 6466, 5091, 5740, 5087, 5963, 4988, 5791, 4920, 5505, 5315, 5715, 5662, 5378],
  [5493, 5781, 5391, 5922, 5735, 5518, 5673, 5922, 5629, 5658, 6310, 5773, 6269, 5966, 5854, 5556],
  [6223, 5129, 6902, 4524, 7423, 3349, 7955, 2044, 8343, 768, 8383, 222, 8374, 132, 8259, 90],
  [8480, 107, 8628, 140, 8976, 184, 9375, 183, 9027, 150, 9066, 110, 9219, 142, 9060, 116],
  [8750, 149, 8539, 552, 8250, 1242, 8349, 2605, 7387, 3929, 6886, 4913, 6568, 5190, 6343, 5143],
  [6180, 5207, 5611, 5960, 5279, 5696, 5862, 5285, 5274, 5495, 5408, 5319, 5209, 5416, 5246, 5690],
  [4965, 5579, 5095, 5464, 5086, 5613, 5107, 5757, 5311, 5515, 5427, 5594, 5588, 5406, 5985, 4694],
  [6177, 5130, 5899, 4989, 5409, 5428, 5348, 5562, 5270, 5643, 5091, 5770, 5320, 5940, 4825, 6364],
  [4445, 7097, 4000, 7018, 2932, 7754, 1846, 8545, 950, 8945, 221, 8949, 57, 8998, 104, 9102],
  [72, 9072, 22, 9077, 99, 9231, 110, 8956, 142, 9253, 631, 9741, 1119, 9167, 697, 8889],
  [224, 8993, 145, 9184, 206, 9219, 142, 9244, 96, 9249, 134, 9158, 165, 9293, 264, 9075],
  [322, 9159, 287, 9106, 247, 8969, 134, 9270, 169, 9127, 144, 9027, 150, 8833, 108, 8800],
  [100, 8634, 133, 8656, 164, 8790, 156, 8858, 158, 8750, 156, 8838, 181, 8736, 117, 8378],
  [127, 8792, 110, 8423, 118, 8788, 115, 8674, 88, 8492, 94, 8914, 97, 9217, 127, 8815],
  [85, 8857, 81, 8933, 76, 8824, 74, 8939, 69, 9102, 72, 9044, 52, 9117, 55, 9034],
  [63, 8945, 63, 8842, 54, 8718, 37, 9091, 58, 8701, 57, 8544, 32, 9071, 106, 8163],
  [24, 7765, 17, 7821, 47, 7260, 19, 6247, 6, 5989, 20, 3331, 8, 15000, 2593, 12728]
]

private def sortedBlocks : List (List Nat) := [
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18],
  [20, 21, 22, 24, 25, 27, 28, 30, 32, 33, 35, 36, 40, 42, 44, 45],
  [48, 50, 54, 55, 56, 60, 63, 66, 70, 72, 75, 77, 80, 84, 88, 90],
  [96, 99, 100, 105, 108, 110, 112, 120, 126, 132, 135, 140, 144, 150, 154, 160],
  [165, 168, 175, 176, 180, 189, 198, 200, 210, 216, 220, 224, 225, 231, 240, 252],
  [264, 270, 275, 280, 288, 297, 300, 308, 315, 330, 336, 350, 352, 360, 378, 385],
  [396, 400, 420, 432, 440, 450, 462, 480, 495, 504, 525, 528, 540, 550, 560, 594],
  [600, 616, 630, 660, 672, 675, 693, 700, 720, 756, 770, 792, 800, 825, 840, 864],
  [880, 900, 924, 945, 990, 1008, 1050, 1056, 1080, 1100, 1120, 1155, 1188, 1200, 1232, 1260],
  [1320, 1350, 1386, 1400, 1440, 1485, 1512, 1540, 1575, 1584, 1650, 1680, 1760, 1800, 1848, 1890],
  [1925, 1980, 2016, 2079, 2100, 2160, 2200, 2310, 2376, 2400, 2464, 2475, 2520, 2640, 2700, 2772],
  [2800, 2970, 3024, 3080, 3150, 3168, 3300, 3360, 3465, 3600, 3696, 3780, 3850, 3960, 4158, 4200],
  [4320, 4400, 4620, 4725, 4752, 4950, 5040, 5280, 5400, 5544, 5600, 5775, 5940, 6048, 6160, 6300],
  [6600, 6930, 7200, 7392, 7425, 7560, 7700, 7920, 8316, 8400, 8800, 9240, 9450, 9504, 9900, 10080],
  [10395, 10800, 11088, 11550, 11880, 12320, 12600, 13200, 13860, 14850, 15120, 15400, 15840, 16632, 16800, 17325],
  [18480, 18900, 19800, 20790, 21600, 22176, 23100, 23760, 25200, 26400, 27720, 29700, 30240, 30800, 33264, 34650],
  [36960, 37800, 39600, 41580, 46200, 47520, 50400, 51975, 55440, 59400, 61600, 66528, 69300, 75600, 79200, 83160],
  [92400, 103950, 110880, 118800, 138600, 151200, 166320, 184800, 207900, 237600, 277200, 332640, 415800, 554400, 831600, 1663200]
]

private def permIdxBlocks : List (List Nat) := [
  [162, 156, 160, 158, 164, 166, 154, 184, 168, 178, 182, 186, 176, 180, 188, 198],
  [206, 208, 202, 200, 204, 190, 152, 196, 210, 194, 192, 63, 174, 170, 61, 212],
  [214, 65, 216, 150, 222, 218, 59, 172, 226, 224, 67, 220, 75, 232, 228, 148],
  [230, 79, 73, 234, 69, 77, 71, 236, 240, 146, 242, 244, 252, 81, 246, 248],
  [254, 238, 262, 144, 250, 57, 280, 274, 256, 272, 142, 268, 260, 258, 147, 149],
  [145, 151, 140, 143, 153, 141, 264, 138, 155, 139, 266, 157, 136, 137, 278, 159],
  [135, 134, 161, 133, 131, 132, 163, 55, 129, 165, 130, 127, 167, 173, 175, 169],
  [171, 177, 128, 125, 83, 179, 126, 276, 181, 124, 183, 123, 270, 185, 122, 53],
  [187, 121, 120, 189, 191, 118, 119, 193, 282, 116, 195, 117, 114, 197, 115, 112],
  [199, 113, 51, 201, 110, 111, 203, 284, 108, 109, 205, 107, 106, 85, 207, 105],
  [104, 49, 103, 209, 54, 56, 52, 102, 211, 58, 101, 50, 100, 47, 213, 48],
  [60, 99, 215, 98, 97, 46, 62, 217, 45, 95, 87, 219, 96, 64, 44, 221],
  [93, 43, 66, 94, 223, 89, 91, 68, 42, 41, 225, 70, 92, 72, 40, 227],
  [74, 39, 76, 229, 38, 90, 78, 37, 231, 80, 36, 88, 82, 233, 35, 34],
  [84, 86, 235, 33, 32, 237, 31, 239, 30, 241, 29, 28, 26, 243, 27, 24],
  [245, 25, 22, 247, 23, 20, 249, 21, 251, 18, 253, 19, 255, 16, 257, 14],
  [259, 17, 12, 261, 15, 263, 10, 265, 13, 267, 11, 8, 269, 271, 9, 6],
  [273, 7, 4, 275, 5, 277, 2, 3, 279, 0, 286, 281, 1, 283, 287, 285]
]

private def xFn (i : Nat) : Nat := (xBlocks.getD (i / 16) []).getD (i % 16) 0

private def pFn (i : Nat) : Nat := (pBlocks.getD (i / 16) []).getD (i % 16) 0

private def isStrictInc : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a < b) && isStrictInc (b :: rest)

private def lastLtHead : List Nat → List Nat → Bool
  | [a], b :: _ => a < b
  | _ :: a :: as, bs => lastLtHead (a :: as) bs
  | _, _ => false

private def allRowsStrictInc : List (List Nat) → Bool
  | [] => true
  | [r] => isStrictInc r
  | r1 :: r2 :: rs => isStrictInc r1 && lastLtHead r1 r2 && allRowsStrictInc (r2 :: rs)

private def checkPermRow : List Nat → List Nat → Bool
  | [], [] => true
  | i :: is, d :: ds => (i < 288) && (xFn i == d) && checkPermRow is ds
  | _, _ => false

private def checkPermBlocks : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | r1 :: rs1, r2 :: rs2 => checkPermRow r1 r2 && checkPermBlocks rs1 rs2
  | _, _ => false

private def checkBoundsPow2 (lo : Nat) : Nat → Bool
  | 0 =>
    let d := xFn ((lo + 1) % 288) + xFn ((lo + 2) % 288)
    10000 * xFn lo ≤ pFn lo * d
  | d + 1 => checkBoundsPow2 lo d && checkBoundsPow2 (lo + 2 ^ d) d

private def sumPow2 (lo : Nat) : Nat → Nat
  | 0 => pFn lo
  | d + 1 => sumPow2 lo d + sumPow2 (lo + 2 ^ d) d

private theorem h_xBlocks_len : xBlocks.length = 18 := rfl
private theorem h_xBlocks_rows : xBlocks.all (fun row => row.length == 16) = true := rfl
private theorem h_xBlocks_divs :
    xBlocks.all (fun row => row.all (fun d => (0 < d) && (1663200 % d == 0))) = true := rfl
private theorem h_sorted_len : sortedBlocks.length = 18 := rfl
private theorem h_sorted_rows : sortedBlocks.all (fun row => row.length == 16) = true := rfl
private theorem h_sorted_inc : allRowsStrictInc sortedBlocks = true := rfl
private theorem h_perm : checkPermBlocks permIdxBlocks sortedBlocks = true := rfl
private theorem h_bounds1 : checkBoundsPow2 0 8 = true := rfl
private theorem h_bounds2 : checkBoundsPow2 256 5 = true := rfl
private theorem h_sum1 : sumPow2 0 8 = 1298694 := rfl
private theorem h_sum2 : sumPow2 256 5 = 139420 := rfl
private theorem h_sum_lt : Nat.ble (2 * (1298694 + 139420) + 1) (288 * 10000) = true := rfl

private lemma getD_mem_of_lt {α : Type*} (d : α) :
    ∀ (l : List α) (k : Nat), k < l.length → l.getD k d ∈ l := by
  intro l
  induction l with
  | nil =>
    intro k hk
    exact absurd hk (Nat.not_lt_zero k)
  | cons a as ih =>
    intro k hk
    cases k with
    | zero => exact List.Mem.head _
    | succ k' => exact List.Mem.tail _ (ih k' (Nat.lt_of_succ_lt_succ hk))

private lemma xFn_pos_and_dvd {i : Nat} (hi : i < 288) : 0 < xFn i ∧ xFn i ∣ 1663200 := by
  have hq : i / 16 < xBlocks.length := by
    rw [h_xBlocks_len]
    exact Nat.div_lt_of_lt_mul hi
  have hrow_mem : xBlocks.getD (i / 16) [] ∈ xBlocks := getD_mem_of_lt [] xBlocks (i / 16) hq
  have hrow_len : (xBlocks.getD (i / 16) []).length = 16 := by
    have h1 := List.all_eq_true.mp h_xBlocks_rows _ hrow_mem
    exact beq_iff_eq.mp h1
  have hr : i % 16 < (xBlocks.getD (i / 16) []).length := by
    rw [hrow_len]
    exact Nat.mod_lt i (Nat.zero_lt_succ 15)
  have hx_mem : xFn i ∈ xBlocks.getD (i / 16) [] := getD_mem_of_lt 0 _ (i % 16) hr
  have hrow_ok := List.all_eq_true.mp h_xBlocks_divs _ hrow_mem
  have hx_ok := List.all_eq_true.mp hrow_ok _ hx_mem
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx_ok
  exact ⟨hx_ok.1, Nat.dvd_of_mod_eq_zero hx_ok.2⟩

private lemma lt_of_isStrictInc :
    ∀ (a : Nat) (l : List Nat), isStrictInc (a :: l) = true → ∀ y ∈ l, a < y := by
  intro a l
  induction l generalizing a with
  | nil =>
    intro _ y hy
    cases hy
  | cons b bs ih =>
    intro h y hy
    simp only [isStrictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact h.1
    · exact Nat.lt_trans h.1 (ih b h.2 y hy')

private lemma nodup_of_isStrictInc :
    ∀ (l : List Nat), isStrictInc l = true → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a as ih =>
    intro h
    have htail : isStrictInc as = true := by
      cases as with
      | nil => rfl
      | cons b bs =>
        simp only [isStrictInc, Bool.and_eq_true] at h
        exact h.2
    refine List.nodup_cons.mpr ⟨?_, ih htail⟩
    intro ha
    exact Nat.lt_irrefl a (lt_of_isStrictInc a as h a ha)

private lemma mem_of_isStrictInc_ge_head :
    ∀ (b : Nat) (bs : List Nat), isStrictInc (b :: bs) = true → ∀ y ∈ b :: bs, b ≤ y := by
  intro b bs h y hy
  rcases List.mem_cons.mp hy with rfl | hy'
  · exact le_refl _
  · exact Nat.le_of_lt (lt_of_isStrictInc b bs h y hy')

private lemma lastLtHead_nil_right : ∀ (r : List Nat), lastLtHead r [] = false
  | [] => rfl
  | [_] => rfl
  | _ :: a :: as => lastLtHead_nil_right (a :: as)

private lemma mem_le_last_of_lastLtHead :
    ∀ (r1 r2 : List Nat), isStrictInc r1 = true → lastLtHead r1 r2 = true →
      ∀ x ∈ r1, ∀ y ∈ r2, isStrictInc r2 = true → x < y := by
  intro r1
  induction r1 with
  | nil => intro _ _ h; simp [lastLtHead] at h
  | cons a as ih =>
    intro r2 hinc1 hlt x hx y hy hinc2
    cases r2 with
    | nil => cases hy
    | cons b bs =>
      have hy_ge : b ≤ y := mem_of_isStrictInc_ge_head b bs hinc2 y hy
      cases as with
      | nil =>
        simp only [lastLtHead, decide_eq_true_eq] at hlt
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Nat.lt_of_lt_of_le hlt hy_ge
        · cases hx'
      | cons a2 as2 =>
        have htail1 : isStrictInc (a2 :: as2) = true := by
          simp only [isStrictInc, Bool.and_eq_true] at hinc1
          exact hinc1.2
        have hlt' : lastLtHead (a2 :: as2) (b :: bs) = true := by
          simpa [lastLtHead] using hlt
        have ha_lt_a2 : a < a2 := by
          simp only [isStrictInc, Bool.and_eq_true, decide_eq_true_eq] at hinc1
          exact hinc1.1
        rcases List.mem_cons.mp hx with rfl | hx'
        · have ha2_lt_y := ih (b :: bs) htail1 hlt' a2 (List.Mem.head _) y hy hinc2
          exact Nat.lt_trans ha_lt_a2 ha2_lt_y
        · exact ih (b :: bs) htail1 hlt' x hx' y hy hinc2

private def blocksFinset : List (List Nat) → Finset Nat
  | [] => ∅
  | r :: rs => r.toFinset ∪ blocksFinset rs

private lemma head_lt_of_allRowsStrictInc :
    ∀ (r : List Nat) (rs : List (List Nat)),
      allRowsStrictInc (r :: rs) = true →
      ∀ x ∈ r, ∀ y ∈ blocksFinset rs, x < y := by
  intro r rs
  induction rs generalizing r with
  | nil =>
    intro _ _ _ _ hy
    simp [blocksFinset] at hy
  | cons r2 rs2 ih =>
    intro h x hx y hy
    simp only [allRowsStrictInc, Bool.and_eq_true] at h
    have hr1 : isStrictInc r = true := h.1.1
    have hlast : lastLtHead r r2 = true := h.1.2
    have hrest : allRowsStrictInc (r2 :: rs2) = true := h.2
    have hr2 : isStrictInc r2 = true := by
      cases rs2 with
      | nil => exact hrest
      | cons _ _ =>
        simp only [allRowsStrictInc, Bool.and_eq_true] at hrest
        exact hrest.1.1
    simp only [blocksFinset, Finset.mem_union, List.mem_toFinset] at hy
    rcases hy with hy2 | hy_rest
    · exact mem_le_last_of_lastLtHead r r2 hr1 hlast x hx y hy2 hr2
    · cases r2 with
      | nil =>
        rw [lastLtHead_nil_right] at hlast
        cases hlast
      | cons b bs =>
        have hx_lt_b : x < b := mem_le_last_of_lastLtHead r (b :: bs) hr1 hlast x hx b (List.Mem.head _) hr2
        have hb_lt_y : b < y := ih (b :: bs) hrest b (List.Mem.head _) y hy_rest
        exact Nat.lt_trans hx_lt_b hb_lt_y

private lemma blocksFinset_card :
    ∀ (rows : List (List Nat)),
      allRowsStrictInc rows = true →
      rows.all (fun row => row.length == 16) = true →
      (blocksFinset rows).card = 16 * rows.length := by
  intro rows
  induction rows with
  | nil =>
    intro _ _
    rfl
  | cons r rs ih =>
    intro hinc hlen
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hlen
    have hr_inc : isStrictInc r = true := by
      cases rs with
      | nil => exact hinc
      | cons _ _ =>
        simp only [allRowsStrictInc, Bool.and_eq_true] at hinc
        exact hinc.1.1
    have hrs_inc : allRowsStrictInc rs = true := by
      cases rs with
      | nil => rfl
      | cons _ _ =>
        simp only [allRowsStrictInc, Bool.and_eq_true] at hinc
        exact hinc.2
    have hdisj : Disjoint r.toFinset (blocksFinset rs) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have hlt := head_lt_of_allRowsStrictInc r rs hinc x (List.mem_toFinset.mp hx1) x hx2
      exact Nat.lt_irrefl x hlt
    rw [blocksFinset, Finset.card_union_of_disjoint hdisj]
    rw [List.toFinset_card_of_nodup (nodup_of_isStrictInc r hr_inc), hlen.1]
    rw [ih hrs_inc hlen.2, List.length_cons, Nat.mul_succ, Nat.add_comm]

private lemma mem_image_of_checkPermRow :
    ∀ (is ds : List Nat), checkPermRow is ds = true →
      ∀ d ∈ ds, d ∈ (Finset.range 288).image xFn := by
  intro is ds h
  induction is generalizing ds with
  | nil =>
    cases ds with
    | nil =>
      intro d hd
      cases hd
    | cons _ _ => simp [checkPermRow] at h
  | cons i is ih =>
    cases ds with
    | nil => simp [checkPermRow] at h
    | cons d ds =>
      simp only [checkPermRow, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr h.1.1, h.1.2⟩
      · exact ih ds h.2 v hv'

private lemma mem_image_of_checkPermBlocks :
    ∀ (bs1 bs2 : List (List Nat)), checkPermBlocks bs1 bs2 = true →
      blocksFinset bs2 ⊆ (Finset.range 288).image xFn := by
  intro bs1 bs2 h
  induction bs1 generalizing bs2 with
  | nil =>
    cases bs2 with
    | nil => simp [blocksFinset]
    | cons _ _ => simp [checkPermBlocks] at h
  | cons r1 rs1 ih =>
    cases bs2 with
    | nil => simp [checkPermBlocks] at h
    | cons r2 rs2 =>
      simp only [checkPermBlocks, Bool.and_eq_true] at h
      intro v hv
      simp only [blocksFinset, Finset.mem_union, List.mem_toFinset] at hv
      rcases hv with hv1 | hv2
      · exact mem_image_of_checkPermRow r1 r2 h.1 v hv1
      · exact ih rs2 h.2 hv2

private lemma bound_of_checkBoundsPow2 :
    ∀ (d lo k : Nat), checkBoundsPow2 lo d = true → lo ≤ k → k < lo + 2 ^ d →
      10000 * xFn k ≤ pFn k * (xFn ((k + 1) % 288) + xFn ((k + 2) % 288)) := by
  intro d
  induction d with
  | zero =>
    intro lo k h hlo hhi
    have hkeq : k = lo := Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlo
    subst hkeq
    simpa [checkBoundsPow2] using h
  | succ d ih =>
    intro lo k h hlo hhi
    simp only [checkBoundsPow2, Bool.and_eq_true] at h
    by_cases hlt : k < lo + 2 ^ d
    · exact ih lo k h.1 hlo hlt
    · have hge : lo + 2 ^ d ≤ k := Nat.le_of_not_lt hlt
      have hhi' : k < lo + 2 ^ d + 2 ^ d := by
        simpa [Nat.pow_succ, Nat.mul_two, Nat.add_assoc] using hhi
      exact ih (lo + 2 ^ d) k h.2 hge hhi'

private lemma my_sum_range_add (f : Nat → ℚ) (a b : Nat) :
    (∑ i ∈ Finset.range (a + b), f i) =
    (∑ i ∈ Finset.range a, f i) + (∑ i ∈ Finset.range b, f (a + i)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, Rat.add_assoc]

private lemma sumPow2_eq_sum_range :
    ∀ (d lo : Nat), (∑ i ∈ Finset.range (2 ^ d), (pFn (lo + i) : ℚ)) = ((sumPow2 lo d : Nat) : ℚ)
  | 0, lo => by simp [sumPow2]
  | d + 1, lo => by
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ, Nat.mul_two]
    rw [hpow, my_sum_range_add]
    have ih1 := sumPow2_eq_sum_range d lo
    have ih2 := sumPow2_eq_sum_range d (lo + 2 ^ d)
    have hshift : (∑ i ∈ Finset.range (2 ^ d), (pFn (lo + (2 ^ d + i)) : ℚ)) =
        ∑ i ∈ Finset.range (2 ^ d), (pFn ((lo + 2 ^ d) + i) : ℚ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_assoc]
    rw [hshift, ih1, ih2, sumPow2, ← Rat.natCast_add]

private lemma rat_lt_of_le_of_lt {a b c : ℚ} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rw [← Rat.not_le]
  intro hca
  exact (Rat.not_le.mpr hbc) (Rat.le_trans hca hab)

private lemma rat_add_pos {a b : ℚ} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  have hb' : a < a + b := by
    have h := Rat.add_lt_add_left (a := 0) (b := b) (c := a) |>.mpr hb
    rwa [Rat.add_zero] at h
  exact rat_lt_of_le_of_lt (Rat.le_of_lt ha) hb'

private lemma rat_add_le_add {a b c d : ℚ} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr h1) (Rat.add_le_add_left.mpr h2)

private lemma rat_sum_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℚ)
    (h : ∀ i ∈ s, f i ≤ g i) : (∑ i ∈ s, f i) ≤ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact rat_add_le_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

private lemma rat_sum_div_const (s : Finset Nat) (f : Nat → ℚ) (c : ℚ) :
    (∑ i ∈ s, f i / c) = (∑ i ∈ s, f i) / c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Rat.div_def]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]

private lemma rat_div_le_div {a b c d : ℚ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  apply Rat.le_of_mul_le_mul_right _ hb
  apply Rat.le_of_mul_le_mul_right _ hd
  rw [Rat.div_mul_cancel (Rat.ne_of_gt hb)]
  rw [Rat.mul_assoc, Rat.mul_comm b d, ← Rat.mul_assoc, Rat.div_mul_cancel (Rat.ne_of_gt hd)]
  exact h

private lemma rat_div_lt_div {a b c d : ℚ} (hb : 0 < b) (hd : 0 < d) (h : a * d < c * b) :
    a / b < c / d := by
  apply Rat.lt_of_mul_lt_mul_right _ (Rat.le_of_lt hb)
  apply Rat.lt_of_mul_lt_mul_right _ (Rat.le_of_lt hd)
  rw [Rat.div_mul_cancel (Rat.ne_of_gt hb)]
  rw [Rat.mul_assoc, Rat.mul_comm b d, ← Rat.mul_assoc, Rat.div_mul_cancel (Rat.ne_of_gt hd)]
  exact h

private lemma card_divisors_mul_le (a b : Nat) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hsub : (a * b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    rcases Nat.dvd_mul.mp hd.1 with ⟨u, v, hu, hv, rfl⟩
    exact Finset.mem_image.mpr ⟨(u, v),
      Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hu, ha⟩, Nat.mem_divisors.mpr ⟨hv, hb⟩⟩,
      rfl⟩
  calc (a * b).divisors.card
      ≤ ((a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2)).card := Finset.card_le_card hsub
    _ ≤ (a.divisors ×ˢ b.divisors).card := Finset.card_image_le
    _ = a.divisors.card * b.divisors.card := Finset.card_product _ _

private lemma card_divisors_mul5_le (a b c d e : Nat) :
    (a * (b * (c * (d * e)))).divisors.card ≤
      a.divisors.card * (b.divisors.card * (c.divisors.card * (d.divisors.card * e.divisors.card))) := by
  have h1 := card_divisors_mul_le a (b * (c * (d * e)))
  have h2 := card_divisors_mul_le b (c * (d * e))
  have h3 := card_divisors_mul_le c (d * e)
  have h4 := card_divisors_mul_le d e
  exact Nat.le_trans h1 (Nat.mul_le_mul_left _
    (Nat.le_trans h2 (Nat.mul_le_mul_left _
      (Nat.le_trans h3 (Nat.mul_le_mul_left _ h4)))))

private lemma card_divisors_prime_pow {p : Nat} (hp : p.Prime) (k : Nat) :
    (p ^ k).divisors.card = k + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

private lemma card_divisors_N_le : (1663200 : Nat).divisors.card ≤ 288 := by
  have hN : (1663200 : Nat) = 2 ^ 5 * (3 ^ 3 * (5 ^ 2 * (7 ^ 1 * 11 ^ 1))) := rfl
  rw [hN]
  have hp2 : Nat.Prime 2 := by decide
  have hp3 : Nat.Prime 3 := by decide
  have hp5 : Nat.Prime 5 := by decide
  have hp7 : Nat.Prime 7 := by decide
  have hp11 : Nat.Prime 11 := by decide
  have h := card_divisors_mul5_le (2 ^ 5) (3 ^ 3) (5 ^ 2) (7 ^ 1) (11 ^ 1)
  rw [card_divisors_prime_pow hp2 5, card_divisors_prime_pow hp3 3,
      card_divisors_prime_pow hp5 2, card_divisors_prime_pow hp7 1,
      card_divisors_prime_pow hp11 1] at h
  exact h

end Mo433111Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_433111.main) := by
  intro h
  have hN_pos : 0 < 1663200 := Nat.zero_lt_succ (1663200 - 1)
  have hN_ne : (1663200 : Nat) ≠ 0 := Nat.succ_ne_zero (1663200 - 1)
  have hsub_divs : (Finset.range 288).image Mo433111Proof.xFn ⊆ (1663200 : Nat).divisors := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨i, hi, rfl⟩
    exact Nat.mem_divisors.mpr ⟨(Mo433111Proof.xFn_pos_and_dvd (Finset.mem_range.mp hi)).2, hN_ne⟩
  have hsub_sorted : Mo433111Proof.blocksFinset Mo433111Proof.sortedBlocks ⊆
      (Finset.range 288).image Mo433111Proof.xFn :=
    Mo433111Proof.mem_image_of_checkPermBlocks _ _ Mo433111Proof.h_perm
  have hcard_sorted : (Mo433111Proof.blocksFinset Mo433111Proof.sortedBlocks).card = 288 := by
    rw [Mo433111Proof.blocksFinset_card _ Mo433111Proof.h_sorted_inc Mo433111Proof.h_sorted_rows]
    rw [Mo433111Proof.h_sorted_len]
  have hcard_img_ge : 288 ≤ ((Finset.range 288).image Mo433111Proof.xFn).card :=
    Nat.le_trans (Nat.le_of_eq hcard_sorted.symm) (Finset.card_le_card hsub_sorted)
  have hcard_img_le : ((Finset.range 288).image Mo433111Proof.xFn).card ≤ 288 := by
    calc ((Finset.range 288).image Mo433111Proof.xFn).card
        ≤ (Finset.range 288).card := Finset.card_image_le
      _ = 288 := Finset.card_range 288
  have hcard_img : ((Finset.range 288).image Mo433111Proof.xFn).card = 288 :=
    Nat.le_antisymm hcard_img_le hcard_img_ge
  have hcard_N : (1663200 : Nat).divisors.card = 288 := by
    apply Nat.le_antisymm Mo433111Proof.card_divisors_N_le
    exact Nat.le_trans (Nat.le_of_eq hcard_img.symm) (Finset.card_le_card hsub_divs)
  have himg_eq : (Finset.range 288).image Mo433111Proof.xFn = (1663200 : Nat).divisors := by
    apply Finset.eq_of_subset_of_card_le hsub_divs
    rw [hcard_img, hcard_N]
  have hinj : Set.InjOn Mo433111Proof.xFn (Set.Iio 288) := by
    have hrange_eq : (Finset.range 288 : Set Nat) = Set.Iio 288 := by
      ext i; simp
    rw [← hrange_eq]
    exact Finset.card_image_iff.mp (by rw [hcard_img, Finset.card_range])
  have hmaps : Set.MapsTo Mo433111Proof.xFn (Set.Iio 288) (↑(1663200 : Nat).divisors : Set Nat) := by
    intro i hi
    exact hsub_divs (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi))
  have hsurj : Set.SurjOn Mo433111Proof.xFn (Set.Iio 288) (↑(1663200 : Nat).divisors : Set Nat) := by
    intro d hd
    have hd' : d ∈ (Finset.range 288).image Mo433111Proof.xFn := himg_eq ▸ hd
    rcases Finset.mem_image.mp hd' with ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  have hbij : Set.BijOn Mo433111Proof.xFn (Set.Iio 288) (↑(1663200 : Nat).divisors : Set Nat) :=
    ⟨hmaps, hinj, hsurj⟩
  have hle := h 1663200 hN_pos Mo433111Proof.xFn
  dsimp only at hle
  rw [hcard_N] at hle
  have hle' := hle hbij
  have hsum_le :
      (∑ i ∈ Finset.range 288, (Mo433111Proof.xFn i : ℚ) /
        ((Mo433111Proof.xFn ((i + 1) % 288) : ℚ) + (Mo433111Proof.xFn ((i + 2) % 288) : ℚ))) ≤
      ∑ i ∈ Finset.range 288, (Mo433111Proof.pFn i : ℚ) / (10000 : ℚ) := by
    apply Mo433111Proof.rat_sum_le_sum
    intro i hi
    have hi' : i < 288 := Finset.mem_range.mp hi
    have h1' : (i + 1) % 288 < 288 := Nat.mod_lt _ (Nat.zero_lt_succ (288 - 1))
    have h2' : (i + 2) % 288 < 288 := Nat.mod_lt _ (Nat.zero_lt_succ (288 - 1))
    have hp1 : 0 < Mo433111Proof.xFn ((i + 1) % 288) := (Mo433111Proof.xFn_pos_and_dvd h1').1
    have hp2 : 0 < Mo433111Proof.xFn ((i + 2) % 288) := (Mo433111Proof.xFn_pos_and_dvd h2').1
    have hden_pos : (0 : ℚ) < (Mo433111Proof.xFn ((i + 1) % 288) : ℚ) + (Mo433111Proof.xFn ((i + 2) % 288) : ℚ) :=
      Mo433111Proof.rat_add_pos (Rat.natCast_lt_natCast.mpr hp1) (Rat.natCast_lt_natCast.mpr hp2)
    have hM_pos : (0 : ℚ) < (10000 : ℚ) := Rat.natCast_lt_natCast.mpr (Nat.zero_lt_succ (10000 - 1))
    apply Mo433111Proof.rat_div_le_div hden_pos hM_pos
    have hnat : 10000 * Mo433111Proof.xFn i ≤
        Mo433111Proof.pFn i * (Mo433111Proof.xFn ((i + 1) % 288) + Mo433111Proof.xFn ((i + 2) % 288)) := by
      by_cases h256 : i < 256
      · exact Mo433111Proof.bound_of_checkBoundsPow2 8 0 i Mo433111Proof.h_bounds1 (Nat.zero_le i) h256
      · exact Mo433111Proof.bound_of_checkBoundsPow2 5 256 i Mo433111Proof.h_bounds2 (Nat.le_of_not_lt h256) hi'
    have hnat' : Mo433111Proof.xFn i * 10000 ≤
        Mo433111Proof.pFn i * (Mo433111Proof.xFn ((i + 1) % 288) + Mo433111Proof.xFn ((i + 2) % 288)) := by
      rw [Nat.mul_comm]
      exact hnat
    have hq := Rat.natCast_le_natCast.mpr hnat'
    rw [Rat.natCast_mul, Rat.natCast_mul, Rat.natCast_add] at hq
    exact hq
  have hsum_p : (∑ i ∈ Finset.range 288, (Mo433111Proof.pFn i : ℚ)) = ((1298694 + 139420 : Nat) : ℚ) := by
    have hn_eq : 288 = 2 ^ 8 + 2 ^ 5 := rfl
    rw [hn_eq, Mo433111Proof.my_sum_range_add]
    have hs1 := Mo433111Proof.sumPow2_eq_sum_range 8 0
    have hs2 := Mo433111Proof.sumPow2_eq_sum_range 5 (2 ^ 8)
    simp only [Nat.zero_add] at hs1
    have hsum2' : Mo433111Proof.sumPow2 (2 ^ 8) 5 = 139420 := Mo433111Proof.h_sum2
    rw [Mo433111Proof.h_sum1] at hs1
    rw [hsum2'] at hs2
    rw [hs1, hs2, ← Rat.natCast_add]
  have hsum_rhs :
      (∑ i ∈ Finset.range 288, (Mo433111Proof.pFn i : ℚ) / (10000 : ℚ)) = ((1298694 + 139420 : Nat) : ℚ) / (10000 : ℚ) := by
    rw [Mo433111Proof.rat_sum_div_const, hsum_p]
  have hlt_nat : 2 * (1298694 + 139420) < 288 * 10000 := Nat.le_of_ble_eq_true Mo433111Proof.h_sum_lt
  have hlt_rat : ((1298694 + 139420 : Nat) : ℚ) / (10000 : ℚ) < (288 : ℚ) / 2 := by
    have hM_pos : (0 : ℚ) < (10000 : ℚ) := Rat.natCast_lt_natCast.mpr (Nat.zero_lt_succ (10000 - 1))
    have h2_pos : (0 : ℚ) < (2 : ℚ) := Rat.natCast_lt_natCast.mpr (Nat.zero_lt_succ 1)
    apply Mo433111Proof.rat_div_lt_div hM_pos h2_pos
    have hlt_nat' : (1298694 + 139420) * 2 < 288 * 10000 := by
      rw [Nat.mul_comm]
      exact hlt_nat
    have hlt_q := Rat.natCast_lt_natCast.mpr hlt_nat'
    rw [Rat.natCast_mul, Rat.natCast_mul] at hlt_q
    exact hlt_q
  have h_contra : ((288 : Nat) : ℚ) / 2 < ((288 : Nat) : ℚ) / 2 := by
    have h1 := Rat.le_trans hle' hsum_le
    rw [hsum_rhs] at h1
    exact Mo433111Proof.rat_lt_of_le_of_lt h1 hlt_rat
  exact Rat.lt_irrefl h_contra
