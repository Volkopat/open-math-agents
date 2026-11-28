import OMAStatements.S_oeis_a250760
import Mathlib

-- Proof of the conjectures in OEIS A250760 (statement by @ivillar).
-- Idea: the conditions only involve 2 X 2 blocks, so the count is a walk count on the columns of the
-- array (transfer matrix). The 729 states are lumped into 27 classes with constant numbers of successors in
-- each class (checked by decide), which gives a linear system for the class counts W n c. The recurrence
-- of order 3 follows from explicit row vectors orthogonal to all W n (an invariant subspace of the
-- transposed class matrix), and the generating function and closed forms follow from the recurrence
-- and the first values.

namespace OMAA250760Helpers

open OMA.S_oeis_a250760

instance (p q r s : ℕ) : Decidable (Blk p q r s) := by
  unfold Blk; infer_instance

/-- The states of the transfer matrix: the columns of the array, encoded as numbers in base 3
(digit j of the code is entry j). -/
abbrev R := Fin (3 ^ 6)

/-- Digit j of the code a in base 3. -/
def dig (a j : ℕ) : ℕ := a / 3 ^ j % 3

/-- Consecutive columns u, v: all the 2 X 2 blocks they form satisfy the condition. -/
abbrev BlockOK (u v : Fin 6 → Fin 3) : Prop :=
  ∀ i : Fin 5, Blk (u i.castSucc) (v i.castSucc) (u i.succ) (v i.succ)

/-- The truth table of `Blk` on entries below 3: bit ((p * 3 + q) * 3 + r) * 3 + s. -/
def blkTab : ℕ := 1469006537725837178850615

/-- `Blk` read off the truth table. -/
def blkB (p q r s : ℕ) : Bool := Nat.testBit blkTab (((p * 3 + q) * 3 + r) * 3 + s)

theorem blk_iff : ∀ p q r s : Fin 3, blkB p q r s = true ↔ Blk p q r s := by decide +kernel

/-- The same condition on codes. -/
def compatB (r s : ℕ) : Bool :=
  blkB (dig r 0) (dig s 0) (dig r 1) (dig s 1) &&
    (blkB (dig r 1) (dig s 1) (dig r 2) (dig s 2) &&
    (blkB (dig r 2) (dig s 2) (dig r 3) (dig s 3) &&
    (blkB (dig r 3) (dig s 3) (dig r 4) (dig s 4) &&
    (blkB (dig r 4) (dig s 4) (dig r 5) (dig s 5)))))

abbrev compatN (r s : ℕ) : Prop := compatB r s = true

/-- States are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Every state may start a walk. -/
abbrev init (_r : R) : Prop := True

/-- Compatibility of consecutive states. -/
abbrev compat (r s : R) : Prop := compatN r.val s.val

theorem dig_enc (u : Fin 6 → Fin 3) (i : Fin 6) : dig ((finFunctionFinEquiv (m := 3) (n := 6)) u).val i.val = (u i).val :=
  congrArg Fin.val (congrFun (Equiv.symm_apply_apply (finFunctionFinEquiv (m := 3) (n := 6)) u) i)

theorem dig_e0 (u : Fin 6 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 6)) u).val 0 = (u 0).val := dig_enc u 0

theorem dig_e1 (u : Fin 6 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 6)) u).val 1 = (u 1).val := dig_enc u 1

theorem dig_e2 (u : Fin 6 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 6)) u).val 2 = (u 2).val := dig_enc u 2

theorem dig_e3 (u : Fin 6 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 6)) u).val 3 = (u 3).val := dig_enc u 3

theorem dig_e4 (u : Fin 6 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 6)) u).val 4 = (u 4).val := dig_enc u 4

theorem dig_e5 (u : Fin 6 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 6)) u).val 5 = (u 5).val := dig_enc u 5


theorem blockOK_iff (u v : Fin 6 → Fin 3) :
    BlockOK u v ↔
      (Blk (u 0) (v 0) (u 1) (v 1) ∧
      (Blk (u 1) (v 1) (u 2) (v 2) ∧
      (Blk (u 2) (v 2) (u 3) (v 3) ∧
      (Blk (u 3) (v 3) (u 4) (v 4) ∧
      (Blk (u 4) (v 4) (u 5) (v 5)))))) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ j
    fin_cases j <;>
      first
        | exact h0
        | exact h1
        | exact h2
        | exact h3
        | exact h4

theorem compat_enc (u v : Fin 6 → Fin 3) :
    compat ((finFunctionFinEquiv (m := 3) (n := 6)) u) ((finFunctionFinEquiv (m := 3) (n := 6)) v) ↔ BlockOK u v := by
  rw [blockOK_iff]
  simp only [compat, compatN, compatB, Bool.and_eq_true, dig_e0, dig_e1, dig_e2, dig_e3, dig_e4, dig_e5, blk_iff]

/-- Arrays as sequences of encoded columns. -/
def enc (n : ℕ) : (Fin 6 → Fin (n + 1) → Fin 3) ≃ (Fin (n + 1) → R) where
  toFun := fun x j => (finFunctionFinEquiv (m := 3) (n := 6)) (fun i => x i j)
  invFun := fun y i j => (finFunctionFinEquiv (m := 3) (n := 6)).symm (y j) i
  left_inv := fun x => by funext i j; exact congrFun (Equiv.symm_apply_apply _ _) i
  right_inv := fun y => by funext j; exact Equiv.apply_symm_apply _ _

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

def F (n : ℕ) (s : R) : ℕ := ∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0

theorem F_zero (s : R) : F 0 s = if ok s then 1 else 0 := by
  unfold F
  rw [← (Equiv.funUnique (Fin 1) R).symm.sum_comp]
  have h : ∀ r : R, (if Walk ((Equiv.funUnique (Fin 1) R).symm r) ∧
      (Equiv.funUnique (Fin 1) R).symm r 0 = s then 1 else 0) = if r = s then (if ok s then 1 else 0) else 0 := by
    intro r
    simp only [Equiv.funUnique_symm_apply, Walk, IsEmpty.forall_iff, and_true]
    by_cases hr : r = s
    · subst hr; simp
    · simp [hr]
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq']
  simp

theorem F_succ (n : ℕ) (s : R) :
    F (n + 1) s = ∑ t : R, if ok s ∧ compat s t then F n t else 0 := by
  have lhs : F (n + 1) s = ∑ y : Fin (n + 1) → R, if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0 := by
    unfold F
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => R)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have h : ∀ r : R, (if Walk ((Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y)) ∧
        (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) 0 = s then 1 else 0) =
        if r = s then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
      intro r
      rw [show (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) = (Fin.cons r y : Fin (n + 2) → R)
        from rfl]
      simp only [walk_cons, Fin.cons_zero]
      by_cases hr : r = s
      · subst hr
        rw [if_pos rfl]
        exact if_congr ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩ rfl rfl
      · rw [if_neg hr, if_neg (show ¬((ok r ∧ compat r (y 0) ∧ Walk y) ∧ r = s) from fun h => hr h.2)]
    rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [lhs]
  unfold F
  have h2 : ∀ t : R, (if ok s ∧ compat s t then
      ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = t then 1 else 0) else 0) =
      ∑ y : Fin (n + 1) → R, if y 0 = t then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
    intro t
    split_ifs with ht
    · apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y 0 = t
      · subst hy
        rw [if_pos (rfl : y 0 = y 0)]
        exact if_congr ⟨fun h => ⟨ht.1, ht.2, h.1⟩, fun h => ⟨h.2.2, rfl⟩⟩ rfl rfl
      · rw [if_neg hy, if_neg (show ¬(Walk y ∧ y 0 = t) from fun h => hy h.2)]
    · symm
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y 0 = t
      · subst hy; rw [if_pos rfl, if_neg (fun h => ht ⟨h.1, h.2.1⟩)]
      · rw [if_neg hy]
  rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- The classes of the states, one byte per state. -/
def clsTab : ℕ := 31726672644278044934414012109246894224898406989145400205220479616918357910569514857302431326567929765360996454673800809196691550555455542073526381467154670717299362776852922326666213120638742098194710406292270734133787337341900738120139230201456757538594905048971488523984228888253912909904321567181241887201489172011112988333793557524923616515742255983383163557146135406739568656382295762020574458462317900933402390295281965002855295356195874230757318537972292368660878033630127072795359639143800931537349109964201115488753276766150019043669808420690603744721828780867217296395328111574336954882555639283146500044283060002491323265086570617419234388302239709843072173794505065477775992188755791632427477775380380261579983922843990383064989268433225123330290241009027920150628504798456302311401213220029204482091641188859578408533955867998502834358970129857891145857343799412700918466107408977665790016383182887057728107434608352384494738547342978573279256615844386274525005711171104302128768738823652945964259874326526401312693561349988225278094229804474333034989795782850520941148867150422856104240532985829399821683972486785975327339076566890584794523838656282634115966549370175892902710274760042655373791159314993211939295073878769613580689571894963231741246475764894948865177868851635499033459936750247450768201252228636387932815366403959967564965195338638611742753594884392095532952191511803882565099625341770388084791816248490188159989841106090700416184316507733586417229524723260381200094376889540240976668155708181570692884734444520393581558627477637918692040437355339344054060988331400132150388930591169945551781674475771856623565321824745240399137791607040703167828203544643094278647119045645308018073319102659884976400065066606407636465227008

/-- The class of a code (states of one class have the same numbers of successors in each class). -/
def clsF (a : ℕ) : Fin 27 := ⟨(clsTab >>> (8 * a)) % 256 % 27, Nat.mod_lt _ (by norm_num)⟩

/-- The class of a state. -/
def cls (t : R) : Fin 27 := clsF t.val

/-- The codes of the states of each class. -/
def mem : Fin 27 → List ℕ :=
  ![[0, 2], [243, 245, 246, 248, 252, 254, 255, 257, 270, 272, 273, 275, 279, 281, 282, 284, 324, 326, 327, 329, 333, 335, 336, 338, 351, 353, 354, 356, 360, 362, 363, 365], [486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728], [81, 83, 84, 86, 90, 92, 93, 95, 108, 110, 111, 113, 117, 119, 120, 122], [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242], [405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485], [27, 29, 30, 32, 36, 38, 39, 41], [54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80], [297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404], [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161], [9, 11, 12, 14], [18, 19, 20, 21, 22, 23, 24, 25, 26], [261, 262, 263, 264, 265, 266, 267, 268, 269, 288, 289, 290, 291, 292, 293, 294, 295, 296, 342, 343, 344, 345, 346, 347, 348, 349, 350, 369, 370, 371, 372, 373, 374, 375, 376, 377], [99, 100, 101, 102, 103, 104, 105, 106, 107, 126, 127, 128, 129, 130, 131, 132, 133, 134], [45, 46, 47, 48, 49, 50, 51, 52, 53], [3, 5], [6, 7, 8], [249, 250, 251, 258, 259, 260, 276, 277, 278, 285, 286, 287, 330, 331, 332, 339, 340, 341, 357, 358, 359, 366, 367, 368], [87, 88, 89, 96, 97, 98, 114, 115, 116, 123, 124, 125], [33, 34, 35, 42, 43, 44], [15, 16, 17], [1], [244, 247, 253, 256, 271, 274, 280, 283, 325, 328, 334, 337, 352, 355, 361, 364], [82, 85, 91, 94, 109, 112, 118, 121], [28, 31, 37, 40], [10, 13], [4]]

/-- Mat c d: the number of successors of class d of a state of class c. -/
def Mat : Fin 27 → Fin 27 → ℤ :=
  ![![1, 5, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 6, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 11, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 3, 15, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 5, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 4, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 7, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 2, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 0, 0, 0, 0],
    ![0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 7, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 13, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0],
    ![0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0],
    ![0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 4, 0, 0, 0, 1]]

/-- W n c: the number of walks with n steps starting at a given state of class c. -/
def W : ℕ → Fin 27 → ℤ
  | 0 => fun _ => 1
  | n + 1 => fun c => ∑ d, Mat c d * W n d

theorem hmem_0 : ∀ c : Fin 27, 0 ≤ c.val → c.val < 1 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_1 : ∀ c : Fin 27, 1 ≤ c.val → c.val < 2 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_2 : ∀ c : Fin 27, 2 ≤ c.val → c.val < 3 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_3 : ∀ c : Fin 27, 3 ≤ c.val → c.val < 4 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_4 : ∀ c : Fin 27, 4 ≤ c.val → c.val < 5 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_5 : ∀ c : Fin 27, 5 ≤ c.val → c.val < 6 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_6 : ∀ c : Fin 27, 6 ≤ c.val → c.val < 7 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_7 : ∀ c : Fin 27, 7 ≤ c.val → c.val < 8 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_8 : ∀ c : Fin 27, 8 ≤ c.val → c.val < 9 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_9 : ∀ c : Fin 27, 9 ≤ c.val → c.val < 10 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_10 : ∀ c : Fin 27, 10 ≤ c.val → c.val < 11 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_11 : ∀ c : Fin 27, 11 ≤ c.val → c.val < 12 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_12 : ∀ c : Fin 27, 12 ≤ c.val → c.val < 13 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_13 : ∀ c : Fin 27, 13 ≤ c.val → c.val < 14 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_14 : ∀ c : Fin 27, 14 ≤ c.val → c.val < 15 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_15 : ∀ c : Fin 27, 15 ≤ c.val → c.val < 16 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_16 : ∀ c : Fin 27, 16 ≤ c.val → c.val < 17 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_17 : ∀ c : Fin 27, 17 ≤ c.val → c.val < 18 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_18 : ∀ c : Fin 27, 18 ≤ c.val → c.val < 19 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_19 : ∀ c : Fin 27, 19 ≤ c.val → c.val < 20 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_20 : ∀ c : Fin 27, 20 ≤ c.val → c.val < 21 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_21 : ∀ c : Fin 27, 21 ≤ c.val → c.val < 22 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_22 : ∀ c : Fin 27, 22 ≤ c.val → c.val < 23 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_23 : ∀ c : Fin 27, 23 ≤ c.val → c.val < 24 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_24 : ∀ c : Fin 27, 24 ≤ c.val → c.val < 25 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_25 : ∀ c : Fin 27, 25 ≤ c.val → c.val < 26 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_26 : ∀ c : Fin 27, 26 ≤ c.val → c.val < 27 →
    mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem : ∀ c : Fin 27, mem c = (List.range (3 ^ 6)).filter (fun a => clsF a = c) := fun c =>
  if h13 : c.val < 13 then
    if h6 : c.val < 6 then
      if h3 : c.val < 3 then
        if h1 : c.val < 1 then
          hmem_0 c (Nat.zero_le _) h1
        else
          if h2 : c.val < 2 then
            hmem_1 c (Nat.le_of_not_lt h1) h2
          else
            hmem_2 c (Nat.le_of_not_lt h2) h3
      else
        if h4 : c.val < 4 then
          hmem_3 c (Nat.le_of_not_lt h3) h4
        else
          if h5 : c.val < 5 then
            hmem_4 c (Nat.le_of_not_lt h4) h5
          else
            hmem_5 c (Nat.le_of_not_lt h5) h6
    else
      if h9 : c.val < 9 then
        if h7 : c.val < 7 then
          hmem_6 c (Nat.le_of_not_lt h6) h7
        else
          if h8 : c.val < 8 then
            hmem_7 c (Nat.le_of_not_lt h7) h8
          else
            hmem_8 c (Nat.le_of_not_lt h8) h9
      else
        if h11 : c.val < 11 then
          if h10 : c.val < 10 then
            hmem_9 c (Nat.le_of_not_lt h9) h10
          else
            hmem_10 c (Nat.le_of_not_lt h10) h11
        else
          if h12 : c.val < 12 then
            hmem_11 c (Nat.le_of_not_lt h11) h12
          else
            hmem_12 c (Nat.le_of_not_lt h12) h13
  else
    if h20 : c.val < 20 then
      if h16 : c.val < 16 then
        if h14 : c.val < 14 then
          hmem_13 c (Nat.le_of_not_lt h13) h14
        else
          if h15 : c.val < 15 then
            hmem_14 c (Nat.le_of_not_lt h14) h15
          else
            hmem_15 c (Nat.le_of_not_lt h15) h16
      else
        if h18 : c.val < 18 then
          if h17 : c.val < 17 then
            hmem_16 c (Nat.le_of_not_lt h16) h17
          else
            hmem_17 c (Nat.le_of_not_lt h17) h18
        else
          if h19 : c.val < 19 then
            hmem_18 c (Nat.le_of_not_lt h18) h19
          else
            hmem_19 c (Nat.le_of_not_lt h19) h20
    else
      if h23 : c.val < 23 then
        if h21 : c.val < 21 then
          hmem_20 c (Nat.le_of_not_lt h20) h21
        else
          if h22 : c.val < 22 then
            hmem_21 c (Nat.le_of_not_lt h21) h22
          else
            hmem_22 c (Nat.le_of_not_lt h22) h23
      else
        if h25 : c.val < 25 then
          if h24 : c.val < 24 then
            hmem_23 c (Nat.le_of_not_lt h23) h24
          else
            hmem_24 c (Nat.le_of_not_lt h24) h25
        else
          if h26 : c.val < 26 then
            hmem_25 c (Nat.le_of_not_lt h25) h26
          else
            hmem_26 c (Nat.le_of_not_lt h26) c.isLt

set_option maxHeartbeats 0 in
theorem cntN : ∀ s : R, ∀ c : Fin 27,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  have h_0 : ∀ a ∈ List.range' 0 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_1 : ∀ a ∈ List.range' 6 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_2 : ∀ a ∈ List.range' 12 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_3 : ∀ a ∈ List.range' 18 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_4 : ∀ a ∈ List.range' 24 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_5 : ∀ a ∈ List.range' 30 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_6 : ∀ a ∈ List.range' 36 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_7 : ∀ a ∈ List.range' 42 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_8 : ∀ a ∈ List.range' 48 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_9 : ∀ a ∈ List.range' 54 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_10 : ∀ a ∈ List.range' 60 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_11 : ∀ a ∈ List.range' 66 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_12 : ∀ a ∈ List.range' 72 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_13 : ∀ a ∈ List.range' 78 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_14 : ∀ a ∈ List.range' 84 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_15 : ∀ a ∈ List.range' 90 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_16 : ∀ a ∈ List.range' 96 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_17 : ∀ a ∈ List.range' 102 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_18 : ∀ a ∈ List.range' 108 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_19 : ∀ a ∈ List.range' 114 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_20 : ∀ a ∈ List.range' 120 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_21 : ∀ a ∈ List.range' 126 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_22 : ∀ a ∈ List.range' 132 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_23 : ∀ a ∈ List.range' 138 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_24 : ∀ a ∈ List.range' 144 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_25 : ∀ a ∈ List.range' 150 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_26 : ∀ a ∈ List.range' 156 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_27 : ∀ a ∈ List.range' 162 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_28 : ∀ a ∈ List.range' 168 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_29 : ∀ a ∈ List.range' 174 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_30 : ∀ a ∈ List.range' 180 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_31 : ∀ a ∈ List.range' 186 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_32 : ∀ a ∈ List.range' 192 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_33 : ∀ a ∈ List.range' 198 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_34 : ∀ a ∈ List.range' 204 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_35 : ∀ a ∈ List.range' 210 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_36 : ∀ a ∈ List.range' 216 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_37 : ∀ a ∈ List.range' 222 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_38 : ∀ a ∈ List.range' 228 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_39 : ∀ a ∈ List.range' 234 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_40 : ∀ a ∈ List.range' 240 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_41 : ∀ a ∈ List.range' 246 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_42 : ∀ a ∈ List.range' 252 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_43 : ∀ a ∈ List.range' 258 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_44 : ∀ a ∈ List.range' 264 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_45 : ∀ a ∈ List.range' 270 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_46 : ∀ a ∈ List.range' 276 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_47 : ∀ a ∈ List.range' 282 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_48 : ∀ a ∈ List.range' 288 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_49 : ∀ a ∈ List.range' 294 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_50 : ∀ a ∈ List.range' 300 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_51 : ∀ a ∈ List.range' 306 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_52 : ∀ a ∈ List.range' 312 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_53 : ∀ a ∈ List.range' 318 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_54 : ∀ a ∈ List.range' 324 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_55 : ∀ a ∈ List.range' 330 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_56 : ∀ a ∈ List.range' 336 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_57 : ∀ a ∈ List.range' 342 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_58 : ∀ a ∈ List.range' 348 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_59 : ∀ a ∈ List.range' 354 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_60 : ∀ a ∈ List.range' 360 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_61 : ∀ a ∈ List.range' 366 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_62 : ∀ a ∈ List.range' 372 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_63 : ∀ a ∈ List.range' 378 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_64 : ∀ a ∈ List.range' 384 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_65 : ∀ a ∈ List.range' 390 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_66 : ∀ a ∈ List.range' 396 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_67 : ∀ a ∈ List.range' 402 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_68 : ∀ a ∈ List.range' 408 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_69 : ∀ a ∈ List.range' 414 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_70 : ∀ a ∈ List.range' 420 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_71 : ∀ a ∈ List.range' 426 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_72 : ∀ a ∈ List.range' 432 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_73 : ∀ a ∈ List.range' 438 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_74 : ∀ a ∈ List.range' 444 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_75 : ∀ a ∈ List.range' 450 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_76 : ∀ a ∈ List.range' 456 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_77 : ∀ a ∈ List.range' 462 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_78 : ∀ a ∈ List.range' 468 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_79 : ∀ a ∈ List.range' 474 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_80 : ∀ a ∈ List.range' 480 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_81 : ∀ a ∈ List.range' 486 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_82 : ∀ a ∈ List.range' 492 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_83 : ∀ a ∈ List.range' 498 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_84 : ∀ a ∈ List.range' 504 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_85 : ∀ a ∈ List.range' 510 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_86 : ∀ a ∈ List.range' 516 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_87 : ∀ a ∈ List.range' 522 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_88 : ∀ a ∈ List.range' 528 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_89 : ∀ a ∈ List.range' 534 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_90 : ∀ a ∈ List.range' 540 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_91 : ∀ a ∈ List.range' 546 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_92 : ∀ a ∈ List.range' 552 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_93 : ∀ a ∈ List.range' 558 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_94 : ∀ a ∈ List.range' 564 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_95 : ∀ a ∈ List.range' 570 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_96 : ∀ a ∈ List.range' 576 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_97 : ∀ a ∈ List.range' 582 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_98 : ∀ a ∈ List.range' 588 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_99 : ∀ a ∈ List.range' 594 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_100 : ∀ a ∈ List.range' 600 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_101 : ∀ a ∈ List.range' 606 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_102 : ∀ a ∈ List.range' 612 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_103 : ∀ a ∈ List.range' 618 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_104 : ∀ a ∈ List.range' 624 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_105 : ∀ a ∈ List.range' 630 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_106 : ∀ a ∈ List.range' 636 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_107 : ∀ a ∈ List.range' 642 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_108 : ∀ a ∈ List.range' 648 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_109 : ∀ a ∈ List.range' 654 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_110 : ∀ a ∈ List.range' 660 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_111 : ∀ a ∈ List.range' 666 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_112 : ∀ a ∈ List.range' 672 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_113 : ∀ a ∈ List.range' 678 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_114 : ∀ a ∈ List.range' 684 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_115 : ∀ a ∈ List.range' 690 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_116 : ∀ a ∈ List.range' 696 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_117 : ∀ a ∈ List.range' 702 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_118 : ∀ a ∈ List.range' 708 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_119 : ∀ a ∈ List.range' 714 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_120 : ∀ a ∈ List.range' 720 6, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_121 : ∀ a ∈ List.range' 726 3, ∀ c : Fin 27,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  exact fun s c =>
    if h61 : s.val < 366 then
      if h30 : s.val < 180 then
        if h15 : s.val < 90 then
          if h7 : s.val < 42 then
            if h3 : s.val < 18 then
              if h1 : s.val < 6 then
                h_0 s.val (List.mem_range'_1.mpr ⟨(Nat.zero_le _), h1⟩) c
              else
                if h2 : s.val < 12 then
                  h_1 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h1), h2⟩) c
                else
                  h_2 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h2), h3⟩) c
            else
              if h5 : s.val < 30 then
                if h4 : s.val < 24 then
                  h_3 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h3), h4⟩) c
                else
                  h_4 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h4), h5⟩) c
              else
                if h6 : s.val < 36 then
                  h_5 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h5), h6⟩) c
                else
                  h_6 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h6), h7⟩) c
          else
            if h11 : s.val < 66 then
              if h9 : s.val < 54 then
                if h8 : s.val < 48 then
                  h_7 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h7), h8⟩) c
                else
                  h_8 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h8), h9⟩) c
              else
                if h10 : s.val < 60 then
                  h_9 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h9), h10⟩) c
                else
                  h_10 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h10), h11⟩) c
            else
              if h13 : s.val < 78 then
                if h12 : s.val < 72 then
                  h_11 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h11), h12⟩) c
                else
                  h_12 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h12), h13⟩) c
              else
                if h14 : s.val < 84 then
                  h_13 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h13), h14⟩) c
                else
                  h_14 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h14), h15⟩) c
        else
          if h22 : s.val < 132 then
            if h18 : s.val < 108 then
              if h16 : s.val < 96 then
                h_15 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h15), h16⟩) c
              else
                if h17 : s.val < 102 then
                  h_16 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h16), h17⟩) c
                else
                  h_17 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h17), h18⟩) c
            else
              if h20 : s.val < 120 then
                if h19 : s.val < 114 then
                  h_18 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h18), h19⟩) c
                else
                  h_19 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h19), h20⟩) c
              else
                if h21 : s.val < 126 then
                  h_20 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h20), h21⟩) c
                else
                  h_21 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h21), h22⟩) c
          else
            if h26 : s.val < 156 then
              if h24 : s.val < 144 then
                if h23 : s.val < 138 then
                  h_22 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h22), h23⟩) c
                else
                  h_23 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h23), h24⟩) c
              else
                if h25 : s.val < 150 then
                  h_24 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h24), h25⟩) c
                else
                  h_25 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h25), h26⟩) c
            else
              if h28 : s.val < 168 then
                if h27 : s.val < 162 then
                  h_26 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h26), h27⟩) c
                else
                  h_27 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h27), h28⟩) c
              else
                if h29 : s.val < 174 then
                  h_28 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h28), h29⟩) c
                else
                  h_29 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h29), h30⟩) c
      else
        if h45 : s.val < 270 then
          if h37 : s.val < 222 then
            if h33 : s.val < 198 then
              if h31 : s.val < 186 then
                h_30 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h30), h31⟩) c
              else
                if h32 : s.val < 192 then
                  h_31 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h31), h32⟩) c
                else
                  h_32 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h32), h33⟩) c
            else
              if h35 : s.val < 210 then
                if h34 : s.val < 204 then
                  h_33 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h33), h34⟩) c
                else
                  h_34 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h34), h35⟩) c
              else
                if h36 : s.val < 216 then
                  h_35 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h35), h36⟩) c
                else
                  h_36 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h36), h37⟩) c
          else
            if h41 : s.val < 246 then
              if h39 : s.val < 234 then
                if h38 : s.val < 228 then
                  h_37 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h37), h38⟩) c
                else
                  h_38 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h38), h39⟩) c
              else
                if h40 : s.val < 240 then
                  h_39 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h39), h40⟩) c
                else
                  h_40 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h40), h41⟩) c
            else
              if h43 : s.val < 258 then
                if h42 : s.val < 252 then
                  h_41 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h41), h42⟩) c
                else
                  h_42 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h42), h43⟩) c
              else
                if h44 : s.val < 264 then
                  h_43 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h43), h44⟩) c
                else
                  h_44 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h44), h45⟩) c
        else
          if h53 : s.val < 318 then
            if h49 : s.val < 294 then
              if h47 : s.val < 282 then
                if h46 : s.val < 276 then
                  h_45 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h45), h46⟩) c
                else
                  h_46 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h46), h47⟩) c
              else
                if h48 : s.val < 288 then
                  h_47 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h47), h48⟩) c
                else
                  h_48 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h48), h49⟩) c
            else
              if h51 : s.val < 306 then
                if h50 : s.val < 300 then
                  h_49 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h49), h50⟩) c
                else
                  h_50 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h50), h51⟩) c
              else
                if h52 : s.val < 312 then
                  h_51 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h51), h52⟩) c
                else
                  h_52 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h52), h53⟩) c
          else
            if h57 : s.val < 342 then
              if h55 : s.val < 330 then
                if h54 : s.val < 324 then
                  h_53 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h53), h54⟩) c
                else
                  h_54 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h54), h55⟩) c
              else
                if h56 : s.val < 336 then
                  h_55 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h55), h56⟩) c
                else
                  h_56 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h56), h57⟩) c
            else
              if h59 : s.val < 354 then
                if h58 : s.val < 348 then
                  h_57 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h57), h58⟩) c
                else
                  h_58 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h58), h59⟩) c
              else
                if h60 : s.val < 360 then
                  h_59 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h59), h60⟩) c
                else
                  h_60 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h60), h61⟩) c
    else
      if h91 : s.val < 546 then
        if h76 : s.val < 456 then
          if h68 : s.val < 408 then
            if h64 : s.val < 384 then
              if h62 : s.val < 372 then
                h_61 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h61), h62⟩) c
              else
                if h63 : s.val < 378 then
                  h_62 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h62), h63⟩) c
                else
                  h_63 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h63), h64⟩) c
            else
              if h66 : s.val < 396 then
                if h65 : s.val < 390 then
                  h_64 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h64), h65⟩) c
                else
                  h_65 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h65), h66⟩) c
              else
                if h67 : s.val < 402 then
                  h_66 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h66), h67⟩) c
                else
                  h_67 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h67), h68⟩) c
          else
            if h72 : s.val < 432 then
              if h70 : s.val < 420 then
                if h69 : s.val < 414 then
                  h_68 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h68), h69⟩) c
                else
                  h_69 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h69), h70⟩) c
              else
                if h71 : s.val < 426 then
                  h_70 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h70), h71⟩) c
                else
                  h_71 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h71), h72⟩) c
            else
              if h74 : s.val < 444 then
                if h73 : s.val < 438 then
                  h_72 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h72), h73⟩) c
                else
                  h_73 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h73), h74⟩) c
              else
                if h75 : s.val < 450 then
                  h_74 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h74), h75⟩) c
                else
                  h_75 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h75), h76⟩) c
        else
          if h83 : s.val < 498 then
            if h79 : s.val < 474 then
              if h77 : s.val < 462 then
                h_76 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h76), h77⟩) c
              else
                if h78 : s.val < 468 then
                  h_77 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h77), h78⟩) c
                else
                  h_78 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h78), h79⟩) c
            else
              if h81 : s.val < 486 then
                if h80 : s.val < 480 then
                  h_79 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h79), h80⟩) c
                else
                  h_80 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h80), h81⟩) c
              else
                if h82 : s.val < 492 then
                  h_81 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h81), h82⟩) c
                else
                  h_82 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h82), h83⟩) c
          else
            if h87 : s.val < 522 then
              if h85 : s.val < 510 then
                if h84 : s.val < 504 then
                  h_83 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h83), h84⟩) c
                else
                  h_84 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h84), h85⟩) c
              else
                if h86 : s.val < 516 then
                  h_85 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h85), h86⟩) c
                else
                  h_86 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h86), h87⟩) c
            else
              if h89 : s.val < 534 then
                if h88 : s.val < 528 then
                  h_87 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h87), h88⟩) c
                else
                  h_88 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h88), h89⟩) c
              else
                if h90 : s.val < 540 then
                  h_89 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h89), h90⟩) c
                else
                  h_90 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h90), h91⟩) c
      else
        if h106 : s.val < 636 then
          if h98 : s.val < 588 then
            if h94 : s.val < 564 then
              if h92 : s.val < 552 then
                h_91 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h91), h92⟩) c
              else
                if h93 : s.val < 558 then
                  h_92 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h92), h93⟩) c
                else
                  h_93 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h93), h94⟩) c
            else
              if h96 : s.val < 576 then
                if h95 : s.val < 570 then
                  h_94 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h94), h95⟩) c
                else
                  h_95 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h95), h96⟩) c
              else
                if h97 : s.val < 582 then
                  h_96 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h96), h97⟩) c
                else
                  h_97 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h97), h98⟩) c
          else
            if h102 : s.val < 612 then
              if h100 : s.val < 600 then
                if h99 : s.val < 594 then
                  h_98 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h98), h99⟩) c
                else
                  h_99 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h99), h100⟩) c
              else
                if h101 : s.val < 606 then
                  h_100 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h100), h101⟩) c
                else
                  h_101 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h101), h102⟩) c
            else
              if h104 : s.val < 624 then
                if h103 : s.val < 618 then
                  h_102 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h102), h103⟩) c
                else
                  h_103 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h103), h104⟩) c
              else
                if h105 : s.val < 630 then
                  h_104 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h104), h105⟩) c
                else
                  h_105 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h105), h106⟩) c
        else
          if h114 : s.val < 684 then
            if h110 : s.val < 660 then
              if h108 : s.val < 648 then
                if h107 : s.val < 642 then
                  h_106 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h106), h107⟩) c
                else
                  h_107 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h107), h108⟩) c
              else
                if h109 : s.val < 654 then
                  h_108 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h108), h109⟩) c
                else
                  h_109 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h109), h110⟩) c
            else
              if h112 : s.val < 672 then
                if h111 : s.val < 666 then
                  h_110 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h110), h111⟩) c
                else
                  h_111 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h111), h112⟩) c
              else
                if h113 : s.val < 678 then
                  h_112 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h112), h113⟩) c
                else
                  h_113 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h113), h114⟩) c
          else
            if h118 : s.val < 708 then
              if h116 : s.val < 696 then
                if h115 : s.val < 690 then
                  h_114 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h114), h115⟩) c
                else
                  h_115 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h115), h116⟩) c
              else
                if h117 : s.val < 702 then
                  h_116 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h116), h117⟩) c
                else
                  h_117 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h117), h118⟩) c
            else
              if h120 : s.val < 720 then
                if h119 : s.val < 714 then
                  h_118 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h118), h119⟩) c
                else
                  h_119 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h119), h120⟩) c
              else
                if h121 : s.val < 726 then
                  h_120 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h120), h121⟩) c
                else
                  h_121 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h121), s.isLt⟩) c

/-- U i: the row vector (class sizes) * Mat^i. -/
def U : Fin 5 → Fin 27 → ℤ :=
  ![![2, 32, 243, 16, 81, 81, 8, 27, 54, 27, 4, 9, 36, 18, 9, 2, 3, 24, 12, 6, 3, 1, 16, 8, 4, 2, 1],
    ![2, 96, 1969, 16, 81, 389, 8, 27, 208, 27, 4, 9, 122, 18, 9, 2, 3, 76, 12, 6, 3, 1, 49, 8, 4, 2, 1],
    ![2, 160, 5392, 16, 81, 697, 8, 27, 362, 27, 4, 9, 208, 18, 9, 2, 3, 128, 12, 6, 3, 1, 82, 8, 4, 2, 1],
    ![2, 224, 10512, 16, 81, 1005, 8, 27, 516, 27, 4, 9, 294, 18, 9, 2, 3, 180, 12, 6, 3, 1, 115, 8, 4, 2, 1],
    ![2, 288, 17329, 16, 81, 1313, 8, 27, 670, 27, 4, 9, 380, 18, 9, 2, 3, 232, 12, 6, 3, 1, 148, 8, 4, 2, 1]]

theorem totN : ∀ c : Fin 27, ((mem c).length : ℤ) = U 0 c := by decide +kernel

theorem card_cls (c : Fin 27) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun t : R => cls t = c ∧ P t.val)).card = ((mem c).filter (fun a => P a)).length := by
  have key : (Finset.univ.filter (fun t : R => cls t = c ∧ P t.val)).map Fin.valEmbedding =
      ((mem c).filter (fun a => P a)).toFinset := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    rw [hmem c]
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨t.isLt, h1⟩, h2⟩
    · rintro ⟨⟨ha, hc⟩, h2⟩
      exact ⟨⟨a, ha⟩, ⟨hc, h2⟩, rfl⟩
  have hnd : (mem c).Nodup := by
    rw [hmem c]
    exact List.Nodup.filter _ (by first | exact List.nodup_range | exact List.nodup_range _)
  rw [← Finset.card_map Fin.valEmbedding, key, List.toFinset_card_of_nodup (hnd.filter _)]

theorem cnt : ∀ s : R, ∀ c : Fin 27,
    ((Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t))).card : ℤ) = Mat (cls s) c := by
  intro s c
  have h2 : Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t)) =
      Finset.univ.filter (fun t : R => cls t = c ∧ compatN s.val t.val) :=
    Finset.filter_congr (fun t _ => ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2⟩⟩)
  rw [h2, card_cls c (fun a => compatN s.val a)]
  have h3 : (mem c).filter (fun a => decide (compatN s.val a)) = (mem c).filter (fun a => compatB s.val a) :=
    List.filter_congr (fun a _ => by simp only [compatN, Bool.decide_eq_true])
  first
    | (rw [h3]; exact cntN s c)
    | (simpa [compatN] using cntN s c)

theorem tot : ∀ c : Fin 27,
    ((Finset.univ.filter (fun t : R => cls t = c ∧ init t)).card : ℤ) = U 0 c := by
  intro c
  have h2 : Finset.univ.filter (fun t : R => cls t = c ∧ init t) =
      Finset.univ.filter (fun t : R => cls t = c ∧ (fun _ : ℕ => True) t.val) :=
    Finset.filter_congr (fun t _ => Iff.rfl)
  rw [h2, card_cls c (fun _ : ℕ => True)]
  simpa using totN c

theorem hU0 : ∀ d : Fin 27, ∑ c, U 0 c * Mat c d = U 1 d := by decide +kernel

theorem hU1 : ∀ d : Fin 27, ∑ c, U 1 c * Mat c d = U 2 d := by decide +kernel

theorem hU2 : ∀ d : Fin 27, ∑ c, U 2 c * Mat c d = U 3 d := by decide +kernel

theorem hU3 : ∀ d : Fin 27, ∑ c, U 3 c * Mat c d = U 4 d := by decide +kernel

theorem hU : ∀ (i : Fin 4) (d : Fin 27), ∑ c, U i.castSucc c * Mat c d = U i.succ d := by
  intro i d
  fin_cases i
  · exact hU0 d
  · exact hU1 d
  · exact hU2 d
  · exact hU3 d

/-- Coefficients of the recurrence. -/
def L : Fin 5 → ℤ := ![-1, 3, -3, 1, 0]

/-- Row vectors orthogonal to all the vectors W n. -/
def Rm : Fin 1 → Fin 27 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def Am : Fin 1 → Fin 1 → ℤ :=
  ![![0]]

theorem hRA : ∀ (l : Fin 1) (d : Fin 27), ∑ c, Rm l c * Mat c d = ∑ l', Am l l' * Rm l' d := by
  decide +kernel

theorem hR0 : ∀ l : Fin 1, ∑ c, Rm l c = 0 := by decide +kernel

theorem hL : ∀ c : Fin 27, ∑ i, L i * U i c = Rm 0 c := by decide +kernel

/-- The first values. -/
def vals : Fin 5 → ℤ := ![729, 3152, 7272, 13089, 20603]

theorem hV : ∀ i : Fin 5, ∑ c, U i c = vals i := by decide +kernel

theorem sum_cls (g : Fin 27 → ℤ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (cls t) else 0) =
      ∑ c : Fin 27, ((Finset.univ.filter (fun t => cls t = c ∧ P t)).card : ℤ) * g c := by
  rw [← Finset.sum_fiberwise Finset.univ cls]
  apply Finset.sum_congr rfl
  intro c _
  have h : ∑ t ∈ Finset.univ.filter (fun t => cls t = c), (if P t then g (cls t) else 0) =
      ∑ t ∈ Finset.univ.filter (fun t => cls t = c), (if P t then g c else 0) :=
    Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2])
  rw [h, ← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul]

theorem F_eq (n : ℕ) : ∀ s : R, (F n s : ℤ) = W n (cls s) := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    simp [W, ok]
  | succ n ih =>
    intro s
    rw [F_succ]
    push_cast
    simp only [ih]
    rw [sum_cls (W n) (fun t => ok s ∧ compat s t)]
    simp only [cnt]
    rfl

theorem swap_sum (f : Fin 27 → ℤ) (n : ℕ) :
    ∑ c, f c * W (n + 1) c = ∑ d, (∑ c, f c * Mat c d) * W n d := by
  have h : ∀ c, f c * W (n + 1) c = ∑ d, f c * Mat c d * W n d := by
    intro c
    show f c * ∑ d, Mat c d * W n d = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  simp only [h, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem W_inv : ∀ (n : ℕ) (l : Fin 1), ∑ c, Rm l c * W n c = 0 := by
  intro n
  induction n with
  | zero =>
    intro l
    simpa [W] using hR0 l
  | succ n ih =>
    intro l
    rw [swap_sum]
    simp only [hRA, Finset.sum_mul]
    rw [Finset.sum_comm]
    have h : ∀ l', ∑ d, Am l l' * Rm l' d * W n d = Am l l' * ∑ d, Rm l' d * W n d := by
      intro l'
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    simp only [h, ih, mul_zero, Finset.sum_const_zero]

theorem W_shift : ∀ (i : Fin 5) (n : ℕ), ∑ c, U 0 c * W (n + i) c = ∑ c, U i c * W n c := by
  intro i
  induction i using Fin.induction with
  | zero => intro n; simp
  | succ i ih =>
    intro n
    have h1 : n + ((i.succ : Fin 5) : ℕ) = (n + 1) + ((i.castSucc : Fin 5) : ℕ) := by
      simp only [Fin.val_succ, Fin.val_castSucc]; omega
    rw [h1, ih (n + 1), swap_sum]
    simp only [hU]

theorem a_eq (n : ℕ) : (a n : ℤ) = ∑ c, U 0 c * W n c := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquiv (enc n)
      (p := fun x : Fin 6 → Fin (n + 1) → Fin 3 => ∀ i : Fin 5, ∀ j : Fin n,
        Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ))
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, fun j => (compat_enc _ _).mpr (fun i => h i j)⟩,
        fun h i j => (compat_enc _ _).mp (h.2 j) i⟩)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, if init s then F n s else 0 := by
    unfold F
    simp only [init, if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) = if y 0 = s then (if Walk y then 1 else 0) else 0 := by
      intro s
      by_cases h : y 0 = s
      · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
      · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
    rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [h1]
  push_cast
  simp only [F_eq]
  rw [sum_cls (W n) init]
  simp only [tot]

theorem a_shift (i : Fin 5) (n : ℕ) : (a (n + i) : ℤ) = ∑ c, U i c * W n c := by
  rw [a_eq, W_shift]

theorem a_rec (n : ℕ) : ∑ i : Fin 5, L i * (a (n + i) : ℤ) = 0 := by
  simp only [a_shift, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ c, ∑ i, L i * (U i c * W n c) = Rm 0 c * W n c := by
    intro c
    rw [← hL c, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [h]
  exact W_inv n 0

theorem a_val (i : Fin 5) : (a i : ℤ) = vals i := by
  have h := a_shift i 0
  rw [Nat.zero_add] at h
  rw [h, ← hV i]
  apply Finset.sum_congr rfl
  intro c _
  simp [W]

theorem rec0 (n : ℕ) : (a (n + 3) : ℤ) = 3 * (a (n + 2) : ℤ) - 3 * (a (n + 1) : ℤ) + (a (n) : ℤ) := by
  have h := a_rec n
  simp [Fin.sum_univ_succ, L] at h
  linarith

theorem v0 : a 0 = 729 := by
  have h := a_val 0
  simp [vals] at h
  exact_mod_cast h

theorem v1 : a 1 = 3152 := by
  have h := a_val 1
  simp [vals] at h
  exact_mod_cast h

theorem v2 : a 2 = 7272 := by
  have h := a_val 2
  simp [vals] at h
  exact_mod_cast h

theorem v3 : a 3 = 13089 := by
  have h := a_val 3
  simp [vals] at h
  exact_mod_cast h

theorem v4 : a 4 = 20603 := by
  have h := a_val 4
  simp [vals] at h
  exact_mod_cast h

theorem conj1 : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 1697 / 2 * (n : ℚ) ^ 2 + 3149 / 2 * (n : ℚ) + 729 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hs : n < 4
    · interval_cases n <;> norm_num [v1, v2, v3]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have g0 := ih (k + 1) (by omega) (by omega)
      have g1 := ih (k + 2) (by omega) (by omega)
      have g2 := ih (k + 3) (by omega) (by omega)
      have hr : (a (k + 4) : ℚ) = 3 * (a (k + 3) : ℚ) - 3 * (a (k + 2) : ℚ) + (a (k + 1) : ℚ) := by exact_mod_cast rec0 (k + 1)
      rw [hr, g2, g1, g0]
      push_cast
      ring

theorem conj2 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * ((1 - PowerSeries.X) ^ 3) =
      F' - PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.X ^ 3 * F' := by
    simp only [map_ofNat]
    ring
  have e2 : (PowerSeries.X * (3152 - 2184 * PowerSeries.X + 729 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
      PowerSeries.C (3152 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (2184 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (729 : ℚ) * PowerSeries.X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 3
  · interval_cases n <;> norm_num [v0, v1, v2, v3]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have h1 : (a (j + 4) : ℚ) = 3 * (a (j + 3) : ℚ) - 3 * (a (j + 2) : ℚ) + (a (j + 1) : ℚ) := by exact_mod_cast rec0 (j + 1)
    simp
    linear_combination h1

theorem conj3 : ∀ n : ℕ, 3 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega]
  have h1 : (a (k + 4) : ℤ) = 3 * (a (k + 3) : ℤ) - 3 * (a (k + 2) : ℤ) + (a (k + 1) : ℤ) := rec0 (k + 1)
  linear_combination h1

end OMAA250760Helpers

open OMA.S_oeis_a250760 OMAA250760Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250760.main :=
  ⟨conj1, conj2, conj3⟩
