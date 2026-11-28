import OMAReductions.R_Green97_green_97_variants_simkin_R2
import Mathlib

namespace SimkinUpper

open Finset

private def yInt (k : Fin 102) : ℤ :=
  match k.val with
  | 0 => -61
  | 1 => -39
  | 2 => -19
  | 3 => -2
  | 4 => 12
  | 5 => 23
  | 6 => 31
  | 7 => 36
  | 8 => 38
  | 9 => 36
  | 10 => 31
  | 11 => 23
  | 12 => 12
  | 13 => -2
  | 14 => -19
  | 15 => -39
  | 16 => -61
  | 17 => -61
  | 18 => -39
  | 19 => -19
  | 20 => -2
  | 21 => 12
  | 22 => 23
  | 23 => 31
  | 24 => 36
  | 25 => 38
  | 26 => 36
  | 27 => 31
  | 28 => 23
  | 29 => 12
  | 30 => -2
  | 31 => -19
  | 32 => -39
  | 33 => -61
  | 34 => -185
  | 35 => -189
  | 36 => -195
  | 37 => -203
  | 38 => -213
  | 39 => -225
  | 40 => -239
  | 41 => -254
  | 42 => -269
  | 43 => -285
  | 44 => -300
  | 45 => -313
  | 46 => -325
  | 47 => -336
  | 48 => -344
  | 49 => -351
  | 50 => -355
  | 51 => -355
  | 52 => -351
  | 53 => -344
  | 54 => -336
  | 55 => -325
  | 56 => -313
  | 57 => -300
  | 58 => -285
  | 59 => -269
  | 60 => -254
  | 61 => -239
  | 62 => -225
  | 63 => -213
  | 64 => -203
  | 65 => -195
  | 66 => -189
  | 67 => -185
  | 68 => -185
  | 69 => -189
  | 70 => -195
  | 71 => -203
  | 72 => -213
  | 73 => -225
  | 74 => -239
  | 75 => -254
  | 76 => -269
  | 77 => -285
  | 78 => -300
  | 79 => -313
  | 80 => -325
  | 81 => -336
  | 82 => -344
  | 83 => -351
  | 84 => -355
  | 85 => -355
  | 86 => -351
  | 87 => -344
  | 88 => -336
  | 89 => -325
  | 90 => -313
  | 91 => -300
  | 92 => -285
  | 93 => -269
  | 94 => -254
  | 95 => -239
  | 96 => -225
  | 97 => -213
  | 98 => -203
  | 99 => -195
  | 100 => -189
  | 101 => -185
  | _ => 0

private def zVal (k : Fin 81) : ℤ :=
  match k.val with
  | 0 => -766
  | 1 => -762
  | 2 => -750
  | 3 => -746
  | 4 => -744
  | 5 => -740
  | 6 => -736
  | 7 => -734
  | 8 => -733
  | 9 => -732
  | 10 => -729
  | 11 => -728
  | 12 => -727
  | 13 => -726
  | 14 => -724
  | 15 => -722
  | 16 => -721
  | 17 => -720
  | 18 => -719
  | 19 => -718
  | 20 => -717
  | 21 => -716
  | 22 => -715
  | 23 => -714
  | 24 => -713
  | 25 => -712
  | 26 => -711
  | 27 => -710
  | 28 => -709
  | 29 => -708
  | 30 => -707
  | 31 => -706
  | 32 => -705
  | 33 => -704
  | 34 => -702
  | 35 => -701
  | 36 => -700
  | 37 => -699
  | 38 => -698
  | 39 => -697
  | 40 => -696
  | 41 => -695
  | 42 => -694
  | 43 => -693
  | 44 => -692
  | 45 => -691
  | 46 => -690
  | 47 => -688
  | 48 => -687
  | 49 => -686
  | 50 => -685
  | 51 => -684
  | 52 => -682
  | 53 => -681
  | 54 => -680
  | 55 => -679
  | 56 => -677
  | 57 => -676
  | 58 => -675
  | 59 => -672
  | 60 => -671
  | 61 => -669
  | 62 => -664
  | 63 => -661
  | 64 => -455
  | 65 => -451
  | 66 => -444
  | 67 => -436
  | 68 => -425
  | 69 => -413
  | 70 => -400
  | 71 => -385
  | 72 => -369
  | 73 => -354
  | 74 => -339
  | 75 => -325
  | 76 => -313
  | 77 => -303
  | 78 => -295
  | 79 => -289
  | 80 => -285
  | _ => 0

private def ubInt (k : Fin 81) : ℤ :=
  match k.val with
  | 0 => 4714
  | 1 => 4906
  | 2 => 5531
  | 3 => 5757
  | 4 => 5873
  | 5 => 6113
  | 6 => 6363
  | 7 => 6491
  | 8 => 6556
  | 9 => 6622
  | 10 => 6824
  | 11 => 6892
  | 12 => 6962
  | 13 => 7032
  | 14 => 7174
  | 15 => 7319
  | 16 => 7392
  | 17 => 7466
  | 18 => 7541
  | 19 => 7617
  | 20 => 7694
  | 21 => 7771
  | 22 => 7849
  | 23 => 7928
  | 24 => 8008
  | 25 => 8088
  | 26 => 8169
  | 27 => 8252
  | 28 => 8335
  | 29 => 8418
  | 30 => 8503
  | 31 => 8588
  | 32 => 8675
  | 33 => 8762
  | 34 => 8939
  | 35 => 9029
  | 36 => 9119
  | 37 => 9211
  | 38 => 9304
  | 39 => 9397
  | 40 => 9492
  | 41 => 9587
  | 42 => 9683
  | 43 => 9781
  | 44 => 9879
  | 45 => 9978
  | 46 => 10078
  | 47 => 10282
  | 48 => 10385
  | 49 => 10490
  | 50 => 10595
  | 51 => 10702
  | 52 => 10918
  | 53 => 11027
  | 54 => 11138
  | 55 => 11250
  | 56 => 11478
  | 57 => 11593
  | 58 => 11709
  | 59 => 12066
  | 60 => 12187
  | 61 => 12433
  | 62 => 13071
  | 63 => 13469
  | 64 => 105673
  | 65 => 109986
  | 66 => 117960
  | 67 => 127785
  | 68 => 142643
  | 69 => 160830
  | 70 => 183157
  | 71 => 212799
  | 72 => 249721
  | 73 => 290135
  | 74 => 337088
  | 75 => 387744
  | 76 => 437179
  | 77 => 483159
  | 78 => 523398
  | 79 => 555763
  | 80 => 578445
  | _ => 0

private noncomputable def yRow (i : Fin 17) : ℝ := (yInt ⟨i.val, by omega⟩ : ℝ) / 100
private noncomputable def yCol (j : Fin 17) : ℝ := (yInt ⟨17 + j.val, by omega⟩ : ℝ) / 100
private noncomputable def yDiag (b : Bool) (s : Fin 34) : ℝ :=
  (yInt ⟨(if b then 68 else 34) + s.val, by cases b <;> simp <;> omega⟩ : ℝ) / 100

private def sPlus (i j : Fin 17) (t : Fin 4) : Fin 34 :=
  if t.val = 0 ∨ t.val = 1 then ⟨i.val + j.val, by omega⟩ else ⟨i.val + j.val + 1, by omega⟩

private def sMinus (i j : Fin 17) (t : Fin 4) : Fin 34 :=
  if t.val = 0 ∨ t.val = 3 then ⟨i.val + 16 - j.val, by omega⟩ else ⟨i.val + 17 - j.val, by omega⟩

private def cellZInt (i j : Fin 17) (t : Fin 4) : ℤ :=
  yInt ⟨i.val, by omega⟩ + yInt ⟨17 + j.val, by omega⟩ +
  yInt ⟨34 + (sPlus i j t).val, by omega⟩ + yInt ⟨68 + (sMinus i j t).val, by omega⟩ - 100

private def diagZInt (b : Bool) (s : Fin 34) : ℤ :=
  yInt ⟨(if b then 68 else 34) + s.val, by cases b <;> simp <;> omega⟩ - 100

private def cellIdx (i j : Fin 17) (t : Fin 4) : Fin 81 :=
  match (List.finRange 81).find? (fun k => decide (zVal k = cellZInt i j t)) with
  | some k => k
  | none => ⟨0, by decide⟩

private def diagIdx (b : Bool) (s : Fin 34) : Fin 81 :=
  match (List.finRange 81).find? (fun k => decide (zVal k = diagZInt b s)) with
  | some k => k
  | none => ⟨0, by decide⟩

set_option maxRecDepth 20000 in
private lemma cellIdx_spec : ∀ (i j : Fin 17) (t : Fin 4), zVal (cellIdx i j t) = cellZInt i j t := by
  decide +kernel

set_option maxRecDepth 20000 in
private lemma diagIdx_spec : ∀ (b : Bool) (s : Fin 34), zVal (diagIdx b s) = diagZInt b s := by
  decide +kernel

set_option maxRecDepth 20000 in
private lemma sum_ub_eq : (∑ i : Fin 17, ∑ j : Fin 17, ∑ t : Fin 4, ubInt (cellIdx i j t)) +
    (∑ b : Bool, ∑ s : Fin 34, ubInt (diagIdx b s)) = 30002924 := by
  decide +kernel

set_option maxRecDepth 20000 in
private lemma sum_yInt_eq : (∑ i : Fin 17, yInt ⟨i.val, by omega⟩) +
    (∑ j : Fin 17, yInt ⟨17 + j.val, by omega⟩) +
    (∑ b : Bool, ∑ s : Fin 34, yInt ⟨(if b then 68 else 34) + s.val, by cases b <;> simp <;> omega⟩) = -18324 := by
  decide +kernel

private lemma exp_neg_le_eight (q B U : ℝ) (hq : 0 ≤ q) (hB : 0 < B)
    (hsum : B ≤ ∑ m ∈ Finset.range 9, (q / 8) ^ m / (m.factorial : ℝ))
    (hU : (B ^ 8)⁻¹ ≤ U) :
    Real.exp (-q) ≤ U := by
  have hexp : B ≤ Real.exp (q / 8) := hsum.trans (Real.sum_le_exp_of_nonneg (by positivity) 9)
  have hpow : B ^ 8 ≤ Real.exp q := by
    calc B ^ 8 ≤ (Real.exp (q / 8)) ^ 8 := pow_le_pow_left₀ hB.le hexp 8
      _ = Real.exp ((8 : ℕ) * (q / 8)) := (Real.exp_nat_mul (q / 8) 8).symm
      _ = Real.exp q := by push_cast; ring_nf
  rw [Real.exp_neg]
  exact (inv_anti₀ (pow_pos hB 8) hpow).trans hU

private lemma exp_ub_0 : Real.exp ((zVal 0 : ℝ) / 100) ≤ (ubInt 0 : ℝ) / 10000000 := by
  rw [show ((zVal 0 : ℝ) / 100) = -((766 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 0 : ℝ) / 10000000) = (4714 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((766 : ℝ) / 100) ((2605173 : ℝ) / 1000000) ((4714 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_1 : Real.exp ((zVal 1 : ℝ) / 100) ≤ (ubInt 1 : ℝ) / 10000000 := by
  rw [show ((zVal 1 : ℝ) / 100) = -((762 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 1 : ℝ) / 10000000) = (4906 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((762 : ℝ) / 100) ((2592180 : ℝ) / 1000000) ((4906 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_2 : Real.exp ((zVal 2 : ℝ) / 100) ≤ (ubInt 2 : ℝ) / 10000000 := by
  rw [show ((zVal 2 : ℝ) / 100) = -((750 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 2 : ℝ) / 10000000) = (5531 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((750 : ℝ) / 100) ((2553587 : ℝ) / 1000000) ((5531 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_3 : Real.exp ((zVal 3 : ℝ) / 100) ≤ (ubInt 3 : ℝ) / 10000000 := by
  rw [show ((zVal 3 : ℝ) / 100) = -((746 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 3 : ℝ) / 10000000) = (5757 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((746 : ℝ) / 100) ((2540851 : ℝ) / 1000000) ((5757 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_4 : Real.exp ((zVal 4 : ℝ) / 100) ≤ (ubInt 4 : ℝ) / 10000000 := by
  rw [show ((zVal 4 : ℝ) / 100) = -((744 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 4 : ℝ) / 10000000) = (5873 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((744 : ℝ) / 100) ((2534507 : ℝ) / 1000000) ((5873 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_5 : Real.exp ((zVal 5 : ℝ) / 100) ≤ (ubInt 5 : ℝ) / 10000000 := by
  rw [show ((zVal 5 : ℝ) / 100) = -((740 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 5 : ℝ) / 10000000) = (6113 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((740 : ℝ) / 100) ((2521866 : ℝ) / 1000000) ((6113 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_6 : Real.exp ((zVal 6 : ℝ) / 100) ≤ (ubInt 6 : ℝ) / 10000000 := by
  rw [show ((zVal 6 : ℝ) / 100) = -((736 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 6 : ℝ) / 10000000) = (6363 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((736 : ℝ) / 100) ((2509288 : ℝ) / 1000000) ((6363 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_7 : Real.exp ((zVal 7 : ℝ) / 100) ≤ (ubInt 7 : ℝ) / 10000000 := by
  rw [show ((zVal 7 : ℝ) / 100) = -((734 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 7 : ℝ) / 10000000) = (6491 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((734 : ℝ) / 100) ((2503023 : ℝ) / 1000000) ((6491 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_8 : Real.exp ((zVal 8 : ℝ) / 100) ≤ (ubInt 8 : ℝ) / 10000000 := by
  rw [show ((zVal 8 : ℝ) / 100) = -((733 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 8 : ℝ) / 10000000) = (6556 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((733 : ℝ) / 100) ((2499896 : ℝ) / 1000000) ((6556 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_9 : Real.exp ((zVal 9 : ℝ) / 100) ≤ (ubInt 9 : ℝ) / 10000000 := by
  rw [show ((zVal 9 : ℝ) / 100) = -((732 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 9 : ℝ) / 10000000) = (6622 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((732 : ℝ) / 100) ((2496773 : ℝ) / 1000000) ((6622 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_10 : Real.exp ((zVal 10 : ℝ) / 100) ≤ (ubInt 10 : ℝ) / 10000000 := by
  rw [show ((zVal 10 : ℝ) / 100) = -((729 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 10 : ℝ) / 10000000) = (6824 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((729 : ℝ) / 100) ((2487428 : ℝ) / 1000000) ((6824 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_11 : Real.exp ((zVal 11 : ℝ) / 100) ≤ (ubInt 11 : ℝ) / 10000000 := by
  rw [show ((zVal 11 : ℝ) / 100) = -((728 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 11 : ℝ) / 10000000) = (6892 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((728 : ℝ) / 100) ((2484321 : ℝ) / 1000000) ((6892 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_12 : Real.exp ((zVal 12 : ℝ) / 100) ≤ (ubInt 12 : ℝ) / 10000000 := by
  rw [show ((zVal 12 : ℝ) / 100) = -((727 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 12 : ℝ) / 10000000) = (6962 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((727 : ℝ) / 100) ((2481217 : ℝ) / 1000000) ((6962 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_13 : Real.exp ((zVal 13 : ℝ) / 100) ≤ (ubInt 13 : ℝ) / 10000000 := by
  rw [show ((zVal 13 : ℝ) / 100) = -((726 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 13 : ℝ) / 10000000) = (7032 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((726 : ℝ) / 100) ((2478118 : ℝ) / 1000000) ((7032 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_14 : Real.exp ((zVal 14 : ℝ) / 100) ≤ (ubInt 14 : ℝ) / 10000000 := by
  rw [show ((zVal 14 : ℝ) / 100) = -((724 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 14 : ℝ) / 10000000) = (7174 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((724 : ℝ) / 100) ((2471930 : ℝ) / 1000000) ((7174 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_15 : Real.exp ((zVal 15 : ℝ) / 100) ≤ (ubInt 15 : ℝ) / 10000000 := by
  rw [show ((zVal 15 : ℝ) / 100) = -((722 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 15 : ℝ) / 10000000) = (7319 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((722 : ℝ) / 100) ((2465758 : ℝ) / 1000000) ((7319 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_16 : Real.exp ((zVal 16 : ℝ) / 100) ≤ (ubInt 16 : ℝ) / 10000000 := by
  rw [show ((zVal 16 : ℝ) / 100) = -((721 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 16 : ℝ) / 10000000) = (7392 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((721 : ℝ) / 100) ((2462678 : ℝ) / 1000000) ((7392 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_17 : Real.exp ((zVal 17 : ℝ) / 100) ≤ (ubInt 17 : ℝ) / 10000000 := by
  rw [show ((zVal 17 : ℝ) / 100) = -((720 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 17 : ℝ) / 10000000) = (7466 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((720 : ℝ) / 100) ((2459601 : ℝ) / 1000000) ((7466 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_18 : Real.exp ((zVal 18 : ℝ) / 100) ≤ (ubInt 18 : ℝ) / 10000000 := by
  rw [show ((zVal 18 : ℝ) / 100) = -((719 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 18 : ℝ) / 10000000) = (7541 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((719 : ℝ) / 100) ((2456529 : ℝ) / 1000000) ((7541 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_19 : Real.exp ((zVal 19 : ℝ) / 100) ≤ (ubInt 19 : ℝ) / 10000000 := by
  rw [show ((zVal 19 : ℝ) / 100) = -((718 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 19 : ℝ) / 10000000) = (7617 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((718 : ℝ) / 100) ((2453460 : ℝ) / 1000000) ((7617 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_20 : Real.exp ((zVal 20 : ℝ) / 100) ≤ (ubInt 20 : ℝ) / 10000000 := by
  rw [show ((zVal 20 : ℝ) / 100) = -((717 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 20 : ℝ) / 10000000) = (7694 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((717 : ℝ) / 100) ((2450395 : ℝ) / 1000000) ((7694 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_21 : Real.exp ((zVal 21 : ℝ) / 100) ≤ (ubInt 21 : ℝ) / 10000000 := by
  rw [show ((zVal 21 : ℝ) / 100) = -((716 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 21 : ℝ) / 10000000) = (7771 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((716 : ℝ) / 100) ((2447334 : ℝ) / 1000000) ((7771 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_22 : Real.exp ((zVal 22 : ℝ) / 100) ≤ (ubInt 22 : ℝ) / 10000000 := by
  rw [show ((zVal 22 : ℝ) / 100) = -((715 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 22 : ℝ) / 10000000) = (7849 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((715 : ℝ) / 100) ((2444277 : ℝ) / 1000000) ((7849 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_23 : Real.exp ((zVal 23 : ℝ) / 100) ≤ (ubInt 23 : ℝ) / 10000000 := by
  rw [show ((zVal 23 : ℝ) / 100) = -((714 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 23 : ℝ) / 10000000) = (7928 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((714 : ℝ) / 100) ((2441224 : ℝ) / 1000000) ((7928 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_24 : Real.exp ((zVal 24 : ℝ) / 100) ≤ (ubInt 24 : ℝ) / 10000000 := by
  rw [show ((zVal 24 : ℝ) / 100) = -((713 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 24 : ℝ) / 10000000) = (8008 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((713 : ℝ) / 100) ((2438174 : ℝ) / 1000000) ((8008 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_25 : Real.exp ((zVal 25 : ℝ) / 100) ≤ (ubInt 25 : ℝ) / 10000000 := by
  rw [show ((zVal 25 : ℝ) / 100) = -((712 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 25 : ℝ) / 10000000) = (8088 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((712 : ℝ) / 100) ((2435128 : ℝ) / 1000000) ((8088 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_26 : Real.exp ((zVal 26 : ℝ) / 100) ≤ (ubInt 26 : ℝ) / 10000000 := by
  rw [show ((zVal 26 : ℝ) / 100) = -((711 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 26 : ℝ) / 10000000) = (8169 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((711 : ℝ) / 100) ((2432086 : ℝ) / 1000000) ((8169 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_27 : Real.exp ((zVal 27 : ℝ) / 100) ≤ (ubInt 27 : ℝ) / 10000000 := by
  rw [show ((zVal 27 : ℝ) / 100) = -((710 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 27 : ℝ) / 10000000) = (8252 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((710 : ℝ) / 100) ((2429048 : ℝ) / 1000000) ((8252 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_28 : Real.exp ((zVal 28 : ℝ) / 100) ≤ (ubInt 28 : ℝ) / 10000000 := by
  rw [show ((zVal 28 : ℝ) / 100) = -((709 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 28 : ℝ) / 10000000) = (8335 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((709 : ℝ) / 100) ((2426013 : ℝ) / 1000000) ((8335 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_29 : Real.exp ((zVal 29 : ℝ) / 100) ≤ (ubInt 29 : ℝ) / 10000000 := by
  rw [show ((zVal 29 : ℝ) / 100) = -((708 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 29 : ℝ) / 10000000) = (8418 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((708 : ℝ) / 100) ((2422983 : ℝ) / 1000000) ((8418 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_30 : Real.exp ((zVal 30 : ℝ) / 100) ≤ (ubInt 30 : ℝ) / 10000000 := by
  rw [show ((zVal 30 : ℝ) / 100) = -((707 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 30 : ℝ) / 10000000) = (8503 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((707 : ℝ) / 100) ((2419956 : ℝ) / 1000000) ((8503 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_31 : Real.exp ((zVal 31 : ℝ) / 100) ≤ (ubInt 31 : ℝ) / 10000000 := by
  rw [show ((zVal 31 : ℝ) / 100) = -((706 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 31 : ℝ) / 10000000) = (8588 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((706 : ℝ) / 100) ((2416933 : ℝ) / 1000000) ((8588 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_32 : Real.exp ((zVal 32 : ℝ) / 100) ≤ (ubInt 32 : ℝ) / 10000000 := by
  rw [show ((zVal 32 : ℝ) / 100) = -((705 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 32 : ℝ) / 10000000) = (8675 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((705 : ℝ) / 100) ((2413914 : ℝ) / 1000000) ((8675 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_33 : Real.exp ((zVal 33 : ℝ) / 100) ≤ (ubInt 33 : ℝ) / 10000000 := by
  rw [show ((zVal 33 : ℝ) / 100) = -((704 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 33 : ℝ) / 10000000) = (8762 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((704 : ℝ) / 100) ((2410898 : ℝ) / 1000000) ((8762 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_34 : Real.exp ((zVal 34 : ℝ) / 100) ≤ (ubInt 34 : ℝ) / 10000000 := by
  rw [show ((zVal 34 : ℝ) / 100) = -((702 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 34 : ℝ) / 10000000) = (8939 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((702 : ℝ) / 100) ((2404879 : ℝ) / 1000000) ((8939 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_35 : Real.exp ((zVal 35 : ℝ) / 100) ≤ (ubInt 35 : ℝ) / 10000000 := by
  rw [show ((zVal 35 : ℝ) / 100) = -((701 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 35 : ℝ) / 10000000) = (9029 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((701 : ℝ) / 100) ((2401874 : ℝ) / 1000000) ((9029 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_36 : Real.exp ((zVal 36 : ℝ) / 100) ≤ (ubInt 36 : ℝ) / 10000000 := by
  rw [show ((zVal 36 : ℝ) / 100) = -((700 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 36 : ℝ) / 10000000) = (9119 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((700 : ℝ) / 100) ((2398874 : ℝ) / 1000000) ((9119 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_37 : Real.exp ((zVal 37 : ℝ) / 100) ≤ (ubInt 37 : ℝ) / 10000000 := by
  rw [show ((zVal 37 : ℝ) / 100) = -((699 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 37 : ℝ) / 10000000) = (9211 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((699 : ℝ) / 100) ((2395877 : ℝ) / 1000000) ((9211 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_38 : Real.exp ((zVal 38 : ℝ) / 100) ≤ (ubInt 38 : ℝ) / 10000000 := by
  rw [show ((zVal 38 : ℝ) / 100) = -((698 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 38 : ℝ) / 10000000) = (9304 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((698 : ℝ) / 100) ((2392884 : ℝ) / 1000000) ((9304 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_39 : Real.exp ((zVal 39 : ℝ) / 100) ≤ (ubInt 39 : ℝ) / 10000000 := by
  rw [show ((zVal 39 : ℝ) / 100) = -((697 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 39 : ℝ) / 10000000) = (9397 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((697 : ℝ) / 100) ((2389895 : ℝ) / 1000000) ((9397 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_40 : Real.exp ((zVal 40 : ℝ) / 100) ≤ (ubInt 40 : ℝ) / 10000000 := by
  rw [show ((zVal 40 : ℝ) / 100) = -((696 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 40 : ℝ) / 10000000) = (9492 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((696 : ℝ) / 100) ((2386909 : ℝ) / 1000000) ((9492 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_41 : Real.exp ((zVal 41 : ℝ) / 100) ≤ (ubInt 41 : ℝ) / 10000000 := by
  rw [show ((zVal 41 : ℝ) / 100) = -((695 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 41 : ℝ) / 10000000) = (9587 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((695 : ℝ) / 100) ((2383928 : ℝ) / 1000000) ((9587 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_42 : Real.exp ((zVal 42 : ℝ) / 100) ≤ (ubInt 42 : ℝ) / 10000000 := by
  rw [show ((zVal 42 : ℝ) / 100) = -((694 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 42 : ℝ) / 10000000) = (9683 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((694 : ℝ) / 100) ((2380950 : ℝ) / 1000000) ((9683 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_43 : Real.exp ((zVal 43 : ℝ) / 100) ≤ (ubInt 43 : ℝ) / 10000000 := by
  rw [show ((zVal 43 : ℝ) / 100) = -((693 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 43 : ℝ) / 10000000) = (9781 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((693 : ℝ) / 100) ((2377975 : ℝ) / 1000000) ((9781 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_44 : Real.exp ((zVal 44 : ℝ) / 100) ≤ (ubInt 44 : ℝ) / 10000000 := by
  rw [show ((zVal 44 : ℝ) / 100) = -((692 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 44 : ℝ) / 10000000) = (9879 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((692 : ℝ) / 100) ((2375005 : ℝ) / 1000000) ((9879 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_45 : Real.exp ((zVal 45 : ℝ) / 100) ≤ (ubInt 45 : ℝ) / 10000000 := by
  rw [show ((zVal 45 : ℝ) / 100) = -((691 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 45 : ℝ) / 10000000) = (9978 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((691 : ℝ) / 100) ((2372038 : ℝ) / 1000000) ((9978 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_46 : Real.exp ((zVal 46 : ℝ) / 100) ≤ (ubInt 46 : ℝ) / 10000000 := by
  rw [show ((zVal 46 : ℝ) / 100) = -((690 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 46 : ℝ) / 10000000) = (10078 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((690 : ℝ) / 100) ((2369075 : ℝ) / 1000000) ((10078 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_47 : Real.exp ((zVal 47 : ℝ) / 100) ≤ (ubInt 47 : ℝ) / 10000000 := by
  rw [show ((zVal 47 : ℝ) / 100) = -((688 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 47 : ℝ) / 10000000) = (10282 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((688 : ℝ) / 100) ((2363159 : ℝ) / 1000000) ((10282 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_48 : Real.exp ((zVal 48 : ℝ) / 100) ≤ (ubInt 48 : ℝ) / 10000000 := by
  rw [show ((zVal 48 : ℝ) / 100) = -((687 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 48 : ℝ) / 10000000) = (10385 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((687 : ℝ) / 100) ((2360207 : ℝ) / 1000000) ((10385 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_49 : Real.exp ((zVal 49 : ℝ) / 100) ≤ (ubInt 49 : ℝ) / 10000000 := by
  rw [show ((zVal 49 : ℝ) / 100) = -((686 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 49 : ℝ) / 10000000) = (10490 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((686 : ℝ) / 100) ((2357259 : ℝ) / 1000000) ((10490 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_50 : Real.exp ((zVal 50 : ℝ) / 100) ≤ (ubInt 50 : ℝ) / 10000000 := by
  rw [show ((zVal 50 : ℝ) / 100) = -((685 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 50 : ℝ) / 10000000) = (10595 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((685 : ℝ) / 100) ((2354314 : ℝ) / 1000000) ((10595 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_51 : Real.exp ((zVal 51 : ℝ) / 100) ≤ (ubInt 51 : ℝ) / 10000000 := by
  rw [show ((zVal 51 : ℝ) / 100) = -((684 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 51 : ℝ) / 10000000) = (10702 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((684 : ℝ) / 100) ((2351373 : ℝ) / 1000000) ((10702 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_52 : Real.exp ((zVal 52 : ℝ) / 100) ≤ (ubInt 52 : ℝ) / 10000000 := by
  rw [show ((zVal 52 : ℝ) / 100) = -((682 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 52 : ℝ) / 10000000) = (10918 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((682 : ℝ) / 100) ((2345502 : ℝ) / 1000000) ((10918 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_53 : Real.exp ((zVal 53 : ℝ) / 100) ≤ (ubInt 53 : ℝ) / 10000000 := by
  rw [show ((zVal 53 : ℝ) / 100) = -((681 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 53 : ℝ) / 10000000) = (11027 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((681 : ℝ) / 100) ((2342572 : ℝ) / 1000000) ((11027 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_54 : Real.exp ((zVal 54 : ℝ) / 100) ≤ (ubInt 54 : ℝ) / 10000000 := by
  rw [show ((zVal 54 : ℝ) / 100) = -((680 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 54 : ℝ) / 10000000) = (11138 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((680 : ℝ) / 100) ((2339646 : ℝ) / 1000000) ((11138 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_55 : Real.exp ((zVal 55 : ℝ) / 100) ≤ (ubInt 55 : ℝ) / 10000000 := by
  rw [show ((zVal 55 : ℝ) / 100) = -((679 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 55 : ℝ) / 10000000) = (11250 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((679 : ℝ) / 100) ((2336723 : ℝ) / 1000000) ((11250 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_56 : Real.exp ((zVal 56 : ℝ) / 100) ≤ (ubInt 56 : ℝ) / 10000000 := by
  rw [show ((zVal 56 : ℝ) / 100) = -((677 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 56 : ℝ) / 10000000) = (11478 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((677 : ℝ) / 100) ((2330888 : ℝ) / 1000000) ((11478 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_57 : Real.exp ((zVal 57 : ℝ) / 100) ≤ (ubInt 57 : ℝ) / 10000000 := by
  rw [show ((zVal 57 : ℝ) / 100) = -((676 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 57 : ℝ) / 10000000) = (11593 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((676 : ℝ) / 100) ((2327977 : ℝ) / 1000000) ((11593 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_58 : Real.exp ((zVal 58 : ℝ) / 100) ≤ (ubInt 58 : ℝ) / 10000000 := by
  rw [show ((zVal 58 : ℝ) / 100) = -((675 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 58 : ℝ) / 10000000) = (11709 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((675 : ℝ) / 100) ((2325069 : ℝ) / 1000000) ((11709 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_59 : Real.exp ((zVal 59 : ℝ) / 100) ≤ (ubInt 59 : ℝ) / 10000000 := by
  rw [show ((zVal 59 : ℝ) / 100) = -((672 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 59 : ℝ) / 10000000) = (12066 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((672 : ℝ) / 100) ((2316366 : ℝ) / 1000000) ((12066 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_60 : Real.exp ((zVal 60 : ℝ) / 100) ≤ (ubInt 60 : ℝ) / 10000000 := by
  rw [show ((zVal 60 : ℝ) / 100) = -((671 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 60 : ℝ) / 10000000) = (12187 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((671 : ℝ) / 100) ((2313472 : ℝ) / 1000000) ((12187 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_61 : Real.exp ((zVal 61 : ℝ) / 100) ≤ (ubInt 61 : ℝ) / 10000000 := by
  rw [show ((zVal 61 : ℝ) / 100) = -((669 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 61 : ℝ) / 10000000) = (12433 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((669 : ℝ) / 100) ((2307696 : ℝ) / 1000000) ((12433 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_62 : Real.exp ((zVal 62 : ℝ) / 100) ≤ (ubInt 62 : ℝ) / 10000000 := by
  rw [show ((zVal 62 : ℝ) / 100) = -((664 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 62 : ℝ) / 10000000) = (13071 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((664 : ℝ) / 100) ((2293318 : ℝ) / 1000000) ((13071 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_63 : Real.exp ((zVal 63 : ℝ) / 100) ≤ (ubInt 63 : ℝ) / 10000000 := by
  rw [show ((zVal 63 : ℝ) / 100) = -((661 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 63 : ℝ) / 10000000) = (13469 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((661 : ℝ) / 100) ((2284734 : ℝ) / 1000000) ((13469 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_64 : Real.exp ((zVal 64 : ℝ) / 100) ≤ (ubInt 64 : ℝ) / 10000000 := by
  rw [show ((zVal 64 : ℝ) / 100) = -((455 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 64 : ℝ) / 10000000) = (105673 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((455 : ℝ) / 100) ((1766058 : ℝ) / 1000000) ((105673 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_65 : Real.exp ((zVal 65 : ℝ) / 100) ≤ (ubInt 65 : ℝ) / 10000000 := by
  rw [show ((zVal 65 : ℝ) / 100) = -((451 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 65 : ℝ) / 10000000) = (109986 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((451 : ℝ) / 100) ((1757249 : ℝ) / 1000000) ((109986 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_66 : Real.exp ((zVal 66 : ℝ) / 100) ≤ (ubInt 66 : ℝ) / 10000000 := by
  rw [show ((zVal 66 : ℝ) / 100) = -((444 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 66 : ℝ) / 10000000) = (117960 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((444 : ℝ) / 100) ((1741940 : ℝ) / 1000000) ((117960 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_67 : Real.exp ((zVal 67 : ℝ) / 100) ≤ (ubInt 67 : ℝ) / 10000000 := by
  rw [show ((zVal 67 : ℝ) / 100) = -((436 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 67 : ℝ) / 10000000) = (127785 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((436 : ℝ) / 100) ((1724608 : ℝ) / 1000000) ((127785 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_68 : Real.exp ((zVal 68 : ℝ) / 100) ≤ (ubInt 68 : ℝ) / 10000000 := by
  rw [show ((zVal 68 : ℝ) / 100) = -((425 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 68 : ℝ) / 10000000) = (142643 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((425 : ℝ) / 100) ((1701057 : ℝ) / 1000000) ((142643 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_69 : Real.exp ((zVal 69 : ℝ) / 100) ≤ (ubInt 69 : ℝ) / 10000000 := by
  rw [show ((zVal 69 : ℝ) / 100) = -((413 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 69 : ℝ) / 10000000) = (160830 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((413 : ℝ) / 100) ((1675731 : ℝ) / 1000000) ((160830 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_70 : Real.exp ((zVal 70 : ℝ) / 100) ≤ (ubInt 70 : ℝ) / 10000000 := by
  rw [show ((zVal 70 : ℝ) / 100) = -((400 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 70 : ℝ) / 10000000) = (183157 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((400 : ℝ) / 100) ((1648721 : ℝ) / 1000000) ((183157 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_71 : Real.exp ((zVal 71 : ℝ) / 100) ≤ (ubInt 71 : ℝ) / 10000000 := by
  rw [show ((zVal 71 : ℝ) / 100) = -((385 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 71 : ℝ) / 10000000) = (212799 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((385 : ℝ) / 100) ((1618095 : ℝ) / 1000000) ((212799 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_72 : Real.exp ((zVal 72 : ℝ) / 100) ≤ (ubInt 72 : ℝ) / 10000000 := by
  rw [show ((zVal 72 : ℝ) / 100) = -((369 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 72 : ℝ) / 10000000) = (249721 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((369 : ℝ) / 100) ((1586055 : ℝ) / 1000000) ((249721 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_73 : Real.exp ((zVal 73 : ℝ) / 100) ≤ (ubInt 73 : ℝ) / 10000000 := by
  rw [show ((zVal 73 : ℝ) / 100) = -((354 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 73 : ℝ) / 10000000) = (290135 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((354 : ℝ) / 100) ((1556593 : ℝ) / 1000000) ((290135 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_74 : Real.exp ((zVal 74 : ℝ) / 100) ≤ (ubInt 74 : ℝ) / 10000000 := by
  rw [show ((zVal 74 : ℝ) / 100) = -((339 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 74 : ℝ) / 10000000) = (337088 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((339 : ℝ) / 100) ((1527679 : ℝ) / 1000000) ((337088 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_75 : Real.exp ((zVal 75 : ℝ) / 100) ≤ (ubInt 75 : ℝ) / 10000000 := by
  rw [show ((zVal 75 : ℝ) / 100) = -((325 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 75 : ℝ) / 10000000) = (387744 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((325 : ℝ) / 100) ((1501177 : ℝ) / 1000000) ((387744 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_76 : Real.exp ((zVal 76 : ℝ) / 100) ≤ (ubInt 76 : ℝ) / 10000000 := by
  rw [show ((zVal 76 : ℝ) / 100) = -((313 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 76 : ℝ) / 10000000) = (437179 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((313 : ℝ) / 100) ((1478828 : ℝ) / 1000000) ((437179 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_77 : Real.exp ((zVal 77 : ℝ) / 100) ≤ (ubInt 77 : ℝ) / 10000000 := by
  rw [show ((zVal 77 : ℝ) / 100) = -((303 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 77 : ℝ) / 10000000) = (483159 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((303 : ℝ) / 100) ((1460457 : ℝ) / 1000000) ((483159 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_78 : Real.exp ((zVal 78 : ℝ) / 100) ≤ (ubInt 78 : ℝ) / 10000000 := by
  rw [show ((zVal 78 : ℝ) / 100) = -((295 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 78 : ℝ) / 10000000) = (523398 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((295 : ℝ) / 100) ((1445926 : ℝ) / 1000000) ((523398 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_79 : Real.exp ((zVal 79 : ℝ) / 100) ≤ (ubInt 79 : ℝ) / 10000000 := by
  rw [show ((zVal 79 : ℝ) / 100) = -((289 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 79 : ℝ) / 10000000) = (555763 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((289 : ℝ) / 100) ((1435122 : ℝ) / 1000000) ((555763 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]
private lemma exp_ub_80 : Real.exp ((zVal 80 : ℝ) / 100) ≤ (ubInt 80 : ℝ) / 10000000 := by
  rw [show ((zVal 80 : ℝ) / 100) = -((285 : ℝ) / 100) by norm_num [zVal],
      show ((ubInt 80 : ℝ) / 10000000) = (578445 : ℝ) / 10000000 by norm_num [ubInt]]
  refine exp_neg_le_eight ((285 : ℝ) / 100) ((1427964 : ℝ) / 1000000) ((578445 : ℝ) / 10000000)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  norm_num [Finset.sum_range_succ]

private lemma exp_zVal_le (k : Fin 81) : Real.exp ((zVal k : ℝ) / 100) ≤ (ubInt k : ℝ) / 10000000 := by
  fin_cases k
  · dsimp; exact exp_ub_0
  · dsimp; exact exp_ub_1
  · dsimp; exact exp_ub_2
  · dsimp; exact exp_ub_3
  · dsimp; exact exp_ub_4
  · dsimp; exact exp_ub_5
  · dsimp; exact exp_ub_6
  · dsimp; exact exp_ub_7
  · dsimp; exact exp_ub_8
  · dsimp; exact exp_ub_9
  · dsimp; exact exp_ub_10
  · dsimp; exact exp_ub_11
  · dsimp; exact exp_ub_12
  · dsimp; exact exp_ub_13
  · dsimp; exact exp_ub_14
  · dsimp; exact exp_ub_15
  · dsimp; exact exp_ub_16
  · dsimp; exact exp_ub_17
  · dsimp; exact exp_ub_18
  · dsimp; exact exp_ub_19
  · dsimp; exact exp_ub_20
  · dsimp; exact exp_ub_21
  · dsimp; exact exp_ub_22
  · dsimp; exact exp_ub_23
  · dsimp; exact exp_ub_24
  · dsimp; exact exp_ub_25
  · dsimp; exact exp_ub_26
  · dsimp; exact exp_ub_27
  · dsimp; exact exp_ub_28
  · dsimp; exact exp_ub_29
  · dsimp; exact exp_ub_30
  · dsimp; exact exp_ub_31
  · dsimp; exact exp_ub_32
  · dsimp; exact exp_ub_33
  · dsimp; exact exp_ub_34
  · dsimp; exact exp_ub_35
  · dsimp; exact exp_ub_36
  · dsimp; exact exp_ub_37
  · dsimp; exact exp_ub_38
  · dsimp; exact exp_ub_39
  · dsimp; exact exp_ub_40
  · dsimp; exact exp_ub_41
  · dsimp; exact exp_ub_42
  · dsimp; exact exp_ub_43
  · dsimp; exact exp_ub_44
  · dsimp; exact exp_ub_45
  · dsimp; exact exp_ub_46
  · dsimp; exact exp_ub_47
  · dsimp; exact exp_ub_48
  · dsimp; exact exp_ub_49
  · dsimp; exact exp_ub_50
  · dsimp; exact exp_ub_51
  · dsimp; exact exp_ub_52
  · dsimp; exact exp_ub_53
  · dsimp; exact exp_ub_54
  · dsimp; exact exp_ub_55
  · dsimp; exact exp_ub_56
  · dsimp; exact exp_ub_57
  · dsimp; exact exp_ub_58
  · dsimp; exact exp_ub_59
  · dsimp; exact exp_ub_60
  · dsimp; exact exp_ub_61
  · dsimp; exact exp_ub_62
  · dsimp; exact exp_ub_63
  · dsimp; exact exp_ub_64
  · dsimp; exact exp_ub_65
  · dsimp; exact exp_ub_66
  · dsimp; exact exp_ub_67
  · dsimp; exact exp_ub_68
  · dsimp; exact exp_ub_69
  · dsimp; exact exp_ub_70
  · dsimp; exact exp_ub_71
  · dsimp; exact exp_ub_72
  · dsimp; exact exp_ub_73
  · dsimp; exact exp_ub_74
  · dsimp; exact exp_ub_75
  · dsimp; exact exp_ub_76
  · dsimp; exact exp_ub_77
  · dsimp; exact exp_ub_78
  · dsimp; exact exp_ub_79
  · dsimp; exact exp_ub_80

private lemma log_seventeen_gt : (28332133 / 10000000 : ℝ) < Real.log 17 := by
  have h16 : Real.log 17 = 4 * Real.log 2 - Real.log (16 / 17) := by
    have h17 : (17 : ℝ) = 2 ^ 4 / (16 / 17) := by norm_num
    rw [h17, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hrem := Real.abs_log_sub_add_sum_range_le (x := (1 / 17 : ℝ)) (by norm_num) 6
  have hhi := (abs_le.mp hrem).2
  norm_num [Finset.sum_range_succ] at hhi
  linarith [Real.log_two_gt_d9]

private lemma fenchel_log {x c : ℝ} (hx : 0 ≤ x) :
    c * x - Real.exp (c - 1) ≤ x * Real.log x := by
  rcases hx.eq_or_lt with rfl | hpos
  · simp [le_of_lt (Real.exp_pos _)]
  · have h := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos (c - 1)) hpos)
    rw [Real.log_div (Real.exp_pos (c - 1)).ne' hpos.ne', Real.log_exp] at h
    have hm := mul_le_mul_of_nonneg_right h hx
    have hdiv : Real.exp (c - 1) / x * x = Real.exp (c - 1) := div_mul_cancel₀ _ hpos.ne'
    linarith

private noncomputable def LCell (i j : Fin 17) (t : Fin 4) : ℝ :=
  yRow i + yCol j + yDiag false (sPlus i j t) + yDiag true (sMinus i j t) + Real.log 1156

private noncomputable def LDiag (b : Bool) (s : Fin 34) : ℝ :=
  yDiag b s + Real.log 17

private lemma exp_LCell_div (i j : Fin 17) (t : Fin 4) :
    Real.exp (LCell i j t - 1) / 1156 ≤ (ubInt (cellIdx i j t) : ℝ) / 10000000 := by
  have heq : LCell i j t - 1 = ((cellZInt i j t : ℝ) / 100) + Real.log 1156 := by
    unfold LCell yRow yCol yDiag cellZInt
    dsimp
    push_cast
    ring
  rw [heq, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 1156), mul_div_cancel_right₀ _ (by norm_num)]
  rw [← cellIdx_spec i j t]
  exact exp_zVal_le (cellIdx i j t)

private lemma exp_LDiag_div (b : Bool) (s : Fin 34) :
    Real.exp (LDiag b s - 1) / 17 ≤ (ubInt (diagIdx b s) : ℝ) / 10000000 := by
  have heq : LDiag b s - 1 = ((diagZInt b s : ℝ) / 100) + Real.log 17 := by
    unfold LDiag yDiag diagZInt
    push_cast
    ring
  rw [heq, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 17), mul_div_cancel_right₀ _ (by norm_num)]
  rw [← diagIdx_spec b s]
  exact exp_zVal_le (diagIdx b s)

private def splitOrig {N : ℕ} (_hN : 0 < N) : Fin (34 * N) ≃ Fin N × Fin 34 where
  toFun u := (⟨u.val / 34, by omega⟩, ⟨u.val % 34, by omega⟩)
  invFun pa := ⟨34 * pa.1.val + pa.2.val, by omega⟩
  left_inv u := by ext; dsimp; omega
  right_inv pa := by ext <;> dsimp <;> omega

private def splitCoarse {N : ℕ} (hN : 0 < N) : Fin (34 * N) ≃ Fin 17 × Fin (2 * N) where
  toFun u := (⟨u.val / (2 * N), by nlinarith [u.isLt, Nat.div_mul_le_self u.val (2 * N)]⟩,
              ⟨u.val % (2 * N), Nat.mod_lt _ (by omega)⟩)
  invFun ia := ⟨2 * N * ia.1.val + ia.2.val, by nlinarith [ia.1.isLt, ia.2.isLt]⟩
  left_inv u := by
    ext; dsimp
    exact Nat.div_add_mod u.val (2 * N)
  right_inv ia := by
    ext <;> dsimp
    · rw [Nat.mul_add_div (by omega : 0 < 2 * N), Nat.div_eq_of_lt ia.2.isLt, add_zero]
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ia.2.isLt]

private def split68Orig {N : ℕ} (_hN : 0 < N) : Fin (68 * N) ≃ Fin (2 * N) × Fin 34 where
  toFun m := (⟨m.val / 34, by omega⟩, ⟨m.val % 34, by omega⟩)
  invFun kr := ⟨34 * kr.1.val + kr.2.val, by omega⟩
  left_inv m := by ext; dsimp; omega
  right_inv kr := by ext <;> dsimp <;> omega

private def split68Coarse {N : ℕ} (hN : 0 < N) : Fin (68 * N) ≃ Fin 34 × Fin (2 * N) where
  toFun m := (⟨m.val / (2 * N), by nlinarith [m.isLt, Nat.div_mul_le_self m.val (2 * N)]⟩,
              ⟨m.val % (2 * N), Nat.mod_lt _ (by omega)⟩)
  invFun sr := ⟨2 * N * sr.1.val + sr.2.val, by nlinarith [sr.1.isLt, sr.2.isLt]⟩
  left_inv m := by ext; dsimp; exact Nat.div_add_mod m.val (2 * N)
  right_inv sr := by
    ext <;> dsimp
    · rw [Nat.mul_add_div (by omega : 0 < 2 * N), Nat.div_eq_of_lt sr.2.isLt, add_zero]
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt sr.2.isLt]

private def wTriNat (N a b : ℕ) (t : Fin 4) : ℕ :=
  if t.val = 0 then
    if a + b < 2 * N - 1 ∧ a < b then 4
    else if (a + b = 2 * N - 1 ∧ a < b) ∨ (a + b < 2 * N - 1 ∧ a = b) then 2 else 0
  else if t.val = 1 then
    if a + b < 2 * N - 1 ∧ b < a then 4
    else if (a + b = 2 * N - 1 ∧ b < a) ∨ (a + b < 2 * N - 1 ∧ a = b) then 2 else 0
  else if t.val = 2 then
    if 2 * N - 1 < a + b ∧ b < a then 4
    else if (a + b = 2 * N - 1 ∧ b < a) ∨ (2 * N - 1 < a + b ∧ a = b) then 2 else 0
  else
    if 2 * N - 1 < a + b ∧ a < b then 4
    else if (a + b = 2 * N - 1 ∧ a < b) ∨ (2 * N - 1 < a + b ∧ a = b) then 2 else 0

@[simp] private lemma wTriNat_0 (N a b : ℕ) : wTriNat N a b 0 =
    (if a + b < 2 * N - 1 ∧ a < b then 4
     else if (a + b = 2 * N - 1 ∧ a < b) ∨ (a + b < 2 * N - 1 ∧ a = b) then 2 else 0) := rfl

@[simp] private lemma wTriNat_1 (N a b : ℕ) : wTriNat N a b 1 =
    (if a + b < 2 * N - 1 ∧ b < a then 4
     else if (a + b = 2 * N - 1 ∧ b < a) ∨ (a + b < 2 * N - 1 ∧ a = b) then 2 else 0) := rfl

@[simp] private lemma wTriNat_2 (N a b : ℕ) : wTriNat N a b 2 =
    (if 2 * N - 1 < a + b ∧ b < a then 4
     else if (a + b = 2 * N - 1 ∧ b < a) ∨ (2 * N - 1 < a + b ∧ a = b) then 2 else 0) := rfl

@[simp] private lemma wTriNat_3 (N a b : ℕ) : wTriNat N a b 3 =
    (if 2 * N - 1 < a + b ∧ a < b then 4
     else if (a + b = 2 * N - 1 ∧ a < b) ∨ (2 * N - 1 < a + b ∧ a = b) then 2 else 0) := rfl

private lemma wTriNat_sum_four {N : ℕ} (hN : 0 < N) (a b : Fin (2 * N)) :
    ∑ t : Fin 4, wTriNat N a.val b.val t = 4 := by
  rw [Fin.sum_univ_four]
  simp only [wTriNat_0, wTriNat_1, wTriNat_2, wTriNat_3]
  have ha := a.isLt; have hb := b.isLt
  split_ifs <;> omega

private lemma wTriNat_block_sum {N : ℕ} (hN : 0 < N) (t : Fin 4) :
    ∑ a : Fin (2 * N), ∑ b : Fin (2 * N), wTriNat N a.val b.val t = 4 * N ^ 2 := by
  let S (k : Fin 4) : ℕ := ∑ a : Fin (2 * N), ∑ b : Fin (2 * N), wTriNat N a.val b.val k
  have h10 : S 1 = S 0 := by
    dsimp [S]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> omega
  have h23 : S 2 = S 3 := by
    dsimp [S]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> omega
  have h20 : S 2 = S 0 := by
    dsimp [S]
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have ha := a.isLt; have hb := b.isLt
    simp only [Fin.revPerm_apply, Fin.val_rev]
    split_ifs <;> omega
  have htot : S 0 + S 1 + S 2 + S 3 = 16 * N ^ 2 := by
    have h4 : S 0 + S 1 + S 2 + S 3 = ∑ k : Fin 4, S k := (Fin.sum_univ_four S).symm
    rw [h4]
    dsimp [S]
    rw [Finset.sum_comm]
    have hinner : ∀ a : Fin (2 * N), ∑ k : Fin 4, ∑ b : Fin (2 * N), wTriNat N a.val b.val k = 8 * N := by
      intro a
      rw [Finset.sum_comm]
      simp_rw [wTriNat_sum_four hN]
      simp [Finset.sum_const, Fintype.card_fin]; ring
    simp_rw [hinner]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  change S t = 4 * N ^ 2
  fin_cases t <;> dsimp <;> omega

set_option maxRecDepth 20000 in
private lemma fin34_counts : ∀ t : Fin 68,
    ((Finset.univ.filter fun p : Fin 34 × Fin 34 => p.1.val + p.2.val = t.val).card +
     (Finset.univ.filter fun p : Fin 34 × Fin 34 => p.1.val + p.2.val + 1 = t.val).card) =
    if t.val < 34 then 2 * t.val + 1 else 67 - 2 * (t.val - 34) := by
  decide +kernel

private lemma fin34_diag_bridge (g : ℕ → ℝ) :
    ∑ a1 : Fin 34, ∑ a2 : Fin 34, (g (a1.val + a2.val) + g (a1.val + a2.val + 1)) / 2 =
    ∑ r : Fin 34, (((2 * (r.val : ℝ) + 1) / 2) * g r.val +
      ((67 - 2 * (r.val : ℝ)) / 2) * g (34 + r.val)) := by
  have hsum1 : ∑ p : Fin 34 × Fin 34, g (p.1.val + p.2.val) =
      ∑ t : Fin 68, ((Finset.univ.filter fun p : Fin 34 × Fin 34 => p.1.val + p.2.val = t.val).card : ℝ) * g t.val := by
    have h := (Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin 34 × Fin 34)))
      (t := (Finset.univ : Finset (Fin 68)))
      (g := fun p : Fin 34 × Fin 34 => (⟨p.1.val + p.2.val, by omega⟩ : Fin 68))
      (f := fun p => g (p.1.val + p.2.val)) (fun _ _ => Finset.mem_univ _)).symm
    rw [h]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hcongr : ∑ x ∈ Finset.univ.filter (fun p : Fin 34 × Fin 34 => (⟨p.1.val + p.2.val, by omega⟩ : Fin 68) = t),
        g (x.1.val + x.2.val) =
        ∑ _x ∈ Finset.univ.filter (fun p : Fin 34 × Fin 34 => p.1.val + p.2.val = t.val), g t.val := by
      refine Finset.sum_congr ?_ fun x hx => ?_
      · ext p; simp [Fin.ext_iff]
      · simp only [Finset.mem_filter] at hx; rw [hx.2]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  have hsum2 : ∑ p : Fin 34 × Fin 34, g (p.1.val + p.2.val + 1) =
      ∑ t : Fin 68, ((Finset.univ.filter fun p : Fin 34 × Fin 34 => p.1.val + p.2.val + 1 = t.val).card : ℝ) * g t.val := by
    have h := (Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin 34 × Fin 34)))
      (t := (Finset.univ : Finset (Fin 68)))
      (g := fun p : Fin 34 × Fin 34 => (⟨p.1.val + p.2.val + 1, by omega⟩ : Fin 68))
      (f := fun p => g (p.1.val + p.2.val + 1)) (fun _ _ => Finset.mem_univ _)).symm
    rw [h]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hcongr : ∑ x ∈ Finset.univ.filter (fun p : Fin 34 × Fin 34 => (⟨p.1.val + p.2.val + 1, by omega⟩ : Fin 68) = t),
        g (x.1.val + x.2.val + 1) =
        ∑ _x ∈ Finset.univ.filter (fun p : Fin 34 × Fin 34 => p.1.val + p.2.val + 1 = t.val), g t.val := by
      refine Finset.sum_congr ?_ fun x hx => ?_
      · ext p; simp [Fin.ext_iff]
      · simp only [Finset.mem_filter] at hx; rw [hx.2]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.sum_prod_type']
  simp_rw [add_div]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, hsum1, hsum2, ← add_div, ← Finset.sum_add_distrib]
  have hcomb : (∑ x : Fin 68,
      (((Finset.univ.filter fun p : Fin 34 × Fin 34 => p.1.val + p.2.val = x.val).card : ℝ) * g x.val +
       ((Finset.univ.filter fun p : Fin 34 × Fin 34 => p.1.val + p.2.val + 1 = x.val).card : ℝ) * g x.val)) / 2 =
      ∑ x : Fin 68, (((if x.val < 34 then 2 * x.val + 1 else 67 - 2 * (x.val - 34) : ℕ) : ℝ) / 2) * g x.val := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← add_mul, ← Nat.cast_add, fin34_counts x, mul_div_right_comm]
  rw [hcomb]
  let e : Fin 34 ⊕ Fin 34 ≃ Fin 68 := finSumFinEquiv
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr := r.isLt
  have h1 : (e (Sum.inl r)).val = r.val := by
    change (finSumFinEquiv (Sum.inl r)).val = r.val
    rw [finSumFinEquiv_apply_left]; rfl
  have h2 : (e (Sum.inr r)).val = 34 + r.val := by
    change (finSumFinEquiv (Sum.inr r)).val = 34 + r.val
    rw [finSumFinEquiv_apply_right]; exact Fin.val_natAdd 34 r
  rw [h1, h2, if_pos hr, if_neg (by omega : ¬ 34 + r.val < 34)]
  have hsub : 34 + r.val - 34 = r.val := by omega
  have hle : 2 * r.val ≤ 67 := by omega
  rw [hsub, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_sub hle, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat]
  ring

private lemma integral_seg_fenchel {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (L : Fin 34 → ℝ) :
    ∑ r : Fin 34, (1 / 34 : ℝ) *
      (L r * (((67 - 2 * (r.val : ℝ)) / 68) * a + ((2 * (r.val : ℝ) + 1) / 68) * b) -
       Real.exp (L r - 1)) ≤
    ∫ t in (0 : ℝ)..1, ((1 - t) * a + t * b) * Real.log ((1 - t) * a + t * b) := by
  let g (t : ℝ) : ℝ := ((1 - t) * a + t * b) * Real.log ((1 - t) * a + t * b)
  have hg_cont : Continuous g :=
    Real.continuous_mul_log.comp ((continuous_const.sub continuous_id).mul continuous_const |>.add (continuous_id.mul continuous_const))
  have hsplit : (∑ k ∈ Finset.range 34, ∫ t in ((k : ℝ) / 34)..(((k + 1 : ℕ) : ℝ) / 34), g t) =
      ∫ t in (0 : ℝ)..1, g t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (μ := MeasureTheory.volume) (a := fun k : ℕ => (k : ℝ) / 34) (n := 34)
      (fun k _ => hg_cont.intervalIntegrable _ _)
    simpa using h
  rw [← hsplit, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_le_sum fun r _ => ?_
  let t0 : ℝ := (r.val : ℝ) / 34
  let t1 : ℝ := ((r.val + 1 : ℕ) : ℝ) / 34
  have ht01 : t0 ≤ t1 := by dsimp [t0, t1]; push_cast; linarith
  let lin (t : ℝ) : ℝ := L r * ((1 - t) * a + t * b) - Real.exp (L r - 1)
  have hlin_cont : Continuous lin := by fun_prop
  have hmono : ∫ t in t0..t1, lin t ≤ ∫ t in t0..t1, g t := by
    refine intervalIntegral.integral_mono_on ht01 (hlin_cont.intervalIntegrable _ _)
      (hg_cont.intervalIntegrable _ _) fun t ht => ?_
    have hr := r.isLt
    have ht_lo : 0 ≤ t := by
      have : (0 : ℝ) ≤ t0 := by dsimp [t0]; positivity
      exact this.trans ht.1
    have ht_hi : t ≤ 1 := by
      have : t1 ≤ 1 := by
        dsimp [t1]; push_cast
        have hr1 : (r.val : ℝ) + 1 ≤ 34 := by exact_mod_cast hr
        linarith
      exact ht.2.trans this
    have hnonneg : 0 ≤ (1 - t) * a + t * b := add_nonneg (mul_nonneg (by linarith) ha) (mul_nonneg ht_lo hb)
    exact fenchel_log hnonneg
  refine le_trans ?_ hmono
  have heq_lin : ∀ t : ℝ, lin t = (L r * a - Real.exp (L r - 1)) + (L r * (b - a)) * t := fun t => by
    dsimp [lin]; ring
  simp_rw [heq_lin]
  rw [intervalIntegral.integral_add (intervalIntegrable_const) ((intervalIntegral.intervalIntegrable_id).const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  dsimp [t0, t1]
  push_cast
  exact le_of_eq (by ring)

private def diagArg {N : ℕ} (b : Bool) (v : Fin (34 * N)) : ℕ :=
  if b then 34 * N - 1 - v.val else v.val

private lemma diagArg_lt {N : ℕ} (b : Bool) (v : Fin (34 * N)) :
    diagArg b v < 34 * N := by
  unfold diagArg
  have := v.isLt
  split_ifs <;> omega

private def diagSlot {N : ℕ} (_hN : 0 < N) (b : Bool) (u v : Fin (34 * N)) (c : ℕ) (hc : c ≤ 1) : Fin 34 :=
  ⟨(u.val + diagArg b v + c) / (2 * N), by
    have hu := u.isLt
    have hv := diagArg_lt b v
    have hsum : u.val + diagArg b v + c < 68 * N := by omega
    nlinarith [Nat.div_mul_le_self (u.val + diagArg b v + c) (2 * N)]⟩

private lemma div_2N_add {N i r : ℕ} (hN : 0 < N) (hr : r < 2 * N) :
    (2 * N * i + r) / (2 * N) = i := by
  rw [Nat.mul_add_div (by omega : 0 < 2 * N), Nat.div_eq_of_lt hr, add_zero]

set_option maxHeartbeats 800000 in
private lemma pointwise_cancel {N : ℕ} (hN : 0 < N) (u v : Fin (34 * N)) :
    let i : Fin 17 := ⟨u.val / (2 * N), by nlinarith [u.isLt, Nat.div_mul_le_self u.val (2 * N)]⟩
    let α : Fin (2 * N) := ⟨u.val % (2 * N), Nat.mod_lt _ (by omega)⟩
    let j : Fin 17 := ⟨v.val / (2 * N), by nlinarith [v.isLt, Nat.div_mul_le_self v.val (2 * N)]⟩
    let β : Fin (2 * N) := ⟨v.val % (2 * N), Nat.mod_lt _ (by omega)⟩
    (∑ t : Fin 4, ((wTriNat N α.val β.val t : ℝ) / 4) * LCell i j t) -
      ((LDiag false (diagSlot hN false u v 0 (by omega)) +
        LDiag false (diagSlot hN false u v 1 (by omega))) / 2 +
       (LDiag true (diagSlot hN true u v 0 (by omega)) +
        LDiag true (diagSlot hN true u v 1 (by omega))) / 2) =
    yRow i + yCol j + 2 * Real.log 2 := by
  intro i α j β
  have hu : u.val = 2 * N * i.val + α.val := (Nat.div_add_mod u.val (2 * N)).symm
  have hv : v.val = 2 * N * j.val + β.val := (Nat.div_add_mod v.val (2 * N)).symm
  have hi := i.isLt; have hj := j.isLt; have hα := α.isLt; have hβ := β.isLt; have hv_lt := v.isLt
  have hj16 : (16 - j.val) + j.val = 16 := by omega
  have hβ1 : (2 * N - 1 - β.val) + β.val + 1 = 2 * N := by omega
  have hw_add : diagArg true v + v.val + 1 = 34 * N := by unfold diagArg; simp; omega
  have hw : diagArg true v = 2 * N * (16 - j.val) + (2 * N - 1 - β.val) := by
    have hsum_rhs : (2 * N * (16 - j.val) + (2 * N - 1 - β.val)) + v.val + 1 = 34 * N := by
      calc (2 * N * (16 - j.val) + (2 * N - 1 - β.val)) + v.val + 1
        _ = 2 * N * ((16 - j.val) + j.val) + ((2 * N - 1 - β.val) + β.val + 1) := by rw [hv]; ring
        _ = 34 * N := by rw [hj16, hβ1]; ring
    omega
  have hdf : diagArg false v = v.val := rfl
  have hlog : Real.log 1156 - 2 * Real.log 17 = 2 * Real.log 2 := by
    have h1156 : (1156 : ℝ) = 2 ^ 2 * 17 ^ 2 := by norm_num
    rw [h1156, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  have hsum_w : (∑ t : Fin 4, (wTriNat N α.val β.val t : ℝ) / 4) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, wTriNat_sum_four hN α β]
    norm_num
  have hp_eq : ∑ t : Fin 4, ((wTriNat N α.val β.val t : ℝ) / 4) * yDiag false (sPlus i j t) =
      (yDiag false (diagSlot hN false u v 0 (by omega)) +
       yDiag false (diagSlot hN false u v 1 (by omega))) / 2 := by
    rw [Fin.sum_univ_four]
    rcases lt_trichotomy (α.val + β.val) (2 * N - 1) with hlt | heq | hgt
    · have d1 : diagSlot hN false u v 0 (by omega) = ⟨i.val + j.val, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg false v + 0) / (2 * N) = i.val + j.val
        have hnum : u.val + diagArg false v + 0 = 2 * N * (i.val + j.val) + (α.val + β.val) := by rw [hdf, hu, hv]; ring
        rw [hnum]; exact div_2N_add hN (by omega)
      have d2 : diagSlot hN false u v 1 (by omega) = ⟨i.val + j.val, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg false v + 1) / (2 * N) = i.val + j.val
        have hnum : u.val + diagArg false v + 1 = 2 * N * (i.val + j.val) + (α.val + β.val + 1) := by rw [hdf, hu, hv]; ring
        rw [hnum]; exact div_2N_add hN (by omega)
      have hw01 : wTriNat N α.val β.val 0 + wTriNat N α.val β.val 1 = 4 := by
        simp only [wTriNat_0, wTriNat_1]; split_ifs <;> omega
      have hw2 : wTriNat N α.val β.val 2 = 0 := by simp only [wTriNat_2]; split_ifs <;> omega
      have hw3 : wTriNat N α.val β.val 3 = 0 := by simp only [wTriNat_3]; split_ifs <;> omega
      have sp0 : sPlus i j 0 = ⟨i.val + j.val, by omega⟩ := rfl
      have sp1 : sPlus i j 1 = ⟨i.val + j.val, by omega⟩ := rfl
      rw [sp0, sp1, hw2, hw3, d1, d2]
      simp only [Nat.cast_zero, zero_div, zero_mul, add_zero]
      rw [← add_mul, ← add_div, ← Nat.cast_add, hw01]; ring
    · have h2N : (2 * N - 1) + 1 = 2 * N := by omega
      have d1 : diagSlot hN false u v 0 (by omega) = ⟨i.val + j.val, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg false v + 0) / (2 * N) = i.val + j.val
        have hnum : u.val + diagArg false v + 0 = 2 * N * (i.val + j.val) + (2 * N - 1) := by
          calc u.val + diagArg false v + 0 = 2 * N * (i.val + j.val) + (α.val + β.val) := by rw [hdf, hu, hv]; ring
            _ = 2 * N * (i.val + j.val) + (2 * N - 1) := by rw [heq]
        rw [hnum]; exact div_2N_add hN (by omega)
      have d2 : diagSlot hN false u v 1 (by omega) = ⟨i.val + j.val + 1, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg false v + 1) / (2 * N) = i.val + j.val + 1
        have hnum : u.val + diagArg false v + 1 = 2 * N * (i.val + j.val + 1) + 0 := by
          calc u.val + diagArg false v + 1 = 2 * N * (i.val + j.val) + ((α.val + β.val) + 1) := by rw [hdf, hu, hv]; ring
            _ = 2 * N * (i.val + j.val + 1) + 0 := by rw [heq, h2N]; ring
        rw [hnum]; exact div_2N_add hN (by omega)
      have hw01 : wTriNat N α.val β.val 0 + wTriNat N α.val β.val 1 = 2 := by
        simp only [wTriNat_0, wTriNat_1]; split_ifs <;> omega
      have hw23 : wTriNat N α.val β.val 2 + wTriNat N α.val β.val 3 = 2 := by
        simp only [wTriNat_2, wTriNat_3]; split_ifs <;> omega
      have sp0 : sPlus i j 0 = ⟨i.val + j.val, by omega⟩ := rfl
      have sp1 : sPlus i j 1 = ⟨i.val + j.val, by omega⟩ := rfl
      have sp2 : sPlus i j 2 = ⟨i.val + j.val + 1, by omega⟩ := rfl
      have sp3 : sPlus i j 3 = ⟨i.val + j.val + 1, by omega⟩ := rfl
      rw [sp0, sp1, sp2, sp3, d1, d2]
      have hg1 : ((wTriNat N α.val β.val 0 : ℝ) / 4) * yDiag false ⟨i.val + j.val, by omega⟩ +
          ((wTriNat N α.val β.val 1 : ℝ) / 4) * yDiag false ⟨i.val + j.val, by omega⟩ =
          (2 / 4 : ℝ) * yDiag false ⟨i.val + j.val, by omega⟩ := by
        rw [← add_mul, ← add_div, ← Nat.cast_add, hw01]; norm_num
      have hg2 : ((wTriNat N α.val β.val 2 : ℝ) / 4) * yDiag false ⟨i.val + j.val + 1, by omega⟩ +
          ((wTriNat N α.val β.val 3 : ℝ) / 4) * yDiag false ⟨i.val + j.val + 1, by omega⟩ =
          (2 / 4 : ℝ) * yDiag false ⟨i.val + j.val + 1, by omega⟩ := by
        rw [← add_mul, ← add_div, ← Nat.cast_add, hw23]; norm_num
      linarith [hg1, hg2]
    · let r1 := α.val + β.val - 2 * N
      let r2 := α.val + β.val + 1 - 2 * N
      have hsub1 : α.val + β.val = r1 + 2 * N := by dsimp [r1]; omega
      have hsub2 : α.val + β.val + 1 = r2 + 2 * N := by dsimp [r2]; omega
      have d1 : diagSlot hN false u v 0 (by omega) = ⟨i.val + j.val + 1, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg false v + 0) / (2 * N) = i.val + j.val + 1
        have hnum : u.val + diagArg false v + 0 = 2 * N * (i.val + j.val + 1) + r1 := by
          calc u.val + diagArg false v + 0 = 2 * N * (i.val + j.val) + (α.val + β.val) := by rw [hdf, hu, hv]; ring
            _ = 2 * N * (i.val + j.val + 1) + r1 := by rw [hsub1]; ring
        rw [hnum]; exact div_2N_add hN (by dsimp [r1]; omega)
      have d2 : diagSlot hN false u v 1 (by omega) = ⟨i.val + j.val + 1, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg false v + 1) / (2 * N) = i.val + j.val + 1
        have hnum : u.val + diagArg false v + 1 = 2 * N * (i.val + j.val + 1) + r2 := by
          calc u.val + diagArg false v + 1 = 2 * N * (i.val + j.val) + (α.val + β.val + 1) := by rw [hdf, hu, hv]; ring
            _ = 2 * N * (i.val + j.val + 1) + r2 := by rw [hsub2]; ring
        rw [hnum]; exact div_2N_add hN (by dsimp [r2]; omega)
      have hw0 : wTriNat N α.val β.val 0 = 0 := by simp only [wTriNat_0]; split_ifs <;> omega
      have hw1 : wTriNat N α.val β.val 1 = 0 := by simp only [wTriNat_1]; split_ifs <;> omega
      have hw23 : wTriNat N α.val β.val 2 + wTriNat N α.val β.val 3 = 4 := by
        simp only [wTriNat_2, wTriNat_3]; split_ifs <;> omega
      have sp2 : sPlus i j 2 = ⟨i.val + j.val + 1, by omega⟩ := rfl
      have sp3 : sPlus i j 3 = ⟨i.val + j.val + 1, by omega⟩ := rfl
      rw [hw0, hw1, sp2, sp3, d1, d2]
      simp only [Nat.cast_zero, zero_div, zero_mul, zero_add]
      rw [← add_mul, ← add_div, ← Nat.cast_add, hw23]; ring
  have hm_eq : ∑ t : Fin 4, ((wTriNat N α.val β.val t : ℝ) / 4) * yDiag true (sMinus i j t) =
      (yDiag true (diagSlot hN true u v 0 (by omega)) +
       yDiag true (diagSlot hN true u v 1 (by omega))) / 2 := by
    rw [Fin.sum_univ_four]
    rcases lt_trichotomy α.val β.val with hlt | heq | hgt
    · have hij : i.val + (16 - j.val) = i.val + 16 - j.val := by omega
      have hab1 : α.val + (2 * N - 1 - β.val) = α.val + 2 * N - 1 - β.val := by omega
      have hab2 : α.val + (2 * N - 1 - β.val) + 1 = α.val + 2 * N - β.val := by omega
      have d1 : diagSlot hN true u v 0 (by omega) = ⟨i.val + 16 - j.val, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg true v + 0) / (2 * N) = i.val + 16 - j.val
        have hnum : u.val + diagArg true v + 0 = 2 * N * (i.val + 16 - j.val) + (α.val + 2 * N - 1 - β.val) := by
          calc u.val + diagArg true v + 0 = 2 * N * (i.val + (16 - j.val)) + (α.val + (2 * N - 1 - β.val)) := by rw [hu, hw]; ring
            _ = 2 * N * (i.val + 16 - j.val) + (α.val + 2 * N - 1 - β.val) := by rw [hij, hab1]
        rw [hnum]; exact div_2N_add hN (by omega)
      have d2 : diagSlot hN true u v 1 (by omega) = ⟨i.val + 16 - j.val, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg true v + 1) / (2 * N) = i.val + 16 - j.val
        have hnum : u.val + diagArg true v + 1 = 2 * N * (i.val + 16 - j.val) + (α.val + 2 * N - β.val) := by
          calc u.val + diagArg true v + 1 = 2 * N * (i.val + (16 - j.val)) + (α.val + (2 * N - 1 - β.val) + 1) := by rw [hu, hw]; ring
            _ = 2 * N * (i.val + 16 - j.val) + (α.val + 2 * N - β.val) := by rw [hij, hab2]
        rw [hnum]; exact div_2N_add hN (by omega)
      have hw03 : wTriNat N α.val β.val 0 + wTriNat N α.val β.val 3 = 4 := by
        simp only [wTriNat_0, wTriNat_3]; split_ifs <;> omega
      have hw1 : wTriNat N α.val β.val 1 = 0 := by simp only [wTriNat_1]; split_ifs <;> omega
      have hw2 : wTriNat N α.val β.val 2 = 0 := by simp only [wTriNat_2]; split_ifs <;> omega
      have sm0 : sMinus i j 0 = ⟨i.val + 16 - j.val, by omega⟩ := rfl
      have sm3 : sMinus i j 3 = ⟨i.val + 16 - j.val, by omega⟩ := rfl
      rw [sm0, sm3, hw1, hw2, d1, d2]
      simp only [Nat.cast_zero, zero_div, zero_mul, add_zero]
      rw [← add_mul, ← add_div, ← Nat.cast_add, hw03]; ring
    · have hij1 : i.val + (16 - j.val) = i.val + 16 - j.val := by omega
      have hij2 : i.val + (16 - j.val) + 1 = i.val + 17 - j.val := by omega
      have hab1 : α.val + (2 * N - 1 - β.val) = 2 * N - 1 := by omega
      have hab2 : α.val + (2 * N - 1 - β.val) + 1 = 2 * N := by omega
      have d1 : diagSlot hN true u v 0 (by omega) = ⟨i.val + 16 - j.val, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg true v + 0) / (2 * N) = i.val + 16 - j.val
        have hnum : u.val + diagArg true v + 0 = 2 * N * (i.val + 16 - j.val) + (2 * N - 1) := by
          calc u.val + diagArg true v + 0 = 2 * N * (i.val + (16 - j.val)) + (α.val + (2 * N - 1 - β.val)) := by rw [hu, hw]; ring
            _ = 2 * N * (i.val + 16 - j.val) + (2 * N - 1) := by rw [hij1, hab1]
        rw [hnum]; exact div_2N_add hN (by omega)
      have d2 : diagSlot hN true u v 1 (by omega) = ⟨i.val + 17 - j.val, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg true v + 1) / (2 * N) = i.val + 17 - j.val
        have hnum : u.val + diagArg true v + 1 = 2 * N * (i.val + 17 - j.val) + 0 := by
          calc u.val + diagArg true v + 1 = 2 * N * (i.val + (16 - j.val)) + (α.val + (2 * N - 1 - β.val) + 1) := by rw [hu, hw]; ring
            _ = 2 * N * (i.val + (16 - j.val) + 1) + 0 := by rw [hab2]; ring
            _ = 2 * N * (i.val + 17 - j.val) + 0 := by rw [hij2]
        rw [hnum]; exact div_2N_add hN (by omega)
      have hw03 : wTriNat N α.val β.val 0 + wTriNat N α.val β.val 3 = 2 := by
        simp only [wTriNat_0, wTriNat_3]; split_ifs <;> omega
      have hw12 : wTriNat N α.val β.val 1 + wTriNat N α.val β.val 2 = 2 := by
        simp only [wTriNat_1, wTriNat_2]; split_ifs <;> omega
      have sm0 : sMinus i j 0 = ⟨i.val + 16 - j.val, by omega⟩ := rfl
      have sm1 : sMinus i j 1 = ⟨i.val + 17 - j.val, by omega⟩ := rfl
      have sm2 : sMinus i j 2 = ⟨i.val + 17 - j.val, by omega⟩ := rfl
      have sm3 : sMinus i j 3 = ⟨i.val + 16 - j.val, by omega⟩ := rfl
      rw [sm0, sm1, sm2, sm3, d1, d2]
      have hg1 : ((wTriNat N α.val β.val 0 : ℝ) / 4) * yDiag true ⟨i.val + 16 - j.val, by omega⟩ +
          ((wTriNat N α.val β.val 3 : ℝ) / 4) * yDiag true ⟨i.val + 16 - j.val, by omega⟩ =
          (2 / 4 : ℝ) * yDiag true ⟨i.val + 16 - j.val, by omega⟩ := by
        rw [← add_mul, ← add_div, ← Nat.cast_add, hw03]; norm_num
      have hg2 : ((wTriNat N α.val β.val 1 : ℝ) / 4) * yDiag true ⟨i.val + 17 - j.val, by omega⟩ +
          ((wTriNat N α.val β.val 2 : ℝ) / 4) * yDiag true ⟨i.val + 17 - j.val, by omega⟩ =
          (2 / 4 : ℝ) * yDiag true ⟨i.val + 17 - j.val, by omega⟩ := by
        rw [← add_mul, ← add_div, ← Nat.cast_add, hw12]; norm_num
      linarith [hg1, hg2]
    · have hij : i.val + (16 - j.val) + 1 = i.val + 17 - j.val := by omega
      have hab1 : α.val + (2 * N - 1 - β.val) = 2 * N + (α.val - 1 - β.val) := by omega
      have hab2 : α.val + (2 * N - 1 - β.val) + 1 = 2 * N + (α.val - β.val) := by omega
      have d1 : diagSlot hN true u v 0 (by omega) = ⟨i.val + 17 - j.val, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg true v + 0) / (2 * N) = i.val + 17 - j.val
        have hnum : u.val + diagArg true v + 0 = 2 * N * (i.val + 17 - j.val) + (α.val - 1 - β.val) := by
          calc u.val + diagArg true v + 0 = 2 * N * (i.val + (16 - j.val)) + (α.val + (2 * N - 1 - β.val)) := by rw [hu, hw]; ring
            _ = 2 * N * (i.val + (16 - j.val) + 1) + (α.val - 1 - β.val) := by rw [hab1]; ring
            _ = 2 * N * (i.val + 17 - j.val) + (α.val - 1 - β.val) := by rw [hij]
        rw [hnum]; exact div_2N_add hN (by omega)
      have d2 : diagSlot hN true u v 1 (by omega) = ⟨i.val + 17 - j.val, by omega⟩ := by
        apply Fin.ext; change (u.val + diagArg true v + 1) / (2 * N) = i.val + 17 - j.val
        have hnum : u.val + diagArg true v + 1 = 2 * N * (i.val + 17 - j.val) + (α.val - β.val) := by
          calc u.val + diagArg true v + 1 = 2 * N * (i.val + (16 - j.val)) + (α.val + (2 * N - 1 - β.val) + 1) := by rw [hu, hw]; ring
            _ = 2 * N * (i.val + (16 - j.val) + 1) + (α.val - β.val) := by rw [hab2]; ring
            _ = 2 * N * (i.val + 17 - j.val) + (α.val - β.val) := by rw [hij]
        rw [hnum]; exact div_2N_add hN (by omega)
      have hw0 : wTriNat N α.val β.val 0 = 0 := by simp only [wTriNat_0]; split_ifs <;> omega
      have hw3 : wTriNat N α.val β.val 3 = 0 := by simp only [wTriNat_3]; split_ifs <;> omega
      have hw12 : wTriNat N α.val β.val 1 + wTriNat N α.val β.val 2 = 4 := by
        simp only [wTriNat_1, wTriNat_2]; split_ifs <;> omega
      have sm1 : sMinus i j 1 = ⟨i.val + 17 - j.val, by omega⟩ := rfl
      have sm2 : sMinus i j 2 = ⟨i.val + 17 - j.val, by omega⟩ := rfl
      rw [hw0, hw3, sm1, sm2, d1, d2]
      simp only [Nat.cast_zero, zero_div, zero_mul, zero_add, add_zero]
      rw [← add_mul, ← add_div, ← Nat.cast_add, hw12]; ring
  have hL_expand : ∑ t : Fin 4, ((wTriNat N α.val β.val t : ℝ) / 4) * LCell i j t =
      (yRow i + yCol j + Real.log 1156) * (∑ t : Fin 4, (wTriNat N α.val β.val t : ℝ) / 4) +
      (∑ t : Fin 4, ((wTriNat N α.val β.val t : ℝ) / 4) * yDiag false (sPlus i j t)) +
      (∑ t : Fin 4, ((wTriNat N α.val β.val t : ℝ) / 4) * yDiag true (sMinus i j t)) := by
    simp only [LCell]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => by ring
  rw [hL_expand, hsum_w, hp_eq, hm_eq]
  unfold LDiag
  linarith [hlog]

end SimkinUpper

set_option maxHeartbeats 800000 in
theorem OMA.solution : OMA.R_Green97_green_97_variants_simkin_R2.H2 := by
  refine ⟨-194003 / 100000, by norm_num, ?_⟩
  rintro r ⟨N, hN, A, hA0, hrow, hcol, hd0, rfl⟩
  let f := fun x : ℝ ↦ x * Real.log x
  let d := fun (b : Bool) (k : ℕ) ↦ 1 - (∑ i : Fin N, ∑ j : Fin N,
    if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  let B (u v : Fin (34 * N)) : ℝ := A ⟨u.val / 34, by omega⟩ ⟨v.val / 34, by omega⟩
  have hB0 (u v : Fin (34 * N)) : 0 ≤ B u v := hA0 _ _
  have hcell_eq : (∑ p : Fin N, ∑ q : Fin N, f (A p q)) / (N : ℝ) ^ 2 =
      (∑ u : Fin (34 * N), ∑ v : Fin (34 * N), f (B u v)) / (1156 * (N : ℝ) ^ 2) := by
    have hsum : ∑ u : Fin (34 * N), ∑ v : Fin (34 * N), f (B u v) =
        1156 * ∑ p : Fin N, ∑ q : Fin N, f (A p q) := by
      rw [← Equiv.sum_comp (SimkinUpper.splitOrig hN).symm, Fintype.sum_prod_type]
      simp_rw [← Equiv.sum_comp (SimkinUpper.splitOrig hN).symm, Fintype.sum_prod_type]
      have hinner : ∀ p : Fin N, ∑ a1 : Fin 34, ∑ q : Fin N, ∑ a2 : Fin 34,
          f (B ((SimkinUpper.splitOrig hN).symm (p, a1)) ((SimkinUpper.splitOrig hN).symm (q, a2))) =
          1156 * ∑ q : Fin N, f (A p q) := by
        intro p
        have heval : ∀ (a1 : Fin 34) (q : Fin N) (a2 : Fin 34),
            B ((SimkinUpper.splitOrig hN).symm (p, a1)) ((SimkinUpper.splitOrig hN).symm (q, a2)) = A p q := by
          intro a1 q a2
          dsimp [B, SimkinUpper.splitOrig]
          congr 1 <;> ext <;> dsimp <;> omega
        simp_rw [heval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum]; ring
      simp_rw [hinner, ← Finset.mul_sum]
    rw [hsum]; field_simp
  let iOf (u : Fin (34 * N)) : Fin 17 := ⟨u.val / (2 * N), by nlinarith [u.isLt, Nat.div_mul_le_self u.val (2 * N)]⟩
  let αOf (u : Fin (34 * N)) : Fin (2 * N) := ⟨u.val % (2 * N), Nat.mod_lt _ (by omega)⟩
  let cellCoeff (u v : Fin (34 * N)) : ℝ :=
    ∑ t : Fin 4, ((SimkinUpper.wTriNat N (αOf u).val (αOf v).val t : ℝ) / 4) * SimkinUpper.LCell (iOf u) (iOf v) t
  let cellExp (u v : Fin (34 * N)) : ℝ :=
    ∑ t : Fin 4, ((SimkinUpper.wTriNat N (αOf u).val (αOf v).val t : ℝ) / 4) * Real.exp (SimkinUpper.LCell (iOf u) (iOf v) t - 1)
  have hcell_lo : ∑ u : Fin (34 * N), ∑ v : Fin (34 * N), (cellCoeff u v * B u v - cellExp u v) ≤
      ∑ u : Fin (34 * N), ∑ v : Fin (34 * N), f (B u v) := by
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
    have hw1 : ∑ t : Fin 4, ((SimkinUpper.wTriNat N (αOf u).val (αOf v).val t : ℝ) / 4) = 1 := by
      rw [← Finset.sum_div, ← Nat.cast_sum, SimkinUpper.wTriNat_sum_four hN (αOf u) (αOf v)]; norm_num
    have hf1 : f (B u v) = ∑ t : Fin 4, ((SimkinUpper.wTriNat N (αOf u).val (αOf v).val t : ℝ) / 4) * f (B u v) := by
      rw [← Finset.sum_mul, hw1, one_mul]
    rw [hf1]
    dsimp [cellCoeff, cellExp]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    have hfy := SimkinUpper.fenchel_log (hB0 u v) (c := SimkinUpper.LCell (iOf u) (iOf v) t)
    have hwnn : (0 : ℝ) ≤ (SimkinUpper.wTriNat N (αOf u).val (αOf v).val t : ℝ) / 4 := by positivity
    have hm := mul_le_mul_of_nonneg_left hfy hwnn
    linarith
  have hcellExp_sum : (∑ u : Fin (34 * N), ∑ v : Fin (34 * N), cellExp u v) / (1156 * (N : ℝ) ^ 2) =
      ∑ i : Fin 17, ∑ j : Fin 17, ∑ t : Fin 4, Real.exp (SimkinUpper.LCell i j t - 1) / 1156 := by
    have hsum : ∑ u : Fin (34 * N), ∑ v : Fin (34 * N), cellExp u v =
        (N : ℝ) ^ 2 * ∑ i : Fin 17, ∑ j : Fin 17, ∑ t : Fin 4, Real.exp (SimkinUpper.LCell i j t - 1) := by
      rw [← Equiv.sum_comp (SimkinUpper.splitCoarse hN).symm, Fintype.sum_prod_type]
      simp_rw [← Equiv.sum_comp (SimkinUpper.splitCoarse hN).symm, Fintype.sum_prod_type]
      have heval : ∀ (i : Fin 17) (a : Fin (2 * N)), iOf ((SimkinUpper.splitCoarse hN).symm (i, a)) = i ∧
          αOf ((SimkinUpper.splitCoarse hN).symm (i, a)) = a := by
        intro i a
        exact Prod.mk.inj ((SimkinUpper.splitCoarse hN).right_inv (i, a))
      have hi_step : ∀ i : Fin 17, ∑ a : Fin (2 * N), ∑ j : Fin 17, ∑ b : Fin (2 * N),
          cellExp ((SimkinUpper.splitCoarse hN).symm (i, a)) ((SimkinUpper.splitCoarse hN).symm (j, b)) =
          (N : ℝ) ^ 2 * ∑ j : Fin 17, ∑ t : Fin 4, Real.exp (SimkinUpper.LCell i j t - 1) := by
        intro i
        rw [Finset.sum_comm]
        have hj_step : ∀ j : Fin 17, ∑ a : Fin (2 * N), ∑ b : Fin (2 * N),
            cellExp ((SimkinUpper.splitCoarse hN).symm (i, a)) ((SimkinUpper.splitCoarse hN).symm (j, b)) =
            (N : ℝ) ^ 2 * ∑ t : Fin 4, Real.exp (SimkinUpper.LCell i j t - 1) := by
          intro j
          have hce : ∀ (a b : Fin (2 * N)), cellExp ((SimkinUpper.splitCoarse hN).symm (i, a)) ((SimkinUpper.splitCoarse hN).symm (j, b)) =
              ∑ t : Fin 4, ((SimkinUpper.wTriNat N a.val b.val t : ℝ) / 4) * Real.exp (SimkinUpper.LCell i j t - 1) := by
            intro a b
            dsimp [cellExp]
            rw [(heval i a).1, (heval i a).2, (heval j b).1, (heval j b).2]
          simp_rw [hce]
          conv_lhs =>
            enter [2, a]
            rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          simp_rw [← Finset.sum_mul, ← Finset.sum_div, ← Nat.cast_sum, SimkinUpper.wTriNat_block_sum hN t]
          push_cast; ring
        simp_rw [hj_step, ← Finset.mul_sum]
      simp_rw [hi_step, ← Finset.mul_sum]
    rw [hsum]
    calc ((N : ℝ) ^ 2 * ∑ i : Fin 17, ∑ j : Fin 17, ∑ t : Fin 4, Real.exp (SimkinUpper.LCell i j t - 1)) / (1156 * (N : ℝ) ^ 2)
      _ = (∑ i : Fin 17, ∑ j : Fin 17, ∑ t : Fin 4, Real.exp (SimkinUpper.LCell i j t - 1)) / 1156 := by field_simp
      _ = _ := by simp_rw [Finset.sum_div]
  have hdiag_lo : ∀ b : Bool,
      (1 / 17 : ℝ) * (∑ s : Fin 34, SimkinUpper.LDiag b s) -
      (∑ u : Fin (34 * N), ∑ v : Fin (34 * N),
        ((SimkinUpper.LDiag b (SimkinUpper.diagSlot hN b u v 0 (by omega)) +
          SimkinUpper.LDiag b (SimkinUpper.diagSlot hN b u v 1 (by omega))) / 2) * B u v) / (1156 * (N : ℝ) ^ 2) -
      (∑ s : Fin 34, Real.exp (SimkinUpper.LDiag b s - 1) / 17) ≤
      (∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1))) / N := by
    intro b
    let gNat (m : ℕ) : ℝ :=
      if hm : m < 68 * N then SimkinUpper.LDiag b ⟨m / (2 * N), by nlinarith [hm, Nat.div_mul_le_self m (2 * N)]⟩ else 0
    have hstep1 : ∑ k : Fin (2 * N), ∑ r : Fin 34, (1 / 34 : ℝ) *
        (gNat (34 * k.val + r.val) * (((67 - 2 * (r.val : ℝ)) / 68) * d b k.val + ((2 * (r.val : ℝ) + 1) / 68) * d b (k.val + 1)) -
         Real.exp (gNat (34 * k.val + r.val) - 1)) ≤
        ∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hk0 : 0 ≤ d b k.val := hd0 b ⟨k.val, by omega⟩
      have hk1 : 0 ≤ d b (k.val + 1) := hd0 b ⟨k.val + 1, by omega⟩
      exact SimkinUpper.integral_seg_fenchel hk0 hk1 (fun r => gNat (34 * k.val + r.val))
    have hdiv1 := div_le_div_of_nonneg_right hstep1 hN_pos.le
    refine le_trans ?_ hdiv1
    have hexp_part : (∑ k : Fin (2 * N), ∑ r : Fin 34, (1 / 34 : ℝ) * Real.exp (gNat (34 * k.val + r.val) - 1)) / N =
        ∑ s : Fin 34, Real.exp (SimkinUpper.LDiag b s - 1) / 17 := by
      have h68 : ∑ k : Fin (2 * N), ∑ r : Fin 34, Real.exp (gNat (34 * k.val + r.val) - 1) =
          (2 * (N : ℝ)) * ∑ s : Fin 34, Real.exp (SimkinUpper.LDiag b s - 1) := by
        rw [← Fintype.sum_prod_type', ← Equiv.sum_comp (SimkinUpper.split68Orig hN),
            ← Equiv.sum_comp (SimkinUpper.split68Coarse hN).symm, Fintype.sum_prod_type]
        have hev : ∀ (s : Fin 34) (a : Fin (2 * N)),
            gNat (34 * ((SimkinUpper.split68Orig hN) ((SimkinUpper.split68Coarse hN).symm (s, a))).1.val +
              ((SimkinUpper.split68Orig hN) ((SimkinUpper.split68Coarse hN).symm (s, a))).2.val) = SimkinUpper.LDiag b s := by
          intro s a
          let m := (SimkinUpper.split68Coarse hN).symm (s, a)
          change gNat (34 * (m.val / 34) + m.val % 34) = _
          rw [Nat.div_add_mod m.val 34]
          dsimp [gNat]
          rw [dif_pos m.isLt]
          exact congrArg (SimkinUpper.LDiag b) (Prod.mk.inj ((SimkinUpper.split68Coarse hN).right_inv (s, a))).1
        simp_rw [hev, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
        push_cast; rfl
      simp_rw [← Finset.mul_sum]
      rw [h68]
      calc ((1 / 34 : ℝ) * (2 * (N : ℝ) * ∑ s : Fin 34, Real.exp (SimkinUpper.LDiag b s - 1))) / N
        _ = (∑ s : Fin 34, Real.exp (SimkinUpper.LDiag b s - 1)) / 17 := by field_simp; ring
        _ = _ := by simp_rw [Finset.sum_div]
    have hconst_part : (∑ k : Fin (2 * N), ∑ r : Fin 34, (1 / 34 : ℝ) * gNat (34 * k.val + r.val)) / N =
        (1 / 17 : ℝ) * ∑ s : Fin 34, SimkinUpper.LDiag b s := by
      have h68 : ∑ k : Fin (2 * N), ∑ r : Fin 34, gNat (34 * k.val + r.val) =
          (2 * (N : ℝ)) * ∑ s : Fin 34, SimkinUpper.LDiag b s := by
        rw [← Fintype.sum_prod_type', ← Equiv.sum_comp (SimkinUpper.split68Orig hN),
            ← Equiv.sum_comp (SimkinUpper.split68Coarse hN).symm, Fintype.sum_prod_type]
        have hev : ∀ (s : Fin 34) (a : Fin (2 * N)),
            gNat (34 * ((SimkinUpper.split68Orig hN) ((SimkinUpper.split68Coarse hN).symm (s, a))).1.val +
              ((SimkinUpper.split68Orig hN) ((SimkinUpper.split68Coarse hN).symm (s, a))).2.val) = SimkinUpper.LDiag b s := by
          intro s a
          let m := (SimkinUpper.split68Coarse hN).symm (s, a)
          change gNat (34 * (m.val / 34) + m.val % 34) = _
          rw [Nat.div_add_mod m.val 34]
          dsimp [gNat]
          rw [dif_pos m.isLt]
          exact congrArg (SimkinUpper.LDiag b) (Prod.mk.inj ((SimkinUpper.split68Coarse hN).right_inv (s, a))).1
        simp_rw [hev, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
        push_cast; rfl
      simp_rw [← Finset.mul_sum]
      rw [h68]; field_simp; ring
    have hA_part : (∑ k : Fin (2 * N), ∑ r : Fin 34, (1 / 34 : ℝ) *
        (gNat (34 * k.val + r.val) * (((67 - 2 * (r.val : ℝ)) / 68) * (1 - d b k.val) +
          ((2 * (r.val : ℝ) + 1) / 68) * (1 - d b (k.val + 1))))) / N =
        (∑ u : Fin (34 * N), ∑ v : Fin (34 * N),
          ((SimkinUpper.LDiag b (SimkinUpper.diagSlot hN b u v 0 (by omega)) +
            SimkinUpper.LDiag b (SimkinUpper.diagSlot hN b u v 1 (by omega))) / 2) * B u v) / (1156 * (N : ℝ) ^ 2) := by
      have hd_sub : ∀ m : ℕ, 1 - d b m = (∑ p : Fin N, ∑ q : Fin N,
          if p.val + (if b then q.rev else q).val + 1 = m then A p q else 0) / N := by
        intro m
        dsimp [d]
        have hswap : ∀ p : Fin N, (∑ j : Fin N, if p.val + j.val + 1 = m then A p (if b then j.rev else j) else 0) =
            ∑ q : Fin N, if p.val + (if b then q.rev else q).val + 1 = m then A p q else 0 := by
          intro p
          cases b
          · rfl
          · rw [← Equiv.sum_comp Fin.revPerm]
            refine Finset.sum_congr rfl fun q _ => ?_
            simp [Fin.revPerm]
        simp_rw [hswap]; ring
      simp_rw [hd_sub]
      have h_pq_outer : ∑ k : Fin (2 * N), ∑ r : Fin 34, (1 / 34 : ℝ) *
          (gNat (34 * k.val + r.val) * (((67 - 2 * (r.val : ℝ)) / 68) * ((∑ p : Fin N, ∑ q : Fin N,
              if p.val + (if b then q.rev else q).val + 1 = k.val then A p q else 0) / N) +
            ((2 * (r.val : ℝ) + 1) / 68) * ((∑ p : Fin N, ∑ q : Fin N,
              if p.val + (if b then q.rev else q).val + 1 = k.val + 1 then A p q else 0) / N))) =
          (1 / (1156 * (N : ℝ))) * ∑ p : Fin N, ∑ q : Fin N, A p q *
            (∑ a1 : Fin 34, ∑ a2 : Fin 34,
              (gNat (34 * (p.val + (if b then q.rev else q).val) + a1.val + a2.val) +
               gNat (34 * (p.val + (if b then q.rev else q).val) + a1.val + a2.val + 1)) / 2) := by
        have hterm_eq : ∀ (k : Fin (2 * N)) (r : Fin 34),
            (1 / 34 : ℝ) * (gNat (34 * k.val + r.val) * (((67 - 2 * (r.val : ℝ)) / 68) * ((∑ p : Fin N, ∑ q : Fin N,
                if p.val + (if b then q.rev else q).val + 1 = k.val then A p q else 0) / N) +
              ((2 * (r.val : ℝ) + 1) / 68) * ((∑ p : Fin N, ∑ q : Fin N,
                if p.val + (if b then q.rev else q).val + 1 = k.val + 1 then A p q else 0) / N))) =
            ∑ p : Fin N, ∑ q : Fin N, (1 / (1156 * (N : ℝ))) * A p q *
              ((if p.val + (if b then q.rev else q).val + 1 = k.val then ((67 - 2 * (r.val : ℝ)) / 2) * gNat (34 * k.val + r.val) else 0) +
               (if p.val + (if b then q.rev else q).val = k.val then ((2 * (r.val : ℝ) + 1) / 2) * gNat (34 * k.val + r.val) else 0)) := by
          intro k r
          simp_rw [Finset.sum_div, Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          simp_rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          have hcond : (p.val + (if b then q.rev else q).val + 1 = k.val + 1) ↔
              (p.val + (if b then q.rev else q).val = k.val) := by omega
          simp only [hcond]
          split_ifs <;> ring
        simp_rw [hterm_eq]
        conv_lhs => enter [2, k]; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        conv_lhs => enter [2, p, 2, k]; rw [Finset.sum_comm]
        conv_lhs => enter [2, p]; rw [Finset.sum_comm]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp_rw [← Finset.mul_sum]
        rw [← mul_assoc]
        congr 1
        let m0 := p.val + (if b then q.rev else q).val
        have hm0_lt : m0 + 1 < 2 * N := by
          have hp := p.isLt
          have hq : (if b then q.rev else q).val < N := (if b then q.rev else q).isLt
          dsimp [m0]; omega
        let k0 : Fin (2 * N) := ⟨m0, by omega⟩
        let k1 : Fin (2 * N) := ⟨m0 + 1, hm0_lt⟩
        rw [Finset.sum_comm]
        have hr_eval : ∀ r : Fin 34,
            ∑ k : Fin (2 * N), ((if m0 + 1 = k.val then ((67 - 2 * (r.val : ℝ)) / 2) * gNat (34 * k.val + r.val) else 0) +
              (if m0 = k.val then ((2 * (r.val : ℝ) + 1) / 2) * gNat (34 * k.val + r.val) else 0)) =
            ((2 * (r.val : ℝ) + 1) / 2) * gNat (34 * m0 + r.val) +
            ((67 - 2 * (r.val : ℝ)) / 2) * gNat (34 * m0 + (34 + r.val)) := by
          intro r
          rw [Finset.sum_add_distrib]
          have hs1 : ∑ k : Fin (2 * N), (if m0 + 1 = k.val then ((67 - 2 * (r.val : ℝ)) / 2) * gNat (34 * k.val + r.val) else 0) =
              ((67 - 2 * (r.val : ℝ)) / 2) * gNat (34 * (m0 + 1) + r.val) := by
            have hcongr : ∀ k : Fin (2 * N), (if m0 + 1 = k.val then ((67 - 2 * (r.val : ℝ)) / 2) * gNat (34 * k.val + r.val) else 0) =
                if k = k1 then ((67 - 2 * (r.val : ℝ)) / 2) * gNat (34 * k.val + r.val) else 0 := by
              intro k; by_cases hk : k = k1
              · subst hk; simp [k1]
              · have hne : m0 + 1 ≠ k.val := fun h => hk (Fin.ext h.symm)
                simp [hk, hne]
            simp_rw [hcongr, Finset.sum_ite_eq', Finset.mem_univ, ite_true]; rfl
          have hs0 : ∑ k : Fin (2 * N), (if m0 = k.val then ((2 * (r.val : ℝ) + 1) / 2) * gNat (34 * k.val + r.val) else 0) =
              ((2 * (r.val : ℝ) + 1) / 2) * gNat (34 * m0 + r.val) := by
            have hcongr : ∀ k : Fin (2 * N), (if m0 = k.val then ((2 * (r.val : ℝ) + 1) / 2) * gNat (34 * k.val + r.val) else 0) =
                if k = k0 then ((2 * (r.val : ℝ) + 1) / 2) * gNat (34 * k.val + r.val) else 0 := by
              intro k; by_cases hk : k = k0
              · subst hk; simp [k0]
              · have hne : m0 ≠ k.val := fun h => hk (Fin.ext h.symm)
                simp [hk, hne]
            simp_rw [hcongr, Finset.sum_ite_eq', Finset.mem_univ, ite_true]; rfl
          rw [hs1, hs0, show 34 * (m0 + 1) + r.val = 34 * m0 + (34 + r.val) by ring, add_comm]
        rw [Finset.sum_congr rfl fun r _ => hr_eval r]
        have hbr := (SimkinUpper.fin34_diag_bridge (fun t => gNat (34 * m0 + t))).symm
        simpa only [add_assoc] using hbr
      rw [h_pq_outer]
      have hB_reindex : ∑ u : Fin (34 * N), ∑ v : Fin (34 * N),
          ((SimkinUpper.LDiag b (SimkinUpper.diagSlot hN b u v 0 (by omega)) +
            SimkinUpper.LDiag b (SimkinUpper.diagSlot hN b u v 1 (by omega))) / 2) * B u v =
          ∑ p : Fin N, ∑ q : Fin N, A p q *
            (∑ a1 : Fin 34, ∑ a2 : Fin 34,
              (gNat (34 * (p.val + (if b then q.rev else q).val) + a1.val + a2.val) +
               gNat (34 * (p.val + (if b then q.rev else q).val) + a1.val + a2.val + 1)) / 2) := by
        rw [← Equiv.sum_comp (SimkinUpper.splitOrig hN).symm, Fintype.sum_prod_type]
        simp_rw [← Equiv.sum_comp (SimkinUpper.splitOrig hN).symm, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a1 _ => ?_
        rw [Finset.mul_sum]
        have ha2_sum : ∑ a2 : Fin 34,
            ((SimkinUpper.LDiag b (SimkinUpper.diagSlot hN b ((SimkinUpper.splitOrig hN).symm (p, a1)) ((SimkinUpper.splitOrig hN).symm (q, a2)) 0 (by omega)) +
              SimkinUpper.LDiag b (SimkinUpper.diagSlot hN b ((SimkinUpper.splitOrig hN).symm (p, a1)) ((SimkinUpper.splitOrig hN).symm (q, a2)) 1 (by omega))) / 2) *
              B ((SimkinUpper.splitOrig hN).symm (p, a1)) ((SimkinUpper.splitOrig hN).symm (q, a2)) =
            ∑ a2 : Fin 34, A p q * ((gNat (34 * (p.val + (if b then q.rev else q).val) + a1.val + a2.val) +
              gNat (34 * (p.val + (if b then q.rev else q).val) + a1.val + a2.val + 1)) / 2) := by
          have hBpq : ∀ a2 : Fin 34, B ((SimkinUpper.splitOrig hN).symm (p, a1)) ((SimkinUpper.splitOrig hN).symm (q, a2)) = A p q := by
            intro a2; dsimp [B, SimkinUpper.splitOrig]; congr 1 <;> ext <;> dsimp <;> omega
          simp_rw [hBpq]
          cases b
          · refine Finset.sum_congr rfl fun a2 _ => ?_
            let m := 34 * (p.val + q.val) + a1.val + a2.val
            have hm_eq0 : ((SimkinUpper.splitOrig hN).symm (p, a1)).val +
                SimkinUpper.diagArg false ((SimkinUpper.splitOrig hN).symm (q, a2)) + 0 = m := by
              dsimp [SimkinUpper.splitOrig, SimkinUpper.diagArg, m]; ring
            have hm_eq1 : ((SimkinUpper.splitOrig hN).symm (p, a1)).val +
                SimkinUpper.diagArg false ((SimkinUpper.splitOrig hN).symm (q, a2)) + 1 = m + 1 := by
              dsimp [SimkinUpper.splitOrig, SimkinUpper.diagArg, m]; ring
            have hlt1 : m < 68 * N := by
              have := p.isLt; have := q.isLt; have := a1.isLt; have := a2.isLt; dsimp [m]; omega
            have hlt2 : m + 1 < 68 * N := by
              have := p.isLt; have := q.isLt; have := a1.isLt; have := a2.isLt; dsimp [m]; omega
            have hs0 : SimkinUpper.diagSlot hN false ((SimkinUpper.splitOrig hN).symm (p, a1)) ((SimkinUpper.splitOrig hN).symm (q, a2)) 0 (by omega) =
                ⟨m / (2 * N), by nlinarith [hlt1, Nat.div_mul_le_self m (2 * N)]⟩ := Fin.ext (congrArg (· / (2 * N)) hm_eq0)
            have hs1 : SimkinUpper.diagSlot hN false ((SimkinUpper.splitOrig hN).symm (p, a1)) ((SimkinUpper.splitOrig hN).symm (q, a2)) 1 (by omega) =
                ⟨(m + 1) / (2 * N), by nlinarith [hlt2, Nat.div_mul_le_self (m + 1) (2 * N)]⟩ := Fin.ext (congrArg (· / (2 * N)) hm_eq1)
            dsimp [gNat]
            change ((SimkinUpper.LDiag false _ + SimkinUpper.LDiag false _) / 2) * A p q =
              A p q * (((if hm : m < 68 * N then SimkinUpper.LDiag false ⟨m / (2 * N), _⟩ else 0) +
                (if hm : m + 1 < 68 * N then SimkinUpper.LDiag false ⟨(m + 1) / (2 * N), _⟩ else 0)) / 2)
            rw [dif_pos hlt1, dif_pos hlt2, hs0, hs1]
            ring
          · rw [← Equiv.sum_comp Fin.revPerm]
            refine Finset.sum_congr rfl fun a2 _ => ?_
            let m := 34 * (p.val + q.rev.val) + a1.val + a2.val
            have hm_eq0 : ((SimkinUpper.splitOrig hN).symm (p, a1)).val +
                SimkinUpper.diagArg true ((SimkinUpper.splitOrig hN).symm (q, Fin.revPerm a2)) + 0 = m := by
              have hp := p.isLt; have hq := q.isLt; have ha1 := a1.isLt; have ha2 := a2.isLt
              dsimp [SimkinUpper.splitOrig, SimkinUpper.diagArg, Fin.revPerm, Fin.rev, m]
              have hqrev : (N - (q.val + 1)) + q.val + 1 = N := by omega
              have harev : (34 - (a2.val + 1)) + a2.val + 1 = 34 := by omega
              omega
            have hm_eq1 : ((SimkinUpper.splitOrig hN).symm (p, a1)).val +
                SimkinUpper.diagArg true ((SimkinUpper.splitOrig hN).symm (q, Fin.revPerm a2)) + 1 = m + 1 := by omega
            have hlt1 : m < 68 * N := by
              have := p.isLt; have := q.rev.isLt; have := a1.isLt; have := a2.isLt; dsimp [m]; omega
            have hlt2 : m + 1 < 68 * N := by
              have := p.isLt; have := q.rev.isLt; have := a1.isLt; have := a2.isLt; dsimp [m]; omega
            have hs0 : SimkinUpper.diagSlot hN true ((SimkinUpper.splitOrig hN).symm (p, a1)) ((SimkinUpper.splitOrig hN).symm (q, Fin.revPerm a2)) 0 (by omega) =
                ⟨m / (2 * N), by nlinarith [hlt1, Nat.div_mul_le_self m (2 * N)]⟩ := Fin.ext (congrArg (· / (2 * N)) hm_eq0)
            have hs1 : SimkinUpper.diagSlot hN true ((SimkinUpper.splitOrig hN).symm (p, a1)) ((SimkinUpper.splitOrig hN).symm (q, Fin.revPerm a2)) 1 (by omega) =
                ⟨(m + 1) / (2 * N), by nlinarith [hlt2, Nat.div_mul_le_self (m + 1) (2 * N)]⟩ := Fin.ext (congrArg (· / (2 * N)) hm_eq1)
            dsimp [gNat]
            change ((SimkinUpper.LDiag true _ + SimkinUpper.LDiag true _) / 2) * A p q =
              A p q * (((if hm : m < 68 * N then SimkinUpper.LDiag true ⟨m / (2 * N), _⟩ else 0) +
                (if hm : m + 1 < 68 * N then SimkinUpper.LDiag true ⟨(m + 1) / (2 * N), _⟩ else 0)) / 2)
            rw [dif_pos hlt1, dif_pos hlt2, hs0, hs1]
            ring
        exact ha2_sum
      rw [hB_reindex]
      field_simp
    have halg : (∑ k : Fin (2 * N), ∑ r : Fin 34, (1 / 34 : ℝ) *
        (gNat (34 * k.val + r.val) * (((67 - 2 * (r.val : ℝ)) / 68) * d b k.val + ((2 * (r.val : ℝ) + 1) / 68) * d b (k.val + 1)) -
         Real.exp (gNat (34 * k.val + r.val) - 1))) / N =
        (∑ k : Fin (2 * N), ∑ r : Fin 34, (1 / 34 : ℝ) * gNat (34 * k.val + r.val)) / N -
        (∑ k : Fin (2 * N), ∑ r : Fin 34, (1 / 34 : ℝ) *
          (gNat (34 * k.val + r.val) * (((67 - 2 * (r.val : ℝ)) / 68) * (1 - d b k.val) +
            ((2 * (r.val : ℝ) + 1) / 68) * (1 - d b (k.val + 1))))) / N -
        (∑ k : Fin (2 * N), ∑ r : Fin 34, (1 / 34 : ℝ) * Real.exp (gNat (34 * k.val + r.val) - 1)) / N := by
      rw [← sub_div, ← sub_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => by ring
    rw [halg, hconst_part, hA_part, hexp_part]
  have hd_false := hdiag_lo false
  have hd_true := hdiag_lo true
  have hrow_sum : (∑ u : Fin (34 * N), ∑ v : Fin (34 * N), SimkinUpper.yRow (iOf u) * B u v) / (1156 * (N : ℝ) ^ 2) =
      (1 / 17 : ℝ) * ∑ i : Fin 17, SimkinUpper.yRow i := by
    have hinner : ∀ u : Fin (34 * N), ∑ v : Fin (34 * N), SimkinUpper.yRow (iOf u) * B u v =
        34 * (N : ℝ) * SimkinUpper.yRow (iOf u) := by
      intro u
      rw [← Finset.mul_sum, ← Equiv.sum_comp (SimkinUpper.splitOrig hN).symm, Fintype.sum_prod_type]
      have hv_eq : ∀ (q : Fin N) (a2 : Fin 34), B u ((SimkinUpper.splitOrig hN).symm (q, a2)) = A ⟨u.val / 34, by omega⟩ q := by
        intro q a2; dsimp [B, SimkinUpper.splitOrig]; congr 1; ext; dsimp; omega
      simp_rw [hv_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hrow]
      ring
    simp_rw [hinner]
    rw [← Equiv.sum_comp (SimkinUpper.splitCoarse hN).symm, Fintype.sum_prod_type]
    have hi_eq : ∀ (i : Fin 17) (a : Fin (2 * N)), iOf ((SimkinUpper.splitCoarse hN).symm (i, a)) = i :=
      fun i a => (Prod.mk.inj ((SimkinUpper.splitCoarse hN).right_inv (i, a))).1
    simp_rw [hi_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    push_cast; field_simp; ring
  have hcol_sum : (∑ u : Fin (34 * N), ∑ v : Fin (34 * N), SimkinUpper.yCol (iOf v) * B u v) / (1156 * (N : ℝ) ^ 2) =
      (1 / 17 : ℝ) * ∑ j : Fin 17, SimkinUpper.yCol j := by
    rw [Finset.sum_comm]
    have hinner : ∀ v : Fin (34 * N), ∑ u : Fin (34 * N), SimkinUpper.yCol (iOf v) * B u v =
        34 * (N : ℝ) * SimkinUpper.yCol (iOf v) := by
      intro v
      rw [← Finset.mul_sum, ← Equiv.sum_comp (SimkinUpper.splitOrig hN).symm, Fintype.sum_prod_type]
      have hu_eq : ∀ (p : Fin N) (a1 : Fin 34), B ((SimkinUpper.splitOrig hN).symm (p, a1)) v = A p ⟨v.val / 34, by omega⟩ := by
        intro p a1; dsimp [B, SimkinUpper.splitOrig]; congr 1; ext; dsimp; omega
      simp_rw [hu_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hcol]
      ring
    simp_rw [hinner]
    rw [← Equiv.sum_comp (SimkinUpper.splitCoarse hN).symm, Fintype.sum_prod_type]
    have hj_eq : ∀ (j : Fin 17) (b : Fin (2 * N)), iOf ((SimkinUpper.splitCoarse hN).symm (j, b)) = j :=
      fun j b => (Prod.mk.inj ((SimkinUpper.splitCoarse hN).right_inv (j, b))).1
    simp_rw [hj_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    push_cast; field_simp; ring
  have hlog2_sum : (∑ u : Fin (34 * N), ∑ v : Fin (34 * N), (2 * Real.log 2) * B u v) / (1156 * (N : ℝ) ^ 2) =
      2 * Real.log 2 := by
    have hinner : ∀ u : Fin (34 * N), ∑ v : Fin (34 * N), (2 * Real.log 2) * B u v = 34 * (N : ℝ) * (2 * Real.log 2) := by
      intro u
      rw [← Finset.mul_sum, ← Equiv.sum_comp (SimkinUpper.splitOrig hN).symm, Fintype.sum_prod_type]
      have hv_eq : ∀ (q : Fin N) (a2 : Fin 34), B u ((SimkinUpper.splitOrig hN).symm (q, a2)) = A ⟨u.val / 34, by omega⟩ q := by
        intro q a2; dsimp [B, SimkinUpper.splitOrig]; congr 1; ext; dsimp; omega
      simp_rw [hv_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hrow]
      ring
    simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; field_simp; ring
  have hB_cancel : (∑ u : Fin (34 * N), ∑ v : Fin (34 * N), cellCoeff u v * B u v) / (1156 * (N : ℝ) ^ 2) -
      (∑ u : Fin (34 * N), ∑ v : Fin (34 * N),
        ((SimkinUpper.LDiag false (SimkinUpper.diagSlot hN false u v 0 (by omega)) +
          SimkinUpper.LDiag false (SimkinUpper.diagSlot hN false u v 1 (by omega))) / 2) * B u v) / (1156 * (N : ℝ) ^ 2) -
      (∑ u : Fin (34 * N), ∑ v : Fin (34 * N),
        ((SimkinUpper.LDiag true (SimkinUpper.diagSlot hN true u v 0 (by omega)) +
          SimkinUpper.LDiag true (SimkinUpper.diagSlot hN true u v 1 (by omega))) / 2) * B u v) / (1156 * (N : ℝ) ^ 2) =
      (1 / 17 : ℝ) * (∑ i : Fin 17, SimkinUpper.yRow i) + (1 / 17 : ℝ) * (∑ j : Fin 17, SimkinUpper.yCol j) + 2 * Real.log 2 := by
    rw [← hrow_sum, ← hcol_sum, ← hlog2_sum, ← sub_div, ← sub_div, ← add_div, ← add_div]
    congr 1
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hpw := SimkinUpper.pointwise_cancel hN u v
    dsimp [cellCoeff, iOf, αOf]
    linear_combination hpw * B u v
  have hcell_div := div_le_div_of_nonneg_right hcell_lo (by positivity : (0 : ℝ) ≤ 1156 * (N : ℝ) ^ 2)
  simp_rw [Finset.sum_sub_distrib] at hcell_div
  rw [sub_div, hcellExp_sum, ← hcell_eq] at hcell_div
  have hbool_sum : (∑ b : Bool, ∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1))) / N =
      (∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1, f ((1 - t) * d false k.val + t * d false (k.val + 1))) / N +
      (∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1, f ((1 - t) * d true k.val + t * d true (k.val + 1))) / N := by
    rw [Fintype.sum_bool, add_comm, add_div]
  have hexp_bound : (∑ i : Fin 17, ∑ j : Fin 17, ∑ t : Fin 4, Real.exp (SimkinUpper.LCell i j t - 1) / 1156) +
      (∑ s : Fin 34, Real.exp (SimkinUpper.LDiag false s - 1) / 17) +
      (∑ s : Fin 34, Real.exp (SimkinUpper.LDiag true s - 1) / 17) ≤
      (30002924 : ℝ) / 10000000 := by
    have hc : ∑ i : Fin 17, ∑ j : Fin 17, ∑ t : Fin 4, Real.exp (SimkinUpper.LCell i j t - 1) / 1156 ≤
        ∑ i : Fin 17, ∑ j : Fin 17, ∑ t : Fin 4, (SimkinUpper.ubInt (SimkinUpper.cellIdx i j t) : ℝ) / 10000000 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun t _ => SimkinUpper.exp_LCell_div i j t
    have hdf : ∑ s : Fin 34, Real.exp (SimkinUpper.LDiag false s - 1) / 17 ≤
        ∑ s : Fin 34, (SimkinUpper.ubInt (SimkinUpper.diagIdx false s) : ℝ) / 10000000 :=
      Finset.sum_le_sum fun s _ => SimkinUpper.exp_LDiag_div false s
    have hdt : ∑ s : Fin 34, Real.exp (SimkinUpper.LDiag true s - 1) / 17 ≤
        ∑ s : Fin 34, (SimkinUpper.ubInt (SimkinUpper.diagIdx true s) : ℝ) / 10000000 :=
      Finset.sum_le_sum fun s _ => SimkinUpper.exp_LDiag_div true s
    have htot := SimkinUpper.sum_ub_eq
    rw [Fintype.sum_bool, add_comm (∑ s : Fin 34, SimkinUpper.ubInt (SimkinUpper.diagIdx true s))] at htot
    have htot_cast : ((∑ i : Fin 17, ∑ j : Fin 17, ∑ t : Fin 4, (SimkinUpper.ubInt (SimkinUpper.cellIdx i j t) : ℝ) / 10000000) +
        (∑ s : Fin 34, (SimkinUpper.ubInt (SimkinUpper.diagIdx false s) : ℝ) / 10000000) +
        (∑ s : Fin 34, (SimkinUpper.ubInt (SimkinUpper.diagIdx true s) : ℝ) / 10000000)) = (30002924 : ℝ) / 10000000 := by
      simp_rw [← Finset.sum_div, ← Int.cast_sum]
      rw [← add_div, ← add_div, ← Int.cast_add, ← Int.cast_add, add_assoc, htot]
      norm_num
    linarith [hc, hdf, hdt, htot_cast]
  have hy_const : (1 / 17 : ℝ) * (∑ i : Fin 17, SimkinUpper.yRow i) +
      (1 / 17 : ℝ) * (∑ j : Fin 17, SimkinUpper.yCol j) +
      (1 / 17 : ℝ) * (∑ s : Fin 34, SimkinUpper.LDiag false s) +
      (1 / 17 : ℝ) * (∑ s : Fin 34, SimkinUpper.LDiag true s) =
      (-18324 : ℝ) / 1700 + 4 * Real.log 17 := by
    simp only [SimkinUpper.LDiag, SimkinUpper.yRow, SimkinUpper.yCol, SimkinUpper.yDiag, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Bool.false_eq_true, ↓reduceIte]
    simp_rw [← Finset.sum_div, ← Int.cast_sum]
    have hy := SimkinUpper.sum_yInt_eq
    rw [Fintype.sum_bool] at hy
    simp only [Bool.false_eq_true, ↓reduceIte] at hy
    have hyR : ((∑ i : Fin 17, SimkinUpper.yInt ⟨i.val, by omega⟩ : ℤ) : ℝ) +
        ((∑ j : Fin 17, SimkinUpper.yInt ⟨17 + j.val, by omega⟩ : ℤ) : ℝ) +
        ((∑ s : Fin 34, SimkinUpper.yInt ⟨34 + s.val, by omega⟩ : ℤ) : ℝ) +
        ((∑ s : Fin 34, SimkinUpper.yInt ⟨68 + s.val, by omega⟩ : ℤ) : ℝ) = -18324 := by
      exact_mod_cast (by linarith [hy] :
        (∑ i : Fin 17, SimkinUpper.yInt ⟨i.val, by omega⟩) +
        (∑ j : Fin 17, SimkinUpper.yInt ⟨17 + j.val, by omega⟩) +
        (∑ s : Fin 34, SimkinUpper.yInt ⟨34 + s.val, by omega⟩) +
        (∑ s : Fin 34, SimkinUpper.yInt ⟨68 + s.val, by omega⟩) = -18324)
    linarith [hyR]
  linarith [hcell_div, hd_false, hd_true, hbool_sum, hB_cancel, hexp_bound, hy_const,
            Real.log_two_gt_d9, SimkinUpper.log_seventeen_gt]

