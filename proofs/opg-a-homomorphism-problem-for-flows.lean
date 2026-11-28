import OMAStatements.S_opg_a_homomorphism_problem_for_flows

namespace OPGAHomFlowProof

open OMA.S_opg_a_homomorphism_problem_for_flows

abbrev Vec6 := Fin 6 → ZMod 2
abbrev Vec64 := Vec6 → ZMod 2

private def single1 (x : Vec6) : Vec64 := Pi.single x (1 : ZMod 2)

private lemma zmod2_neg : ∀ x : ZMod 2, -x = x := by decide

private lemma zmod2_add_self : ∀ x : ZMod 2, x + x = 0 := by decide

private lemma zmod2_sub_eq_add : ∀ x y : ZMod 2, x - y = x + y := by decide

private lemma vec_neg {α : Type} (f : α → ZMod 2) : -f = f := by
  funext i; exact zmod2_neg (f i)

private lemma vec_add_self {α : Type} (f : α → ZMod 2) : f + f = 0 := by
  funext i; exact zmod2_add_self (f i)

private lemma vec_sub_eq_add {α : Type} (f g : α → ZMod 2) : f - g = f + g := by
  funext i; exact zmod2_sub_eq_add (f i) (g i)

private lemma vec_eq_iff_add_eq_zero {α : Type} (f g : α → ZMod 2) : f = g ↔ f + g = 0 := by
  constructor
  · rintro rfl; exact vec_add_self f
  · intro h
    have := congrArg (· + g) h
    simpa [add_assoc, vec_add_self] using this

/-! ### Explicit Petersen graph (10 vertices, 15 edges: 9 tree edges 0..8 and 6 chords 9..14) -/

private def pSrc : Fin 15 → Fin 10
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 2 | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 0 | ⟨5, _⟩ => 1 | ⟨6, _⟩ => 2 | ⟨7, _⟩ => 3 | ⟨8, _⟩ => 4
  | ⟨9, _⟩ => 4
  | ⟨10, _⟩ => 5 | ⟨11, _⟩ => 7 | ⟨12, _⟩ => 9 | ⟨13, _⟩ => 6 | ⟨14, _⟩ => 8

private def pTgt : Fin 15 → Fin 10
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 2 | ⟨2, _⟩ => 3 | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 5 | ⟨5, _⟩ => 6 | ⟨6, _⟩ => 7 | ⟨7, _⟩ => 8 | ⟨8, _⟩ => 9
  | ⟨9, _⟩ => 0
  | ⟨10, _⟩ => 7 | ⟨11, _⟩ => 9 | ⟨12, _⟩ => 6 | ⟨13, _⟩ => 8 | ⟨14, _⟩ => 5

private lemma pSrc_ne_pTgt : ∀ e : Fin 15, pSrc e ≠ pTgt e := by decide

private lemma flow_iff_inc_sum_zero {α : Type} (φ : Fin 15 → (α → ZMod 2)) (v : Fin 10) :
    (∑ e ∈ Finset.univ.filter (fun e => pTgt e = v), φ e =
      ∑ e ∈ Finset.univ.filter (fun e => pSrc e = v), φ e) ↔
    ∑ e ∈ Finset.univ.filter (fun e => pTgt e = v ∨ pSrc e = v), φ e = 0 := by
  have hdisj : Disjoint (Finset.univ.filter (fun e => pTgt e = v))
      (Finset.univ.filter (fun e => pSrc e = v)) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact pSrc_ne_pTgt e (h2.trans h1.symm)
  have hunion : Finset.univ.filter (fun e => pTgt e = v ∨ pSrc e = v) =
      Finset.univ.filter (fun e => pTgt e = v) ∪ Finset.univ.filter (fun e => pSrc e = v) := by
    ext e; simp
  rw [hunion, Finset.sum_union hdisj, vec_eq_iff_add_eq_zero]

/-! ### Fundamental cycle basis of the Petersen graph (6 cycles as 15-bit masks) -/

private def basisMask : Fin 6 → ℕ
  | ⟨0, _⟩ => 527    -- edges {0, 1, 2, 3, 9}
  | ⟨1, _⟩ => 1107   -- edges {0, 1, 4, 6, 10}
  | ⟨2, _⟩ => 2380   -- edges {2, 3, 6, 8, 11}
  | ⟨3, _⟩ => 4398   -- edges {1, 2, 3, 5, 8, 12}
  | ⟨4, _⟩ => 8358   -- edges {1, 2, 5, 7, 13}
  | ⟨5, _⟩ => 16535  -- edges {0, 1, 2, 4, 7, 14}

private def pSigma (e : Fin 15) : Vec6 :=
  fun i => if (basisMask i).testBit e.val then 1 else 0

private def zEval (a : Vec6) (e : Fin 15) : ZMod 2 :=
  ∑ i : Fin 6, a i * pSigma e i

private def zMask (a : ℕ) : ℕ :=
  (if a.testBit 0 then basisMask 0 else 0) ^^^
  (if a.testBit 1 then basisMask 1 else 0) ^^^
  (if a.testBit 2 then basisMask 2 else 0) ^^^
  (if a.testBit 3 then basisMask 3 else 0) ^^^
  (if a.testBit 4 then basisMask 4 else 0) ^^^
  (if a.testBit 5 then basisMask 5 else 0)

private def bitVec (a : ℕ) : Vec6 :=
  fun i => if a.testBit i.val then 1 else 0

private def vecToNat (a : Vec6) : ℕ :=
  (a 0).val + 2 * ((a 1).val + 2 * ((a 2).val + 2 * ((a 3).val + 2 * ((a 4).val + 2 * (a 5).val))))

private lemma vecToNat_lt (a : Vec6) : vecToNat a < 64 := by
  have h0 := (a 0).val_lt; have h1 := (a 1).val_lt; have h2 := (a 2).val_lt
  have h3 := (a 3).val_lt; have h4 := (a 4).val_lt; have h5 := (a 5).val_lt
  unfold vecToNat; omega

private lemma testBit_zmod2_succ (x : ZMod 2) (m k : ℕ) :
    (x.val + 2 * m).testBit (k + 1) = m.testBit k := by
  rw [Nat.testBit_succ]
  have hdiv : (x.val + 2 * m) / 2 = m := by have := x.val_lt; omega
  rw [hdiv]

private lemma ite_val_mod2 : ∀ x : ZMod 2,
    (if x.val % 2 = 1 then (1 : ZMod 2) else 0) = x := by decide

private lemma bitVec_vecToNat (a : Vec6) : bitVec (vecToNat a) = a := by
  funext i
  fin_cases i
  · change (if (vecToNat a).testBit 0 = true then (1 : ZMod 2) else 0) = a 0
    simp [vecToNat, ite_val_mod2]
  · change (if (vecToNat a).testBit 1 = true then (1 : ZMod 2) else 0) = a 1
    simp [vecToNat, testBit_zmod2_succ, ite_val_mod2]
  · change (if (vecToNat a).testBit 2 = true then (1 : ZMod 2) else 0) = a 2
    simp [vecToNat, testBit_zmod2_succ, ite_val_mod2]
  · change (if (vecToNat a).testBit 3 = true then (1 : ZMod 2) else 0) = a 3
    simp [vecToNat, testBit_zmod2_succ, ite_val_mod2]
  · change (if (vecToNat a).testBit 4 = true then (1 : ZMod 2) else 0) = a 4
    simp [vecToNat, testBit_zmod2_succ, ite_val_mod2]
  · change (if (vecToNat a).testBit 5 = true then (1 : ZMod 2) else 0) = a 5
    simp [vecToNat, testBit_zmod2_succ, ite_val_mod2]

private lemma zmod2_add_ite (b1 b2 : Bool) :
    ((if b1 then (1 : ZMod 2) else 0) + (if b2 then (1 : ZMod 2) else 0)) =
      if xor b1 b2 then 1 else 0 := by
  cases b1 <;> cases b2 <;> decide

private lemma zmod2_mul_ite (b1 b2 : Bool) :
    ((if b1 then (1 : ZMod 2) else 0) * (if b2 then (1 : ZMod 2) else 0)) =
      if b1 && b2 then 1 else 0 := by
  cases b1 <;> cases b2 <;> decide

private lemma testBit_ite_zero (b : Bool) (m k : ℕ) :
    (if b then m else 0).testBit k = (b && m.testBit k) := by
  cases b <;> simp

private lemma zEval_bitVec_eq_zMask (a : ℕ) (e : Fin 15) :
    zEval (bitVec a) e = if (zMask a).testBit e.val then 1 else 0 := by
  unfold zEval bitVec pSigma zMask
  rw [Fin.sum_univ_six]
  simp only [Nat.testBit_xor, testBit_ite_zero, zmod2_mul_ite, zmod2_add_ite]
  rfl

private lemma pSigma_ne_zero : ∀ e : Fin 15, pSigma e ≠ 0 := by
  decide

private lemma pSigma_chord (i : Fin 6) : pSigma ⟨9 + i.val, by omega⟩ = Pi.single i 1 := by
  fin_cases i <;> funext j <;> fin_cases j <;> decide

private lemma pSigma_flow :
    ∀ v : Fin 10, ∑ e ∈ Finset.univ.filter (fun e => pTgt e = v ∨ pSrc e = v), pSigma e = 0 := by
  decide

private lemma zEval_flow (a : Vec6) (v : Fin 10) :
    ∑ e ∈ Finset.univ.filter (fun e => pTgt e = v ∨ pSrc e = v), zEval a e = 0 := by
  unfold zEval
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.mul_sum]
  have hv := congrFun (pSigma_flow v) i
  simp only [Finset.sum_apply, Pi.zero_apply] at hv
  rw [hv, mul_zero]

/-! ### Every binary cycle of the Petersen graph is in the span of the 6 fundamental cycles -/

private lemma inc_v5 : Finset.univ.filter (fun e : Fin 15 => pTgt e = 5 ∨ pSrc e = 5) = {4, 10, 14} := by decide
private lemma inc_v6 : Finset.univ.filter (fun e : Fin 15 => pTgt e = 6 ∨ pSrc e = 6) = {5, 12, 13} := by decide
private lemma inc_v7 : Finset.univ.filter (fun e : Fin 15 => pTgt e = 7 ∨ pSrc e = 7) = {6, 10, 11} := by decide
private lemma inc_v8 : Finset.univ.filter (fun e : Fin 15 => pTgt e = 8 ∨ pSrc e = 8) = {7, 13, 14} := by decide
private lemma inc_v9 : Finset.univ.filter (fun e : Fin 15 => pTgt e = 9 ∨ pSrc e = 9) = {8, 11, 12} := by decide
private lemma inc_v4 : Finset.univ.filter (fun e : Fin 15 => pTgt e = 4 ∨ pSrc e = 4) = {3, 8, 9} := by decide
private lemma inc_v3 : Finset.univ.filter (fun e : Fin 15 => pTgt e = 3 ∨ pSrc e = 3) = {2, 3, 7} := by decide
private lemma inc_v2 : Finset.univ.filter (fun e : Fin 15 => pTgt e = 2 ∨ pSrc e = 2) = {1, 2, 6} := by decide
private lemma inc_v1 : Finset.univ.filter (fun e : Fin 15 => pTgt e = 1 ∨ pSrc e = 1) = {0, 1, 5} := by decide

private lemma cycle_eq_zEval (z : Fin 15 → ZMod 2)
    (hz : ∀ v : Fin 10, ∑ e ∈ Finset.univ.filter (fun e => pTgt e = v ∨ pSrc e = v), z e = 0) :
    ∃ a : Vec6, z = zEval a := by
  let a : Vec6 := fun i => z ⟨9 + i.val, by omega⟩
  refine ⟨a, ?_⟩
  let w : Fin 15 → ZMod 2 := fun e => z e + zEval a e
  have hw_flow : ∀ v : Fin 10, ∑ e ∈ Finset.univ.filter (fun e => pTgt e = v ∨ pSrc e = v), w e = 0 := by
    intro v
    simp only [w, Finset.sum_add_distrib, hz v, zEval_flow a v, add_zero]
  have hw_chord : ∀ i : Fin 6, w ⟨9 + i.val, by omega⟩ = 0 := by
    intro i
    simp only [w, zEval, pSigma_chord i, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, a]
    exact zmod2_add_self _
  have hw9 : w 9 = 0 := hw_chord 0
  have hw10 : w 10 = 0 := hw_chord 1
  have hw11 : w 11 = 0 := hw_chord 2
  have hw12 : w 12 = 0 := hw_chord 3
  have hw13 : w 13 = 0 := hw_chord 4
  have hw14 : w 14 = 0 := hw_chord 5
  have h5 := hw_flow 5; rw [inc_v5] at h5
  have hw4 : w 4 = 0 := by simpa [hw10, hw14] using h5
  have h6 := hw_flow 6; rw [inc_v6] at h6
  have hw5 : w 5 = 0 := by simpa [hw12, hw13] using h6
  have h7 := hw_flow 7; rw [inc_v7] at h7
  have hw6 : w 6 = 0 := by simpa [hw10, hw11] using h7
  have h8 := hw_flow 8; rw [inc_v8] at h8
  have hw7 : w 7 = 0 := by simpa [hw13, hw14] using h8
  have h9 := hw_flow 9; rw [inc_v9] at h9
  have hw8 : w 8 = 0 := by simpa [hw11, hw12] using h9
  have h4 := hw_flow 4; rw [inc_v4] at h4
  have hw3 : w 3 = 0 := by simpa [hw8, hw9] using h4
  have h3 := hw_flow 3; rw [inc_v3] at h3
  have hw2 : w 2 = 0 := by simpa [hw3, hw7] using h3
  have h2 := hw_flow 2; rw [inc_v2] at h2
  have hw1 : w 1 = 0 := by simpa [hw2, hw6] using h2
  have h1 := hw_flow 1; rw [inc_v1] at h1
  have hw0 : w 0 = 0 := by simpa [hw1, hw5] using h1
  have hw_zero : w = 0 := by
    funext e
    match e with
    | ⟨0, _⟩ => exact hw0
    | ⟨1, _⟩ => exact hw1
    | ⟨2, _⟩ => exact hw2
    | ⟨3, _⟩ => exact hw3
    | ⟨4, _⟩ => exact hw4
    | ⟨5, _⟩ => exact hw5
    | ⟨6, _⟩ => exact hw6
    | ⟨7, _⟩ => exact hw7
    | ⟨8, _⟩ => exact hw8
    | ⟨9, _⟩ => exact hw9
    | ⟨10, _⟩ => exact hw10
    | ⟨11, _⟩ => exact hw11
    | ⟨12, _⟩ => exact hw12
    | ⟨13, _⟩ => exact hw13
    | ⟨14, _⟩ => exact hw14
  exact (vec_eq_iff_add_eq_zero z (zEval a)).mpr hw_zero

/-! ### Finite decodable properties of Petersen's cycle space: girth 5, snark, edge-criticality -/

private def maskWeight15 (m : ℕ) : ℕ :=
  ((List.range 15).filter (fun e => m.testBit e)).length

private lemma check_girth5 :
    (List.range 64).all (fun a => a == 0 || 5 ≤ maskWeight15 (zMask a)) = true := by
  decide

private def allZMasks : List ℕ := (List.range 64).map zMask

private lemma check_no_3ec :
    allZMasks.all (fun ma => allZMasks.all (fun mb => (ma ||| mb) != 32767)) = true := by
  decide

private def witA : ℕ → ℕ
  | 0 => 23 | 1 => 22 | 2 => 22 | 3 => 23 | 4 => 20 | 5 => 26 | 6 => 22 | 7 => 10
  | 8 => 18 | 9 => 26 | 10 => 21 | 11 => 19 | 12 => 19 | 13 => 6 | _ => 10

private def witB : ℕ → ℕ
  | 0 => 42 | 1 => 43 | 2 => 45 | 3 => 43 | 4 => 43 | 5 => 37 | 6 => 41 | 7 => 53
  | 8 => 45 | 9 => 44 | 10 => 45 | 11 => 43 | 12 => 39 | 13 => 43 | _ => 23

private lemma check_crit_3ec :
    (List.range 15).all (fun e0 =>
      (zMask (witA e0) ||| zMask (witB e0)) == (32767 ^^^ (1 <<< e0))) = true := by
  decide

private lemma maskWeight15_eq_card (m : ℕ) :
    maskWeight15 m = (Finset.univ.filter (fun e : Fin 15 => m.testBit e.val = true)).card := by
  unfold maskWeight15
  have h1 : (Finset.univ.filter (fun e : Fin 15 => m.testBit e.val = true)).card =
      ((Finset.range 15).filter (fun e : ℕ => m.testBit e = true)).card := by
    refine Finset.card_bij (fun e _ => e.val) ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at he ⊢
      exact ⟨e.isLt, he⟩
    · intro e1 _ e2 _ h; exact Fin.ext h
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      exact ⟨⟨k, hk.1⟩, by simpa using hk.2, rfl⟩
  rw [h1, ← List.toFinset_range, ← List.toFinset_filter]
  exact (List.toFinset_card_of_nodup ((List.nodup_range).filter _)).symm

private lemma girth5_of_zEval {a : Vec6} (ha : zEval a ≠ 0) :
    5 ≤ (Finset.univ.filter (fun e : Fin 15 => zEval a e ≠ 0)).card := by
  set n := vecToNat a
  have hn_lt : n < 64 := vecToNat_lt a
  have hbv : bitVec n = a := bitVec_vecToNat a
  have hn_ne : n ≠ 0 := by
    intro h0
    apply ha
    funext e
    rw [← hbv, zEval_bitVec_eq_zMask, h0]
    simp [zMask]
  have hall := List.all_eq_true.mp check_girth5 n (List.mem_range.mpr hn_lt)
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
  have hge : 5 ≤ maskWeight15 (zMask n) := hall.resolve_left hn_ne
  rw [maskWeight15_eq_card] at hge
  convert hge using 2
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hbv, zEval_bitVec_eq_zMask]
  cases (zMask n).testBit e.val <;> simp

private lemma no_3ec_zEval (a b : Vec6) :
    ¬ ∀ e : Fin 15, zEval a e ≠ 0 ∨ zEval b e ≠ 0 := by
  intro hcov
  set na := vecToNat a
  set nb := vecToNat b
  have hna : na < 64 := vecToNat_lt a
  have hnb : nb < 64 := vecToNat_lt b
  have hne : (zMask na ||| zMask nb) ≠ 32767 := by
    have hma : zMask na ∈ allZMasks := List.mem_map.mpr ⟨na, List.mem_range.mpr hna, rfl⟩
    have hmb : zMask nb ∈ allZMasks := List.mem_map.mpr ⟨nb, List.mem_range.mpr hnb, rfl⟩
    have h1 := List.all_eq_true.mp check_no_3ec (zMask na) hma
    have h2 := List.all_eq_true.mp h1 (zMask nb) hmb
    simpa using h2
  apply hne
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 15
  · have h32767 : (32767 : ℕ).testBit k = true := by
      have : (32767 : ℕ) = 2 ^ 15 - 1 := by decide
      rw [this, Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hk
    rw [h32767, Nat.testBit_or]
    have he := hcov ⟨k, hk⟩
    rw [← bitVec_vecToNat a, ← bitVec_vecToNat b, zEval_bitVec_eq_zMask, zEval_bitVec_eq_zMask] at he
    change (if (zMask na).testBit k = true then (1 : ZMod 2) else 0) ≠ 0 ∨
      (if (zMask nb).testBit k = true then (1 : ZMod 2) else 0) ≠ 0 at he
    rcases he with h | h
    · have ht : (zMask na).testBit k = true := by
        cases hc : (zMask na).testBit k <;> simp_all
      simp [ht]
    · have ht : (zMask nb).testBit k = true := by
        cases hc : (zMask nb).testBit k <;> simp_all
      simp [ht]
  · have hlt_a : zMask na < 2 ^ 15 := by
      have : ∀ x : Fin 64, zMask x.val < 32768 := by decide
      exact this ⟨na, hna⟩
    have hlt_b : zMask nb < 2 ^ 15 := by
      have : ∀ x : Fin 64, zMask x.val < 32768 := by decide
      exact this ⟨nb, hnb⟩
    have h32767 : (32767 : ℕ).testBit k = false := by
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hk)))
    have ha0 : (zMask na).testBit k = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_a (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hk)))
    have hb0 : (zMask nb).testBit k = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_b (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hk)))
    rw [Nat.testBit_or, ha0, hb0, h32767]
    rfl

private lemma exists_crit_3ec (e0 : Fin 15) :
    ∃ a b : Vec6, ∀ e : Fin 15, e ≠ e0 → zEval a e ≠ 0 ∨ zEval b e ≠ 0 := by
  refine ⟨bitVec (witA e0.val), bitVec (witB e0.val), fun e he => ?_⟩
  have hchk := List.all_eq_true.mp check_crit_3ec e0.val (List.mem_range.mpr e0.isLt)
  simp only [beq_iff_eq] at hchk
  have hbit := congrArg (fun m => m.testBit e.val) hchk
  have hrhs : (32767 ^^^ (1 <<< e0.val)).testBit e.val = true := by
    have h1 : (32767 : ℕ).testBit e.val = true := by
      have : (32767 : ℕ) = 2 ^ 15 - 1 := by decide
      rw [this, Nat.testBit_two_pow_sub_one]
      exact decide_eq_true e.isLt
    have h2 : (1 <<< e0.val).testBit e.val = false := by
      rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
      exact decide_eq_false (fun h => he (Fin.ext h.symm))
    rw [Nat.testBit_xor, h1, h2]
    rfl
  rw [hrhs, Nat.testBit_or, Bool.or_eq_true] at hbit
  rw [zEval_bitVec_eq_zMask, zEval_bitVec_eq_zMask]
  rcases hbit with h | h
  · left; simp [h]
  · right; simp [h]

/-! ### Counterexample sets B ⊆ Vec6 and B' ⊆ Vec64 -/

private def setB : Set Vec6 := Set.range pSigma

private def setB' : Set Vec64 :=
  {f : Vec64 | ∃ x y : Vec6, y - x ∈ setB ∧ f = single1 x + single1 y}

private lemma neg_setB : -setB = setB := by
  ext x
  simp only [Set.mem_neg, vec_neg]

private lemma neg_setB' : -setB' = setB' := by
  ext f
  simp only [Set.mem_neg, vec_neg]

private lemma zero_not_mem_setB : (0 : Vec6) ∉ setB := by
  rintro ⟨e, he⟩
  exact pSigma_ne_zero e he

private lemma zero_not_mem_setB' : (0 : Vec64) ∉ setB' := by
  rintro ⟨x, y, hxy, hf⟩
  have hval := congrFun hf x
  simp only [single1, Pi.zero_apply, Pi.add_apply, Pi.single_apply, ite_true] at hval
  by_cases hxy_eq : x = y
  · subst hxy_eq
    rw [sub_self] at hxy
    exact zero_not_mem_setB hxy
  · rw [if_neg hxy_eq] at hval
    norm_num at hval

private def cayHom : cay setB →g cay setB' where
  toFun x := single1 x
  map_rel' {x y} hxy := by
    have hsub : y - x ∈ setB := by
      rcases hxy with ⟨_, h | h⟩
      · exact h
      · have : -(x - y) ∈ -setB := Set.neg_mem_neg.mpr h
        rw [neg_sub, neg_setB] at this
        exact this
    have hne : single1 x ≠ single1 y := by
      intro heq
      have h1 : x = y := by
        by_contra h
        have hv := congrFun heq x
        simp [single1, h] at hv
      subst h1
      rw [sub_self] at hsub
      exact zero_not_mem_setB hsub
    refine ⟨hne, Or.inl ?_⟩
    refine ⟨x, y, hsub, ?_⟩
    rw [vec_sub_eq_add, add_comm]

private lemma petersen_has_B_flow : HasFlow setB pSrc pTgt := by
  refine ⟨pSigma, fun e => ⟨e, rfl⟩, fun v => ?_⟩
  rw [flow_iff_inc_sum_zero]
  exact pSigma_flow v

private lemma petersen_not_has_B'_flow : ¬ HasFlow setB' pSrc pTgt := by
  rintro ⟨ψ, hψB', hψflow⟩
  have hψinc : ∀ v : Fin 10,
      ∑ e ∈ Finset.univ.filter (fun e => pTgt e = v ∨ pSrc e = v), ψ e = 0 := fun v =>
    (flow_iff_inc_sum_zero ψ v).mp (hψflow v)
  -- Extract endpoints x e, y e and edge label c e for every edge e of Petersen
  have hex : ∀ e : Fin 15, ∃ x y : Vec6, ∃ c : Fin 15,
      x ≠ y ∧ x + y = pSigma c ∧ ψ e = single1 x + single1 y := by
    intro e
    rcases hψB' e with ⟨x, y, ⟨c, hc⟩, hfe⟩
    have hxy : x + y = pSigma c := by rw [hc, vec_sub_eq_add, add_comm]
    have hne : x ≠ y := by
      intro heq
      subst heq
      rw [vec_add_self] at hxy
      exact pSigma_ne_zero c hxy.symm
    exact ⟨x, y, c, hne, hxy, hfe⟩
  choose x y c hxy_ne hxy_sum hψ_eq using hex
  -- Step 1: c is cycle-continuous, hence surjective (since P is a critical snark)
  have hc_pullback : ∀ a : Vec6, ∃ a' : Vec6, ∀ e : Fin 15, zEval a' e = zEval a (c e) := by
    intro a
    let z : Fin 15 → ZMod 2 := fun e => zEval a (c e)
    have hz_eq : ∀ e : Fin 15, z e = ∑ u : Vec6, ψ e u * (∑ i : Fin 6, a i * u i) := by
      intro e
      rw [hψ_eq e]
      simp only [single1, Pi.add_apply, add_mul, Finset.sum_add_distrib, Pi.single_apply, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [← Finset.sum_add_distrib]
      unfold z zEval
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_add, ← Pi.add_apply, hxy_sum e]
    have hz_flow : ∀ v : Fin 10,
        ∑ e ∈ Finset.univ.filter (fun e => pTgt e = v ∨ pSrc e = v), z e = 0 := by
      intro v
      simp_rw [hz_eq]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [← Finset.sum_mul]
      have hv := congrFun (hψinc v) u
      simp only [Finset.sum_apply, Pi.zero_apply] at hv
      rw [hv, zero_mul]
    rcases cycle_eq_zEval z hz_flow with ⟨a', ha'⟩
    exact ⟨a', fun e => (congrFun ha' e).symm⟩
  have hc_surj : Function.Surjective c := by
    intro e0
    by_contra hmiss
    push Not at hmiss
    rcases exists_crit_3ec e0 with ⟨a, b, hab⟩
    rcases hc_pullback a with ⟨a', ha'⟩
    rcases hc_pullback b with ⟨b', hb'⟩
    refine no_3ec_zEval a' b' (fun e => ?_)
    rw [ha' e, hb' e]
    exact hab (c e) (hmiss e)
  -- Step 2: Let S be the set of active vertices in Vec6; girth 5 forces every w ∈ S to have degree ≥ 5, so |S| ≤ 6
  let S : Finset Vec6 := Finset.univ.image x ∪ Finset.univ.image y
  have hxS : ∀ e : Fin 15, x e ∈ S := fun e =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem x (Finset.mem_univ e))
  have hyS : ∀ e : Fin 15, y e ∈ S := fun e =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem y (Finset.mem_univ e))
  have hψ_val : ∀ (e : Fin 15) (w : Vec6),
      ψ e w = if w = x e ∨ w = y e then 1 else 0 := by
    intro e w
    rw [hψ_eq e]
    simp only [single1, Pi.add_apply, Pi.single_apply]
    by_cases h1 : w = x e
    · subst h1
      simp [hxy_ne e]
    · by_cases h2 : w = y e
      · subst h2
        simp [h1]
      · simp [h1, h2]
  have hdeg_ge5 : ∀ w ∈ S, 5 ≤ (Finset.univ.filter (fun e : Fin 15 => ψ e w ≠ 0)).card := by
    intro w hw
    let δ : Fin 15 → ZMod 2 := fun e => ψ e w
    have hδ_flow : ∀ v : Fin 10,
        ∑ e ∈ Finset.univ.filter (fun e => pTgt e = v ∨ pSrc e = v), δ e = 0 := by
      intro v
      have hv := congrFun (hψinc v) w
      simpa [δ] using hv
    rcases cycle_eq_zEval δ hδ_flow with ⟨a, ha⟩
    have hδ_ne : δ ≠ 0 := by
      intro h0
      rcases Finset.mem_union.mp hw with h | h
      · rcases Finset.mem_image.mp h with ⟨e, _, rfl⟩
        have hv := congrFun h0 e
        simp only [δ, hψ_val e (x e), true_or, ite_true, Pi.zero_apply] at hv
        norm_num at hv
      · rcases Finset.mem_image.mp h with ⟨e, _, rfl⟩
        have hv := congrFun h0 e
        simp only [δ, hψ_val e (y e), or_true, ite_true, Pi.zero_apply] at hv
        norm_num at hv
    change 5 ≤ (Finset.univ.filter (fun e : Fin 15 => δ e ≠ 0)).card
    rw [ha] at hδ_ne ⊢
    exact girth5_of_zEval hδ_ne
  have hS_card : S.card ≤ 6 := by
    have h1 : 5 * S.card ≤ ∑ w ∈ S, (Finset.univ.filter (fun e : Fin 15 => ψ e w ≠ 0)).card := by
      calc
        5 * S.card = ∑ _w ∈ S, 5 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ w ∈ S, (Finset.univ.filter (fun e : Fin 15 => ψ e w ≠ 0)).card :=
          Finset.sum_le_sum hdeg_ge5
    have h2 : (∑ w ∈ S, (Finset.univ.filter (fun e : Fin 15 => ψ e w ≠ 0)).card) =
        ∑ e : Fin 15, (S.filter (fun w => ψ e w ≠ 0)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have h3 : ∀ e : Fin 15, (S.filter (fun w => ψ e w ≠ 0)).card = 2 := by
      intro e
      have hflt : S.filter (fun w => ψ e w ≠ 0) = {x e, y e} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, hψ_val e w]
        constructor
        · rintro ⟨_, hne⟩
          by_contra hnot
          rw [if_neg hnot] at hne
          exact hne rfl
        · rintro (rfl | rfl)
          · exact ⟨hxS e, by simp⟩
          · exact ⟨hyS e, by simp⟩
      rw [hflt, Finset.card_pair (hxy_ne e)]
    rw [h2, Finset.sum_congr rfl (fun e _ => h3 e)] at h1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    omega
  -- Step 3: Even-sum functions on S have cardinality ≤ 32, yet surject onto Vec6 (card 64)
  have hS_ne : x 0 ∈ S := hxS 0
  clear hψB' hψflow hψinc hψ_eq hc_pullback hdeg_ge5
  generalize S = S' at hxS hyS hS_card hS_ne
  let EvenS := {f : S' → ZMod 2 // ∑ w : S', f w = 0}
  let π : EvenS → Vec6 := fun f => ∑ w : S', (f.1 w) • w.1
  have hπ_surj : Function.Surjective π := by
    intro u
    have hpick : ∀ i : Fin 6, ∃ e : Fin 15, c e = ⟨9 + i.val, by omega⟩ :=
      fun i => hc_surj ⟨9 + i.val, by omega⟩
    choose ei hei using hpick
    let v : Fin 15 → ZMod 2 := fun e => ∑ i : Fin 6, if e = ei i then u i else 0
    let f : S' → ZMod 2 := fun w => ∑ e : Fin 15, v e * ψ e w.1
    have hf_even : ∑ w : S', f w = 0 := by
      simp only [f]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [← Finset.mul_sum]
      have hsum2 : ∑ w : S', ψ e w.1 = 0 := by
        rw [Finset.sum_coe_sort S' (fun w => ψ e w)]
        have hsub : ({x e, y e} : Finset Vec6) ⊆ S' := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw'
          · exact hxS e
          · rw [Finset.mem_singleton.mp hw']; exact hyS e
        rw [← Finset.sum_subset hsub]
        · rw [Finset.sum_pair (hxy_ne e), hψ_val e (x e), hψ_val e (y e)]
          simp only [true_or, or_true, ite_true]
          exact zmod2_add_self 1
        · intro w _ hnot
          rw [hψ_val e w, if_neg]
          rintro (rfl | rfl) <;> simp at hnot
      rw [hsum2, mul_zero]
    refine ⟨⟨f, hf_even⟩, ?_⟩
    funext j
    have hstep1 : π ⟨f, hf_even⟩ j = ∑ e : Fin 15, v e * (∑ w : S', ψ e w.1 * w.1 j) := by
      simp only [π, f, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp_rw [mul_assoc, ← Finset.mul_sum]
    have hinner : ∀ e : Fin 15, (∑ w : S', ψ e w.1 * w.1 j) = pSigma (c e) j := by
      intro e
      rw [Finset.sum_coe_sort S' (fun w => ψ e w * w j)]
      have hsub : ({x e, y e} : Finset Vec6) ⊆ S' := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact hxS e
        · rw [Finset.mem_singleton.mp hw']; exact hyS e
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_pair (hxy_ne e), hψ_val e (x e), hψ_val e (y e)]
        simp only [true_or, or_true, ite_true, one_mul]
        exact congrFun (hxy_sum e) j
      · intro w _ hnot
        rw [hψ_val e w, if_neg]
        · simp
        · rintro (rfl | rfl) <;> simp at hnot
    rw [hstep1]
    simp_rw [hinner, v, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hcol : ∀ i : Fin 6,
        (∑ e : Fin 15, (if e = ei i then u i else 0) * pSigma (c e) j) =
          if j = i then u i else 0 := by
      intro i
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hei i,
        pSigma_chord i, Pi.single_apply, mul_ite, mul_one, mul_zero]
    simp_rw [hcol]
    simp
  have hcard_ge : 64 ≤ Fintype.card EvenS := by
    have h64 : Fintype.card Vec6 = 64 := by
      simp [Vec6, ZMod.card]
    rw [← h64]
    exact Fintype.card_le_of_surjective π hπ_surj
  -- Upper bound Fintype.card EvenS ≤ 32
  let w0 : S' := ⟨x 0, hS_ne⟩
  let rest := {w : S' // w ≠ w0}
  let res : EvenS → (rest → ZMod 2) := fun f w => f.1 w.1
  have hres_inj : Function.Injective res := by
    intro f g hfg
    apply Subtype.ext
    funext w
    by_cases hw : w = w0
    · subst hw
      have hf0 := f.2
      have hg0 := g.2
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w0)] at hf0 hg0
      have hsum_eq : ∑ u ∈ Finset.univ.erase w0, f.1 u = ∑ u ∈ Finset.univ.erase w0, g.1 u := by
        refine Finset.sum_congr rfl fun u hu => ?_
        exact congrFun hfg ⟨u, (Finset.mem_erase.mp hu).1⟩
      rw [hsum_eq] at hf0
      exact add_right_cancel (hf0.trans hg0.symm)
    · exact congrFun hfg ⟨w, hw⟩
  have hcard_le : Fintype.card EvenS ≤ 32 := by
    have h1 := Fintype.card_le_of_injective res hres_inj
    have h2 : Fintype.card (rest → ZMod 2) = 2 ^ Fintype.card rest := by
      simp [ZMod.card]
    have h3 : Fintype.card rest = S'.card - 1 := by
      simp [rest, Fintype.card_subtype_compl]
    rw [h3] at h2
    have h4 : 2 ^ (S'.card - 1) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

end OPGAHomFlowProof

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_a_homomorphism_problem_for_flows.main) := by
  intro hmain
  have hflow := hmain OPGAHomFlowProof.Vec6 OPGAHomFlowProof.Vec64
    OPGAHomFlowProof.setB OPGAHomFlowProof.setB'
    OPGAHomFlowProof.neg_setB OPGAHomFlowProof.neg_setB'
    OPGAHomFlowProof.zero_not_mem_setB OPGAHomFlowProof.zero_not_mem_setB'
    ⟨OPGAHomFlowProof.cayHom⟩
    (Fin 10) (Fin 15) OPGAHomFlowProof.pSrc OPGAHomFlowProof.pTgt
    OPGAHomFlowProof.petersen_has_B_flow
  exact OPGAHomFlowProof.petersen_not_has_B'_flow hflow
