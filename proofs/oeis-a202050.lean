import OMAStatements.S_oeis_a202050

namespace OMA.S_oeis_a202050_Proof

open OMA.S_oeis_a202050

private instance (b0 b1 b2 : Fin 2) : Decidable (avoids3 b0 b1 b2) := by
  unfold avoids3
  infer_instance

private lemma avoids3_flip (b0 b1 b2 : Fin 2) :
    avoids3 (1 - b0) (1 - b1) (1 - b2) ↔ avoids3 b0 b1 b2 := by
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> decide

private def isValidRow (r : Fin 8 → Fin 2) : Prop :=
  ∀ c : Fin 6, avoids3 (r ⟨c.1, by omega⟩) (r ⟨c.1 + 1, by omega⟩) (r ⟨c.1 + 2, by omega⟩)

private instance (r : Fin 8 → Fin 2) : Decidable (isValidRow r) := by
  unfold isValidRow
  infer_instance

private def invPi (c : Fin 8) : ℕ :=
  match c.1 with
  | 0 => 0
  | 1 => 7
  | 2 => 1
  | 3 => 6
  | 4 => 2
  | 5 => 5
  | 6 => 3
  | _ => 4

private def piFin (t : Fin 8) : Fin 8 :=
  match t.1 with
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 6
  | 4 => 7
  | 5 => 5
  | 6 => 3
  | _ => 1

private lemma invPi_piFin (t : Fin 8) : invPi (piFin t) = t.1 := by
  fin_cases t <;> rfl

private lemma piFin_surj (c : Fin 8) : ∃ t : Fin 8, piFin t = c := by
  fin_cases c
  · exact ⟨0, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

private def rowVec (i : Fin 16) (c : Fin 8) : Fin 2 :=
  if 8 ≤ (invPi c + 16 - i.1) % 16 then 1 else 0

private lemma rowVec_valid (i : Fin 16) : isValidRow (rowVec i) := by
  revert i
  decide

private lemma rowVec_injective : Function.Injective rowVec := by
  intro i j h
  have h' : ∀ c : Fin 8, rowVec i c = rowVec j c := fun c => congrFun h c
  revert i j h'
  decide

private def mkRow (b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2) (c : Fin 8) : Fin 2 :=
  match c.1 with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5
  | 6 => b6
  | _ => b7

private lemma mkRow_surj :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2,
      avoids3 b0 b1 b2 → avoids3 b1 b2 b3 → avoids3 b2 b3 b4 →
      avoids3 b3 b4 b5 → avoids3 b4 b5 b6 → avoids3 b5 b6 b7 →
      ∃ i : Fin 16, ∀ c : Fin 8, rowVec i c = mkRow b0 b1 b2 b3 b4 b5 b6 b7 c := by
  decide

private lemma rowVec_surjective (r : Fin 8 → Fin 2) (hr : isValidRow r) :
    ∃ i : Fin 16, rowVec i = r := by
  have h := mkRow_surj (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7)
    (hr 0) (hr 1) (hr 2) (hr 3) (hr 4) (hr 5)
  rcases h with ⟨i, hi⟩
  refine ⟨i, funext fun c => ?_⟩
  rw [hi c]
  fin_cases c <;> rfl

private noncomputable def validRowEquiv : Fin 16 ≃ {r : Fin 8 → Fin 2 // isValidRow r} :=
  Equiv.ofBijective (fun i => ⟨rowVec i, rowVec_valid i⟩)
    ⟨fun i j h => rowVec_injective (congrArg Subtype.val h),
     fun ⟨r, hr⟩ => by
       rcases rowVec_surjective r hr with ⟨i, hi⟩
       exact ⟨i, Subtype.ext hi⟩⟩

private def cycDist (i j : Fin 16) : ℕ :=
  min ((j.1 + 16 - i.1) % 16) ((i.1 + 16 - j.1) % 16)

private def cycDistFin (i j : Fin 16) : Fin 9 :=
  ⟨cycDist i j, by unfold cycDist; omega⟩

private def shift (s i : Fin 16) : Fin 16 :=
  ⟨(i.1 + s.1) % 16, Nat.mod_lt _ (by omega)⟩

private def shift1 (i : Fin 16) : Fin 16 :=
  ⟨(i.1 + 1) % 16, Nat.mod_lt _ (by omega)⟩

private lemma cycDist_shift (s i j : Fin 16) :
    cycDist (shift s i) (shift s j) = cycDist i j := by
  unfold cycDist shift
  simp only
  omega

private lemma shift_zero (i : Fin 16) : shift 0 i = i := by
  ext
  simp only [shift, Fin.val_zero, add_zero]
  exact Nat.mod_eq_of_lt i.2

private def compat (i j k : Fin 16) : Prop :=
  ∀ c : Fin 8, avoids3 (rowVec i c) (rowVec j c) (rowVec k c)

private instance (i j k : Fin 16) : Decidable (compat i j k) := by
  unfold compat
  infer_instance

private lemma rowVec_shift1_succ (i : Fin 16) (t : Fin 8) (ht : t.1 < 7) :
    rowVec (shift1 i) (piFin ⟨t.1 + 1, by omega⟩) = rowVec i (piFin t) := by
  unfold rowVec shift1
  rw [invPi_piFin, invPi_piFin]
  simp only
  have hmod : (t.1 + 1 + 16 - (i.1 + 1) % 16) % 16 = (t.1 + 16 - i.1) % 16 := by omega
  rw [hmod]

private lemma rowVec_shift1_zero (i : Fin 16) :
    rowVec (shift1 i) (piFin 0) = 1 - rowVec i (piFin 7) := by
  unfold rowVec shift1
  rw [invPi_piFin, invPi_piFin]
  simp only [Fin.val_zero]
  have h7 : (7 : Fin 8).1 = 7 := rfl
  rw [h7]
  by_cases h : 8 ≤ (7 + 16 - i.1) % 16
  · have h' : ¬ (8 ≤ (0 + 16 - (i.1 + 1) % 16) % 16) := by omega
    simp [h, h']
  · have h' : 8 ≤ (0 + 16 - (i.1 + 1) % 16) % 16 := by omega
    simp [h, h']

private lemma compat_shift1 (i j k : Fin 16) :
    compat (shift1 i) (shift1 j) (shift1 k) ↔ compat i j k := by
  constructor
  · intro h c
    rcases piFin_surj c with ⟨t, rfl⟩
    by_cases ht : t.1 < 7
    · have h1 := h (piFin ⟨t.1 + 1, by omega⟩)
      rwa [rowVec_shift1_succ i t ht, rowVec_shift1_succ j t ht, rowVec_shift1_succ k t ht] at h1
    · have ht7 : t = 7 := by ext; omega
      subst ht7
      have h0 := h (piFin 0)
      rw [rowVec_shift1_zero i, rowVec_shift1_zero j, rowVec_shift1_zero k, avoids3_flip] at h0
      exact h0
  · intro h c
    rcases piFin_surj c with ⟨t, rfl⟩
    by_cases ht : t.1 = 0
    · have ht0 : t = 0 := by ext; omega
      subst ht0
      rw [rowVec_shift1_zero i, rowVec_shift1_zero j, rowVec_shift1_zero k, avoids3_flip]
      exact h (piFin 7)
    · have ht' : t.1 - 1 < 7 := by omega
      have hteq : (⟨(t.1 - 1) + 1, by omega⟩ : Fin 8) = t := by ext; simp only; omega
      have h1 := h (piFin ⟨t.1 - 1, by omega⟩)
      rw [← hteq, rowVec_shift1_succ i ⟨t.1 - 1, by omega⟩ ht',
        rowVec_shift1_succ j ⟨t.1 - 1, by omega⟩ ht',
        rowVec_shift1_succ k ⟨t.1 - 1, by omega⟩ ht']
      exact h1

private lemma compat_shift_nat (m : ℕ) (i j k : Fin 16) :
    compat (shift ⟨m % 16, Nat.mod_lt _ (by omega)⟩ i)
           (shift ⟨m % 16, Nat.mod_lt _ (by omega)⟩ j)
           (shift ⟨m % 16, Nat.mod_lt _ (by omega)⟩ k) ↔ compat i j k := by
  induction m with
  | zero =>
    have h0 : (⟨0 % 16, Nat.mod_lt _ (by omega)⟩ : Fin 16) = 0 := rfl
    rw [h0, shift_zero, shift_zero, shift_zero]
  | succ m ih =>
    have hstep : ∀ x : Fin 16,
        shift ⟨(m + 1) % 16, Nat.mod_lt _ (by omega)⟩ x =
        shift1 (shift ⟨m % 16, Nat.mod_lt _ (by omega)⟩ x) := by
      intro x; ext; simp only [shift, shift1]; omega
    rw [hstep i, hstep j, hstep k, compat_shift1, ih]

private lemma compat_shift (s i j k : Fin 16) :
    compat (shift s i) (shift s j) (shift s k) ↔ compat i j k := by
  have hs : s = ⟨s.1 % 16, Nat.mod_lt _ (by omega)⟩ := by
    ext; exact (Nat.mod_eq_of_lt s.2).symm
  conv_lhs => rw [hs]
  exact compat_shift_nat s.1 i j k

private lemma compat_zero_iff_geodesic :
    ∀ j k : Fin 16, compat 0 j k ↔ cycDist 0 k + cycDist k j = cycDist 0 j := by
  decide

private lemma compat_iff_geodesic (i j k : Fin 16) :
    compat i j k ↔ cycDist i k + cycDist k j = cycDist i j := by
  let s : Fin 16 := ⟨(16 - i.1) % 16, Nat.mod_lt _ (by omega)⟩
  have hsi : shift s i = 0 := by ext; simp only [shift, s, Fin.val_zero]; omega
  rw [← compat_shift s i j k, hsi, compat_zero_iff_geodesic,
      ← cycDist_shift s i k, ← cycDist_shift s k j, ← cycDist_shift s i j, hsi]

private def expectedTrans (D d : ℕ) : ℕ :=
  if D = 8 then (if d = 0 ∨ d = 8 then 1 else 2)
  else (if d ≤ D then 1 else 0)

private lemma geodesic_count_zero :
    ∀ j : Fin 16, ∀ d : Fin 9,
      (Finset.univ.filter (fun k : Fin 16 =>
        cycDist 0 k + cycDist k j = cycDist 0 j ∧ cycDistFin j k = d)).card =
      expectedTrans (cycDist 0 j) d.1 := by
  decide

private lemma trans_count (i j : Fin 16) (d : Fin 9) :
    (Finset.univ.filter (fun k : Fin 16 => compat i j k ∧ cycDistFin j k = d)).card =
      expectedTrans (cycDist i j) d.1 := by
  let s : Fin 16 := ⟨(16 - i.1) % 16, Nat.mod_lt _ (by omega)⟩
  have hsi : shift s i = 0 := by ext; simp only [shift, s, Fin.val_zero]; omega
  have hcard :
      (Finset.univ.filter (fun k : Fin 16 => compat i j k ∧ cycDistFin j k = d)).card =
      (Finset.univ.filter (fun k' : Fin 16 =>
        cycDist 0 k' + cycDist k' (shift s j) = cycDist 0 (shift s j) ∧
        cycDistFin (shift s j) k' = d)).card := by
    refine Finset.card_bij (fun k _ => shift s k) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rw [compat_iff_geodesic] at hk
      refine ⟨?_, ?_⟩
      · rw [← hsi, cycDist_shift, cycDist_shift, cycDist_shift]
        exact hk.1
      · ext
        simp only [cycDistFin]
        rw [cycDist_shift]
        exact congrArg Fin.val hk.2
    · intro k1 _ k2 _ h
      ext
      have hv : (shift s k1).1 = (shift s k2).1 := congrArg Fin.val h
      simp only [shift] at hv
      omega
    · intro k' hk'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk'
      refine ⟨shift i k', ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hback : shift s (shift i k') = k' := by
          ext; simp only [shift, s]; omega
        rw [compat_iff_geodesic]
        refine ⟨?_, ?_⟩
        · rw [← cycDist_shift s i (shift i k'), ← cycDist_shift s (shift i k') j,
              ← cycDist_shift s i j, hsi, hback]
          exact hk'.1
        · ext
          simp only [cycDistFin]
          rw [← cycDist_shift s j (shift i k'), hback]
          exact congrArg Fin.val hk'.2
      · ext; simp only [shift, s]; omega
  rw [hcard, geodesic_count_zero (shift s j) d, ← hsi, cycDist_shift]

private lemma init_count_zero :
    ∀ d : Fin 9,
      (Finset.univ.filter (fun j : Fin 16 => cycDistFin 0 j = d)).card =
      if d.1 = 0 ∨ d.1 = 8 then 1 else 2 := by
  decide

private lemma init_count (d : Fin 9) :
    (Finset.univ.filter (fun p : Fin 16 × Fin 16 => cycDistFin p.1 p.2 = d)).card =
      if d.1 = 0 ∨ d.1 = 8 then 16 else 32 := by
  have hcard :
      (Finset.univ.filter (fun p : Fin 16 × Fin 16 => cycDistFin p.1 p.2 = d)).card =
      ((Finset.univ : Finset (Fin 16)) ×ˢ
        (Finset.univ.filter (fun j : Fin 16 => cycDistFin 0 j = d))).card := by
    refine Finset.card_bij
      (fun p _ => (p.1, shift ⟨(16 - p.1.1) % 16, Nat.mod_lt _ (by omega)⟩ p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢
      ext
      simp only [cycDistFin]
      have h0 : shift ⟨(16 - p.1.1) % 16, Nat.mod_lt _ (by omega)⟩ p.1 = 0 := by
        ext; simp only [shift, Fin.val_zero]; omega
      rw [← h0, cycDist_shift]
      exact congrArg Fin.val hp
    · intro p1 _ p2 _ h
      rcases Prod.mk.inj h with ⟨h1, h2⟩
      have h1v : p1.1.1 = p2.1.1 := congrArg Fin.val h1
      have h2v : (shift ⟨(16 - p1.1.1) % 16, Nat.mod_lt _ (by omega)⟩ p1.2).1 =
                 (shift ⟨(16 - p2.1.1) % 16, Nat.mod_lt _ (by omega)⟩ p2.2).1 :=
        congrArg Fin.val h2
      simp only [shift] at h2v
      ext
      · exact h1v
      · omega
    · intro q hq
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter] at hq
      refine ⟨(q.1, shift q.1 q.2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        ext
        simp only [cycDistFin]
        have h0 : shift q.1 0 = q.1 := by
          ext; simp only [shift, Fin.val_zero, zero_add]; exact Nat.mod_eq_of_lt q.1.2
        calc
          cycDist q.1 (shift q.1 q.2) = cycDist (shift q.1 0) (shift q.1 q.2) := by rw [h0]
          _ = cycDist 0 q.2 := cycDist_shift q.1 0 q.2
          _ = d.1 := congrArg Fin.val hq
      · ext
        · rfl
        · simp only [shift]; omega
  rw [hcard, Finset.card_product, Finset.card_univ, Fintype.card_fin, init_count_zero d]
  split_ifs <;> rfl

private def ValidArrFrom (n : ℕ) (i j : Fin 16) :=
  {A : Fin (n + 2) → Fin 8 → Fin 2 // isValid n A ∧ A 0 = rowVec i ∧ A 1 = rowVec j}

private noncomputable instance (n : ℕ) (i j : Fin 16) : Fintype (ValidArrFrom n i j) := by
  classical
  unfold ValidArrFrom
  infer_instance

private noncomputable def extCount (n : ℕ) (i j : Fin 16) : ℕ :=
  Fintype.card (ValidArrFrom n i j)

private lemma validArrFrom_heq {n : ℕ} {i1 i2 j1 j2 : Fin 16}
    {x : ValidArrFrom n i1 j1} {y : ValidArrFrom n i2 j2}
    (hi : i1 = i2) (hj : j1 = j2) (hval : x.1 = y.1) : HEq x y := by
  subst hi; subst hj
  exact heq_of_eq (Subtype.ext hval)

private def consRow {n : ℕ} (r : Fin 8 → Fin 2) (B : Fin (n + 2) → Fin 8 → Fin 2) :
    Fin (n + 3) → Fin 8 → Fin 2
  | ⟨0, _⟩ => r
  | ⟨m + 1, hm⟩ => B ⟨m, by omega⟩

private lemma card_valid_eq_sum (n : ℕ) :
    Fintype.card {A : Fin (n + 2) → Fin 8 → Fin 2 // isValid n A} =
      ∑ p : Fin 16 × Fin 16, extCount n p.1 p.2 := by
  classical
  unfold extCount
  rw [← Fintype.card_sigma]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun ⟨A, hA⟩ =>
        let i := validRowEquiv.symm ⟨A 0, hA.1 0⟩
        let j := validRowEquiv.symm ⟨A 1, hA.1 1⟩
        ⟨(i, j), ⟨A, hA,
          (congrArg Subtype.val (validRowEquiv.apply_symm_apply ⟨A 0, hA.1 0⟩)).symm,
          (congrArg Subtype.val (validRowEquiv.apply_symm_apply ⟨A 1, hA.1 1⟩)).symm⟩⟩
      invFun := fun ⟨_, ⟨A, hA, _, _⟩⟩ => ⟨A, hA⟩
      left_inv := fun ⟨A, hA⟩ => rfl
      right_inv := fun ⟨⟨i, j⟩, ⟨A, hA, h0, h1⟩⟩ => by
        dsimp only
        have hi : validRowEquiv.symm ⟨A 0, hA.1 0⟩ = i := by
          apply validRowEquiv.injective
          rw [validRowEquiv.apply_symm_apply]
          exact Subtype.ext h0
        have hj : validRowEquiv.symm ⟨A 1, hA.1 1⟩ = j := by
          apply validRowEquiv.injective
          rw [validRowEquiv.apply_symm_apply]
          exact Subtype.ext h1
        exact Sigma.ext (Prod.ext hi hj) (validArrFrom_heq hi hj rfl) }

private lemma extCount_zero (i j : Fin 16) : extCount 0 i j = 1 := by
  unfold extCount
  let A0 : Fin 2 → Fin 8 → Fin 2 := fun r => if r.1 = 0 then rowVec i else rowVec j
  have hA0_valid : isValid 0 A0 := by
    refine ⟨fun r => ?_, fun c r => r.elim0⟩
    fin_cases r
    · exact rowVec_valid i
    · exact rowVec_valid j
  refine Fintype.card_eq_one_iff.mpr ⟨⟨A0, hA0_valid, rfl, rfl⟩, fun ⟨A, _, h0, h1⟩ => ?_⟩
  apply Subtype.ext
  funext r
  fin_cases r
  · exact h0
  · exact h1

private lemma extCount_succ (n : ℕ) (i j : Fin 16) :
    extCount (n + 1) i j = ∑ k ∈ Finset.univ.filter (compat i j), extCount n j k := by
  classical
  unfold extCount
  have hsum :
      ∑ k ∈ Finset.univ.filter (compat i j), Fintype.card (ValidArrFrom n j k) =
      Fintype.card (Σ k : {k : Fin 16 // compat i j k}, ValidArrFrom n j k.1) := by
    rw [Fintype.card_sigma]
    exact Finset.sum_subtype (p := compat i j) (Finset.univ.filter (compat i j))
      (fun _ => by simp) (fun k => Fintype.card (ValidArrFrom n j k))
  rw [hsum]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun ⟨A, hA, h0, h1⟩ =>
        let r2 : Fin (n + 3) := ⟨2, by omega⟩
        let k := validRowEquiv.symm ⟨A r2, hA.1 r2⟩
        have hk_eq : rowVec k = A r2 :=
          congrArg Subtype.val (validRowEquiv.apply_symm_apply ⟨A r2, hA.1 r2⟩)
        have hcomp : compat i j k := by
          intro c
          have hc := hA.2 c ⟨0, by omega⟩
          have h0' : A ⟨0, by omega⟩ c = rowVec i c := congrFun h0 c
          have h1' : A ⟨1, by omega⟩ c = rowVec j c := congrFun h1 c
          have h2' : A r2 c = rowVec k c := (congrFun hk_eq c).symm
          rw [h0', h1', h2'] at hc
          exact hc
        let B : Fin (n + 2) → Fin 8 → Fin 2 := fun r => A r.succ
        have hB_valid : isValid n B := by
          refine ⟨fun r => hA.1 r.succ, fun c r => ?_⟩
          exact hA.2 c ⟨r.1 + 1, by omega⟩
        have hB0 : B 0 = rowVec j := h1
        have hB1 : B 1 = rowVec k := hk_eq.symm
        ⟨⟨k, hcomp⟩, ⟨B, hB_valid, hB0, hB1⟩⟩
      invFun := fun ⟨⟨k, hcomp⟩, ⟨B, hB, hB0, hB1⟩⟩ =>
        let A : Fin (n + 3) → Fin 8 → Fin 2 := consRow (rowVec i) B
        have hA_valid : isValid (n + 1) A := by
          refine ⟨fun r => ?_, fun c r => ?_⟩
          · rcases r with ⟨_ | m, hm⟩
            · exact rowVec_valid i
            · exact hB.1 ⟨m, by omega⟩
          · rcases r with ⟨_ | m, hm⟩
            · change avoids3 (rowVec i c) (B 0 c) (B 1 c)
              rw [hB0, hB1]
              exact hcomp c
            · exact hB.2 c ⟨m, by omega⟩
        ⟨A, hA_valid, rfl, hB0⟩
      left_inv := fun ⟨A, hA, h0, h1⟩ => by
        apply Subtype.ext
        funext r
        rcases r with ⟨_ | m, hm⟩
        · exact h0.symm
        · rfl
      right_inv := fun ⟨⟨k, hcomp⟩, ⟨B, hB, hB0, hB1⟩⟩ => by
        dsimp only
        have hk : ∀ hp : isValidRow (consRow (rowVec i) B ⟨2, by omega⟩),
            validRowEquiv.symm ⟨consRow (rowVec i) B ⟨2, by omega⟩, hp⟩ = k := by
          intro hp
          apply validRowEquiv.injective
          rw [validRowEquiv.apply_symm_apply]
          exact Subtype.ext hB1
        refine Sigma.ext (Subtype.ext (hk _)) (validArrFrom_heq rfl (hk _) ?_)
        funext r
        rfl }

private def F (d : Fin 9) (n : ℕ) : ℚ :=
  let x : ℚ := n
  match d.1 with
  | 0 => 1
  | 1 => x + 1
  | 2 => (x + 1) * (x + 2) / 2
  | 3 => (x + 1) * (x + 2) * (x + 3) / 6
  | 4 => (x + 1) * (x + 2) * (x + 3) * (x + 4) / 24
  | 5 => (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) / 120
  | 6 => (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) / 720
  | 7 => (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) / 5040
  | _ =>
    1 + x + 2 * (
      x * (x + 1) / 2
      + x * (x + 1) * (x + 2) / 6
      + x * (x + 1) * (x + 2) * (x + 3) / 24
      + x * (x + 1) * (x + 2) * (x + 3) * (x + 4) / 120
      + x * (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) / 720
      + x * (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) / 5040
      + x * (x + 1) * (x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) / 40320)

private lemma F_zero (d : Fin 9) : F d 0 = 1 := by
  fin_cases d <;> norm_num [F]

private lemma F_step (D : Fin 9) (n : ℕ) :
    ∑ d : Fin 9, (expectedTrans D.1 d.1 : ℚ) * F d n = F D (n + 1) := by
  fin_cases D <;>
    simp [Fin.sum_univ_succ, expectedTrans, F] <;>
    ring

private lemma extCount_eq_F (n : ℕ) :
    ∀ i j : Fin 16, (extCount n i j : ℚ) = F (cycDistFin i j) n := by
  induction n with
  | zero =>
    intro i j
    rw [extCount_zero, F_zero]
    norm_num
  | succ n ih =>
    intro i j
    rw [extCount_succ]
    push_cast
    simp_rw [ih]
    have hgroup :
        ∑ k ∈ Finset.univ.filter (compat i j), F (cycDistFin j k) n =
        ∑ d : Fin 9,
          ((Finset.univ.filter (fun k : Fin 16 => compat i j k ∧ cycDistFin j k = d)).card : ℚ) *
          F d n := by
      have h1 := Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ.filter (compat i j))
        (t := (Finset.univ : Finset (Fin 9)))
        (g := fun k => cycDistFin j k)
        (f := fun k => F (cycDistFin j k) n)
        (fun _ _ => Finset.mem_univ _)
      rw [← h1]
      refine Finset.sum_congr rfl fun d _ => ?_
      have hfilt :
          (Finset.univ.filter (compat i j)).filter (fun k => cycDistFin j k = d) =
          Finset.univ.filter (fun k : Fin 16 => compat i j k ∧ cycDistFin j k = d) := by
        ext k; simp
      rw [hfilt]
      calc
        ∑ k ∈ Finset.univ.filter (fun k : Fin 16 => compat i j k ∧ cycDistFin j k = d),
            F (cycDistFin j k) n
          = ∑ _k ∈ Finset.univ.filter (fun k : Fin 16 => compat i j k ∧ cycDistFin j k = d),
              F d n := by
            refine Finset.sum_congr rfl fun k hk => ?_
            simp only [Finset.mem_filter] at hk
            rw [hk.2.2]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [hgroup]
    simp_rw [trans_count]
    exact F_step (cycDistFin i j) n

private def polyVal (x : ℚ) : ℚ :=
  (322560 + 643536 * x + 509004 * x ^ 2 + 214676 * x ^ 3 + 54649 * x ^ 4
    + 8624 * x ^ 5 + 826 * x ^ 6 + 44 * x ^ 7 + x ^ 8) / 1260

private lemma card_valid_eq_poly (n : ℕ) :
    (Fintype.card {A : Fin (n + 2) → Fin 8 → Fin 2 // isValid n A} : ℚ) = polyVal (n : ℚ) := by
  rw [card_valid_eq_sum]
  push_cast
  simp_rw [extCount_eq_F]
  have hgroup :
      ∑ p : Fin 16 × Fin 16, F (cycDistFin p.1 p.2) n =
      ∑ d : Fin 9,
        ((Finset.univ.filter (fun p : Fin 16 × Fin 16 => cycDistFin p.1 p.2 = d)).card : ℚ) *
        F d n := by
    have h1 := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin 16 × Fin 16)))
      (t := (Finset.univ : Finset (Fin 9)))
      (g := fun p : Fin 16 × Fin 16 => cycDistFin p.1 p.2)
      (f := fun p : Fin 16 × Fin 16 => F (cycDistFin p.1 p.2) n)
      (fun _ _ => Finset.mem_univ _)
    rw [← h1]
    refine Finset.sum_congr rfl fun d _ => ?_
    calc
      ∑ p ∈ Finset.univ.filter (fun p : Fin 16 × Fin 16 => cycDistFin p.1 p.2 = d),
          F (cycDistFin p.1 p.2) n
        = ∑ _p ∈ Finset.univ.filter (fun p : Fin 16 × Fin 16 => cycDistFin p.1 p.2 = d),
            F d n := by
          refine Finset.sum_congr rfl fun p hp => ?_
          simp only [Finset.mem_filter] at hp
          rw [hp.2]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hgroup]
  simp_rw [init_count]
  simp [Fin.sum_univ_succ, F, polyVal]
  ring

private lemma a_eq_poly {n : ℕ} (hn : 0 < n) : (a n : ℚ) = polyVal (n : ℚ) := by
  have hne : n ≠ 0 := by omega
  simp only [a, hne, ↓reduceIte]
  exact card_valid_eq_poly n

private lemma a_vals :
    (a 0 : ℚ) = 0 ∧ (a 1 : ℚ) = 1392 ∧ (a 2 : ℚ) = 5216 ∧ (a 3 : ℚ) = 15760 ∧
    (a 4 : ℚ) = 41088 ∧ (a 5 : ℚ) = 95984 ∧ (a 6 : ℚ) = 205792 ∧ (a 7 : ℚ) = 411696 ∧
    (a 8 : ℚ) = 777760 ∧ (a 9 : ℚ) = 1400080 := by
  refine ⟨by simp [a], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [a_eq_poly (by omega)]; unfold polyVal; norm_num)

private lemma recurrence_part :
    ∀ n : ℕ, 9 < n →
      (a n : ℤ) =
        9 * (a (n - 1) : ℤ) - 36 * (a (n - 2) : ℤ) + 84 * (a (n - 3) : ℤ)
        - 126 * (a (n - 4) : ℤ) + 126 * (a (n - 5) : ℤ) - 84 * (a (n - 6) : ℤ)
        + 36 * (a (n - 7) : ℤ) - 9 * (a (n - 8) : ℤ) + (a (n - 9) : ℤ) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  have hq :
      (a (m + 10) : ℚ) =
        9 * (a (m + 9) : ℚ) - 36 * (a (m + 8) : ℚ) + 84 * (a (m + 7) : ℚ)
        - 126 * (a (m + 6) : ℚ) + 126 * (a (m + 5) : ℚ) - 84 * (a (m + 4) : ℚ)
        + 36 * (a (m + 3) : ℚ) - 9 * (a (m + 2) : ℚ) + (a (m + 1) : ℚ) := by
    rw [a_eq_poly (by omega), a_eq_poly (by omega), a_eq_poly (by omega),
        a_eq_poly (by omega), a_eq_poly (by omega), a_eq_poly (by omega),
        a_eq_poly (by omega), a_eq_poly (by omega), a_eq_poly (by omega),
        a_eq_poly (by omega)]
    unfold polyVal
    push_cast
    ring
  have h1 : m + 10 - 1 = m + 9 := by omega
  have h2 : m + 10 - 2 = m + 8 := by omega
  have h3 : m + 10 - 3 = m + 7 := by omega
  have h4 : m + 10 - 4 = m + 6 := by omega
  have h5 : m + 10 - 5 = m + 5 := by omega
  have h6 : m + 10 - 6 = m + 4 := by omega
  have h7 : m + 10 - 7 = m + 3 := by omega
  have h8 : m + 10 - 8 = m + 2 := by omega
  have h9 : m + 10 - 9 = m + 1 := by omega
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
  exact_mod_cast hq

private lemma coeff_mul_X_pow_rat (f : PowerSeries ℚ) (k n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X ^ k) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  induction k generalizing n with
  | zero =>
    simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc]
    cases n with
    | zero =>
      simp
    | succ m =>
      rw [PowerSeries.coeff_succ_mul_X, ih m]
      have hiff : k ≤ m ↔ k + 1 ≤ m + 1 := by omega
      have hsub : m - k = m + 1 - (k + 1) := by omega
      simp only [hiff, hsub]

private lemma coeff_X_pow_rat (k n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℚ) ^ k) = if n = k then 1 else 0 := by
  rw [PowerSeries.coeff_X_pow]

private lemma gf_coeff_lt10 (f : ℕ → ℚ)
    (h0 : f 0 = 0) (h1 : f 1 = 1392) (h2 : f 2 = 5216) (h3 : f 3 = 15760)
    (h4 : f 4 = 41088) (h5 : f 5 = 95984) (h6 : f 6 = 205792) (h7 : f 7 = 411696)
    (h8 : f 8 = 777760) (h9 : f 9 = 1400080) {n : ℕ} (hn : n < 10) :
    f n - 9 * (if 1 ≤ n then f (n - 1) else 0)
        + 36 * (if 2 ≤ n then f (n - 2) else 0)
        - 84 * (if 3 ≤ n then f (n - 3) else 0)
        + 126 * (if 4 ≤ n then f (n - 4) else 0)
        - 126 * (if 5 ≤ n then f (n - 5) else 0)
        + 84 * (if 6 ≤ n then f (n - 6) else 0)
        - 36 * (if 7 ≤ n then f (n - 7) else 0)
        + 9 * (if 8 ≤ n then f (n - 8) else 0)
        - (if 9 ≤ n then f (n - 9) else 0) =
      1392 * (if n = 1 then 1 else 0)
        - 7312 * (if n = 2 then 1 else 0)
        + 18928 * (if n = 3 then 1 else 0)
        - 29904 * (if n = 4 then 1 else 0)
        + 30800 * (if n = 5 then 1 else 0)
        - 20912 * (if n = 6 then 1 else 0)
        + 9072 * (if n = 7 then 1 else 0)
        - 2288 * (if n = 8 then 1 else 0)
        + 256 * (if n = 9 then 1 else 0) := by
  interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

private lemma gf_part :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 9 =
      16 * PowerSeries.X *
        (87 - 457 * PowerSeries.X + 1183 * PowerSeries.X ^ 2 - 1869 * PowerSeries.X ^ 3
          + 1925 * PowerSeries.X ^ 4 - 1307 * PowerSeries.X ^ 5 + 567 * PowerSeries.X ^ 6
          - 143 * PowerSeries.X ^ 7 + 16 * PowerSeries.X ^ 8) := by
  set A : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
  have hlhs :
      A * (1 - PowerSeries.X) ^ 9 =
        A - PowerSeries.C (9 : ℚ) * (A * PowerSeries.X ^ 1)
          + PowerSeries.C (36 : ℚ) * (A * PowerSeries.X ^ 2)
          - PowerSeries.C (84 : ℚ) * (A * PowerSeries.X ^ 3)
          + PowerSeries.C (126 : ℚ) * (A * PowerSeries.X ^ 4)
          - PowerSeries.C (126 : ℚ) * (A * PowerSeries.X ^ 5)
          + PowerSeries.C (84 : ℚ) * (A * PowerSeries.X ^ 6)
          - PowerSeries.C (36 : ℚ) * (A * PowerSeries.X ^ 7)
          + PowerSeries.C (9 : ℚ) * (A * PowerSeries.X ^ 8)
          - A * PowerSeries.X ^ 9 := by
    simp only [map_ofNat]
    ring
  have hrhs :
      (16 : PowerSeries ℚ) * PowerSeries.X *
        (87 - 457 * PowerSeries.X + 1183 * PowerSeries.X ^ 2 - 1869 * PowerSeries.X ^ 3
          + 1925 * PowerSeries.X ^ 4 - 1307 * PowerSeries.X ^ 5 + 567 * PowerSeries.X ^ 6
          - 143 * PowerSeries.X ^ 7 + 16 * PowerSeries.X ^ 8) =
        PowerSeries.C (1392 : ℚ) * PowerSeries.X ^ 1
          - PowerSeries.C (7312 : ℚ) * PowerSeries.X ^ 2
          + PowerSeries.C (18928 : ℚ) * PowerSeries.X ^ 3
          - PowerSeries.C (29904 : ℚ) * PowerSeries.X ^ 4
          + PowerSeries.C (30800 : ℚ) * PowerSeries.X ^ 5
          - PowerSeries.C (20912 : ℚ) * PowerSeries.X ^ 6
          + PowerSeries.C (9072 : ℚ) * PowerSeries.X ^ 7
          - PowerSeries.C (2288 : ℚ) * PowerSeries.X ^ 8
          + PowerSeries.C (256 : ℚ) * PowerSeries.X ^ 9 := by
    simp only [map_ofNat]
    ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, coeff_mul_X_pow_rat,
    coeff_X_pow_rat, PowerSeries.coeff_mk, A]
  by_cases hn : n < 10
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := a_vals
    exact gf_coeff_lt10 (fun k => (a k : ℚ)) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    simp only [
      show 1 ≤ m + 10 by omega, show 2 ≤ m + 10 by omega, show 3 ≤ m + 10 by omega,
      show 4 ≤ m + 10 by omega, show 5 ≤ m + 10 by omega, show 6 ≤ m + 10 by omega,
      show 7 ≤ m + 10 by omega, show 8 ≤ m + 10 by omega, show 9 ≤ m + 10 by omega,
      show m + 10 ≠ 1 by omega, show m + 10 ≠ 2 by omega, show m + 10 ≠ 3 by omega,
      show m + 10 ≠ 4 by omega, show m + 10 ≠ 5 by omega, show m + 10 ≠ 6 by omega,
      show m + 10 ≠ 7 by omega, show m + 10 ≠ 8 by omega, show m + 10 ≠ 9 by omega,
      show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
      show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega,
      show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega,
      show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega,
      show m + 10 - 9 = m + 1 by omega,
      ↓reduceIte]
    rw [a_eq_poly (by omega), a_eq_poly (by omega), a_eq_poly (by omega),
        a_eq_poly (by omega), a_eq_poly (by omega), a_eq_poly (by omega),
        a_eq_poly (by omega), a_eq_poly (by omega), a_eq_poly (by omega),
        a_eq_poly (by omega)]
    unfold polyVal
    push_cast
    ring

end OMA.S_oeis_a202050_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a202050.main :=
  ⟨OMA.S_oeis_a202050_Proof.gf_part, OMA.S_oeis_a202050_Proof.recurrence_part⟩
