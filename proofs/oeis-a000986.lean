import OMAStatements.S_oeis_a000986

section Proof

open Finset

private def V (α : Type*) [Fintype α] [DecidableEq α] : Finset (Matrix α α (Fin 2)) :=
  Finset.univ.filter (fun M => M.IsSymm ∧ ∀ i, ∑ j, (M i j : ℕ) = 2)

private lemma mem_V_iff {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α (Fin 2)) :
    M ∈ V α ↔ M.IsSymm ∧ ∀ i, ∑ j, (M i j : ℕ) = 2 := by
  simp [V]

private def l (n : ℕ) : ℕ :=
  if h : 0 < n then ((V (Fin n)).filter (fun M => M ⟨0, h⟩ ⟨0, h⟩ = 1)).card else 0

private def nl (n : ℕ) : ℕ :=
  if h : 0 < n then ((V (Fin n)).filter (fun M => M ⟨0, h⟩ ⟨0, h⟩ = 0)).card else 0

private lemma fin2_val_eq (x : Fin 2) : (x : ℕ) = if x = 1 then 1 else 0 := by
  fin_cases x <;> rfl

private lemma fin2_val_one : ((1 : Fin 2) : ℕ) = 1 := rfl

private lemma fin2_val_zero : ((0 : Fin 2) : ℕ) = 0 := rfl

private lemma fin2_ne_one_iff (x : Fin 2) : x ≠ 1 ↔ x = 0 := by
  fin_cases x <;> decide

private lemma fin2_ne_zero_iff (x : Fin 2) : x ≠ 0 ↔ x = 1 := by
  fin_cases x <;> decide

private lemma sum_fin2_eq_card {α : Type*} (T : Finset α) (f : α → Fin 2) :
    ∑ j ∈ T, (f j : ℕ) = (T.filter (fun j => f j = 1)).card := by
  simp only [fin2_val_eq, Finset.sum_boole, Nat.cast_id]

private lemma isSymm_iff {α : Type*} (M : Matrix α α (Fin 2)) :
    M.IsSymm ↔ ∀ i j, M j i = M i j :=
  ⟨fun h i j => by
      simpa [Matrix.transpose_apply] using congrArg (fun N : Matrix α α (Fin 2) => N i j) h,
   fun h => Matrix.ext fun i j => h i j⟩

private lemma card_ne_eq {α : Type*} [Fintype α] [DecidableEq α] (z : α) :
    Fintype.card {x : α // x ≠ z} = Fintype.card α - 1 := by
  have h1 : Fintype.card {x : α // x = z} = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨z, rfl⟩, fun y => Subtype.ext y.2⟩
  rw [Fintype.card_subtype_compl, h1]

private lemma a_eq_V_card {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (h : Fintype.card α = n) : OMA.S_oeis_a000986.a n = (V α).card := by
  unfold OMA.S_oeis_a000986.a
  let e : α ≃ Fin n := Fintype.equivFinOfCardEq h
  refine Finset.card_bij (fun M _ => Matrix.of fun i j => M (e i) (e j)) ?_ ?_ ?_
  · intro M hM
    rw [Finset.mem_filter] at hM
    rw [mem_V_iff]
    rcases hM.2 with ⟨hs, hr⟩
    rw [isSymm_iff] at hs ⊢
    refine ⟨fun i j => by simp [hs], fun i => ?_⟩
    simpa [Equiv.sum_comp e (fun j => (M (e i) j : ℕ))] using hr (e i)
  · intro M₁ _ M₂ _ heq
    refine Matrix.ext fun i j => ?_
    have := congrArg (fun M : Matrix α α (Fin 2) => M (e.symm i) (e.symm j)) heq
    simpa using this
  · intro M' hM'
    rw [mem_V_iff] at hM'
    refine ⟨Matrix.of fun i j => M' (e.symm i) (e.symm j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rcases hM' with ⟨hs, hr⟩
      rw [isSymm_iff] at hs ⊢
      refine ⟨fun i j => by simp [hs], fun i => ?_⟩
      simpa [Equiv.sum_comp e.symm (fun j => (M' (e.symm i) j : ℕ))] using hr (e.symm i)
    · refine Matrix.ext fun i j => ?_
      simp

private lemma Vdiag_card_eq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (x : α) :
    ((V α).filter (fun M => M x x = 1)).card =
      ((V β).filter (fun M => M (e x) (e x) = 1)).card := by
  refine Finset.card_bij (fun M _ => Matrix.of fun i j => M (e.symm i) (e.symm j)) ?_ ?_ ?_
  · intro M hM
    rw [Finset.mem_filter, mem_V_iff] at hM
    rw [Finset.mem_filter, mem_V_iff]
    rcases hM with ⟨⟨hs, hr⟩, hxx⟩
    rw [isSymm_iff] at hs ⊢
    refine ⟨⟨fun i j => by simp [hs], fun i => ?_⟩, by simpa using hxx⟩
    simpa [Equiv.sum_comp e.symm (fun j => (M (e.symm i) j : ℕ))] using hr (e.symm i)
  · intro M₁ _ M₂ _ heq
    refine Matrix.ext fun i j => ?_
    have := congrArg (fun M : Matrix β β (Fin 2) => M (e i) (e j)) heq
    simpa using this
  · intro M' hM'
    rw [Finset.mem_filter, mem_V_iff] at hM'
    rcases hM' with ⟨⟨hs, hr⟩, hxx⟩
    rw [isSymm_iff] at hs
    refine ⟨Matrix.of fun i j => M' (e i) (e j), ?_, Matrix.ext fun i j => by simp⟩
    rw [Finset.mem_filter, mem_V_iff, isSymm_iff]
    refine ⟨⟨fun i j => by simp [hs], fun i => ?_⟩, by simpa using hxx⟩
    simpa [Equiv.sum_comp e (fun j => (M' (e i) j : ℕ))] using hr (e i)

private lemma Vdiag_card_const {α : Type*} [Fintype α] [DecidableEq α] (x y : α) :
    ((V α).filter (fun M => M x x = 1)).card =
      ((V α).filter (fun M => M y y = 1)).card := by
  have h := Vdiag_card_eq (Equiv.swap x y) x
  simpa using h

private lemma l_eq_Vdiag_card {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (x : α) (h : Fintype.card α = n) :
    l n = ((V α).filter (fun M => M x x = 1)).card := by
  have hpos : 0 < n := by
    rw [← h]
    exact Fintype.card_pos_iff.mpr ⟨x⟩
  unfold l
  simp only [hpos, ↓reduceDIte]
  let e : α ≃ Fin n := Fintype.equivFinOfCardEq h
  rw [Vdiag_card_const x (e.symm ⟨0, hpos⟩), Vdiag_card_eq e (e.symm ⟨0, hpos⟩)]
  simp

private lemma a_eq_l_add_nl {n : ℕ} (hn : 0 < n) :
    OMA.S_oeis_a000986.a n = l n + nl n := by
  rw [a_eq_V_card (Fintype.card_fin n)]
  unfold l nl
  simp only [hn, ↓reduceDIte]
  rw [add_comm,
    ← Finset.card_filter_add_card_filter_not (s := V (Fin n)) (fun M => M ⟨0, hn⟩ ⟨0, hn⟩ = 0)]
  congr 1
  exact congrArg Finset.card (Finset.ext fun M => by simp [fin2_ne_zero_iff])

private lemma sum_univ_sub {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : α → ℕ) :
    ∑ x : α, f x = (∑ x ∈ S, f x) + ∑ y : {x : α // x ∉ S}, f y.1 := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S) f]
  congr 1
  · congr 1
    ext x
    simp
  · refine (Finset.sum_bij (fun y _ => y.1) ?_ ?_ ?_ ?_).symm
    · intro y _
      simp [y.2]
    · intro y₁ _ y₂ _ heq
      exact Subtype.ext heq
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
    · intro _ _
      rfl

private lemma sum_univ_ne {α : Type*} [Fintype α] [DecidableEq α]
    (z : α) (f : α → ℕ) :
    ∑ x : α, f x = f z + ∑ y : {x : α // x ≠ z}, f y.1 := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ z)]
  congr 1
  refine (Finset.sum_bij (fun y _ => y.1) ?_ ?_ ?_ ?_).symm
  · intro y _
    exact Finset.mem_erase.mpr ⟨y.2, Finset.mem_univ _⟩
  · intro y₁ _ y₂ _ heq
    exact Subtype.ext heq
  · intro x hx
    exact ⟨⟨x, (Finset.mem_erase.mp hx).1⟩, Finset.mem_univ _, rfl⟩
  · intro _ _
    rfl

private lemma row_zero_of_diag_one {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matrix α α (Fin 2)} (hM : M ∈ V α) {x : α} (hxx : M x x = 1) :
    ∃! v, v ≠ x ∧ M x v = 1 := by
  rw [mem_V_iff] at hM
  have hr := hM.2 x
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hxx] at hr
  change 1 + ∑ j ∈ Finset.univ.erase x, (M x j : ℕ) = 2 at hr
  rw [sum_fin2_eq_card] at hr
  have hcard : ((Finset.univ.erase x).filter (fun j => M x j = 1)).card = 1 := by omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  refine ⟨v, ?_, fun w hw => ?_⟩
  · have hmem : v ∈ (Finset.univ.erase x).filter (fun j => M x j = 1) := by rw [hv]; simp
    rw [Finset.mem_filter, Finset.mem_erase] at hmem
    exact ⟨hmem.1.1, hmem.2⟩
  · have hmem : w ∈ (Finset.univ.erase x).filter (fun j => M x j = 1) := by
      rw [Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨hw.1, Finset.mem_univ _⟩, hw.2⟩
    rw [hv, Finset.mem_singleton] at hmem
    exact hmem

private lemma off_diag_zero_of_two_ones {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matrix α α (Fin 2)} (hM : M ∈ V α) {x u v : α} (huv : u ≠ v)
    (hu : M x u = 1) (hv : M x v = 1) :
    ∀ w, w ≠ u → w ≠ v → M x w = 0 := by
  rw [mem_V_iff] at hM
  have hr := hM.2 x
  have hmemu : u ∈ Finset.univ := Finset.mem_univ u
  have hmemv : v ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩
  rw [← Finset.add_sum_erase _ _ hmemu, ← Finset.add_sum_erase _ _ hmemv, hu, hv] at hr
  change 1 + (1 + ∑ w ∈ (Finset.univ.erase u).erase v, (M x w : ℕ)) = 2 at hr
  have hsum0 : ∑ w ∈ (Finset.univ.erase u).erase v, (M x w : ℕ) = 0 := by omega
  intro w hwu hwv
  have hwmem : w ∈ (Finset.univ.erase u).erase v :=
    Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr ⟨hwu, Finset.mem_univ w⟩⟩
  have := Finset.sum_eq_zero_iff.mp hsum0 w hwmem
  exact Fin.ext (by simpa using this)

private lemma eq1_diag1 {k : ℕ} (z v : Fin k) (hvz : v ≠ z) :
    ((V (Fin k)).filter (fun M => M z z = 1 ∧ M z v = 1 ∧ M v v = 1)).card =
      OMA.S_oeis_a000986.a (k - 2) := by
  let S : Finset (Fin k) := {z, v}
  have hScard : S.card = 2 := Finset.card_pair hvz.symm
  let β := {x : Fin k // x ∉ S}
  have hβcard : Fintype.card β = k - 2 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hScard]
  rw [a_eq_V_card hβcard]
  refine Finset.card_bij (fun M _ => Matrix.of fun x y => M x.1 y.1) ?_ ?_ ?_
  · intro M hM
    rw [Finset.mem_filter, mem_V_iff] at hM
    rw [mem_V_iff]
    rcases hM with ⟨⟨hs, hr⟩, hzz, hzv, hvv⟩
    have hMV : M ∈ V (Fin k) := (mem_V_iff M).mpr ⟨hs, hr⟩
    rw [isSymm_iff] at hs ⊢
    have hz0 : ∀ w, w ≠ z → w ≠ v → M z w = 0 := off_diag_zero_of_two_ones hMV hvz.symm hzz hzv
    have hv0 : ∀ w, w ≠ z → w ≠ v → M v w = 0 :=
      off_diag_zero_of_two_ones hMV hvz.symm (by simpa [hs] using hzv) hvv
    refine ⟨fun x y => by simp [hs], fun x => ?_⟩
    have hxS : x.1 ∉ S := x.2
    have hxz : x.1 ≠ z := fun h => hxS (by simp [S, h])
    have hxv : x.1 ≠ v := fun h => hxS (by simp [S, h])
    have hsum := hr x.1
    rw [sum_univ_sub S] at hsum
    have hS0 : ∑ w ∈ S, (M x.1 w : ℕ) = 0 := by
      rw [Finset.sum_pair hvz.symm, hs z x.1, hz0 x.1 hxz hxv, hs v x.1, hv0 x.1 hxz hxv]
      rfl
    rw [hS0, zero_add] at hsum
    simpa using hsum
  · intro M₁ hM₁ M₂ hM₂ heq
    rw [Finset.mem_filter, mem_V_iff] at hM₁ hM₂
    rcases hM₁ with ⟨⟨hs₁', hr₁⟩, hzz₁, hzv₁, hvv₁⟩
    rcases hM₂ with ⟨⟨hs₂', hr₂⟩, hzz₂, hzv₂, hvv₂⟩
    have hMV₁ : M₁ ∈ V (Fin k) := (mem_V_iff M₁).mpr ⟨hs₁', hr₁⟩
    have hMV₂ : M₂ ∈ V (Fin k) := (mem_V_iff M₂).mpr ⟨hs₂', hr₂⟩
    have hs₁ := (isSymm_iff M₁).mp hs₁'
    have hs₂ := (isSymm_iff M₂).mp hs₂'
    have hz0₁ := off_diag_zero_of_two_ones hMV₁ hvz.symm hzz₁ hzv₁
    have hz0₂ := off_diag_zero_of_two_ones hMV₂ hvz.symm hzz₂ hzv₂
    have hv0₁ := off_diag_zero_of_two_ones hMV₁ hvz.symm (by simpa [hs₁] using hzv₁) hvv₁
    have hv0₂ := off_diag_zero_of_two_ones hMV₂ hvz.symm (by simpa [hs₂] using hzv₂) hvv₂
    refine Matrix.ext fun i j => ?_
    rcases eq_or_ne i z with hiz | hiz
    · rcases eq_or_ne j z with hjz | hjz
      · rw [hiz, hjz, hzz₁, hzz₂]
      · rcases eq_or_ne j v with hjv | hjv
        · rw [hiz, hjv, hzv₁, hzv₂]
        · rw [hiz, hz0₁ j hjz hjv, hz0₂ j hjz hjv]
    · rcases eq_or_ne i v with hiv | hiv
      · rcases eq_or_ne j z with hjz | hjz
        · rw [hiv, hjz, hs₁ z v, hs₂ z v, hzv₁, hzv₂]
        · rcases eq_or_ne j v with hjv | hjv
          · rw [hiv, hjv, hvv₁, hvv₂]
          · rw [hiv, hv0₁ j hjz hjv, hv0₂ j hjz hjv]
      · rcases eq_or_ne j z with hjz | hjz
        · rw [hjz, hs₁ z i, hs₂ z i, hz0₁ i hiz hiv, hz0₂ i hiz hiv]
        · rcases eq_or_ne j v with hjv | hjv
          · rw [hjv, hs₁ v i, hs₂ v i, hv0₁ i hiz hiv, hv0₂ i hiz hiv]
          · have hiS : i ∉ S := by simp [S, hiz, hiv]
            have hjS : j ∉ S := by simp [S, hjz, hjv]
            have := congrArg (fun M : Matrix β β (Fin 2) => M ⟨i, hiS⟩ ⟨j, hjS⟩) heq
            simpa using this
  · intro M' hM'
    rw [mem_V_iff] at hM'
    rcases hM' with ⟨hs', hr'⟩
    rw [isSymm_iff] at hs'
    let M : Matrix (Fin k) (Fin k) (Fin 2) := Matrix.of fun i j =>
      if hi : i ∈ S then
        if j ∈ S then 1 else 0
      else
        if hj : j ∈ S then 0 else M' ⟨i, hi⟩ ⟨j, hj⟩
    have hzS : z ∈ S := Finset.mem_insert_self z _
    have hvS : v ∈ S := Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
    have hM_zz : M z z = 1 := by simp [M, hzS]
    have hM_zv : M z v = 1 := by simp [M, hzS, hvS]
    have hM_vv : M v v = 1 := by simp [M, hvS]
    have hMsymm : M.IsSymm := (isSymm_iff M).mpr fun i j => by
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [M, hi, hj, hs']
    have hMrow : ∀ i, ∑ j, (M i j : ℕ) = 2 := fun i => by
      rw [sum_univ_sub S]
      by_cases hiS : i ∈ S
      · have hsub0 : ∑ y : β, (M i y.1 : ℕ) = 0 := Finset.sum_eq_zero fun y _ => by
          simp [M, hiS, y.2]
        have hSsum : ∑ x ∈ S, (M i x : ℕ) = 2 := by
          rw [Finset.sum_pair hvz.symm]
          simp [M, hiS, hzS, hvS]
        rw [hSsum, hsub0]
      · have hSsum : ∑ x ∈ S, (M i x : ℕ) = 0 := Finset.sum_eq_zero fun x hx => by
          simp [M, hiS, hx]
        have hsub2 : ∑ y : β, (M i y.1 : ℕ) = 2 := by
          have := hr' ⟨i, hiS⟩
          have hcongr : ∑ y : β, (M i y.1 : ℕ) = ∑ y : β, (M' ⟨i, hiS⟩ y : ℕ) :=
            Finset.sum_congr rfl fun y _ => by simp [M, hiS, y.2]
          rw [hcongr, this]
        rw [hSsum, zero_add, hsub2]
    refine ⟨M, ?_, Matrix.ext fun x y => by simp [M, x.2, y.2]⟩
    rw [Finset.mem_filter, mem_V_iff]
    exact ⟨⟨hMsymm, hMrow⟩, hM_zz, hM_zv, hM_vv⟩

private lemma eq1_diag0 {k : ℕ} (z v : Fin k) (hvz : v ≠ z) :
    ((V (Fin k)).filter (fun M => M z z = 1 ∧ M z v = 1 ∧ M v v = 0)).card = l (k - 1) := by
  let γ := {x : Fin k // x ≠ z}
  have hγcard : Fintype.card γ = k - 1 := by
    rw [card_ne_eq z, Fintype.card_fin]
  let v' : γ := ⟨v, hvz⟩
  rw [l_eq_Vdiag_card v' hγcard]
  refine Finset.card_bij
    (fun M _ => Matrix.of fun x y => if x = v' ∧ y = v' then 1 else M x.1 y.1) ?_ ?_ ?_
  · intro M hM
    rw [Finset.mem_filter, mem_V_iff] at hM
    rw [Finset.mem_filter, mem_V_iff]
    rcases hM with ⟨⟨hs, hr⟩, hzz, hzv, hvv⟩
    have hMV : M ∈ V (Fin k) := (mem_V_iff M).mpr ⟨hs, hr⟩
    rw [isSymm_iff] at hs ⊢
    have hz0 : ∀ w, w ≠ z → w ≠ v → M z w = 0 := off_diag_zero_of_two_ones hMV hvz.symm hzz hzv
    refine ⟨⟨fun x y => by
        by_cases hx : x = v' <;> by_cases hy : y = v' <;> simp [hx, hy, hs], fun x => ?_⟩, by simp⟩
    have hxsum := hr x.1
    rw [sum_univ_ne z] at hxsum
    by_cases hxv : x = v'
    · subst hxv
      have hMvz : M v' z = 1 := by simpa [hs] using hzv
      have hMvv : M v' v' = 0 := hvv
      rw [hMvz, fin2_val_one] at hxsum
      change 1 + ∑ y : γ, (M v'.1 y.1 : ℕ) = 2 at hxsum
      have hsub1 : ∑ y : γ, (M v'.1 y.1 : ℕ) = 1 := by omega
      have hsub1' : ∑ y ∈ Finset.univ.erase v', (M v'.1 y.1 : ℕ) = 1 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v'), hMvv, fin2_val_zero, zero_add] at hsub1
        exact hsub1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v')]
      have hhead :
          ((Matrix.of (fun a b : γ => if a = v' ∧ b = v' then (1 : Fin 2) else M a.1 b.1))
            v' v' : ℕ) = 1 := by simp
      have hrest :
          ∑ y ∈ Finset.univ.erase v',
            ((Matrix.of (fun a b : γ => if a = v' ∧ b = v' then (1 : Fin 2) else M a.1 b.1))
              v' y : ℕ) =
            ∑ y ∈ Finset.univ.erase v', (M v'.1 y.1 : ℕ) :=
        Finset.sum_congr rfl fun y hy => by simp [(Finset.mem_erase.mp hy).1]
      rw [hhead, hrest, hsub1']
    · have hMxz : M x.1 z = 0 := by rw [hs z x.1]; exact hz0 x.1 x.2 (fun h => hxv (Subtype.ext h))
      rw [hMxz, fin2_val_zero, zero_add] at hxsum
      have hcongr :
          ∑ y : γ,
            ((Matrix.of (fun a b : γ => if a = v' ∧ b = v' then (1 : Fin 2) else M a.1 b.1))
              x y : ℕ) =
            ∑ y : γ, (M x.1 y.1 : ℕ) :=
        Finset.sum_congr rfl fun y _ => by simp [hxv]
      rw [hcongr, hxsum]
  · intro M₁ hM₁ M₂ hM₂ heq
    rw [Finset.mem_filter, mem_V_iff] at hM₁ hM₂
    rcases hM₁ with ⟨⟨hs₁', hr₁⟩, hzz₁, hzv₁, hvv₁⟩
    rcases hM₂ with ⟨⟨hs₂', hr₂⟩, hzz₂, hzv₂, hvv₂⟩
    have hMV₁ : M₁ ∈ V (Fin k) := (mem_V_iff M₁).mpr ⟨hs₁', hr₁⟩
    have hMV₂ : M₂ ∈ V (Fin k) := (mem_V_iff M₂).mpr ⟨hs₂', hr₂⟩
    have hs₁ := (isSymm_iff M₁).mp hs₁'
    have hs₂ := (isSymm_iff M₂).mp hs₂'
    have hz0₁ := off_diag_zero_of_two_ones hMV₁ hvz.symm hzz₁ hzv₁
    have hz0₂ := off_diag_zero_of_two_ones hMV₂ hvz.symm hzz₂ hzv₂
    refine Matrix.ext fun i j => ?_
    by_cases hiz : i = z <;> by_cases hjz : j = z
    · rw [hiz, hjz, hzz₁, hzz₂]
    · by_cases hjv : j = v
      · rw [hiz, hjv, hzv₁, hzv₂]
      · rw [hiz, hz0₁ j hjz hjv, hz0₂ j hjz hjv]
    · by_cases hiv : i = v
      · rw [hjz, hiv, hs₁ z v, hs₂ z v, hzv₁, hzv₂]
      · rw [hjz, hs₁ z i, hs₂ z i, hz0₁ i hiz hiv, hz0₂ i hiz hiv]
    · by_cases hboth : i = v ∧ j = v
      · rw [hboth.1, hboth.2, hvv₁, hvv₂]
      · have hnot : ¬ (⟨i, hiz⟩ = v' ∧ ⟨j, hjz⟩ = v') := by
          rintro ⟨h1, h2⟩
          exact hboth ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
        have := congrArg (fun M : Matrix γ γ (Fin 2) => M ⟨i, hiz⟩ ⟨j, hjz⟩) heq
        simpa [hnot] using this
  · intro M' hM'
    rw [Finset.mem_filter, mem_V_iff] at hM'
    rcases hM' with ⟨⟨hs', hr'⟩, hv'1⟩
    rw [isSymm_iff] at hs'
    let M : Matrix (Fin k) (Fin k) (Fin 2) := Matrix.of fun i j =>
      if hi : i = z then
        if j = z ∨ j = v then 1 else 0
      else if hj : j = z then
        if i = v then 1 else 0
      else if i = v ∧ j = v then 0
      else M' ⟨i, hi⟩ ⟨j, hj⟩
    have hM_zz : M z z = 1 := by simp [M]
    have hM_zv : M z v = 1 := by simp [M]
    have hM_vv : M v v = 0 := by simp [M, hvz]
    have hMsymm : M.IsSymm := (isSymm_iff M).mpr fun i j => by
      by_cases hiz : i = z <;> by_cases hjz : j = z <;>
        by_cases hiv : i = v <;> by_cases hjv : j = v <;>
        simp [M, hiz, hjz, hiv, hjv, hs']
    have hMrow : ∀ i, ∑ j, (M i j : ℕ) = 2 := fun i => by
      rw [sum_univ_ne z]
      by_cases hiz : i = z
      · rw [hiz]
        have hS : (M z z : ℕ) = 1 := by simp [M]
        have hsub : ∑ y : γ, (M z y.1 : ℕ) = 1 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v')]
          have hv1 : (M z v'.1 : ℕ) = 1 := by simp [M, v']
          have hrest : ∑ y ∈ Finset.univ.erase v', (M z y.1 : ℕ) = 0 :=
            Finset.sum_eq_zero fun y hy => by
              have hyv : y.1 ≠ v := fun h => (Finset.mem_erase.mp hy).1 (Subtype.ext h)
              simp [M, y.2, hyv]
          rw [hv1, hrest, add_zero]
        rw [hS, hsub]
      · let i' : γ := ⟨i, hiz⟩
        by_cases hiv : i = v
        · have hiv' : i' = v' := Subtype.ext hiv
          have hMz : (M i z : ℕ) = 1 := by simp [M, hiv]
          have hr_i' := hr' i'
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v')] at hr_i'
          have hM'vv : (M' i' v' : ℕ) = 1 := by rw [hiv', hv'1]; rfl
          rw [hM'vv] at hr_i'
          have hsub_rest : ∑ y ∈ Finset.univ.erase v', (M i y.1 : ℕ) =
              ∑ y ∈ Finset.univ.erase v', (M' i' y : ℕ) :=
            Finset.sum_congr rfl fun y hy => by
              have hyv : y.1 ≠ v := fun h => (Finset.mem_erase.mp hy).1 (Subtype.ext h)
              simp [M, hiz, y.2, hyv, i']
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v')]
          have hMvv0 : (M i v'.1 : ℕ) = 0 := by simp [M, hiv, hvz, v']
          rw [hMz, hMvv0, zero_add, hsub_rest]
          omega
        · have hMz : (M i z : ℕ) = 0 := by simp [M, hiz, hiv]
          have hr_i' := hr' i'
          have hsub_all : ∑ y : γ, (M i y.1 : ℕ) = ∑ y : γ, (M' i' y : ℕ) :=
            Finset.sum_congr rfl fun y _ => by simp [M, hiz, y.2, hiv, i']
          rw [hMz, zero_add, hsub_all, hr_i']
    refine ⟨M, ?_, Matrix.ext fun x y => ?_⟩
    · rw [Finset.mem_filter, mem_V_iff]
      exact ⟨⟨hMsymm, hMrow⟩, hM_zz, hM_zv, hM_vv⟩
    · by_cases hboth : x = v' ∧ y = v'
      · simp [hboth, hv'1]
      · have hnot : ¬ (x.1 = v ∧ y.1 = v) := fun h =>
          hboth ⟨Subtype.ext h.1, Subtype.ext h.2⟩
        simp [hboth, M, x.2, y.2, hnot]

private lemma eq1 (k : ℕ) (hk : 2 ≤ k) :
    (l k : ℤ) = ((k : ℤ) - 1) * (OMA.S_oeis_a000986.a (k - 2) : ℤ) +
      ((k : ℤ) - 1) * (l (k - 1) : ℤ) := by
  have hkpos : 0 < k := by omega
  conv_lhs => unfold l; simp only [hkpos, ↓reduceDIte]
  set z : Fin k := ⟨0, hkpos⟩
  let Lk := (V (Fin k)).filter (fun M => M z z = 1)
  have hpart_v :
      Lk.card = ∑ v ∈ Finset.univ.erase z, (Lk.filter (fun M => M z v = 1)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext M
      simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
        Finset.mem_filter, Lk]
      constructor
      · intro hM
        obtain ⟨v, hv, _⟩ := row_zero_of_diag_one hM.1 hM.2
        exact ⟨v, hv.1, hM, hv.2⟩
      · rintro ⟨v, _, hM, _⟩
        exact hM
    · intro v₁ hv₁ v₂ hv₂ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro M hM₁ hM₂
      simp only [Finset.mem_filter, Lk] at hM₁ hM₂
      rw [Finset.mem_coe, Finset.mem_erase] at hv₁ hv₂
      obtain ⟨_, _, huniq⟩ := row_zero_of_diag_one hM₁.1.1 hM₁.1.2
      exact hne ((huniq v₁ ⟨hv₁.1, hM₁.2⟩).trans (huniq v₂ ⟨hv₂.1, hM₂.2⟩).symm)
  have hsplit_v :
      ∀ v ∈ Finset.univ.erase z,
        (Lk.filter (fun M => M z v = 1)).card =
          OMA.S_oeis_a000986.a (k - 2) + l (k - 1) := by
    intro v hv
    have hvz : v ≠ z := (Finset.mem_erase.mp hv).1
    let Lv := Lk.filter (fun M => M z v = 1)
    rw [← Finset.card_filter_add_card_filter_not (s := Lv) (fun M => M v v = 1)]
    have h1 :
        (Lv.filter (fun M => M v v = 1)).card =
          ((V (Fin k)).filter (fun M => M z z = 1 ∧ M z v = 1 ∧ M v v = 1)).card :=
      congrArg Finset.card (Finset.ext fun M => by simp only [Finset.mem_filter, Lv, Lk]; tauto)
    have h0 :
        (Lv.filter (fun M => M v v ≠ 1)).card =
          ((V (Fin k)).filter (fun M => M z z = 1 ∧ M z v = 1 ∧ M v v = 0)).card :=
      congrArg Finset.card
        (Finset.ext fun M => by simp only [Finset.mem_filter, Lv, Lk, fin2_ne_one_iff]; tauto)
    rw [h1, h0, eq1_diag1 z v hvz, eq1_diag0 z v hvz]
  have hcard_l :
      Lk.card = (k - 1) * (OMA.S_oeis_a000986.a (k - 2) + l (k - 1)) := by
    rw [hpart_v, Finset.sum_congr rfl hsplit_v, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_fin, smul_eq_mul]
  have hcast := congrArg (Nat.cast (R := ℤ)) hcard_l
  push_cast [show 1 ≤ k by omega] at hcast
  linarith [hcast]

private lemma eq2_p1 {k : ℕ} (z u v : Fin k) (huz : u ≠ z) (hvz : v ≠ z) (huv : u ≠ v) :
    ((V (Fin k)).filter
      (fun M => M z z = 0 ∧ M z u = 1 ∧ M z v = 1 ∧ M u v = 1)).card =
      OMA.S_oeis_a000986.a (k - 3) := by
  let T : Finset (Fin k) := {z, u, v}
  have hzT' : z ∉ ({u, v} : Finset (Fin k)) := by simp [huz.symm, hvz.symm]
  have hTcard : T.card = 3 := by
    rw [show T = insert z {u, v} from rfl, Finset.card_insert_of_notMem hzT',
      Finset.card_pair huv]
  let δ := {x : Fin k // x ∉ T}
  have hδcard : Fintype.card δ = k - 3 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hTcard]
  rw [a_eq_V_card hδcard]
  refine Finset.card_bij (fun M _ => Matrix.of fun x y => M x.1 y.1) ?_ ?_ ?_
  · intro M hM
    rw [Finset.mem_filter, mem_V_iff] at hM
    rw [mem_V_iff]
    rcases hM with ⟨⟨hs, hr⟩, hzz, hzu, hzv, huv1⟩
    have hMV : M ∈ V (Fin k) := (mem_V_iff M).mpr ⟨hs, hr⟩
    rw [isSymm_iff] at hs ⊢
    have hzu0 : ∀ w, w ≠ u → w ≠ v → M z w = 0 := off_diag_zero_of_two_ones hMV huv hzu hzv
    have huv0 : ∀ w, w ≠ z → w ≠ v → M u w = 0 :=
      off_diag_zero_of_two_ones hMV hvz.symm (by simpa [hs] using hzu) huv1
    have hvu0 : ∀ w, w ≠ z → w ≠ u → M v w = 0 :=
      off_diag_zero_of_two_ones hMV huz.symm (by simpa [hs] using hzv) (by simpa [hs] using huv1)
    refine ⟨fun x y => by simp [hs], fun x => ?_⟩
    have hxT : x.1 ∉ T := x.2
    have hxz : x.1 ≠ z := fun h => hxT (by simp [T, h])
    have hxu : x.1 ≠ u := fun h => hxT (by simp [T, h])
    have hxv : x.1 ≠ v := fun h => hxT (by simp [T, h])
    have hsum := hr x.1
    rw [sum_univ_sub T] at hsum
    have hT0 : ∑ w ∈ T, (M x.1 w : ℕ) = 0 := by
      have hTins : ∀ f : Fin k → ℕ, ∑ w ∈ T, f w = f z + (f u + f v) := fun f => by
        rw [show T = insert z {u, v} from rfl, Finset.sum_insert hzT', Finset.sum_pair huv]
      rw [hTins, hs z x.1, hzu0 x.1 hxu hxv, hs u x.1, huv0 x.1 hxz hxv, hs v x.1,
        hvu0 x.1 hxz hxu]
      rfl
    rw [hT0, zero_add] at hsum
    simpa using hsum
  · intro M₁ hM₁ M₂ hM₂ heq
    rw [Finset.mem_filter, mem_V_iff] at hM₁ hM₂
    rcases hM₁ with ⟨⟨hs₁', hr₁⟩, hzz₁, hzu₁, hzv₁, huv₁⟩
    rcases hM₂ with ⟨⟨hs₂', hr₂⟩, hzz₂, hzu₂, hzv₂, huv₂⟩
    have hMV₁ : M₁ ∈ V (Fin k) := (mem_V_iff M₁).mpr ⟨hs₁', hr₁⟩
    have hMV₂ : M₂ ∈ V (Fin k) := (mem_V_iff M₂).mpr ⟨hs₂', hr₂⟩
    have hs₁ := (isSymm_iff M₁).mp hs₁'
    have hs₂ := (isSymm_iff M₂).mp hs₂'
    have hzu0₁ := off_diag_zero_of_two_ones hMV₁ huv hzu₁ hzv₁
    have hzu0₂ := off_diag_zero_of_two_ones hMV₂ huv hzu₂ hzv₂
    have huv0₁ := off_diag_zero_of_two_ones hMV₁ hvz.symm (by simpa [hs₁] using hzu₁) huv₁
    have huv0₂ := off_diag_zero_of_two_ones hMV₂ hvz.symm (by simpa [hs₂] using hzu₂) huv₂
    have hvu0₁ := off_diag_zero_of_two_ones hMV₁ huz.symm (by simpa [hs₁] using hzv₁)
      (by simpa [hs₁] using huv₁)
    have hvu0₂ := off_diag_zero_of_two_ones hMV₂ huz.symm (by simpa [hs₂] using hzv₂)
      (by simpa [hs₂] using huv₂)
    refine Matrix.ext fun i j => ?_
    by_cases hiT : i ∈ T <;> by_cases hjT : j ∈ T
    · have hcases : ∀ a ∈ T, a = z ∨ a = u ∨ a = v := fun a ha => by simpa [T] using ha
      rcases hcases i hiT with hiz | hiu | hiv <;>
        rcases hcases j hjT with hjz | hju | hjv
      · rw [hiz, hjz, hzz₁, hzz₂]
      · rw [hiz, hju, hzu₁, hzu₂]
      · rw [hiz, hjv, hzv₁, hzv₂]
      · rw [hiu, hjz, hs₁ z u, hs₂ z u, hzu₁, hzu₂]
      · rw [hiu, hju, huv0₁ u huz huv, huv0₂ u huz huv]
      · rw [hiu, hjv, huv₁, huv₂]
      · rw [hiv, hjz, hs₁ z v, hs₂ z v, hzv₁, hzv₂]
      · rw [hiv, hju, hs₁ u v, hs₂ u v, huv₁, huv₂]
      · rw [hiv, hjv, hvu0₁ v hvz huv.symm, hvu0₂ v hvz huv.symm]
    · have hjz : j ≠ z := fun h => hjT (by simp [T, h])
      have hju : j ≠ u := fun h => hjT (by simp [T, h])
      have hjv : j ≠ v := fun h => hjT (by simp [T, h])
      rcases (by simpa [T] using hiT : i = z ∨ i = u ∨ i = v) with hiz | hiu | hiv
      · rw [hiz, hzu0₁ j hju hjv, hzu0₂ j hju hjv]
      · rw [hiu, huv0₁ j hjz hjv, huv0₂ j hjz hjv]
      · rw [hiv, hvu0₁ j hjz hju, hvu0₂ j hjz hju]
    · have hiz : i ≠ z := fun h => hiT (by simp [T, h])
      have hiu : i ≠ u := fun h => hiT (by simp [T, h])
      have hiv : i ≠ v := fun h => hiT (by simp [T, h])
      rcases (by simpa [T] using hjT : j = z ∨ j = u ∨ j = v) with hjz | hju | hjv
      · rw [hjz, hs₁ z i, hs₂ z i, hzu0₁ i hiu hiv, hzu0₂ i hiu hiv]
      · rw [hju, hs₁ u i, hs₂ u i, huv0₁ i hiz hiv, huv0₂ i hiz hiv]
      · rw [hjv, hs₁ v i, hs₂ v i, hvu0₁ i hiz hiu, hvu0₂ i hiz hiu]
    · have := congrArg (fun M : Matrix δ δ (Fin 2) => M ⟨i, hiT⟩ ⟨j, hjT⟩) heq
      simpa using this
  · intro M' hM'
    rw [mem_V_iff] at hM'
    rcases hM' with ⟨hs', hr'⟩
    rw [isSymm_iff] at hs'
    let M : Matrix (Fin k) (Fin k) (Fin 2) := Matrix.of fun i j =>
      if hi : i ∈ T then
        if j ∈ T then (if i = j then 0 else 1) else 0
      else
        if hj : j ∈ T then 0 else M' ⟨i, hi⟩ ⟨j, hj⟩
    have hzT : z ∈ T := Finset.mem_insert_self z _
    have huT : u ∈ T := Finset.mem_insert_of_mem (Finset.mem_insert_self u _)
    have hvT : v ∈ T :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
    have hMsymm : M.IsSymm := (isSymm_iff M).mpr fun i j => by
      by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;> simp [M, hi, hj, hs', eq_comm]
    have hMrow : ∀ i, ∑ j, (M i j : ℕ) = 2 := fun i => by
      rw [sum_univ_sub T]
      by_cases hiT : i ∈ T
      · have hsub0 : ∑ y : δ, (M i y.1 : ℕ) = 0 := Finset.sum_eq_zero fun y _ => by
          simp [M, hiT, y.2]
        have hTsum : ∑ w ∈ T, (M i w : ℕ) = 2 := by
          rw [show T = insert z {u, v} from rfl, Finset.sum_insert hzT', Finset.sum_pair huv]
          rcases (by simpa [T] using hiT : i = z ∨ i = u ∨ i = v) with hiz | hiu | hiv
          · rw [hiz]
            simp [M, hzT, huT, hvT, huz.symm, hvz.symm]
          · rw [hiu]
            simp [M, hzT, huT, hvT, huz, huv]
          · rw [hiv]
            simp [M, hzT, huT, hvT, hvz, huv.symm]
        rw [hTsum, hsub0]
      · have hTsum : ∑ w ∈ T, (M i w : ℕ) = 0 := Finset.sum_eq_zero fun w hw => by
          simp [M, hiT, hw]
        have hsub2 : ∑ y : δ, (M i y.1 : ℕ) = 2 := by
          have := hr' ⟨i, hiT⟩
          have hcongr : ∑ y : δ, (M i y.1 : ℕ) = ∑ y : δ, (M' ⟨i, hiT⟩ y : ℕ) :=
            Finset.sum_congr rfl fun y _ => by simp [M, hiT, y.2]
          rw [hcongr, this]
        rw [hTsum, zero_add, hsub2]
    refine ⟨M, ?_, Matrix.ext fun x y => by simp [M, x.2, y.2]⟩
    rw [Finset.mem_filter, mem_V_iff]
    exact ⟨⟨hMsymm, hMrow⟩, by simp [M, hzT], by simp [M, hzT, huT, huz.symm],
      by simp [M, hzT, hvT, hvz.symm], by simp [M, huT, hvT, huv]⟩

private noncomputable def toGamMat {k : ℕ} (z u v : Fin k) (M : Matrix (Fin k) (Fin k) (Fin 2)) :
    Matrix {x : Fin k // x ≠ z} {x : Fin k // x ≠ z} (Fin 2) :=
  Matrix.of fun a b =>
    if (a.1 = u ∧ b.1 = v) ∨ (a.1 = v ∧ b.1 = u) then 1 else M a.1 b.1

private lemma eq2_p0_eq_Q {k : ℕ} (z : Fin k) :
    ((((V (Fin k)).filter (fun M => M z z = 0) ×ˢ
        (Finset.univ.erase z).offDiag).filter
      (fun x => x.1 z x.2.1 = 1 ∧ x.1 z x.2.2 = 1 ∧ x.1 x.2.1 x.2.2 = 0)).card) =
      (((V {x : Fin k // x ≠ z}) ×ˢ
        (Finset.univ : Finset {x : Fin k // x ≠ z}).offDiag).filter
        (fun y => y.1 y.2.1 y.2.2 = 1)).card := by
  let γ := {x : Fin k // x ≠ z}
  let NLk := (V (Fin k)).filter (fun M => M z z = 0)
  let U := (Finset.univ.erase z).offDiag
  let P0 := (NLk ×ˢ U).filter (fun x => x.1 z x.2.1 = 1 ∧ x.1 z x.2.2 = 1 ∧ x.1 x.2.1 x.2.2 = 0)
  let Q := ((V γ) ×ˢ (Finset.univ : Finset γ).offDiag).filter (fun y => y.1 y.2.1 y.2.2 = 1)
  have hu_ne : ∀ x ∈ P0, x.2.1 ≠ z := fun x hx => by
    have h := (Finset.mem_filter.mp hx).1
    exact (Finset.mem_erase.mp (Finset.mem_offDiag.mp (Finset.mem_product.mp h).2).1).1
  have hv_ne : ∀ x ∈ P0, x.2.2 ≠ z := fun x hx => by
    have h := (Finset.mem_filter.mp hx).1
    exact (Finset.mem_erase.mp (Finset.mem_offDiag.mp (Finset.mem_product.mp h).2).2.1).1
  change P0.card = Q.card
  refine Finset.card_bij
    (fun x hx => (toGamMat z x.2.1 x.2.2 x.1, (⟨x.2.1, hu_ne x hx⟩, ⟨x.2.2, hv_ne x hx⟩)))
    ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_offDiag,
      Finset.mem_erase, Finset.mem_erase, mem_V_iff] at hx
    rcases hx with ⟨⟨⟨⟨hs_raw, hr⟩, hzz⟩, ⟨⟨huz, _⟩, ⟨hvz, _⟩, huv⟩⟩, hzu, hzv, huv0⟩
    have hMV : x.1 ∈ V (Fin k) := (mem_V_iff x.1).mpr ⟨hs_raw, hr⟩
    have hs := (isSymm_iff x.1).mp hs_raw
    have hz0 : ∀ w, w ≠ x.2.1 → w ≠ x.2.2 → x.1 z w = 0 :=
      off_diag_zero_of_two_ones hMV huv hzu hzv
    let u' : γ := ⟨x.2.1, huz⟩
    let v' : γ := ⟨x.2.2, hvz⟩
    have huv' : u' ≠ v' := fun h => huv (congrArg Subtype.val h)
    rw [Finset.mem_filter, Finset.mem_product, mem_V_iff, Finset.mem_offDiag]
    refine ⟨⟨⟨(isSymm_iff _).mpr fun a b => ?_, fun a => ?_⟩,
        ⟨Finset.mem_univ _, Finset.mem_univ _, huv'⟩⟩, by simp [toGamMat]⟩
    · dsimp [toGamMat]
      by_cases h1 : (a.1 = x.2.1 ∧ b.1 = x.2.2) ∨ (a.1 = x.2.2 ∧ b.1 = x.2.1)
      · have h2 : (b.1 = x.2.1 ∧ a.1 = x.2.2) ∨ (b.1 = x.2.2 ∧ a.1 = x.2.1) := by tauto
        simp [h1, h2]
      · have h2 : ¬ ((b.1 = x.2.1 ∧ a.1 = x.2.2) ∨ (b.1 = x.2.2 ∧ a.1 = x.2.1)) := by tauto
        simp [h1, h2, hs]
    · have hasum := hr a.1
      rw [sum_univ_ne z] at hasum
      by_cases hau : a = u'
      · subst hau
        have hMuz : x.1 u'.1 z = 1 := by simpa [hs] using hzu
        rw [hMuz, fin2_val_one] at hasum
        change 1 + ∑ b : γ, (x.1 u'.1 b.1 : ℕ) = 2 at hasum
        have hsub1 : ∑ b : γ, (x.1 u'.1 b.1 : ℕ) = 1 := by omega
        have heq_b : ∀ b : γ, (toGamMat z x.2.1 x.2.2 x.1 u' b : ℕ) =
            if b = v' then 1 else (x.1 u'.1 b.1 : ℕ) := fun b => by
          by_cases hbv : b = v'
          · simp [toGamMat, hbv, u', v']
          · have hbne : b.1 ≠ x.2.2 := fun h => hbv (Subtype.ext h)
            simp [toGamMat, u', hbv, hbne, huv]
        simp only [heq_b]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v')]
        have hrest : ∑ b ∈ Finset.univ.erase v',
            (if b = v' then 1 else (x.1 u'.1 b.1 : ℕ)) =
            ∑ b ∈ Finset.univ.erase v', (x.1 u'.1 b.1 : ℕ) :=
          Finset.sum_congr rfl fun b hb => by simp [(Finset.mem_erase.mp hb).1]
        have hsub_rest : ∑ b ∈ Finset.univ.erase v', (x.1 u'.1 b.1 : ℕ) = 1 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v')] at hsub1
          have h0 : (x.1 u'.1 v'.1 : ℕ) = 0 := by simp [u', v', huv0]
          omega
        simp [hrest, hsub_rest]
      · by_cases hav : a = v'
        · subst hav
          have hMvz : x.1 v'.1 z = 1 := by simpa [hs] using hzv
          rw [hMvz, fin2_val_one] at hasum
          change 1 + ∑ b : γ, (x.1 v'.1 b.1 : ℕ) = 2 at hasum
          have hsub1 : ∑ b : γ, (x.1 v'.1 b.1 : ℕ) = 1 := by omega
          have heq_b : ∀ b : γ, (toGamMat z x.2.1 x.2.2 x.1 v' b : ℕ) =
              if b = u' then 1 else (x.1 v'.1 b.1 : ℕ) := fun b => by
            by_cases hbu : b = u'
            · simp [toGamMat, hbu, u', v']
            · have hbne : b.1 ≠ x.2.1 := fun h => hbu (Subtype.ext h)
              simp [toGamMat, v', hbu, hbne, huv.symm]
          simp only [heq_b]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u')]
          have hrest : ∑ b ∈ Finset.univ.erase u',
              (if b = u' then 1 else (x.1 v'.1 b.1 : ℕ)) =
              ∑ b ∈ Finset.univ.erase u', (x.1 v'.1 b.1 : ℕ) :=
            Finset.sum_congr rfl fun b hb => by simp [(Finset.mem_erase.mp hb).1]
          have hsub_rest : ∑ b ∈ Finset.univ.erase u', (x.1 v'.1 b.1 : ℕ) = 1 := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u')] at hsub1
            have h0 : (x.1 v'.1 u'.1 : ℕ) = 0 := by simp [u', v', hs, huv0]
            omega
          simp [hrest, hsub_rest]
        · have hMaz : x.1 a.1 z = 0 := by
            rw [hs z a.1]
            exact hz0 a.1 (fun h => hau (Subtype.ext h)) (fun h => hav (Subtype.ext h))
          rw [hMaz, fin2_val_zero, zero_add] at hasum
          have ha1 : a.1 ≠ x.2.1 := fun h => hau (Subtype.ext h)
          have ha2 : a.1 ≠ x.2.2 := fun h => hav (Subtype.ext h)
          have heq_b : ∀ b : γ, (toGamMat z x.2.1 x.2.2 x.1 a b : ℕ) = (x.1 a.1 b.1 : ℕ) :=
            fun b => by simp [toGamMat, ha1, ha2]
          rw [Finset.sum_congr rfl fun b _ => heq_b b]
          exact hasum
  · intro x₁ hx₁ x₂ hx₂ heq
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_offDiag,
      Finset.mem_erase, Finset.mem_erase, mem_V_iff] at hx₁ hx₂
    rcases hx₁ with ⟨⟨⟨⟨hs_raw₁, hr₁⟩, hzz₁⟩, ⟨⟨huz₁, _⟩, ⟨hvz₁, _⟩, huv₁⟩⟩, hzu₁, hzv₁, huv0₁⟩
    rcases hx₂ with ⟨⟨⟨⟨hs_raw₂, hr₂⟩, hzz₂⟩, ⟨⟨huz₂, _⟩, ⟨hvz₂, _⟩, huv₂⟩⟩, hzu₂, hzv₂, huv0₂⟩
    have hMV₁ : x₁.1 ∈ V (Fin k) := (mem_V_iff x₁.1).mpr ⟨hs_raw₁, hr₁⟩
    have hMV₂ : x₂.1 ∈ V (Fin k) := (mem_V_iff x₂.1).mpr ⟨hs_raw₂, hr₂⟩
    have hp1 : x₁.2.1 = x₂.2.1 := congrArg (fun t => t.2.1.1) heq
    have hp2 : x₁.2.2 = x₂.2.2 := congrArg (fun t => t.2.2.1) heq
    have hpeq : x₁.2 = x₂.2 := Prod.ext hp1 hp2
    have hs₁ := (isSymm_iff x₁.1).mp hs_raw₁
    have hs₂ := (isSymm_iff x₂.1).mp hs_raw₂
    have hz0₁ := off_diag_zero_of_two_ones hMV₁ huv₁ hzu₁ hzv₁
    have hz0₂ := off_diag_zero_of_two_ones hMV₂ huv₂ hzu₂ hzv₂
    have hM : x₁.1 = x₂.1 := by
      refine Matrix.ext fun i j => ?_
      by_cases hiz : i = z <;> by_cases hjz : j = z
      · simp [hiz, hjz, hzz₁, hzz₂]
      · by_cases hj1 : j = x₁.2.1
        · rw [hiz, hj1, hzu₁, hp1, hzu₂]
        · by_cases hj2 : j = x₁.2.2
          · rw [hiz, hj2, hzv₁, hp2, hzv₂]
          · rw [hiz, hz0₁ j hj1 hj2,
              hz0₂ j (by rw [← hp1]; exact hj1) (by rw [← hp2]; exact hj2)]
      · by_cases hi1 : i = x₁.2.1
        · rw [hjz, hi1, hs₁ z x₁.2.1, hs₂ z x₁.2.1, hzu₁, hp1, hzu₂]
        · by_cases hi2 : i = x₁.2.2
          · rw [hjz, hi2, hs₁ z x₁.2.2, hs₂ z x₁.2.2, hzv₁, hp2, hzv₂]
          · rw [hjz, hs₁ z i, hs₂ z i, hz0₁ i hi1 hi2,
              hz0₂ i (by rw [← hp1]; exact hi1) (by rw [← hp2]; exact hi2)]
      · by_cases hboth : (i = x₁.2.1 ∧ j = x₁.2.2) ∨ (i = x₁.2.2 ∧ j = x₁.2.1)
        · rcases hboth with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [huv0₁, hp1, hp2, huv0₂]
          · rw [hs₁, huv0₁, hs₂, hp1, hp2, huv0₂]
        · have hnot1 : ¬ ((i = x₁.2.1 ∧ j = x₁.2.2) ∨ (i = x₁.2.2 ∧ j = x₁.2.1)) := hboth
          have hnot2 : ¬ ((i = x₂.2.1 ∧ j = x₂.2.2) ∨ (i = x₂.2.2 ∧ j = x₂.2.1)) := by
            rwa [← hp1, ← hp2]
          have := congrArg (fun t => t.1 ⟨i, hiz⟩ ⟨j, hjz⟩) heq
          simpa [toGamMat, hnot1, hnot2] using this
    exact Prod.ext hM hpeq
  · intro y hy
    rw [Finset.mem_filter, Finset.mem_product, mem_V_iff, Finset.mem_offDiag] at hy
    rcases hy with ⟨⟨⟨hs', hr'⟩, ⟨_, _, huv'⟩⟩, hy1⟩
    rw [isSymm_iff] at hs'
    let u := y.2.1.1
    let v := y.2.2.1
    have huz : u ≠ z := y.2.1.2
    have hvz : v ≠ z := y.2.2.2
    have huv : u ≠ v := fun h => huv' (Subtype.ext h)
    let M : Matrix (Fin k) (Fin k) (Fin 2) := Matrix.of fun i j =>
      if hi : i = z then
        if j = u ∨ j = v then 1 else 0
      else if hj : j = z then
        if i = u ∨ i = v then 1 else 0
      else if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then 0
      else y.1 ⟨i, hi⟩ ⟨j, hj⟩
    have hMsymm : M.IsSymm := (isSymm_iff M).mpr fun i j => by
      by_cases hi : i = z
      · rw [hi]
        by_cases hj : j = z
        · simp [M, hj]
        · simp [M, hj]
      · by_cases hj : j = z
        · rw [hj]
          simp [M, hi]
        · by_cases hboth : (i = u ∧ j = v) ∨ (i = v ∧ j = u)
          · have hboth' : (j = u ∧ i = v) ∨ (j = v ∧ i = u) := by tauto
            simp [M, hi, hj, hboth, hboth']
          · have hboth' : ¬ ((j = u ∧ i = v) ∨ (j = v ∧ i = u)) := by tauto
            simp [M, hi, hj, hboth, hboth', hs']
    have hMrow : ∀ i, ∑ j, (M i j : ℕ) = 2 := fun i => by
      rw [sum_univ_ne z]
      by_cases hiz : i = z
      · rw [hiz]
        have hS : (M z z : ℕ) = 0 := by simp [M, huz.symm, hvz.symm]
        have hsub : ∑ b : γ, (M z b.1 : ℕ) = 2 := by
          have hu_mem : y.2.1 ∈ (Finset.univ : Finset γ) := Finset.mem_univ _
          have hv_mem : y.2.2 ∈ (Finset.univ : Finset γ).erase y.2.1 :=
            Finset.mem_erase.mpr ⟨huv'.symm, Finset.mem_univ _⟩
          rw [← Finset.add_sum_erase _ _ hu_mem, ← Finset.add_sum_erase _ _ hv_mem]
          have h1 : (M z y.2.1.1 : ℕ) = 1 := by simp [M, u]
          have h2 : (M z y.2.2.1 : ℕ) = 1 := by simp [M, v]
          have hrest : ∑ b ∈ (Finset.univ.erase y.2.1).erase y.2.2, (M z b.1 : ℕ) = 0 :=
            Finset.sum_eq_zero fun b hb => by
              rw [Finset.mem_erase, Finset.mem_erase] at hb
              have hbu : b.1 ≠ u := fun h => hb.2.1 (Subtype.ext h)
              have hbv : b.1 ≠ v := fun h => hb.1 (Subtype.ext h)
              simp [M, hbu, hbv]
          rw [h1, h2, hrest]
          rfl
        rw [hS, zero_add, hsub]
      · let i' : γ := ⟨i, hiz⟩
        by_cases hiu : i = u
        · have hMz : (M i z : ℕ) = 1 := by simp [M, hiu, huz]
          have hi' : i' = y.2.1 := Subtype.ext hiu
          have hr_i' := hr' i'
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y.2.2)] at hr_i'
          have hy1' : (y.1 i' y.2.2 : ℕ) = 1 := by rw [hi', hy1]; rfl
          rw [hy1'] at hr_i'
          have hsub_rest : ∑ b ∈ Finset.univ.erase y.2.2, (M i b.1 : ℕ) =
              ∑ b ∈ Finset.univ.erase y.2.2, (y.1 i' b : ℕ) :=
            Finset.sum_congr rfl fun b hb => by
              have hbv : b.1 ≠ v := fun h => (Finset.mem_erase.mp hb).1 (Subtype.ext h)
              simp [M, huz, b.2, hiu, hbv, huv, i']
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y.2.2)]
          have hMiv0 : (M i y.2.2.1 : ℕ) = 0 := by simp [M, huz, hvz, hiu, v]
          rw [hMz, hMiv0, zero_add, hsub_rest]
          omega
        · by_cases hiv : i = v
          · have hMz : (M i z : ℕ) = 1 := by simp [M, hiv, hvz]
            have hi' : i' = y.2.2 := Subtype.ext hiv
            have hr_i' := hr' i'
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y.2.1)] at hr_i'
            have hy1' : (y.1 i' y.2.1 : ℕ) = 1 := by rw [hi', hs', hy1]; rfl
            rw [hy1'] at hr_i'
            have hsub_rest : ∑ b ∈ Finset.univ.erase y.2.1, (M i b.1 : ℕ) =
                ∑ b ∈ Finset.univ.erase y.2.1, (y.1 i' b : ℕ) :=
              Finset.sum_congr rfl fun b hb => by
                have hbu : b.1 ≠ u := fun h => (Finset.mem_erase.mp hb).1 (Subtype.ext h)
                simp [M, hvz, b.2, hiv, hbu, huv.symm, i']
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y.2.1)]
            have hMiu0 : (M i y.2.1.1 : ℕ) = 0 := by simp [M, hvz, huz, hiv, u]
            rw [hMz, hMiu0, zero_add, hsub_rest]
            omega
          · have hMz : (M i z : ℕ) = 0 := by simp [M, hiz, hiu, hiv]
            have hr_i' := hr' i'
            have hsub_all : ∑ b : γ, (M i b.1 : ℕ) = ∑ b : γ, (y.1 i' b : ℕ) :=
              Finset.sum_congr rfl fun b _ => by simp [M, hiz, b.2, hiu, hiv, i']
            rw [hMz, zero_add, hsub_all, hr_i']
    have hmemP0 : (M, (u, v)) ∈ P0 := by
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_offDiag,
        Finset.mem_erase, Finset.mem_erase, mem_V_iff]
      exact ⟨⟨⟨⟨hMsymm, hMrow⟩, by simp [M, huz.symm, hvz.symm]⟩,
        ⟨⟨huz, Finset.mem_univ _⟩, ⟨hvz, Finset.mem_univ _⟩, huv⟩⟩,
        by simp [M, u], by simp [M, v], by simp [M, huz, hvz, huv]⟩
    refine ⟨(M, (u, v)), hmemP0, ?_⟩
    refine Prod.ext (Matrix.ext fun a b => ?_) (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))
    dsimp [toGamMat]
    by_cases hboth : (a.1 = u ∧ b.1 = v) ∨ (a.1 = v ∧ b.1 = u)
    · rcases hboth with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have ha' : a = y.2.1 := Subtype.ext ha
        have hb' : b = y.2.2 := Subtype.ext hb
        subst ha'; subst hb'
        simp [u, v, hy1]
      · have ha' : a = y.2.2 := Subtype.ext ha
        have hb' : b = y.2.1 := Subtype.ext hb
        subst ha'; subst hb'
        simp [u, v, hs', hy1]
    · simp [hboth, M, a.2, b.2]

private lemma eq2 (k : ℕ) (hk : 3 ≤ k) :
    2 * (nl k : ℤ) =
      ((k : ℤ) - 1) * ((k : ℤ) - 2) * (OMA.S_oeis_a000986.a (k - 3) : ℤ) +
        2 * ((k : ℤ) - 1) * (OMA.S_oeis_a000986.a (k - 1) : ℤ) -
        ((k : ℤ) - 1) * (l (k - 1) : ℤ) := by
  have hkpos : 0 < k := by omega
  set z : Fin k := ⟨0, hkpos⟩
  let NLk := (V (Fin k)).filter (fun M => M z z = 0)
  have hnl_eq : nl k = NLk.card := by
    unfold nl
    simp only [hkpos, ↓reduceDIte]
    rfl
  let U := (Finset.univ.erase z).offDiag
  have hUcard : U.card = (k - 1) * (k - 2) := by
    rw [Finset.offDiag_card, Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_fin]
    rw [show k - 1 = (k - 2) + 1 by omega]
    ring_nf
    omega
  let P := (NLk ×ˢ U).filter (fun x => x.1 z x.2.1 = 1 ∧ x.1 z x.2.2 = 1)
  have hP_lhs : P.card = 2 * nl k := by
    rw [hnl_eq]
    simp only [P, Finset.card_filter, Finset.sum_product]
    have hM_sum :
        ∀ M ∈ NLk,
          ∑ p ∈ U, (if M z p.1 = 1 ∧ M z p.2 = 1 then 1 else 0) = 2 := by
      intro M hM
      rw [Finset.mem_filter, mem_V_iff] at hM
      let S := (Finset.univ.erase z).filter (fun j => M z j = 1)
      have hScard : S.card = 2 := by
        have hr := hM.1.2 z
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z), hM.2] at hr
        change 0 + ∑ j ∈ Finset.univ.erase z, (M z j : ℕ) = 2 at hr
        rw [zero_add, sum_fin2_eq_card] at hr
        exact hr
      have hSoff : S.offDiag.card = 2 := by
        rw [Finset.offDiag_card, hScard]
      have hU_f :
          ∑ p ∈ U, (if M z p.1 = 1 ∧ M z p.2 = 1 then 1 else 0) =
            (U.filter (fun p => M z p.1 = 1 ∧ M z p.2 = 1)).card :=
        (Finset.card_filter _ _).symm
      rw [hU_f]
      refine (congrArg Finset.card (Finset.ext fun p => ?_)).trans hSoff
      simp only [Finset.mem_filter, U, S, Finset.mem_offDiag, Finset.mem_erase, Finset.mem_univ,
        and_true]
      tauto
    rw [Finset.sum_congr rfl hM_sum, Finset.sum_const, smul_eq_mul, mul_comm]
  have hsplit := Finset.card_filter_add_card_filter_not (s := P) (fun x => x.1 x.2.1 x.2.2 = 1)
  have hP1 :
      (P.filter (fun x => x.1 x.2.1 x.2.2 = 1)).card =
        (k - 1) * (k - 2) * OMA.S_oeis_a000986.a (k - 3) := by
    have hP1_eq :
        (P.filter (fun x => x.1 x.2.1 x.2.2 = 1)) =
          (NLk ×ˢ U).filter (fun x => x.1 z x.2.1 = 1 ∧ x.1 z x.2.2 = 1 ∧ x.1 x.2.1 x.2.2 = 1) := by
      ext x
      simp only [P, Finset.mem_filter]
      tauto
    rw [hP1_eq]
    simp only [Finset.card_filter, Finset.sum_product_right]
    have hp_card :
        ∀ p ∈ U,
          (∑ M ∈ NLk, if M z p.1 = 1 ∧ M z p.2 = 1 ∧ M p.1 p.2 = 1 then 1 else 0) =
            OMA.S_oeis_a000986.a (k - 3) := by
      intro p hp
      rw [Finset.mem_offDiag, Finset.mem_erase, Finset.mem_erase] at hp
      rcases hp with ⟨⟨huz, _⟩, ⟨hvz, _⟩, huv⟩
      have hcard_eq :
          (∑ M ∈ NLk, if M z p.1 = 1 ∧ M z p.2 = 1 ∧ M p.1 p.2 = 1 then 1 else 0) =
            ((V (Fin k)).filter
              (fun M => M z z = 0 ∧ M z p.1 = 1 ∧ M z p.2 = 1 ∧ M p.1 p.2 = 1)).card := by
        rw [← Finset.card_filter]
        exact congrArg Finset.card (Finset.ext fun M => by simp only [Finset.mem_filter, NLk]; tauto)
      rw [hcard_eq, eq2_p1 z p.1 p.2 huz hvz huv]
    rw [Finset.sum_congr rfl hp_card, Finset.sum_const, hUcard, smul_eq_mul]
  let γ := {x : Fin k // x ≠ z}
  have hγcard : Fintype.card γ = k - 1 := by
    rw [card_ne_eq z, Fintype.card_fin]
  let Q := ((V γ) ×ˢ (Finset.univ : Finset γ).offDiag).filter (fun y => y.1 y.2.1 y.2.2 = 1)
  have hP0_eq :
      (P.filter (fun x => x.1 x.2.1 x.2.2 ≠ 1)).card = Q.card := by
    have hP0_eq' :
        P.filter (fun x => x.1 x.2.1 x.2.2 ≠ 1) =
          (NLk ×ˢ U).filter (fun x => x.1 z x.2.1 = 1 ∧ x.1 z x.2.2 = 1 ∧ x.1 x.2.1 x.2.2 = 0) := by
      ext x
      simp only [P, Finset.mem_filter, fin2_ne_one_iff]
      tauto
    rw [hP0_eq']
    exact eq2_p0_eq_Q z
  have hQ_eq :
      (Q.card : ℤ) =
        2 * ((k : ℤ) - 1) * (OMA.S_oeis_a000986.a (k - 1) : ℤ) -
          ((k : ℤ) - 1) * (l (k - 1) : ℤ) := by
    have hQ_nat :
        Q.card = ∑ M' ∈ V γ, ∑ a : γ, ∑ b ∈ Finset.univ.erase a, (M' a b : ℕ) := by
      simp only [Q, Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun M' _ => ?_
      have hoff :
          (Finset.univ : Finset γ).offDiag =
            ((Finset.univ : Finset γ).sigma (fun a => Finset.univ.erase a)).map
              ⟨fun p => (p.1, p.2), fun p q h => by
                rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
                simp_all⟩ := by
        ext p
        rw [Finset.mem_offDiag, Finset.mem_map]
        constructor
        · intro h
          refine ⟨⟨p.1, p.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
            Finset.mem_erase.mpr ⟨h.2.2.symm, Finset.mem_univ _⟩⟩, rfl⟩
        · rintro ⟨⟨a, b⟩, hab, rfl⟩
          exact ⟨Finset.mem_univ _, Finset.mem_univ _,
            (Finset.mem_erase.mp (Finset.mem_sigma.mp hab).2).1.symm⟩
      rw [hoff, Finset.sum_map, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      exact (fin2_val_eq _).symm
    have hQ_int :
        (Q.card : ℤ) = ∑ a : γ, ∑ M' ∈ V γ, (2 - (if M' a a = 1 then (1 : ℤ) else 0)) := by
      rw [hQ_nat, Finset.sum_comm]
      push_cast
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun M' hM' => ?_
      rw [mem_V_iff] at hM'
      have hr := hM'.2 a
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at hr
      have haa : (M' a a : ℤ) = if M' a a = 1 then 1 else 0 := by
        have := fin2_val_eq (M' a a)
        exact_mod_cast this
      have hr_z : (M' a a : ℤ) + ∑ b ∈ Finset.univ.erase a, (M' a b : ℤ) = 2 := by
        exact_mod_cast hr
      linarith
    rw [hQ_int]
    have hinner :
        ∀ a : γ,
          (∑ M' ∈ V γ, (2 - (if M' a a = 1 then (1 : ℤ) else 0))) =
            2 * (OMA.S_oeis_a000986.a (k - 1) : ℤ) - (l (k - 1) : ℤ) := by
      intro a
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, a_eq_V_card hγcard,
        l_eq_Vdiag_card a hγcard]
      have hsum_ite :
          (∑ M' ∈ V γ, (if M' a a = 1 then (1 : ℤ) else 0)) =
            (((V γ).filter (fun M' => M' a a = 1)).card : ℤ) := by
        simp [Finset.sum_boole]
      rw [hsum_ite]
      ring
    rw [Finset.sum_congr rfl fun a _ => hinner a, Finset.sum_const, Finset.card_univ, hγcard,
      nsmul_eq_mul]
    push_cast [show 1 ≤ k by omega]
    ring
  have hP_split : (P.card : ℤ) =
      ((P.filter (fun x => x.1 x.2.1 x.2.2 = 1)).card : ℤ) +
        ((P.filter (fun x => x.1 x.2.1 x.2.2 ≠ 1)).card : ℤ) := by
    exact_mod_cast hsplit.symm
  rw [hP_lhs, hP1, hP0_eq, hQ_eq] at hP_split
  push_cast [show 1 ≤ k by omega, show 2 ≤ k by omega] at hP_split
  linarith

private lemma order4 (n : ℕ) (hn : 4 ≤ n) :
    2 * (OMA.S_oeis_a000986.a n : ℤ) -
      4 * ((n : ℤ) - 1) * (OMA.S_oeis_a000986.a (n - 1) : ℤ) +
      2 * ((n : ℤ) - 1) * ((n : ℤ) - 3) * (OMA.S_oeis_a000986.a (n - 2) : ℤ) +
      ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (OMA.S_oeis_a000986.a (n - 4) : ℤ) = 0 := by
  have heq1_n := eq1 n (by omega)
  have heq2_n := eq2 n (by omega)
  have heq1_n1 := eq1 (n - 1) (by omega)
  have heq2_n1 := eq2 (n - 1) (by omega)
  have hal_n := congrArg (Nat.cast (R := ℤ)) (a_eq_l_add_nl (show 0 < n by omega))
  have hal_n1 := congrArg (Nat.cast (R := ℤ)) (a_eq_l_add_nl (show 0 < n - 1 by omega))
  rw [show n - 1 - 1 = n - 2 by omega, show n - 1 - 2 = n - 3 by omega] at heq1_n1
  rw [show n - 1 - 1 = n - 2 by omega, show n - 1 - 3 = n - 4 by omega] at heq2_n1
  push_cast [show 1 ≤ n by omega] at heq1_n1 heq2_n1 hal_n hal_n1
  have hEn :
      2 * (OMA.S_oeis_a000986.a n : ℤ) =
        2 * ((n : ℤ) - 1) * (OMA.S_oeis_a000986.a (n - 1) : ℤ) +
          2 * ((n : ℤ) - 1) * (OMA.S_oeis_a000986.a (n - 2) : ℤ) +
          ((n : ℤ) - 1) * ((n : ℤ) - 2) * (OMA.S_oeis_a000986.a (n - 3) : ℤ) +
          ((n : ℤ) - 1) * (l (n - 1) : ℤ) := by
    linarith
  have hEn1 :
      2 * (OMA.S_oeis_a000986.a (n - 1) : ℤ) =
        2 * ((n : ℤ) - 2) * (OMA.S_oeis_a000986.a (n - 2) : ℤ) +
          2 * ((n : ℤ) - 2) * (OMA.S_oeis_a000986.a (n - 3) : ℤ) +
          ((n : ℤ) - 2) * ((n : ℤ) - 3) * (OMA.S_oeis_a000986.a (n - 4) : ℤ) +
          ((n : ℤ) - 2) * (l (n - 2) : ℤ) := by
    linarith
  have hcomb :
      ((n : ℤ) - 1) * (2 * (OMA.S_oeis_a000986.a (n - 1) : ℤ)) =
        2 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (OMA.S_oeis_a000986.a (n - 2) : ℤ) +
          ((n : ℤ) - 1) * ((n : ℤ) - 2) * (OMA.S_oeis_a000986.a (n - 3) : ℤ) +
          ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (OMA.S_oeis_a000986.a (n - 4) : ℤ) +
          ((n : ℤ) - 1) * (l (n - 1) : ℤ) := by
    linear_combination ((n : ℤ) - 1) * hEn1 - ((n : ℤ) - 1) * heq1_n1
  linarith

end Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a000986.main := by
  intro n hn
  have h1 := order4 n (by omega)
  have h2 := order4 (n - 1) (by omega)
  rw [show n - 1 - 1 = n - 2 by omega, show n - 1 - 2 = n - 3 by omega,
    show n - 1 - 4 = n - 5 by omega] at h2
  push_cast [show 1 ≤ n by omega] at h2
  linear_combination h1 - h2
