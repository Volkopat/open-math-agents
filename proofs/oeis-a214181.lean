import OMAStatements.S_oeis_a214181

namespace OMA.S_oeis_a214181

open PowerSeries Finset


instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance


instance {R K : ℕ} : DecidablePred (@Proper R K) := fun x => by
  unfold Proper; infer_instance


/-! ## Rows -/

/-- Cyclically adjacent entries of a row differ. -/
def hrow (r : Fin 3 → Fin 7) : Prop := ∀ j j' : Fin 3, j'.val = (j.val + 1) % 3 → r j ≠ r j'

/-- The row s may lie directly below the row r: vertically adjacent entries differ. -/
def ok (r s : Fin 3 → Fin 7) : Prop := ∀ j, r j ≠ s j

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- Rows valid and consecutive rows compatible. -/
def Valid {n : ℕ} (g : Fin n → Fin 3 → Fin 7) : Prop :=
  (∀ i, hrow (g i)) ∧ ∀ i i' : Fin n, i'.val = i.val + 1 → ok (g i) (g i')

instance {n : ℕ} : DecidablePred (@Valid n) := fun g => by unfold Valid; infer_instance

lemma cond_iff {n : ℕ} (x : Fin n → Fin 3 → Fin 7) : Proper x ↔ Valid x := by
  unfold Proper Valid hrow ok
  exact Iff.rfl

/-! ## Values introduced in row major order, after the values below c -/

/-- The values below c count as introduced before the array; every other value below an entry
occurs at an earlier position in row major order. -/
def RGSfrom {R C K : ℕ} (c : ℕ) (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → u.val < c ∨ ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} (c : ℕ) : DecidablePred (@RGSfrom R C K c) := fun x => by
  unfold RGSfrom; infer_instance

/-- The same for one row. -/
def rowRgs {C K : ℕ} (c : ℕ) (r : Fin C → Fin K) : Prop :=
  ∀ j, ∀ u : Fin K, u < r j → u.val < c ∨ ∃ j', j' < j ∧ r j' = u

instance {C K : ℕ} (c : ℕ) : DecidablePred (@rowRgs C K c) := fun r => by
  unfold rowRgs; infer_instance

/-- The number of values introduced after the row r, when c were introduced before it. -/
def newc {C K : ℕ} (c : ℕ) (r : Fin C → Fin K) : ℕ := max c (univ.sup fun j => (r j).val + 1)

lemma lt_newc {C K : ℕ} (c : ℕ) (r : Fin C → Fin K) (u : ℕ) :
    u < newc c r ↔ u < c ∨ ∃ j, u ≤ (r j).val := by
  unfold newc
  rw [lt_max_iff, Finset.lt_sup_iff]
  simp

lemma newc_le {C K : ℕ} (c : ℕ) (hc : c ≤ K) (r : Fin C → Fin K) : newc c r ≤ K :=
  max_le hc (Finset.sup_le fun j _ => (r j).isLt)

lemma rmn_iff {R C K : ℕ} (x : Fin R → Fin C → Fin K) : RowMajorNew x ↔ RGSfrom 0 x := by
  unfold RowMajorNew RGSfrom
  simp only [Nat.not_lt_zero, false_or]

lemma RGSfrom_one {C K : ℕ} (c : ℕ) (f : Fin 1 → Fin C → Fin K) : RGSfrom c f ↔ rowRgs c (f 0) := by
  constructor
  · intro H j u hu
    rcases H 0 j u hu with h | ⟨i', j', hb, he⟩
    · exact Or.inl h
    · right
      have hi : i' = 0 := Fin.fin_one_eq_zero i'
      subst hi
      rcases hb with hb | ⟨_, hj⟩
      · exact absurd hb (lt_irrefl _)
      · exact ⟨j', hj, he⟩
  · intro H i j u hu
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    rcases H j u hu with h | ⟨j', hj, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨0, j', Or.inr ⟨rfl, hj⟩, he⟩

lemma RGSfrom_cons {n C K : ℕ} (c : ℕ) (r : Fin C → Fin K) (h : Fin (n + 1) → Fin C → Fin K) :
    RGSfrom c (Fin.cons r h : Fin (n + 2) → Fin C → Fin K) ↔
      rowRgs c r ∧ RGSfrom (newc c r) h := by
  constructor
  · intro H
    refine ⟨fun j u hu => ?_, fun i j u hu => ?_⟩
    · rcases H 0 j u (by simpa using hu) with h1 | ⟨i', j', hb, he⟩
      · exact Or.inl h1
      · right
        rcases hb with hb | ⟨rfl, hj⟩
        · exact absurd hb (Fin.not_lt_zero _)
        · exact ⟨j', hj, by simpa using he⟩
    · rcases H i.succ j u (by simpa using hu) with h1 | ⟨i', j', hb, he⟩
      · left
        rw [lt_newc]
        exact Or.inl h1
      · induction i' using Fin.cases with
        | zero =>
          left
          rw [lt_newc]
          right
          refine ⟨j', ?_⟩
          simp only [Fin.cons_zero] at he
          rw [he]
        | succ i'' =>
          right
          refine ⟨i'', j', ?_, by simpa using he⟩
          rcases hb with hb | ⟨hb, hj⟩
          · exact Or.inl (Fin.succ_lt_succ_iff.mp hb)
          · exact Or.inr ⟨Fin.succ_injective _ hb, hj⟩
  · rintro ⟨H0, H⟩ i j u hu
    induction i using Fin.cases with
    | zero =>
      rcases H0 j u (by simpa using hu) with h1 | ⟨j', hj, he⟩
      · exact Or.inl h1
      · exact Or.inr ⟨0, j', Or.inr ⟨rfl, hj⟩, by simpa using he⟩
    | succ i =>
      rcases H i j u (by simpa using hu) with h1 | ⟨i', j', hb, he⟩
      · rw [lt_newc] at h1
        rcases h1 with h1 | ⟨j', hj'⟩
        · exact Or.inl h1
        · rcases Nat.lt_or_eq_of_le hj' with hlt | heq
          · rcases H0 j' u hlt with h2 | ⟨j'', _, he⟩
            · exact Or.inl h2
            · exact Or.inr ⟨0, j'', Or.inl (Fin.succ_pos _), by simpa using he⟩
          · exact Or.inr ⟨0, j', Or.inl (Fin.succ_pos _), by simpa using (Fin.ext heq).symm⟩
      · right
        refine ⟨i'.succ, j', ?_, by simpa using he⟩
        rcases hb with hb | ⟨rfl, hj⟩
        · exact Or.inl (Fin.succ_lt_succ_iff.mpr hb)
        · exact Or.inr ⟨rfl, hj⟩

/-! ## Counting by the first row -/

/-- W(n, r, c): arrays with n + 1 rows, first row r, consecutive rows compatible, values introduced
in row major order after the values below c. -/
def W (n : ℕ) (r : Fin 3 → Fin 7) (c : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 3 → Fin 7)).filter
    (fun g => Valid g ∧ RGSfrom c g ∧ g 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 3 → Fin 7) (g : Fin (n + 1) → Fin 3 → Fin 7) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 3 → Fin 7) ↔ hrow x ∧ ok x (g 0) ∧ Valid g := by
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨by simpa using hr 0, ?_, fun i => by simpa using hr i.succ, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨hx, h0, hg, hgo⟩
    refine ⟨?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hx
      | succ i => simpa using hg i
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j =>
          have hj : j = 0 := by ext; simp at hij; omega
          subst hj
          simpa using h0
      | succ i =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j =>
          simp only [Fin.cons_succ]
          exact hgo i j (by simp at hij; omega)

lemma W_zero (r : Fin 3 → Fin 7) (c : ℕ) : W 0 r c = if hrow r ∧ rowRgs c r then 1 else 0 := by
  unfold W
  split_ifs with hr
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => r, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, _, hf⟩
      funext i
      rw [Fin.fin_one_eq_zero i, hf]
    · rintro rfl
      refine ⟨⟨fun _ => hr.1, ?_⟩, (RGSfrom_one c _).2 hr.2, rfl⟩
      intro i j hij
      have := j.isLt
      omega
  · rw [Finset.card_eq_zero]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨h1, _⟩, hR, h0⟩
    apply hr
    rw [← h0]
    exact ⟨h1 0, (RGSfrom_one c f).1 hR⟩

/-- Prepending the row r to an array with n + 1 rows. -/
def consEmb (n : ℕ) (r : Fin 3 → Fin 7) :
    (Fin (n + 1) → Fin 3 → Fin 7) ↪ (Fin (n + 2) → Fin 3 → Fin 7) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 3 → Fin 7) (g : Fin (n + 1) → Fin 3 → Fin 7) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Fin 3 → Fin 7) (c : ℕ) :
    W (n + 1) r c = if hrow r ∧ rowRgs c r then
      ∑ s : Fin 3 → Fin 7, (if ok r s then W n s (newc c r) else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 3 → Fin 7)).filter
      (fun f => Valid f ∧ RGSfrom c f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 3 → Fin 7)).filter
        (fun g => ((hrow r ∧ rowRgs c r) ∧ ok r (g 0)) ∧ Valid g ∧
          RGSfrom (newc c r) g)).map (consEmb n r)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, hR, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons r (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        rw [hf, RGSfrom_cons] at hR
        exact ⟨⟨⟨hv.1, hR.1⟩, hv.2.1⟩, hv.2.2, hR.2⟩
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, ⟨⟨⟨h1, h2⟩, h3⟩, hg, hR⟩, rfl⟩
      exact ⟨(valid_cons r g).2 ⟨h1, h3, hg⟩, (RGSfrom_cons c r g).2 ⟨h2, hR⟩, by simp⟩
  unfold W
  rw [e, Finset.card_map]
  split_ifs with hrc
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs with hrs
    · congr 1
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, hg⟩, h0⟩
        exact ⟨hg.1, hg.2, h0⟩
      · rintro ⟨hg, hR, h0⟩
        exact ⟨⟨⟨hrc, by rw [h0]; exact hrs⟩, hg, hR⟩, h0⟩
    · rw [Finset.card_eq_zero]
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨⟨⟨_, h2⟩, _⟩, h0⟩
      exact hrs (by rw [← h0]; exact h2)
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨h1, _⟩, _⟩
    exact hrc h1

lemma hrow_perm (σ : Equiv.Perm (Fin 7)) (r : Fin 3 → Fin 7) : hrow (fun j => σ (r j)) ↔ hrow r := by
  unfold hrow
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]

lemma ok_perm (σ : Equiv.Perm (Fin 7)) (r s : Fin 3 → Fin 7) :
    ok (fun j => σ (r j)) (fun j => σ (s j)) ↔ ok r s := by
  unfold ok
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]

/-! ## Renaming the values introduced before a row

W(n, r, c) does not change when the values below c are permuted among themselves (the values from c
on, which the array still has to introduce in order, stay fixed). The kernel checks then run over
the rows whose values below c appear in order of first occurrence (`canon` fixes them). -/

/-- σ fixes every value from c on. -/
def FixFrom (c : ℕ) (σ : Equiv.Perm (Fin 7)) : Prop := ∀ v : Fin 7, c ≤ v.val → σ v = v

lemma fixFrom_lt (c : ℕ) (σ : Equiv.Perm (Fin 7)) (h : FixFrom c σ) (v : Fin 7)
    (hv : v.val < c) : (σ v).val < c := by
  by_contra hc
  push_neg at hc
  have h1 : σ (σ v) = σ v := h (σ v) hc
  have h2 : σ v = v := σ.injective h1
  rw [h2] at hc
  omega

lemma fixFrom_symm (c : ℕ) (σ : Equiv.Perm (Fin 7)) (h : FixFrom c σ) : FixFrom c σ.symm := by
  intro v hv
  rw [Equiv.symm_apply_eq]
  exact (h v hv).symm

lemma RGSfrom_perm {R : ℕ} (c : ℕ) (σ : Equiv.Perm (Fin 7)) (h : FixFrom c σ)
    (g : Fin R → Fin 3 → Fin 7) (H : RGSfrom c g) : RGSfrom c (fun i j => σ (g i j)) := by
  intro i j u hu
  by_cases huc : u.val < c
  · exact Or.inl huc
  · push_neg at huc
    have hv : c ≤ (g i j).val := by
      by_contra hv
      push_neg at hv
      have h1 := fixFrom_lt c σ h (g i j) hv
      have h2 : u.val < (σ (g i j)).val := hu
      omega
    have hσv : σ (g i j) = g i j := h _ hv
    have hu' : u < g i j := by
      have h2 : u.val < (σ (g i j)).val := hu
      rw [hσv] at h2
      exact h2
    rcases H i j u hu' with h1 | ⟨i', j', hb, he⟩
    · omega
    · right
      refine ⟨i', j', hb, ?_⟩
      show σ (g i' j') = u
      rw [he]
      exact h u huc

lemma RGSfrom_perm_iff {R : ℕ} (c : ℕ) (σ : Equiv.Perm (Fin 7)) (h : FixFrom c σ)
    (g : Fin R → Fin 3 → Fin 7) : RGSfrom c (fun i j => σ (g i j)) ↔ RGSfrom c g := by
  constructor
  · intro H
    have := RGSfrom_perm c σ.symm (fixFrom_symm c σ h) _ H
    simpa using this
  · exact RGSfrom_perm c σ h g

lemma W_perm (σ : Equiv.Perm (Fin 7)) (c : ℕ) (hσ : FixFrom c σ) (n : ℕ) (r : Fin 3 → Fin 7) :
    W n (fun j => σ (r j)) c = W n r c := by
  have hv : ∀ {m : ℕ} (g : Fin m → Fin 3 → Fin 7), Valid (fun i j => σ (g i j)) ↔ Valid g := by
    intro m g
    unfold Valid
    simp only [hrow_perm, ok_perm]
  unfold W
  refine Finset.card_bij' (fun g _ => fun i j => σ.symm (g i j)) (fun g _ => fun i j => σ (g i j))
    ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨h1, h2, h3⟩ := hg
    refine ⟨?_, ?_, ?_⟩
    · rw [← hv]
      simpa using h1
    · rw [← RGSfrom_perm_iff c σ hσ]
      simpa using h2
    · funext j
      simp [h3]
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨h1, h2, h3⟩ := hg
    exact ⟨(hv g).2 h1, (RGSfrom_perm_iff c σ hσ g).2 h2, by rw [h3]⟩
  · intro g _
    funext i j
    simp
  · intro g _
    funext i j
    simp

/-- The swap of v with the label m (mod 7) when v is below c and not below the label; the
identity otherwise. -/
def sw (c m : ℕ) (v : Fin 7) : Equiv.Perm (Fin 7) :=
  if v.val < c ∧ m % 7 ≤ v.val then Equiv.swap v ⟨m % 7, Nat.mod_lt _ (by norm_num)⟩
  else Equiv.refl _

lemma sw_fix (c m : ℕ) (v : Fin 7) : FixFrom c (sw c m v) := by
  intro u hu
  unfold sw
  split_ifs with h
  · rw [Equiv.swap_apply_of_ne_of_ne]
    · intro e
      rw [e] at hu
      omega
    · intro e
      rw [e] at hu
      simp at hu
      omega
  · rfl

/-- Rename the value at position j of r to the label m, when it is below c and not yet renamed. -/
def stepAt (c m : ℕ) (j : Fin 3) (r : Fin 3 → Fin 7) : Fin 3 → Fin 7 := fun i => sw c m (r j) (r i)

/-- The next label after position j. -/
def nextM (c m : ℕ) (j : Fin 3) (r : Fin 3 → Fin 7) : ℕ :=
  if (r j).val < c ∧ (r j).val = m % 7 then m + 1 else m

lemma W_stepAt (n c m : ℕ) (j : Fin 3) (r : Fin 3 → Fin 7) : W n (stepAt c m j r) c = W n r c :=
  W_perm (sw c m (r j)) c (sw_fix c m (r j)) n r

/-- The values of r below c renamed in order of first occurrence. -/
def canon (c : ℕ) (r : Fin 3 → Fin 7) : Fin 3 → Fin 7 :=
  let r1 := stepAt c 0 0 r
  let m1 := nextM c 0 0 r1
  let r2 := stepAt c m1 1 r1
  let m2 := nextM c m1 1 r2
  let r3 := stepAt c m2 2 r2
  r3

lemma W_canon (n c : ℕ) (r : Fin 3 → Fin 7) : W n (canon c r) c = W n r c := by
  unfold canon
  simp only [W_stepAt]

/-- The swap of the values a and b, by cases (the kernel evaluates it faster than `Equiv.swap`). -/
def swV (a b v : Fin 7) : Fin 7 := if v = a then b else if v = b then a else v

/-- `stepAt` by cases. -/
def stepV (c m : ℕ) (j : Fin 3) (r : Fin 3 → Fin 7) : Fin 3 → Fin 7 :=
  if (r j).val < c ∧ m % 7 ≤ (r j).val then
    fun i => swV (r j) ⟨m % 7, Nat.mod_lt _ (by norm_num)⟩ (r i)
  else r

lemma stepV_eq (c m : ℕ) (j : Fin 3) (r : Fin 3 → Fin 7) : stepV c m j r = stepAt c m j r := by
  unfold stepV stepAt sw
  split_ifs with h
  · funext i
    rw [Equiv.swap_apply_def]
    rfl
  · rfl

/-- `canon` by cases. -/
def canonV (c : ℕ) (r : Fin 3 → Fin 7) : Fin 3 → Fin 7 :=
  let r1 := stepV c 0 0 r
  let m1 := nextM c 0 0 r1
  let r2 := stepV c m1 1 r1
  let m2 := nextM c m1 1 r2
  let r3 := stepV c m2 2 r2
  r3

lemma canonV_eq' (c : ℕ) (r : Fin 3 → Fin 7) : canon c r = canonV c r := by
  unfold canon canonV
  simp only [stepV_eq]

/-- `canonV c r = r` as a Boolean. -/
def isCanon (c : ℕ) (r : Fin 3 → Fin 7) : Bool :=
  decide (canonV c r 0 = r 0) &&
    decide (canonV c r 1 = r 1) &&
    decide (canonV c r 2 = r 2)

lemma isCanon_of_eq (c : ℕ) (r : Fin 3 → Fin 7) (h : canonV c r = r) : isCanon c r = true := by
  unfold isCanon
  rw [h]
  simp

lemma isCanon_eq (c : ℕ) (r : Fin 3 → Fin 7) (h : isCanon c r = true) : canonV c r = r := by
  unfold isCanon at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  funext j
  fin_cases j
  · exact h.1.1
  · exact h.1.2
  · exact h.2

lemma canon_idem : ∀ c : Fin 8, ∀ y1 y2 y3 : Fin 7,
    isCanon c.val (canonV c.val ![y1, y2, y3]) = true := by
  decide +kernel

/-! ## Kernel form of the transfer -/

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 7) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 7, f s = ∑ x : Fin 7, ∑ t : Fin m → Fin 7, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 7).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : (Fin 3 → Fin 7) → ℕ) :
    ∑ s : Fin 3 → Fin 7, f s = ∑ x : Fin 7, ∑ y : Fin 7, ∑ z : Fin 7, f ![x, y, z] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

lemma row_eta (r : Fin 3 → Fin 7) : r = ![r 0, r 1, r 2] := by
  funext j
  fin_cases j <;> rfl

/-! Fast Boolean forms of the conditions for the kernel checks. -/

/-- `hrow r` as a Boolean. -/
def hrowB (r : Fin 3 → Fin 7) : Bool :=
  decide (r 0 ≠ r 1) && decide (r 1 ≠ r 2) && decide (r 2 ≠ r 0)

/-- `ok r s` as a Boolean. -/
def okB (r s : Fin 3 → Fin 7) : Bool :=
  decide (r 0 ≠ s 0) && decide (r 1 ≠ s 1) && decide (r 2 ≠ s 2)

/-- `rowRgs c r` as a Boolean. -/
def rgsB (c : ℕ) (r : Fin 3 → Fin 7) : Bool :=
  decide ((r 0).val ≤ c) &&
    decide ((r 1).val ≤ max c ((r 0).val + 1)) &&
    decide ((r 2).val ≤ max (max c ((r 0).val + 1)) ((r 1).val + 1))

/-- `newc c r` by explicit maxima. -/
def newcB (c : ℕ) (r : Fin 3 → Fin 7) : ℕ :=
  max (max (max c ((r 0).val + 1)) ((r 1).val + 1)) ((r 2).val + 1)

lemma hrowB_eq : ∀ y1 y2 y3 : Fin 7, decide (hrow ![y1, y2, y3]) = hrowB ![y1, y2, y3] := by
  decide +kernel

lemma rgsB_eq : ∀ c : Fin 8, ∀ y1 y2 y3 : Fin 7,
    decide (rowRgs c.val ![y1, y2, y3]) = rgsB c.val ![y1, y2, y3] := by
  decide +kernel

lemma newcB_eq : ∀ c : Fin 8, ∀ y1 y2 y3 : Fin 7,
    newc c.val ![y1, y2, y3] = newcB c.val ![y1, y2, y3] := by
  decide +kernel

lemma hrowB_iff (r : Fin 3 → Fin 7) : hrow r ↔ hrowB r = true := by
  rw [row_eta r, ← hrowB_eq, decide_eq_true_iff]

lemma ok_iffB (r s : Fin 3 → Fin 7) : ok r s ↔ okB r s = true := by
  unfold ok okB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2

lemma rgsB_iff (c : ℕ) (hc : c ≤ 7) (r : Fin 3 → Fin 7) : rowRgs c r ↔ rgsB c r = true := by
  rw [row_eta r, ← rgsB_eq ⟨c, by omega⟩, decide_eq_true_iff]

lemma newcB_eq' (c : ℕ) (hc : c ≤ 7) (r : Fin 3 → Fin 7) : newc c r = newcB c r := by
  rw [row_eta r]
  exact newcB_eq ⟨c, by omega⟩ (r 0) (r 1) (r 2)

lemma newcB_le (c : ℕ) (hc : c ≤ 7) (r : Fin 3 → Fin 7) : newcB c r ≤ 7 := by
  rw [← newcB_eq' c hc r]
  exact newc_le c hc r

/-- One step of the transfer, the rows below r enumerated entry by entry. -/
def T (g : (Fin 3 → Fin 7) → ℕ → ℕ) (r : Fin 3 → Fin 7) (c : ℕ) : ℕ :=
  if hrowB r = true ∧ rgsB c r = true then
    ∑ x : Fin 7, ∑ y : Fin 7, ∑ z : Fin 7, (if okB r ![x, y, z] = true then g ![x, y, z] (newcB c r) else 0) else 0

lemma W_succT (n : ℕ) (r : Fin 3 → Fin 7) (c : ℕ) (hc : c ≤ 7) : W (n + 1) r c = T (W n) r c := by
  rw [W_succ, sum_row]
  unfold T
  simp only [hrowB_iff, rgsB_iff c hc, ok_iffB, newcB_eq' c hc]

lemma T_congr (g g' : (Fin 3 → Fin 7) → ℕ → ℕ) (r : Fin 3 → Fin 7) (c : ℕ)
    (h : ∀ s, g s (newcB c r) = g' s (newcB c r)) : T g r c = T g' r c := by
  unfold T
  simp only [h]

/-- W(0) as a function. -/
def W0f (s : Fin 3 → Fin 7) (c : ℕ) : ℕ := if hrowB s = true ∧ rgsB c s = true then 1 else 0

lemma W_zero' (s : Fin 3 → Fin 7) (c : ℕ) (hc : c ≤ 7) : W 0 s c = W0f s c := by
  rw [W_zero]
  unfold W0f
  simp only [hrowB_iff, rgsB_iff c hc]

lemma canon_canon (c : ℕ) (hc : c ≤ 7) (r : Fin 3 → Fin 7) : canonV c (canonV c r) = canonV c r := by
  apply isCanon_eq
  rw [row_eta r]
  exact canon_idem ⟨c, by omega⟩ (r 0) (r 1) (r 2)

lemma W_canonV (n c : ℕ) (r : Fin 3 → Fin 7) (hc : c ≤ 7) : W n (canonV c r) c = W n r c := by
  rw [← canonV_eq' c r]
  exact W_canon n c r

/-- W(1, r, c) for c <= 7, nested by the entries of r and then c. -/
def L1 : List (List (List (List ℕ))) :=
  [[[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [18, 18, 18, 18, 42, 83, 134, 134], [0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 18, 18, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 42, 42, 42, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 83, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 134, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 18, 18, 18, 42, 83, 134, 134], [0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 18, 18, 18, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 42, 42, 42, 42, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 83, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 134, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134]], [[0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 18, 18, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 42, 42, 42, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 18, 18, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 42, 42, 42, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 42, 42, 42, 83, 134, 134], [0, 0, 42, 42, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 83, 83, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 134, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134]], [[0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 83, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 83, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 42, 42, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 83, 83, 83, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 83, 83, 83, 134, 134], [0, 0, 0, 83, 83, 83, 134, 134], [0, 0, 0, 83, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 134, 134, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134]], [[0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 134, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 134, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 134, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 83, 83, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 134, 134, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 134, 134, 134, 134], [0, 0, 0, 0, 134, 134, 134, 134], [0, 0, 0, 0, 134, 134, 134, 134], [0, 0, 0, 0, 134, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 134, 134, 134, 134]], [[0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134]], [[0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134]], [[0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134]], [[0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134]], [[0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 134, 134, 134]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 134, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 134, 134], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]]

/-- W(1) as a table. -/
def tab1 (r : Fin 3 → Fin 7) (c : ℕ) : ℕ := (((L1.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD c 0

/-- W(1) read at the renamed row. -/
def tabc1 (r : Fin 3 → Fin 7) (c : ℕ) : ℕ := tab1 (canonV c r) c

/-- W(2, r, c) for c <= 7, nested by the entries of r and then c. -/
def L2 : List (List (List (List ℕ))) :=
  [[[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1046, 1046, 1046, 1046, 3545, 9490, 17956, 17956], [0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1046, 1046, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3545, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 9490, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1046, 1046, 1046, 3545, 9490, 17956, 17956], [0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 1046, 1046, 1046, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 3545, 3545, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 9490, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1046, 1046, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3545, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 1046, 1046, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 3545, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 3545, 3545, 3545, 9490, 17956, 17956], [0, 0, 3545, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 9490, 9490, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 9490, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 9490, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 3545, 3545, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 9490, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 9490, 9490, 9490, 17956, 17956], [0, 0, 0, 9490, 9490, 9490, 17956, 17956], [0, 0, 0, 9490, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 17956, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 9490, 9490, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 17956, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 17956, 17956, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956]], [[0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956]], [[0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956]], [[0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956]], [[0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 17956, 17956, 17956]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 17956, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 17956, 17956], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]]

/-- W(2) as a table. -/
def tab2 (r : Fin 3 → Fin 7) (c : ℕ) : ℕ := (((L2.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD c 0

/-- W(2) read at the renamed row. -/
def tabc2 (r : Fin 3 → Fin 7) (c : ℕ) : ℕ := tab2 (canonV c r) c

/-- W(3, r, c) for c <= 7, nested by the entries of r and then c. -/
def L3 : List (List (List (List ℕ))) :=
  [[[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [108893, 108893, 108893, 108893, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 108893, 108893, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 417845, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1219436, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 108893, 108893, 108893, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 108893, 108893, 108893, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 417845, 417845, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1219436, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 108893, 108893, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 417845, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 108893, 108893, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 417845, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 417845, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 417845, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1219436, 1219436, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1219436, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1219436, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 417845, 417845, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1219436, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 1219436, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 1219436, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 1219436, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 2406104, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 1219436, 1219436, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2406104, 2406104, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104]], [[0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104]], [[0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104]], [[0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104]], [[0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 2406104, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]], [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 2406104, 2406104], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]]

/-- W(3) as a table. -/
def tab3 (r : Fin 3 → Fin 7) (c : ℕ) : ℕ := (((L3.getD (r 0).val []).getD (r 1).val []).getD (r 2).val []).getD c 0

/-- W(3) read at the renamed row. -/
def tabc3 (r : Fin 3 → Fin 7) (c : ℕ) : ℕ := tab3 (canonV c r) c

lemma check1 : ∀ c : Fin 8, ∀ x y z : Fin 7, 
    isCanon c.val ![x, y, z] = true →
    T W0f ![x, y, z] c.val = tab1 ![x, y, z] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma check2 : ∀ c : Fin 8, ∀ x y z : Fin 7, 
    isCanon c.val ![x, y, z] = true →
    T tabc1 ![x, y, z] c.val = tab2 ![x, y, z] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma check3 : ∀ c : Fin 8, ∀ x y z : Fin 7, 
    isCanon c.val ![x, y, z] = true →
    T tabc2 ![x, y, z] c.val = tab3 ![x, y, z] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma check_rel : ∀ c : Fin 8, ∀ x y z : Fin 7, 
    isCanon c.val ![x, y, z] = true →
    T tabc3 ![x, y, z] c.val + 6468 * tab2 ![x, y, z] c.val + 94336 * W0f ![x, y, z] c.val =
      179 * tab3 ![x, y, z] c.val + 59396 * tab1 ![x, y, z] c.val := by
  intro c
  fin_cases c <;> decide +kernel

lemma W_1 (r : Fin 3 → Fin 7) (c : ℕ) (hc : c ≤ 7) : W 1 r c = tabc1 r c := by
  rw [← W_canonV 1 c r hc]
  unfold tabc1
  have hcan := canon_canon c hc r
  generalize canonV c r = r' at hcan ⊢
  have hg := isCanon_of_eq c r' hcan
  rw [show W 1 r' c = W (0 + 1) r' c from rfl, W_succT _ r' c hc,
    T_congr _ W0f r' c (fun s => W_zero' s _ (newcB_le c hc r'))]
  rw [row_eta r'] at hg ⊢
  exact check1 ⟨c, by omega⟩ (r' 0) (r' 1) (r' 2) hg

lemma W_2 (r : Fin 3 → Fin 7) (c : ℕ) (hc : c ≤ 7) : W 2 r c = tabc2 r c := by
  rw [← W_canonV 2 c r hc]
  unfold tabc2
  have hcan := canon_canon c hc r
  generalize canonV c r = r' at hcan ⊢
  have hg := isCanon_of_eq c r' hcan
  rw [show W 2 r' c = W (1 + 1) r' c from rfl, W_succT _ r' c hc,
    T_congr _ tabc1 r' c (fun s => W_1 s _ (newcB_le c hc r'))]
  rw [row_eta r'] at hg ⊢
  exact check2 ⟨c, by omega⟩ (r' 0) (r' 1) (r' 2) hg

lemma W_3 (r : Fin 3 → Fin 7) (c : ℕ) (hc : c ≤ 7) : W 3 r c = tabc3 r c := by
  rw [← W_canonV 3 c r hc]
  unfold tabc3
  have hcan := canon_canon c hc r
  generalize canonV c r = r' at hcan ⊢
  have hg := isCanon_of_eq c r' hcan
  rw [show W 3 r' c = W (2 + 1) r' c from rfl, W_succT _ r' c hc,
    T_congr _ tabc2 r' c (fun s => W_2 s _ (newcB_le c hc r'))]
  rw [row_eta r'] at hg ⊢
  exact check3 ⟨c, by omega⟩ (r' 0) (r' 1) (r' 2) hg

lemma W_rec (n : ℕ) : ∀ (r : Fin 3 → Fin 7) (c : ℕ), c ≤ 7 →
    W (n + 4) r c + 6468 * W (n + 2) r c + 94336 * W n r c = 179 * W (n + 3) r c + 59396 * W (n + 1) r c := by
  induction n with
  | zero =>
    intro r c hc
    rw [show W (0 + 4) r c = W 4 r c from rfl, show W (0 + 3) r c = W 3 r c from rfl, show W (0 + 2) r c = W 2 r c from rfl, show W (0 + 1) r c = W 1 r c from rfl]
    rw [← W_canonV 4 c r hc, ← W_canonV 3 c r hc, ← W_canonV 2 c r hc, ← W_canonV 1 c r hc, ← W_canonV 0 c r hc]
    have hcan := canon_canon c hc r
    generalize canonV c r = r' at hcan ⊢
    have hg := isCanon_of_eq c r' hcan
    rw [show W 4 r' c = W (3 + 1) r' c from rfl, W_succT 3 r' c hc,
      T_congr _ tabc3 r' c (fun s => W_3 s _ (newcB_le c hc r')),
      W_zero' r' c hc,
      W_1 r' c hc,
      W_2 r' c hc,
      W_3 r' c hc]
    simp only [tabc1, tabc2, tabc3, hcan]
    rw [row_eta r'] at hg ⊢
    exact check_rel ⟨c, by omega⟩ (r' 0) (r' 1) (r' 2) hg
  | succ n ih =>
    intro r c hc
    rw [W_succT (n + 4) r c hc, W_succT (n + 3) r c hc, W_succT (n + 2) r c hc, W_succT (n + 1) r c hc, W_succT n r c hc]
    unfold T
    split_ifs with h
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      split_ifs
      · exact ih _ _ (newcB_le c hc r)
      · simp
    · simp

lemma a_eq (n : ℕ) : a (n + 1) = ∑ r : Fin 3 → Fin 7, W n r 0 := by
  unfold a W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr (fun f _ => ?_))
  rw [cond_iff, rmn_iff, and_assoc]

lemma a_rec (n : ℕ) : a (n + 5) + 6468 * a (n + 3) + 94336 * a (n + 1) = 179 * a (n + 4) + 59396 * a (n + 2) := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  exact W_rec n r 0 (by norm_num)

lemma a_one : a 1 = 1 := by
  rw [a_eq 0, sum_row]
  simp only [W_zero]
  decide +kernel

lemma a_two : a 2 = 18 := by
  have h : ∀ r, W 1 r 0 = tab1 r 0 := fun r => W_1 r 0 (by norm_num)
  rw [a_eq 1, sum_row]
  simp only [h]
  decide +kernel

lemma a_three : a 3 = 1046 := by
  have h : ∀ r, W 2 r 0 = tab2 r 0 := fun r => W_2 r 0 (by norm_num)
  rw [a_eq 2, sum_row]
  simp only [h]
  decide +kernel

lemma a_four : a 4 = 108893 := by
  have h : ∀ r, W 3 r 0 = tab3 r 0 := fun r => W_3 r 0 (by norm_num)
  rw [a_eq 3, sum_row]
  simp only [h]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(1 - 161x + 4292x^2 - 21313x^3) / ((1 - 2x)(1 - 11x)(1 - 32x)(1 - 134x)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - 2 * X) * (1 - 11 * X) * (1 - 32 * X) * (1 - 134 * X)) = X * (1 - 161 * X + 4292 * X ^ 2 - 21313 * X ^ 3) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - 2 * X) * (1 - 11 * X) * (1 - 32 * X) * (1 - 134 * X)) = A - A * X ^ 1 * C 179 + A * X ^ 2 * C 6468 - A * X ^ 3 * C 59396 + A * X ^ 4 * C 94336 := by
    rw [show (C (179 : ℚ) : ℚ⟦X⟧) = 179 from map_ofNat C 179,
      show (C (6468 : ℚ) : ℚ⟦X⟧) = 6468 from map_ofNat C 6468,
      show (C (59396 : ℚ) : ℚ⟦X⟧) = 59396 from map_ofNat C 59396,
      show (C (94336 : ℚ) : ℚ⟦X⟧) = 94336 from map_ofNat C 94336]
    ring
  have e2 : (X * (1 - 161 * X + 4292 * X ^ 2 - 21313 * X ^ 3) : ℚ⟦X⟧) = X ^ 1 * C 1 - X ^ 2 * C 161 + X ^ 3 * C 4292 - X ^ 4 * C 21313 := by
    rw [show (C (1 : ℚ) : ℚ⟦X⟧) = 1 from map_one C,
      show (C (161 : ℚ) : ℚ⟦X⟧) = 161 from map_ofNat C 161,
      show (C (4292 : ℚ) : ℚ⟦X⟧) = 4292 from map_ofNat C 4292,
      show (C (21313 : ℚ) : ℚ⟦X⟧) = 21313 from map_ofNat C 21313]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | n
  · simp
  · simp [a_one] <;> norm_num
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · simp [a_one, a_two, a_three, a_four] <;> norm_num
  · have h := a_rec n
    
    have hq : (a (n + 5) : ℚ) + 6468 * (a (n + 3) : ℚ) + 94336 * (a (n + 1) : ℚ) = 179 * (a (n + 4) : ℚ) + 59396 * (a (n + 2) : ℚ) := by exact_mod_cast h
    simp only [show ¬ (n + 5 = 0) by omega,
      if_false,
      if_true,
      show 1 ≤ n + 5 by omega,
      show n + 5 - 1 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 2 ≤ n + 5 by omega,
      show n + 5 - 2 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 3 ≤ n + 5 by omega,
      show n + 5 - 3 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show 4 ≤ n + 5 by omega,
      show n + 5 - 4 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 5 = 1) by omega,
      show ¬ (n + 5 = 2) by omega,
      show ¬ (n + 5 = 3) by omega,
      show ¬ (n + 5 = 4) by omega]
    linear_combination hq

theorem cf (b : ℕ → ℕ) (h1 : b 1 = 1) (h2 : b 2 = 18) (h3 : b 3 = 1046)
    (h4 : b 4 = 108893)
    (hr : ∀ n, b (n + 5) + 6468 * b (n + 3) + 94336 * b (n + 1) =
      179 * b (n + 4) + 59396 * b (n + 2)) :
    ∀ n : ℕ, 1 ≤ n → (b n : ℝ) =
      (2 ^ ((n : ℤ) - 4) * (67 ^ ((n : ℤ) - 1) + 9) + 11 ^ ((n : ℤ) - 1) +
        3 * 2 ^ (5 * (n : ℤ) - 7)) / 3 := by
  set H : ℕ → ℝ := fun n => 9 * 2 ^ n / 16 + 2 ^ n * 67 ^ n / 1072 + 11 ^ n / 11 +
    3 * 2 ^ (5 * n) / 128 with hH
  have key : ∀ k, (b (k + 1) : ℝ) * 3 = H (k + 1) ∧ (b (k + 2) : ℝ) * 3 = H (k + 2) ∧
      (b (k + 3) : ℝ) * 3 = H (k + 3) ∧ (b (k + 4) : ℝ) * 3 = H (k + 4) := by
    intro k
    induction k with
    | zero =>
      simp only [hH, Nat.zero_add]
      rw [h1, h2, h3, h4]
      norm_num
    | succ k ih =>
      obtain ⟨i1, i2, i3, i4⟩ := ih
      refine ⟨i2, i3, i4, ?_⟩
      have h := hr k
      have hq : ((b (k + 5) : ℕ) : ℝ) + 6468 * b (k + 3) + 94336 * b (k + 1) =
          179 * b (k + 4) + 59396 * b (k + 2) := by exact_mod_cast h
      rw [show k + 1 + 4 = k + 5 from rfl]
      simp only [hH] at i1 i2 i3 i4 ⊢
      linear_combination 3 * hq + 179 * i4 - 6468 * i3 + 59396 * i2 - 94336 * i1
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := (key k).1
  have e1 : (2 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - 4) = 2 ^ (k + 1) / 16 := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast]
    norm_num
  have e2 : (67 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - 1) = 67 ^ k := by
    rw [show ((k + 1 : ℕ) : ℤ) - 1 = ((k : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have e3 : (11 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - 1) = 11 ^ k := by
    rw [show ((k + 1 : ℕ) : ℤ) - 1 = ((k : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have e4 : (2 : ℝ) ^ (5 * ((k + 1 : ℕ) : ℤ) - 7) = 2 ^ (5 * (k + 1)) / 128 := by
    rw [show 5 * ((k + 1 : ℕ) : ℤ) - 7 = ((5 * (k + 1) : ℕ) : ℤ) - 7 by push_cast; ring,
      zpow_sub₀ (by norm_num), zpow_natCast]
    norm_num
  rw [e1, e2, e3, e4]
  have hb : (b (k + 1) : ℝ) = H (k + 1) / 3 := by linarith
  rw [hb]
  simp only [hH]
  ring

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ ((n : ℤ) - 4) * (67 ^ ((n : ℤ) - 1) + 9) + 11 ^ ((n : ℤ) - 1) +
        3 * 2 ^ (5 * (n : ℤ) - 7)) / 3 :=
  cf a a_one a_two a_three a_four a_rec

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - 2 * X) * (1 - 11 * X) * (1 - 32 * X) * (1 - 134 * X)) = X * (1 - 161 * X + 4292 * X ^ 2 - 21313 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ ((n : ℤ) - 4) * (67 ^ ((n : ℤ) - 1) + 9) + 11 ^ ((n : ℤ) - 1) +
        3 * 2 ^ (5 * (n : ℤ) - 7)) / 3 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and the first values. -/
theorem controls : a 1 = 1 ∧ a 2 = 18 ∧ a 3 = 1046 ∧ a 4 = 108893 ∧ a 5 = 13701111 ∧ a 6 = 1808609113 ∧ a 7 = 241491378451 ∧ a 8 = 32332391658753 ∧ a 9 = 4331663509964171 ∧ a 10 = 580414863999963833 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5
  have h1 := a_one; have h2 := a_two; have h3 := a_three; have h4 := a_four
  norm_num at r0 r1 r2 r3 r4 r5
  omega

end OMA.S_oeis_a214181

theorem OMA.solution : type_of% @OMA.S_oeis_a214181.main :=
  OMA.S_oeis_a214181.conjecture
