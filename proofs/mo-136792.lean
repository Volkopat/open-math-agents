import OMAStatements.S_mo_136792

open MeasureTheory Set Filter Topology

namespace MO136792Disproof

abbrev XSpace : Type := ℕ → ℕ
abbrev Code : Type := (List ℕ → ℕ) × (List ℕ → ℕ)

/-! ### Encoding tree codes and sequences of analytic-set codes into Baire space -/

def idxT (s : List ℕ) : ℕ := 3 * Encodable.encode s
def idxL (s : List ℕ) : ℕ := 3 * Encodable.encode s + 1
def idxC (n i : ℕ) (s : List ℕ) : ℕ :=
  3 * Nat.pair n (Nat.pair i (Encodable.encode s)) + 2

def TOf (x : XSpace) : List ℕ → ℕ := fun s => x (idxT s)
def LOf (x : XSpace) : List ℕ → ℕ := fun s => x (idxL s)
def codeOf (x : XSpace) : Code := (TOf x, LOf x)

def pack (T L : List ℕ → ℕ) (C : ℕ → ℕ × List ℕ → ℕ) (k : ℕ) : ℕ :=
  match k % 3 with
  | 0 =>
      match Encodable.decode (α := List ℕ) (k / 3) with
      | some s => T s
      | none => 0
  | 1 =>
      match Encodable.decode (α := List ℕ) (k / 3) with
      | some s => L s
      | none => 0
  | _ =>
      let p1 := Nat.unpair (k / 3)
      let p2 := Nat.unpair p1.2
      match Encodable.decode (α := List ℕ) p2.2 with
      | some s => C p1.1 (p2.1, s)
      | none => 0

lemma TOf_pack (T L : List ℕ → ℕ) (C : ℕ → ℕ × List ℕ → ℕ) :
    TOf (pack T L C) = T := by
  funext s
  have hmod : (3 * Encodable.encode s) % 3 = 0 := by omega
  have hdiv : (3 * Encodable.encode s) / 3 = Encodable.encode s := by omega
  simp [TOf, pack, idxT, hmod, hdiv]

lemma LOf_pack (T L : List ℕ → ℕ) (C : ℕ → ℕ × List ℕ → ℕ) :
    LOf (pack T L C) = L := by
  funext s
  have hmod : (3 * Encodable.encode s + 1) % 3 = 1 := by omega
  have hdiv : (3 * Encodable.encode s + 1) / 3 = Encodable.encode s := by omega
  simp [LOf, pack, idxL, hmod, hdiv]

lemma pack_idxC (T L : List ℕ → ℕ) (C : ℕ → ℕ × List ℕ → ℕ) (n i : ℕ) (s : List ℕ) :
    pack T L C (idxC n i s) = C n (i, s) := by
  set m := Nat.pair n (Nat.pair i (Encodable.encode s))
  have hmod : (3 * m + 2) % 3 = 2 := by omega
  have hdiv : (3 * m + 2) / 3 = m := by omega
  simp [pack, idxC, m, hmod, hdiv, Nat.unpair_pair]

/-! ### Encoding Z and Y into Baire space -/

def TOfZ (z : XSpace) : List ℕ → ℕ := fun s => z (3 * Encodable.encode s)
def LOfZ (z : XSpace) : List ℕ → ℕ := fun s => z (3 * Encodable.encode s + 1)
def codeOfZ (z : XSpace) : Code := (TOfZ z, LOfZ z)
def WOfZ (z : XSpace) : ℕ → ℕ := fun n => z (3 * n + 2)

def packZ (T L : List ℕ → ℕ) (w : ℕ → ℕ) (k : ℕ) : ℕ :=
  match k % 3 with
  | 0 =>
      match Encodable.decode (α := List ℕ) (k / 3) with
      | some s => T s
      | none => 0
  | 1 =>
      match Encodable.decode (α := List ℕ) (k / 3) with
      | some s => L s
      | none => 0
  | _ => w (k / 3)

lemma TOfZ_packZ (T L : List ℕ → ℕ) (w : ℕ → ℕ) : TOfZ (packZ T L w) = T := by
  funext s
  have hmod : (3 * Encodable.encode s) % 3 = 0 := by omega
  have hdiv : (3 * Encodable.encode s) / 3 = Encodable.encode s := by omega
  simp [TOfZ, packZ, hmod, hdiv]

lemma LOfZ_packZ (T L : List ℕ → ℕ) (w : ℕ → ℕ) : LOfZ (packZ T L w) = L := by
  funext s
  have hmod : (3 * Encodable.encode s + 1) % 3 = 1 := by omega
  have hdiv : (3 * Encodable.encode s + 1) / 3 = Encodable.encode s := by omega
  simp [LOfZ, packZ, hmod, hdiv]

lemma WOfZ_packZ (T L : List ℕ → ℕ) (w : ℕ → ℕ) : WOfZ (packZ T L w) = w := by
  funext n
  have hmod : (3 * n + 2) % 3 = 2 := by omega
  have hdiv : (3 * n + 2) / 3 = n := by omega
  simp [WOfZ, packZ, hmod, hdiv]

def zOfY (y : XSpace) : XSpace := fun k => y (3 * k)
def alphaOfY (y : XSpace) : ℕ → ℕ := fun n => y (3 * n + 1)
def vOfY (y : XSpace) : List ℕ → ℕ := fun s => y (3 * Encodable.encode s + 2)

def packY (z : XSpace) (α : ℕ → ℕ) (v : List ℕ → ℕ) (k : ℕ) : ℕ :=
  match k % 3 with
  | 0 => z (k / 3)
  | 1 => α (k / 3)
  | _ =>
      match Encodable.decode (α := List ℕ) (k / 3) with
      | some s => v s
      | none => 0

lemma zOfY_packY (z : XSpace) (α : ℕ → ℕ) (v : List ℕ → ℕ) :
    zOfY (packY z α v) = z := by
  funext k
  have hmod : (3 * k) % 3 = 0 := by omega
  have hdiv : (3 * k) / 3 = k := by omega
  simp [zOfY, packY, hmod, hdiv]

lemma alphaOfY_packY (z : XSpace) (α : ℕ → ℕ) (v : List ℕ → ℕ) :
    alphaOfY (packY z α v) = α := by
  funext n
  have hmod : (3 * n + 1) % 3 = 1 := by omega
  have hdiv : (3 * n + 1) / 3 = n := by omega
  simp [alphaOfY, packY, hmod, hdiv]

lemma vOfY_packY (z : XSpace) (α : ℕ → ℕ) (v : List ℕ → ℕ) :
    vOfY (packY z α v) = v := by
  funext s
  have hmod : (3 * Encodable.encode s + 2) % 3 = 2 := by omega
  have hdiv : (3 * Encodable.encode s + 2) / 3 = Encodable.encode s := by omega
  simp [vOfY, packY, hmod, hdiv]

/-! ### Finite initial segments of sequences in Baire space -/

def initList (α : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => initList α n ++ [α n]

lemma initList_length (α : ℕ → ℕ) (n : ℕ) : (initList α n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [initList, ih]

lemma initList_ne_nil (α : ℕ → ℕ) (n : ℕ) : initList α (n + 1) ≠ [] := by
  simp [initList]

lemma initList_succ_cons (α : ℕ → ℕ) (n : ℕ) :
    initList α (n + 1) = α 0 :: initList (fun m => α (m + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change initList α (n + 1) ++ [α (n + 1)] = _
      rw [ih]
      rfl

lemma initList_eq_iff (α β : ℕ → ℕ) (n : ℕ) :
    initList β n = initList α n ↔ ∀ j < n, β j = α j := by
  induction n with
  | zero => simp [initList]
  | succ n ih =>
      constructor
      · intro h j hj
        have hlen : (initList β n).length = (initList α n).length := by
          simp [initList_length]
        have hpair := List.append_inj h hlen
        have hbn : β n = α n := by simpa using hpair.2
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · exact ih.mp hpair.1 j hlt
        · exact hbn
      · intro h
        simp only [initList]
        have h1 : initList β n = initList α n :=
          ih.mpr fun j hj => h j (Nat.lt_succ_of_lt hj)
        have h2 : β n = α n := h n (Nat.lt_succ_self n)
        rw [h1, h2]

lemma isOpen_initList_eq (k : ℕ) (s : List ℕ) :
    IsOpen { α : ℕ → ℕ | initList α k = s } := by
  induction k generalizing s with
  | zero =>
      by_cases hs : [] = s
      · subst hs; simp [initList]
      · have : { α : ℕ → ℕ | initList α 0 = s } = ∅ := by
          ext α; simp [initList, hs]
        rw [this]; exact isOpen_empty
  | succ k ih =>
      refine List.reverseRecOn s ?_ ?_
      · have : { α : ℕ → ℕ | initList α (k + 1) = [] } = ∅ := by
          ext α; simp [initList]
        rw [this]; exact isOpen_empty
      · intro t a _
        have hset :
            { α : ℕ → ℕ | initList α (k + 1) = t ++ [a] } =
              { α : ℕ → ℕ | initList α k = t } ∩ ((fun α : ℕ → ℕ => α k) ⁻¹' {a}) := by
          ext α
          simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq, initList]
          constructor
          · intro h
            have h1 : [α k].length = [a].length := rfl
            have hpair := List.append_inj' h h1
            exact ⟨hpair.1, by simpa using hpair.2⟩
          · rintro ⟨h1, h2⟩
            rw [h1, h2]
        rw [hset]
        have hopen : IsOpen ((fun α : ℕ → ℕ => α k) ⁻¹' ({a} : Set ℕ)) :=
          (isOpen_discrete ({a} : Set ℕ)).preimage (continuous_apply k)
        exact (ih t).inter hopen

lemma measurableSet_initList_eq (k : ℕ) (s : List ℕ) :
    MeasurableSet { α : ℕ → ℕ | initList α k = s } :=
  (isOpen_initList_eq k s).measurableSet

/-! ### Diagonal analytic sets and universal coding of analytic subsets of Baire space -/

def D (n : ℕ) : Set XSpace :=
  { x | ∃ α : ℕ → ℕ, ∀ i : ℕ, ∃ k : ℕ, x (idxC n i (initList α k)) = x i + 1 }

lemma analyticSet_D (n : ℕ) : AnalyticSet (D n) := by
  let W : Set (XSpace × (ℕ → ℕ)) :=
    ⋂ i : ℕ, ⋃ k : ℕ, ⋃ s : List ℕ,
      { p : XSpace × (ℕ → ℕ) | initList p.2 k = s } ∩
      { p : XSpace × (ℕ → ℕ) | p.1 (idxC n i s) = p.1 i + 1 }
  have hW_meas : MeasurableSet W := by
    refine MeasurableSet.iInter fun i => MeasurableSet.iUnion fun k =>
      MeasurableSet.iUnion fun s => MeasurableSet.inter ?_ ?_
    · exact (measurableSet_initList_eq k s).preimage measurable_snd
    · exact measurableSet_eq_fun
        ((measurable_pi_apply (idxC n i s)).comp measurable_fst)
        (((measurable_pi_apply i).comp measurable_fst).add_const 1)
  have hW_an : AnalyticSet W := hW_meas.analyticSet
  have hD_eq : Prod.fst '' W = D n := by
    ext x
    constructor
    · rintro ⟨⟨x', α⟩, hmem, rfl⟩
      refine ⟨α, fun i => ?_⟩
      have hi := mem_iInter.mp hmem i
      rcases mem_iUnion.mp hi with ⟨k, hk⟩
      rcases mem_iUnion.mp hk with ⟨s, hs⟩
      rcases hs with ⟨hs1, hs2⟩
      exact ⟨k, by rw [hs1]; exact hs2⟩
    · rintro ⟨α, hα⟩
      refine ⟨(x, α), ?_, rfl⟩
      refine mem_iInter.mpr fun i => ?_
      rcases hα i with ⟨k, hk⟩
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨initList α k, ⟨rfl, hk⟩⟩⟩
  rw [← hD_eq]
  exact hW_an.image_of_continuous continuous_fst

lemma exists_code_of_analyticSet {A : Set XSpace} (hA : AnalyticSet A) :
    ∃ φ : ℕ × List ℕ → ℕ, ∀ x : XSpace,
      x ∈ A ↔ ∃ α : ℕ → ℕ, ∀ i : ℕ, ∃ k : ℕ, φ (i, initList α k) = x i + 1 := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf_cont, rfl⟩
  · refine ⟨fun _ => 0, fun x => ?_⟩
    simp only [mem_empty_iff_false, false_iff, not_exists, not_forall]
    intro α
    exact ⟨0, fun k hk => by omega⟩
  · classical
    let φ : ℕ × List ℕ → ℕ := fun p =>
      if h : ∃ v : ℕ, ∀ β : ℕ → ℕ, initList β p.2.length = p.2 → f β p.1 = v
      then Classical.choose h + 1
      else 0
    refine ⟨φ, fun x => ?_⟩
    constructor
    · rintro ⟨α, rfl⟩
      refine ⟨α, fun i => ?_⟩
      have hcont_i : Continuous (fun β : ℕ → ℕ => f β i) :=
        (continuous_apply i).comp hf_cont
      have hnhds : (fun β : ℕ → ℕ => f β i) ⁻¹' {f α i} ∈ 𝓝 α :=
        hcont_i.continuousAt.preimage_mem_nhds
          ((isOpen_discrete ({f α i} : Set ℕ)).mem_nhds rfl)
      rw [nhds_pi, Filter.mem_pi] at hnhds
      rcases hnhds with ⟨I, hI, t, ht, hsub⟩
      let k := hI.toFinset.sup id + 1
      have hconst : ∀ β : ℕ → ℕ, initList β (initList α k).length = initList α k →
          f β i = f α i := by
        intro β hβ
        rw [initList_length] at hβ
        have hβ' := (initList_eq_iff α β k).mp hβ
        have hmem_pi : β ∈ Set.pi I t := by
          intro j hj
          have hjk : j < k := Nat.lt_succ_of_le
            (Finset.le_sup (f := id) (hI.mem_toFinset.mpr hj))
          rw [hβ' j hjk]
          exact mem_of_mem_nhds (ht j)
        exact hsub hmem_pi
      have hex : ∃ v : ℕ, ∀ β : ℕ → ℕ,
          initList β (initList α k).length = initList α k → f β i = v :=
        ⟨f α i, hconst⟩
      refine ⟨k, ?_⟩
      simp only [φ, dif_pos hex]
      have hval : f α i = Classical.choose hex :=
        Classical.choose_spec hex α (by rw [initList_length])
      omega
    · rintro ⟨α, hα⟩
      refine ⟨α, funext fun i => ?_⟩
      rcases hα i with ⟨k, hk⟩
      by_cases hex : ∃ v : ℕ, ∀ β : ℕ → ℕ,
          initList β (initList α k).length = initList α k → f β i = v
      · simp only [φ, dif_pos hex] at hk
        have hval : f α i = Classical.choose hex :=
          Classical.choose_spec hex α (by rw [initList_length])
        omega
      · simp only [φ, dif_neg hex] at hk
        omega

/-! ### Well-founded Borel tree codes and evaluation -/

def WF (T : List ℕ → ℕ) : Prop :=
  ∀ α : ℕ → ℕ, ∃ n : ℕ, T (initList α (n + 1)) = 0

def child (T : List ℕ → ℕ) (s' s : List ℕ) : Prop :=
  ∃ k : ℕ, s' = s ++ [k] ∧ T (s ++ [k]) ≠ 0

def Reachable (T : List ℕ → ℕ) (s : List ℕ) : Prop :=
  ∀ i : ℕ, i < s.length → T (s.take (i + 1)) ≠ 0

def Valid (τ : Code) (w : ℕ → ℕ) (v : List ℕ → ℕ) : Prop :=
  ∀ s : List ℕ, Reachable τ.1 s →
    ((∃ k : ℕ, τ.1 (s ++ [k]) ≠ 0) ∧
      ((v s = 1 ∧ ∀ k : ℕ, τ.1 (s ++ [k]) ≠ 0 → v (s ++ [k]) = 0) ∨
       (v s = 0 ∧ ∃ k : ℕ, τ.1 (s ++ [k]) ≠ 0 ∧ v (s ++ [k]) ≠ 0))) ∨
    ((¬ ∃ k : ℕ, τ.1 (s ++ [k]) ≠ 0) ∧
      v s = if w (τ.2 s) = 0 then 0 else 1)

lemma reachable_nil (T : List ℕ → ℕ) : Reachable T [] := by
  intro i hi; simp at hi

lemma reachable_snoc {T : List ℕ → ℕ} {s : List ℕ} {k : ℕ} :
    Reachable T (s ++ [k]) ↔ Reachable T s ∧ T (s ++ [k]) ≠ 0 := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have hi' : i < (s ++ [k]).length := by simp; omega
      have htake : (s ++ [k]).take (i + 1) = s.take (i + 1) :=
        List.take_append_of_le_length (by omega)
      simpa [htake] using h i hi'
    · have hlen : s.length < (s ++ [k]).length := by simp
      have htake : (s ++ [k]).take (s.length + 1) = s ++ [k] :=
        List.take_of_length_le (by simp)
      simpa [htake] using h s.length hlen
  · rintro ⟨hs, hk⟩ i hi
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · have htake : (s ++ [k]).take (i + 1) = s.take (i + 1) :=
        List.take_append_of_le_length (by omega)
      rw [htake]; exact hs i hlt
    · have htake : (s ++ [k]).take (s.length + 1) = s ++ [k] :=
        List.take_of_length_le (by simp)
      rw [htake]; exact hk

lemma valid_zero_or_one {τ : Code} {w : ℕ → ℕ} {v : List ℕ → ℕ} {s : List ℕ}
    (hv : Valid τ w v) (hs : Reachable τ.1 s) : v s = 0 ∨ v s = 1 := by
  rcases hv s hs with ⟨_, ⟨h1, _⟩ | ⟨h0, _⟩⟩ | ⟨_, h⟩
  · exact Or.inr h1
  · exact Or.inl h0
  · split_ifs at h
    · exact Or.inl h
    · exact Or.inr h

lemma acc_nil_of_wf {T : List ℕ → ℕ} (hWF : WF T) : Acc (child T) [] := by
  classical
  by_contra h0
  have hstep : ∀ s : List ℕ, ¬ Acc (child T) s →
      ∃ k : ℕ, T (s ++ [k]) ≠ 0 ∧ ¬ Acc (child T) (s ++ [k]) := by
    intro s hs
    by_contra hnone
    push Not at hnone
    apply hs
    refine Acc.intro s fun s' hchild => ?_
    rcases hchild with ⟨k, rfl, hk⟩
    exact hnone k hk
  let nextK : List ℕ → ℕ := fun s =>
    if h : ∃ k : ℕ, T (s ++ [k]) ≠ 0 ∧ ¬ Acc (child T) (s ++ [k])
    then Classical.choose h else 0
  let branch : ℕ → List ℕ := Nat.rec [] fun _ s => s ++ [nextK s]
  let α : ℕ → ℕ := fun n => nextK (branch n)
  have hbranch_eq : ∀ n : ℕ, branch n = initList α n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change branch n ++ [α n] = initList α n ++ [α n]
        rw [ih]
  have hnotacc : ∀ n : ℕ, ¬ Acc (child T) (branch n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
        have hex := hstep (branch n) ih
        change ¬ Acc (child T) (branch n ++ [nextK (branch n)])
        simp only [nextK, dif_pos hex]
        exact (Classical.choose_spec hex).2
  have hall : ∀ n : ℕ, T (initList α (n + 1)) ≠ 0 := by
    intro n
    rw [← hbranch_eq (n + 1)]
    have hex := hstep (branch n) (hnotacc n)
    change T (branch n ++ [nextK (branch n)]) ≠ 0
    simp only [nextK, dif_pos hex]
    exact (Classical.choose_spec hex).1
  rcases hWF α with ⟨n, hn⟩
  exact hall n hn

lemma acc_of_reachable {T : List ℕ → ℕ} (hWF : WF T) (s : List ℕ) (hs : Reachable T s) :
    Acc (child T) s := by
  refine List.reverseRecOn s (fun _ => acc_nil_of_wf hWF) ?_ hs
  intro t k ih htk
  rcases reachable_snoc.mp htk with ⟨ht, hk⟩
  exact (ih ht).inv ⟨k, rfl, hk⟩

open Classical in
noncomputable def evalAcc (τ : Code) (w : ℕ → ℕ)
    (s : List ℕ) (h : Acc (child τ.1) s) : ℕ :=
  Acc.rec (motive := fun _ _ => ℕ)
    (fun t _ ih =>
      if _ : ∃ k : ℕ, τ.1 (t ++ [k]) ≠ 0 then
        if ∀ k : ℕ, (hk : τ.1 (t ++ [k]) ≠ 0) →
            ih (t ++ [k]) ⟨k, rfl, hk⟩ = 0
        then 1 else 0
      else
        if w (τ.2 t) = 0 then 0 else 1)
    h

open Classical in
lemma evalAcc_eq (τ : Code) (w : ℕ → ℕ) (s : List ℕ) (h : Acc (child τ.1) s) :
    evalAcc τ w s h =
      if _ : ∃ k : ℕ, τ.1 (s ++ [k]) ≠ 0 then
        if ∀ k : ℕ, (hk : τ.1 (s ++ [k]) ≠ 0) →
            evalAcc τ w (s ++ [k]) (h.inv ⟨k, rfl, hk⟩) = 0
        then 1 else 0
      else
        if w (τ.2 s) = 0 then 0 else 1 := by
  cases h
  rfl

open Classical in
noncomputable def evalVal (τ : Code) (w : ℕ → ℕ) (hWF : WF τ.1) (s : List ℕ) : ℕ :=
  if hs : Reachable τ.1 s then evalAcc τ w s (acc_of_reachable hWF s hs) else 0

lemma valid_evalVal (τ : Code) (w : ℕ → ℕ) (hWF : WF τ.1) :
    Valid τ w (evalVal τ w hWF) := by
  classical
  intro s hs
  have hval_s : evalVal τ w hWF s = evalAcc τ w s (acc_of_reachable hWF s hs) := by
    simp [evalVal, hs]
  by_cases hex : ∃ k : ℕ, τ.1 (s ++ [k]) ≠ 0
  · left
    refine ⟨hex, ?_⟩
    by_cases hall : ∀ k : ℕ, (hk : τ.1 (s ++ [k]) ≠ 0) →
        evalAcc τ w (s ++ [k]) ((acc_of_reachable hWF s hs).inv ⟨k, rfl, hk⟩) = 0
    · left
      have h1 : evalVal τ w hWF s = 1 := by
        rw [hval_s, evalAcc_eq, dif_pos hex, if_pos hall]
      refine ⟨h1, fun k hk => ?_⟩
      have hsk : Reachable τ.1 (s ++ [k]) := reachable_snoc.mpr ⟨hs, hk⟩
      simp only [evalVal, dif_pos hsk]
      exact hall k hk
    · right
      have h0 : evalVal τ w hWF s = 0 := by
        rw [hval_s, evalAcc_eq, dif_pos hex, if_neg hall]
      push Not at hall
      rcases hall with ⟨k, hk, hne⟩
      refine ⟨h0, k, hk, ?_⟩
      have hsk : Reachable τ.1 (s ++ [k]) := reachable_snoc.mpr ⟨hs, hk⟩
      simp only [evalVal, dif_pos hsk]
      exact hne
  · right
    refine ⟨hex, ?_⟩
    rw [hval_s, evalAcc_eq, dif_neg hex]

/-! ### Representing every set in `analyticSigma XSpace` by a well-founded Borel code -/

open Classical in
noncomputable def ind (A : ℕ → Set XSpace) (x : XSpace) (n : ℕ) : ℕ :=
  if x ∈ A n then 1 else 0

def Represented (E : Set XSpace) : Prop :=
  ∃ (τ : Code) (A : ℕ → Set XSpace),
    WF τ.1 ∧ (∀ n, AnalyticSet (A n)) ∧
      ∀ (x : XSpace) (v : List ℕ → ℕ),
        Valid τ (ind A x) v → (x ∈ E ↔ v [] = 1)

lemma represented_of_analyticSet {E : Set XSpace} (hE : AnalyticSet E) : Represented E := by
  refine ⟨(fun _ => 0, fun _ => 0), fun _ => E, ?_, fun _ => hE, ?_⟩
  · intro α; exact ⟨0, rfl⟩
  · intro x v hv
    rcases hv [] (reachable_nil _) with ⟨⟨_, hk⟩, _⟩ | ⟨_, h0⟩
    · exact absurd rfl hk
    · rw [h0]
      by_cases hx : x ∈ E <;> simp [ind, hx]

def complT (T : List ℕ → ℕ) : List ℕ → ℕ
  | 0 :: [] => 1
  | 0 :: a :: t => T (a :: t)
  | _ => 0

def complL (L : List ℕ → ℕ) : List ℕ → ℕ
  | 0 :: t => L t
  | _ => 0

lemma complT_cons_ne_nil (T : List ℕ → ℕ) {t : List ℕ} (ht : t ≠ []) :
    complT T (0 :: t) = T t := by
  cases t with
  | nil => contradiction
  | cons a t' => rfl

lemma complT_snoc (T : List ℕ → ℕ) (t : List ℕ) (k : ℕ) :
    complT T (0 :: (t ++ [k])) = T (t ++ [k]) :=
  complT_cons_ne_nil T (by simp)

lemma complT_singleton (T : List ℕ → ℕ) (k : ℕ) :
    complT T [k] = if k = 0 then 1 else 0 := by
  cases k with
  | zero => rfl
  | succ m => rfl

lemma wf_complT {T : List ℕ → ℕ} (hWF : WF T) : WF (complT T) := by
  intro α
  by_cases h0 : α 0 = 0
  · rcases hWF (fun m => α (m + 1)) with ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    rw [initList_succ_cons, h0, complT_cons_ne_nil T (initList_ne_nil _ _)]
    exact hm
  · refine ⟨0, ?_⟩
    change complT T [α 0] = 0
    rw [complT_singleton, if_neg h0]

lemma reachable_complT {T : List ℕ → ℕ} {t : List ℕ} (ht : Reachable T t) :
    Reachable (complT T) (0 :: t) := by
  intro i hi
  cases i with
  | zero =>
      change complT T [0] ≠ 0
      simp [complT]
  | succ j =>
      have hj : j < t.length := by simpa using hi
      have htake : (0 :: t).take (j + 2) = 0 :: t.take (j + 1) := rfl
      have hlen : (t.take (j + 1)).length = j + 1 := List.length_take_of_le (by omega)
      have hne : t.take (j + 1) ≠ [] := by
        intro hnil
        rw [hnil] at hlen
        simp at hlen
      rw [htake, complT_cons_ne_nil T hne]
      exact ht j hj

lemma represented_compl {E : Set XSpace} (hE : Represented E) : Represented Eᶜ := by
  rcases hE with ⟨⟨T, L⟩, A, hWF, hA, hspec⟩
  refine ⟨(complT T, complL L), A, wf_complT hWF, hA, ?_⟩
  intro x v hv
  have hv_sub : Valid (T, L) (ind A x) (fun t => v (0 :: t)) := by
    intro t ht
    have h := hv (0 :: t) (reachable_complT ht)
    simpa [complT_snoc, complL] using h
  have hE_iff : x ∈ E ↔ v [0] = 1 := hspec x (fun t => v (0 :: t)) hv_sub
  have hv0_bool : v [0] = 0 ∨ v [0] = 1 :=
    valid_zero_or_one (s := []) hv_sub (reachable_nil T)
  have hroot := hv [] (reachable_nil _)
  have hiff : v [] = 1 ↔ v [0] = 0 := by
    rcases hroot with ⟨_, ⟨h1, hall⟩ | ⟨h0, k, hk, hvk⟩⟩ | ⟨hno, _⟩
    · have hv0 : v [0] = 0 := hall 0 (by simp [complT])
      simp [h1, hv0]
    · simp only [List.nil_append] at hk hvk
      rw [complT_singleton] at hk
      have hk0 : k = 0 := by
        by_contra hne
        simp [hne] at hk
      subst hk0
      simp [h0, hvk]
    · exact absurd ⟨0, by simp [complT]⟩ hno
  rw [mem_compl_iff, hE_iff, hiff]
  rcases hv0_bool with h0 | h1
  · simp [h0]
  · simp [h1]

def norT (T : ℕ → List ℕ → ℕ) : List ℕ → ℕ
  | _ :: [] => 1
  | k :: a :: t => T k (a :: t)
  | [] => 0

def norL (L : ℕ → List ℕ → ℕ) : List ℕ → ℕ
  | k :: t => Nat.pair k (L k t)
  | [] => 0

def pairSets (A : ℕ → ℕ → Set XSpace) (m : ℕ) : Set XSpace :=
  A (Nat.unpair m).1 (Nat.unpair m).2

lemma ind_pairSets (A : ℕ → ℕ → Set XSpace) (x : XSpace) (k m : ℕ) :
    ind (pairSets A) x (Nat.pair k m) = ind (A k) x m := by
  unfold ind pairSets
  rw [Nat.unpair_pair]

lemma norT_cons_ne_nil (T : ℕ → List ℕ → ℕ) (k : ℕ) {t : List ℕ} (ht : t ≠ []) :
    norT T (k :: t) = T k t := by
  cases t with
  | nil => contradiction
  | cons a t' => rfl

lemma norT_snoc (T : ℕ → List ℕ → ℕ) (k : ℕ) (t : List ℕ) (m : ℕ) :
    norT T (k :: (t ++ [m])) = T k (t ++ [m]) :=
  norT_cons_ne_nil T k (by simp)

lemma wf_norT {T : ℕ → List ℕ → ℕ} (hWF : ∀ k, WF (T k)) : WF (norT T) := by
  intro α
  rcases hWF (α 0) (fun m => α (m + 1)) with ⟨m, hm⟩
  refine ⟨m + 1, ?_⟩
  rw [initList_succ_cons, norT_cons_ne_nil T (α 0) (initList_ne_nil _ _)]
  exact hm

lemma reachable_norT {T : ℕ → List ℕ → ℕ} (k : ℕ) {t : List ℕ} (ht : Reachable (T k) t) :
    Reachable (norT T) (k :: t) := by
  intro i hi
  cases i with
  | zero =>
      change norT T [k] ≠ 0
      simp [norT]
  | succ j =>
      have hj : j < t.length := by simpa using hi
      have htake : (k :: t).take (j + 2) = k :: t.take (j + 1) := rfl
      have hlen : (t.take (j + 1)).length = j + 1 := List.length_take_of_le (by omega)
      have hne : t.take (j + 1) ≠ [] := by
        intro hnil
        rw [hnil] at hlen
        simp at hlen
      rw [htake, norT_cons_ne_nil T k hne]
      exact ht j hj

lemma represented_iUnion {E : ℕ → Set XSpace} (hE : ∀ k, Represented (E k)) :
    Represented (⋃ k, E k) := by
  have hnor : Represented (⋃ k, E k)ᶜ := by
    choose τ A hWF hA hspec using hE
    let T : ℕ → List ℕ → ℕ := fun k => (τ k).1
    let L : ℕ → List ℕ → ℕ := fun k => (τ k).2
    refine ⟨(norT T, norL L), pairSets A, wf_norT hWF, fun m => hA _ _, ?_⟩
    intro x v hv
    have hv_sub : ∀ k, Valid (τ k) (ind (A k) x) (fun t => v (k :: t)) := by
      intro k t ht
      have h := hv (k :: t) (reachable_norT k ht)
      have hind : ind (pairSets A) x (norL L (k :: t)) = ind (A k) x (L k t) :=
        ind_pairSets A x k (L k t)
      simpa [T, L, norT_snoc, hind] using h
    have hE_iff : ∀ k, x ∈ E k ↔ v [k] = 1 :=
      fun k => hspec k x (fun t => v (k :: t)) (hv_sub k)
    have hv_bool : ∀ k, v [k] = 0 ∨ v [k] = 1 :=
      fun k => valid_zero_or_one (s := []) (hv_sub k) (reachable_nil _)
    have hroot := hv [] (reachable_nil _)
    have hiff : v [] = 1 ↔ ∀ k, v [k] = 0 := by
      rcases hroot with ⟨_, ⟨h1, hall⟩ | ⟨h0, k, _, hvk⟩⟩ | ⟨hno, _⟩
      · have hall' : ∀ k, v [k] = 0 := fun k => hall k (by simp [norT])
        simp [h1, hall']
      · simp only [List.nil_append] at hvk
        constructor
        · intro h; omega
        · intro hall; exact absurd (hall k) hvk
      · exact absurd ⟨0, by simp [norT]⟩ hno
    rw [mem_compl_iff, mem_iUnion, hiff]
    push Not
    constructor
    · intro h k
      rcases hv_bool k with h0 | h1
      · exact h0
      · exact absurd ((hE_iff k).mpr h1) (h k)
    · intro h k hk
      have h1 := (hE_iff k).mp hk
      have h0 := h k
      omega
  simpa [compl_compl] using represented_compl hnor

lemma represented_of_analyticSigma {E : Set XSpace}
    (hE : @MeasurableSet XSpace (OMA.S_mo_136792.analyticSigma XSpace) E) :
    Represented E := by
  refine @MeasurableSpace.generateFrom_induction XSpace {s : Set XSpace | AnalyticSet s}
    (fun s _ => Represented s) ?_ ?_ ?_ ?_ E hE
  · intro s hs _
    exact represented_of_analyticSet hs
  · exact represented_of_analyticSet analyticSet_empty
  · intro s _ ih
    exact represented_compl ih
  · intro s _ ih
    exact represented_iUnion ih

/-! ### Borel measurability of `Valid` and construction of `K`, `g`, `h` on Baire space -/

lemma measurableSet_valid :
    MeasurableSet { p : Code × (ℕ → ℕ) × (List ℕ → ℕ) | Valid p.1 p.2.1 p.2.2 } := by
  let S : List ℕ → Set (Code × (ℕ → ℕ) × (List ℕ → ℕ)) := fun s =>
    let R : Set (Code × (ℕ → ℕ) × (List ℕ → ℕ)) :=
      ⋂ (i : ℕ) (_ : i < s.length), { p | p.1.1 (s.take (i + 1)) ≠ 0 }
    let H : Set (Code × (ℕ → ℕ) × (List ℕ → ℕ)) :=
      ⋃ k : ℕ, { p | p.1.1 (s ++ [k]) ≠ 0 }
    let B1 : Set (Code × (ℕ → ℕ) × (List ℕ → ℕ)) :=
      { p | p.2.2 s = 1 } ∩
      ⋂ k : ℕ, ({ p | p.1.1 (s ++ [k]) ≠ 0 }ᶜ ∪ { p | p.2.2 (s ++ [k]) = 0 })
    let B2 : Set (Code × (ℕ → ℕ) × (List ℕ → ℕ)) :=
      { p | p.2.2 s = 0 } ∩
      ⋃ k : ℕ, ({ p | p.1.1 (s ++ [k]) ≠ 0 } ∩ { p | p.2.2 (s ++ [k]) ≠ 0 })
    let Lf : Set (Code × (ℕ → ℕ) × (List ℕ → ℕ)) :=
      ⋃ n : ℕ, ({ p | p.1.2 s = n } ∩
        (({ p | p.2.1 n = 0 } ∩ { p | p.2.2 s = 0 }) ∪
         ({ p | p.2.1 n ≠ 0 } ∩ { p | p.2.2 s = 1 })))
    Rᶜ ∪ ((H ∩ (B1 ∪ B2)) ∪ (Hᶜ ∩ Lf))
  have hEq : { p : Code × (ℕ → ℕ) × (List ℕ → ℕ) | Valid p.1 p.2.1 p.2.2 } = ⋂ s, S s := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, Valid]
    refine forall_congr' fun s => ?_
    dsimp only [S]
    simp only [mem_union, mem_compl_iff, mem_iInter, mem_iUnion, mem_inter_iff,
      mem_ofPred_eq, Reachable]
    constructor
    · intro h
      by_cases hR : ∀ i < s.length, p.1.1 (s.take (i + 1)) ≠ 0
      · right
        rcases h hR with ⟨hH, hB⟩ | ⟨hH, hL⟩
        · left
          refine ⟨hH, ?_⟩
          rcases hB with ⟨h1, hall⟩ | ⟨h0, h2⟩
          · left
            refine ⟨h1, fun k => ?_⟩
            by_cases hk : p.1.1 (s ++ [k]) ≠ 0
            · right; exact hall k hk
            · left; exact hk
          · right
            exact ⟨h0, h2⟩
        · right
          refine ⟨hH, p.1.2 s, rfl, ?_⟩
          by_cases hw : p.2.1 (p.1.2 s) = 0
          · left; exact ⟨hw, by simpa [hw] using hL⟩
          · right; exact ⟨hw, by simpa [hw] using hL⟩
      · left; exact hR
    · intro h hR
      rcases h with hnotR | ⟨hH, hB⟩ | ⟨hH, n, hn, hL⟩
      · exact absurd hR hnotR
      · left
        refine ⟨hH, ?_⟩
        rcases hB with ⟨h1, hall⟩ | ⟨h0, h2⟩
        · left
          refine ⟨h1, fun k hk => ?_⟩
          rcases hall k with hnotk | hv0
          · exact absurd hk hnotk
          · exact hv0
        · right
          exact ⟨h0, h2⟩
      · right
        refine ⟨hH, ?_⟩
        subst hn
        rcases hL with ⟨hw, hv⟩ | ⟨hw, hv⟩
        · simp [hw, hv]
        · simp [hw, hv]
  rw [hEq]
  refine MeasurableSet.iInter fun s => ?_
  have hT : ∀ t : List ℕ, Measurable (fun p : Code × (ℕ → ℕ) × (List ℕ → ℕ) => p.1.1 t) :=
    fun t => (measurable_pi_apply t).comp (measurable_fst.comp measurable_fst)
  have hL : ∀ t : List ℕ, Measurable (fun p : Code × (ℕ → ℕ) × (List ℕ → ℕ) => p.1.2 t) :=
    fun t => (measurable_pi_apply t).comp (measurable_snd.comp measurable_fst)
  have hW : ∀ n : ℕ, Measurable (fun p : Code × (ℕ → ℕ) × (List ℕ → ℕ) => p.2.1 n) :=
    fun n => (measurable_pi_apply n).comp (measurable_fst.comp measurable_snd)
  have hV : ∀ t : List ℕ, Measurable (fun p : Code × (ℕ → ℕ) × (List ℕ → ℕ) => p.2.2 t) :=
    fun t => (measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)
  have hR_m : MeasurableSet
      (⋂ (i : ℕ) (_ : i < s.length),
        { p : Code × (ℕ → ℕ) × (List ℕ → ℕ) | p.1.1 (s.take (i + 1)) ≠ 0 }) :=
    MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      (measurableSet_eq_fun (hT _) measurable_const).compl
  have hH_m : MeasurableSet
      (⋃ k : ℕ, { p : Code × (ℕ → ℕ) × (List ℕ → ℕ) | p.1.1 (s ++ [k]) ≠ 0 }) :=
    MeasurableSet.iUnion fun k => (measurableSet_eq_fun (hT _) measurable_const).compl
  have hB1_m : MeasurableSet
      ({ p : Code × (ℕ → ℕ) × (List ℕ → ℕ) | p.2.2 s = 1 } ∩
        ⋂ k : ℕ, ({ p | p.1.1 (s ++ [k]) ≠ 0 }ᶜ ∪ { p | p.2.2 (s ++ [k]) = 0 })) :=
    (measurableSet_eq_fun (hV s) measurable_const).inter <|
      MeasurableSet.iInter fun k =>
        (measurableSet_eq_fun (hT _) measurable_const).compl.compl.union
          (measurableSet_eq_fun (hV _) measurable_const)
  have hB2_m : MeasurableSet
      ({ p : Code × (ℕ → ℕ) × (List ℕ → ℕ) | p.2.2 s = 0 } ∩
        ⋃ k : ℕ, ({ p | p.1.1 (s ++ [k]) ≠ 0 } ∩ { p | p.2.2 (s ++ [k]) ≠ 0 })) :=
    (measurableSet_eq_fun (hV s) measurable_const).inter <|
      MeasurableSet.iUnion fun k =>
        (measurableSet_eq_fun (hT _) measurable_const).compl.inter
          (measurableSet_eq_fun (hV _) measurable_const).compl
  have hLf_m : MeasurableSet
      (⋃ n : ℕ, ({ p : Code × (ℕ → ℕ) × (List ℕ → ℕ) | p.1.2 s = n } ∩
        (({ p | p.2.1 n = 0 } ∩ { p | p.2.2 s = 0 }) ∪
         ({ p | p.2.1 n ≠ 0 } ∩ { p | p.2.2 s = 1 })))) :=
    MeasurableSet.iUnion fun n =>
      (measurableSet_eq_fun (hL s) measurable_const).inter <|
        ((measurableSet_eq_fun (hW n) measurable_const).inter
          (measurableSet_eq_fun (hV s) measurable_const)).union
        ((measurableSet_eq_fun (hW n) measurable_const).compl.inter
          (measurableSet_eq_fun (hV s) measurable_const))
  exact hR_m.compl.union ((hH_m.inter (hB1_m.union hB2_m)).union (hH_m.compl.inter hLf_m))

def KSet : Set (XSpace × XSpace) :=
  { p | (alphaOfY p.2 0 ≠ 0 ∧
          ∀ n : ℕ, TOfZ (zOfY p.2) (initList (fun m => alphaOfY p.2 (m + 1)) (n + 1)) ≠ 0) ∨
        (alphaOfY p.2 0 = 0 ∧ Valid (codeOfZ (zOfY p.2)) (WOfZ (zOfY p.2)) (vOfY p.2)) }

def gMap : XSpace × XSpace → XSpace := fun p => zOfY p.2

noncomputable def hMap : XSpace → XSpace :=
  fun x => packZ (TOf x) (LOf x) (ind D x)

lemma analyticSet_KSet : AnalyticSet KSet := by
  have hK_meas : MeasurableSet KSet := by
    let part1 : Set (XSpace × XSpace) :=
      { p | alphaOfY p.2 0 ≠ 0 } ∩
      ⋂ n : ℕ, ⋃ s : List ℕ,
        { p : XSpace × XSpace | initList (fun m => alphaOfY p.2 (m + 1)) (n + 1) = s } ∩
        { p : XSpace × XSpace | TOfZ (zOfY p.2) s ≠ 0 }
    let part2 : Set (XSpace × XSpace) :=
      { p | alphaOfY p.2 0 = 0 } ∩
      ((fun p : XSpace × XSpace => (codeOfZ (zOfY p.2), WOfZ (zOfY p.2), vOfY p.2)) ⁻¹'
        { q : Code × (ℕ → ℕ) × (List ℕ → ℕ) | Valid q.1 q.2.1 q.2.2 })
    have hEq : KSet = part1 ∪ part2 := by
      ext p
      simp only [KSet, part1, part2, mem_union, mem_inter_iff, mem_iInter, mem_iUnion,
        mem_preimage, mem_ofPred_eq]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · left
          exact ⟨h1, fun n => ⟨initList (fun m => alphaOfY p.2 (m + 1)) (n + 1), rfl, h2 n⟩⟩
        · right
          exact ⟨h1, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · left
          refine ⟨h1, fun n => ?_⟩
          rcases h2 n with ⟨s, hs, hne⟩
          rw [hs]
          exact hne
        · right
          exact ⟨h1, h2⟩
    rw [hEq]
    have hm_isInf : Measurable (fun p : XSpace × XSpace => alphaOfY p.2 0) :=
      (measurable_pi_apply (3 * 0 + 1)).comp measurable_snd
    have hm_alpha : Measurable (fun p : XSpace × XSpace => fun m : ℕ => alphaOfY p.2 (m + 1)) :=
      measurable_pi_lambda _ fun m =>
        (measurable_pi_apply (3 * (m + 1) + 1)).comp measurable_snd
    have hm_T : ∀ s : List ℕ, Measurable (fun p : XSpace × XSpace => TOfZ (zOfY p.2) s) := fun s =>
      (measurable_pi_apply (3 * (3 * Encodable.encode s))).comp measurable_snd
    have hm_proj : Measurable (fun p : XSpace × XSpace =>
        (codeOfZ (zOfY p.2), WOfZ (zOfY p.2), vOfY p.2)) := by
      refine ((measurable_pi_lambda _ fun s => hm_T s).prodMk
        (measurable_pi_lambda _ fun s =>
          (measurable_pi_apply (3 * (3 * Encodable.encode s + 1))).comp measurable_snd)).prodMk ?_
      refine (measurable_pi_lambda _ fun n =>
        (measurable_pi_apply (3 * (3 * n + 2))).comp measurable_snd).prodMk ?_
      exact measurable_pi_lambda _ fun s =>
        (measurable_pi_apply (3 * Encodable.encode s + 2)).comp measurable_snd
    have hp1 : MeasurableSet part1 :=
      (measurableSet_eq_fun hm_isInf measurable_const).compl.inter <|
        MeasurableSet.iInter fun n => MeasurableSet.iUnion fun s =>
          ((measurableSet_initList_eq (n + 1) s).preimage hm_alpha).inter
            (measurableSet_eq_fun (hm_T s) measurable_const).compl
    have hp2 : MeasurableSet part2 :=
      (measurableSet_eq_fun hm_isInf measurable_const).inter
        (measurableSet_valid.preimage hm_proj)
    exact hp1.union hp2
  exact hK_meas.analyticSet

lemma measurable_gMap :
    @Measurable (XSpace × XSpace) XSpace (borel (XSpace × XSpace)) (borel XSpace) gMap := by
  have h1 : borel (XSpace × XSpace) = (inferInstance : MeasurableSpace (XSpace × XSpace)) :=
    BorelSpace.measurable_eq.symm
  have h2 : borel XSpace = (inferInstance : MeasurableSpace XSpace) :=
    BorelSpace.measurable_eq.symm
  rw [h1, h2]
  exact measurable_pi_lambda _ fun k => (measurable_pi_apply (3 * k)).comp measurable_snd

lemma borel_le_analyticSigma :
    borel XSpace ≤ OMA.S_mo_136792.analyticSigma XSpace := by
  refine MeasurableSpace.generateFrom_mono fun s hs => ?_
  have hopen : IsOpen s := hs
  exact hopen.measurableSet.analyticSet

lemma measurable_hMap :
    @Measurable XSpace XSpace (OMA.S_mo_136792.analyticSigma XSpace) (borel XSpace) hMap := by
  have hZ : borel XSpace = (inferInstance : MeasurableSpace XSpace) :=
    BorelSpace.measurable_eq.symm
  rw [hZ]
  refine @measurable_pi_lambda XSpace ℕ (fun _ => ℕ) (OMA.S_mo_136792.analyticSigma XSpace) _ _ fun k => ?_
  have hm_coord : ∀ j : ℕ, @Measurable XSpace ℕ (OMA.S_mo_136792.analyticSigma XSpace) _
      (fun x => x j) := fun j => by
    have hm_borel : @Measurable XSpace ℕ (borel XSpace) _ (fun x => x j) := by
      have hX : borel XSpace = (inferInstance : MeasurableSpace XSpace) :=
        BorelSpace.measurable_eq.symm
      rw [hX]
      exact measurable_pi_apply j
    exact hm_borel.mono borel_le_analyticSigma le_rfl
  change @Measurable XSpace ℕ (OMA.S_mo_136792.analyticSigma XSpace) _
    (fun x => packZ (TOf x) (LOf x) (ind D x) k)
  unfold packZ
  rcases hmod : k % 3 with _ | _ | _
  · cases hdec : Encodable.decode (α := List ℕ) (k / 3) with
    | none => exact @measurable_const _ _ _ (OMA.S_mo_136792.analyticSigma XSpace) 0
    | some s => exact hm_coord (idxT s)
  · cases hdec : Encodable.decode (α := List ℕ) (k / 3) with
    | none => exact @measurable_const _ _ _ (OMA.S_mo_136792.analyticSigma XSpace) 0
    | some s => exact hm_coord (idxL s)
  · classical
    intro s _
    change @MeasurableSet XSpace (OMA.S_mo_136792.analyticSigma XSpace)
      ((fun x => ind D x (k / 3)) ⁻¹' s)
    have hpre : (fun x => ind D x (k / 3)) ⁻¹' s =
        (if (1 : ℕ) ∈ s then D (k / 3) else ∅) ∪ (if (0 : ℕ) ∈ s then (D (k / 3))ᶜ else ∅) := by
      ext x
      simp only [mem_preimage, ind, mem_union]
      by_cases hx : x ∈ D (k / 3) <;> by_cases h1 : (1 : ℕ) ∈ s <;> by_cases h0 : (0 : ℕ) ∈ s <;>
        simp [hx, h1, h0]
    rw [hpre]
    have hDn : @MeasurableSet XSpace (OMA.S_mo_136792.analyticSigma XSpace) (D (k / 3)) :=
      MeasurableSpace.measurableSet_generateFrom (analyticSet_D (k / 3))
    refine @MeasurableSet.union XSpace (OMA.S_mo_136792.analyticSigma XSpace) _ _ ?_ ?_
    · split_ifs
      · exact hDn
      · exact @MeasurableSet.empty XSpace (OMA.S_mo_136792.analyticSigma XSpace)
    · split_ifs
      · exact hDn.compl
      · exact @MeasurableSet.empty XSpace (OMA.S_mo_136792.analyticSigma XSpace)

lemma exists_lift_pointwise (x : XSpace) :
    ∃ y : XSpace, (x, y) ∈ KSet ∧ gMap (x, y) = hMap x := by
  set z := hMap x
  by_cases hWF : WF (TOfZ z)
  · let v := evalVal (codeOfZ z) (WOfZ z) hWF
    refine ⟨packY z (fun _ => 0) v, ?_, ?_⟩
    · right
      refine ⟨?_, ?_⟩
      · simp [alphaOfY_packY]
      · simp only [zOfY_packY, vOfY_packY]
        exact valid_evalVal (codeOfZ z) (WOfZ z) hWF
    · dsimp only [gMap]
      exact zOfY_packY z _ _
  · unfold WF at hWF
    push Not at hWF
    rcases hWF with ⟨α, hα⟩
    let α' : ℕ → ℕ := fun m => match m with | 0 => 1 | k + 1 => α k
    refine ⟨packY z α' (fun _ => 0), ?_, ?_⟩
    · left
      simp only [alphaOfY_packY, zOfY_packY]
      exact ⟨Nat.one_ne_zero, hα⟩
    · dsimp only [gMap]
      exact zOfY_packY z _ _

end MO136792Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_136792.main) := by
  intro hMain
  open MO136792Disproof in
  rcases hMain XSpace XSpace XSpace KSet gMap hMap
      analyticSet_KSet measurable_gMap measurable_hMap exists_lift_pointwise with
    ⟨f, hf_meas, hf_spec⟩
  let E : Set XSpace := { x : XSpace | vOfY (f x) [] = 0 }
  have hE_meas : @MeasurableSet XSpace (OMA.S_mo_136792.analyticSigma XSpace) E := by
    have hY : borel XSpace = (inferInstance : MeasurableSpace XSpace) :=
      BorelSpace.measurable_eq.symm
    have h0 : @MeasurableSet XSpace (borel XSpace) { y : XSpace | vOfY y [] = 0 } := by
      rw [hY]
      exact measurableSet_eq_fun (measurable_pi_apply (3 * Encodable.encode ([] : List ℕ) + 2))
        measurable_const
    exact hf_meas h0
  rcases represented_of_analyticSigma hE_meas with ⟨τ, A, hWF, hA, hspec⟩
  have hcodes : ∀ n : ℕ, ∃ φ : ℕ × List ℕ → ℕ, ∀ x : XSpace,
      x ∈ A n ↔ ∃ α : ℕ → ℕ, ∀ i : ℕ, ∃ k : ℕ, φ (i, initList α k) = x i + 1 :=
    fun n => exists_code_of_analyticSet (hA n)
  choose C hC using hcodes
  let xstar : XSpace := pack τ.1 τ.2 C
  have hD_eq_A : ∀ n : ℕ, xstar ∈ D n ↔ xstar ∈ A n := by
    intro n
    rw [hC n xstar]
    simp only [D, mem_ofPred_eq, xstar, pack_idxC]
  have hind_eq : ind D xstar = ind A xstar := by
    funext n
    simp only [ind]
    by_cases hn : xstar ∈ A n
    · have hDn : xstar ∈ D n := (hD_eq_A n).mpr hn
      simp [hn, hDn]
    · have hDn : xstar ∉ D n := mt (hD_eq_A n).mp hn
      simp [hn, hDn]
  have hh_eq : hMap xstar = packZ τ.1 τ.2 (ind A xstar) := by
    simp only [hMap, xstar, TOf_pack, LOf_pack, hind_eq]
  rcases hf_spec xstar with ⟨hK, hg⟩
  have hz_eq : zOfY (f xstar) = packZ τ.1 τ.2 (ind A xstar) := by
    simpa [gMap, hh_eq] using hg
  have hcode_eq : codeOfZ (zOfY (f xstar)) = τ := by
    rw [hz_eq]
    exact Prod.ext (TOfZ_packZ τ.1 τ.2 _) (LOfZ_packZ τ.1 τ.2 _)
  have hW_eq : WOfZ (zOfY (f xstar)) = ind A xstar := by
    rw [hz_eq]
    exact WOfZ_packZ τ.1 τ.2 _
  rcases hK with ⟨_, hinf⟩ | ⟨_, hvalid⟩
  · have hT_eq : TOfZ (zOfY (f xstar)) = τ.1 := by
      rw [hz_eq]
      exact TOfZ_packZ τ.1 τ.2 _
    rw [hT_eq] at hinf
    rcases hWF (fun m => alphaOfY (f xstar) (m + 1)) with ⟨n, hn⟩
    exact hinf n hn
  · rw [hcode_eq, hW_eq] at hvalid
    have hv_bool : vOfY (f xstar) [] = 0 ∨ vOfY (f xstar) [] = 1 :=
      valid_zero_or_one hvalid (reachable_nil τ.1)
    have hE_iff_1 : xstar ∈ E ↔ vOfY (f xstar) [] = 1 :=
      hspec xstar (vOfY (f xstar)) hvalid
    have hE_iff_0 : xstar ∈ E ↔ vOfY (f xstar) [] = 0 := Iff.rfl
    rcases hv_bool with h0 | h1
    · have : vOfY (f xstar) [] = 1 := hE_iff_1.mp (hE_iff_0.mpr h0)
      omega
    · have : vOfY (f xstar) [] = 0 := hE_iff_0.mp (hE_iff_1.mpr h1)
      omega
