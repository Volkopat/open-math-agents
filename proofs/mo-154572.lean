import OMAStatements.S_mo_154572

open OMA.S_mo_154572 Finset Set

variable {X V Z : Type} [Fintype X] [Fintype V] [Fintype Z]

private theorem feasible_iff (P : X → V → ℝ) (ε : ℝ) (K : X → Z → ℝ) :
    (∃ h : V → Z → ℝ, FeasibleLP P ε K h) ↔ Channel K ∧ leakage P K ≤ ε := by
  constructor
  · rintro ⟨h,hK,hh,hsum⟩
    refine ⟨hK, ?_⟩
    unfold leakage
    apply (div_le_iff₀ (by norm_num)).2
    have hb : ∑ z, ∑ v, |dv P K v z| ≤ ∑ z, ∑ v, h v z :=
      sum_le_sum fun z _ => sum_le_sum fun v _ => abs_le.mpr ⟨by linarith [(hh v z).2], (hh v z).1⟩
    linarith
  · rintro ⟨hK,hLeak⟩
    refine ⟨fun v z => |dv P K v z|, hK, fun v z => ⟨le_abs_self _, neg_le_abs _⟩, ?_⟩
    unfold leakage at hLeak
    linarith

private noncomputable def signs [DecidableEq X] (P : X → V → ℝ) (K : X → Z → ℝ) :
    Z → Finset X := fun z => univ.filter fun x => 0 ≤ dx P K x z

private theorem le_utility [DecidableEq X] (P : X → V → ℝ) (K : X → Z → ℝ) (s : Z → Finset X) :
    score P K s ≤ utility P K := by
  unfold score utility
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply sum_le_sum
  intro z _
  apply sum_le_sum
  intro x _
  split_ifs
  · simpa using le_abs_self (dx P K x z)
  · simpa using neg_le_abs (dx P K x z)

private theorem score_signs [DecidableEq X] (P : X → V → ℝ) (K : X → Z → ℝ) :
    score P K (signs P K) = utility P K := by
  unfold score utility
  congr 1
  apply sum_congr rfl
  intro z _
  apply sum_congr rfl
  intro x _
  by_cases hx : 0 ≤ dx P K x z
  · simp [signs, hx, abs_of_nonneg hx]
  · simp [signs, hx, abs_of_neg (lt_of_not_ge hx)]

private theorem fixed_maximum [DecidableEq X] [Nonempty Z] (P : X → V → ℝ)
    (hP : Joint P) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ m, IsGreatest (values P ε Z) m ∧ IsGreatest (⋃ s : Z → Finset X, lpValues P ε s) m := by
  classical
  let C : Set (X → Z → ℝ) := {K | Channel K ∧ leakage P K ≤ ε}
  have hc : Continuous (fun K : X → Z → ℝ => leakage P K) := by
    unfold leakage dv pz
    fun_prop
  have hu : Continuous (fun K : X → Z → ℝ => utility P K) := by
    unfold utility dx pz
    fun_prop
  have hclosed : IsClosed C := by
    change IsClosed ({K : X → Z → ℝ | Channel K} ∩ {K | leakage P K ≤ ε})
    apply IsClosed.inter _ (isClosed_le hc continuous_const)
    simp only [Channel, Set.ofPred_and, Set.ofPred_forall]
    apply IsClosed.inter
    · exact isClosed_iInter fun x => isClosed_iInter fun z =>
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun x => isClosed_eq (by fun_prop) continuous_const
  have hbox : C ⊆ Set.Icc (0 : X → Z → ℝ) 1 := by
    rintro K ⟨hK,_⟩
    refine ⟨hK.1, fun x z => ?_⟩
    have hsum : K x z ≤ ∑ j : Z, K x j :=
      single_le_sum (fun j _ => hK.1 x j) (mem_univ z)
    change K x z ≤ (1:ℝ)
    simpa only [hK.2 x] using hsum
  have hcompact : IsCompact C := isCompact_Icc.of_isClosed_subset hclosed hbox
  obtain ⟨z₀⟩ := ‹Nonempty Z›
  let K₀ (x : X) (z : Z) : ℝ := if z = z₀ then 1 else 0
  have hK₀ : Channel K₀ := by
    constructor
    · intro x z
      simp [K₀, apply_ite (fun q : ℝ => 0 ≤ q)]
    · intro x
      simp [K₀]
  have hLeak₀ : leakage P K₀ = 0 := by
    have hz (z : Z) : pz P K₀ z = if z = z₀ then 1 else 0 := by
      by_cases he : z = z₀ <;> simp [pz, px, K₀, he, hP.2]
    have hv (v : V) (z : Z) : dv P K₀ v z = 0 := by
      by_cases he : z = z₀ <;> simp [dv, pv, K₀, he, hz]
    simp [leakage, hv]
  have hnon : C.Nonempty := ⟨K₀,hK₀,hLeak₀ ▸ hε⟩
  obtain ⟨K,hK,hmax⟩ := hcompact.exists_isMaxOn hnon hu.continuousOn
  have hK' : Channel K ∧ leakage P K ≤ ε := hK
  refine ⟨utility P K, ⟨⟨K,hK'.1,hK'.2,rfl⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro t ⟨L,hL,hLeak,ht⟩
    rw [← ht]
    exact hmax (show L ∈ C from ⟨hL,hLeak⟩)
  · apply Set.mem_iUnion.mpr
    obtain ⟨h,hh⟩ := (feasible_iff P ε K).2 hK'
    exact ⟨signs P K,K,h,hh,score_signs P K⟩
  · intro t ht
    obtain ⟨s,L,h,hh,he⟩ := Set.mem_iUnion.mp ht
    have hL : L ∈ C := (feasible_iff P ε L).1 ⟨h,hh⟩
    rw [← he]
    exact (le_utility P L s).trans (hmax hL)

private noncomputable def groupChannel [DecidableEq X]
    (K : X → Z → ℝ) (s : Z → Finset X) (x : X) (u : Finset X) : ℝ :=
  ∑ z ∈ univ.filter (fun z => s z = u), K x z

private theorem group_pz [DecidableEq X] (P : X → V → ℝ) (K : X → Z → ℝ)
    (s : Z → Finset X) (u : Finset X) :
    pz P (groupChannel K s) u = ∑ z ∈ univ.filter (fun z => s z = u), pz P K z := by
  simp only [pz, groupChannel, mul_sum]
  exact sum_comm

private theorem group_dx [DecidableEq X] (P : X → V → ℝ) (K : X → Z → ℝ)
    (s : Z → Finset X) (u : Finset X) (x : X) :
    dx P (groupChannel K s) x u = ∑ z ∈ univ.filter (fun z => s z = u), dx P K x z := by
  simp only [dx, group_pz, groupChannel, ← sum_sub_distrib, mul_sum]

private theorem group_dv [DecidableEq X] (P : X → V → ℝ) (K : X → Z → ℝ)
    (s : Z → Finset X) (u : Finset X) (v : V) :
    dv P (groupChannel K s) v u = ∑ z ∈ univ.filter (fun z => s z = u), dv P K v z := by
  simp only [dv, group_pz, groupChannel, mul_sum, sum_sub_distrib]
  rw [sum_comm (s := (univ : Finset X))]

private theorem compression [DecidableEq X] (P : X → V → ℝ) (K : X → Z → ℝ) (hK : Channel K) :
    ∃ L : X → Finset X → ℝ, Channel L ∧ leakage P L ≤ leakage P K ∧
      score P L (id : Finset X → Finset X) = utility P K := by
  let s := signs P K
  let L := groupChannel K s
  refine ⟨L, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x u
    exact sum_nonneg fun z _ => hK.1 x z
  · intro x
    exact (sum_fiberwise univ s (K x)).trans (hK.2 x)
  · unfold leakage
    apply div_le_div_of_nonneg_right _ (by norm_num)
    calc
      (∑ u : Finset X, ∑ v, |dv P L v u|) ≤
          ∑ u : Finset X, ∑ v, ∑ z ∈ univ.filter (fun z => s z = u), |dv P K v z| := by
        apply sum_le_sum
        intro u _
        apply sum_le_sum
        intro v _
        change |dv P (groupChannel K s) v u| ≤ _
        rw [group_dv]
        exact abs_sum_le_sum_abs _ _
      _ = _ := by
        simp_rw [sum_comm (s := (univ : Finset V))]
        exact sum_fiberwise univ s (fun z => ∑ v, |dv P K v z|)
  · rw [← score_signs P K]
    unfold score
    congr 1
    calc
      (∑ u : Finset X, ∑ x, (if x ∈ id u then 1 else -1) * dx P L x u) =
          ∑ u : Finset X, ∑ z ∈ univ.filter (fun z => s z = u),
            ∑ x, (if x ∈ s z then 1 else -1) * dx P K x z := by
        apply sum_congr rfl
        intro u _
        simp only [id_eq, L, group_dx, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro z hz
        rw [(mem_filter.mp hz).2]
      _ = _ := sum_fiberwise univ s (fun z => ∑ x, (if x ∈ s z then 1 else -1) * dx P K x z)

theorem OMA.solution : type_of% @OMA.S_mo_154572.main := by
  intro X V _ _ _ P hP ε hε
  refine ⟨fun Z _ _ => fixed_maximum P hP ε hε.le, ?_⟩
  obtain ⟨m,hm,_⟩ := fixed_maximum (Z := Finset X) P hP ε hε.le
  have hbound (Z : Type) [Fintype Z] (K : X → Z → ℝ)
      (hK : Channel K) (hLeak : leakage P K ≤ ε) : utility P K ≤ m := by
    obtain ⟨L,hL,hLeak',hscore⟩ := compression P K hK
    have hval_bound : utility P L ≤ m := hm.2 ⟨L,hL,hLeak'.trans hLeak,rfl⟩
    rw [← hscore]
    exact (le_utility P L id).trans hval_bound
  refine ⟨m, ⟨⟨Finset X,inferInstance,hm.1⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro t ⟨Z,inst,K,hK,hLeak,rfl⟩
    exact hbound Z K hK hLeak
  · obtain ⟨K,hK,hLeak,hval⟩ := hm.1
    obtain ⟨L,hL,hLeak',hscore⟩ := compression P K hK
    obtain ⟨h,hh⟩ := (feasible_iff P ε L).2 ⟨hL,hLeak'.trans hLeak⟩
    exact ⟨L,h,hh,hscore.trans hval⟩
  · rintro t ⟨K,h,hh,he⟩
    obtain ⟨hK,hLeak⟩ := (feasible_iff P ε K).1 ⟨h,hh⟩
    rw [← he]
    exact (le_utility P K id).trans (hbound _ K hK hLeak)