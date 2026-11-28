import OMAStatements.S_mo_104812

noncomputable section

namespace Wave10I

open Filter Set Topology

abbrev Rate := ℕ → ℕ
def Dom (a b : Rate) : Prop := ∀ᶠ n in atTop, a n ≤ b n

theorem dom_refl (b : Rate) : Dom b b := Eventually.of_forall (fun _ => le_rfl)
theorem dom_trans {a b c : Rate} (h : Dom a b) (j : Dom b c) : Dom a c := by
  filter_upwards [h,j] with n hn jn using le_trans hn jn

theorem dom_countable {ι : Type} [Encodable ι] (a : ι → Rate) :
    ∃ b : Rate, ∀ i, Dom (a i) b := by
  let b : Rate := fun n => (Finset.range (n+1)).sup fun j =>
    ((Encodable.decode (α := ι) j).map (fun i => a i n)).getD 0
  refine ⟨b, fun i => ?_⟩
  filter_upwards [eventually_ge_atTop (Encodable.encode i)] with n hn
  have hm : Encodable.encode i ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
  simpa [b] using Finset.le_sup (f := fun j =>
    ((Encodable.decode (α := ι) j).map (fun i => a i n)).getD 0) hm

inductive Side where
  | apex
  | branch (h : Rate)

instance : TopologicalSpace Side where
  IsOpen U := Side.apex ∈ U → ∃ b, ∀ h, Dom b h → Side.branch h ∈ U
  isOpen_univ := fun _ => ⟨fun _ => 0, fun _ _ => trivial⟩
  isOpen_inter := by
    intro U V hU hV ha
    obtain ⟨b,hb⟩ := hU ha.1
    obtain ⟨c,hc⟩ := hV ha.2
    refine ⟨fun n => max (b n) (c n), fun h hh => ⟨hb h ?_, hc h ?_⟩⟩
    · exact dom_trans (Eventually.of_forall fun n => le_max_left (b n) (c n)) hh
    · exact dom_trans (Eventually.of_forall fun n => le_max_right (b n) (c n)) hh
  isOpen_sUnion := by
    rintro F hF ⟨U, hUF, ha⟩
    obtain ⟨b,hb⟩ := hF U hUF ha
    exact ⟨b, fun h hh => ⟨U,hUF,hb h hh⟩⟩

def tail (b : Rate) : Set Side
  | .apex => True
  | .branch h => Dom b h

theorem tail_clopen (b : Rate) : IsClopen (tail b) := by
  constructor
  · apply isOpen_compl_iff.mp
    exact fun h => (h trivial).elim
  · exact fun _ => ⟨b, fun _ hh => hh⟩

theorem stabilize {ι : Type} [Encodable ι] (c : ι → C(Side, ℝ)) :
    ∃ b : Rate, ∀ h, Dom b h → ∀ i, c i (.branch h) = c i .apex := by
  have ex (p : ι × ℕ) : ∃ b : Rate, ∀ h, Dom b h →
      dist (c p.1 (.branch h)) (c p.1 .apex) < 1 / ((p.2 : ℝ) + 1) := by
    have op : IsOpen ((c p.1) ⁻¹' Metric.ball (c p.1 .apex) (1 / ((p.2 : ℝ) + 1))) :=
      Metric.isOpen_ball.preimage (c p.1).continuous
    exact op (Metric.mem_ball_self (by positivity))
  choose a ha using ex
  obtain ⟨b,hb⟩ := dom_countable a
  refine ⟨b, fun h hh i => ?_⟩
  by_contra ne
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (dist_pos.mpr ne)
  exact (not_lt_of_ge hm.le) (ha (i,m) h (dom_trans (hb (i,m)) hh))

abbrev X := ℕ × Side × ℝ
abbrev R := C(X, ℝ)

def epsilon (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

def witness : R := ⟨fun x => x.2.2, continuous_snd.comp continuous_snd⟩

def sample (s : Side) (n k : ℕ) : X := (n,s,epsilon k)

theorem sample_stabilize (a : R) :
    ∃ b : Rate, ∀ h, Dom b h → ∀ n k,
      a (sample (.branch h) n k) = a (sample .apex n k) := by
  let c (p : ℕ × ℕ) : C(Side,ℝ) :=
    ⟨fun s => a (sample s p.1 p.2), a.continuous.comp (by unfold sample; fun_prop)⟩
  obtain ⟨b,hb⟩ := stabilize c
  exact ⟨b,fun h hh n k => hb h hh (n,k)⟩

theorem small_on_tail (a : R) :
    ∃ b : Rate, ∀ h, Dom b h → ∀ᶠ n in atTop,
      a (sample (.branch h) n (h n)) * epsilon (h n) < 1/2 := by
  have he : Tendsto epsilon atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ex (n : ℕ) : ∃ N : ℕ, ∀ k ≥ N, a (sample .apex n k) * epsilon k < 1/2 := by
    have hc : Continuous (fun t : ℝ => a (n, Side.apex, t)) := by fun_prop
    have ht := (hc.continuousAt (x := 0)).tendsto.comp he
    have hlim : Tendsto (fun k => a (sample .apex n k) * epsilon k) atTop (𝓝 0) := by
      simpa [sample] using ht.mul he
    exact eventually_atTop.1 (hlim.eventually_lt_const (by norm_num : (0:ℝ) < 1/2))
  choose N hN using ex
  obtain ⟨b,hb⟩ := sample_stabilize a
  refine ⟨fun n => max (b n) (N n), fun h hh => ?_⟩
  have hd : Dom b h := dom_trans (Eventually.of_forall fun n => le_max_left (b n) (N n)) hh
  filter_upwards [hh] with n hn
  rw [hb h hd n (h n)]
  exact hN n _ (le_trans (le_max_right _ _) hn)

abbrev SeqR := ℕ → ℝ

def eventuallyZero : Ideal SeqR where
  carrier := {v | ∀ᶠ n in atTop, v n = 0}
  zero_mem' := Eventually.of_forall (fun _ => rfl)
  add_mem' {x y} hx hy := by
    filter_upwards [hx,hy] with n h j
    change x n + y n = 0
    simp [h,j]
  smul_mem' c x hx := by
    filter_upwards [hx] with n hn
    change c n * x n = 0
    simp [hn]

theorem exists_seq_max : ∃ K : Ideal SeqR, K.IsMaximal ∧ eventuallyZero ≤ K := by
  apply Ideal.exists_le_maximal
  apply eventuallyZero.ne_top_iff_one.mpr
  intro h
  change ∀ᶠ n : ℕ in atTop, (1:ℝ) = 0 at h
  exact one_ne_zero h.exists.choose_spec

def diagonal (s : Side) (h : Rate) : R →+* SeqR where
  toFun a n := a (sample s n (h n))
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem diagonal_surj (s : Side) (h : Rate) : Function.Surjective (diagonal s h) := by
  intro v
  exact ⟨⟨fun x => v x.1, (continuous_of_discreteTopology (f := v)).comp continuous_fst⟩,rfl⟩

def intersectionIdeal (K : Ideal SeqR) (pos : Rate → Side) : Ideal R :=
  ⨅ h : Rate, K.comap (diagonal (pos h) h)

theorem maximal_intersection (K : Ideal SeqR) [K.IsMaximal] (pos : Rate → Side) :
    ∃ S : Set (Ideal R), (∀ M ∈ S, M.IsMaximal) ∧ intersectionIdeal K pos = sInf S := by
  refine ⟨Set.range (fun h => K.comap (diagonal (pos h) h)), ?_,rfl⟩
  rintro _ ⟨h,rfl⟩
  exact Ideal.comap_isMaximal_of_surjective _ (diagonal_surj _ _)

abbrev I (K : Ideal SeqR) := intersectionIdeal K (fun _ => .apex)
abbrev J (K : Ideal SeqR) := intersectionIdeal K Side.branch

theorem mem_inter {K : Ideal SeqR} {pos : Rate → Side} {a : R} :
    a ∈ intersectionIdeal K pos ↔ ∀ h, diagonal (pos h) h a ∈ K := by
  simp [intersectionIdeal, Ideal.mem_comap]

theorem outside (K : Ideal SeqR) (hK : K.IsMaximal) : witness ∉ I K ⊔ J K := by
  intro hm
  obtain ⟨g,hg,j,hj,heq⟩ := Submodule.mem_sup.mp hm
  obtain ⟨b,hb⟩ := sample_stabilize g
  have eq : diagonal (.branch b) b g = diagonal .apex b g := by
    funext n
    exact hb b (dom_refl _) n (b n)
  have m1 : diagonal (.branch b) b g ∈ K := eq ▸ (mem_inter.mp hg b)
  have m2 := mem_inter.mp hj b
  have m3 : diagonal (.branch b) b witness ∈ K := by
    rw [←heq,map_add]
    exact K.add_mem m1 m2
  have hu : IsUnit (diagonal (.branch b) b witness) := by
    apply Pi.isUnit_iff.mpr
    intro n
    apply isUnit_iff_ne_zero.mpr
    change 1 / ((b n : ℝ) + 1) ≠ 0
    positivity
  exact hK.ne_top (K.eq_top_of_isUnit_mem m3 hu)

def correction (a : R) : R :=
  ⟨fun x => 2 * max (a x * witness x - 1/2) 0, by fun_prop⟩

def restricted (b : Rate) (v : R) : R :=
  let S := (fun x : X => x.2.1) ⁻¹' tail b
  ⟨S.indicator v, ((tail_clopen b).preimage (continuous_fst.comp continuous_snd)).continuous_indicator v.continuous⟩

theorem restricted_of_mem (b : Rate) (v : R) (x : X) (hx : x.2.1 ∈ tail b) :
    restricted b v x = v x := Set.indicator_of_mem (s := (fun x : X => x.2.1) ⁻¹' tail b) hx _

theorem restricted_of_notMem (b : Rate) (v : R) (x : X) (hx : x.2.1 ∉ tail b) :
    restricted b v x = 0 := Set.indicator_of_notMem (s := (fun x : X => x.2.1) ⁻¹' tail b) hx _

theorem correction_mem (K : Ideal SeqR) (hK : eventuallyZero ≤ K) (a : R) :
    correction a ∈ I K ⊔ J K := by
  classical
  obtain ⟨b,hb⟩ := small_on_tail a
  let v := correction a
  let w := restricted b v
  apply Submodule.mem_sup.mpr
  refine ⟨v-w,mem_inter.mpr ?_,w,mem_inter.mpr ?_, sub_add_cancel _ _⟩
  · intro h
    have he : diagonal .apex h (v-w) = 0 := by
      funext n
      change v _ - w _ = 0
      exact sub_eq_zero.mpr (restricted_of_mem b v (sample .apex n (h n)) trivial).symm
    rw [he]
    exact K.zero_mem
  · intro h
    apply hK
    change ∀ᶠ n in atTop, w (sample (.branch h) n (h n)) = 0
    by_cases hd : Dom b h
    · filter_upwards [hb h hd] with n hn
      have hneg : a (sample (.branch h) n (h n)) * witness (sample (.branch h) n (h n)) - 1/2 ≤ 0 :=
        sub_nonpos.mpr hn.le
      rw [show w (sample (.branch h) n (h n)) = v _ from restricted_of_mem _ _ _ hd]
      change 2 * max (a (sample (.branch h) n (h n)) * witness (sample (.branch h) n (h n)) - 1/2) 0 = 0
      rw [max_eq_right hneg, mul_zero]
    · exact Eventually.of_forall (fun n => restricted_of_notMem b v _ hd)

theorem inside_max {K : Ideal SeqR} (hK : eventuallyZero ≤ K)
    (M : Ideal R) (hm : M.IsMaximal) (hs : I K ⊔ J K ≤ M) : witness ∈ M := by
  by_contra h
  obtain ⟨a,i,hi,he⟩ := hm.exists_inv h
  have hu : IsUnit (i + correction a) := by
    apply ((i + correction a).isUnit_iff_forall_ne_zero).mpr
    intro x
    have e := congrArg (fun f : R => f x) he
    change a x * witness x + i x = 1 at e
    change i x + 2 * max (a x * witness x - 1/2) 0 ≠ 0
    have h₁ := le_max_left (a x * witness x - 1/2) 0
    have h₂ := le_max_right (a x * witness x - 1/2) 0
    linarith
  exact hm.ne_top (M.eq_top_of_isUnit_mem (M.add_mem hi (hs (correction_mem K hK a))) hu)

end Wave10I

open Wave10I in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_104812.main) := by
  intro all
  obtain ⟨K, hm, hzero⟩ := exists_seq_max
  let _ : K.IsMaximal := hm
  obtain ⟨S, hS, heq⟩ := all X (I K) (J K)
    (maximal_intersection K (fun _ => .apex)) (maximal_intersection K Side.branch)
  apply outside K hm
  rw [heq, Ideal.mem_sInf]
  intro M hM
  apply inside_max hzero M (hS M hM)
  rw [heq]
  exact sInf_le hM
