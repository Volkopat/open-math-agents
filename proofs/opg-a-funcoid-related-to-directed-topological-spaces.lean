import OMAStatements.S_opg_a_funcoid_related_to_directed_topological_spaces

/-!
Let X consist of the odd positive integers and let Y be the union of the
intervals (2n,2n+1). The meet relates X to Y. A witness below both factors
relates U to V when arbitrarily large odd positive integers belong to U and
to the closure of V. Finite unions distribute over this condition.

For a single point 2n+1, split Y at that point. Its lower part cannot be
related by the order, and its upper part starts beyond the next even integer,
so its closure misses 2n+1. Thus no singleton in X relates to Y in the meet.
-/

namespace DirectedFuncoid

open Set Filter OMA.S_opg_a_funcoid_related_to_directed_topological_spaces

private def coord (n : ℕ) : EReal := ((n : ℝ) : EReal)
private def point (n : ℕ) : EReal := coord (2*n+1)
private def leftEnd (n : ℕ) : EReal := coord (2*n)

private theorem coord_lt {n m : ℕ} : coord n < coord m ↔ n < m := by simp [coord]
private theorem coord_le {n m : ℕ} : coord n ≤ coord m ↔ n ≤ m := by simp [coord]

private def F (U V : Set EReal) : Prop :=
  ∃ᶠ n : ℕ in atTop, point n ∈ U ∧ point n ∈ closure V

private theorem F_funcoid : IsFuncoid F := by
  refine ⟨?_,?_,?_,?_⟩
  · intro V; simp [F]
  · intro U; simp [F]
  · intro U U' V
    simp only [F,mem_union,or_and_right,frequently_or_distrib]
  · intro U V V'
    simp only [F,closure_union,mem_union,and_or_left,frequently_or_distrib]

private theorem F_topology (U V : Set EReal) (h : F U V) : R U V := by
  obtain ⟨n,hn⟩ := h.exists
  exact ⟨point n,hn⟩

private theorem F_order (U V : Set EReal) (h : F U V) :
    OMA.S_opg_a_funcoid_related_to_directed_topological_spaces.ge U V := by
  obtain ⟨n,hn⟩ := h.exists
  obtain ⟨m,hm,_,hc⟩ := frequently_atTop.mp h (n+1)
  have above : point n < point m := coord_lt.mpr (by omega)
  obtain ⟨y,hy,hV⟩ := mem_closure_iff.mp hc (Ioi (point n)) isOpen_Ioi above
  exact ⟨point n,hn.1,y,hV,le_of_lt hy⟩

private def intervals : Set EReal := ⋃ n : ℕ, Ioo (leftEnd n) (point n)
private def singles : Set (Set EReal) := range (fun n : ℕ => {point n})

private theorem limit_point (n : ℕ) : point n ∈ closure intervals := by
  have h : leftEnd n < point n := coord_lt.mpr (by omega)
  apply closure_mono (subset_iUnion (fun k : ℕ => Ioo (leftEnd k) (point k)) n)
  rw [closure_Ioo h.ne]
  exact ⟨h.le,le_rfl⟩

private theorem union_hit : funcoidMeet R OMA.S_opg_a_funcoid_related_to_directed_topological_spaces.ge
    (⋃₀ singles) intervals := by
  refine ⟨F,F_funcoid,F_topology,F_order,?_⟩
  apply Frequently.of_forall
  intro n
  exact ⟨mem_sUnion.mpr ⟨{point n},⟨n,rfl⟩,rfl⟩,limit_point n⟩

private theorem upper_gap (n : ℕ) :
    point n ∉ closure (intervals ∩ Ici (point n)) := by
  intro hc
  have gap : point n < leftEnd (n+1) := coord_lt.mpr (by omega)
  obtain ⟨y,hy,hyint,hyn⟩ := mem_closure_iff.mp hc (Iio (leftEnd (n+1))) isOpen_Iio gap
  obtain ⟨k,hklo,hkhi⟩ := mem_iUnion.mp hyint
  by_cases hk : k ≤ n
  · have h : point k ≤ point n := coord_le.mpr (by omega)
    exact (not_lt_of_ge hyn) (hkhi.trans_le h)
  · have h : leftEnd (n+1) ≤ leftEnd k := coord_le.mpr (by omega)
    exact (not_lt_of_ge (h.trans hklo.le)) hy

private theorem singleton_miss (n : ℕ) :
    ¬ funcoidMeet R OMA.S_opg_a_funcoid_related_to_directed_topological_spaces.ge {point n} intervals := by
  rintro ⟨h,hh,ht,ho,hrel⟩
  have split : intervals = (intervals ∩ Iio (point n)) ∪ (intervals ∩ Ici (point n)) := by
    ext y; simp only [mem_union,mem_inter_iff,mem_Iio,mem_Ici]
    constructor
    · intro hy; rcases lt_or_ge y (point n) with e|e
      · exact Or.inl ⟨hy,e⟩
      · exact Or.inr ⟨hy,e⟩
    · rintro (⟨hy,_⟩|⟨hy,_⟩) <;> exact hy
  rw [split] at hrel
  rcases (hh.2.2.2 _ _ _).mp hrel with below|above
  · obtain ⟨x,hx,y,hy,hxy⟩ := ho _ _ below
    have hx' : x = point n := hx
    subst x
    exact (not_lt_of_ge hxy) hy.2
  · obtain ⟨x,hx,hc⟩ := ht _ _ above
    have hx' : x = point n := hx
    exact upper_gap n (hx' ▸ hc)

end DirectedFuncoid

open DirectedFuncoid OMA.S_opg_a_funcoid_related_to_directed_topological_spaces

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_a_funcoid_related_to_directed_topological_spaces.main) := by
  intro h
  obtain ⟨_,⟨n,rfl⟩,ha⟩ := (h.2 singles intervals).mp union_hit
  exact singleton_miss n ha
