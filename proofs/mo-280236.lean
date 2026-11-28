import OMAStatements.S_mo_280236

/-!
Retains @marcusbuffett’s complete proof #30854, head
 a895e4683056e68ec824f4c1e4534860639a9289, and @AkiRA-COM-FP’s statement #26033.
The density of rationals after removing a finite set replaces the local induction;
the standard geometric-series summability supplies the same convergence bound.
An order-based injectivity criterion replaces the final trichotomy helper.
Source: Taras Banakh, https://mathoverflow.net/questions/280236 (CC BY-SA 3.0).

Enumerate the target and construct a continuous scalar function taking distinct
rational values on its points. In each rational level set, removing its unique
enumerated point (if present) leaves a countable union of closed sets. For each
such closed set use a continuous function equal to √2 there and rational on
the enumeration. These functions, together with the first scalar function,
are the coordinates of the required map.

The interpolation uses successively smaller continuous bumps, each of which
vanishes on the closed set and on all previously assigned points.
-/

open OMA.S_mo_280236

open Set

namespace RationalPreimage

private lemma fresh_rat (s : Finset ℝ) {a b : ℝ} (h : a<b) :
    ∃ q : ℚ, a < q ∧ (q:ℝ)<b ∧ (q:ℝ) ∉ s := by
  obtain ⟨x,⟨⟨q,rfl⟩,hq⟩,hl,hu⟩ :=
    (Rat.denseRange_cast.sdiff_finset s).exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr h)
  exact ⟨q,hl,hu,hq⟩

variable {X : Type} [TopologicalSpace X] [T1Space X] [NormalSpace X]
variable (e : ℕ → X) (einj : Function.Injective e) (F : Set X) (closedF : IsClosed F)
    (away : ∀ n, e n ∉ F)

private def Step (n : ℕ) (f g : C(X,ℝ)) : Prop :=
  (∀ x, |g x-f x| ≤ (1/2:ℝ)^n) ∧
  (∀ x ∈ F, g x=f x) ∧
  (∀ i<n, g (e i)=f (e i)) ∧
  (∃ q : ℚ, (q:ℝ)=g (e n)) ∧
  ∀ i<n, g (e i)≠g (e n)

include einj closedF away
private lemma make_step (n : ℕ) (f : C(X,ℝ)) : ∃ g, Step e F n f g := by
  classical
  let s := (Finset.range n).image e
  have hs : IsClosed ((s : Set X) ∪ F) := s.finite_toSet.isClosed.union closedF
  have hne : e n ∉ (s : Set X) ∪ F := by
    rintro (h | h)
    · obtain ⟨i,hi,h⟩ := Finset.mem_image.1 h
      have := Finset.mem_range.1 hi
      have := einj h
      omega
    · exact away n h
  obtain ⟨u,hu,hu₁,huI⟩ := exists_continuous_zero_one_of_isClosed hs
    (isClosed_singleton (X := X) (x := e n)) (Set.disjoint_singleton_right.2 hne)
  have eps : 0<(1/2:ℝ)^n := by positivity
  obtain ⟨q,hq,hq',hqf⟩ := fresh_rat (s.image f) (a := f (e n)) (b := f (e n)+(1/2:ℝ)^n) (by linarith)
  let g : C(X,ℝ) := ⟨fun x => f x + ((q:ℝ)-f (e n))*u x, by fun_prop⟩
  have He : g (e n)=q := by
    have h : u (e n)=1 := hu₁ (by simp)
    simp [g,h]
  have H (x : X) (hx : x ∈ (s:Set X) ∪ F) : g x=f x := by
    have h : u x=0 := hu hx
    simp [g,h]
  have earlier (i : ℕ) (hi : i<n) : e i ∈ s := Finset.mem_image.2 ⟨i,Finset.mem_range.2 hi,rfl⟩
  refine ⟨g,?_,fun x hx => H x (Or.inr hx),fun i hi => H _ (Or.inl (earlier i hi)),
    ⟨q,He.symm⟩,?_⟩
  · intro x
    obtain ⟨h₀,h₁⟩ := huI x
    change |f x + ((q:ℝ)-f (e n))*u x-f x| ≤ _
    rw [add_sub_cancel_left,abs_of_nonneg (mul_nonneg (by linarith) h₀)]
    nlinarith
  · intro i hi
    rw [H _ (Or.inl (earlier i hi)),He]
    intro h
    exact hqf (Finset.mem_image.2 ⟨_,earlier i hi,h⟩)

/-- The scalar interpolation fixes the prescribed value on the closed set and
assigns distinct rationals to the enumerated points outside it. -/
private lemma interpolate (base : ℝ) : ∃ f : C(X,ℝ),
    (∀ x ∈ F, f x=base) ∧ (∀ n, ∃ q : ℚ, (q:ℝ)=f (e n)) ∧ Function.Injective (f ∘ e) := by
  classical
  choose next hnext using make_step e einj F closedF away
  let f : ℕ → C(X,ℝ) := Nat.rec (ContinuousMap.const X base) (fun n v => next n v)
  have S (n : ℕ) : Step e F n (f n) (f (n+1)) := hnext n (f n)
  let delta (n : ℕ) (x : X) := f (n+1) x - f n x
  let g : C(X,ℝ) := ⟨fun x => base + ∑' n, delta n x, continuous_const.add
    (continuous_tsum (fun n => (f (n+1)).continuous.sub (f n).continuous)
      hasSum_geometric_two.summable
      (fun n x => (S n).1 x))⟩
  have fixed (i : ℕ) : g (e i)=f (i+1) (e i) := by
    change base + ∑' n, delta n (e i) = _
    rw [tsum_eq_sum (s := Finset.range (i+1)) (by
      intro n hn
      have := (S n).2.2.1 i (by simpa using hn : i < n)
      simp [delta,this])]
    simp only [delta]
    rw [Finset.sum_range_sub (fun j => f j (e i))]
    change base+(f (i+1) (e i)-base)=_
    ring
  have stable (i n : ℕ) (hi : i<n) : f n (e i) = f (i+1) (e i) := by
    induction n with
    | zero => omega
    | succ n ih =>
      rcases eq_or_lt_of_le (by omega : i≤n) with rfl | h
      · rfl
      · exact ((S n).2.2.1 i h).trans (ih h)
  refine ⟨g,?_,fun i => by rw [fixed]; exact (S i).2.2.2.1,?_⟩
  · intro x hx
    have H : ∀ n, delta n x=0 := fun n => sub_eq_zero.2 ((S n).2.1 x hx)
    simp [g,H]
  · apply Function.Injective.of_lt_imp_ne
    intro i j hij
    change g (e i) ≠ g (e j)
    rw [fixed,fixed,← stable i (j+1) (by omega)]
    exact (S j).2.2.2.2 i hij

omit einj closedF away

private lemma cover_fiber {Y : Type} [MetricSpace Y]
    (u : ℕ → Y) (g : C(Y,ℝ)) (hg : Function.Injective (g ∘ u)) (q : ℚ) :
    ∃ K : ℕ → Set Y, (∀ j, IsClosed (K j) ∧ ∀ i, u i ∉ K j) ∧
    ∀ y, g y=(q:ℝ) → y ∈ range u ∨ ∃ j, y ∈ K j := by
  classical
  let S := {y | g y=(q:ℝ)}
  have hc : IsClosed S := isClosed_eq g.continuous continuous_const
  by_cases he : ∃ i, g (u i)=(q:ℝ)
  · obtain ⟨i,hi⟩ := he
    let K (j : ℕ) := S ∩ {y | 1/((j:ℝ)+1) ≤ dist y (u i)}
    refine ⟨K,fun j => ⟨hc.inter (isClosed_le continuous_const (continuous_id.dist continuous_const)),?_⟩,?_⟩
    · intro k hk
      have heq : g (u k)=(q:ℝ) := hk.1
      have eq : k=i := hg (heq.trans hi.symm)
      have H := hk.2
      change 1/((j:ℝ)+1) ≤ dist (u k) (u i) at H
      rw [eq,dist_self] at H
      exact (not_lt_of_ge H) (by positivity)
    · intro y hy
      by_cases h : y=u i
      · exact Or.inl ⟨i,h.symm⟩
      · obtain ⟨j,hj⟩ := exists_nat_one_div_lt (dist_pos.2 h)
        exact Or.inr ⟨j,hy,hj.le⟩
  · exact ⟨fun _ => S,fun _ => ⟨hc,fun i h => he ⟨i,h⟩⟩,fun y h => Or.inr ⟨0,h⟩⟩

private lemma represent_range {Y : Type} [MetricSpace Y] (u : ℕ → Y)
    (hu : Function.Injective u) :
    ∃ Φ : Y → ℕ → ℝ, Continuous Φ ∧ ∀ x, (∀ n, ∃ q : ℚ, (q:ℝ)=Φ x n) ↔ x ∈ range u := by
  classical
  obtain ⟨g,_,hgr,hgi⟩ := interpolate u hu ∅ isClosed_empty (by simp) 0
  choose K hK hcover using cover_fiber u g hgi
  have mk (q : ℚ) (j : ℕ) := interpolate u hu (K q j) (hK q j).1 (hK q j).2 (Real.sqrt 2)
  choose test hconst hrat hinj using mk
  let κ := Unit ⊕ (ℚ × ℕ)
  let idx : ℕ ≃ κ := Classical.choice nonempty_equiv_of_countable
  let coord : κ → C(Y,ℝ) := Sum.elim (fun _ => g) (fun qj => test qj.1 qj.2)
  refine ⟨fun x n => coord (idx n) x,continuous_pi (fun i => (coord _).continuous),?_⟩
  intro x
  constructor
  · intro hx
    have rat (a : κ) : ∃ q : ℚ, (q:ℝ)=coord a x := by simpa using hx (idx.symm a)
    obtain ⟨q,hq⟩ := rat (.inl ())
    rcases hcover q x hq.symm with h | ⟨j,hj⟩
    · exact h
    · obtain ⟨r,hr⟩ := rat (.inr (q,j))
      exact False.elim (irrational_sqrt_two ⟨r,hr.trans (hconst q j x hj)⟩)
  · rintro ⟨i,rfl⟩ n
    change ∃ r : ℚ, (r:ℝ)=coord (idx n) (u i)
    cases idx n with
    | inl => exact hgr i
    | inr qj => exact hrat _ _ i

private lemma countable_target : eventuallyZeroRationalSequences.Countable := by
  classical
  let pad (p : Σ n : ℕ, Fin n → ℚ) (i : ℕ) : ℝ :=
    if h : i<p.1 then (p.2 ⟨i,h⟩ : ℚ) else 0
  apply (Set.countable_range pad).mono
  rintro x ⟨hq,N,hN⟩
  choose a ha using hq
  refine ⟨⟨N,fun i => a i.val⟩,?_⟩
  funext i
  by_cases h : i<N
  · simpa [pad,h] using ha i
  · simp [pad,h,hN i (by omega)]

private lemma infinite_target : eventuallyZeroRationalSequences.Infinite := by
  let single (k i : ℕ) : ℝ := if i=0 then k else 0
  have hinj : Function.Injective single := by
    intro i j h
    simpa [single] using congrFun h 0
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨k,rfl⟩
  refine ⟨fun i => ?_,1,fun i hi => by simp [single,show i≠0 by omega]⟩
  by_cases h : i=0
  · exact ⟨k,by simp [single,h]⟩
  · exact ⟨0,by simp [single,h]⟩

end RationalPreimage

open RationalPreimage

theorem OMA.solution : type_of% @OMA.S_mo_280236.main := by
  classical
  let : MetricSpace (ℕ → ℝ) := TopologicalSpace.metrizableSpaceMetric _
  have : Countable eventuallyZeroRationalSequences := countable_target.to_subtype
  have : Infinite eventuallyZeroRationalSequences := infinite_target.to_subtype
  obtain ⟨enumeration⟩ : Nonempty (ℕ ≃ eventuallyZeroRationalSequences) := nonempty_equiv_of_countable
  let u (n : ℕ) : ℕ → ℝ := enumeration n
  obtain ⟨f,hf,h⟩ := represent_range u (Subtype.val_injective.comp enumeration.injective)
  refine ⟨f,hf,Set.ext (fun x => (h x).trans ?_)⟩
  exact ⟨fun ⟨i,hi⟩ => hi ▸ (enumeration i).property,
    fun hx => ⟨enumeration.symm ⟨x,hx⟩,by simp [u]⟩⟩
