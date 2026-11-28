import FormalConjectures.ErdosProblems.«70»
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Transfer from the first uncountable ordinal to the real line

Jones's 2008 paper, *Partitioning triples and partially ordered sets* (DOI
10.1090/S0002-9939-07-09170-8), proves a stronger version of the real-order target.
This file gives another route, using Jones's 2018 ordinal result (DOI 10.1090/proc/13503).
The finite Ramsey input is proved within the file.
-/

namespace OMA.R_Erdos70_erdos_70_variants_omega_times_two_four_R1

open Cardinal Ordinal Set

/-- A consequence of Jones's ordinal partition theorem (2018, DOI 10.1090/proc/13503). -/
def H1 : Prop :=
  ∀ n : ℕ, Erdos70.OrdinalCardinalRamsey3 (Cardinal.aleph 1).ord (Ordinal.omega0.{0} * 2) n

/-- The finite Ramsey theorem for triples, three colors and homogeneous sets of size five. -/
def H2 : Prop :=
  ∃ N : ℕ, ∀ color : Fin N → Fin N → Fin N → Fin 3,
    ∃ e : Fin 5 ↪o Fin N, ∃ c : Fin 3,
      ∀ i j k : Fin 5, i < j → j < k → color (e i) (e j) (e k) = c

section

-- Sorting argument adapted from @koolkao in open-math-agents PR #4934.
private theorem triplewise_of_sorted {α : Type} [LinearOrder α] (p : α → α → α → Prop)
    (hs : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (p x y z ↔ p y x z) ∧ (p x y z ↔ p x z y))
    (s : Set α) (h : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x < y → y < z → p x y z) :
    s.Triplewise p := by
  intro x hx y hy z hz hxy hyz hxz
  rcases lt_or_gt_of_ne hxy with h₁ | h₁ <;> rcases lt_or_gt_of_ne hyz with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hxz with h₃ | h₃
  · exact h x hx y hy z hz h₁ h₂
  · exact (lt_asymm (h₁.trans h₂) h₃).elim
  · exact (hs x y z hxy hyz hxz).2.mpr (h x hx z hz y hy h₃ h₂)
  · rw [(hs x y z hxy hyz hxz).2, (hs x z y hxz hyz.symm hxy).1]
    exact h z hz x hx y hy h₃ h₁
  · exact (hs x y z hxy hyz hxz).1.mpr (h y hy x hx z hz h₁ h₃)
  · rw [(hs x y z hxy hyz hxz).1, (hs y x z hxy.symm hxz hyz).2]
    exact h y hy z hz x hx h₂ h₃
  · exact (lt_asymm (h₂.trans h₁) h₃).elim
  · rw [(hs x y z hxy hyz hxz).1, (hs y x z hxy.symm hxz hyz).2,
      (hs y z x hyz hxz.symm hxy.symm).1]
    exact h z hz y hy x hx h₂ h₁

private theorem monotone_triple {α : Type} [LinearOrder α] (f : Fin 5 → α)
    (hf : Function.Injective f) :
    ∃ i j k : Fin 5, i < j ∧ j < k ∧
      ((f i < f j ∧ f j < f k) ∨ (f k < f j ∧ f j < f i)) := by
  classical
  by_contra h
  let label (j : Fin 5) : Bool × Bool :=
    (decide (∃ i, i < j ∧ f i < f j), decide (∃ i, i < j ∧ f j < f i))
  have hlabel : ∀ i j, i < j → label i ≠ label j := by
    intro i j hij heq
    rcases lt_or_gt_of_ne (fun e => hij.ne (hf e)) with hinc | hdec
    · have hi : ¬ ∃ k, k < i ∧ f k < f i := by
        rintro ⟨k, hki, hk⟩
        exact h ⟨k, i, j, hki, hij, Or.inl ⟨hk, hinc⟩⟩
      have hj : ∃ k, k < j ∧ f k < f j := ⟨i, hij, hinc⟩
      have := congrArg Prod.fst heq
      simp [label, hi, hj] at this
    · have hi : ¬ ∃ k, k < i ∧ f i < f k := by
        rintro ⟨k, hki, hk⟩
        exact h ⟨k, i, j, hki, hij, Or.inr ⟨hdec, hk⟩⟩
      have hj : ∃ k, k < j ∧ f j < f k := ⟨i, hij, hdec⟩
      have := congrArg Prod.snd heq
      simp [label, hi, hj] at this
  have hlabel' : Function.Injective label := by
    intro i j heq
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (hlabel i j hij heq).elim
    · rfl
    · exact (hlabel j i hji heq.symm).elim
  have impossible := Fintype.card_le_of_injective label hlabel'
  norm_num at impossible

private theorem orientation {α β : Type} [LinearOrder α] [NoMaxOrder α] [Nonempty α]
    [LinearOrder β] (f : α → β)
    (h : ∀ x y z, x < y → y < z →
      (f x < f y ∧ f y < f z) ∨ (f z < f y ∧ f y < f x)) :
    StrictMono f ∨ StrictAnti f := by
  have agree : ∀ x y z, x < y → y < z → (f x < f y ↔ f y < f z) ∧
      (f x < f z ↔ f y < f z) := by
    intro x y z hxy hyz
    rcases h x y z hxy hyz with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simp [h₁, h₂, h₁.trans h₂]
    · simp [not_lt_of_gt h₁, not_lt_of_gt h₂, not_lt_of_gt (h₁.trans h₂)]
  let a : α := Classical.choice inferInstance
  obtain ⟨b, hab⟩ := exists_gt a
  have same : ∀ x y, x < y → (f x < f y ↔ f a < f b) := by
    intro x y hxy
    obtain ⟨z, hz⟩ := exists_gt (max y b)
    have hyz := (le_max_left y b).trans_lt hz
    have hbz := (le_max_right y b).trans_lt hz
    have anchor : f y < f z ↔ f b < f z := by
      rcases lt_trichotomy y b with hyb | rfl | hby
      · exact (agree y b z hyb hbz).2
      · rfl
      · exact (agree b y z hby hyz).2.symm
    exact (agree x y z hxy hyz).1.trans (anchor.trans (agree a b z hab hbz).1.symm)
  by_cases hinc : f a < f b
  · exact Or.inl (fun _ _ hxy => (same _ _ hxy).mpr hinc)
  · right
    intro x y hxy
    obtain ⟨z, hyz⟩ := exists_gt y
    rcases h x y z hxy hyz with ⟨h₁, _⟩ | ⟨_, h₂⟩
    · exact (hinc ((same x y hxy).mp h₁)).elim
    · exact h₂

private theorem range_card (n : ℕ) {α : Type} (f : Fin n → α)
    (hf : Function.Injective f) : #(Set.range f) = n :=
  (Cardinal.mk_congr (Equiv.ofInjective f hf)).symm.trans (Cardinal.mk_fin n)

/-- Test each ordinal triple in the original real coloring and in its reflection. -/
theorem main : H1 → H2 → type_of% @Erdos70.erdos_70.variants.omega_times_two_four := by
  classical
  intro hord ⟨N, hfinite⟩ r hs
  let A := (Cardinal.aleph 1).ord.ToType
  have hcard : #A ≤ #ℝ := by
    change #((Cardinal.aleph 1).ord.ToType) ≤ #ℝ
    simpa [Cardinal.mk_toType, Cardinal.mk_real] using Cardinal.aleph_one_le_continuum
  obtain ⟨f⟩ := (Cardinal.le_def A ℝ).mp hcard
  let monotone (x y z : A) : Prop :=
    ∀ a ∈ ({x, y, z} : Set A), ∀ b ∈ ({x, y, z} : Set A), ∀ c ∈ ({x, y, z} : Set A),
      a < b → b < c → (f a < f b ∧ f b < f c) ∨ (f c < f b ∧ f b < f a)
  let p (x y z : A) : Prop := r (f x) (f y) (f z) ∧ r (-f x) (-f y) (-f z) ∧ monotone x y z
  have hp : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (p x y z ↔ p y x z) ∧ (p x y z ↔ p x z y) := by
    intro x y z hxy hyz hxz
    have h := hs (f x) (f y) (f z) (f.injective.ne hxy) (f.injective.ne hyz) (f.injective.ne hxz)
    have h' := hs (-f x) (-f y) (-f z) (neg_injective.ne (f.injective.ne hxy))
      (neg_injective.ne (f.injective.ne hyz)) (neg_injective.ne (f.injective.ne hxz))
    exact ⟨and_congr h.1 (and_congr h'.1 (by unfold monotone; rw [Set.insert_comm x y])),
      and_congr h.2 (and_congr h'.2 (by unfold monotone; rw [Set.pair_comm y z]))⟩
  rcases hord N p hp with ⟨s, htype, hred⟩ | ⟨s, hsize, hblue⟩
  · left
    let B := (Ordinal.omega0 * 2).ToType
    have htype' : typeLT B = typeLT s := (Ordinal.type_toType _).trans htype.symm
    obtain ⟨e⟩ := Ordinal.type_eq.mp htype'
    have hlimit : Order.IsSuccPrelimit (Ordinal.omega0 * 2) := by
      rw [Ordinal.mul_two]
      exact (Ordinal.isSuccLimit_add_iff.mpr (Or.inl Ordinal.isSuccLimit_omega0)).isSuccPrelimit
    have : NoMaxOrder B := Ordinal.isSuccPrelimit_type_lt_iff.mp
      ((Ordinal.type_toType _).symm ▸ hlimit)
    have : Nonempty B := by
      apply Cardinal.mk_ne_zero_iff.mp
      rw [Cardinal.mk_toType, Ordinal.mul_two, Ordinal.card_add]
      simp [Cardinal.aleph0_ne_zero]
    have strict : ∀ x y : B, x < y → (e x : A) < e y :=
      fun _ _ hxy => e.map_rel_iff.mpr hxy
    have hr : ∀ x y z : B, x ≠ y → y ≠ z → x ≠ z → p (e x) (e y) (e z) := by
      intro x y z hxy hyz hxz
      exact hred (e x).2 (e y).2 (e z).2
        (Subtype.val_injective.ne (e.injective.ne hxy))
        (Subtype.val_injective.ne (e.injective.ne hyz))
        (Subtype.val_injective.ne (e.injective.ne hxz))
    obtain hinc | hdec := orientation (fun x : B => f (e x)) (by
      intro x y z hxy hyz
      exact (hr x y z hxy.ne hyz.ne (hxy.trans hyz).ne).2.2
        _ (by simp) _ (by simp) _ (by simp) (strict x y hxy) (strict y z hyz))
    · refine ⟨OrderEmbedding.ofStrictMono (fun x : B => f (e x)) hinc, ?_⟩
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨z, rfl⟩ hxy hyz hxz
      exact (hr x y z (ne_of_apply_ne _ hxy) (ne_of_apply_ne _ hyz) (ne_of_apply_ne _ hxz)).1
    · have hneg : StrictMono (fun x : B => -f (e x)) :=
        fun _ _ hxy => neg_lt_neg (hdec hxy)
      refine ⟨OrderEmbedding.ofStrictMono (fun x : B => -f (e x)) hneg, ?_⟩
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨z, rfl⟩ hxy hyz hxz
      exact (hr x y z (ne_of_apply_ne _ hxy) (ne_of_apply_ne _ hyz) (ne_of_apply_ne _ hxz)).2.1
  · right
    obtain ⟨t, hts, htc⟩ := Cardinal.mk_set_eq_nat_iff_finset.mp hsize
    let g := t.orderEmbOfFin htc
    have hg (i : Fin N) : g i ∈ s := by
      rw [← hts]
      exact t.orderEmbOfFin_mem htc i
    let color (i j k : Fin N) : Fin 3 :=
      if ¬ r (f (g i)) (f (g j)) (f (g k)) then 0
      else if ¬ r (-f (g i)) (-f (g j)) (-f (g k)) then 1 else 2
    obtain ⟨e, c, he⟩ := hfinite color
    let u (i : Fin 5) : A := g (e i)
    have hu : Function.Injective u := g.injective.comp e.injective
    have blueRange (v : Fin 5 → ℝ) (hv : Function.Injective v)
        (hb : ∀ i j k : Fin 5, i < j → j < k → ¬ r (v i) (v j) (v k)) :
        ∃ t : Set ℝ, #t = 4 ∧ t.Triplewise (fun x y z => ¬ r x y z) := by
      let inc : Fin 4 ↪o Fin 5 := Fin.castLEOrderEmb (by decide)
      let w := v ∘ inc
      refine ⟨Set.range w, range_card _ w (hv.comp inc.injective), ?_⟩
      have hsym : ∀ i j k : Fin 4, i ≠ j → j ≠ k → i ≠ k →
          ((¬ r (w i) (w j) (w k)) ↔ ¬ r (w j) (w i) (w k)) ∧
          ((¬ r (w i) (w j) (w k)) ↔ ¬ r (w i) (w k) (w j)) := by
        intro i j k hij hjk hik
        have inj := hv.comp inc.injective
        have h := hs (w i) (w j) (w k) (inj.ne hij) (inj.ne hjk) (inj.ne hik)
        exact ⟨not_congr h.1, not_congr h.2⟩
      have hall := triplewise_of_sorted _ hsym Set.univ
        (fun i _ j _ k _ hij hjk => hb _ _ _ (inc.strictMono hij) (inc.strictMono hjk))
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hij hjk hik
      exact hall (Set.mem_univ i) (Set.mem_univ j) (Set.mem_univ k)
        (ne_of_apply_ne _ hij) (ne_of_apply_ne _ hjk) (ne_of_apply_ne _ hik)
    fin_cases c
    · apply blueRange (f ∘ u) (f.injective.comp hu)
      intro i j k hij hjk hr
      have h := he i j k hij hjk
      change (if ¬ r (f (u i)) (f (u j)) (f (u k)) then (0 : Fin 3)
        else if ¬ r (-f (u i)) (-f (u j)) (-f (u k)) then 1 else 2) = 0 at h
      change r (f (u i)) (f (u j)) (f (u k)) at hr
      by_cases hr' : r (-f (u i)) (-f (u j)) (-f (u k)) <;> simp [hr, hr'] at h
    · apply blueRange (fun i => -f (u i)) (neg_injective.comp (f.injective.comp hu))
      intro i j k hij hjk hr
      have h := he i j k hij hjk
      change (if ¬ r (f (u i)) (f (u j)) (f (u k)) then (0 : Fin 3)
        else if ¬ r (-f (u i)) (-f (u j)) (-f (u k)) then 1 else 2) = 1 at h
      by_cases hr' : r (f (u i)) (f (u j)) (f (u k)) <;> simp [hr, hr'] at h
    · obtain ⟨i, j, k, hij, hjk, hmono⟩ := monotone_triple (f ∘ u) (f.injective.comp hu)
      have h := he i j k hij hjk
      change (if ¬ r (f (u i)) (f (u j)) (f (u k)) then (0 : Fin 3)
        else if ¬ r (-f (u i)) (-f (u j)) (-f (u k)) then 1 else 2) = 2 at h
      have hr : r (f (u i)) (f (u j)) (f (u k)) := by
        by_contra hn
        simp [hn] at h
      have hr' : r (-f (u i)) (-f (u j)) (-f (u k)) := by
        by_contra hn
        simp [hr, hn] at h
      exfalso
      have hnot := hblue (hg (e i)) (hg (e j)) (hg (e k))
        (hu.ne hij.ne) (hu.ne hjk.ne) (hu.ne (hij.trans hjk).ne)
      apply hnot
      refine ⟨hr, hr', ?_⟩
      intro a ha b hb c hc hab hbc
      -- Every increasing enumeration of these three points has the same middle point.
      have h₁ : u i < u j := g.strictMono (e.strictMono hij)
      have h₂ : u j < u k := g.strictMono (e.strictMono hjk)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        rcases hc with rfl | rfl | rfl <;> first | exact hmono | (exfalso; order)

end

section FiniteRamsey

open Filter

private theorem eventually_color (U : Ultrafilter ℕ) (f : ℕ → Fin 3) :
    ∃ b, ∀ᶠ k in U, f k = b :=
  U.eventually_exists_iff.mp (Eventually.of_forall fun k => ⟨f k, rfl⟩)

private theorem finite_mono_in_nat (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (color : ℕ → ℕ → ℕ → Fin 3) (m : ℕ) :
    ∃ e : Fin m ↪o ℕ, ∃ b : Fin 3,
      ∀ i j k : Fin m, i < j → j < k → color (e i) (e j) (e k) = b := by
  classical
  let d (x y : ℕ) := (eventually_color U (color x y)).choose
  have hd (x y : ℕ) : ∀ᶠ z in U, color x y z = d x y :=
    (eventually_color U (color x y)).choose_spec
  let a (x : ℕ) := (eventually_color U (d x)).choose
  have ha (x : ℕ) : ∀ᶠ y in U, d x y = a x := (eventually_color U (d x)).choose_spec
  obtain ⟨b, hb⟩ := eventually_color U a
  suffices hex : ∃ s : Finset ℕ, s.card = m ∧ (∀ x ∈ s, a x = b) ∧
      (∀ x ∈ s, ∀ y ∈ s, x < y → d x y = b) ∧
      (∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x < y → y < z → color x y z = b) by
    obtain ⟨s, hs, _, _, h⟩ := hex
    let e := s.orderEmbOfFin hs
    exact ⟨e, b, fun i j k hij hjk => h _ (s.orderEmbOfFin_mem hs i) _
      (s.orderEmbOfFin_mem hs j) _ (s.orderEmbOfFin_mem hs k) (e.strictMono hij)
      (e.strictMono hjk)⟩
  induction m with
  | zero => exact ⟨∅, by simp⟩
  | succ m ih =>
    obtain ⟨s, hs, hs₁, hs₂, hs₃⟩ := ih
    have ev₁ : ∀ᶠ k in U, ∀ x ∈ (s : Set ℕ), d x k = a x :=
      (s.finite_toSet.eventually_all).mpr fun x _ => ha x
    have ev₂ : ∀ᶠ k in U, ∀ x ∈ (s : Set ℕ), ∀ y ∈ (s : Set ℕ), color x y k = d x y :=
      (s.finite_toSet.eventually_all).mpr fun x _ =>
        (s.finite_toSet.eventually_all).mpr fun y _ => hd x y
    have ev₀ : ∀ᶠ k in U, s.sup id < k := hU (eventually_gt_atTop (s.sup id))
    obtain ⟨k, hk, hk₁, hk₂, hk₃⟩ := (ev₀.and (hb.and (ev₁.and ev₂))).exists
    have below (x : ℕ) (hx : x ∈ s) : x < k := (Finset.le_sup (f := id) hx).trans_lt hk
    have hkn : k ∉ s := fun h => (below k h).false
    refine ⟨insert k s, by simp [Finset.card_insert_of_notMem hkn, hs], ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hk₁
      · exact hs₁ x hx
    · intro x hx y hy hxy
      have hys : y ≤ k := (Finset.mem_insert.mp hy).elim
        (fun h => h.le) (fun h => (below y h).le)
      have hxs : x ∈ s := (Finset.mem_insert.mp hx).resolve_left (hxy.trans_le hys).ne
      rcases Finset.mem_insert.mp hy with rfl | hys'
      · exact (hk₂ x hxs).trans (hs₁ x hxs)
      · exact hs₂ x hxs y hys' hxy
    · intro x hx y hy z hz hxy hyz
      have hzs : z ≤ k := (Finset.mem_insert.mp hz).elim
        (fun h => h.le) (fun h => (below z h).le)
      have hys : y ∈ s := (Finset.mem_insert.mp hy).resolve_left (hyz.trans_le hzs).ne
      have hxs : x ∈ s :=
        (Finset.mem_insert.mp hx).resolve_left ((hxy.trans hyz).trans_le hzs).ne
      rcases Finset.mem_insert.mp hz with rfl | hzs'
      · exact (hk₃ x hxs y hys).trans (hs₂ x hxs y hys hxy)
      · exact hs₃ x hxs y hys z hzs' hxy hyz

/-- A finite form of Ramsey's theorem, obtained by compactness via an ultrafilter. -/
theorem finite_ramsey : H2 := by
  classical
  unfold H2
  by_contra h
  push Not at h
  choose bad hbad using h
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  let ext (N i j k : ℕ) : Fin 3 :=
    if hi : i < N then if hj : j < N then if hk : k < N then
      bad N ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ else 0 else 0 else 0
  let color (i j k : ℕ) : Fin 3 := (eventually_color U (fun N => ext N i j k)).choose
  have hcolor (i j k : ℕ) : ∀ᶠ N in U, ext N i j k = color i j k :=
    (eventually_color U (fun N => ext N i j k)).choose_spec
  obtain ⟨e, b, he⟩ := finite_mono_in_nat U hU color 5
  have hBound : ∀ᶠ N in U, ∀ i : Fin 5, e i < N := by
    exact eventually_all.mpr fun i => hU (eventually_gt_atTop (e i))
  have hAgree : ∀ᶠ N in U, ∀ i j k : Fin 5, ext N (e i) (e j) (e k) = color (e i) (e j) (e k) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k =>
      hcolor (e i) (e j) (e k)
  obtain ⟨N, hN, hAgreeN⟩ := (hBound.and hAgree).exists
  let eN : Fin 5 ↪o Fin N := OrderEmbedding.ofStrictMono (fun i => ⟨e i, hN i⟩)
    (fun _ _ hij => e.strictMono hij)
  obtain ⟨i, j, k, hij, hjk, hn⟩ := hbad N eN b
  apply hn
  change bad N ⟨e i, hN i⟩ ⟨e j, hN j⟩ ⟨e k, hN k⟩ = b
  have hEq := (hAgreeN i j k).trans (he i j k hij hjk)
  simpa [ext, hN i, hN j, hN k] using hEq

end FiniteRamsey

/-- The only remaining input is the ordinal partition theorem. -/
theorem from_ordinal (h : H1) :
    type_of% @Erdos70.erdos_70.variants.omega_times_two_four :=
  main h finite_ramsey

end OMA.R_Erdos70_erdos_70_variants_omega_times_two_four_R1
