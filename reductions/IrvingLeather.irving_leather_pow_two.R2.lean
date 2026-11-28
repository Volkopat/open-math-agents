import FormalConjectures.Paper.IrvingLeatherStableMatchings
import Mathlib.Tactic

/-!
# Triangular support and weighted bounds for stable families

Credit: @MrSeizy. The comparison of stable partners and the rank-sorting lemma
are adapted from the merged interval-schedule reduction R1.H3.R1.
The recurrence growth estimate is adapted from @tatashbar's R1.H1.
-/

open StableMarriage IrvingLeather
namespace OMA.R_IrvingLeather_irving_leather_pow_two_R2
variable {n : ℕ}

-- Conflict-of-interest comparison from the merged interval-schedule reduction R1.H3.R1.
private theorem opposite (p : Profile n) {a b : Matching n}
    (ha : IsStable p a) (hb : IsStable p b) (m : Fin n) :
    p.manRank m (a m) < p.manRank m (b m) ↔
      p.womanRank (b m) m < p.womanRank (b m) (a.symm (b m)) := by
  classical
  let S := Finset.univ.filter (fun i => p.manRank i (a i) < p.manRank i (b i))
  let T := Finset.univ.filter (fun w => p.womanRank w (b.symm w) < p.womanRank w (a.symm w))
  have hST : S.image a ⊆ T := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have h : p.manRank i (a i) < p.manRank i (b i) := (Finset.mem_filter.mp hi).2
    have hn : b i ≠ a i := fun e => (ne_of_lt h) (congrArg (p.manRank i) e.symm)
    have hne : i ≠ b.symm (a i) := by
      intro e
      exact hn (by simpa using congrArg b e)
    have hle := not_lt.mp (fun hl => hb i (a i) ⟨hn, h, hl⟩)
    have hlt := lt_of_le_of_ne hle (fun e => hne ((p.womanRank (a i)).injective e.symm))
    simpa [T] using hlt
  have hTS : T.image b.symm ⊆ S := by
    intro i hi
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
    have h : p.womanRank w (b.symm w) < p.womanRank w (a.symm w) := (Finset.mem_filter.mp hw).2
    have hn : a (b.symm w) ≠ w := by
      intro e
      have he : b.symm w = a.symm w := by simpa using congrArg a.symm e
      exact (ne_of_lt h) (congrArg (p.womanRank w) he)
    have hle := not_lt.mp (fun hl => ha (b.symm w) w ⟨hn, hl, h⟩)
    have hlt := lt_of_le_of_ne hle (fun e => hn ((p.manRank (b.symm w)).injective e))
    simpa [S] using hlt
  have hc := Finset.card_le_card hST
  rw [Finset.card_image_of_injective _ a.injective] at hc
  have he : T.image b.symm = S := Finset.eq_of_subset_of_card_le hTS
    ((Finset.card_image_of_injective _ b.symm.injective).symm ▸ hc)
  have hm : m ∈ S ↔ b m ∈ T := by
    rw [← he]
    constructor
    · intro h
      obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp h
      have hw' : w = b m := by simpa using congrArg b hew
      simpa only [hw'] using hw
    · intro h
      exact Finset.mem_image.mpr ⟨b m, h, b.symm_apply_apply _⟩
  simpa [S, T] using hm

private theorem exists_sorted_rank {α : Type*} [LinearOrder α] (f : Fin n → α)
    (hf : Function.Injective f) :
    ∃ r : Equiv.Perm (Fin n), ∀ i j, r i < r j ↔ f i < f j := by
  classical
  let s := Finset.univ.image f
  have hs : s.card = n := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  let g : Fin n ≃ s := Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_image_of_mem f (Finset.mem_univ i)⟩)
    ⟨fun _ _ h => hf (congrArg Subtype.val h), by
      intro y
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp y.property
      exact ⟨i, Subtype.ext hi⟩⟩
  let order := (s.orderIsoOfFin hs).symm
  exact ⟨g.trans order.toEquiv, fun _ _ => order.lt_iff_lt⟩


/-- Worst stable partners for men form a matching giving each woman her best stable partner. -/
private theorem optimal {p : Profile n} {s : Finset (Matching n)} (hne : s.Nonempty)
    (hs : ∀ a ∈ s, IsStable p a) :
    ∃ b : Matching n, IsStable p b ∧
      (∀ w, ∃ a ∈ s, a.symm w = b.symm w) ∧
      ∀ w a, a ∈ s → p.womanRank w (b.symm w) ≤ p.womanRank w (a.symm w) := by
  classical
  choose t ht hmax using fun m => s.exists_max_image (fun a => p.manRank m (a m)) hne
  let f (m : Fin n) := t m m
  have best (m) (a) (ha : a ∈ s) :
      p.womanRank (f m) m ≤ p.womanRank (f m) (a.symm (f m)) := by
    by_cases e : a m = f m
    · have eq := a.eq_symm_apply.mpr e
      rw [← eq]
    · have lt' := lt_of_le_of_ne (hmax m a ha) (fun he => e ((p.manRank m).injective he))
      exact ((opposite p (hs a ha) (hs _ (ht m)) m).mp lt').le
  have inj : Function.Injective f := by
    intro i j e
    have hi := best i (t j) (ht j)
    have hj := best j (t i) (ht i)
    rw [e] at hi
    rw [← e] at hj
    change p.womanRank (f j) i ≤ p.womanRank (f j) ((t j).symm (t j j)) at hi
    change p.womanRank (f i) j ≤ p.womanRank (f i) ((t i).symm (t i i)) at hj
    simp only [Equiv.symm_apply_apply] at hi hj
    rw [e] at hj
    exact (p.womanRank (f j)).injective (le_antisymm hi hj)
  let b := Equiv.ofBijective f ⟨inj, Finite.surjective_of_injective inj⟩
  have hb (w) (a) (ha : a ∈ s) : p.womanRank w (b.symm w) ≤ p.womanRank w (a.symm w) := by
    have := best (b.symm w) a ha
    change p.womanRank (b (b.symm w)) (b.symm w) ≤
      p.womanRank (b (b.symm w)) (a.symm (b (b.symm w))) at this
    simpa only [Equiv.apply_symm_apply] using this
  refine ⟨b, ?_, ?_, hb⟩
  · intro m w h
    exact hs _ (ht m) m w ⟨h.1, h.2.1, h.2.2.trans_le (hb w _ (ht m))⟩
  · intro w
    refine ⟨t (b.symm w), ht _, (t (b.symm w)).symm_apply_eq.mpr ?_⟩
    exact (b.apply_symm_apply w).symm

/-- Move the second class behind the first while preserving the old order in each class. -/
private theorem rank_by_class (r : Equiv.Perm (Fin n)) (P : Fin n → Prop) :
    ∃ h : Equiv.Perm (Fin n), (∀ i j, P i → ¬ P j → h i < h j) ∧
      (∀ i j, (P i ↔ P j) → (h i < h j ↔ r i < r j)) := by
  classical
  let key (i : Fin n) := (if P i then 0 else n) + (r i).val
  have incr {i j} (hi : P i) (hj : ¬ P j) : key i < key j := by
    simpa [key, hi, hj] using show (r i).val < n + (r j).val by have := (r i).isLt; omega
  have same {i j} (e : P i ↔ P j) : key i < key j ↔ r i < r j := by
    simp only [key, e, Nat.add_lt_add_iff_left]; rfl
  have inj : Function.Injective key := by
    intro i j eq
    by_cases e : P i ↔ P j
    · apply r.injective
      apply Fin.ext
      simpa [key, e] using eq
    · by_cases hi : P i
      · exact False.elim ((incr hi (fun hj => e (iff_of_true hi hj))).ne eq)
      · have hj : P j := by by_contra hn; exact e (iff_of_false hi hn)
        exact False.elim ((incr hj hi).ne eq.symm)
  obtain ⟨h, hh⟩ := exists_sorted_rank key inj
  exact ⟨h, fun i j hi hj => (hh i j).mpr (incr hi hj),
    fun i j e => (hh i j).trans (same e)⟩

/-- Append a matching that gives each woman either an unused partner or her best
partner in the old stable family. -/
theorem extend_family {p : Profile n} {s : Finset (Matching n)}
    (hs : ∀ a ∈ s, IsStable p a) (q : Matching n)
    (hq : ∀ w, (∃ a ∈ s, a.symm w = q.symm w) →
      ∀ a ∈ s, p.womanRank w (q.symm w) ≤ p.womanRank w (a.symm w)) :
    ∃ p' : Profile n, ∀ a ∈ insert q s, IsStable p' a := by
  classical
  let used (m w : Fin n) := ∃ a ∈ s, a m = w
  choose mr mfirst msame using fun m => rank_by_class (p.manRank m) (used m)
  choose wr wfirst wsame using fun w => rank_by_class (p.womanRank w) (· = q.symm w)
  refine ⟨⟨mr, wr⟩, ?_⟩
  intro a ha m w h
  rcases Finset.mem_insert.mp ha with rfl | ha
  · have hne : m ≠ a.symm w := fun e => h.1 (a.eq_symm_apply.mp e)
    exact (wfirst w _ _ rfl hne).not_gt h.2.2
  have hused : used m (a m) := ⟨a, ha, rfl⟩
  have he : used m w := by
    by_contra hn
    exact (mfirst m _ _ hused hn).not_gt h.2.1
  have hm := (msame m _ _ (iff_of_true he hused)).mp h.2.1
  apply hs a ha m w
  refine ⟨h.1, hm, ?_⟩
  by_cases hnew : m = q.symm w
  · obtain ⟨v, hv, hvw⟩ := he
    have hle := hq w ⟨v, hv, (v.eq_symm_apply.mpr hvw).symm.trans hnew⟩ a ha
    rw [← hnew] at hle
    exact lt_of_le_of_ne hle (fun e => h.1 (a.eq_symm_apply.mp ((p.womanRank w).injective e)))
  · have hn : a.symm w ≠ q.symm w := by
      intro e
      exact (wfirst w _ _ e hnew).not_gt h.2.2
    exact (wsame w _ _ (iff_of_false hnew hn)).mp h.2.2

/-- Restrict a map on a finite nonempty invariant set to a nonempty subset on which
it is onto. Outside this subset the resulting permutation fixes every point. -/
private theorem perm_of_map (f : Fin n → Fin n) (s : Finset (Fin n))
    (hs : s.Nonempty) (hf : ∀ i ∈ s, f i ∈ s) :
    ∃ (u : Finset (Fin n)) (e : Equiv.Perm (Fin n)), u.Nonempty ∧ u ⊆ s ∧
      (∀ i ∈ u, e i = f i) ∧ ∀ i ∉ u, e i = i := by
  classical
  have sub : s.image f ⊆ s := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hf i hi
  by_cases eq : s.image f = s
  · let g (i : s) : s := ⟨f i, hf i i.property⟩
    have sur : Function.Surjective g := by
      intro y
      have hy : y.val ∈ s.image f := eq.symm ▸ y.property
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hy
      exact ⟨⟨i, hi⟩, Subtype.ext he⟩
    let d : Equiv.Perm s := Equiv.ofBijective g ⟨Finite.injective_iff_surjective.mpr sur, sur⟩
    exact ⟨s, Equiv.Perm.ofSubtype d, hs, Finset.Subset.refl _,
      fun i hi => d.ofSubtype_apply_of_mem hi, fun i hi => d.ofSubtype_apply_of_not_mem hi⟩
  · have small := Finset.card_lt_card (show s.image f ⊂ s from Finset.ssubset_iff_subset_ne.mpr ⟨sub, eq⟩)
    obtain ⟨u, e, hu, hus, hin, hout⟩ := perm_of_map f (s.image f) (hs.image f)
      (fun i hi => Finset.mem_image_of_mem _ (sub hi))
    exact ⟨u, e, hu, hus.trans sub, hin, hout⟩
termination_by s.card

/-- A maximizing profile admits a matching b such that every nonempty set of its
couples has a man who sees every woman of that set among his stable partners. -/
theorem extremal_support (p : Profile n) (hmax : numStableMatchings p = maxStableMatchings n)
    (hp : 0 < numStableMatchings p) :
    ∃ b : Matching n, IsStable p b ∧
      (∀ w a, IsStable p a → p.womanRank w (b.symm w) ≤ p.womanRank w (a.symm w)) ∧
      ∀ t : Finset (Fin n), t.Nonempty →
        ∃ i ∈ t, ∀ j ∈ t, ∃ a : Matching n, IsStable p a ∧ a i = b j := by
  classical
  let s := Finset.univ.filter (IsStable p)
  have mem (a : Matching n) : a ∈ s ↔ IsStable p a := by simp [s]
  have hc : s.card = numStableMatchings p := (Fintype.card_subtype _).symm
  obtain ⟨b, hb, _, best⟩ := optimal (Finset.card_pos.mp (hc.symm ▸ hp)) (fun a ha => (mem a).mp ha)
  refine ⟨b, hb, fun w a ha => best w a ((mem a).mpr ha), ?_⟩
  intro t ht
  by_contra! hn
  choose next hnext using hn
  let f (i : Fin n) := if hi : i ∈ t then next i hi else i
  have hf (i) (hi : i ∈ t) : f i ∈ t ∧ ∀ a, IsStable p a → a i ≠ b (f i) := by
    simpa [f, hi] using hnext i hi
  obtain ⟨u, e, hu, hut, hin, hout⟩ := perm_of_map f t ht (fun i hi => (hf i hi).1)
  let q : Matching n := e.trans b
  have changed (m) (hm : m ∈ u) (a) (ha : IsStable p a) : a m ≠ q m := by
    change a m ≠ b (e m)
    rw [hin m hm]
    exact (hf m (hut hm)).2 a ha
  have fixed (m) (hm : m ∉ u) : q m = b m := by
    change b (e m) = b m
    rw [hout m hm]
  have hq : q ∉ s := by
    obtain ⟨m, hm⟩ := hu
    exact fun h => changed m hm q ((mem q).mp h) rfl
  obtain ⟨p', hext⟩ := extend_family (fun a ha => (mem a).mp ha) q (by
    rintro w ⟨v, hv, eq⟩ a ha
    have hstay : q.symm w ∉ u := by
      intro h
      apply changed _ h v ((mem v).mp hv)
      rw [← eq, v.apply_symm_apply, eq, q.apply_symm_apply]
    have hbw : q.symm w = b.symm w := b.eq_symm_apply.mpr ((fixed _ hstay).symm.trans (q.apply_symm_apply w))
    rw [hbw]
    exact best w a ha)
  have sub : insert q s ⊆ Finset.univ.filter (IsStable p') :=
    fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hext a ha⟩
  have he := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem hq, hc, hmax, ← Fintype.card_subtype] at he
  have hle : numStableMatchings p' ≤ maxStableMatchings n :=
    Finset.le_sup (s := Finset.univ) (f := numStableMatchings) (Finset.mem_univ p')
  change maxStableMatchings n + 1 ≤ numStableMatchings p' at he
  omega


private theorem order_support (R : Fin n → Fin n → Prop) (s : Finset (Fin n))
    (hs : ∀ t ⊆ s, t.Nonempty → ∃ i ∈ t, ∀ j ∈ t, R i j) :
    ∃ g : Fin n → ℕ, Set.InjOn g (s : Set (Fin n)) ∧
      ∀ i ∈ s, ∀ j ∈ s, g i ≤ g j → R i j := by
  classical
  by_cases he : s.Nonempty
  · obtain ⟨v, hv, hall⟩ := hs s (Finset.Subset.refl _) he
    have small := Finset.card_erase_lt_of_mem hv
    obtain ⟨f, hinj, ho⟩ := order_support R (s.erase v) (fun t ht => hs t (ht.trans (Finset.erase_subset _ _)))
    let g (i : Fin n) := if i = v then 0 else f i + 1
    refine ⟨g, ?_, ?_⟩
    · intro i hi j hj eq
      by_cases ei : i = v <;> by_cases ej : j = v
      · exact ei.trans ej.symm
      · simp [g, ei, ej] at eq
      · simp [g, ei, ej] at eq
      · exact hinj (Finset.mem_erase.mpr ⟨ei, hi⟩) (Finset.mem_erase.mpr ⟨ej, hj⟩)
          (by simpa [g, ei, ej] using eq)
    · intro i hi j hj le
      by_cases ei : i = v
      · exact ei ▸ hall j hj
      by_cases ej : j = v
      · simp [g, ei, ej] at le
      exact ho i (Finset.mem_erase.mpr ⟨ei, hi⟩) j (Finset.mem_erase.mpr ⟨ej, hj⟩)
        (by simpa [g, ei, ej] using le)
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    exact ⟨fun _ => 0, by simp, by simp⟩
termination_by s.card

/-- Normalize the terminal stable matching to women's first and men's last choices.
Every stable matching of the old profile survives. -/
private theorem extremes {p : Profile n} (b : Matching n) (hb : IsStable p b)
    (best : ∀ w a, IsStable p a → p.womanRank w (b.symm w) ≤ p.womanRank w (a.symm w)) :
    ∃ p' : Profile n, (∀ a, IsStable p a → IsStable p' a) ∧
      (∀ w i, i ≠ b.symm w → p'.womanRank w (b.symm w) < p'.womanRank w i) ∧
      ∀ m w, w ≠ b m → p'.manRank m w < p'.manRank m (b m) := by
  classical
  let used (w m : Fin n) := ∃ a, IsStable p a ∧ a m = w
  choose wr wf ws using fun w => rank_by_class (p.womanRank w) (used w)
  choose mr mf ms using fun m => rank_by_class (p.manRank m) (fun w => w ≠ b m)
  have use (a) (ha : IsStable p a) (w) : used w (a.symm w) := ⟨a, ha, a.apply_symm_apply w⟩
  refine ⟨⟨mr, wr⟩, ?_, ?_, fun m w hn => mf m _ _ hn (not_not.mpr rfl)⟩
  · intro a ha m w h
    have hw : used w m := by
      by_contra hn
      exact (wf w _ _ (use a ha w) hn).not_gt h.2.2
    have hwlt := (ws w _ _ (iff_of_true hw (use a ha w))).mp h.2.2
    apply ha m w
    refine ⟨h.1, ?_, hwlt⟩
    have hn : w ≠ b m := by
      rintro rfl
      exact (mf m _ _ h.1 (not_not.mpr rfl)).not_gt h.2.1
    by_cases he : a m = b m
    · obtain ⟨c, hc, hc'⟩ := hw
      have hle : p.manRank m (c m) ≤ p.manRank m (b m) := by
        refine le_of_not_gt fun lt' => ?_
        have hl := (opposite p hb hc m).mp lt'
        have hbest := best (c m) c hc
        rw [c.symm_apply_apply] at hbest
        exact hbest.not_gt hl
      rw [he, ← hc']
      exact lt_of_le_of_ne hle (fun eq => hn (hc' ▸ (p.manRank m).injective eq))
    · exact (ms m _ _ (iff_of_true hn he)).mp h.2.1
  · intro w i hn
    by_cases hi : used w i
    · obtain ⟨a, ha, hw⟩ := hi
      have he := (a.eq_symm_apply.mpr hw).symm
      apply (ws w _ _ (iff_of_true (use b hb w) ⟨a, ha, hw⟩)).mpr
      exact lt_of_le_of_ne (he ▸ best w a ha)
        (fun eq => hn ((p.womanRank w).injective eq).symm)
    · exact wf w _ _ (use b hb w) hi

/-- After relabeling and changing ranks on unsupported pairs, a maximizer has
the upper triangle in its stable-pair graph and opposite diagonal extreme ranks. -/
theorem normalized_max (n : ℕ) (hpos : 0 < maxStableMatchings n) :
    ∃ p : Profile n, numStableMatchings p = maxStableMatchings n ∧
      (∀ i j, i ≠ j → p.womanRank i i < p.womanRank i j ∧ p.manRank i j < p.manRank i i) ∧
      ∀ i j : Fin n, i ≤ j → ∃ a : Matching n, IsStable p a ∧ a i = j := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Profile n)) numStableMatchings
    Finset.univ_nonempty
  have hmax : numStableMatchings p = maxStableMatchings n := le_antisymm
    (Finset.le_sup (f := numStableMatchings) (Finset.mem_univ p)) (Finset.sup_le hp)
  obtain ⟨b, hb, hbest, htri⟩ := extremal_support p hmax (hmax ▸ hpos)
  obtain ⟨r, hstab, hw, hm⟩ := extremes b hb hbest
  obtain ⟨g, hinj, horder⟩ := order_support
    (fun i j => ∃ a : Matching n, IsStable p a ∧ a i = b j) Finset.univ (fun t _ => htri t)
  obtain ⟨idx, hidx⟩ := exists_sorted_rank g (fun i j eq => hinj (Finset.mem_univ i) (Finset.mem_univ j) eq)
  let M := idx.symm
  let W := M.trans b
  let p' : Profile n := ⟨fun i => W.trans (r.manRank (M i)), fun j => M.trans (r.womanRank (W j))⟩
  let rel (a : Matching n) := M.trans (a.trans W.symm)
  have stab (a) (ha : IsStable p a) : IsStable p' (rel a) := by
    intro i j h
    apply hstab a ha (M i) (W j)
    have he : W ((rel a) i) = a (M i) := W.apply_symm_apply _
    have he' : M ((rel a).symm j) = a.symm (W j) := M.apply_symm_apply _
    refine ⟨fun eq => h.1 (W.injective (he.trans eq)), ?_, ?_⟩
    · have lt' := h.2.1
      change r.manRank (M i) (W j) < r.manRank (M i) (W ((rel a) i)) at lt'
      rwa [he] at lt'
    · have lt' := h.2.2
      change r.womanRank (W j) (M i) < r.womanRank (W j) (M ((rel a).symm j)) at lt'
      rwa [he'] at lt'
  refine ⟨p', le_antisymm (Finset.le_sup (f := numStableMatchings) (Finset.mem_univ p')) ?_, ?_, ?_⟩
  · rw [← hmax]
    apply Fintype.card_le_of_injective
      (fun a : {a : Matching n // IsStable p a} => (⟨rel a.val, stab a.val a.property⟩ : {a : Matching n // IsStable p' a}))
    intro a c eq
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have h := congrArg (fun v : {v : Matching n // IsStable p' v} => W (v.val (M.symm i))) eq
    simpa [rel] using h
  · intro i j hn
    have eq : b.symm (W i) = M i := b.symm_apply_apply _
    have hw' := hw (W i) (M j) (by rw [eq]; exact fun h => hn (M.injective h).symm)
    rw [eq] at hw'
    exact ⟨hw', hm (M i) (W j) (fun h => hn (W.injective h).symm)⟩
  · intro i j hij
    have hle : g (M i) ≤ g (M j) := by
      refine le_of_not_gt fun hl => hij.not_gt ?_
      simpa [M] using (hidx _ _).mpr hl
    obtain ⟨a, ha, he⟩ := horder _ (Finset.mem_univ _) _ (Finset.mem_univ _) hle
    exact ⟨rel a, stab a ha, W.symm_apply_eq.mpr he⟩

private lemma separated {p : Profile n} {s : Finset (Matching n)}
    (hs : ∀ a ∈ s, IsStable p a) (h : 1 < s.card) :
    ∃ (l r : Finset (Matching n)) (i j : Fin n),
      i ≠ j ∧ l.Nonempty ∧ r.Nonempty ∧ Disjoint l r ∧ l ∪ r = s ∧
      Disjoint ((l.image (fun a => a i))) ((r.image (fun a => a i))) ∧ Disjoint ((l.image (fun a => a j))) ((r.image (fun a => a j))) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
  obtain ⟨w, hw⟩ : ∃ w, a.symm w ≠ b.symm w := by
    by_contra! hn
    exact hab (by simpa using congrArg Equiv.symm (Equiv.ext hn))
  let f (x : Matching n) := p.womanRank w (x.symm w)
  have hf : f a ≠ f b := fun e => hw ((p.womanRank w).injective e)
  let ranks := s.image f
  let low := ranks.min' ⟨_, Finset.mem_image_of_mem f ha⟩
  have hlow : low ∈ ranks := Finset.min'_mem _ _
  have hrest : (ranks.erase low).Nonempty := by
    by_cases he : f a = low
    · exact ⟨f b, Finset.mem_erase.mpr ⟨fun e => hf (he.trans e.symm), Finset.mem_image_of_mem f hb⟩⟩
    · exact ⟨f a, Finset.mem_erase.mpr ⟨he, Finset.mem_image_of_mem f ha⟩⟩
  let nxt := (ranks.erase low).min' hrest
  have hnxt := Finset.mem_erase.mp (Finset.min'_mem _ hrest)
  obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp hlow
  obtain ⟨v, hv, hev⟩ := Finset.mem_image.mp hnxt.2
  let l := s.filter (fun x => f x = low)
  let r := s.filter (fun x => f x ≠ low)
  have hlu : u ∈ l := Finset.mem_filter.mpr ⟨hu, heu⟩
  have hrv : v ∈ r := Finset.mem_filter.mpr ⟨hv, fun e => hnxt.1 (hev.symm.trans e)⟩
  have hmin (x) (hx : x ∈ r) : nxt ≤ f x :=
    Finset.min'_le _ _ (Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hx).2,
      Finset.mem_image_of_mem f (Finset.mem_filter.mp hx).1⟩)
  have hlt : low < nxt := lt_of_le_of_ne (Finset.min'_le ranks _ hnxt.2) hnxt.1.symm
  refine ⟨l, r, u.symm w, v.symm w, fun e => hlt.ne (heu.symm.trans
    ((congrArg (p.womanRank w) e).trans hev)), ⟨_, hlu⟩, ⟨_, hrv⟩, ?_, ?_, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr fun x hx hy => (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2
  · ext x
    simp [l, r, ← and_or_left, em]
  · apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hz'
    have hx' : x.symm w = u.symm w :=
      (p.womanRank w).injective ((Finset.mem_filter.mp hx).2.trans heu.symm)
    have he' : y (u.symm w) = w := by rw [he, ← hx', x.apply_symm_apply]
    have hy' : y.symm w = u.symm w := (y.symm_apply_eq.mpr he'.symm)
    exact (Finset.mem_filter.mp hy).2 ((congrArg (p.womanRank w) hy').trans heu)
  · apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hz'
    have comp (q : Matching n) (hq : q ∈ s) :
        p.manRank (v.symm w) (v (v.symm w)) < p.manRank (v.symm w) (q (v.symm w)) ↔
          f q < f v := by
      -- Compare with the matching v at its partner w.
      have op := opposite p (hs q hq) (hs v hv) (v.symm w)
      simp only [Equiv.apply_symm_apply] at op ⊢
      change _ ↔ p.womanRank w (q.symm w) < p.womanRank w (v.symm w)
      have heq : p.manRank (v.symm w) (q (v.symm w)) = p.manRank (v.symm w) w ↔
          p.womanRank w (v.symm w) = p.womanRank w (q.symm w) := by
        simp only [Equiv.apply_eq_iff_eq, Equiv.eq_symm_apply]
      exact lt_iff_lt_of_le_iff_le (by
        simp only [le_iff_lt_or_eq, op, heq])
    have hxl : f x < f v := (Finset.mem_filter.mp hx).2 ▸ hev ▸ hlt
    have hrank := (comp x (Finset.mem_filter.mp hx).1).mpr hxl
    rw [← he] at hrank
    have hylt := (comp y (Finset.mem_filter.mp hy).1).mp hrank
    rw [hev] at hylt
    exact (not_lt_of_ge (hmin y hy)) hylt


private theorem combine_squares {a b W x y u v C : ℕ}
    (ha : a ^ 2 * W ≤ x * y * C) (hb : b ^ 2 * W ≤ u * v * C) :
    (a + b) ^ 2 * W ≤ (x + u) * (y + v) * C := by
  have cs (i j : ℕ) : 4 * i * j ≤ (i + j) ^ 2 := by
    exact_mod_cast (show 4 * (i : ℤ) * j ≤ (i + j : ℤ) ^ 2 by nlinarith [sq_nonneg ((i : ℤ) - j)])
  have cross : 2 * a * b * W ≤ (x * v + u * y) * C := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    calc
      (2 * a * b * W) ^ 2 = 4 * ((a ^ 2 * W) * (b ^ 2 * W)) := by ring
      _ ≤ 4 * ((x * y * C) * (u * v * C)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul ha hb)
      _ = (4 * (x * v) * (u * y)) * C ^ 2 := by ring
      _ ≤ (x * v + u * y) ^ 2 * C ^ 2 := Nat.mul_le_mul_right _ (cs _ _)
      _ = ((x * v + u * y) * C) ^ 2 := by ring
  nlinarith only [ha, hb, cross]

/-- A weighted bound for any simultaneously stable family. Each column weight
occurs exactly once in each matching. -/
theorem family_weight_bound (p : Profile n) (s : Finset (Matching n))
    (hs : ∀ a ∈ s, IsStable p a) (z : Fin n → ℕ) :
    s.card ^ 2 * (∏ w, z w) ≤ ∏ i, ∑ w ∈ s.image (fun a => a i), z w := by
  classical
  by_cases h : 1 < s.card
  · obtain ⟨l, r, i, j, hij, hl, hr, hd, hu, hi, hj⟩ := separated hs h
    have hc : l.card + r.card = s.card := hu ▸ (Finset.card_union_of_disjoint hd).symm
    have hls : l ⊆ s := hu ▸ Finset.subset_union_left
    have hrs : r ⊆ s := hu ▸ Finset.subset_union_right
    have sl : l.card < s.card := by have := hr.card_pos; omega
    have sr : r.card < s.card := by have := hl.card_pos; omega
    let d (t : Finset (Matching n)) (m : Fin n) := ∑ w ∈ t.image (fun a => a m), z w
    let rem := (Finset.univ.erase i).erase j
    let C := ∏ m ∈ rem, d s m
    have factor (t : Finset (Matching n)) :
        (∏ m, d t m) = d t i * d t j * ∏ m ∈ rem, d t m := by
      have h1 := Finset.prod_erase_mul Finset.univ (d t) (Finset.mem_univ i)
      have h2 := Finset.prod_erase_mul (Finset.univ.erase i) (d t)
        (show j ∈ Finset.univ.erase i by simp [Ne.symm hij])
      unfold rem
      rw [← h1, ← h2]
      ring
    have mono {t : Finset (Matching n)} (ht : t ⊆ s) :
        (∏ m ∈ rem, d t m) ≤ C := by
      apply Finset.prod_le_prod' fun m _ => ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image ht) (by simp)
    have transfer (t : Finset (Matching n)) (ht : t ⊆ s) (st : t.card < s.card) :
        t.card ^ 2 * (∏ w, z w) ≤ d t i * d t j * C := by
      have ih := family_weight_bound p t (fun a ha => hs a (ht ha)) z
      change _ ≤ ∏ m, d t m at ih
      rw [factor] at ih
      exact ih.trans (Nat.mul_le_mul_left _ (mono ht))
    have join (m : Fin n) (hm : Disjoint ((l.image (fun a => a m))) ((r.image (fun a => a m)))) :
        d s m = d l m + d r m := by
      simp only [d, ← hu, Finset.image_union]
      exact Finset.sum_union hm
    change _ ≤ ∏ m, d s m
    rw [factor, join i hi, join j hj, ← hc]
    exact combine_squares (transfer l hls sl) (transfer r hrs sr)
  · by_cases he : s = ∅
    · simp [he]
    · have hh : s.card = 1 := by
        have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        omega
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hh
      simp only [Finset.card_singleton, one_pow, one_mul, Finset.image_singleton, Finset.sum_singleton]
      exact (Equiv.prod_comp a z).symm.le
termination_by s.card


/-- Column cycles are the complete obstruction to simultaneous stability for fixed men's ranks. -/
theorem realize_acyclic (s : Finset (Matching n)) (r : Fin n → Equiv.Perm (Fin n))
    (h : ∀ w, WellFounded (fun j m : Fin n => ∃ a ∈ s, a j = w ∧ r m w < r m (a m))) :
    ∃ p : Profile n, p.manRank = r ∧ ∀ a ∈ s, IsStable p a := by
  classical
  let rel (w j m : Fin n) := ∃ a ∈ s, a j = w ∧ r m w < r m (a m)
  have order (w) : ∃ rank : Equiv.Perm (Fin n), ∀ j m, rel w j m → rank j < rank m := by
    obtain ⟨g, inj, hg⟩ := order_support (fun i j => ¬ rel w j i) Finset.univ (by
      intro t _ ht
      exact (h w).has_min (t : Set (Fin n)) ht)
    obtain ⟨rank, hr⟩ := exists_sorted_rank g (fun i j eq => inj (Finset.mem_univ i) (Finset.mem_univ j) eq)
    exact ⟨rank, fun j m edge => (hr j m).mpr (lt_of_not_ge fun le =>
      hg m (Finset.mem_univ _) j (Finset.mem_univ _) le edge)⟩
  choose wr hw using order
  refine ⟨⟨r, wr⟩, rfl, ?_⟩
  intro a ha m w block
  exact (hw w (a.symm w) m ⟨a, ha, a.apply_symm_apply w, block.2.1⟩).not_gt block.2.2

-- The recurrence estimate is adapted from @tatashbar's merged R1.H1.
private theorem count_growth (k : ℕ) :
    1 ≤ irvingLeatherCount k ∧ 2 * irvingLeatherCount k ^ 2 ≤ irvingLeatherCount (k + 1) := by
  induction k with
  | zero => simp [irvingLeatherCount]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hy4 : 2 * irvingLeatherCount k ^ 4 ≤ irvingLeatherCount (k + 1) ^ 2 := by
      have : 2 * irvingLeatherCount k ^ 2 * (2 * irvingLeatherCount k ^ 2) ≤
          irvingLeatherCount (k + 1) * irvingLeatherCount (k + 1) := Nat.mul_le_mul h2 h2
      nlinarith
    refine ⟨by nlinarith, ?_⟩
    change _ ≤ 3 * irvingLeatherCount (k + 1) ^ 2 - 2 * irvingLeatherCount k ^ 4
    apply Nat.le_sub_of_add_le
    linarith

private theorem cover_size (k : ℕ) :
    Fintype.card {e : Fin (2 ^ k) × Fin (2 ^ k) // e.1 ≤ e.2} ≤ irvingLeatherCount k + 1 := by
  have large (l : ℕ) : (2 ^ (l + 3)) ^ 2 ≤ irvingLeatherCount (l + 3) := by
    induction l with
    | zero => decide
    | succ l ih =>
      have hg := (count_growth (l + 3)).2
      have hbase : 2 ≤ (2 ^ (l + 3)) ^ 2 := by
        have := Nat.one_le_two_pow (n := l)
        rw [pow_add]; nlinarith
      change (2 ^ ((l + 3) + 1)) ^ 2 ≤ _
      calc
        _ = 4 * (2 ^ (l + 3)) ^ 2 := by rw [pow_succ (2 : ℕ) (l + 3)]; ring
        _ ≤ 2 * irvingLeatherCount (l + 3) ^ 2 := by
          nlinarith only [Nat.mul_le_mul (hbase.trans ih) ih]
        _ ≤ _ := hg
  rcases k with _ | _ | _ | l
  · decide
  · decide
  · decide
  · refine (Fintype.card_subtype_le _).trans ?_
    rw [Fintype.card_prod, Fintype.card_fin, ← sq]
    exact (large l).trans (Nat.le_succ _)

/-- The Irving–Leather construction lower bound, already proved in R1.H1. -/
def H1 : Prop :=
  ∀ k, irvingLeatherCount k ≤ maxStableMatchings (2 ^ k)

/-- The remaining extremal question. A family of the forbidden size that covers
the upper triangle and passes every weighted partner test must force a cycle
in some woman's comparisons, for every choice of diagonal-last men's orders. -/
def H2 : Prop :=
  ∀ (k : ℕ) (s : Finset (Matching (2 ^ k))) (r : Fin (2 ^ k) → Equiv.Perm (Fin (2 ^ k))),
    s.card = irvingLeatherCount k + 1 →
    (∀ i j, i ≤ j → ∃ a ∈ s, a i = j) →
    (∀ i j, i ≠ j → r i j < r i i) →
    (∀ t ⊆ s, ∀ z : Fin (2 ^ k) → ℕ,
      t.card ^ 2 * (∏ w, z w) ≤ ∏ i, ∑ w ∈ t.image (fun a => a i), z w) →
    ∃ w, ¬ WellFounded (fun j m => ∃ a ∈ s, a j = w ∧ r m w < r m (a m))


/-- A counterexample to the cycle condition gives a violating profile by ordering
each column consistently with its forced comparisons. -/
theorem cycle_condition_of_upper
    (upper : ∀ k, maxStableMatchings (2 ^ k) ≤ irvingLeatherCount k) : H2 := by
  classical
  intro k s r hc _ _ _
  by_contra! h
  obtain ⟨p, _, hs⟩ := realize_acyclic s r h
  have sub : s ⊆ Finset.univ.filter (IsStable p) :=
    fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs a ha⟩
  have hcard := Finset.card_le_card sub
  rw [← Fintype.card_subtype] at hcard
  change s.card ≤ numStableMatchings p at hcard
  have hm : numStableMatchings p ≤ maxStableMatchings (2 ^ k) :=
    Finset.le_sup (s := Finset.univ) (f := numStableMatchings) (Finset.mem_univ p)
  have := (hcard.trans hm).trans (upper k)
  omega

theorem main : H1 → H2 → type_of% @IrvingLeather.irving_leather_pow_two := by
  classical
  intro lower upper k
  refine le_antisymm ?_ (lower k)
  by_contra! hlt
  obtain ⟨p, hp, he, htri⟩ := normalized_max (2 ^ k) (Nat.zero_lt_of_lt hlt)
  let all := Finset.univ.filter (IsStable p)
  have mem (a : Matching (2 ^ k)) : a ∈ all ↔ IsStable p a := by simp [all]
  have hc : all.card = maxStableMatchings (2 ^ k) := (Fintype.card_subtype _).symm.trans hp
  let Cell := {e : Fin (2 ^ k) × Fin (2 ^ k) // e.1 ≤ e.2}
  choose pick hstable hcell using fun t : Cell => htri t.val.1 t.val.2 t.property
  let seed := Finset.univ.image pick
  have hseed : seed ⊆ all := by
    intro a ha
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp ha
    exact (mem _).mpr (hstable e)
  have size : seed.card ≤ irvingLeatherCount k + 1 := by
    apply Finset.card_image_le.trans
    simpa only [Finset.card_univ] using cover_size k
  obtain ⟨s, hseed', hs, hsize⟩ := Finset.exists_subsuperset_card_eq hseed size (hc ▸ hlt)
  obtain ⟨w, bad⟩ := upper k s p.manRank hsize (by
    intro i j hij
    let e : Cell := ⟨(i, j), hij⟩
    exact ⟨pick e, hseed' (Finset.mem_image_of_mem _ (Finset.mem_univ e)), hcell e⟩)
    (fun i j hn => (he i j hn).2)
    (fun t ht z => family_weight_bound p t (fun a ha => (mem a).mp (hs (ht ha))) z)
  apply bad
  apply Subrelation.wf (r := fun j m : Fin (2 ^ k) => p.womanRank w j < p.womanRank w m)
    _ (InvImage.wf (p.womanRank w) wellFounded_lt)
  rintro j m ⟨a, ha, haj, hl⟩
  have hne : a m ≠ w := fun e => (e ▸ hl).false
  have hst := (mem a).mp (hs ha)
  have heq : a.symm w = j := a.symm_apply_eq.mpr haj.symm
  have hn := fun hh => hst m w ⟨hne, hl, hh⟩
  rw [heq] at hn
  exact lt_of_le_of_ne (le_of_not_gt hn) (fun eq => hne ((p.womanRank w).injective eq ▸ haj))

end OMA.R_IrvingLeather_irving_leather_pow_two_R2
