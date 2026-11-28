import OMAStatements.S_arxiv_2608_00825

namespace OMA.P_arxiv_2608_00825

open OMA.S_arxiv_2608_00825

/-! ### Part 0: General FinDigraph & Transport Helpers -/

private lemma reachIn_trans {V : Type*} {D : FinDigraph V} {k₁ k₂ : ℕ} {u w v : V}
    (h1 : ReachIn D k₁ u w) (h2 : ReachIn D k₂ w v) : ReachIn D (k₁ + k₂) u v := by
  induction h1 with
  | zero _ => simpa using h2
  | succ ha _ ih =>
    rw [Nat.succ_add]
    exact ReachIn.succ ha (ih h2)

private lemma reachIn_one {V : Type*} {D : FinDigraph V} {u v : V} (h : D.adj u v) :
    ReachIn D 1 u v :=
  ReachIn.succ h (ReachIn.zero v)

private lemma reachIn_of_iter {V : Type*} {D : FinDigraph V} (f : V → V)
    (hf : ∀ v, D.adj v (f v)) (u : V) : ∀ k : ℕ, ReachIn D k u (f^[k] u)
  | 0 => ReachIn.zero u
  | k + 1 => by
    rw [Function.iterate_succ_apply]
    exact ReachIn.succ (hf u) (reachIn_of_iter f hf (f u) k)

private def comapDigraph {V W : Type*} (D : FinDigraph V) (e : W ≃ V) : FinDigraph W where
  adj x y := D.adj (e x) (e y)
  loopless x := D.loopless (e x)

private lemma reachIn_comap_iff {V W : Type*} {D : FinDigraph V} (e : W ≃ V)
    {k : ℕ} {x y : W} : ReachIn (comapDigraph D e) k x y ↔ ReachIn D k (e x) (e y) := by
  constructor
  · intro h
    induction h with
    | zero _ => exact ReachIn.zero _
    | succ ha _ ih => exact ReachIn.succ ha ih
  · intro h
    generalize hx : e x = u at h
    generalize hy : e y = v at h
    induction h generalizing x y with
    | zero _ =>
      have : x = y := e.injective (hx.trans hy.symm)
      subst this; exact ReachIn.zero _
    | @succ k a b c ha _ ih =>
      have hb : e (e.symm b) = b := e.apply_symm_apply b
      have h1 : (comapDigraph D e).adj x (e.symm b) := by
        show D.adj (e x) (e (e.symm b))
        rwa [hx, hb]
      exact ReachIn.succ h1 (ih hb hy)

private lemma hasDirCycle_comap_iff {V W : Type*} {D : FinDigraph V} (e : W ≃ V) (ℓ : ℕ) :
    HasDirCycle (comapDigraph D e) ℓ ↔ HasDirCycle D ℓ := by
  constructor
  · rintro ⟨hℓ, f, hinj, hadj⟩
    exact ⟨hℓ, e ∘ f, e.injective.comp hinj, fun i => hadj i⟩
  · rintro ⟨hℓ, f, hinj, hadj⟩
    refine ⟨hℓ, e.symm ∘ f, e.symm.injective.comp hinj, fun i => ?_⟩
    show D.adj (e (e.symm (f i))) (e (e.symm _))
    simpa using hadj i

private lemma directedGirth_comap_iff {V W : Type*} {D : FinDigraph V} (e : W ≃ V) (ℓ : ℕ) :
    DirectedGirth (comapDigraph D e) ℓ ↔ DirectedGirth D ℓ := by
  simp only [DirectedGirth, hasDirCycle_comap_iff]

private lemma stronglyConnected_comap {V W : Type*} {D : FinDigraph V} (e : W ≃ V)
    (h : IsStronglyConnected D) : IsStronglyConnected (comapDigraph D e) := by
  intro x y
  obtain ⟨k, hk⟩ := h (e x) (e y)
  exact ⟨k, (reachIn_comap_iff e).mpr hk⟩

private lemma weaklyConnected_comap {V W : Type*} {D : FinDigraph V} (e : W ≃ V)
    (h : IsWeaklyConnected D) : IsWeaklyConnected (comapDigraph D e) := by
  intro x y
  have hr := h (e x) (e y)
  generalize hx : e x = u at hr
  generalize hy : e y = v at hr
  induction hr generalizing x y with
  | refl =>
    have : x = y := e.injective (hx.trans hy.symm)
    subst this; exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    have h1 := ih (x := x) (y := e.symm b) hx (e.apply_symm_apply b)
    refine Relation.ReflTransGen.tail h1 ?_
    show D.adj (e (e.symm b)) (e y) ∨ D.adj (e y) (e (e.symm b))
    simpa [hy] using hbc

private lemma sourceFree_comap {V W : Type*} {D : FinDigraph V} (e : W ≃ V)
    (h : IsSourceFree D) : IsSourceFree (comapDigraph D e) := by
  intro y
  obtain ⟨u, hu⟩ := h (e y)
  refine ⟨e.symm u, ?_⟩
  show D.adj (e (e.symm u)) (e y)
  simpa using hu

private lemma bipartite_comap_iff {V W : Type*} {D : FinDigraph V} (e : W ≃ V) :
    IsBipartite (comapDigraph D e) ↔ IsBipartite D := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c ∘ e.symm, fun u v huv => ?_⟩
    have : (comapDigraph D e).adj (e.symm u) (e.symm v) := by
      show D.adj (e (e.symm u)) (e (e.symm v)); simpa using huv
    exact hc _ _ this
  · rintro ⟨c, hc⟩
    exact ⟨c ∘ e, fun u v huv => hc (e u) (e v) huv⟩

private lemma qKernel_comap_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    {D : FinDigraph V} (e : W ≃ V) {q : ℕ} {Q : Finset W}
    (hQ : IsQKernel (comapDigraph D e) q Q) : IsQKernel D q (Q.image e) := by
  constructor
  · intro u hu v hv hadj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    exact hQ.1 x hx y hy hadj
  · intro v
    obtain ⟨x, hx, k, hk, hreach⟩ := hQ.2 (e.symm v)
    refine ⟨e x, Finset.mem_image_of_mem e hx, k, hk, ?_⟩
    have := (reachIn_comap_iff e).mp hreach
    simpa using this

private lemma card_image_equiv {V W : Type*} [DecidableEq V] (e : W ≃ V) (Q : Finset W) :
    (Q.image e).card = Q.card :=
  Finset.card_image_of_injective Q e.injective

/-! ### Part 1: Circlets and Theorems 1.2 & 1.3 -/

private abbrev CircletV (ℓ s t q : ℕ) :=
  (Fin ℓ × Fin s) ⊕ (Fin ℓ × Fin s × Fin t × Fin q)

private def finNext {ℓ : ℕ} (hℓ : 0 < ℓ) (r : Fin ℓ) : Fin ℓ :=
  ⟨(r.val + 1) % ℓ, Nat.mod_lt _ hℓ⟩

private lemma finNext_ne {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (r : Fin ℓ) :
    finNext (by omega : 0 < ℓ) r ≠ r := by
  intro h
  have hv := congrArg Fin.val h
  dsimp only [finNext] at hv
  by_cases hlt : r.val + 1 < ℓ
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have hr : r.val + 1 = ℓ := by omega
    rw [hr, Nat.mod_self] at hv; omega

private def circletAdj (ℓ s t q : ℕ) (hℓ : 2 ≤ ℓ) (_hs : 1 ≤ s) (_hq : 2 ≤ q) :
    CircletV ℓ s t q → CircletV ℓ s t q → Prop
  | Sum.inl (r₁, i₁), Sum.inl (r₂, i₂) =>
      (r₁ = r₂ ∧ i₁.val < i₂.val) ∨
      (r₂ = finNext (by omega) r₁ ∧ i₂.val = 0)
  | Sum.inl (r₁, i₁), Sum.inr (r₂, i₂, _, k₂) =>
      r₁ = r₂ ∧ i₁ = i₂ ∧ k₂.val = 0
  | Sum.inr (r₁, i₁, j₁, k₁), Sum.inr (r₂, i₂, j₂, k₂) =>
      r₁ = r₂ ∧ i₁ = i₂ ∧ j₁ = j₂ ∧ k₂.val = k₁.val + 1
  | Sum.inr (r₁, i₁, _, k₁), Sum.inl (r₂, i₂) =>
      k₁.val + 1 = q ∧
      if i₁.val + 1 < s then (r₂ = r₁ ∧ i₂.val = i₁.val + 1)
      else (r₂ = finNext (by omega) r₁ ∧ i₂.val = 0)

private def circletDigraph (ℓ s t q : ℕ) (hℓ : 2 ≤ ℓ) (hs : 1 ≤ s) (hq : 2 ≤ q) :
    FinDigraph (CircletV ℓ s t q) where
  adj := circletAdj ℓ s t q hℓ hs hq
  loopless := by
    intro v h
    rcases v with ⟨r, i⟩ | ⟨r, i, j, k⟩
    · rcases h with ⟨_, hlt⟩ | ⟨hnext, _⟩
      · omega
      · exact finNext_ne hℓ r hnext.symm
    · rcases h with ⟨_, _, _, hk⟩
      omega

private lemma circlet_stronglyConnected {ℓ s t q : ℕ} (hℓ : 2 ≤ ℓ) (hs : 1 ≤ s) (hq : 2 ≤ q) :
    IsStronglyConnected (circletDigraph ℓ s t q hℓ hs hq) := by
  let D := circletDigraph ℓ s t q hℓ hs hq
  let c0 : Fin ℓ → CircletV ℓ s t q := fun r => Sum.inl (r, ⟨0, hs⟩)
  -- Step 1: `c0 r` reaches `c0 (finNext r)` in 1 step, hence any `c0 r'` in `≤ ℓ` steps!
  have hc0_step : ∀ r : Fin ℓ, D.adj (c0 r) (c0 (finNext (by omega) r)) := fun r =>
    Or.inr ⟨rfl, rfl⟩
  have hc0_reach : ∀ r₁ r₂ : Fin ℓ, ∃ k, ReachIn D k (c0 r₁) (c0 r₂) := by
    intro r₁ r₂
    have hiter : ∀ k : ℕ, ∃ r' : Fin ℓ, r'.val = (r₁.val + k) % ℓ ∧ ReachIn D k (c0 r₁) (c0 r') := by
      intro k
      induction k with
      | zero => exact ⟨r₁, by simp [Nat.mod_eq_of_lt r₁.isLt], ReachIn.zero _⟩
      | succ k ih =>
        obtain ⟨r', hr', hreach⟩ := ih
        refine ⟨finNext (by omega) r', ?_, reachIn_trans hreach (reachIn_one (hc0_step r'))⟩
        dsimp only [finNext]
        rw [hr', Nat.mod_add_mod, Nat.add_assoc]
    let d := (r₂.val + ℓ - r₁.val) % ℓ
    obtain ⟨r', hr', hreach⟩ := hiter d
    have hr'_eq : r' = r₂ := by
      apply Fin.ext
      rw [hr']
      have h1 : (r₁.val + (r₂.val + ℓ - r₁.val) % ℓ) % ℓ = (r₁.val + (r₂.val + ℓ - r₁.val)) % ℓ := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [h1, show r₁.val + (r₂.val + ℓ - r₁.val) = r₂.val + ℓ by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt r₂.isLt]
    exact ⟨d, hr'_eq ▸ hreach⟩
  -- Step 2: Every `c0 r` reaches every vertex in block `r`
  have hfrom_c0 : ∀ (r : Fin ℓ) (v : CircletV ℓ s t q),
      (match v with | Sum.inl (r', _) => r' = r | Sum.inr (r', _, _, _) => r' = r) →
      ∃ k, ReachIn D k (c0 r) v := by
    intro r v hv
    rcases v with ⟨r', i⟩ | ⟨r', i, j, k⟩
    · dsimp only at hv; subst r'
      by_cases hi : i.val = 0
      · have : i = ⟨0, hs⟩ := Fin.ext hi; subst this; exact ⟨0, ReachIn.zero _⟩
      · exact ⟨1, reachIn_one (Or.inl ⟨rfl, by show (0 : ℕ) < i.val; omega⟩)⟩
    · dsimp only at hv; subst r'
      have hci : ∃ k1, ReachIn D k1 (c0 r) (Sum.inl (r, i)) := by
        by_cases hi : i.val = 0
        · have : i = ⟨0, hs⟩ := Fin.ext hi; subst this; exact ⟨0, ReachIn.zero _⟩
        · exact ⟨1, reachIn_one (Or.inl ⟨rfl, by show (0 : ℕ) < i.val; omega⟩)⟩
      have hpath : ∀ (m : ℕ) (hm : m < q),
          ReachIn D (m + 1) (Sum.inl (r, i)) (Sum.inr (r, i, j, ⟨m, hm⟩)) := by
        intro m
        induction m with
        | zero => intro hm; exact reachIn_one ⟨rfl, rfl, rfl⟩
        | succ m ih =>
          intro hm
          exact reachIn_trans (ih (by omega)) (reachIn_one ⟨rfl, rfl, rfl, rfl⟩)
      obtain ⟨k1, hk1⟩ := hci
      exact ⟨k1 + (k.val + 1), reachIn_trans hk1 (hpath k.val k.isLt)⟩
  -- Step 3: Every vertex reaches some `c0 r'`
  have hto_c0 : ∀ u : CircletV ℓ s t q, ∃ r' k, ReachIn D k u (c0 r') := by
    intro u
    rcases u with ⟨r, i⟩ | ⟨r, i, j, k⟩
    · exact ⟨finNext (by omega) r, 1, reachIn_one (Or.inr ⟨rfl, rfl⟩)⟩
    · have hwalk : ∀ (d : ℕ) (m : ℕ) (hm : m < q), m + d = q - 1 →
          ReachIn D d (Sum.inr (r, i, j, ⟨m, hm⟩)) (Sum.inr (r, i, j, ⟨q - 1, by omega⟩)) := by
        intro d
        induction d with
        | zero =>
          intro m hm hsum
          have : m = q - 1 := by omega
          subst this; exact ReachIn.zero _
        | succ d ih =>
          intro m hm hsum
          have hm1 : m + 1 < q := by omega
          exact ReachIn.succ (w := Sum.inr (r, i, j, ⟨m + 1, hm1⟩)) ⟨rfl, rfl, rfl, rfl⟩ (ih (m + 1) hm1 (by omega))
      have hreach_end := hwalk (q - 1 - k.val) k.val k.isLt (by omega)
      by_cases hi : i.val + 1 < s
      · have hlast : D.adj (Sum.inr (r, i, j, ⟨q - 1, by omega⟩)) (Sum.inl (r, ⟨i.val + 1, hi⟩)) := by
          refine ⟨by show q - 1 + 1 = q; omega, ?_⟩; simp [hi]
        have hstep := reachIn_trans hreach_end (reachIn_one hlast)
        exact ⟨finNext (by omega) r, (q - 1 - k.val) + 1 + 1,
          reachIn_trans hstep (reachIn_one (Or.inr ⟨rfl, rfl⟩))⟩
      · have hlast : D.adj (Sum.inr (r, i, j, ⟨q - 1, by omega⟩)) (c0 (finNext (by omega) r)) := by
          refine ⟨by show q - 1 + 1 = q; omega, ?_⟩; simp [hi]
        exact ⟨finNext (by omega) r, (q - 1 - k.val) + 1,
          reachIn_trans hreach_end (reachIn_one hlast)⟩
  intro u v
  obtain ⟨r₁, k₁, hk₁⟩ := hto_c0 u
  let r₂ : Fin ℓ := match v with | Sum.inl (r, _) => r | Sum.inr (r, _, _, _) => r
  obtain ⟨k₂, hk₂⟩ := hc0_reach r₁ r₂
  obtain ⟨k₃, hk₃⟩ := hfrom_c0 r₂ v (by cases v <;> rfl)
  exact ⟨k₁ + k₂ + k₃, reachIn_trans (reachIn_trans hk₁ hk₂) hk₃⟩

private lemma circlet_not_bipartite {ℓ s t q : ℕ} (hℓ : 2 ≤ ℓ) (hs2 : 2 ≤ s) (hq : 2 ≤ q) :
    ¬ IsBipartite (circletDigraph ℓ s t q hℓ (by omega) hq) := by
  rintro ⟨c, hc⟩
  let u1 : CircletV ℓ s t q := Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩)
  let u2 : CircletV ℓ s t q := Sum.inl (⟨0, by omega⟩, ⟨1, hs2⟩)
  let u3 : CircletV ℓ s t q := Sum.inl (finNext (by omega) ⟨0, by omega⟩, ⟨0, by omega⟩)
  have h12 : c u1 ≠ c u2 := hc u1 u2 (Or.inl ⟨rfl, by show (0 : ℕ) < 1; omega⟩)
  have h23 : c u2 ≠ c u3 := hc u2 u3 (Or.inr ⟨rfl, rfl⟩)
  have h13 : c u1 ≠ c u3 := hc u1 u3 (Or.inr ⟨rfl, rfl⟩)
  cases hcu1 : c u1 <;> cases hcu2 : c u2 <;> cases hcu3 : c u3 <;> simp_all

private def circletBlock {ℓ s t q : ℕ} : CircletV ℓ s t q → Fin ℓ
  | Sum.inl (r, _) => r
  | Sum.inr (r, _, _, _) => r

private def circletRank {ℓ s t q : ℕ} : CircletV ℓ s t q → ℕ
  | Sum.inl (_, i) => i.val * (q + 1)
  | Sum.inr (_, i, _, k) => i.val * (q + 1) + (k.val + 1)

private lemma circlet_arc_block_rank {ℓ s t q : ℕ} (hℓ : 2 ≤ ℓ) (hs : 1 ≤ s) (hq : 2 ≤ q)
    {u v : CircletV ℓ s t q} (h : (circletDigraph ℓ s t q hℓ hs hq).adj u v) :
    (circletBlock v = circletBlock u ∧ circletRank u < circletRank v) ∨
    circletBlock v = finNext (by omega) (circletBlock u) := by
  rcases u with ⟨r₁, i₁⟩ | ⟨r₁, i₁, j₁, k₁⟩ <;> rcases v with ⟨r₂, i₂⟩ | ⟨r₂, i₂, j₂, k₂⟩
  · rcases h with ⟨rfl, hlt⟩ | ⟨rfl, _⟩
    · left; refine ⟨rfl, ?_⟩
      simp only [circletRank]; exact Nat.mul_lt_mul_of_pos_right hlt (by omega)
    · right; rfl
  · rcases h with ⟨rfl, rfl, hk2⟩
    left; refine ⟨rfl, ?_⟩
    simp only [circletRank]; omega
  · rcases h with ⟨hk1, hcond⟩
    by_cases hi : i₁.val + 1 < s
    · rw [if_pos hi] at hcond
      rcases hcond with ⟨rfl, hi2⟩
      left; refine ⟨rfl, ?_⟩
      simp only [circletRank, hi2]
      have : (i₁.val + 1) * (q + 1) = i₁.val * (q + 1) + (q + 1) := by ring
      omega
    · rw [if_neg hi] at hcond
      rcases hcond with ⟨rfl, _⟩
      right; rfl
  · rcases h with ⟨rfl, rfl, rfl, hk2⟩
    left; refine ⟨rfl, ?_⟩
    simp only [circletRank]; omega

private lemma circlet_directedGirth {ℓ s t q : ℕ} (hℓ : 2 ≤ ℓ) (hs : 1 ≤ s) (hq : 2 ≤ q) :
    DirectedGirth (circletDigraph ℓ s t q hℓ hs hq) ℓ := by
  let D := circletDigraph ℓ s t q hℓ hs hq
  constructor
  · refine ⟨hℓ, fun r => Sum.inl (r, ⟨0, hs⟩), fun r₁ r₂ h => ?_, fun r => Or.inr ⟨rfl, rfl⟩⟩
    injection h with h1; exact congrArg Prod.fst h1
  · rintro ℓ' ⟨hℓ'2, f, _, hadj⟩
    -- Count how many steps around the cycle advance `circletBlock` by `+1 (mod ℓ)`.
    let stepAdv (i : Fin ℓ') : ℕ :=
      if circletBlock (f ⟨(i.val + 1) % ℓ', Nat.mod_lt _ (by omega)⟩) = circletBlock (f i) then 0 else 1
    have hstep_mod : ∀ m : ℕ, m ≤ ℓ' →
        (circletBlock (f ⟨m % ℓ', Nat.mod_lt _ (by omega)⟩)).val =
          ((circletBlock (f ⟨0, by omega⟩)).val +
            ∑ i ∈ Finset.univ.filter (fun i : Fin ℓ' => i.val < m), stepAdv i) % ℓ := by
      intro m hm
      induction m with
      | zero =>
        simp [Nat.mod_eq_of_lt (circletBlock (f ⟨0, by omega⟩)).isLt]
      | succ m ih =>
        have hlt : m < ℓ' := by omega
        let im : Fin ℓ' := ⟨m, hlt⟩
        have hfilt : (Finset.univ.filter fun i : Fin ℓ' => i.val < m + 1) =
            insert im (Finset.univ.filter fun i : Fin ℓ' => i.val < m) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, im]
          constructor
          · intro h; by_cases hm' : i.val = m
            · left; exact Fin.ext hm'
            · right; omega
          · rintro (rfl | h)
            · dsimp only [im]; omega
            · omega
        have hnotmem : im ∉ Finset.univ.filter (fun i : Fin ℓ' => i.val < m) := by
          simp [im]
        rw [hfilt, Finset.sum_insert hnotmem]
        have hprev := ih (by omega)
        have hmodm : m % ℓ' = m := Nat.mod_eq_of_lt hlt
        have hprev' : (circletBlock (f im)).val =
            ((circletBlock (f ⟨0, by omega⟩)).val +
              ∑ i ∈ Finset.univ.filter (fun i : Fin ℓ' => i.val < m), stepAdv i) % ℓ := by
          have him_eq : im = ⟨m % ℓ', Nat.mod_lt _ (by omega)⟩ := Fin.ext hmodm.symm
          rw [him_eq]; exact hprev
        rcases circlet_arc_block_rank hℓ hs hq (hadj im) with ⟨heq, _⟩ | hnext
        · have hadv0 : stepAdv im = 0 := by simp [stepAdv, im, heq]
          rw [hadv0, zero_add]
          simpa [im, heq] using hprev'
        · have hne : circletBlock (f ⟨(m + 1) % ℓ', Nat.mod_lt _ (by omega)⟩) ≠ circletBlock (f im) := by
            rw [hnext]; exact finNext_ne hℓ _
          have hadv1 : stepAdv im = 1 := by simp [stepAdv, im, hne]
          rw [hadv1]
          have hval : (circletBlock (f ⟨(m + 1) % ℓ', Nat.mod_lt _ (by omega)⟩)).val =
              ((circletBlock (f im)).val + 1) % ℓ := congrArg Fin.val hnext
          rw [hval, hprev', Nat.mod_add_mod]
          congr 1; ring
    let totalAdv := ∑ i : Fin ℓ', stepAdv i
    have hfilt_all : Finset.univ.filter (fun i : Fin ℓ' => i.val < ℓ') = Finset.univ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, i.isLt]
    have hloop := hstep_mod ℓ' (le_refl ℓ')
    have hfin0 : (⟨ℓ' % ℓ', Nat.mod_lt _ (by omega)⟩ : Fin ℓ') = ⟨0, by omega⟩ := Fin.ext (Nat.mod_self ℓ')
    rw [hfin0, hfilt_all] at hloop
    have hdiv : ℓ ∣ totalAdv := by
      have h1 : (circletBlock (f ⟨0, by omega⟩)).val % ℓ =
          ((circletBlock (f ⟨0, by omega⟩)).val + totalAdv) % ℓ := by
        rw [Nat.mod_eq_of_lt (circletBlock (f ⟨0, by omega⟩)).isLt]
        exact hloop
      have hmodEq : (circletBlock (f ⟨0, by omega⟩)).val ≡
          (circletBlock (f ⟨0, by omega⟩)).val + totalAdv [MOD ℓ] := h1
      have h0 : 0 ≡ totalAdv [MOD ℓ] := by
        exact Nat.ModEq.add_left_cancel' (circletBlock (f ⟨0, by omega⟩)).val
          (by simpa [add_zero] using hmodEq)
      exact Nat.dvd_of_mod_eq_zero h0.symm
    have hpos : 0 < totalAdv := by
      by_contra h0
      have hall0 : ∀ i : Fin ℓ', stepAdv i = 0 := fun i => by
        have hle : stepAdv i ≤ totalAdv := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hinc : ∀ m : ℕ, m ≤ ℓ' →
          circletRank (f ⟨0, by omega⟩) + m ≤ circletRank (f ⟨m % ℓ', Nat.mod_lt _ (by omega)⟩) := by
        intro m hm
        induction m with
        | zero => simp
        | succ m ih =>
          have hlt : m < ℓ' := by omega
          let im : Fin ℓ' := ⟨m, hlt⟩
          have h1 := ih (by omega)
          have hmodm : m % ℓ' = m := Nat.mod_eq_of_lt hlt
          have h1' : circletRank (f ⟨0, by omega⟩) + m ≤ circletRank (f im) := by
            have him_eq : im = ⟨m % ℓ', Nat.mod_lt _ (by omega)⟩ := Fin.ext hmodm.symm
            rw [him_eq]; exact h1
          have ha0 := hall0 im
          have hbeq : circletBlock (f ⟨(m + 1) % ℓ', Nat.mod_lt _ (by omega)⟩) = circletBlock (f im) := by
            by_contra hne; simp [stepAdv, im, hne] at ha0
          rcases circlet_arc_block_rank hℓ hs hq (hadj im) with ⟨_, hlt_r⟩ | hnext
          · have hlt_r' : circletRank (f im) < circletRank (f ⟨(m + 1) % ℓ', Nat.mod_lt _ (by omega)⟩) := hlt_r
            omega
          · exact absurd (hbeq.symm.trans hnext) (finNext_ne hℓ _).symm
      have hcontra := hinc ℓ' (le_refl ℓ')
      rw [hfin0] at hcontra
      omega
    have hle_sum : totalAdv ≤ ℓ' := by
      calc totalAdv = ∑ i : Fin ℓ', stepAdv i := rfl
        _ ≤ ∑ _i : Fin ℓ', 1 := Finset.sum_le_sum fun i _ => by dsimp only [stepAdv]; split_ifs <;> omega
        _ = ℓ' := by simp
    have hℓ_le : ℓ ≤ totalAdv := Nat.le_of_dvd hpos hdiv
    omega

private lemma reachIn_snoc_iff {V : Type*} {D : FinDigraph V} {k : ℕ} {u v : V} :
    ReachIn D (k + 1) u v ↔ ∃ w : V, ReachIn D k u w ∧ D.adj w v := by
  constructor
  · intro h
    induction k generalizing u with
    | zero =>
      cases h with
      | succ ha h0 => cases h0; exact ⟨u, ReachIn.zero u, ha⟩
    | succ k ih =>
      cases h with
      | succ ha hrest =>
        obtain ⟨w, hw, hwa⟩ := ih hrest
        exact ⟨w, ReachIn.succ ha hw, hwa⟩
  · rintro ⟨w, hw, hwa⟩
    exact reachIn_trans hw (reachIn_one hwa)

private lemma circlet_pred_pend {ℓ s t q : ℕ} (hℓ : 2 ≤ ℓ) (hs : 1 ≤ s) (hq : 2 ≤ q)
    (r : Fin ℓ) (i : Fin s) (j : Fin t) :
    ∀ (d m : ℕ) (hm : m < q) (u : CircletV ℓ s t q), d ≤ m + 1 →
      ReachIn (circletDigraph ℓ s t q hℓ hs hq) d u (Sum.inr (r, i, j, ⟨m, hm⟩)) →
      u = Sum.inl (r, i) ∨ ∃ k : Fin q, u = Sum.inr (r, i, j, k) := by
  intro d
  induction d with
  | zero =>
    intro m hm u _ hr
    cases hr; exact Or.inr ⟨⟨m, hm⟩, rfl⟩
  | succ d ih =>
    intro m hm u hdm hr
    obtain ⟨w, hwu, hwv⟩ := reachIn_snoc_iff.mp hr
    rcases w with ⟨rw, iw⟩ | ⟨rw, iw, jw, kw⟩
    · rcases hwv with ⟨rfl, rfl, hm0⟩
      change m = 0 at hm0
      have hd0 : d = 0 := by omega
      subst hd0; cases hwu; exact Or.inl rfl
    · rcases hwv with ⟨rfl, rfl, rfl, hkm⟩
      change m = kw.val + 1 at hkm
      have hkw : kw = ⟨m - 1, by omega⟩ := Fin.ext (by show kw.val = m - 1; omega)
      rw [hkw] at hwu
      exact ih (m - 1) (by omega) u (by omega) hwu

private lemma circlet_qKernel_card {ℓ s t q : ℕ} (hℓ : 2 ≤ ℓ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hq : 2 ≤ q)
    {Q : Finset (CircletV ℓ s t q)} (hQ : IsQKernel (circletDigraph ℓ s t q hℓ hs hq) q Q) :
    ℓ * (s - 1) * t + ℓ ≤ Q.card := by
  classical
  -- Partition `Q` by block `r : Fin ℓ`
  let Qblk (r : Fin ℓ) : Finset (CircletV ℓ s t q) := Q.filter fun v => circletBlock v = r
  have hsum_card : ∑ r : Fin ℓ, (Qblk r).card = Q.card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext v; simp [Qblk]
    · intro r₁ _ r₂ _ hne
      change Disjoint (Qblk r₁) (Qblk r₂)
      rw [Finset.disjoint_left]
      intro v h1 h2
      exact hne (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
  have hblk_lb : ∀ r : Fin ℓ, (s - 1) * t + 1 ≤ (Qblk r).card := by
    intro r
    -- Every `(i, j)` has a vertex in `Q` on its path `{c r i} ∪ {p r i j k}`
    have hcov : ∀ (i : Fin s) (j : Fin t),
        Sum.inl (r, i) ∈ Q ∨ ∃ k : Fin q, Sum.inr (r, i, j, k) ∈ Q := by
      intro i j
      obtain ⟨u, huQ, d, hdq, hreach⟩ := hQ.2 (Sum.inr (r, i, j, ⟨q - 1, by omega⟩))
      rcases circlet_pred_pend hℓ hs hq r i j d (q - 1) (by omega) u (by omega) hreach with rfl | ⟨k, rfl⟩
      · exact Or.inl huQ
      · exact Or.inr ⟨k, huQ⟩
    -- At most one `i : Fin s` has `Sum.inl (r, i) ∈ Q`
    have hatmost1 : ∀ i₁ i₂ : Fin s, Sum.inl (r, i₁) ∈ Q → Sum.inl (r, i₂) ∈ Q → i₁ = i₂ := by
      intro i₁ i₂ h1 h2
      by_contra hne
      rcases lt_or_gt_of_ne (fun hv => hne (Fin.ext hv)) with hlt | hgt
      · exact hQ.1 _ h1 _ h2 (Or.inl ⟨rfl, hlt⟩)
      · exact hQ.1 _ h2 _ h1 (Or.inl ⟨rfl, hgt⟩)
    by_cases hex : ∃ i₀ : Fin s, Sum.inl (r, i₀) ∈ Q
    · obtain ⟨i₀, hi₀⟩ := hex
      -- Injection from `((Finset.univ.erase i₀) ×ˢ Finset.univ) ⊕ Unit` into `Qblk r`!
      have hp_ex : ∀ i : Fin s, i ≠ i₀ → ∀ j : Fin t, ∃ k : Fin q, Sum.inr (r, i, j, k) ∈ Q := by
        intro i hi j
        rcases hcov i j with hci | hpk
        · exact absurd (hatmost1 i i₀ hci hi₀) hi
        · exact hpk
      let S_pairs : Finset (Fin s × Fin t) := (Finset.univ.erase i₀) ×ˢ Finset.univ
      let f : Fin s × Fin t → CircletV ℓ s t q := fun p =>
        if h : p.1 ≠ i₀ then Sum.inr (r, p.1, p.2, Classical.choose (hp_ex p.1 h p.2))
        else Sum.inl (r, i₀)
      let Pimg : Finset (CircletV ℓ s t q) := S_pairs.image f
      have hPsub : insert (Sum.inl (r, i₀)) Pimg ⊆ Qblk r := by
        intro v hv
        simp only [Finset.mem_insert, Pimg, Finset.mem_image] at hv
        rcases hv with rfl | ⟨⟨i, j⟩, hij, rfl⟩
        · exact Finset.mem_filter.mpr ⟨hi₀, rfl⟩
        · have hi : i ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_product.mp hij).1).1
          simp only [f, dif_pos hi]
          exact Finset.mem_filter.mpr ⟨Classical.choose_spec (hp_ex i hi j), rfl⟩
      have hnotmem : Sum.inl (r, i₀) ∉ Pimg := by
        simp only [Pimg, Finset.mem_image, not_exists, not_and]
        rintro ⟨i, j⟩ hij heq
        have hi : i ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_product.mp hij).1).1
        simp only [f, dif_pos hi] at heq
        exact Sum.inr_ne_inl heq
      have hPcard : Pimg.card = S_pairs.card := by
        refine Finset.card_image_of_injOn fun p₁ hp₁ p₂ hp₂ heq => ?_
        have h1 : p₁.1 ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_product.mp hp₁).1).1
        have h2 : p₂.1 ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_product.mp hp₂).1).1
        simp only [f, dif_pos h1, dif_pos h2] at heq
        injection heq with htu
        have h1' := congrArg (fun x => x.2.1) htu
        have h2' := congrArg (fun x => x.2.2.1) htu
        exact Prod.ext h1' h2'
      have hScard : S_pairs.card = (s - 1) * t := by
        simp [S_pairs, Finset.card_product, Finset.card_erase_of_mem]
      have hle := Finset.card_le_card hPsub
      rw [Finset.card_insert_of_notMem hnotmem, hPcard, hScard] at hle
      exact hle
    · push Not at hex
      have hp_ex : ∀ (i : Fin s) (j : Fin t), ∃ k : Fin q, Sum.inr (r, i, j, k) ∈ Q := fun i j =>
        (hcov i j).resolve_left (hex i)
      let f : Fin s × Fin t → CircletV ℓ s t q := fun p =>
        Sum.inr (r, p.1, p.2, Classical.choose (hp_ex p.1 p.2))
      have hsub : (Finset.univ : Finset (Fin s × Fin t)).image f ⊆ Qblk r := by
        intro v hv
        obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_filter.mpr ⟨Classical.choose_spec (hp_ex i j), rfl⟩
      have hcard : ((Finset.univ : Finset (Fin s × Fin t)).image f).card = s * t := by
        rw [Finset.card_image_of_injective _ (fun p₁ p₂ heq => by
          injection heq with htu
          exact Prod.ext (congrArg (fun x => x.2.1) htu) (congrArg (fun x => x.2.2.1) htu))]
        simp
      have hle := Finset.card_le_card hsub
      rw [hcard] at hle
      have hst : (s - 1) * t + 1 ≤ s * t := by
        have : s * t = (s - 1) * t + t := by
          cases s with
          | zero => omega
          | succ s' => simp [Nat.add_mul]
        omega
      omega
  have htot : ∑ _r : Fin ℓ, ((s - 1) * t + 1) ≤ ∑ r : Fin ℓ, (Qblk r).card :=
    Finset.sum_le_sum fun r _ => hblk_lb r
  rw [hsum_card, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at htot
  calc ℓ * (s - 1) * t + ℓ = ℓ * ((s - 1) * t + 1) := by ring
    _ ≤ Q.card := htot

private lemma card_circletV (ℓ s t q : ℕ) :
    Fintype.card (CircletV ℓ s t q) = ℓ * s + ℓ * s * t * q := by
  simp only [CircletV, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

private lemma theorem_1_2 :
    ∀ q ℓ : ℕ, 2 ≤ q → q * (q + 1) < ℓ →
      ∃ (n : ℕ) (D : FinDigraph (Fin n)),
        0 < n ∧ IsStronglyConnected D ∧ ¬ IsBipartite D ∧ DirectedGirth D ℓ ∧
        ∀ Q : Finset (Fin n), IsQKernel D q Q →
          ∀ ℓ' : ℕ, HasDirCycle D ℓ' →
            ((ceilDiv ℓ' (q + 1) : ℚ) / (ℓ' : ℚ)) * (n : ℚ) < (Q.card : ℚ) := by
  intro q ℓ hq hℓq
  have hℓ : 2 ≤ ℓ := by nlinarith
  let s : ℕ := 2 * ℓ * (q + 1) + 2
  have hs2 : 2 ≤ s := by omega
  let D0 := circletDigraph ℓ s s q hℓ (by omega) hq
  let n := Fintype.card (CircletV ℓ s s q)
  let e : Fin n ≃ CircletV ℓ s s q := (Fintype.equivFin (CircletV ℓ s s q)).symm
  refine ⟨n, comapDigraph D0 e, ?_, stronglyConnected_comap e (circlet_stronglyConnected hℓ (by omega) hq),
    mt (bipartite_comap_iff e).mp (circlet_not_bipartite hℓ hs2 hq),
    (directedGirth_comap_iff e ℓ).mpr (circlet_directedGirth hℓ (by omega) hq), ?_⟩
  · dsimp only [n]; rw [card_circletV]; positivity
  · intro Q hQ ℓ' hℓ'
    have hℓ'_ge : ℓ ≤ ℓ' :=
      (circlet_directedGirth hℓ (by omega) hq).2 ℓ' ((hasDirCycle_comap_iff e ℓ').mp hℓ')
    have hQcard : ℓ * (s - 1) * s + ℓ ≤ Q.card := by
      have := circlet_qKernel_card hℓ (by omega) (by omega) hq (qKernel_comap_map e hQ)
      rwa [card_image_equiv] at this
    have hn_eq : n = ℓ * s + ℓ * s * s * q := card_circletV ℓ s s q
    -- Bound `(ceilDiv ℓ' (q+1) : ℚ) / ℓ' ≤ 1 / (q+1) + 1 / ℓ`
    have hceil_le : (ceilDiv ℓ' (q + 1) : ℚ) ≤ ((ℓ' : ℚ) + (q : ℚ)) / ((q + 1 : ℕ) : ℚ) := by
      have hnat : ceilDiv ℓ' (q + 1) * (q + 1) ≤ ℓ' + q := by
        dsimp only [ceilDiv]
        have : ℓ' + (q + 1) - 1 = ℓ' + q := by omega
        rw [this]; exact Nat.div_mul_le_self _ _
      have hqpos : (0 : ℚ) < ((q + 1 : ℕ) : ℚ) := by positivity
      rw [le_div_iff₀ hqpos]
      exact_mod_cast hnat
    have hℓ'pos : (0 : ℚ) < (ℓ' : ℚ) := by
      have : 0 < ℓ' := by omega
      exact_mod_cast this
    have hℓpos : (0 : ℚ) < (ℓ : ℚ) := by positivity
    have hq1pos : (0 : ℚ) < ((q + 1 : ℕ) : ℚ) := by positivity
    have hrat_le : (ceilDiv ℓ' (q + 1) : ℚ) / (ℓ' : ℚ) ≤
        1 / ((q + 1 : ℕ) : ℚ) + 1 / (ℓ : ℚ) := by
      have h1 : (ceilDiv ℓ' (q + 1) : ℚ) / (ℓ' : ℚ) ≤
          ((ℓ' : ℚ) + (q : ℚ)) / ((q + 1 : ℕ) : ℚ) / (ℓ' : ℚ) :=
        div_le_div_of_nonneg_right hceil_le (le_of_lt hℓ'pos)
      have h2 : ((ℓ' : ℚ) + (q : ℚ)) / ((q + 1 : ℕ) : ℚ) / (ℓ' : ℚ) =
          1 / ((q + 1 : ℕ) : ℚ) + (q : ℚ) / (((q + 1 : ℕ) : ℚ) * (ℓ' : ℚ)) := by
        field_simp
      have h3 : (q : ℚ) / (((q + 1 : ℕ) : ℚ) * (ℓ' : ℚ)) ≤ 1 / (ℓ : ℚ) := by
        rw [div_le_div_iff₀ (mul_pos hq1pos hℓ'pos) hℓpos]
        have hℓ'_q : (ℓ : ℚ) ≤ (ℓ' : ℚ) := by exact_mod_cast hℓ'_ge
        have hq_lt : (q : ℚ) ≤ ((q + 1 : ℕ) : ℚ) := by push_cast; linarith
        nlinarith
      linarith
    have hmain_lt : (1 / ((q + 1 : ℕ) : ℚ) + 1 / (ℓ : ℚ)) * (n : ℚ) < ((ℓ * (s - 1) * s + ℓ : ℕ) : ℚ) := by
      have hn_q : (n : ℚ) = (ℓ : ℚ) * (s : ℚ) * (1 + (s : ℚ) * (q : ℚ)) := by
        rw [hn_eq]; push_cast; ring
      have hs1_q : ((s - 1 : ℕ) : ℚ) = (s : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; rfl
      rw [hn_q]
      have hq1_eq : ((q + 1 : ℕ) : ℚ) = (q : ℚ) + 1 := by push_cast; rfl
      rw [hq1_eq]
      have hℓq_q : (q : ℚ) * ((q : ℚ) + 1) + 1 ≤ (ℓ : ℚ) := by
        exact_mod_cast (show q * (q + 1) + 1 ≤ ℓ by omega)
      have hℓ1 : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast (by omega : 1 ≤ ℓ)
      have hq1 : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast (by omega : 1 ≤ q)
      have hs_eq : (s : ℚ) = 2 * (ℓ : ℚ) * ((q : ℚ) + 1) + 2 := by
        dsimp only [s]; push_cast; ring
      have hden : (0 : ℚ) < ((q : ℚ) + 1) * (ℓ : ℚ) := by positivity
      suffices ((ℓ : ℚ) + ((q : ℚ) + 1)) * ((ℓ : ℚ) * (s : ℚ) * (1 + (s : ℚ) * (q : ℚ))) <
          ((q : ℚ) + 1) * (ℓ : ℚ) * ((ℓ : ℚ) * ((s : ℚ) - 1) * (s : ℚ) + (ℓ : ℚ)) by
        have hrew : (1 / ((q : ℚ) + 1) + 1 / (ℓ : ℚ)) * ((ℓ : ℚ) * (s : ℚ) * (1 + (s : ℚ) * (q : ℚ))) =
            ((ℓ : ℚ) + ((q : ℚ) + 1)) * ((ℓ : ℚ) * (s : ℚ) * (1 + (s : ℚ) * (q : ℚ))) /
              (((q : ℚ) + 1) * (ℓ : ℚ)) := by field_simp
        rw [hrew, div_lt_iff₀ hden]
        have hcast : ((ℓ * (s - 1) * s + ℓ : ℕ) : ℚ) = (ℓ : ℚ) * ((s : ℚ) - 1) * (s : ℚ) + (ℓ : ℚ) := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hs1_q]
        rw [hcast]
        linarith [show ((ℓ : ℚ) * ((s : ℚ) - 1) * (s : ℚ) + (ℓ : ℚ)) * (((q : ℚ) + 1) * (ℓ : ℚ)) =
            ((q : ℚ) + 1) * (ℓ : ℚ) * ((ℓ : ℚ) * ((s : ℚ) - 1) * (s : ℚ) + (ℓ : ℚ)) by ring]
      have hdiff_ge : (1 : ℚ) ≤ (ℓ : ℚ) - (q : ℚ) * ((q : ℚ) + 1) := by linarith
      have hstep1 : (ℓ : ℚ) * ((q : ℚ) + 1) + (ℓ : ℚ) + ((q : ℚ) + 1) <
          ((ℓ : ℚ) - (q : ℚ) * ((q : ℚ) + 1)) * (s : ℚ) := by
        rw [hs_eq]; nlinarith
      have hpoly : ((q : ℚ) + 1) * (ℓ : ℚ) * ((ℓ : ℚ) * ((s : ℚ) - 1) * (s : ℚ) + (ℓ : ℚ)) -
          ((ℓ : ℚ) + ((q : ℚ) + 1)) * ((ℓ : ℚ) * (s : ℚ) * (1 + (s : ℚ) * (q : ℚ))) =
          (ℓ : ℚ) * ((((ℓ : ℚ) - (q : ℚ) * ((q : ℚ) + 1)) * (s : ℚ) -
            ((ℓ : ℚ) * ((q : ℚ) + 1) + (ℓ : ℚ) + ((q : ℚ) + 1))) * (s : ℚ) + ((q : ℚ) + 1) * (ℓ : ℚ)) := by
        ring
      have hspos : (0 : ℚ) < (s : ℚ) := by positivity
      have hpos_rhs : 0 < (((ℓ : ℚ) - (q : ℚ) * ((q : ℚ) + 1)) * (s : ℚ) -
          ((ℓ : ℚ) * ((q : ℚ) + 1) + (ℓ : ℚ) + ((q : ℚ) + 1))) * (s : ℚ) + ((q : ℚ) + 1) * (ℓ : ℚ) := by
        nlinarith
      have hpos_prod := mul_pos hℓpos hpos_rhs
      linarith
    have hQcard_q : ((ℓ * (s - 1) * s + ℓ : ℕ) : ℚ) ≤ (Q.card : ℚ) := by exact_mod_cast hQcard
    have hn_nonneg : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
    calc ((ceilDiv ℓ' (q + 1) : ℚ) / (ℓ' : ℚ)) * (n : ℚ)
        ≤ (1 / ((q + 1 : ℕ) : ℚ) + 1 / (ℓ : ℚ)) * (n : ℚ) :=
          mul_le_mul_of_nonneg_right hrat_le hn_nonneg
      _ < ((ℓ * (s - 1) * s + ℓ : ℕ) : ℚ) := hmain_lt
      _ ≤ (Q.card : ℚ) := hQcard_q

private lemma theorem_1_3 :
    ∀ q ℓ : ℕ, 2 ≤ q → 2 ≤ ℓ → ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (D : FinDigraph (Fin n)),
        0 < n ∧ IsStronglyConnected D ∧ DirectedGirth D ℓ ∧
        ∀ Q : Finset (Fin n), IsQKernel D q Q →
          1 / (q : ℝ) - ε < (Q.card : ℝ) / (n : ℝ) := by
  intro q ℓ hq hℓ ε hε
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  obtain ⟨s0, hs0⟩ := exists_nat_gt (((q : ℝ) + 1) / (ε * (q : ℝ)))
  let s : ℕ := max s0 2
  have hs2 : 2 ≤ s := le_max_right _ _
  have hs_gt : ((q : ℝ) + 1) / (ε * (q : ℝ)) < (s : ℝ) :=
    lt_of_lt_of_le hs0 (by exact_mod_cast le_max_left s0 2)
  let D0 := circletDigraph ℓ s s q hℓ (by omega) hq
  let n := Fintype.card (CircletV ℓ s s q)
  let e : Fin n ≃ CircletV ℓ s s q := (Fintype.equivFin (CircletV ℓ s s q)).symm
  refine ⟨n, comapDigraph D0 e, ?_, stronglyConnected_comap e (circlet_stronglyConnected hℓ (by omega) hq),
    (directedGirth_comap_iff e ℓ).mpr (circlet_directedGirth hℓ (by omega) hq), ?_⟩
  · dsimp only [n]; rw [card_circletV]; positivity
  · intro Q hQ
    have hQcard : ℓ * (s - 1) * s + ℓ ≤ Q.card := by
      have := circlet_qKernel_card hℓ (by omega) (by omega) hq (qKernel_comap_map e hQ)
      rwa [card_image_equiv] at this
    have hn_eq : n = ℓ * s + ℓ * s * s * q := card_circletV ℓ s s q
    have hn_pos : (0 : ℝ) < (n : ℝ) := by rw [hn_eq]; positivity
    have hQ_r : ((ℓ * (s - 1) * s + ℓ : ℕ) : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hQcard
    have hs1_r : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; rfl
    have hQ_r' : (ℓ : ℝ) * (((s : ℝ) - 1) * (s : ℝ) + 1) ≤ (Q.card : ℝ) := by
      have : ((ℓ * (s - 1) * s + ℓ : ℕ) : ℝ) = (ℓ : ℝ) * (((s : ℝ) - 1) * (s : ℝ) + 1) := by
        push_cast; rw [hs1_r]; ring
      linarith
    have hn_r : (n : ℝ) = (ℓ : ℝ) * ((s : ℝ) * (1 + (s : ℝ) * (q : ℝ))) := by
      rw [hn_eq]; push_cast; ring
    have hεsq : (q : ℝ) + 1 < ε * (q : ℝ) * (s : ℝ) := by
      have h := (div_lt_iff₀ (mul_pos hε hqpos)).mp hs_gt
      linarith
    have hlt_num : (1 / (q : ℝ) - ε) * ((s : ℝ) * (1 + (s : ℝ) * (q : ℝ))) <
        ((s : ℝ) - 1) * (s : ℝ) + 1 := by
      have hdiff : ((s : ℝ) - 1) * (s : ℝ) + 1 -
          (1 / (q : ℝ) - ε) * ((s : ℝ) * (1 + (s : ℝ) * (q : ℝ))) =
          (s : ℝ) * (ε * (s : ℝ) * (q : ℝ) - 1 - 1 / (q : ℝ) + ε) + 1 := by
        field_simp; ring
      have h1 : 1 + 1 / (q : ℝ) < ε * (s : ℝ) * (q : ℝ) := by
        have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
        have := (div_lt_iff₀ hqpos).mpr (show (q : ℝ) + 1 < ε * (s : ℝ) * (q : ℝ) * (q : ℝ) by nlinarith)
        have hrew : ((q : ℝ) + 1) / (q : ℝ) = 1 + 1 / (q : ℝ) := by field_simp
        linarith
      have hspos : (0 : ℝ) < (s : ℝ) := by positivity
      nlinarith
    have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by positivity
    rw [lt_div_iff₀ hn_pos, hn_r]
    calc (1 / (q : ℝ) - ε) * ((ℓ : ℝ) * ((s : ℝ) * (1 + (s : ℝ) * (q : ℝ))))
        = (ℓ : ℝ) * ((1 / (q : ℝ) - ε) * ((s : ℝ) * (1 + (s : ℝ) * (q : ℝ)))) := by ring
      _ < (ℓ : ℝ) * (((s : ℝ) - 1) * (s : ℝ) + 1) := mul_lt_mul_of_pos_left hlt_num hℓpos
      _ ≤ (Q.card : ℝ) := hQ_r'

/-! ### Part 2: Theorem 1.6 (Bipartite + out-branching + odd `q ≥ 3`) -/

private lemma theorem_1_6 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (D : FinDigraph V) (q : ℕ),
      3 ≤ q → Odd q → IsSourceFree D → IsBipartite D → HasOutBranching D →
      ∃ Q : Finset V, IsQKernel D q Q ∧
        (Q.card : ℚ) ≤ (Fintype.card V : ℚ) / ((q + 1 : ℕ) : ℚ) + 1 := by
  classical
  intro V _ _ D q hq3 hqOdd hsf ⟨c, hc⟩ ⟨r, parent, hpar, hreach⟩
  let depth (v : V) : ℕ := Nat.find (hreach v)
  have hdepth_spec : ∀ v : V, parent^[depth v] v = r := fun v => Nat.find_spec (hreach v)
  have hdepth_min : ∀ (v : V) (k : ℕ), parent^[k] v = r → depth v ≤ k := fun v _ hk => Nat.find_min' (hreach v) hk
  have hdepth_r : depth r = 0 := Nat.eq_zero_of_le_zero (hdepth_min r 0 rfl)
  have hdepth_pos : ∀ v : V, v ≠ r → 0 < depth v := fun v hv => by
    by_contra h0
    have hd0 : depth v = 0 := by omega
    have := hdepth_spec v
    rw [hd0] at this; exact hv this
  have hdepth_par : ∀ v : V, v ≠ r → depth v = depth (parent v) + 1 := by
    intro v hv
    have hp := hdepth_pos v hv
    have h1 : parent^[depth v - 1] (parent v) = r := by
      have := hdepth_spec v
      rw [← Nat.sub_add_cancel hp, Function.iterate_succ_apply] at this
      exact this
    have hle1 : depth (parent v) ≤ depth v - 1 := hdepth_min (parent v) (depth v - 1) h1
    have h2 : parent^[depth (parent v) + 1] v = r := by
      rw [Function.iterate_succ_apply]; exact hdepth_spec (parent v)
    have hle2 : depth v ≤ depth (parent v) + 1 := hdepth_min v (depth (parent v) + 1) h2
    omega
  have hiter_depth : ∀ (k : ℕ) (v : V), k ≤ depth v →
      depth (parent^[k] v) + k = depth v ∧ ReachIn D k (parent^[k] v) v := by
    intro k
    induction k with
    | zero => intro v _; exact ⟨by simp, ReachIn.zero v⟩
    | succ k ih =>
      intro v hkv
      have hvr : v ≠ r := by intro h; subst h; rw [hdepth_r] at hkv; omega
      have hdp := hdepth_par v hvr
      obtain ⟨hd, hreach_k⟩ := ih (parent v) (by omega)
      rw [Function.iterate_succ_apply]
      refine ⟨by omega, reachIn_trans hreach_k (reachIn_one (hpar v hvr))⟩
  have hcolor_depth : ∀ (d : ℕ) (v : V), depth v = d →
      c v = if d % 2 = 0 then c r else !(c r) := by
    intro d
    induction d with
    | zero =>
      intro v hv
      have hvr : v = r := by have := hdepth_spec v; rwa [hv] at this
      subst hvr; simp
    | succ d ih =>
      intro v hv
      have hvr : v ≠ r := by intro h; subst h; rw [hdepth_r] at hv; omega
      have hdp := hdepth_par v hvr
      have hcp := ih (parent v) (by omega)
      have hne : c (parent v) ≠ c v := hc (parent v) v (hpar v hvr)
      cases hcr : c r <;> cases hcv : c v <;> by_cases hd2 : d % 2 = 0
      all_goals
        first
        | simp_all [show (d + 1) % 2 = 1 by omega]
        | simp_all [show (d + 1) % 2 = 0 by omega]
  -- Partition `V` by `depth v % (q + 1)`
  let cls (s : Fin (q + 1)) : Finset V := Finset.univ.filter fun v => depth v % (q + 1) = s.val
  have hsum_cls : ∑ s : Fin (q + 1), (cls s).card = Fintype.card V := by
    rw [← Finset.card_biUnion]
    · have huniv : Finset.univ.biUnion cls = Finset.univ := by
        ext v; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, cls, Finset.mem_filter, iff_true]
        exact ⟨⟨depth v % (q + 1), Nat.mod_lt _ (by omega)⟩, rfl⟩
      rw [huniv, Finset.card_univ]
    · intro s₁ _ s₂ _ hne
      change Disjoint (cls s₁) (cls s₂)
      rw [Finset.disjoint_left]
      intro v h1 h2
      exact hne (Fin.ext (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2))
  -- Pigeonhole: pick `s` with `(q + 1) * (cls s).card ≤ Fintype.card V`
  have hex_s : ∃ s : Fin (q + 1), (q + 1) * (cls s).card ≤ Fintype.card V := by
    by_contra hall
    push Not at hall
    have h1 : ∑ _s : Fin (q + 1), Fintype.card V < ∑ s : Fin (q + 1), (q + 1) * (cls s).card :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩) (fun s _ => hall s)
    rw [← Finset.mul_sum, hsum_cls, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    omega
  obtain ⟨s, hs_card⟩ := hex_s
  have hcls_color : ∀ v ∈ cls s, c v = if s.val % 2 = 0 then c r else !(c r) := by
    intro v hv
    have hmod : depth v % (q + 1) = s.val := (Finset.mem_filter.mp hv).2
    have hmod2 : depth v % 2 = s.val % 2 := by
      rcases hqOdd with ⟨m, rfl⟩
      have hdiv := Nat.div_add_mod (depth v) (2 * m + 1 + 1)
      have hlin : depth v = 2 * ((m + 1) * (depth v / (2 * m + 1 + 1))) + s.val := by linarith
      omega
    rw [hcolor_depth (depth v) v rfl, hmod2]
  have hcard_bound : ∀ Q : Finset V, Q.card ≤ (cls s).card + 1 →
      (Q.card : ℚ) ≤ (Fintype.card V : ℚ) / ((q + 1 : ℕ) : ℚ) + 1 := by
    intro Q hQle
    have hq1pos : (0 : ℚ) < ((q + 1 : ℕ) : ℚ) := by positivity
    have h1 : ((cls s).card : ℚ) ≤ (Fintype.card V : ℚ) / ((q + 1 : ℕ) : ℚ) := by
      rw [le_div_iff₀ hq1pos]
      have : ((cls s).card : ℚ) * ((q + 1 : ℕ) : ℚ) = (((q + 1) * (cls s).card : ℕ) : ℚ) := by
        push_cast; ring
      rw [this]; exact_mod_cast hs_card
    have h2 : (Q.card : ℚ) ≤ ((cls s).card : ℚ) + 1 := by exact_mod_cast hQle
    linarith
  -- Helper: any `v` with `s.val ≤ depth v` is reached from `cls s` in `≤ q` steps
  have hreach_ge : ∀ v : V, s.val ≤ depth v → ∃ u ∈ cls s, ∃ k ≤ q, ReachIn D k u v := by
    intro v hv
    let k := (depth v - s.val) % (q + 1)
    have hk_le_q : k ≤ q := by have := Nat.mod_lt (depth v - s.val) (by omega : 0 < q + 1); omega
    have hk_le_d : k ≤ depth v := by
      have := Nat.mod_le (depth v - s.val) (q + 1); omega
    obtain ⟨hd_u, hreach_u⟩ := hiter_depth k v hk_le_d
    refine ⟨parent^[k] v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, k, hk_le_q, hreach_u⟩
    have hdiv := Nat.div_add_mod (depth v - s.val) (q + 1)
    have hdu_eq : depth (parent^[k] v) = s.val + (q + 1) * ((depth v - s.val) / (q + 1)) := by omega
    rw [hdu_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.isLt]
  by_cases hs2 : s.val % 2 = 0
  · refine ⟨insert r (cls s), ⟨?_, ?_⟩, hcard_bound _ (Finset.card_insert_le _ _)⟩
    · intro u hu v hv hadj
      have hcu : c u = c r := by
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · rfl
        · simpa [hs2] using hcls_color u hu'
      have hcv : c v = c r := by
        rcases Finset.mem_insert.mp hv with rfl | hv'
        · rfl
        · simpa [hs2] using hcls_color v hv'
      exact hc u v hadj (hcu.trans hcv.symm)
    · intro v
      by_cases hdv : depth v < s.val
      · refine ⟨r, Finset.mem_insert_self _ _, depth v, by omega, ?_⟩
        have h := (hiter_depth (depth v) v (le_refl _)).2
        rwa [hdepth_spec v] at h
      · obtain ⟨u, hu, k, hk, hr⟩ := hreach_ge v (by omega)
        exact ⟨u, Finset.mem_insert_of_mem hu, k, hk, hr⟩
  · obtain ⟨y, hyr⟩ := hsf r
    have hcy : c y = !(c r) := by
      have := hc y r hyr; cases hcr : c r <;> cases hcy' : c y <;> simp_all
    refine ⟨insert y (cls s), ⟨?_, ?_⟩, hcard_bound _ (Finset.card_insert_le _ _)⟩
    · intro u hu v hv hadj
      have hcu : c u = !(c r) := by
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact hcy
        · simpa [hs2] using hcls_color u hu'
      have hcv : c v = !(c r) := by
        rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact hcy
        · simpa [hs2] using hcls_color v hv'
      exact hc u v hadj (hcu.trans hcv.symm)
    · intro v
      by_cases hdv : depth v < s.val
      · refine ⟨y, Finset.mem_insert_self _ _, depth v + 1, by omega, ?_⟩
        have h := (hiter_depth (depth v) v (le_refl _)).2
        rw [hdepth_spec v] at h
        exact ReachIn.succ hyr h
      · obtain ⟨u, hu, k, hk, hr⟩ := hreach_ge v (by omega)
        exact ⟨u, Finset.mem_insert_of_mem hu, k, hk, hr⟩

/-! ### Part 3: Theorem 1.7 (Bipartite + even `q ≥ 2`, `D_{q,r}`) -/

private abbrev DqV (q : ℕ) := (Fin 2 × Fin (2 * (q + 1))) ⊕ Fin q
private abbrev DqrV (q r : ℕ) := (Fin r × DqV q) ⊕ Unit

private def dqAdj (q : ℕ) (_hq : 2 ≤ q) : DqV q → DqV q → Prop
  | Sum.inl (b₁, k₁), Sum.inl (b₂, k₂) =>
      (b₁ = b₂ ∧ k₂.val = (k₁.val + 1) % (2 * (q + 1))) ∨
      (b₁ = 0 ∧ b₂ = 1 ∧ k₁.val % 2 = 1 ∧ k₂.val = 0)
  | Sum.inl (b₁, k₁), Sum.inr m₂ =>
      b₁ = 1 ∧ k₁.val = 0 ∧ m₂.val = 0
  | Sum.inr m₁, Sum.inr m₂ =>
      m₂.val = m₁.val + 1
  | Sum.inr _, Sum.inl _ => False

private def dqrAdj (q r : ℕ) (_hq : 2 ≤ q) : DqrV q r → DqrV q r → Prop
  | Sum.inl (i₁, v₁), Sum.inl (i₂, v₂) => i₁ = i₂ ∧ dqAdj q _hq v₁ v₂
  | Sum.inl (_, Sum.inr m₁), Sum.inr () => m₁.val + 1 = q
  | _, _ => False

private def dqrDigraph (q r : ℕ) (_hq : 2 ≤ q) : FinDigraph (DqrV q r) where
  adj := dqrAdj q r _hq
  loopless := by
    intro v h
    rcases v with ⟨i, ⟨b, k⟩ | m⟩ | ⟨⟩
    · rcases h with ⟨_, ⟨_, hk⟩ | ⟨h0, h1, _, _⟩⟩
      · by_cases hlt : k.val + 1 < 2 * (q + 1)
        · rw [Nat.mod_eq_of_lt hlt] at hk; omega
        · have heq : k.val + 1 = 2 * (q + 1) := by omega
          rw [heq, Nat.mod_self] at hk; omega
      · rw [h0] at h1; exact absurd h1 (by decide)
    · rcases h with ⟨_, hm⟩; dsimp only [dqAdj] at hm; omega
    · exact h

private lemma dqr_bipartite {q r : ℕ} (hq : 2 ≤ q) (hqEven : Even q) :
    IsBipartite (dqrDigraph q r hq) := by
  let col : DqrV q r → Bool
    | Sum.inl (_, Sum.inl (_, k)) => decide (k.val % 2 = 1)
    | Sum.inl (_, Sum.inr m) => decide ((m.val + 1) % 2 = 1)
    | Sum.inr () => true
  refine ⟨col, fun u v hadj => ?_⟩
  rcases u with ⟨i₁, ⟨b₁, k₁⟩ | m₁⟩ | ⟨⟩ <;> rcases v with ⟨i₂, ⟨b₂, k₂⟩ | m₂⟩ | ⟨⟩
  · rcases hadj with ⟨_, ⟨_, hk⟩ | ⟨_, _, hodd, hk0⟩⟩
    · simp only [col, hk]
      have hmod : ((k₁.val + 1) % (2 * (q + 1))) % 2 = (k₁.val + 1) % 2 := by
        have hdiv := Nat.div_add_mod (k₁.val + 1) (2 * (q + 1))
        have hlin : k₁.val + 1 = 2 * ((q + 1) * ((k₁.val + 1) / (2 * (q + 1)))) + (k₁.val + 1) % (2 * (q + 1)) := by
          linarith
        omega
      rw [hmod]
      by_cases h1 : k₁.val % 2 = 1
      · simp [h1, show (k₁.val + 1) % 2 = 0 by omega]
      · simp [h1, show (k₁.val + 1) % 2 = 1 by omega]
    · simp [col, hodd, hk0]
  · rcases hadj with ⟨_, _, hk0, hm0⟩
    simp [col, hk0, hm0]
  · exact False.elim hadj
  · exact False.elim hadj.2
  · rcases hadj with ⟨_, hm⟩
    dsimp only [dqAdj] at hm
    simp only [col, hm]
    by_cases h1 : (m₁.val + 1) % 2 = 1
    · simp [h1, show (m₁.val + 1 + 1) % 2 = 0 by omega]
    · simp [h1, show (m₁.val + 1 + 1) % 2 = 1 by omega]
  · simp only [col]
    have hm : m₁.val + 1 = q := hadj
    rcases hqEven with ⟨t, rfl⟩
    simp [hm, show (t + t) % 2 = 0 by omega]
  · exact False.elim hadj
  · exact False.elim hadj
  · exact False.elim hadj

private lemma dqr_sourceFree {q r : ℕ} (hq : 2 ≤ q) (hr : 2 ≤ r) :
    IsSourceFree (dqrDigraph q r hq) := by
  intro v
  rcases v with ⟨i, ⟨b, k⟩ | m⟩ | ⟨⟩
  · let prev : Fin (2 * (q + 1)) :=
      if hk : k.val = 0 then ⟨2 * (q + 1) - 1, by omega⟩ else ⟨k.val - 1, by omega⟩
    refine ⟨Sum.inl (i, Sum.inl (b, prev)), rfl, Or.inl ⟨rfl, ?_⟩⟩
    dsimp only [prev]
    split_ifs with hk
    · rw [hk, show 2 * (q + 1) - 1 + 1 = 2 * (q + 1) by omega, Nat.mod_self]
    · rw [show k.val - 1 + 1 = k.val by omega, Nat.mod_eq_of_lt k.isLt]
  · by_cases hm : m.val = 0
    · exact ⟨Sum.inl (i, Sum.inl (1, ⟨0, by omega⟩)), rfl, rfl, rfl, hm⟩
    · exact ⟨Sum.inl (i, Sum.inr ⟨m.val - 1, by omega⟩), rfl, by show m.val = m.val - 1 + 1; omega⟩
  · exact ⟨Sum.inl (⟨0, by omega⟩, Sum.inr ⟨q - 1, by omega⟩), by show q - 1 + 1 = q; omega⟩

private lemma dqr_weaklyConnected {q r : ℕ} (hq : 2 ≤ q) (_hr : 2 ≤ r) :
    IsWeaklyConnected (dqrDigraph q r hq) := by
  let R := fun x y : DqrV q r => (dqrDigraph q r hq).adj x y ∨ (dqrDigraph q r hq).adj y x
  have hto_z : ∀ v : DqrV q r, Relation.ReflTransGen R v (Sum.inr ()) := by
    intro v
    rcases v with ⟨i, ⟨b, k⟩ | m⟩ | ⟨⟩
    · -- First reach `(i, inl (1, 0))`, then `inr 0`, ..., `inr (q-1)`, then `z`
      have hy_to_z : ∀ (d : ℕ) (m : ℕ) (hm : m < q), m + d = q - 1 →
          Relation.ReflTransGen R (Sum.inl (i, Sum.inr ⟨m, hm⟩)) (Sum.inr ()) := by
        intro d
        induction d with
        | zero =>
          intro m hm hsum
          exact Relation.ReflTransGen.single (Or.inl (by show m + 1 = q; omega))
        | succ d ih =>
          intro m hm hsum
          exact Relation.ReflTransGen.head (b := Sum.inl (i, Sum.inr ⟨m + 1, by omega⟩))
            (Or.inl ⟨rfl, by rfl⟩) (ih (m + 1) (by omega) (by omega))
      have hc20_to_z : Relation.ReflTransGen R (Sum.inl (i, Sum.inl (1, ⟨0, by omega⟩))) (Sum.inr ()) :=
        Relation.ReflTransGen.head (b := Sum.inl (i, Sum.inr ⟨0, by omega⟩))
          (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (hy_to_z (q - 1) 0 (by omega) (by omega))
      have hcyc : ∀ (b' : Fin 2) (k₁ : ℕ) (hk₁ : k₁ < 2 * (q + 1)),
          Relation.ReflTransGen R (Sum.inl (i, Sum.inl (b', ⟨k₁, hk₁⟩))) (Sum.inl (i, Sum.inl (b', ⟨0, by omega⟩))) := by
        intro b' k₁
        induction k₁ with
        | zero => intro _; exact Relation.ReflTransGen.refl
        | succ k₁ ih =>
          intro hk₁
          have hadj : (dqrDigraph q r hq).adj (Sum.inl (i, Sum.inl (b', ⟨k₁, by omega⟩)))
              (Sum.inl (i, Sum.inl (b', ⟨k₁ + 1, hk₁⟩))) :=
            ⟨rfl, Or.inl ⟨rfl, (Nat.mod_eq_of_lt hk₁).symm⟩⟩
          exact Relation.ReflTransGen.head (Or.inr hadj) (ih (by omega))
      fin_cases b
      · have h0_1 : Relation.ReflTransGen R (Sum.inl (i, Sum.inl (0, ⟨0, by omega⟩)))
            (Sum.inl (i, Sum.inl (0, ⟨1, by omega⟩))) :=
          Relation.ReflTransGen.single (Or.inl ⟨rfl, Or.inl ⟨rfl, (Nat.mod_eq_of_lt (by omega)).symm⟩⟩)
        have h1_c20 : Relation.ReflTransGen R (Sum.inl (i, Sum.inl (0, ⟨1, by omega⟩)))
            (Sum.inl (i, Sum.inl (1, ⟨0, by omega⟩))) :=
          Relation.ReflTransGen.single (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩)
        exact (hcyc 0 k.val k.isLt).trans (h0_1.trans (h1_c20.trans hc20_to_z))
      · exact (hcyc 1 k.val k.isLt).trans hc20_to_z
    · have hy_to_z : ∀ (d : ℕ) (m' : ℕ) (hm' : m' < q), m' + d = q - 1 →
          Relation.ReflTransGen R (Sum.inl (i, Sum.inr ⟨m', hm'⟩)) (Sum.inr ()) := by
        intro d
        induction d with
        | zero => intro m' hm' hsum; exact Relation.ReflTransGen.single (Or.inl (by show m' + 1 = q; omega))
        | succ d ih =>
          intro m' hm' hsum
          exact Relation.ReflTransGen.head (b := Sum.inl (i, Sum.inr ⟨m' + 1, by omega⟩))
            (Or.inl ⟨rfl, by rfl⟩) (ih (m' + 1) (by omega) (by omega))
      exact hy_to_z (q - 1 - m.val) m.val m.isLt (by omega)
    · exact Relation.ReflTransGen.refl
  have hsymm : ∀ a b, Relation.ReflTransGen R a b → Relation.ReflTransGen R b a := fun a b h => by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.head (Or.symm hstep) ih
  intro u v
  exact (hto_z u).trans (hsymm v (Sum.inr ()) (hto_z v))

private def dqrLayer {q r : ℕ} : DqrV q r → ℕ
  | Sum.inl (_, Sum.inl (b, _)) => b.val
  | Sum.inl (_, Sum.inr _) => 2
  | Sum.inr () => 3

private lemma dqr_cycles_iff {q r : ℕ} (hq : 2 ≤ q) (hr : 2 ≤ r) (ℓ' : ℕ) :
    HasDirCycle (dqrDigraph q r hq) ℓ' ↔ ℓ' = 2 * (q + 1) := by
  let D := dqrDigraph q r hq
  constructor
  · rintro ⟨hℓ'2, f, hinj, hadj⟩
    -- `dqrLayer` is nondecreasing along arcs, so constant on any cycle!
    have hlayer_mono : ∀ u v, D.adj u v → dqrLayer u ≤ dqrLayer v := by
      intro u v h
      rcases u with ⟨i₁, ⟨b₁, k₁⟩ | m₁⟩ | ⟨⟩ <;> rcases v with ⟨i₂, ⟨b₂, k₂⟩ | m₂⟩ | ⟨⟩
      · rcases h with ⟨_, ⟨rfl, _⟩ | ⟨rfl, rfl, _, _⟩⟩ <;> simp [dqrLayer]
      · simp [dqrLayer]
      · exact False.elim h
      · exact False.elim h.2
      · simp [dqrLayer]
      · simp [dqrLayer]
      · exact False.elim h
      · exact False.elim h
      · exact False.elim h
    have hlayer_const : ∀ i : Fin ℓ', dqrLayer (f i) = dqrLayer (f ⟨0, by omega⟩) := by
      have hmono_m : ∀ m : ℕ, m ≤ ℓ' → dqrLayer (f ⟨0, by omega⟩) ≤ dqrLayer (f ⟨m % ℓ', Nat.mod_lt _ (by omega)⟩) := by
        intro m _
        induction m with
        | zero => simp
        | succ m ih =>
          have hstep := hlayer_mono _ _ (hadj ⟨m % ℓ', Nat.mod_lt _ (by omega)⟩)
          have hmod : (m % ℓ' + 1) % ℓ' = (m + 1) % ℓ' := by rw [Nat.mod_add_mod]
          have : dqrLayer (f ⟨(m % ℓ' + 1) % ℓ', Nat.mod_lt _ (by omega)⟩) =
              dqrLayer (f ⟨(m + 1) % ℓ', Nat.mod_lt _ (by omega)⟩) := by
            congr 2; exact Fin.ext hmod
          dsimp only at hstep; omega
      intro i
      have h1 : dqrLayer (f ⟨0, by omega⟩) ≤ dqrLayer (f i) := by
        simpa [Nat.mod_eq_of_lt i.isLt] using hmono_m i.val (le_of_lt i.isLt)
      have h2 : ∀ d : ℕ, d ≤ ℓ' → dqrLayer (f i) ≤ dqrLayer (f ⟨(i.val + d) % ℓ', Nat.mod_lt _ (by omega)⟩) := by
        intro d _
        induction d with
        | zero => simp [Nat.mod_eq_of_lt i.isLt]
        | succ d ih =>
          have hstep := hlayer_mono _ _ (hadj ⟨(i.val + d) % ℓ', Nat.mod_lt _ (by omega)⟩)
          have hmod : ((i.val + d) % ℓ' + 1) % ℓ' = (i.val + (d + 1)) % ℓ' := by
            rw [Nat.mod_add_mod, Nat.add_assoc]
          have : dqrLayer (f ⟨((i.val + d) % ℓ' + 1) % ℓ', Nat.mod_lt _ (by omega)⟩) =
              dqrLayer (f ⟨(i.val + (d + 1)) % ℓ', Nat.mod_lt _ (by omega)⟩) := by
            congr 2; exact Fin.ext hmod
          dsimp only at hstep; omega
      have h3 := h2 (ℓ' - i.val) (by omega)
      have hmod0 : (i.val + (ℓ' - i.val)) % ℓ' = 0 := by
        rw [Nat.add_sub_of_le (le_of_lt i.isLt), Nat.mod_self]
      have : dqrLayer (f ⟨(i.val + (ℓ' - i.val)) % ℓ', Nat.mod_lt _ (by omega)⟩) = dqrLayer (f ⟨0, by omega⟩) := by
        congr 2; exact Fin.ext hmod0
      omega
    -- Inspect `f 0`: it cannot be `inr ()` (no out-edges) or `inl (_, inr m)` (strictly increasing `m`)!
    rcases h0 : f ⟨0, by omega⟩ with ⟨i0, ⟨b0, k0⟩ | m0⟩ | ⟨⟩
    · -- All `f i` have same `(i0, b0)` and step `k ↦ (k + 1) % (2*(q+1))`!
      have hform : ∀ t : ℕ, t ≤ ℓ' →
          f ⟨t % ℓ', Nat.mod_lt _ (by omega)⟩ =
            Sum.inl (i0, Sum.inl (b0, ⟨(k0.val + t) % (2 * (q + 1)), Nat.mod_lt _ (by omega)⟩)) := by
        intro t ht
        induction t with
        | zero =>
          simp only [Nat.zero_mod, add_zero, Nat.mod_eq_of_lt k0.isLt]
          exact h0
        | succ t ih =>
          have hlt : t < ℓ' := by omega
          have hprev := ih (by omega)
          have hfeq : (⟨t % ℓ', Nat.mod_lt _ (by omega)⟩ : Fin ℓ') = ⟨t, hlt⟩ := Fin.ext (Nat.mod_eq_of_lt hlt)
          rw [hfeq] at hprev
          have hstep := hadj ⟨t, hlt⟩
          rw [hprev] at hstep
          have hlay := hlayer_const ⟨(t + 1) % ℓ', Nat.mod_lt _ (by omega)⟩
          rw [h0] at hlay
          rcases hv : f ⟨(t + 1) % ℓ', Nat.mod_lt _ (by omega)⟩ with ⟨i', ⟨b', k'⟩ | m'⟩ | ⟨⟩
          · rw [hv] at hstep hlay
            simp only [dqrLayer] at hlay
            have hb' : b' = b0 := Fin.ext hlay
            subst hb'
            rcases hstep with ⟨rfl, ⟨_, hk'⟩ | ⟨hb0, hb1, _, _⟩⟩
            · congr 4; apply Fin.ext
              rw [hk', Nat.mod_add_mod, Nat.add_assoc]
            · rw [hb0] at hb1; exact absurd hb1 (by decide)
          · rw [hv] at hlay; simp [dqrLayer] at hlay; omega
          · rw [hv] at hlay; simp [dqrLayer] at hlay; omega
      have hwrap := hform ℓ' (le_refl ℓ')
      have hfin0 : (⟨ℓ' % ℓ', Nat.mod_lt _ (by omega)⟩ : Fin ℓ') = ⟨0, by omega⟩ := Fin.ext (Nat.mod_self ℓ')
      rw [hfin0, h0] at hwrap
      injection hwrap with h1; injection h1 with _ h2; injection h2 with h3
      have hmod := congrArg (fun x : Fin 2 × Fin (2 * (q + 1)) => x.2.val) h3
      dsimp only at hmod
      have hdiv : 2 * (q + 1) ∣ ℓ' := by
        have hEq : k0.val + 0 ≡ k0.val + ℓ' [MOD 2 * (q + 1)] := by
          change (k0.val + 0) % (2 * (q + 1)) = (k0.val + ℓ') % (2 * (q + 1))
          rw [add_zero, Nat.mod_eq_of_lt k0.isLt]; exact hmod
        have h0' : 0 ≡ ℓ' [MOD 2 * (q + 1)] := Nat.ModEq.add_left_cancel' k0.val hEq
        exact Nat.dvd_of_mod_eq_zero h0'.symm
      have hge : 2 * (q + 1) ≤ ℓ' := Nat.le_of_dvd (by omega) hdiv
      by_cases heq : ℓ' = 2 * (q + 1)
      · exact heq
      · exfalso
        have hlt : 2 * (q + 1) < ℓ' := by omega
        have hfa := hform (2 * (q + 1)) (le_of_lt hlt)
        have hfin_a : (⟨(2 * (q + 1)) % ℓ', Nat.mod_lt _ (by omega)⟩ : Fin ℓ') = ⟨2 * (q + 1), hlt⟩ :=
          Fin.ext (Nat.mod_eq_of_lt hlt)
        have hk_eq : (⟨(k0.val + 2 * (q + 1)) % (2 * (q + 1)), Nat.mod_lt _ (by omega)⟩ : Fin (2 * (q + 1))) = k0 := by
          apply Fin.ext; dsimp only; rw [Nat.add_mod_right, Nat.mod_eq_of_lt k0.isLt]
        rw [hfin_a, hk_eq] at hfa
        have hfin : (⟨2 * (q + 1), hlt⟩ : Fin ℓ') = ⟨0, by omega⟩ := hinj (hfa.trans h0.symm)
        have := congrArg Fin.val hfin; dsimp only at this; omega
    · exfalso
      -- In layer 2 (`inr m`), every arc strictly increases `m`!
      have hinc : ∀ t : ℕ, t ≤ ℓ' → ∃ i' m', f ⟨t % ℓ', Nat.mod_lt _ (by omega)⟩ = Sum.inl (i', Sum.inr m') ∧
          m0.val + t = m'.val := by
        intro t ht
        induction t with
        | zero => exact ⟨i0, m0, by simpa using h0, by simp⟩
        | succ t ih =>
          have hlt : t < ℓ' := by omega
          obtain ⟨i', m', hft, hm⟩ := ih (by omega)
          have hfeq : (⟨t % ℓ', Nat.mod_lt _ (by omega)⟩ : Fin ℓ') = ⟨t, hlt⟩ := Fin.ext (Nat.mod_eq_of_lt hlt)
          rw [hfeq] at hft
          have hstep := hadj ⟨t, hlt⟩
          rw [hft] at hstep
          have hlay := hlayer_const ⟨(t + 1) % ℓ', Nat.mod_lt _ (by omega)⟩
          rw [h0] at hlay
          rcases hv : f ⟨(t + 1) % ℓ', Nat.mod_lt _ (by omega)⟩ with ⟨i'', ⟨b'', k''⟩ | m''⟩ | ⟨⟩
          · rw [hv] at hlay; simp [dqrLayer] at hlay; omega
          · rw [hv] at hstep; rcases hstep with ⟨rfl, hm''⟩
            exact ⟨i', m'', rfl, by dsimp only [dqAdj] at hm''; omega⟩
          · rw [hv] at hlay; simp [dqrLayer] at hlay
      obtain ⟨_, m', hf0, hm⟩ := hinc ℓ' (le_refl ℓ')
      have hfin0 : (⟨ℓ' % ℓ', Nat.mod_lt _ (by omega)⟩ : Fin ℓ') = ⟨0, by omega⟩ := Fin.ext (Nat.mod_self ℓ')
      rw [hfin0, h0] at hf0
      injection hf0 with h1; injection h1 with _ h2; injection h2 with h3
      subst h3; omega
    · exfalso
      have hstep := hadj ⟨0, by omega⟩
      rw [h0] at hstep
      rcases f ⟨1 % ℓ', Nat.mod_lt _ (by omega)⟩ with ⟨_, _⟩ | ⟨⟩ <;> exact hstep
  · rintro rfl
    refine ⟨by omega, fun k => Sum.inl (⟨0, by omega⟩, Sum.inl (0, k)), ?_, ?_⟩
    · intro k₁ k₂ h; injection h with h1; injection h1 with _ h2; injection h2 with h3
      exact congrArg Prod.snd h3
    · intro k; exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

open Classical in
private lemma dqr_copy_kernel_ge5 {q r : ℕ} (hq : 2 ≤ q) (hqEven : Even q)
    {Q : Finset (DqrV q r)} (hQ : IsQKernel (dqrDigraph q r hq) q Q) (i : Fin r) :
    5 ≤ (Q.filter fun v => match v with | Sum.inl (i', _) => i' = i | Sum.inr () => False).card := by
  classical
  let D := dqrDigraph q r hq
  let ℓ := 2 * (q + 1)
  let Q1 : Finset (Fin ℓ) := Finset.univ.filter fun k => Sum.inl (i, Sum.inl (0, k)) ∈ Q
  let Q2 : Finset (Fin ℓ) := Finset.univ.filter fun k => Sum.inl (i, Sum.inl (1, k)) ∈ Q
  let Qy : Finset (Fin q) := Finset.univ.filter fun m => Sum.inl (i, Sum.inr m) ∈ Q
  -- Helper: any walk to `Sum.inl (i, _)` stays inside copy `i`!
  have hcopy_stay : ∀ (k : ℕ) (u : DqrV q r) (w : DqV q),
      ReachIn D k u (Sum.inl (i, w)) → ∃ u0 : DqV q, u = Sum.inl (i, u0) := by
    intro k
    induction k with
    | zero => intro u w hr; cases hr; exact ⟨w, rfl⟩
    | succ k ih =>
      intro u w hr
      obtain ⟨mid, hmid, hstep⟩ := reachIn_snoc_iff.mp hr
      rcases mid with ⟨im, wm⟩ | ⟨⟩
      · rcases hstep with ⟨rfl, _⟩; exact ih u wm hmid
      · exact False.elim hstep
  -- Helper: walk to `C^1` stays in `C^1` and advances index by `k mod ℓ`!
  have hc1_stay : ∀ (d : ℕ) (u : DqrV q r) (t : Fin ℓ),
      ReachIn D d u (Sum.inl (i, Sum.inl (0, t))) →
      ∃ s : Fin ℓ, u = Sum.inl (i, Sum.inl (0, s)) ∧ (s.val + d) % ℓ = t.val := by
    intro d
    induction d with
    | zero =>
      intro u t hr; cases hr
      exact ⟨t, rfl, by simp [Nat.mod_eq_of_lt t.isLt]⟩
    | succ d ih =>
      intro u t hr
      obtain ⟨mid, hmid, hstep⟩ := reachIn_snoc_iff.mp hr
      rcases mid with ⟨im, ⟨bm, km⟩ | mm⟩ | ⟨⟩
      · rcases hstep with ⟨rfl, ⟨rfl, ht⟩ | ⟨_, h1, _, _⟩⟩
        · obtain ⟨s, rfl, hs⟩ := ih u km hmid
          refine ⟨s, rfl, ?_⟩
          rw [← Nat.add_assoc, ← Nat.mod_add_mod, hs]; exact ht.symm
        · exact absurd h1 (by decide)
      · exact False.elim hstep.2
      · exact False.elim hstep
  -- Helper: walk to `y_{q-1}` of length `≤ q` stays in `{c^2_0} ∪ {y_0, ..., y_{q-1}}`!
  have hy_reach : ∀ (d m : ℕ) (hm : m < q) (u : DqrV q r), d ≤ m + 1 →
      ReachIn D d u (Sum.inl (i, Sum.inr ⟨m, hm⟩)) →
      u = Sum.inl (i, Sum.inl (1, ⟨0, by omega⟩)) ∨ ∃ m' : Fin q, u = Sum.inl (i, Sum.inr m') := by
    intro d
    induction d with
    | zero => intro m hm u _ hr; cases hr; exact Or.inr ⟨⟨m, hm⟩, rfl⟩
    | succ d ih =>
      intro m hm u hdm hr
      obtain ⟨mid, hmid, hstep⟩ := reachIn_snoc_iff.mp hr
      rcases mid with ⟨im, ⟨bm, km⟩ | mm⟩ | ⟨⟩
      · rcases hstep with ⟨rfl, rfl, hkm0, hm0⟩
        change m = 0 at hm0
        have hd0 : d = 0 := by omega
        subst hd0; cases hmid
        have hkm : km = ⟨0, by omega⟩ := Fin.ext hkm0
        rw [hkm]; exact Or.inl rfl
      · rcases hstep with ⟨rfl, hmm⟩
        change m = mm.val + 1 at hmm
        have hmeq : mm = ⟨m - 1, by omega⟩ := Fin.ext (by show mm.val = m - 1; omega)
        rw [hmeq] at hmid
        exact ih (m - 1) (by omega) u (by omega) hmid
      · exact False.elim hstep
  -- Helper: walk of length `≤ q` to `c^2_t` with `q ≤ t` must start in `C^2` (and if `q + 1 ≤ t`, not at `c^2_0`!)
  have hc2_stay : ∀ (d : ℕ) (u : DqrV q r) (t : Fin ℓ), d ≤ t.val →
      ReachIn D d u (Sum.inl (i, Sum.inl (1, t))) →
      (∃ s : Fin ℓ, u = Sum.inl (i, Sum.inl (1, s)) ∧ s.val + d = t.val) ∨
      (d > t.val) := by
    intro d
    induction d with
    | zero => intro u t _ hr; cases hr; exact Or.inl ⟨t, rfl, by simp⟩
    | succ d ih =>
      intro u t hdt hr
      obtain ⟨mid, hmid, hstep⟩ := reachIn_snoc_iff.mp hr
      rcases mid with ⟨im, ⟨bm, km⟩ | mm⟩ | ⟨⟩
      · rcases hstep with ⟨rfl, ⟨rfl, ht⟩ | ⟨_, _, _, ht0⟩⟩
        · have ht_pos : 0 < t.val := by omega
          have hkm_eq : km.val + 1 = t.val := by
            by_cases hlt : km.val + 1 < ℓ
            · rw [Nat.mod_eq_of_lt hlt] at ht; omega
            · have : km.val + 1 = ℓ := by omega
              rw [this, Nat.mod_self] at ht; omega
          rcases ih u km (by omega) hmid with ⟨s, rfl, hs⟩ | hbad
          · exact Or.inl ⟨s, rfl, by omega⟩
          · omega
        · omega
      · exact False.elim hstep.2
      · exact False.elim hstep
  -- Notice `Q1, Q2, Qy` inject disjointly into `Q_i`
  let Qi := Q.filter fun v => match v with | Sum.inl (i', _) => i' = i | Sum.inr () => False
  have hQi_ge : Q1.card + Q2.card + Qy.card ≤ Qi.card := by
    let S1 := Q1.image fun k => (Sum.inl (i, Sum.inl (0, k)) : DqrV q r)
    let S2 := Q2.image fun k => (Sum.inl (i, Sum.inl (1, k)) : DqrV q r)
    let Sy := Qy.image fun m => (Sum.inl (i, Sum.inr m) : DqrV q r)
    have hsub : S1 ∪ S2 ∪ Sy ⊆ Qi := by
      intro v hv
      simp only [Finset.mem_union, S1, S2, Sy, Finset.mem_image, Q1, Q2, Qy, Finset.mem_filter,
        Finset.mem_univ, true_and] at hv
      rcases hv with (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | ⟨m, hm, rfl⟩ <;>
        exact Finset.mem_filter.mpr ⟨by assumption, rfl⟩
    have hd12 : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]; intro v h1 h2
      obtain ⟨k₁, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨k₂, _, heq⟩ := Finset.mem_image.mp h2
      injection heq with h1'; injection h1' with _ h2'; injection h2' with h3'
      have h01 := congrArg Fin.val (congrArg Prod.fst h3')
      simp at h01
    have hd12y : Disjoint (S1 ∪ S2) Sy := by
      rw [Finset.disjoint_left]; intro v h1 h2
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp h2
      rcases Finset.mem_union.mp h1 with h1' | h1' <;>
        (obtain ⟨k, _, heq⟩ := Finset.mem_image.mp h1'; injection heq with h'; injection h' with _ h''; exact Sum.inl_ne_inr h'')
    have hc1 : S1.card = Q1.card := Finset.card_image_of_injective _ (fun a b h => by
      injection h with h1; injection h1 with _ h2; injection h2 with h3; exact congrArg Prod.snd h3)
    have hc2 : S2.card = Q2.card := Finset.card_image_of_injective _ (fun a b h => by
      injection h with h1; injection h1 with _ h2; injection h2 with h3; exact congrArg Prod.snd h3)
    have hcy : Sy.card = Qy.card := Finset.card_image_of_injective _ (fun a b h => by
      injection h with h1; injection h1 with _ h2; injection h2)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd12y, Finset.card_union_of_disjoint hd12, hc1, hc2, hcy] at hle
    exact hle
  -- Every vertex `t ∈ C^1` is covered by `Q1` at cyclic distance `≤ q`
  have hQ1_cov : ∀ t : Fin ℓ, ∃ s ∈ Q1, ∃ d ≤ q, (s.val + d) % ℓ = t.val := by
    intro t
    obtain ⟨u, huQ, d, hdq, hreach⟩ := hQ.2 (Sum.inl (i, Sum.inl (0, t)))
    obtain ⟨s, rfl, hmod⟩ := hc1_stay d u t hreach
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huQ⟩, d, hdq, hmod⟩
  -- Hence `|Q1| ≥ 2` (each `s ∈ Q1` covers at most `q + 1` vertices of `C^1`, total `2*(q+1)`)!
  have hQ1_ge2 : 2 ≤ Q1.card := by
    have hcover : (Finset.univ : Finset (Fin ℓ)) ⊆ Q1.biUnion fun s =>
        (Finset.range (q + 1)).image fun d => (⟨(s.val + d) % ℓ, Nat.mod_lt _ (by omega)⟩ : Fin ℓ) := by
      intro t _
      obtain ⟨s, hs, d, hdq, hmod⟩ := hQ1_cov t
      exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨d, Finset.mem_range.mpr (by omega), Fin.ext hmod⟩⟩
    have hcard := Finset.card_le_card hcover
    have hle_bi : (Q1.biUnion fun s =>
        (Finset.range (q + 1)).image fun d => (⟨(s.val + d) % ℓ, Nat.mod_lt _ (by omega)⟩ : Fin ℓ)).card ≤
        Q1.card * (q + 1) := by
      calc _ ≤ ∑ s ∈ Q1, ((Finset.range (q + 1)).image fun d =>
              (⟨(s.val + d) % ℓ, Nat.mod_lt _ (by omega)⟩ : Fin ℓ)).card := Finset.card_biUnion_le
        _ ≤ ∑ _s ∈ Q1, (q + 1) := Finset.sum_le_sum fun _ _ => le_trans Finset.card_image_le (by simp)
        _ = Q1.card * (q + 1) := by simp
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    have : 2 * (q + 1) ≤ Q1.card * (q + 1) := le_trans hcard hle_bi
    nlinarith
  -- Case split on whether `c^2_0 ∈ Q`!
  by_cases hc20 : Sum.inl (i, Sum.inl (1, ⟨0, by omega⟩)) ∈ Q
  · -- Case 2: `c^2_0 ∈ Q` => no odd-indexed vertex of `C^1` is in `Q`, so `|Q1| ≥ 3`!
    have hQ1_even : ∀ s ∈ Q1, s.val % 2 = 0 := by
      intro s hs
      by_contra hne
      have hodd : s.val % 2 = 1 := by omega
      exact hQ.1 _ (Finset.mem_filter.mp hs).2 _ hc20 ⟨rfl, Or.inr ⟨rfl, rfl, hodd, rfl⟩⟩
    have hQ1_ge3 : 3 ≤ Q1.card := by
      by_contra hlt
      have hQ1_eq2 : Q1.card = 2 := by omega
      obtain ⟨s1, hs1, hcard1⟩ : ∃ s1 ∈ Q1, (Q1.erase s1).card = 1 := by
        obtain ⟨s1, hs1⟩ := Finset.card_pos.mp (by omega : 0 < Q1.card)
        exact ⟨s1, hs1, by rw [Finset.card_erase_of_mem hs1, hQ1_eq2]⟩
      obtain ⟨s2, hs2⟩ := Finset.card_eq_one.mp hcard1
      have hs2_mem : s2 ∈ Q1 := Finset.mem_of_mem_erase (by rw [hs2]; exact Finset.mem_singleton_self s2)
      have hQ1_pair : Q1 = {s1, s2} := by
        ext x; constructor
        · intro hx
          by_cases hx1 : x = s1
          · simp [hx1]
          · have : x ∈ Q1.erase s1 := Finset.mem_erase.mpr ⟨hx1, hx⟩
            rw [hs2, Finset.mem_singleton] at this; simp [this]
        · intro hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
      -- Both `s1.val` and `s2.val` are even, so `((s1.val + q + 1) % ℓ)` is odd;
      -- check `t1 = (s1 + q + 1) % ℓ` and `t2 = (s2 + q + 1) % ℓ`!
      -- Specifically, `t1` cannot be covered by `s1` in `≤ q` steps, so it's covered by `s2` in `≤ q` steps,
      -- AND `t2` must be covered by `s1` in `≤ q` steps!
      have hcov_pair : ∀ t : Fin ℓ, (∃ d ≤ q, (s1.val + d) % ℓ = t.val) ∨ (∃ d ≤ q, (s2.val + d) % ℓ = t.val) := by
        intro t
        obtain ⟨s, hs, d, hdq, hmod⟩ := hQ1_cov t
        rw [hQ1_pair] at hs
        rcases Finset.mem_insert.mp hs with rfl | hs'
        · exact Or.inl ⟨d, hdq, hmod⟩
        · have hs2' := Finset.mem_singleton.mp hs'; subst hs2'; exact Or.inr ⟨d, hdq, hmod⟩
      have he1 := hQ1_even s1 hs1
      have he2 := hQ1_even s2 hs2_mem
      have hq1_odd : (q + 1) % 2 = 1 := by rcases hqEven with ⟨m, rfl⟩; omega
      let t1 : Fin ℓ := ⟨(s1.val + q + 1) % ℓ, Nat.mod_lt _ (by omega)⟩
      rcases hcov_pair t1 with ⟨d, hdq, hmod⟩ | ⟨d1, hd1q, hmod1⟩
      · -- `(s1 + d) % ℓ = (s1 + q + 1) % ℓ` with `d ≤ q < q + 1 < ℓ` -> impossible!
        have h1 : (s1.val + d) % ℓ = (s1.val + (q + 1)) % ℓ := by simpa [t1, Nat.add_assoc] using hmod
        have h2 : d ≡ q + 1 [MOD ℓ] := Nat.ModEq.add_left_cancel' s1.val h1
        rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : d < ℓ), Nat.mod_eq_of_lt (by omega : q + 1 < ℓ)] at h2
        omega
      · let t2 : Fin ℓ := ⟨(s2.val + q + 1) % ℓ, Nat.mod_lt _ (by omega)⟩
        rcases hcov_pair t2 with ⟨d2, hd2q, hmod2⟩ | ⟨d, hdq, hmod⟩
        · -- `s2 + d1 ≡ s1 + q + 1` and `s1 + d2 ≡ s2 + q + 1 (mod ℓ)` => `d1 + d2 ≡ 2*(q+1) = ℓ (mod ℓ)`
          -- Since `0 ≤ d1 + d2 ≤ 2q < ℓ`, we MUST have `d1 + d2 = 0`, so `d1 = 0`, hence `s2 ≡ s1 + q + 1 (mod ℓ)`!
          -- Contradicts `s1, s2` both even and `q + 1` odd!!
          have h1 : (s2.val + d1) % ℓ = (s1.val + (q + 1)) % ℓ := by simpa [t1, Nat.add_assoc] using hmod1
          have h2 : (s1.val + d2) % ℓ = (s2.val + (q + 1)) % ℓ := by simpa [t2, Nat.add_assoc] using hmod2
          have hadd : (s2.val + d1 + (s1.val + d2)) % ℓ = (s1.val + (q + 1) + (s2.val + (q + 1))) % ℓ := by
            rw [Nat.add_mod, h1, h2, ← Nat.add_mod]
          have hrew1 : s2.val + d1 + (s1.val + d2) = (s1.val + s2.val) + (d1 + d2) := by ring
          have hrew2 : s1.val + (q + 1) + (s2.val + (q + 1)) = (s1.val + s2.val) + ℓ := by dsimp [ℓ]; ring
          rw [hrew1, hrew2, Nat.add_mod_right] at hadd
          have hd0 : (d1 + d2) % ℓ = 0 := by
            have := Nat.ModEq.add_left_cancel' (s1.val + s2.val) (show (s1.val + s2.val) + (d1 + d2) ≡ (s1.val + s2.val) + 0 [MOD ℓ] by
              simpa [Nat.ModEq] using hadd)
            simpa [Nat.ModEq] using this
          rw [Nat.mod_eq_of_lt (by omega : d1 + d2 < ℓ)] at hd0
          have hd1_0 : d1 = 0 := by omega
          rw [hd1_0, add_zero, Nat.mod_eq_of_lt s2.isLt] at h1
          have hlin : s1.val + (q + 1) = 2 * ((q + 1) * ((s1.val + (q + 1)) / ℓ)) + s2.val := by
            calc s1.val + (q + 1) = ℓ * ((s1.val + (q + 1)) / ℓ) + (s1.val + (q + 1)) % ℓ := (Nat.div_add_mod _ _).symm
              _ = 2 * ((q + 1) * ((s1.val + (q + 1)) / ℓ)) + s2.val := by rw [← h1]; dsimp only [ℓ]; ring
          omega
        · have h1 : (s2.val + d) % ℓ = (s2.val + (q + 1)) % ℓ := by simpa [t2, Nat.add_assoc] using hmod
          have h2 : d ≡ q + 1 [MOD ℓ] := Nat.ModEq.add_left_cancel' s2.val h1
          rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : d < ℓ), Nat.mod_eq_of_lt (by omega : q + 1 < ℓ)] at h2
          omega
    -- Also `|Q2| ≥ 2`: `c^2_0 ∈ Q2` AND `c^2_{q+1}` is covered by some `s ∈ Q2` with `s ≠ 0`!
    have h0_Q2 : (⟨0, by omega⟩ : Fin ℓ) ∈ Q2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc20⟩
    obtain ⟨u, huQ, d, hdq, hreach⟩ := hQ.2 (Sum.inl (i, Sum.inl (1, ⟨q + 1, by omega⟩)))
    rcases hc2_stay d u ⟨q + 1, by omega⟩ (by show d ≤ q + 1; omega) hreach with ⟨s, rfl, hsd⟩ | hbad
    · have hs_Q2 : s ∈ Q2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huQ⟩
      have hs_ne0 : s ≠ ⟨0, by omega⟩ := by
        intro h; have := congrArg Fin.val h; dsimp only at this hsd; omega
      have hQ2_ge2 : 2 ≤ Q2.card := by
        have hsub : ({⟨0, by omega⟩, s} : Finset (Fin ℓ)) ⊆ Q2 := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hcard : ({⟨0, by omega⟩, s} : Finset (Fin ℓ)).card = 2 := Finset.card_pair hs_ne0.symm
        have := Finset.card_le_card hsub; omega
      show 5 ≤ Qi.card; omega
    · dsimp only at hbad; omega
  · -- Case 1: `c^2_0 ∉ Q` => `|Qy| ≥ 1`, `|Q2| ≥ 2`, `|Q1| ≥ 2`, total `≥ 5`!
    have hQy_ge1 : 1 ≤ Qy.card := by
      obtain ⟨u, huQ, d, hdq, hreach⟩ := hQ.2 (Sum.inl (i, Sum.inr ⟨q - 1, by omega⟩))
      rcases hy_reach d (q - 1) (by omega) u (by omega) hreach with rfl | ⟨m', rfl⟩
      · exact absurd huQ hc20
      · exact Finset.card_pos.mpr ⟨m', Finset.mem_filter.mpr ⟨Finset.mem_univ _, huQ⟩⟩
    -- Vertices `c^2_q` and `c^2_{2q+1}` must be covered by two distinct elements of `Q2`!
    obtain ⟨u1, hu1Q, d1, hd1q, hr1⟩ := hQ.2 (Sum.inl (i, Sum.inl (1, ⟨q, by omega⟩)))
    obtain ⟨u2, hu2Q, d2, hd2q, hr2⟩ := hQ.2 (Sum.inl (i, Sum.inl (1, ⟨2 * q + 1, by omega⟩)))
    rcases hc2_stay d1 u1 ⟨q, by omega⟩ (by show d1 ≤ q; omega) hr1 with ⟨s1, rfl, hs1d⟩ | hbad
    · rcases hc2_stay d2 u2 ⟨2 * q + 1, by omega⟩ (by show d2 ≤ 2 * q + 1; omega) hr2 with ⟨s2, rfl, hs2d⟩ | hbad2
      · have hs1_Q2 : s1 ∈ Q2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu1Q⟩
        have hs2_Q2 : s2 ∈ Q2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu2Q⟩
        have hs12 : s1 ≠ s2 := by
          intro h; have := congrArg Fin.val h; dsimp only at hs1d hs2d; omega
        have hQ2_ge2 : 2 ≤ Q2.card := by
          have hsub : ({s1, s2} : Finset (Fin ℓ)) ⊆ Q2 := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption
          have hcard : ({s1, s2} : Finset (Fin ℓ)).card = 2 := Finset.card_pair hs12
          have := Finset.card_le_card hsub; omega
        show 5 ≤ Qi.card; omega
      · dsimp only at hbad2; omega
    · dsimp only at hbad; omega

private lemma theorem_1_7 :
    ∀ q r : ℕ, 2 ≤ q → Even q → 2 ≤ r →
      ∃ (n : ℕ) (D : FinDigraph (Fin n)),
        n = r * (5 * q + 4) + 1 ∧ IsWeaklyConnected D ∧ IsSourceFree D ∧ IsBipartite D ∧
        (∀ ℓ' : ℕ, HasDirCycle D ℓ' ↔ ℓ' = 2 * (q + 1)) ∧
        ∀ Q : Finset (Fin n), IsQKernel D q Q →
          ((ceilDiv (2 * (q + 1)) (q + 1) : ℚ) / ((2 * (q + 1) : ℕ) : ℚ)) * (n : ℚ) +
            ((r - 1 : ℕ) : ℚ) / ((q + 1 : ℕ) : ℚ) ≤ (Q.card : ℚ) := by
  classical
  intro q r hq hqEven hr
  let D0 := dqrDigraph q r hq
  let n := Fintype.card (DqrV q r)
  have hn_eq : n = r * (5 * q + 4) + 1 := by
    simp only [n, DqV, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    have hu : Fintype.card Unit = 1 := Fintype.card_unique
    rw [hu]; ring
  let e : Fin n ≃ DqrV q r := (Fintype.equivFin (DqrV q r)).symm
  refine ⟨n, comapDigraph D0 e, hn_eq,
    weaklyConnected_comap e (dqr_weaklyConnected hq hr),
    sourceFree_comap e (dqr_sourceFree hq hr),
    (bipartite_comap_iff e).mpr (dqr_bipartite hq hqEven),
    fun ℓ' => (hasDirCycle_comap_iff e ℓ').trans (dqr_cycles_iff hq hr ℓ'), ?_⟩
  intro Q hQ
  let Q0 := Q.image e
  have hQ0 : IsQKernel D0 q Q0 := qKernel_comap_map e hQ
  have hQ0_card : Q0.card = Q.card := card_image_equiv e Q
  let Qi (i : Fin r) : Finset (DqrV q r) :=
    Q0.filter fun v => match v with | Sum.inl (i', _) => i' = i | Sum.inr () => False
  have hdisj : ((Finset.univ : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint Qi := by
    intro i₁ _ i₂ _ hne
    change Disjoint (Qi i₁) (Qi i₂)
    rw [Finset.disjoint_left]
    intro v h1 h2
    have hm1 := (Finset.mem_filter.mp h1).2
    have hm2 := (Finset.mem_filter.mp h2).2
    rcases v with ⟨i', _⟩ | ⟨⟩
    · exact hne (hm1.symm.trans hm2)
    · exact hm1
  have hsub : Finset.univ.biUnion Qi ⊆ Q0 := by
    intro v hv
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp hi).1
  have h5r : 5 * r ≤ Q.card := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj, hQ0_card] at h1
    have h2 : ∑ _i : Fin r, 5 ≤ ∑ i : Fin r, (Qi i).card :=
      Finset.sum_le_sum fun i _ => dqr_copy_kernel_ge5 hq hqEven hQ0 i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
    omega
  have hceil : ceilDiv (2 * (q + 1)) (q + 1) = 2 := by
    dsimp only [ceilDiv]
    have h1 : 2 * (q + 1) + (q + 1) - 1 = (q + 1) * 2 + q := by omega
    rw [h1, Nat.mul_add_div (by omega : 0 < q + 1), Nat.div_eq_of_lt (by omega : q < q + 1)]
  have hn_q : (n : ℚ) = ((r * (5 * q + 4) + 1 : ℕ) : ℚ) := by exact_mod_cast hn_eq
  rw [hceil, hn_q]
  have hr1 : ((r - 1 : ℕ) : ℚ) = (r : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hq1_pos : (0 : ℚ) < ((q + 1 : ℕ) : ℚ) := by positivity
  have hlhs : ((2 : ℚ) / ((2 * (q + 1) : ℕ) : ℚ)) * ((r * (5 * q + 4) + 1 : ℕ) : ℚ) +
      ((r - 1 : ℕ) : ℚ) / ((q + 1 : ℕ) : ℚ) = (5 * r : ℚ) := by
    rw [hr1]; push_cast; field_simp; ring
  rw [Nat.cast_ofNat, hlhs]
  have : ((5 * r : ℕ) : ℚ) ≤ (Q.card : ℚ) := by exact_mod_cast h5r
  simpa using this

/-! ### Part 4: Functional Digraphs, Harary's Lemma, and Theorems 1.9 & 1.8 -/

/-- In a finite functional digraph (`pred v → v`), every vertex eventually enters a periodic cycle. -/
private lemma functional_periodic {V : Type*} [Fintype V] (pred : V → V) (v : V) :
    ∃ (a p : ℕ), 0 < p ∧ pred^[a + p] v = pred^[a] v := by
  have hnotinj : ¬ Function.Injective (fun k : ℕ => pred^[k] v) := by
    intro hinj
    exact absurd (Finite.of_injective _ hinj) (Infinite.not_finite)
  rw [Function.Injective] at hnotinj
  push Not at hnotinj
  obtain ⟨i, j, heq, hne⟩ := hnotinj
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨i, j - i, by omega, by rw [Nat.add_sub_of_le (le_of_lt hlt)]; exact heq.symm⟩
  · exact ⟨j, i - j, by omega, by rw [Nat.add_sub_of_le (le_of_lt hgt)]; exact heq⟩

private lemma functional_iterate_eq_of_weak {V : Type*} (pred : V → V)
    {u v : V} (h : Relation.ReflTransGen (fun x y => pred y = x ∨ pred x = y) u v) :
    ∃ a b : ℕ, pred^[a] u = pred^[b] v := by
  induction h with
  | refl => exact ⟨0, 0, rfl⟩
  | @tail w z _ hstep ih =>
    obtain ⟨a, b, hab⟩ := ih
    rcases hstep with hzw | hwz
    · -- `pred z = w`
      refine ⟨a, b + 1, ?_⟩
      rw [Function.iterate_succ_apply, hzw]; exact hab
    · -- `pred w = z`
      cases b with
      | zero =>
        refine ⟨a + 1, 0, ?_⟩
        rw [Function.iterate_succ_apply', hab]; exact hwz
      | succ b =>
        refine ⟨a, b, ?_⟩
        rw [Function.iterate_succ_apply, hwz] at hab; exact hab

private lemma theorem_1_9 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (D : FinDigraph V) (c : V → Bool) (ℓ q : ℕ),
      3 ≤ q → Odd q → IsUnicyclic D → IsBipartition D c → HasDirCycle D ℓ →
      ∃ Q : Finset V, IsQKernel D q Q ∧ (∀ u ∈ Q, c u = false) ∧
        (Q.card : ℚ) ≤ 2 * ((ceilDiv ℓ (q + 1) : ℚ) / (ℓ : ℚ)) *
          ((Finset.univ.filter fun v => c v = false).card : ℚ) := by
  classical
  intro V _ _ D c ℓ q hq3 hqOdd ⟨hin1, hweak⟩ hc ⟨hℓ2, cyc, hcyc_inj, hcyc_adj⟩
  -- Unique predecessor function `pred v`
  let pred : V → V := fun v => Classical.choose (hin1 v)
  have hpred_adj : ∀ v : V, D.adj (pred v) v := fun v => (Classical.choose_spec (hin1 v)).1
  have hpred_uniq : ∀ u v : V, D.adj u v → u = pred v := fun u v huv =>
    (Classical.choose_spec (hin1 v)).2 u huv
  -- The given cycle satisfies `pred (cyc (i + 1)) = cyc i`!
  have hcyc_pred : ∀ i : Fin ℓ, pred (cyc ⟨(i.val + 1) % ℓ, Nat.mod_lt _ (by omega)⟩) = cyc i :=
    fun i => (hpred_uniq _ _ (hcyc_adj i)).symm
  -- Also `ℓ` is even (since `D` is bipartite)!
  have hcyc_col : ∀ m : ℕ, m ≤ ℓ →
      c (cyc ⟨m % ℓ, Nat.mod_lt _ (by omega)⟩) = if m % 2 = 0 then c (cyc ⟨0, by omega⟩) else !(c (cyc ⟨0, by omega⟩)) := by
    intro m _
    induction m with
    | zero => simp
    | succ m ih =>
      have ihm := ih (by omega)
      have hne := hc _ _ (hcyc_adj ⟨m % ℓ, Nat.mod_lt _ (by omega)⟩)
      have hmod : (m % ℓ + 1) % ℓ = (m + 1) % ℓ := by rw [Nat.mod_add_mod]
      have hne' : c (cyc ⟨m % ℓ, Nat.mod_lt _ (by omega)⟩) ≠ c (cyc ⟨(m + 1) % ℓ, Nat.mod_lt _ (by omega)⟩) := by
        convert hne using 3; exact Fin.ext hmod.symm
      cases hc0 : c (cyc ⟨0, by omega⟩) <;> cases hcm1 : c (cyc ⟨(m + 1) % ℓ, Nat.mod_lt _ (by omega)⟩) <;>
        by_cases hm2 : m % 2 = 0
      all_goals
        first
        | simp_all [show (m + 1) % 2 = 1 by omega]
        | simp_all [show (m + 1) % 2 = 0 by omega]
  have hℓ_even : ℓ % 2 = 0 := by
    have h := hcyc_col ℓ (le_refl ℓ)
    have hfin0 : (⟨ℓ % ℓ, Nat.mod_lt _ (by omega)⟩ : Fin ℓ) = ⟨0, by omega⟩ := Fin.ext (Nat.mod_self ℓ)
    rw [hfin0] at h
    by_contra hodd
    simp [hodd] at h
  -- Rotate the cycle so that `c (c0) = false`!
  let shift : ℕ := if c (cyc ⟨0, by omega⟩) = false then 0 else 1
  let cyc' : Fin ℓ → V := fun i => cyc ⟨(i.val + shift) % ℓ, Nat.mod_lt _ (by omega)⟩
  have hcyc'_inj : Function.Injective cyc' := by
    intro i j h
    have hij := hcyc_inj h
    have hv := congrArg Fin.val hij
    dsimp only at hv
    have hEq : i.val ≡ j.val [MOD ℓ] := Nat.ModEq.add_right_cancel' shift hv
    rw [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hEq
    exact Fin.ext hEq
  have hcyc'_adj : ∀ i : Fin ℓ, D.adj (cyc' i) (cyc' ⟨(i.val + 1) % ℓ, Nat.mod_lt _ (by omega)⟩) := by
    intro i
    have h := hcyc_adj ⟨(i.val + shift) % ℓ, Nat.mod_lt _ (by omega)⟩
    convert h using 2
    apply Fin.ext; dsimp only
    rw [Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1; ring
  have hcyc'_pred : ∀ i : Fin ℓ, pred (cyc' ⟨(i.val + 1) % ℓ, Nat.mod_lt _ (by omega)⟩) = cyc' i :=
    fun i => (hpred_uniq _ _ (hcyc'_adj i)).symm
  have hc0_false : c (cyc' ⟨0, by omega⟩) = false := by
    dsimp only [cyc', shift]
    by_cases h0 : c (cyc ⟨0, by omega⟩) = false
    · simp [h0]
    · simp only [h0, zero_add]
      have h1 := hcyc_col 1 (by omega)
      have hc0t : c (cyc ⟨0, by omega⟩) = true := Bool.eq_true_of_not_eq_false h0
      simpa [hc0t] using h1
  let c0 : V := cyc' ⟨0, by omega⟩
  -- Every vertex `v` reaches `c0` by iterating `pred`! (Harary's Lemma)
  have hpred_to_cyc : ∀ v : V, ∃ k : ℕ, pred^[k] v = c0 := by
    -- First, `pred^[k] (cyc' i) = cyc' ((i + ℓ - k % ℓ) % ℓ)` so `cyc'` is closed & transitive under `pred`!
    have hcyc_reach_c0 : ∀ i : Fin ℓ, pred^[i.val] (cyc' i) = c0 := by
      have hstep : ∀ m : ℕ, (hm : m < ℓ) → pred^[m] (cyc' ⟨m, hm⟩) = c0 := by
        intro m
        induction m with
        | zero => intro _; rfl
        | succ m ih =>
          intro hm
          rw [Function.iterate_succ_apply]
          have hp := hcyc'_pred ⟨m, by omega⟩
          have hfeq : (⟨(m + 1) % ℓ, Nat.mod_lt _ (by omega)⟩ : Fin ℓ) = ⟨m + 1, hm⟩ :=
            Fin.ext (Nat.mod_eq_of_lt hm)
          rw [hfeq] at hp
          rw [hp]
          exact ih (by omega)
      intro i; exact hstep i.val i.isLt
    have hcyc_iter : ∀ (k : ℕ) (i : Fin ℓ), ∃ j : Fin ℓ, pred^[k] (cyc' i) = cyc' j := by
      intro k
      induction k with
      | zero => intro i; exact ⟨i, rfl⟩
      | succ k ih =>
        intro i
        obtain ⟨j, hj⟩ := ih i
        rw [Function.iterate_succ_apply', hj]
        let prev : Fin ℓ := if hj0 : j.val = 0 then ⟨ℓ - 1, by omega⟩ else ⟨j.val - 1, by omega⟩
        have hprev : pred (cyc' j) = cyc' prev := by
          have hp := hcyc'_pred prev
          have hj_eq : j = ⟨(prev.val + 1) % ℓ, Nat.mod_lt _ (by omega)⟩ := by
            apply Fin.ext; dsimp only [prev]
            split_ifs with hj0
            · rw [hj0, show ℓ - 1 + 1 = ℓ by omega, Nat.mod_self]
            · rw [show j.val - 1 + 1 = j.val by omega, Nat.mod_eq_of_lt j.isLt]
          rw [hj_eq]; exact hp
        exact ⟨prev, hprev⟩
    intro v
    have hmono : ∀ {a b : V}, Relation.ReflTransGen (fun x y => D.adj x y ∨ D.adj y x) a b →
        Relation.ReflTransGen (fun x y => pred y = x ∨ pred x = y) a b := fun h => by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hxy ih =>
        refine Relation.ReflTransGen.tail ih ?_
        rcases hxy with h' | h'
        · exact Or.inl (hpred_uniq _ _ h').symm
        · exact Or.inr (hpred_uniq _ _ h').symm
    have hw : Relation.ReflTransGen (fun x y => pred y = x ∨ pred x = y) v c0 := hmono (hweak v c0)
    obtain ⟨a, b, hab⟩ := functional_iterate_eq_of_weak pred hw
    obtain ⟨j, hj⟩ := hcyc_iter b ⟨0, by omega⟩
    have hreach_j : pred^[a] v = cyc' j := hab.trans hj
    refine ⟨j.val + a, ?_⟩
    rw [Function.iterate_add_apply, hreach_j, hcyc_reach_c0 j]
  -- Define `depth v = Nat.find (hpred_to_cyc v)` (distance from `c0` in the out-arborescence!)
  let depth (v : V) : ℕ := Nat.find (hpred_to_cyc v)
  have hdepth_spec : ∀ v : V, pred^[depth v] v = c0 := fun v => Nat.find_spec (hpred_to_cyc v)
  have hdepth_min : ∀ (v : V) (k : ℕ), pred^[k] v = c0 → depth v ≤ k := fun v _ hk => Nat.find_min' (hpred_to_cyc v) hk
  have hdepth_c0 : depth c0 = 0 := Nat.eq_zero_of_le_zero (hdepth_min c0 0 rfl)
  have hdepth_par : ∀ v : V, v ≠ c0 → depth v = depth (pred v) + 1 := by
    intro v hv
    have hp : 0 < depth v := by
      by_contra h0; have hd0 : depth v = 0 := by omega
      have := hdepth_spec v; rw [hd0] at this; exact hv this
    have h1 : pred^[depth v - 1] (pred v) = c0 := by
      have := hdepth_spec v
      rw [← Nat.sub_add_cancel hp, Function.iterate_succ_apply] at this; exact this
    have hle1 : depth (pred v) ≤ depth v - 1 := hdepth_min (pred v) (depth v - 1) h1
    have h2 : pred^[depth (pred v) + 1] v = c0 := by
      rw [Function.iterate_succ_apply]; exact hdepth_spec (pred v)
    have hle2 : depth v ≤ depth (pred v) + 1 := hdepth_min v (depth (pred v) + 1) h2
    omega
  have hiter_depth : ∀ (k : ℕ) (v : V), k ≤ depth v →
      depth (pred^[k] v) + k = depth v ∧ ReachIn D k (pred^[k] v) v := by
    intro k
    induction k with
    | zero => intro v _; exact ⟨by simp, ReachIn.zero v⟩
    | succ k ih =>
      intro v hkv
      have hvc : v ≠ c0 := by intro h; subst h; rw [hdepth_c0] at hkv; omega
      have hdp := hdepth_par v hvc
      obtain ⟨hd, hreach_k⟩ := ih (pred v) (by omega)
      rw [Function.iterate_succ_apply]
      exact ⟨by omega, reachIn_trans hreach_k (reachIn_one (hpred_adj v))⟩
  have hcolor_depth : ∀ (d : ℕ) (v : V), depth v = d → c v = decide (d % 2 = 1) := by
    intro d
    induction d with
    | zero =>
      intro v hv
      have : v = c0 := by have := hdepth_spec v; rwa [hv] at this
      subst this; simpa using hc0_false
    | succ d ih =>
      intro v hv
      have hvc : v ≠ c0 := by intro h; subst h; rw [hdepth_c0] at hv; omega
      have hdp := hdepth_par v hvc
      have hcp := ih (pred v) (by omega)
      have hne := hc (pred v) v (hpred_adj v)
      cases hcv : c v <;> by_cases hd2 : d % 2 = 1
      all_goals
        first
        | simp_all [show (d + 1) % 2 = 0 by omega]
        | simp_all [show (d + 1) % 2 = 1 by omega]
  -- Exact depth of cycle vertices `depth (cyc' i) = i.val`!
  have hdepth_cyc : ∀ i : Fin ℓ, depth (cyc' i) = i.val := by
    have hup : ∀ (m : ℕ) (hm : m < ℓ), pred^[m] (cyc' ⟨m, hm⟩) = c0 := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro hm
        rw [Function.iterate_succ_apply]
        have hp := hcyc'_pred ⟨m, by omega⟩
        have hfeq : (⟨(m + 1) % ℓ, Nat.mod_lt _ (by omega)⟩ : Fin ℓ) = ⟨m + 1, hm⟩ :=
          Fin.ext (Nat.mod_eq_of_lt hm)
        rw [hfeq] at hp
        rw [hp]; exact ih (by omega)
    have hdown : ∀ (k : ℕ) (m : ℕ) (hm : m < ℓ), k ≤ m →
        pred^[k] (cyc' ⟨m, hm⟩) = cyc' ⟨m - k, by omega⟩ := by
      intro k
      induction k with
      | zero => intro m hm _; simp
      | succ k ih =>
        intro m hm hkm
        rw [Function.iterate_succ_apply]
        have hp := hcyc'_pred ⟨m - 1, by omega⟩
        have hm1 : (m - 1 + 1) % ℓ = m := by rw [show m - 1 + 1 = m by omega, Nat.mod_eq_of_lt hm]
        have hfeq : (⟨(m - 1 + 1) % ℓ, Nat.mod_lt _ (by omega)⟩ : Fin ℓ) = ⟨m, hm⟩ := Fin.ext hm1
        rw [hfeq] at hp
        rw [hp, ih (m - 1) (by omega) (by omega)]
        congr 1; exact Fin.ext (by show m - 1 - k = m - (k + 1); omega)
    intro i
    have hle : depth (cyc' i) ≤ i.val := hdepth_min (cyc' i) i.val (hup i.val i.isLt)
    have hspec := hdepth_spec (cyc' i)
    rw [hdown (depth (cyc' i)) i.val i.isLt hle] at hspec
    have hij := hcyc'_inj hspec
    have hv := congrArg Fin.val hij
    dsimp only at hv; omega
  -- Reachability along the cycle from `cyc' i` to `c0` in `ℓ - i.val` steps (for `i.val > 0`)!
  have hcyc_to_c0 : ∀ (m : ℕ) (hm : m < ℓ), 0 < m → ReachIn D (ℓ - m) (cyc' ⟨m, hm⟩) c0 := by
    have hstep : ∀ (d : ℕ) (m : ℕ) (hm : m < ℓ), m + d = ℓ → ReachIn D d (cyc' ⟨m, hm⟩) c0 := by
      intro d
      induction d with
      | zero => intro m hm h; omega
      | succ d ih =>
        intro m hm hsum
        by_cases hd0 : d = 0
        · subst hd0
          have hadj := hcyc'_adj ⟨m, hm⟩
          have hmod : (m + 1) % ℓ = 0 := by rw [hsum, Nat.mod_self]
          have : cyc' ⟨(m + 1) % ℓ, Nat.mod_lt _ (by omega)⟩ = c0 := by congr 1; exact Fin.ext hmod
          rw [this] at hadj; exact reachIn_one hadj
        · have hadj := hcyc'_adj ⟨m, hm⟩
          have hm1 : m + 1 < ℓ := by omega
          have hadj' : D.adj (cyc' ⟨m, hm⟩) (cyc' ⟨m + 1, hm1⟩) := by
            convert hadj using 2; exact Fin.ext (Nat.mod_eq_of_lt hm1).symm
          exact ReachIn.succ hadj' (ih (m + 1) hm1 (by omega))
    intro m hm _; exact hstep (ℓ - m) m hm (by omega)
  -- Now follow the exact proof of Theorem 1.9!
  let U : Finset V := Finset.univ.filter fun v => c v = false
  have hU_ge : ℓ / 2 ≤ U.card := by
    let cycEven : Finset V := (Finset.range (ℓ / 2)).attach.image fun k =>
      cyc' ⟨2 * k.val, by have := Finset.mem_range.mp k.prop; omega⟩
    have hsub : cycEven ⊆ U := by
      intro v hv
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hcolor_depth _ _ (hdepth_cyc ⟨2 * k.val, by have := Finset.mem_range.mp k.prop; omega⟩)]
      simp
    have hcard : cycEven.card = ℓ / 2 := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro k₁ k₂ heq
        have := congrArg Fin.val (hcyc'_inj heq); dsimp only at this
        exact Subtype.ext (by omega)
    have := Finset.card_le_card hsub; omega
  let s := ℓ / (q + 1)
  let t := ℓ % (q + 1)
  have hℓ_eq : ℓ = s * (q + 1) + t := by
    have := Nat.div_add_mod ℓ (q + 1); dsimp only [s, t]; linarith
  have ht_lt : t < q + 1 := Nat.mod_lt ℓ (by omega)
  let m := (q + 1) / 2
  have hm_eq : 2 * m = q + 1 := by rcases hqOdd with ⟨k, rfl⟩; dsimp only [m]; omega
  have hm_pos : 0 < m := by omega
  have ht_even : t % 2 = 0 := by
    have hlin : ℓ = 2 * (s * m) + t := by rw [hℓ_eq, ← hm_eq]; ring
    omega
  let r_cnt : ℕ := if t = 0 then 0 else m - t / 2
  let Qp (j : Fin m) : Finset V := Finset.univ.filter fun v => depth v % (q + 1) = 2 * j.val
  let Qset (j : Fin m) : Finset V :=
    if t = 0 then Qp j
    else if j.val < t / 2 then Qp j
    else insert c0 (Qp j)
  -- Every `Qset j ⊆ U`
  have hQsubU : ∀ j : Fin m, Qset j ⊆ U := by
    intro j v hv
    have hQp_sub : ∀ x ∈ Qp j, x ∈ U := fun x hx => by
      have hmod := (Finset.mem_filter.mp hx).2
      have hmod2 : depth x % 2 = 0 := by
        have hlin : depth x = 2 * (m * (depth x / (q + 1))) + 2 * j.val := by
          calc depth x = (q + 1) * (depth x / (q + 1)) + depth x % (q + 1) := (Nat.div_add_mod _ _).symm
            _ = 2 * (m * (depth x / (q + 1))) + 2 * j.val := by rw [hmod, ← hm_eq]; ring
        omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hcolor_depth _ _ rfl]; simp [hmod2]
    dsimp only [Qset] at hv
    split_ifs at hv
    · exact hQp_sub v hv
    · exact hQp_sub v hv
    · rcases Finset.mem_insert.mp hv with rfl | hv'
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0_false⟩
      · exact hQp_sub v hv'
  -- Every `Qset j` is a `q`-kernel of `D`!
  have hQ_kern' : ∀ j : Fin m, IsQKernel D q (Qset j) := by
    intro j
    constructor
    · intro u hu v hv hadj
      have hcu : c u = false := (Finset.mem_filter.mp (hQsubU j hu)).2
      have hcv : c v = false := (Finset.mem_filter.mp (hQsubU j hv)).2
      exact hc u v hadj (hcu.trans hcv.symm)
    · intro v
      have hQp_sub_Q : Qp j ⊆ Qset j := by
        intro x hx; dsimp only [Qset]; split_ifs
        · exact hx
        · exact hx
        · exact Finset.mem_insert_of_mem hx
      by_cases hdv : 2 * j.val ≤ depth v
      · let k := (depth v - 2 * j.val) % (q + 1)
        have hk_le_q : k ≤ q := by have := Nat.mod_lt (depth v - 2 * j.val) (by omega : 0 < q + 1); omega
        have hk_le_d : k ≤ depth v := by have := Nat.mod_le (depth v - 2 * j.val) (q + 1); omega
        obtain ⟨hd_u, hreach_u⟩ := hiter_depth k v hk_le_d
        refine ⟨pred^[k] v, hQp_sub_Q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩), k, hk_le_q, hreach_u⟩
        have hdiv := Nat.div_add_mod (depth v - 2 * j.val) (q + 1)
        have hdu_eq : depth (pred^[k] v) = 2 * j.val + (q + 1) * ((depth v - 2 * j.val) / (q + 1)) := by omega
        rw [hdu_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      · by_cases hc0_in : c0 ∈ Qset j
        · refine ⟨c0, hc0_in, depth v, by omega, ?_⟩
          have h := (hiter_depth (depth v) v (le_refl _)).2
          rwa [hdepth_spec v] at h
        · by_cases ht0 : t = 0
          · have hs_pos : 0 < s := by
              by_contra h0
              have hs0 : s = 0 := Nat.eq_zero_of_not_pos h0
              have hℓ0 : ℓ = 0 := by rw [hℓ_eq, hs0, ht0, zero_mul, add_zero]
              omega
            have hsq : s * (q + 1) = (s - 1) * (q + 1) + (q + 1) := by
              conv_lhs => rw [← Nat.sub_add_cancel hs_pos]
              rw [Nat.add_mul]; simp
            have hℓ_s1 : ℓ = (s - 1) * (q + 1) + (q + 1) := by rw [hℓ_eq, ht0, add_zero, hsq]
            have hjlt := j.isLt
            have hidx : (s - 1) * (q + 1) + 2 * j.val < ℓ := by omega
            let u := cyc' ⟨(s - 1) * (q + 1) + 2 * j.val, hidx⟩
            have huQ : u ∈ Qset j := hQp_sub_Q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              rw [hdepth_cyc]; dsimp only
              rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]⟩)
            have huc0 := hcyc_to_c0 _ hidx (by omega)
            have hc0v : ReachIn D (depth v) c0 v := by
              have h := (hiter_depth (depth v) v (le_refl _)).2; rwa [hdepth_spec v] at h
            exact ⟨u, huQ, ℓ - ((s - 1) * (q + 1) + 2 * j.val) + depth v, by omega, reachIn_trans huc0 hc0v⟩
          · have hj_lt : j.val < t / 2 := by
              by_contra hge
              apply hc0_in; dsimp only [Qset]; rw [if_neg ht0, if_neg hge]
              exact Finset.mem_insert_self _ _
            have hidx : s * (q + 1) + 2 * j.val < ℓ := by omega
            let u := cyc' ⟨s * (q + 1) + 2 * j.val, hidx⟩
            have huQ : u ∈ Qset j := hQp_sub_Q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              rw [hdepth_cyc]; dsimp only
              rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]⟩)
            have huc0 := hcyc_to_c0 _ hidx (by omega)
            have hc0v : ReachIn D (depth v) c0 v := by
              have h := (hiter_depth (depth v) v (le_refl _)).2; rwa [hdepth_spec v] at h
            exact ⟨u, huQ, ℓ - (s * (q + 1) + 2 * j.val) + depth v, by omega, reachIn_trans huc0 hc0v⟩
  -- Sum of cardinalities `∑ j : Fin m, (Qset j).card = U.card + r_cnt`!
  have hsum_Qp : ∑ j : Fin m, (Qp j).card = U.card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Qp, U, Finset.mem_filter]
      constructor
      · rintro ⟨j, hj⟩
        have hmod2 : depth v % 2 = 0 := by
          have hlin : depth v = 2 * (m * (depth v / (q + 1))) + 2 * j.val := by
            calc depth v = (q + 1) * (depth v / (q + 1)) + depth v % (q + 1) := (Nat.div_add_mod _ _).symm
              _ = 2 * (m * (depth v / (q + 1))) + 2 * j.val := by rw [hj, ← hm_eq]; ring
          omega
        rw [hcolor_depth _ _ rfl]; simp [hmod2]
      · intro hcv
        rw [hcolor_depth _ _ rfl] at hcv
        have hmod2 : depth v % 2 = 0 := by simp at hcv; omega
        have hmod_even : (depth v % (q + 1)) % 2 = 0 := by
          have hlin : depth v = 2 * (m * (depth v / (q + 1))) + depth v % (q + 1) := by
            calc depth v = (q + 1) * (depth v / (q + 1)) + depth v % (q + 1) := (Nat.div_add_mod _ _).symm
              _ = 2 * (m * (depth v / (q + 1))) + depth v % (q + 1) := by rw [← hm_eq]; ring
          omega
        have hlt : depth v % (q + 1) < q + 1 := Nat.mod_lt _ (by omega)
        exact ⟨⟨(depth v % (q + 1)) / 2, by omega⟩, by dsimp only; omega⟩
    · intro j₁ _ j₂ _ hne
      change Disjoint (Qp j₁) (Qp j₂)
      rw [Finset.disjoint_left]
      intro v h1 h2
      have hm1 := (Finset.mem_filter.mp h1).2
      have hm2 := (Finset.mem_filter.mp h2).2
      exact hne (Fin.ext (by omega))
  have hsum_Q : ∑ j : Fin m, (Qset j).card = U.card + r_cnt := by
    by_cases ht0 : t = 0
    · simp only [Qset, r_cnt, if_pos ht0, add_zero]; exact hsum_Qp
    · have hterm : ∀ j : Fin m, (Qset j).card = (Qp j).card + if j.val < t / 2 then 0 else 1 := by
        intro j
        dsimp only [Qset]; rw [if_neg ht0]
        by_cases hj : j.val < t / 2
        · simp [hj]
        · rw [if_neg hj, if_neg hj]
          have hc0_not : c0 ∉ Qp j := by
            simp only [Qp, Finset.mem_filter, Finset.mem_univ, true_and, hdepth_c0, Nat.zero_mod]
            have : 0 < t / 2 := by omega
            omega
          rw [Finset.card_insert_of_notMem hc0_not]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, hsum_Qp]
      congr 1
      have hcnt : (∑ j : Fin m, if j.val < t / 2 then 0 else 1) =
          (Finset.univ.filter fun j : Fin m => ¬ j.val < t / 2).card := by
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun j _ => by split_ifs <;> rfl
      rw [hcnt]
      have hcomp : (Finset.univ.filter fun j : Fin m => j.val < t / 2).card +
          (Finset.univ.filter fun j : Fin m => ¬ j.val < t / 2).card = m := by
        have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun j => j.val < t / 2)
        simpa using this
      have hlt_card : (Finset.univ.filter fun j : Fin m => j.val < t / 2).card = t / 2 := by
        have hbij : (Finset.univ.filter fun j : Fin m => j.val < t / 2) =
            (Finset.range (t / 2)).attach.image fun x => ⟨x.val, by have := Finset.mem_range.mp x.prop; omega⟩ := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach]
          constructor
          · intro hj; exact ⟨⟨j.val, Finset.mem_range.mpr hj⟩, rfl⟩
          · rintro ⟨⟨x, hx⟩, rfl⟩; exact Finset.mem_range.mp hx
        rw [hbij, Finset.card_image_of_injective _ (fun a b h => Subtype.ext (congrArg Fin.val h))]
        simp
      dsimp only [r_cnt]; rw [if_neg ht0]; omega
  -- Pigeonhole on `Fin m`: pick `j` with `m * (Qset j).card ≤ U.card + r_cnt`!
  have hex_j : ∃ j : Fin m, m * (Qset j).card ≤ U.card + r_cnt := by
    by_contra hall
    push Not at hall
    have h1 : ∑ _j : Fin m, (U.card + r_cnt) < ∑ j : Fin m, m * (Qset j).card :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm_pos⟩⟩) (fun j _ => hall j)
    rw [← Finset.mul_sum, hsum_Q, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    omega
  obtain ⟨j, hj_card⟩ := hex_j
  refine ⟨Qset j, hQ_kern' j, fun u hu => (Finset.mem_filter.mp (hQsubU j hu)).2, ?_⟩
  -- Key arithmetic identity: `ℓ + 2 * r_cnt = ceilDiv ℓ (q + 1) * (q + 1)`!
  have hceil_id : ℓ + 2 * r_cnt = ceilDiv ℓ (q + 1) * (q + 1) := by
    dsimp only [r_cnt, ceilDiv]
    by_cases ht0 : t = 0
    · rw [if_pos ht0, mul_zero, add_zero]
      have h1 : ℓ + (q + 1) - 1 = (q + 1) * s + q := by rw [hℓ_eq, ht0, add_zero, mul_comm]; omega
      rw [h1, Nat.mul_add_div (by omega : 0 < q + 1), Nat.div_eq_of_lt (by omega : q < q + 1), add_zero]
      omega
    · rw [if_neg ht0]
      have h1 : ℓ + (q + 1) - 1 = (q + 1) * (s + 1) + (t - 1) := by
        have : (q + 1) * (s + 1) = s * (q + 1) + (q + 1) := by ring
        omega
      rw [h1, Nat.mul_add_div (by omega : 0 < q + 1), Nat.div_eq_of_lt (by omega : t - 1 < q + 1), add_zero]
      have : (s + 1) * (q + 1) = s * (q + 1) + (q + 1) := by ring
      omega
  -- Now finish in `ℚ`: `m * |Q_j| ≤ |U| + r_cnt` and `ℓ ≤ 2 * |U|` => `|Q_j| ≤ 2 * (ceilDiv ℓ (q+1) / ℓ) * |U|`!
  have hℓpos : (0 : ℚ) < (ℓ : ℚ) := by positivity
  have hm_q : (2 : ℚ) * (m : ℚ) = ((q + 1 : ℕ) : ℚ) := by exact_mod_cast hm_eq
  have hU_q : (ℓ : ℚ) ≤ 2 * (U.card : ℚ) := by
    have : ℓ ≤ 2 * U.card := by omega
    exact_mod_cast this
  have hj_q : (m : ℚ) * ((Qset j).card : ℚ) ≤ (U.card : ℚ) + (r_cnt : ℚ) := by exact_mod_cast hj_card
  have hceil_q : (ℓ : ℚ) + 2 * (r_cnt : ℚ) = (ceilDiv ℓ (q + 1) : ℚ) * ((q + 1 : ℕ) : ℚ) := by
    exact_mod_cast hceil_id
  have hr_nonneg : (0 : ℚ) ≤ (r_cnt : ℚ) := Nat.cast_nonneg _
  rw [mul_div_assoc', mul_comm 2, div_mul_eq_mul_div, le_div_iff₀ hℓpos]
  have hq1_pos : (0 : ℚ) < ((q + 1 : ℕ) : ℚ) := by positivity
  suffices ((Qset j).card : ℚ) * (ℓ : ℚ) * ((q + 1 : ℕ) : ℚ) ≤
      (ceilDiv ℓ (q + 1) : ℚ) * 2 * (U.card : ℚ) * ((q + 1 : ℕ) : ℚ) by
    exact le_of_mul_le_mul_right this hq1_pos
  calc ((Qset j).card : ℚ) * (ℓ : ℚ) * ((q + 1 : ℕ) : ℚ)
      = 2 * ((m : ℚ) * ((Qset j).card : ℚ)) * (ℓ : ℚ) := by rw [← hm_q]; ring
    _ ≤ 2 * ((U.card : ℚ) + (r_cnt : ℚ)) * (ℓ : ℚ) := by nlinarith
    _ = 2 * (U.card : ℚ) * (ℓ : ℚ) + 2 * (r_cnt : ℚ) * (ℓ : ℚ) := by ring
    _ ≤ 2 * (U.card : ℚ) * (ℓ : ℚ) + 2 * (r_cnt : ℚ) * (2 * (U.card : ℚ)) := by nlinarith
    _ = ((ℓ : ℚ) + 2 * (r_cnt : ℚ)) * 2 * (U.card : ℚ) := by ring
    _ = (ceilDiv ℓ (q + 1) : ℚ) * 2 * (U.card : ℚ) * ((q + 1 : ℕ) : ℚ) := by rw [hceil_q]; ring

private lemma theorem_1_8 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (D : FinDigraph V) (q : ℕ),
      Nonempty V → 3 ≤ q → Odd q → IsSourceFree D → IsBipartite D →
      ∃ (Q : Finset V) (ℓ : ℕ), IsQKernel D q Q ∧ HasDirCycle D ℓ ∧
        (Q.card : ℚ) ≤ ((ceilDiv ℓ (q + 1) : ℚ) / (ℓ : ℚ)) * (Fintype.card V : ℚ) := by
  classical
  intro V _ _ D q hne hq3 hqOdd hsf ⟨c0, hc0⟩
  -- Pick bipartition `c` with `|U| ≤ |V \ U|`, i.e., `2 * |U| ≤ |V|`!
  let U0 := Finset.univ.filter fun v : V => c0 v = false
  let c : V → Bool := if 2 * U0.card ≤ Fintype.card V then c0 else fun v => !(c0 v)
  have hc : IsBipartition D c := by
    intro u v huv
    dsimp only [c]
    split_ifs
    · exact hc0 u v huv
    · intro h; apply hc0 u v huv; cases h1 : c0 u <;> cases h2 : c0 v <;> simp_all
  let U := Finset.univ.filter fun v : V => c v = false
  have h2U : 2 * U.card ≤ Fintype.card V := by
    dsimp only [U, c]
    split_ifs with hle
    · exact hle
    · have hsum : U0.card + (Finset.univ.filter fun v : V => (!c0 v) = false).card = Fintype.card V := by
        have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V)) (fun v => c0 v = false)
        have h2 : (Finset.univ.filter fun v : V => ¬ c0 v = false) =
            (Finset.univ.filter fun v : V => (!c0 v) = false) := by
          ext v; simp [Bool.not_eq_false]
        rw [h2, Finset.card_univ] at h1; exact h1
      change 2 * (Finset.univ.filter fun v : V => (!c0 v) = false).card ≤ Fintype.card V
      omega
  -- Pick one in-neighbor `pred v` for each `v`, forming spanning functional subdigraph `D'`!
  let pred : V → V := fun v => Classical.choose (hsf v)
  have hpred_adj : ∀ v : V, D.adj (pred v) v := fun v => Classical.choose_spec (hsf v)
  let D' : FinDigraph V :=
    { adj := fun u v => u = pred v
      loopless := fun v h => by have h1 := hpred_adj v; rw [← h] at h1; exact D.loopless v h1 }
  have hD'_sub : ∀ u v, D'.adj u v → D.adj u v := fun u v h => h ▸ hpred_adj v
  -- Decompose `V` into weak connected components of `D'` via `EquivRel` `WeakEq`!
  let WeakEq : V → V → Prop := fun u v =>
    Relation.ReflTransGen (fun x y => D'.adj x y ∨ D'.adj y x) u v
  have hWeak_refl : ∀ v, WeakEq v v := fun _ => Relation.ReflTransGen.refl
  have hWeak_symm : ∀ {u v}, WeakEq u v → WeakEq v u := fun h => by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.head (Or.symm hstep) ih
  have hWeak_trans : ∀ {u v w}, WeakEq u v → WeakEq v w → WeakEq u w := fun h1 h2 => h1.trans h2
  let compOf (v : V) : Finset V := Finset.univ.filter fun w => WeakEq v w
  let comps : Finset (Finset V) := Finset.univ.image compOf
  have hcomp_ne : ∀ C ∈ comps, C.Nonempty := by
    intro C hC
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hWeak_refl v⟩⟩
  have hcomp_closed : ∀ C ∈ comps, ∀ v ∈ C, pred v ∈ C := by
    intro C hC v hv
    obtain ⟨r0, _, rfl⟩ := Finset.mem_image.mp hC
    have hr0v := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hWeak_trans hr0v (Relation.ReflTransGen.single (Or.inr rfl))⟩
  have hcomp_weak : ∀ C ∈ comps, ∀ (u v : C),
      Relation.ReflTransGen (fun x y : C => x.val = pred y.val ∨ y.val = pred x.val) u v := by
    intro C hC ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨r0, _, rfl⟩ := Finset.mem_image.mp hC
    have hru := (Finset.mem_filter.mp hu).2
    have hrv := (Finset.mem_filter.mp hv).2
    have huv : WeakEq u v := hWeak_trans (hWeak_symm hru) hrv
    -- Lift the walk in `V` to `C` since every vertex on the walk is `WeakEq` to `r0`!
    have hlift : ∀ {a b : V} (ha : WeakEq r0 a) (hab : WeakEq a b),
        Relation.ReflTransGen (fun x y : compOf r0 => x.val = pred y.val ∨ y.val = pred x.val)
          ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
          ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hWeak_trans ha hab⟩⟩ := by
      intro a b ha hab
      induction hab with
      | refl => exact Relation.ReflTransGen.refl
      | @tail x y hax hxy ih =>
        exact Relation.ReflTransGen.tail ih hxy
    exact hlift hru huv
  -- On each component `C ∈ comps`, build a restricted unicyclic bipartite digraph `DC` and apply Theorem 1.9!
  have hcomp_sol : ∀ C ∈ comps, ∃ (QC : Finset V) (ℓC : ℕ),
      QC ⊆ C ∧ (∀ u ∈ QC, c u = false) ∧
      (∀ v ∈ C, ∃ u ∈ QC, ∃ k ≤ q, ReachIn D k u v) ∧
      HasDirCycle D ℓC ∧
      (QC.card : ℚ) ≤ 2 * ((ceilDiv ℓC (q + 1) : ℚ) / (ℓC : ℚ)) * ((C ∩ U).card : ℚ) := by
    intro C hC
    let DC : FinDigraph C :=
      { adj := fun x y => x.val = pred y.val
        loopless := fun x h => D'.loopless x.val h }
    have hDC_uni : IsUnicyclic DC := by
      refine ⟨fun y => ⟨⟨pred y.val, hcomp_closed C hC y.val y.prop⟩, rfl,
        fun x hx => Subtype.ext hx⟩, hcomp_weak C hC⟩
    have hDC_bip : IsBipartition DC (fun x : C => c x.val) :=
      fun x y hxy => hc x.val y.val (hD'_sub x.val y.val hxy)
    -- Every finite unicyclic digraph `DC` on nonempty `C` has a directed cycle!
    obtain ⟨v0, hv0⟩ := hcomp_ne C hC
    let predC : C → C := fun x => ⟨pred x.val, hcomp_closed C hC x.val x.prop⟩
    obtain ⟨a, p0, hp0, hper⟩ := functional_periodic predC ⟨v0, hv0⟩
    -- Take minimal positive period `ℓC` of `w0 := predC^[a] ⟨v0, hv0⟩`!
    let w0 : C := predC^[a] ⟨v0, hv0⟩
    have hex_per : ∃ p : ℕ, 0 < p ∧ predC^[p] w0 = w0 :=
      ⟨p0, hp0, by dsimp only [w0]; rw [← Function.iterate_add_apply, add_comm]; exact hper⟩
    let ℓC := Nat.find hex_per
    have hℓC_spec := Nat.find_spec hex_per
    have hℓC_pos : 0 < ℓC := hℓC_spec.1
    have hℓC_eq : predC^[ℓC] w0 = w0 := hℓC_spec.2
    have hℓC_min : ∀ p, 0 < p → predC^[p] w0 = w0 → ℓC ≤ p := fun p hp h => Nat.find_min' hex_per ⟨hp, h⟩
    have hℓC_ge2 : 2 ≤ ℓC := by
      by_contra hlt
      have h1 : ℓC = 1 := by omega
      rw [h1, Function.iterate_one] at hℓC_eq
      exact DC.loopless w0 (congrArg Subtype.val hℓC_eq.symm)
    -- Cycle `i ↦ predC^[ℓC - i.val] w0` goes in the forward direction `DC.adj (f i) (f (i + 1))`!
    let fC : Fin ℓC → C := fun i => predC^[ℓC - i.val] w0
    have hfC_inj : Function.Injective fC := by
      intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne (fun hv => hne (Fin.ext hv)) with hlt | hgt
      · have h1 : predC^[j.val - i.val] w0 = w0 := by
          have : predC^[i.val] (predC^[ℓC - i.val] w0) = predC^[i.val] (predC^[ℓC - j.val] w0) :=
            congrArg (predC^[i.val]) hij
          rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt i.isLt), hℓC_eq,
              ← Function.iterate_add_apply] at this
          have h2 : predC^[j.val - i.val] (predC^[i.val + (ℓC - j.val)] w0) = predC^[j.val - i.val] w0 :=
            congrArg (predC^[j.val - i.val]) this.symm
          rw [← Function.iterate_add_apply, show (j.val - i.val) + (i.val + (ℓC - j.val)) = ℓC by omega,
              hℓC_eq] at h2
          exact h2.symm
        have := hℓC_min (j.val - i.val) (by omega) h1; omega
      · have h1 : predC^[i.val - j.val] w0 = w0 := by
          have : predC^[j.val] (predC^[ℓC - j.val] w0) = predC^[j.val] (predC^[ℓC - i.val] w0) :=
            congrArg (predC^[j.val]) hij.symm
          rw [← Function.iterate_add_apply, Nat.add_sub_of_le (le_of_lt j.isLt), hℓC_eq,
              ← Function.iterate_add_apply] at this
          have h2 : predC^[i.val - j.val] (predC^[j.val + (ℓC - i.val)] w0) = predC^[i.val - j.val] w0 :=
            congrArg (predC^[i.val - j.val]) this.symm
          rw [← Function.iterate_add_apply, show (i.val - j.val) + (j.val + (ℓC - i.val)) = ℓC by omega,
              hℓC_eq] at h2
          exact h2.symm
        have := hℓC_min (i.val - j.val) (by omega) h1; omega
    have hfC_adj : ∀ i : Fin ℓC, DC.adj (fC i) (fC ⟨(i.val + 1) % ℓC, Nat.mod_lt _ (by omega)⟩) := by
      intro i
      show (fC i).val = pred (fC ⟨(i.val + 1) % ℓC, Nat.mod_lt _ (by omega)⟩).val
      have : fC i = predC (fC ⟨(i.val + 1) % ℓC, Nat.mod_lt _ (by omega)⟩) := by
        dsimp only [fC]
        by_cases hlt : i.val + 1 < ℓC
        · rw [Nat.mod_eq_of_lt hlt, show ℓC - i.val = (ℓC - (i.val + 1)) + 1 by omega,
              Function.iterate_succ_apply']
        · have heq : i.val + 1 = ℓC := by omega
          rw [heq, Nat.mod_self, Nat.sub_zero, hℓC_eq, show ℓC - i.val = 1 by omega, Function.iterate_one]
      exact congrArg Subtype.val this
    have hDC_cyc : HasDirCycle DC ℓC := ⟨hℓC_ge2, fC, hfC_inj, hfC_adj⟩
    obtain ⟨QCsub, hQC_kern, hQC_col, hQC_card⟩ :=
      theorem_1_9 C DC (fun x => c x.val) ℓC q hq3 hqOdd hDC_uni hDC_bip hDC_cyc
    let QC : Finset V := QCsub.image Subtype.val
    have hQC_card_eq : QC.card = QCsub.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hCU_card : (Finset.univ.filter fun x : C => c x.val = false).card = (C ∩ U).card := by
      have hEq : (Finset.univ.filter fun x : C => c x.val = false).image Subtype.val = C ∩ U := by
        ext v; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, U]
        constructor
        · rintro ⟨⟨x, hx⟩, hcx, rfl⟩; exact ⟨hx, hcx⟩
        · rintro ⟨hvC, hcv⟩; exact ⟨⟨v, hvC⟩, hcv, rfl⟩
      rw [← hEq, Finset.card_image_of_injective _ Subtype.val_injective]
    refine ⟨QC, ℓC, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv; exact x.prop
    · intro u hu; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu; exact hQC_col x hx
    · intro v hv
      obtain ⟨x, hx, k, hk, hr⟩ := hQC_kern.2 ⟨v, hv⟩
      have hrD : ReachIn D k x.val v := by
        have hlift : ∀ {k : ℕ} {a b : C}, ReachIn DC k a b → ReachIn D k a.val b.val := by
          intro k a b hab
          induction hab with
          | zero _ => exact ReachIn.zero _
          | succ ha _ ih => exact ReachIn.succ (hD'_sub _ _ ha) ih
        exact hlift hr
      exact ⟨x.val, Finset.mem_image_of_mem _ hx, k, hk, hrD⟩
    · exact ⟨hℓC_ge2, fun i => (fC i).val, Subtype.val_injective.comp hfC_inj,
        fun i => hD'_sub _ _ (hfC_adj i)⟩
    · rw [hQC_card_eq, ← hCU_card]; exact hQC_card
  -- Pick `QC, ℓC` for each `C ∈ comps` and take `Q = ⋃_{C ∈ comps} QC`!
  let pickQ (C : Finset V) : Finset V := if hC : C ∈ comps then Classical.choose (hcomp_sol C hC) else ∅
  let pickL (C : Finset V) : ℕ :=
    if hC : C ∈ comps then Classical.choose (Classical.choose_spec (hcomp_sol C hC)) else 2
  have hpick : ∀ C (hC : C ∈ comps),
      pickQ C ⊆ C ∧ (∀ u ∈ pickQ C, c u = false) ∧
      (∀ v ∈ C, ∃ u ∈ pickQ C, ∃ k ≤ q, ReachIn D k u v) ∧
      HasDirCycle D (pickL C) ∧
      ((pickQ C).card : ℚ) ≤ 2 * ((ceilDiv (pickL C) (q + 1) : ℚ) / (pickL C : ℚ)) * ((C ∩ U).card : ℚ) := by
    intro C hC
    simp only [pickQ, pickL, dif_pos hC]
    exact Classical.choose_spec (Classical.choose_spec (hcomp_sol C hC))
  let Q : Finset V := comps.biUnion pickQ
  have hcomps_ne : comps.Nonempty := by
    obtain ⟨v0⟩ := hne
    exact ⟨compOf v0, Finset.mem_image_of_mem _ (Finset.mem_univ v0)⟩
  -- Pick `Cmax ∈ comps` maximizing `ceilDiv (pickL C) (q + 1) / pickL C`!
  let ratio (C : Finset V) : ℚ := (ceilDiv (pickL C) (q + 1) : ℚ) / (pickL C : ℚ)
  obtain ⟨Cmax, hCmax_mem, hCmax_ge⟩ := Finset.exists_max_image comps ratio hcomps_ne
  refine ⟨Q, pickL Cmax, ⟨?_, ?_⟩, (hpick Cmax hCmax_mem).2.2.2.1, ?_⟩
  · intro u hu v hv hadj
    obtain ⟨C1, hC1, hu1⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨C2, hC2, hv2⟩ := Finset.mem_biUnion.mp hv
    have hcu := (hpick C1 hC1).2.1 u hu1
    have hcv := (hpick C2 hC2).2.1 v hv2
    exact hc u v hadj (hcu.trans hcv.symm)
  · intro v
    have hCv : compOf v ∈ comps := Finset.mem_image_of_mem _ (Finset.mem_univ v)
    have hvC : v ∈ compOf v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hWeak_refl v⟩
    obtain ⟨u, hu, k, hk, hr⟩ := (hpick (compOf v) hCv).2.2.1 v hvC
    exact ⟨u, Finset.mem_biUnion.mpr ⟨compOf v, hCv, hu⟩, k, hk, hr⟩
  · -- Sum bounds over disjoint components!
    have hdisj_comps : (comps : Set (Finset V)).PairwiseDisjoint id := by
      intro C1 hC1 C2 hC2 hneC
      obtain ⟨v1, _, rfl⟩ := Finset.mem_image.mp hC1
      obtain ⟨v2, _, rfl⟩ := Finset.mem_image.mp hC2
      change Disjoint (compOf v1) (compOf v2)
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      apply hneC
      ext x
      simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2 ⊢
      have h12 : WeakEq v1 v2 := hWeak_trans hw1 (hWeak_symm hw2)
      exact ⟨fun h => hWeak_trans (hWeak_symm h12) h, fun h => hWeak_trans h12 h⟩
    have hU_sum : ∑ C ∈ comps, (C ∩ U).card = U.card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext v
        simp only [Finset.mem_biUnion, Finset.mem_inter]
        constructor
        · rintro ⟨_, _, _, hvU⟩; exact hvU
        · intro hvU
          exact ⟨compOf v, Finset.mem_image_of_mem _ (Finset.mem_univ v),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hWeak_refl v⟩, hvU⟩
      · intro C1 hC1 C2 hC2 hneC
        exact (hdisj_comps hC1 hC2 hneC).mono Finset.inter_subset_left Finset.inter_subset_left
    have hQ_le : (Q.card : ℚ) ≤ ∑ C ∈ comps, ((pickQ C).card : ℚ) := by
      have := Finset.card_biUnion_le (s := comps) (t := pickQ)
      exact_mod_cast this
    have hratio_nonneg : 0 ≤ ratio Cmax := by
      dsimp only [ratio]; positivity
    have h2U_q : 2 * (U.card : ℚ) ≤ (Fintype.card V : ℚ) := by exact_mod_cast h2U
    calc (Q.card : ℚ)
        ≤ ∑ C ∈ comps, ((pickQ C).card : ℚ) := hQ_le
      _ ≤ ∑ C ∈ comps, (2 * ratio C * ((C ∩ U).card : ℚ)) :=
          Finset.sum_le_sum fun C hC => (hpick C hC).2.2.2.2
      _ ≤ ∑ C ∈ comps, (2 * ratio Cmax * ((C ∩ U).card : ℚ)) :=
          Finset.sum_le_sum fun C hC => by
            have hle := hCmax_ge C hC
            have hnn : (0 : ℚ) ≤ ((C ∩ U).card : ℚ) := Nat.cast_nonneg _
            nlinarith
      _ = 2 * ratio Cmax * ∑ C ∈ comps, ((C ∩ U).card : ℚ) := (Finset.mul_sum _ _ _).symm
      _ = 2 * ratio Cmax * (U.card : ℚ) := by
          congr 1; exact_mod_cast hU_sum
      _ = ratio Cmax * (2 * (U.card : ℚ)) := by ring
      _ ≤ ratio Cmax * (Fintype.card V : ℚ) :=
          mul_le_mul_of_nonneg_left h2U_q hratio_nonneg

theorem main_proof : type_of% @OMA.S_arxiv_2608_00825.main :=
  ⟨theorem_1_2, theorem_1_3, theorem_1_6, theorem_1_7, theorem_1_9, theorem_1_8⟩

end OMA.P_arxiv_2608_00825

theorem OMA.solution : type_of% @OMA.S_arxiv_2608_00825.main :=
  OMA.P_arxiv_2608_00825.main_proof
