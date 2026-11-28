import OMAReductions.R_Erdos599_erdos_599_variants_aharoni_berger_R1

/-!
# Maximal wave existence in arbitrary graphs

Proves `Erdos599.erdos_599.variants.aharoni_berger.R1.H1` (Aharoni-Berger Lemma 3.5 /
Diestel Lemma 8.4.3) via Zorn's lemma on waves ordered by separation and path extension.
-/

namespace OMA.Erdos599H1

open SimpleGraph
open scoped Classical

/-- Every nonempty walk containing a vertex of `S` has a last vertex in `S`, giving a suffix walk
whose tail avoids `S`. -/
lemma exists_last_mem {V : Type} {G : SimpleGraph V} {u v : V}
    (q : G.Walk u v) (hq : q.IsPath) (S : Set V) (h : ∃ w ∈ q.support, w ∈ S) :
    ∃ (w : V) (_ : w ∈ S) (q₂ : G.Walk w v),
      q₂.IsPath ∧ (∀ z ∈ q₂.support, z ∈ q.support) ∧ (∀ z ∈ q₂.support.tail, z ∉ S) := by
  induction q with
  | nil =>
    obtain ⟨w, hw, hwS⟩ := h
    simp only [Walk.support_nil, List.mem_singleton] at hw
    subst hw
    exact ⟨w, hwS, Walk.nil, Walk.IsPath.nil, fun z hz => by simpa using hz, fun z hz => by simp at hz⟩
  | @cons a b c hab q' ih =>
    have hq' : q'.IsPath := hq.of_cons
    by_cases h' : ∃ w ∈ q'.support, w ∈ S
    · obtain ⟨w, hwS, q₂, hq₂, hsub, htail⟩ := ih hq' h'
      refine ⟨w, hwS, q₂, hq₂, ?_, htail⟩
      intro z hz
      exact List.mem_cons_of_mem a (hsub z hz)
    · push Not at h'
      obtain ⟨w, hw, hwS⟩ := h
      rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw'
      · exact ⟨w, hwS, Walk.cons hab q', hq, fun z hz => hz,
          fun z hz => h' z (by simpa [Walk.support_cons] using hz)⟩
      · exact (h' w hw' hwS).elim

/-- Lifting a walk in `G` whose support lies in `s` to a walk in `G.induce s`. -/
def liftWalk {V : Type} {G : SimpleGraph V} {s : Set V} :
    ∀ {u v : V} (q : G.Walk u v), (∀ z ∈ q.support, z ∈ s) →
      ∀ (hu : u ∈ s) (hv : v ∈ s), (G.induce s).Walk ⟨u, hu⟩ ⟨v, hv⟩
  | _, _, Walk.nil, _, hu, hv => by
    have : (⟨_, hu⟩ : s) = ⟨_, hv⟩ := Subtype.ext rfl
    exact Walk.nil.copy rfl this
  | a, _, Walk.cons (v := b) hab q', hmem, hu, hv =>
    have hb : b ∈ s := hmem b (by simp [Walk.support_cons])
    have hmem' : ∀ z ∈ q'.support, z ∈ s := fun z hz => hmem z (List.mem_cons_of_mem a hz)
    Walk.cons (v := ⟨b, hb⟩) (show (G.induce s).Adj ⟨a, hu⟩ ⟨b, hb⟩ from hab) (liftWalk q' hmem' hb hv)

lemma liftWalk_support_map {V : Type} {G : SimpleGraph V} {s : Set V}
    {u v : V} (q : G.Walk u v) (hmem : ∀ z ∈ q.support, z ∈ s) (hu : u ∈ s) (hv : v ∈ s) :
    (liftWalk q hmem hu hv).support.map Subtype.val = q.support := by
  induction q with
  | nil => simp [liftWalk]
  | @cons a b c hab q' ih =>
    have hb : b ∈ s := hmem b (by simp [Walk.support_cons])
    have hmem' : ∀ z ∈ q'.support, z ∈ s := fun z hz => hmem z (List.mem_cons_of_mem a hz)
    simp only [liftWalk, Walk.support_cons, List.map_cons]
    exact congrArg (List.cons a) (ih hmem' hb hv)

lemma liftWalk_isPath {V : Type} {G : SimpleGraph V} {s : Set V}
    {u v : V} (q : G.Walk u v) (hq : q.IsPath) (hmem : ∀ z ∈ q.support, z ∈ s)
    (hu : u ∈ s) (hv : v ∈ s) :
    (liftWalk q hmem hu hv).IsPath := by
  rw [Walk.isPath_def]
  have hnd : ((liftWalk q hmem hu hv).support.map Subtype.val).Nodup := by
    rw [liftWalk_support_map]
    exact hq.support_nodup
  exact hnd.of_map Subtype.val

lemma support_map_induce {V : Type} {G : SimpleGraph V} {s : Set V}
    {u v : s} (q : (G.induce s).Walk u v) :
    (q.map (Embedding.induce s).toHom).support = q.support.map Subtype.val := by
  rw [Walk.support_map]
  rfl

lemma isPath_map_induce {V : Type} {G : SimpleGraph V} {s : Set V}
    {u v : s} {q : (G.induce s).Walk u v} (hq : q.IsPath) :
    (q.map (Embedding.induce s).toHom).IsPath := by
  rw [Walk.isPath_def, support_map_induce]
  exact hq.support_nodup.map Subtype.val_injective

lemma append_isPath_of_disjoint_tail {V : Type} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} {q : G.Walk v w} (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : ∀ z ∈ q.support.tail, z ∉ p.support) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append]
  rw [List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro x hx y hy hxy
  subst hxy
  exact hdisj x hy hx

/-- The set of vertices separated from `B` by `X`. -/
def Before {V : Type} (G : SimpleGraph V) (B X : Set V) : Set V :=
  {v | ∀ b ∈ B, ∀ q : G.Walk v b, q.IsPath → ∃ u ∈ q.support, u ∈ X}

lemma subset_before {V : Type} {G : SimpleGraph V} {B X : Set V} :
    X ⊆ Before G B X := by
  intro x hx b _ q _
  exact ⟨x, q.start_mem_support, hx⟩

lemma before_mono {V : Type} {G : SimpleGraph V} {B X Y : Set V}
    (hXY : X ⊆ Before G B Y) : Before G B X ⊆ Before G B Y := by
  intro v hv b hb q hq
  obtain ⟨x, hx, hxX⟩ := hv b hb q hq
  let q₂ := q.dropUntil x hx
  have hq₂ : q₂.IsPath := hq.dropUntil hx
  obtain ⟨y, hy, hyY⟩ := hXY hxX b hb q₂ hq₂
  exact ⟨y, Walk.support_dropUntil_subset_support q hx hy, hyY⟩

/-- A wave in `(G, A, B)` indexed by its terminal set `X`. -/
structure Wave {V : Type} (G : SimpleGraph V) (A B : Set V) where
  X : Set V
  a : ∀ x : V, x ∈ X → V
  a_mem : ∀ x (hx : x ∈ X), a x hx ∈ A
  p : ∀ x (hx : x ∈ X), G.Walk (a x hx) x
  isPath : ∀ x (hx : x ∈ X), (p x hx).IsPath
  disj : ∀ x₁ (hx₁ : x₁ ∈ X) x₂ (hx₂ : x₂ ∈ X), x₁ ≠ x₂ →
    Disjoint {v | v ∈ (p x₁ hx₁).support} {v | v ∈ (p x₂ hx₂).support}
  sep : A ⊆ Before G B X

/-- The set of all vertices covered by the paths of a wave. -/
def Wave.verts {V : Type} {G : SimpleGraph V} {A B : Set V} (W : Wave G A B) : Set V :=
  {v | ∃ x, ∃ hx : x ∈ W.X, v ∈ (W.p x hx).support}

lemma Wave.X_subset_verts {V : Type} {G : SimpleGraph V} {A B : Set V} (W : Wave G A B) :
    W.X ⊆ W.verts := by
  intro x hx
  exact ⟨x, hx, (W.p x hx).end_mem_support⟩

/-- For any wave `W` and any path `q` from `v` to `B` whose last vertex in `W.verts` is `w`,
that last vertex `w` must lie in `W.X`. -/
lemma Wave.last_in_verts_mem_X {V : Type} {G : SimpleGraph V} {A B : Set V}
    (W : Wave G A B) {w b : V} (hb : b ∈ B) (hw : w ∈ W.verts)
    (q₂ : G.Walk w b) (htail : ∀ z ∈ q₂.support.tail, z ∉ W.verts) :
    w ∈ W.X := by
  by_contra hwX
  obtain ⟨x, hx, hwx⟩ := hw
  let pre := (W.p x hx).takeUntil w hwx
  have hpre_sub : ∀ z ∈ pre.support, z ∈ (W.p x hx).support :=
    fun z hz => Walk.support_takeUntil_subset_support (W.p x hx) hwx hz
  have hpre_no_X : ∀ z ∈ pre.support, z ∉ W.X := by
    intro z hz hzX
    by_cases hzx : z = x
    · rw [hzx] at hz
      have hx_last : x = w := by
        have hnd := (W.isPath x hx).support_nodup
        have happ : pre.support ++ ((W.p x hx).dropUntil w hwx).support.tail = (W.p x hx).support := by
          rw [← Walk.support_append, Walk.take_spec]
        have hnd_app : (pre.support ++ ((W.p x hx).dropUntil w hwx).support.tail).Nodup := by
          rw [happ]; exact hnd
        by_contra hne
        have htail_mem : x ∈ ((W.p x hx).dropUntil w hwx).support.tail := by
          have hmem_end : x ∈ ((W.p x hx).dropUntil w hwx).support := Walk.end_mem_support _
          rw [← Walk.cons_tail_support, List.mem_cons] at hmem_end
          rcases hmem_end with hEq | htl
          · exact (hne hEq).elim
          · exact htl
        exact (List.nodup_append.mp hnd_app).2.2 x hz x htail_mem rfl
      exact hwX (hx_last ▸ hx)
    · exact Set.disjoint_left.mp (W.disj x hx z hzX (Ne.symm hzx))
        (hpre_sub z hz) (W.p z hzX).end_mem_support
  have hq₂_no_X : ∀ z ∈ q₂.support, z ∉ W.X := by
    intro z hz hzX
    rw [← Walk.cons_tail_support, List.mem_cons] at hz
    rcases hz with rfl | htl
    · exact hwX hzX
    · exact htail z htl (W.X_subset_verts hzX)
  let walk : G.Walk (W.a x hx) b := pre.append q₂
  have hwalk_no_X : ∀ z ∈ walk.support, z ∉ W.X := by
    intro z hz
    rw [Walk.support_append, List.mem_append] at hz
    rcases hz with h1 | h2
    · exact hpre_no_X z h1
    · exact hq₂_no_X z (List.mem_of_mem_tail h2)
  obtain ⟨u, hu, huX⟩ := W.sep (W.a_mem x hx) b hb walk.toPath.1 walk.toPath.2
  exact hwalk_no_X u (Walk.support_toPath_subset_support walk hu) huX

/-- Partial order (preorder) on waves:
1. `W₁.X ⊆ Before G B W₂.X`,
2. `W₂.X ∩ Before G B W₁.X ⊆ W₁.X`,
3. Paths ending at a common terminal coincide,
4. Every path of `W₂` extends a path of `W₁`. -/
def WaveLE {V : Type} {G : SimpleGraph V} {A B : Set V} (W₁ W₂ : Wave G A B) : Prop :=
  W₁.X ⊆ Before G B W₂.X ∧
  (∀ y ∈ W₂.X, y ∈ Before G B W₁.X → y ∈ W₁.X) ∧
  (∀ y (hy₁ : y ∈ W₁.X) (hy₂ : y ∈ W₂.X), (W₂.p y hy₂).support = (W₁.p y hy₁).support) ∧
  (∀ y (hy₂ : y ∈ W₂.X), ∃ x, ∃ hx₁ : x ∈ W₁.X, (W₁.p x hx₁).support <+: (W₂.p y hy₂).support)

instance {V : Type} {G : SimpleGraph V} {A B : Set V} : Preorder (Wave G A B) where
  le := WaveLE
  le_refl W := ⟨subset_before, fun _ hy _ => hy, fun _ _ _ => rfl,
    fun y hy => ⟨y, hy, List.prefix_refl _⟩⟩
  le_trans W₁ W₂ W₃ h₁₂ h₂₃ := by
    refine ⟨h₁₂.1.trans (before_mono h₂₃.1), ?_, ?_, ?_⟩
    · intro z hz₃ hzB₁
      have hz₂ : z ∈ W₂.X := h₂₃.2.1 z hz₃ (before_mono h₁₂.1 hzB₁)
      exact h₁₂.2.1 z hz₂ hzB₁
    · intro z hz₁ hz₃
      have hz₂ : z ∈ W₂.X := h₂₃.2.1 z hz₃ (h₁₂.1 hz₁)
      exact (h₂₃.2.2.1 z hz₂ hz₃).trans (h₁₂.2.2.1 z hz₁ hz₂)
    · intro z hz₃
      obtain ⟨y, hy₂, hyz⟩ := h₂₃.2.2.2 z hz₃
      obtain ⟨x, hx₁, hxy⟩ := h₁₂.2.2.2 y hy₂
      exact ⟨x, hx₁, hxy.trans hyz⟩

/-- The trivial wave consisting of length-0 paths at `A`. -/
def trivialWave {V : Type} (G : SimpleGraph V) (A B : Set V) : Wave G A B where
  X := A
  a x _ := x
  a_mem _ hx := hx
  p _ _ := Walk.nil
  isPath _ _ := Walk.IsPath.nil
  disj x₁ _ x₂ _ hne := by
    rw [Set.disjoint_left]
    intro v hv₁ hv₂
    simp only [Set.mem_ofPred_eq, Walk.support_nil, List.mem_singleton] at hv₁ hv₂
    exact hne (hv₁.symm.trans hv₂)
  sep := subset_before

/-- Along a chain of waves, membership `x ∈ W.X` is convex (interval-shaped). -/
lemma chain_mem_between {V : Type} {G : SimpleGraph V} {A B : Set V}
    {W₀ W W₁ : Wave G A B} (h0 : W₀ ≤ W) (h1 : W ≤ W₁)
    {x : V} (hx₀ : x ∈ W₀.X) (hx₁ : x ∈ W₁.X) : x ∈ W.X :=
  h1.2.1 x hx₁ (h0.1 hx₀)

/-- Along a nonempty chain `C`, every finite vertex list `L` that meets `W.X` for all `W ∈ C` above
some `W₀ ∈ C` must contain a vertex that is eventually in `W.X` for all large `W ∈ C`. -/
lemma chain_exists_eventual {V : Type} {G : SimpleGraph V} {A B : Set V}
    {C : Set (Wave G A B)} (hC : IsChain (· ≤ ·) C) {W₀ : Wave G A B} (hW₀ : W₀ ∈ C)
    (L : List V) (hL : ∀ W ∈ C, W₀ ≤ W → ∃ v ∈ L, v ∈ W.X) :
    ∃ v ∈ L, ∃ W₁ ∈ C, ∀ W ∈ C, W₁ ≤ W → v ∈ W.X := by
  by_contra hnone
  push Not at hnone
  have hnot_cof : ∀ v ∈ L, ∃ W ∈ C, W₀ ≤ W ∧ ∀ W' ∈ C, W ≤ W' → v ∉ W'.X := by
    intro v hv
    by_contra hcof
    push Not at hcof
    obtain ⟨W₁, hW₁C, hW01, hv1⟩ := hcof W₀ hW₀ le_rfl
    obtain ⟨W, hWC, hW1W, hvW⟩ := hnone v hv W₁ hW₁C
    obtain ⟨W', hW'C, hWW', hv'⟩ := hcof W hWC (hW01.trans hW1W)
    exact hvW (chain_mem_between hW1W hWW' hv1 hv')
  have hmax : ∀ M : List V, (∀ v ∈ M, ∃ W ∈ C, W₀ ≤ W ∧ ∀ W' ∈ C, W ≤ W' → v ∉ W'.X) →
      ∃ Wm ∈ C, W₀ ≤ Wm ∧ ∀ W' ∈ C, Wm ≤ W' → ∀ v ∈ M, v ∉ W'.X := by
    intro M
    induction M with
    | nil =>
      intro _
      exact ⟨W₀, hW₀, le_rfl, fun _ _ _ _ h => by simp at h⟩
    | cons a t ih =>
      intro hM
      obtain ⟨Wa, hWaC, hW0a, haWa⟩ := hM a (List.mem_cons_self ..)
      obtain ⟨Wt, hWtC, hW0t, ht⟩ := ih (fun v hv => hM v (List.mem_cons_of_mem a hv))
      rcases hC.total hWaC hWtC with hle | hle
      · refine ⟨Wt, hWtC, hW0t, fun W' hW'C hWtW' v hv => ?_⟩
        rw [List.mem_cons] at hv
        rcases hv with rfl | hvt
        · exact haWa W' hW'C (hle.trans hWtW')
        · exact ht W' hW'C hWtW' v hvt
      · refine ⟨Wa, hWaC, hW0a, fun W' hW'C hWaW' v hv => ?_⟩
        rw [List.mem_cons] at hv
        rcases hv with rfl | hvt
        · exact haWa W' hW'C hWaW'
        · exact ht W' hW'C (hle.trans hWaW') v hvt
  obtain ⟨Wm, hWmC, hW0m, hnone_m⟩ := hmax L hnot_cof
  obtain ⟨v, hvL, hvWm⟩ := hL Wm hWmC hW0m
  exact hnone_m Wm hWmC le_rfl v hvL hvWm

/-- Every chain of waves has an upper bound. -/
lemma chain_bddAbove {V : Type} {G : SimpleGraph V} {A B : Set V}
    (C : Set (Wave G A B)) (hC : IsChain (· ≤ ·) C) :
    ∃ W : Wave G A B, ∀ W' ∈ C, W' ≤ W := by
  by_cases hne : C.Nonempty
  · obtain ⟨W₀, hW₀⟩ := hne
    let Xstar : Set V := {x | ∃ W₁ ∈ C, ∀ W ∈ C, W₁ ≤ W → x ∈ W.X}
    -- For each x in Xstar, choose a witnessing wave in C
    have hchoose : ∀ x, x ∈ Xstar → ∃ W₁ ∈ C, ∀ W ∈ C, W₁ ≤ W → x ∈ W.X := fun _ hx => hx
    let wit (x : V) (hx : x ∈ Xstar) : Wave G A B := Classical.choose (hchoose x hx)
    have hwit_mem (x : V) (hx : x ∈ Xstar) : wit x hx ∈ C :=
      (Classical.choose_spec (hchoose x hx)).1
    have hwit_ev (x : V) (hx : x ∈ Xstar) : ∀ W ∈ C, wit x hx ≤ W → x ∈ W.X :=
      (Classical.choose_spec (hchoose x hx)).2
    have hwit_X (x : V) (hx : x ∈ Xstar) : x ∈ (wit x hx).X :=
      hwit_ev x hx (wit x hx) (hwit_mem x hx) le_rfl
    have hsupp_eq (x : V) (hx : x ∈ Xstar) (W : Wave G A B) (hWC : W ∈ C) (hxW : x ∈ W.X) :
        ((wit x hx).p x (hwit_X x hx)).support = (W.p x hxW).support := by
      rcases hC.total (hwit_mem x hx) hWC with hle | hle
      · exact (hle.2.2.1 x (hwit_X x hx) hxW).symm
      · exact hle.2.2.1 x hxW (hwit_X x hx)
    let Wstar : Wave G A B := {
      X := Xstar
      a := fun x hx => (wit x hx).a x (hwit_X x hx)
      a_mem := fun x hx => (wit x hx).a_mem x (hwit_X x hx)
      p := fun x hx => (wit x hx).p x (hwit_X x hx)
      isPath := fun x hx => (wit x hx).isPath x (hwit_X x hx)
      disj := by
        intro x₁ hx₁ x₂ hx₂ hne12
        rcases hC.total (hwit_mem x₁ hx₁) (hwit_mem x₂ hx₂) with hle | hle
        · have hx₁' : x₁ ∈ (wit x₂ hx₂).X := hwit_ev x₁ hx₁ _ (hwit_mem x₂ hx₂) hle
          have h1 := hsupp_eq x₁ hx₁ (wit x₂ hx₂) (hwit_mem x₂ hx₂) hx₁'
          have hd := (wit x₂ hx₂).disj x₁ hx₁' x₂ (hwit_X x₂ hx₂) hne12
          simpa [h1] using hd
        · have hx₂' : x₂ ∈ (wit x₁ hx₁).X := hwit_ev x₂ hx₂ _ (hwit_mem x₁ hx₁) hle
          have h2 := hsupp_eq x₂ hx₂ (wit x₁ hx₁) (hwit_mem x₁ hx₁) hx₂'
          have hd := (wit x₁ hx₁).disj x₁ (hwit_X x₁ hx₁) x₂ hx₂' hne12
          simpa [h2] using hd
      sep := by
        intro a ha b hb q hq
        exact chain_exists_eventual hC hW₀ q.support (fun W _ _ => W.sep ha b hb q hq)
    }
    refine ⟨Wstar, ?_⟩
    intro W hWC
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- W.X ⊆ Before G B Xstar
      intro x hx b hb q hq
      exact chain_exists_eventual hC hWC q.support (fun W' _ hle => hle.1 hx b hb q hq)
    · -- Xstar ∩ Before G B W.X ⊆ W.X
      intro x hxstar hxBW
      rcases hC.total (hwit_mem x hxstar) hWC with hle | hle
      · exact hwit_ev x hxstar W hWC hle
      · exact hle.2.1 x (hwit_X x hxstar) hxBW
    · -- Common terminal paths agree
      intro y hyW hystar
      exact hsupp_eq y hystar W hWC hyW
    · -- Every path of Wstar extends a path of W
      intro y hystar
      rcases hC.total (hwit_mem y hystar) hWC with hle | hle
      · have hyW : y ∈ W.X := hwit_ev y hystar W hWC hle
        refine ⟨y, hyW, ?_⟩
        rw [hsupp_eq y hystar W hWC hyW]
      · exact hle.2.2.2 y (hwit_X y hystar)
  · refine ⟨trivialWave G A B, ?_⟩
    intro W' hW'
    exact (hne ⟨W', hW'⟩).elim

/-- If a wave `U` in the after-wave graph `(G', X', B')` has `X' ⊆ Set.range t`, then
`Set.range t = X'`. -/
lemma range_eq_of_subset_range {V' : Type} {G' : SimpleGraph V'} {X' : Set V'}
    {κ : Type} {s t : κ → V'} {r : ∀ k, G'.Walk (s k) (t k)}
    (hs : ∀ k, s k ∈ X')
    (hdisj : Pairwise fun k₁ k₂ => Disjoint {v | v ∈ (r k₁).support} {v | v ∈ (r k₂).support})
    (hsub : X' ⊆ Set.range t) :
    Set.range t = X' := by
  apply Set.Subset.antisymm _ hsub
  rintro _ ⟨k₀, rfl⟩
  obtain ⟨k₁, hk₁⟩ := hsub (hs k₀)
  have heq : k₀ = k₁ := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne)
      (r k₀).start_mem_support (hk₁ ▸ (r k₁).end_mem_support)
  rw [← heq] at hk₁
  rw [hk₁]
  exact hs k₀

/-- Composing a wave `W` with a non-trivial wave `U` in the after-wave graph produces a wave `W₂`
with `W ≤ W₂` and `W₂.X ≠ W.X`. -/
lemma extend_wave {V : Type} {G : SimpleGraph V} {A B : Set V}
    (W : Wave G A B)
    (κ : Type)
    (s t : κ → {v : V // v ∈ W.X ∨ v ∉ W.verts})
    (r : ∀ k, (G.induce {v : V | v ∈ W.X ∨ v ∉ W.verts}).Walk (s k) (t k))
    (hs : ∀ k, (s k).1 ∈ W.X)
    (hr_path : ∀ k, (r k).IsPath)
    (hr_disj : Pairwise fun k₁ k₂ => Disjoint {v | v ∈ (r k₁).support} {v | v ∈ (r k₂).support})
    (hr_sep : ∀ x' : {v : V // v ∈ W.X ∨ v ∉ W.verts}, x'.1 ∈ W.X →
      ∀ b' : {v : V // v ∈ W.X ∨ v ∉ W.verts}, b'.1 ∈ B →
        ∀ q : (G.induce {v : V | v ∈ W.X ∨ v ∉ W.verts}).Walk x' b', q.IsPath →
          ∃ v ∈ q.support, v ∈ Set.range t)
    (hne : Set.range t ≠ {v : {v : V // v ∈ W.X ∨ v ∉ W.verts} | v.1 ∈ W.X}) :
    ∃ W₂ : Wave G A B, W ≤ W₂ ∧ W₂.X ≠ W.X := by
  let V' : Set V := {v | v ∈ W.X ∨ v ∉ W.verts}
  let G' : SimpleGraph V' := G.induce V'
  let X' : Set V' := {v : V' | v.1 ∈ W.X}
  -- Filtered terminal set: keep terminals in W.X or outside Before G B W.X
  let T : Set V := {v | ∃ k, (t k).1 = v}
  let T' : Set V := {v | v ∈ T ∧ (v ∈ W.X ∨ v ∉ Before G B W.X)}
  have hT'_ne : T' ≠ W.X := by
    intro heq
    apply hne
    apply range_eq_of_subset_range (r := r) hs hr_disj
    intro x' hx'
    have hxT' : x'.1 ∈ T' := heq.symm ▸ hx'
    obtain ⟨k, hk⟩ := hxT'.1
    exact ⟨k, Subtype.ext hk⟩
  -- For each k, take the suffix of r k from its last vertex in X'
  have hlast : ∀ k, ∃ (sk' : V') (_ : sk' ∈ X') (rk' : G'.Walk sk' (t k)),
      rk'.IsPath ∧ (∀ z ∈ rk'.support, z ∈ (r k).support) ∧
      (∀ z ∈ rk'.support.tail, z ∉ X') := fun k =>
    exists_last_mem (r k) (hr_path k) X' ⟨s k, (r k).start_mem_support, hs k⟩
  let sk' (k : κ) : V' := Classical.choose (hlast k)
  have hsk'_X (k : κ) : (sk' k).1 ∈ W.X := (Classical.choose_spec (hlast k)).1
  let rk' (k : κ) : G'.Walk (sk' k) (t k) := Classical.choose (Classical.choose_spec (hlast k)).2
  have hrk'_path (k : κ) : (rk' k).IsPath :=
    (Classical.choose_spec (Classical.choose_spec (hlast k)).2).1
  have hrk'_sub (k : κ) : ∀ z ∈ (rk' k).support, z ∈ (r k).support :=
    (Classical.choose_spec (Classical.choose_spec (hlast k)).2).2.1
  have hrk'_tail (k : κ) : ∀ z ∈ (rk' k).support.tail, z.1 ∉ W.X :=
    (Classical.choose_spec (Classical.choose_spec (hlast k)).2).2.2
  have hrk'_tail_not_verts (k : κ) : ∀ z ∈ (rk' k).support.tail, z.1 ∉ W.verts := by
    intro z hz
    have hnotX := hrk'_tail k z hz
    rcases z.2 with hzX | hzV
    · exact (hnotX hzX).elim
    · exact hzV
  -- Lift rk' k to G
  let rG (k : κ) : G.Walk (sk' k).1 (t k).1 := (rk' k).map (Embedding.induce V').toHom
  have hrG_path (k : κ) : (rG k).IsPath := isPath_map_induce (hrk'_path k)
  have hrG_tail_not_verts (k : κ) : ∀ z ∈ (rG k).support.tail, z ∉ W.verts := by
    intro z hz
    have hsupp : (rG k).support = (rk' k).support.map Subtype.val := support_map_induce (rk' k)
    rw [hsupp, List.map_tail.symm, List.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    exact hrk'_tail_not_verts k z' hz'
  -- Concatenated path for each k
  let qk (k : κ) : G.Walk (W.a (sk' k).1 (hsk'_X k)) (t k).1 :=
    (W.p (sk' k).1 (hsk'_X k)).append (rG k)
  have hqk_path (k : κ) : (qk k).IsPath := by
    apply append_isPath_of_disjoint_tail (W.isPath _ _) (hrG_path k)
    intro z hz hmem
    exact hrG_tail_not_verts k z hz ⟨(sk' k).1, hsk'_X k, hmem⟩
  -- If (t k).1 ∈ W.X then rk' k is nil, so qk k has the same support as W.p (t k).1 _
  have hrk'_nil_of_X (k : κ) (htX : (t k).1 ∈ W.X) :
      sk' k = t k ∧ (rG k).support.tail = [] := by
    have hmem : t k ∈ (rk' k).support := (rk' k).end_mem_support
    rw [← Walk.cons_tail_support, List.mem_cons] at hmem
    rcases hmem with heq | htl
    · have hst : sk' k = t k := heq.symm
      refine ⟨hst, ?_⟩
      have hsupp : (rG k).support = (rk' k).support.map Subtype.val := support_map_induce (rk' k)
      rw [hsupp, List.map_tail.symm]
      have hlen : (rk' k).support.tail = [] := by
        have haux : ∀ {u v : V'} (q : G'.Walk u v), q.IsPath → u = v → q.support.tail = [] := by
          intro u v q hq huv
          subst huv
          cases q with
          | nil => rfl
          | cons hab q'' =>
            exfalso
            have hnd := hq.support_nodup
            rw [Walk.support_cons, List.nodup_cons] at hnd
            exact hnd.1 q''.end_mem_support
        exact haux (rk' k) (hrk'_path k) hst
      simp [hlen]
    · exact (hrk'_tail k (t k) htl htX).elim
  -- Disjointness of qk k₁ and qk k₂ for k₁ ≠ k₂
  have hqk_disj : ∀ k₁ k₂, k₁ ≠ k₂ →
      Disjoint {v | v ∈ (qk k₁).support} {v | v ∈ (qk k₂).support} := by
    intro k₁ k₂ hne12
    have hsk_ne : (sk' k₁).1 ≠ (sk' k₂).1 := by
      intro heq
      have hsub : sk' k₁ = sk' k₂ := Subtype.ext heq
      exact Set.disjoint_left.mp (hr_disj hne12)
        (hrk'_sub k₁ (sk' k₁) (rk' k₁).start_mem_support)
        (hsub ▸ hrk'_sub k₂ (sk' k₂) (rk' k₂).start_mem_support)
    rw [Set.disjoint_left]
    intro v hv₁ hv₂
    simp only [Set.mem_ofPred_eq, qk, Walk.support_append, List.mem_append] at hv₁ hv₂
    rcases hv₁ with h1a | h1b <;> rcases hv₂ with h2a | h2b
    · exact Set.disjoint_left.mp (W.disj _ (hsk'_X k₁) _ (hsk'_X k₂) hsk_ne) h1a h2a
    · exact hrG_tail_not_verts k₂ v h2b ⟨_, hsk'_X k₁, h1a⟩
    · exact hrG_tail_not_verts k₁ v h1b ⟨_, hsk'_X k₂, h2a⟩
    · have hsupp1 : (rG k₁).support = (rk' k₁).support.map Subtype.val := support_map_induce (rk' k₁)
      have hsupp2 : (rG k₂).support = (rk' k₂).support.map Subtype.val := support_map_induce (rk' k₂)
      rw [hsupp1, List.map_tail.symm, List.mem_map] at h1b
      rw [hsupp2, List.map_tail.symm, List.mem_map] at h2b
      obtain ⟨z₁, hz₁, rfl⟩ := h1b
      obtain ⟨z₂, hz₂, hzeq⟩ := h2b
      have hz12 : z₂ = z₁ := Subtype.ext hzeq
      subst hz12
      exact Set.disjoint_left.mp (hr_disj hne12)
        (hrk'_sub k₁ z₂ (List.mem_of_mem_tail hz₁))
        (hrk'_sub k₂ z₂ (List.mem_of_mem_tail hz₂))
  -- Separation: W.X ⊆ Before G B T'
  have hX_before_T' : W.X ⊆ Before G B T' := by
    intro x hx b hb q hq
    obtain ⟨w, hwV, q₂, hq₂_path, hq₂_sub, hq₂_tail⟩ :=
      exists_last_mem q hq W.verts ⟨x, q.start_mem_support, W.X_subset_verts hx⟩
    have hwX : w ∈ W.X := W.last_in_verts_mem_X hb hwV q₂ hq₂_tail
    have hq₂_V' : ∀ z ∈ q₂.support, z ∈ V' := by
      intro z hz
      rw [← Walk.cons_tail_support, List.mem_cons] at hz
      rcases hz with rfl | htl
      · exact Or.inl hwX
      · exact Or.inr (hq₂_tail z htl)
    let q₂' : G'.Walk ⟨w, Or.inl hwX⟩ ⟨b, hq₂_V' b q₂.end_mem_support⟩ :=
      liftWalk q₂ hq₂_V' (Or.inl hwX) (hq₂_V' b q₂.end_mem_support)
    have hq₂'_path : q₂'.IsPath := liftWalk_isPath q₂ hq₂_path hq₂_V' _ _
    obtain ⟨v', hv'supp, ⟨k, hk⟩⟩ := hr_sep ⟨w, Or.inl hwX⟩ hwX ⟨b, hq₂_V' b q₂.end_mem_support⟩
      hb q₂' hq₂'_path
    have hv_q₂ : v'.1 ∈ q₂.support := by
      rw [← liftWalk_support_map q₂ hq₂_V' (Or.inl hwX) (hq₂_V' b q₂.end_mem_support)]
      exact List.mem_map_of_mem hv'supp
    have hv_T' : v'.1 ∈ T' := by
      refine ⟨⟨k, congrArg Subtype.val hk⟩, ?_⟩
      rw [← Walk.cons_tail_support, List.mem_cons] at hv_q₂
      rcases hv_q₂ with heq | htl
      · exact Or.inl (heq ▸ hwX)
      · right
        intro hbef
        -- dropUntil v'.1 along q₂ avoids W.X
        have hv_mem : v'.1 ∈ q₂.support := List.mem_of_mem_tail htl
        let q₃ := q₂.dropUntil v'.1 hv_mem
        obtain ⟨u, hu, huX⟩ := hbef b hb q₃ (hq₂_path.dropUntil hv_mem)
        have hu_q₂ : u ∈ q₂.support := Walk.support_dropUntil_subset_support q₂ hv_mem hu
        rw [← Walk.cons_tail_support, List.mem_cons] at hu_q₂
        rcases hu_q₂ with huw | hu_tl
        · subst huw
          have hnd := hq₂_path.support_nodup
          have happ : (q₂.takeUntil v'.1 hv_mem).support ++ q₃.support.tail = q₂.support := by
            rw [← Walk.support_append, Walk.take_spec]
          have hvw : v'.1 ≠ u := by
            intro hEq
            rw [← Walk.cons_tail_support, List.nodup_cons] at hnd
            exact hnd.1 (hEq ▸ htl)
          rw [← Walk.cons_tail_support, List.mem_cons] at hu
          rcases hu with hEq | hu_q3tl
          · exact hvw hEq.symm
          · have hnd' : ((q₂.takeUntil v'.1 hv_mem).support ++ q₃.support.tail).Nodup := by
              rw [happ]; exact hnd
            exact (List.nodup_append.mp hnd').2.2 u (Walk.start_mem_support _) u hu_q3tl rfl
        · exact hq₂_tail u hu_tl (W.X_subset_verts huX)
    exact ⟨v'.1, hq₂_sub v'.1 hv_q₂, hv_T'⟩
  -- For each y ∈ T', pick its index k
  let idx (y : V) (hy : y ∈ T') : κ := Classical.choose hy.1
  have hidx_eq (y : V) (hy : y ∈ T') : (t (idx y hy)).1 = y := Classical.choose_spec hy.1
  let W₂ : Wave G A B := {
    X := T'
    a := fun y hy => W.a (sk' (idx y hy)).1 (hsk'_X (idx y hy))
    a_mem := fun y hy => W.a_mem _ _
    p := fun y hy => (qk (idx y hy)).copy rfl (hidx_eq y hy)
    isPath := fun y hy => by
      simpa using hqk_path (idx y hy)
    disj := by
      intro y₁ hy₁ y₂ hy₂ hne12
      have hk_ne : idx y₁ hy₁ ≠ idx y₂ hy₂ := by
        intro heq
        apply hne12
        rw [← hidx_eq y₁ hy₁, ← hidx_eq y₂ hy₂, heq]
      simpa [Walk.support_copy] using hqk_disj (idx y₁ hy₁) (idx y₂ hy₂) hk_ne
    sep := W.sep.trans (before_mono hX_before_T')
  }
  refine ⟨W₂, ⟨hX_before_T', ?_, ?_, ?_⟩, hT'_ne⟩
  · intro y hyT' hyB
    rcases hyT'.2 with hyX | hnotB
    · exact hyX
    · exact (hnotB hyB).elim
  · intro y hyW hyT'
    change ((qk (idx y hyT')).copy rfl (hidx_eq y hyT')).support = (W.p y hyW).support
    rw [Walk.support_copy]
    have htX : (t (idx y hyT')).1 ∈ W.X := (hidx_eq y hyT').symm ▸ hyW
    obtain ⟨hst, htail_nil⟩ := hrk'_nil_of_X (idx y hyT') htX
    have hsk_y : (sk' (idx y hyT')).1 = y := (congrArg Subtype.val hst).trans (hidx_eq y hyT')
    simp only [qk, Walk.support_append, htail_nil, List.append_nil]
    have hsupp : ∀ z (hz : z ∈ W.X), z = y → (W.p z hz).support = (W.p y hyW).support := by
      intro z _ hzy
      subst hzy
      rfl
    exact hsupp _ _ hsk_y
  · intro y hyT'
    refine ⟨(sk' (idx y hyT')).1, hsk'_X (idx y hyT'), ?_⟩
    change (W.p (sk' (idx y hyT')).1 (hsk'_X (idx y hyT'))).support <+:
      ((qk (idx y hyT')).copy rfl (hidx_eq y hyT')).support
    rw [Walk.support_copy]
    exact ⟨(rG (idx y hyT')).support.tail, (Walk.support_append _ _).symm⟩

end OMA.Erdos599H1

theorem OMA.solution : OMA.R_Erdos599_erdos_599_variants_aharoni_berger_R1.H1 := by
  intro V G A B
  obtain ⟨W, hWmax⟩ := zorn_le (α := OMA.Erdos599H1.Wave G A B) OMA.Erdos599H1.chain_bddAbove
  refine ⟨W.X, fun i => W.a i.1 i.2, fun i => i.1, fun i => W.p i.1 i.2,
    fun i => W.a_mem i.1 i.2, fun i => W.isPath i.1 i.2, ?_, ?_, ?_⟩
  · intro i j hne
    exact W.disj i.1 i.2 j.1 j.2 (fun h => hne (Subtype.ext h))
  · intro a' ha' b' hb' q hq
    obtain ⟨u, hu, huX⟩ := W.sep ha' b' hb' q hq
    exact ⟨u, hu, ⟨⟨u, huX⟩, rfl⟩⟩
  · -- Show every wave in the after-wave graph has terminal set equal to X'
    dsimp only
    intro κ s t r hs hr_path hr_disj hr_sep
    -- Note that Set.range (fun i : W.X => i.1) = W.X
    have hrange : Set.range (fun i : W.X => i.1) = W.X := Subtype.range_coe
    have hverts_eq :
        {v : V | v ∈ Set.range (fun i : W.X => i.1) ∨
          ∀ i : W.X, v ∉ (W.p i.1 i.2).support} = {v : V | v ∈ W.X ∨ v ∉ W.verts} := by
      ext v
      simp [hrange, OMA.Erdos599H1.Wave.verts]
    by_contra hne
    -- Transport s, t, r across hverts_eq
    have hcast : ∀ (P : Set V), P = {v : V | v ∈ W.X ∨ v ∉ W.verts} →
        ∀ (s : κ → P) (t : κ → P) (r : ∀ k, (G.induce P).Walk (s k) (t k)),
          (∀ k, (s k).1 ∈ W.X) → (∀ k, (r k).IsPath) →
          (Pairwise fun k₁ k₂ => Disjoint {v | v ∈ (r k₁).support} {v | v ∈ (r k₂).support}) →
          (∀ x' : P, x'.1 ∈ W.X → ∀ b' : P, b'.1 ∈ B →
            ∀ q : (G.induce P).Walk x' b', q.IsPath → ∃ v ∈ q.support, v ∈ Set.range t) →
          Set.range t ≠ {v : P | v.1 ∈ W.X} → False := by
      intro P hP
      subst hP
      intro s₀ t₀ r₀ hs₀ hrp₀ hrd₀ hrs₀ hne₀
      obtain ⟨W₂, hle, hXne⟩ :=
        OMA.Erdos599H1.extend_wave W κ s₀ t₀ r₀ hs₀ hrp₀ hrd₀ hrs₀ hne₀
      have hge : W₂ ≤ W := hWmax hle
      apply hXne
      ext y
      constructor
      · intro hy₂
        exact hle.2.1 y hy₂ (hge.1 hy₂)
      · intro hy₁
        exact hge.2.1 y hy₁ (hle.1 hy₁)
    exact hcast _ hverts_eq s t r
      (fun k => by simpa [hrange] using hs k) hr_path hr_disj
      (fun x' hx' b' hb' q hq => hr_sep x' (by simpa [hrange] using hx') b' hb' q hq)
      (fun heq => hne (heq.trans (by ext v; simp [hrange])))
