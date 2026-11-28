import FormalConjectures.Paper.BurningNumberConjecture
import Mathlib

/-!
# The burning number conjecture reduces to non-spider trees of perfect-square order

Proved here:
* (Bonato, Janssen, Roshanbin 2016) a connected graph burns at least as fast as any of its
  spanning trees, since distances can only shrink when edges are added;
* padding: attaching a pendant leaf to a tree gives a tree whose burning number is not
  smaller, so a tree on `n` vertices grows to a tree on exactly `⌈√n⌉ ^ 2` vertices;
* paths (BJR16): a connected graph of maximum degree at most two has a Hamiltonian path and
  burns in `⌈√n⌉` rounds;
* small orders: square-order trees with `k ≤ 2` and a vertex of degree three burn in `k` rounds.

What remains, for trees on `k ^ 2` vertices with `k ≥ 3`:
* `H1` (known: Bonato and Lidbetter 2019; Das, Dev, Sadhukhan, Sahoo, Sen 2018): spiders, trees with
  exactly one vertex of degree at least three, burn in `k` rounds;
* `H2` (open core): trees with at least two vertices of degree at least three burn in `k` rounds.
-/

namespace OMA.R_BurningNumberConjecture_burning_number_conjecture_R1

open BurningNumberConjecture SimpleGraph

/-- Spiders of order `k ^ 2`, `k ≥ 3`, burn in `k` rounds. -/
def H1 : Prop :=
  ∀ (k : ℕ) (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree → Fintype.card V = k ^ 2 →
    3 ≤ k → (∃ c, 3 ≤ (T.neighborSet c).ncard ∧ ∀ v, v ≠ c → (T.neighborSet v).ncard ≤ 2) →
    burningNumber T ≤ k

/-- Trees of order `k ^ 2`, `k ≥ 3`, with two vertices of degree at least three burn in `k`
rounds. -/
def H2 : Prop :=
  ∀ (k : ℕ) (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree → Fintype.card V = k ^ 2 →
    3 ≤ k → (∃ u v, u ≠ v ∧ 3 ≤ (T.neighborSet u).ncard ∧ 3 ≤ (T.neighborSet v).ncard) →
    burningNumber T ≤ k

/-- A map sending edges to edges or to single vertices does not lengthen walks. -/
lemma walk_transfer {V W : Type} {G : SimpleGraph V} {G' : SimpleGraph W} (f : W → V)
    (hf : ∀ a b, G'.Adj a b → G.Adj (f a) (f b) ∨ f a = f b) {a b : W} (p : G'.Walk a b) :
    ∃ q : G.Walk (f a) (f b), q.length ≤ p.length := by
  induction p with
  | nil => exact ⟨Walk.nil, le_rfl⟩
  | cons h p ih =>
    obtain ⟨q, hq⟩ := ih
    rcases hf _ _ h with h' | h'
    · exact ⟨Walk.cons h' q, by simp only [Walk.length_cons]; omega⟩
    · exact ⟨q.copy h'.symm rfl, by simp only [Walk.length_copy, Walk.length_cons]; omega⟩

/-- Burning sequences transfer along such a map when it has a section. -/
lemma burn_transfer {V W : Type} {G : SimpleGraph V} {G' : SimpleGraph W} (f : W → V)
    (hf : ∀ a b, G'.Adj a b → G.Adj (f a) (f b) ∨ f a = f b) (g : V → W)
    (hg : ∀ v, f (g v) = v) {k : ℕ} (x : Fin k → W) (hx : IsBurningSequence G' x) :
    IsBurningSequence G (fun i => f (x i)) := by
  intro v
  obtain ⟨i, hr, hd⟩ := hx (g v)
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := walk_transfer f hf p
  have hq' := SimpleGraph.dist_le q
  have e := hg v
  revert q
  rw [e]
  intro q hq hq'
  refine ⟨i, ⟨q⟩, ?_⟩
  show G.dist (f (x i)) v + (i : ℕ) < k
  omega

lemma burn_set_nonempty {V : Type} [Fintype V] (G : SimpleGraph V) :
    {k | ∃ x : Fin k → V, IsBurningSequence G x}.Nonempty := by
  refine ⟨Fintype.card V, fun i => (Fintype.equivFin V).symm i, fun v => ?_⟩
  refine ⟨Fintype.equivFin V v, ?_, ?_⟩
  · simp
  · simp

lemma bn_le_of_transfer {V W : Type} [Fintype W] {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : W → V) (hf : ∀ a b, G'.Adj a b → G.Adj (f a) (f b) ∨ f a = f b) (g : V → W)
    (hg : ∀ v, f (g v) = v) : burningNumber G ≤ burningNumber G' := by
  obtain ⟨x, hx⟩ := Nat.sInf_mem (burn_set_nonempty G')
  exact Nat.sInf_le ⟨fun i => f (x i), burn_transfer f hf g hg x hx⟩

/-- Lifting an acyclic graph along `some` keeps it acyclic (`none` stays isolated). -/
lemma map_some_isAcyclic {V : Type} {T : SimpleGraph V} (hT : T.IsAcyclic) :
    (T.map (Function.Embedding.some)).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge] at hT ⊢
  intro a b hab
  obtain ⟨-, x, y, hxy, rfl, rfl⟩ := hab
  have hbr := hT hxy
  rw [isBridge_iff] at hbr ⊢
  intro hr
  apply hbr
  let φ : ((T.map (Function.Embedding.some)).deleteEdges {s(some x, some y)}) →g
      (T.deleteEdges {s(x, y)}) :=
    { toFun := fun o => o.getD x
      map_rel' := by
        intro a b h
        rw [deleteEdges_adj, map_adj] at h
        obtain ⟨⟨u, v, huv, rfl, rfl⟩, h2⟩ := h
        rw [deleteEdges_adj]
        refine ⟨huv, fun h3 => h2 ?_⟩
        rw [Set.mem_singleton_iff] at h3 ⊢
        simp only [Function.Embedding.some_apply, Option.getD_some] at h3 ⊢
        simpa using congrArg (Sym2.map some) h3 }
  exact hr.map φ

lemma leaf_ext_isTree {V : Type} {T : SimpleGraph V} (hT : T.IsTree) (w : V) :
    (T.map (Function.Embedding.some) ⊔ edge none (some w)).IsTree := by
  have hnr : ¬ (T.map (Function.Embedding.some)).Reachable none (some w) := by
    rintro ⟨p⟩
    cases p with
    | cons h _ =>
      obtain ⟨-, u, v, _, hu, _⟩ := h
      exact Option.some_ne_none u hu
  refine ⟨?_, (map_some_isAcyclic hT.isAcyclic).sup_edge_of_not_reachable hnr⟩
  have hw : ∀ x : V, (T.map (Function.Embedding.some) ⊔ edge none (some w)).Reachable
      (some w) (some x) := by
    intro x
    have hr : T.Reachable w x := hT.connected w x
    have h1 := hr.map (Embedding.map (Function.Embedding.some) T).toHom
    exact h1.mono le_sup_left
  have hn : (T.map (Function.Embedding.some) ⊔ edge none (some w)).Reachable none (some w) := by
    refine Adj.reachable ?_
    right
    rw [edge_adj]
    simp
  refine Connected.mk ?_
  intro a b
  have ha : ∀ a, (T.map (Function.Embedding.some) ⊔ edge none (some w)).Reachable (some w) a := by
    intro a
    cases a with
    | none => exact hn.symm
    | some x => exact hw x
  exact (ha a).symm.trans (ha b)

lemma leaf_ext_bn {V : Type} [Fintype V] (T : SimpleGraph V) (w : V) :
    burningNumber T ≤
      burningNumber (T.map (Function.Embedding.some) ⊔ edge none (some w)) := by
  refine bn_le_of_transfer (fun o => o.getD w) ?_ some (fun v => rfl)
  intro a b h
  rcases h with h | h
  · obtain ⟨-, u, v, huv, rfl, rfl⟩ := h
    exact Or.inl huv
  · rw [edge_adj] at h
    right
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

lemma pad (k : ℕ) (hsq : ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree →
    Fintype.card V = k ^ 2 → burningNumber T ≤ k) :
    ∀ (d : ℕ) (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree →
      Fintype.card V + d = k ^ 2 → burningNumber T ≤ k := by
  intro d
  induction d with
  | zero =>
    intro V _ T hT hc
    exact hsq V T hT hc
  | succ d ih =>
    intro V _ T hT hc
    obtain ⟨w⟩ := hT.connected.nonempty
    refine (leaf_ext_bn T w).trans ?_
    refine ih (Option V) _ (leaf_ext_isTree hT w) ?_
    rw [Fintype.card_option]
    omega

lemma le_ceil_sqrt_sq (n : ℕ) : n ≤ ⌈Real.sqrt n⌉₊ ^ 2 := by
  have h1 : Real.sqrt n ≤ (⌈Real.sqrt n⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (n : ℝ) ≤ (⌈Real.sqrt n⌉₊ : ℝ) ^ 2 := by
    calc (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
      _ ≤ (⌈Real.sqrt n⌉₊ : ℝ) ^ 2 := by gcongr
  exact_mod_cast h2


section Paths

variable {V V' : Type}

lemma ceil_sqrt_le_iff (n t : ℕ) : ⌈Real.sqrt n⌉₊ ≤ t ↔ n ≤ t ^ 2 := by
  rw [Nat.ceil_le, Real.sqrt_le_left (by positivity), ← Nat.cast_pow, Nat.cast_le]

lemma ceil_sqrt_sq (k : ℕ) : ⌈Real.sqrt ((k ^ 2 : ℕ) : ℝ)⌉₊ = k := by
  rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg k), Nat.ceil_natCast]

/-- Upper bound for paths [BJR16]: `b(P_n) ≤ ⌈√n⌉`. -/
lemma path_upper (n : ℕ) (hn : 1 ≤ n) :
    burningNumber (SimpleGraph.pathGraph n) ≤ ⌈Real.sqrt n⌉₊ := by
  have hreach := pathGraph_preconnected n
  have hdi : ∀ (d : ℕ) (a b : Fin n), b.1 = a.1 + d → (pathGraph n).dist a b ≤ d := by
    intro d; induction d with
    | zero => intro a b h; simp [Fin.ext (by omega : a.1 = b.1)]
    | succ d ih =>
      intro a b h
      let u : Fin n := ⟨a.1 + d, by omega⟩
      have hadj : (pathGraph n).Adj u b := pathGraph_adj.mpr (.inl (by dsimp [u]; omega))
      have := hadj.reachable.dist_triangle_right a
      have := dist_eq_one_iff_adj.mpr hadj
      have := ih a u rfl; omega
  have hdu (a b : Fin n) (r : ℕ) (ha : a.1 ≤ b.1 + r) (hb : b.1 ≤ a.1 + r) :
      (pathGraph n).dist a b ≤ r := by
    by_cases h : a.1 ≤ b.1
    · exact (hdi (b.1 - a.1) a b (by omega)).trans (by omega)
    · rw [SimpleGraph.dist_comm]; exact (hdi (a.1 - b.1) b a (by omega)).trans (by omega)
  let k := ⌈Real.sqrt n⌉₊
  have hceil (t : ℕ) : k ≤ t ↔ n ≤ t ^ 2 := ceil_sqrt_le_iff n t
  have hcover : ∃ x : Fin k → Fin n, IsBurningSequence (pathGraph n) x := by
    let c (i : Fin k) : Fin n :=
      ⟨min (i.rev.1 ^ 2 + i.rev.1) (n - 1), (min_le_right _ _).trans_lt (by omega)⟩
    refine ⟨c, fun v => ?_⟩
    let r : Fin k := ⟨Nat.sqrt v.1, Nat.sqrt_lt'.mpr (v.2.trans_le ((hceil k).1 le_rfl))⟩
    refine ⟨r.rev, hreach _ _, ?_⟩
    have hrlo : r.1 ^ 2 ≤ v.1 := Nat.sqrt_le' _
    have hrhi : v.1 < (r.1 + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have hhi : v.1 ≤ r.1 ^ 2 + 2 * r.1 := by nlinarith
    have : (c r.rev).1 = min (r.1 ^ 2 + r.1) (n - 1) := by simp [c]
    have := v.2; have := hdu (c r.rev) v r.1 (by omega) (by omega)
    have := Fin.val_rev r; omega
  obtain ⟨x, hx⟩ := hcover
  exact Nat.sInf_le ⟨x, hx⟩

/-- A path in a connected graph of maximum degree at most two that misses a vertex
can be extended by one edge. -/
lemma extend [Fintype V] {G : SimpleGraph V} (hc : G.Connected)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 2)
    {u w : V} (p : G.Walk u w) (hp : p.IsPath) {v : V} (hv : v ∉ p.support) :
    ∃ (u' w' : V) (q : G.Walk u' w'), q.IsPath ∧ q.length = p.length + 1 := by
  obtain ⟨r⟩ := hc.preconnected u v
  obtain ⟨d, -, hd1, hd2⟩ :=
    r.exists_boundary_dart {x | x ∈ p.support} p.start_mem_support hv
  have hd2' : d.snd ∉ p.support := hd2
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hd1
  have hab : G.Adj d.fst d.snd := d.adj
  rcases Nat.lt_or_ge i p.length with hlt | hge
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [Walk.getVert_zero] at hi
      have hadj : G.Adj d.snd u := by rw [hi]; exact hab.symm
      exact ⟨d.snd, w, Walk.cons hadj p, (Walk.cons_isPath_iff _ _).mpr ⟨hp, hd2'⟩, by simp⟩
    · exfalso
      have hx : G.Adj d.fst (p.getVert (i - 1)) := by
        have h := p.adj_getVert_succ (i := i - 1) (by omega)
        rw [Nat.sub_add_cancel hpos, hi] at h
        exact h.symm
      have hy : G.Adj d.fst (p.getVert (i + 1)) := by
        have h := p.adj_getVert_succ (i := i) hlt
        rwa [hi] at h
      have hxy : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
        intro h
        have := hp.getVert_injOn (show i - 1 ∈ {j | j ≤ p.length} by
          simp only [Set.mem_ofPred_eq]; omega)
          (show i + 1 ∈ {j | j ≤ p.length} by simp only [Set.mem_ofPred_eq]; omega) h
        omega
      have hxs : p.getVert (i - 1) ∈ p.support :=
        Walk.mem_support_iff_exists_getVert.mpr ⟨i - 1, rfl, by omega⟩
      have hys : p.getVert (i + 1) ∈ p.support :=
        Walk.mem_support_iff_exists_getVert.mpr ⟨i + 1, rfl, by omega⟩
      have hxb : p.getVert (i - 1) ≠ d.snd := fun h => hd2' (h ▸ hxs)
      have hyb : p.getVert (i + 1) ≠ d.snd := fun h => hd2' (h ▸ hys)
      have h3 : ({p.getVert (i - 1), p.getVert (i + 1), d.snd} : Set V).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨_, _, _, hxy, hxb, hyb, rfl⟩
      have hsub : ({p.getVert (i - 1), p.getVert (i + 1), d.snd} : Set V) ⊆
          G.neighborSet d.fst := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact hx
        · exact hy
        · exact hab
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      have := hdeg d.fst
      omega
  · have hiw : i = p.length := by omega
    subst hiw
    rw [Walk.getVert_length] at hi
    have hadj : G.Adj d.snd w := by rw [hi]; exact hab.symm
    refine ⟨d.snd, u, Walk.cons hadj p.reverse, (Walk.cons_isPath_iff _ _).mpr
      ⟨hp.reverse, by simpa [Walk.support_reverse] using hd2'⟩, by simp⟩

/-- A connected finite graph of maximum degree at most two has a Hamiltonian path. -/
lemma exists_ham [Fintype V] {G : SimpleGraph V} (hc : G.Connected)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 2) :
    ∃ (u w : V) (p : G.Walk u w), p.IsPath ∧ ∀ v, v ∈ p.support := by
  by_contra hno
  push Not at hno
  have key : ∀ m : ℕ, ∃ (u w : V) (p : G.Walk u w), p.IsPath ∧ p.length = m := by
    intro m
    induction m with
    | zero =>
      obtain ⟨u⟩ := hc.nonempty
      exact ⟨u, u, Walk.nil, Walk.IsPath.nil, rfl⟩
    | succ m ih =>
      obtain ⟨u, w, p, hp, hl⟩ := ih
      obtain ⟨v, hv⟩ := hno u w p hp
      obtain ⟨u', w', q, hq, hql⟩ := extend hc hdeg p hp hv
      exact ⟨u', w', q, hq, by omega⟩
  obtain ⟨u, w, p, hp, hl⟩ := key (Fintype.card V)
  have := hp.length_lt
  omega

/-- A graph with a spanning walk burns at least as fast as the path of the same length. -/
lemma bn_le_of_ham [Fintype V] {G : SimpleGraph V} {u w : V} (p : G.Walk u w)
    (hcov : ∀ v, v ∈ p.support) :
    burningNumber G ≤ burningNumber (pathGraph (p.length + 1)) := by
  have hψ : ∀ v, ∃ i : Fin (p.length + 1), p.getVert i.val = v := fun v => by
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp (hcov v)
    exact ⟨⟨n, by omega⟩, hn⟩
  choose ψ hψ' using hψ
  refine bn_le_of_transfer (G := G) (G' := pathGraph (p.length + 1))
    (fun i => p.getVert i.val) ?_ ψ hψ'
  intro a b h
  left
  rcases pathGraph_adj.mp h with h | h
  · have := p.adj_getVert_succ (i := a.val) (by omega)
    rw [h] at this
    exact this
  · have := p.adj_getVert_succ (i := b.val) (by omega)
    rw [h] at this
    exact this.symm

/-- The burning number conjecture holds for connected graphs of maximum degree at most two
(paths and cycles). -/
theorem bn_le_of_maxdeg_two [Fintype V] {G : SimpleGraph V} (hc : G.Connected)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 2) :
    burningNumber G ≤ ⌈Real.sqrt (Fintype.card V)⌉₊ := by
  obtain ⟨u, w, p, hp, hcov⟩ := exists_ham hc hdeg
  refine (bn_le_of_ham p hcov).trans ((path_upper _ (by omega)).trans ?_)
  rw [ceil_sqrt_le_iff]
  have h1 := hp.length_lt
  have h2 := (ceil_sqrt_le_iff (Fintype.card V) _).1 le_rfl
  omega

end Paths

section Small

variable {V : Type}

/-- Radius bound: if every vertex is within distance `r` of `c`, then `b(G) ≤ r + 1`. -/
lemma bn_le_of_center {G : SimpleGraph V} (c : V) (r : ℕ)
    (h : ∀ v, G.Reachable c v ∧ G.dist c v ≤ r) : burningNumber G ≤ r + 1 := by
  refine Nat.sInf_le ⟨fun _ => c, fun v => ⟨0, (h v).1, ?_⟩⟩
  have := (h v).2
  simp only [Fin.val_zero]
  omega

/-- Trees (indeed any graphs) on four vertices with a vertex of degree at least three
burn in two rounds; with `k ≤ 2` this settles the square-order case `H2` for small `k`. -/
lemma H2_small : ∀ (k : ℕ) (V : Type) [Fintype V] (T : SimpleGraph V), k ≤ 2 →
    Fintype.card V = k ^ 2 → (∃ v, 3 ≤ (T.neighborSet v).ncard) → burningNumber T ≤ k := by
  intro k V _ T hk hcard ⟨c, hc⟩
  classical
  have hNle : (T.neighborSet c).ncard + 1 ≤ Fintype.card V := by
    have hsub : insert c (T.neighborSet c) ⊆ (Set.univ : Set V) := Set.subset_univ _
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem (s := T.neighborSet c) (a := c) (by simp) (Set.toFinite _),
      Set.ncard_univ, Nat.card_eq_fintype_card] at h1
    exact h1
  have hk2 : k = 2 := by
    interval_cases k <;> simp at hcard <;> omega
  subst hk2
  have hall : ∀ v, v = c ∨ T.Adj c v := by
    by_contra hno
    push Not at hno
    obtain ⟨v, hvc, hvn⟩ := hno
    have hsub : insert v (insert c (T.neighborSet c)) ⊆ (Set.univ : Set V) :=
      Set.subset_univ _
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem (by simp [hvc, hvn]) (Set.toFinite _),
      Set.ncard_insert_of_notMem (s := T.neighborSet c) (a := c) (by simp) (Set.toFinite _),
      Set.ncard_univ, Nat.card_eq_fintype_card] at h1
    omega
  refine bn_le_of_center (G := T) c 1 (fun v => ?_)
  rcases hall v with rfl | hadj
  · exact ⟨Reachable.refl _, by simp⟩
  · exact ⟨hadj.reachable, by rw [dist_eq_one_iff_adj.mpr hadj]⟩

end Small

theorem main : H1 → H2 → type_of% @BurningNumberConjecture.burning_number_conjecture := by
  intro h1 h2 V _ G hc
  obtain ⟨T, hle, hT⟩ := hc.exists_isTree_le
  set k := ⌈Real.sqrt (Fintype.card V)⌉₊ with hk
  have hsq : ∀ (W : Type) [Fintype W] (S : SimpleGraph W), S.IsTree →
      Fintype.card W = k ^ 2 → burningNumber S ≤ k := by
    intro W _ S hS hcard
    by_cases hdeg : ∀ v, (S.neighborSet v).ncard ≤ 2
    · have := bn_le_of_maxdeg_two hS.connected hdeg
      rwa [hcard, ceil_sqrt_sq] at this
    · push Not at hdeg
      obtain ⟨c, hcdeg⟩ := hdeg
      by_cases hk3 : k ≤ 2
      · exact H2_small k W S hk3 hcard ⟨c, by omega⟩
      · by_cases hsp : ∀ v, v ≠ c → (S.neighborSet v).ncard ≤ 2
        · exact h1 k W S hS hcard (by omega) ⟨c, by omega, hsp⟩
        · push Not at hsp
          obtain ⟨v, hvc, hv⟩ := hsp
          exact h2 k W S hS hcard (by omega) ⟨c, v, hvc.symm, by omega, by omega⟩
  have hGT : burningNumber G ≤ burningNumber T :=
    bn_le_of_transfer id (fun a b h => Or.inl (hle h)) id (fun v => rfl)
  have hn := le_ceil_sqrt_sq (Fintype.card V)
  rw [← hk] at hn
  exact hGT.trans (pad k hsq (k ^ 2 - Fintype.card V) V T hT (by omega))

end OMA.R_BurningNumberConjecture_burning_number_conjecture_R1
