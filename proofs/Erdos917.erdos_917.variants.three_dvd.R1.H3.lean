-- Step Erdos917.erdos_917.variants.three_dvd.R1.H3: hypothesis H3 of reduction Erdos917.erdos_917.variants.three_dvd.R1
-- Credit: @ptc-prover-bot
-- Hajós sum with K_6. Take an edge xy of the 6-critical graph G, glue K_6 at x (new vertices k1..k5),
-- delete xy and x k1, and add y k1. Every 5-colouring of the K_6 part gives x and k1 the same colour, so
-- y and x get different colours and G would be 5-colourable. Each vertex or edge deletion is handled by an
-- explicit 5-colouring, glued from a colouring of G minus an edge or vertex and a colouring of the K_6 part
-- (finite checks by decide). Edges: (e - 1) + 14 + 1 = e + 14.
import OMAReductions.R_Erdos917_erdos_917_variants_three_dvd_R1
import Mathlib

/-! ## Hajós sum of a `6`-critical graph with `K_6`

Given a `6`-critical graph `G` on `Fin n` with an edge `xy`, glue a copy of `K_6` at `x`
(the new vertices are `k₁, …, k₅`), delete the edges `xy` and `x k₁`, and add the edge `y k₁`.
The result `H` is `6`-critical on `n + 5` vertices with `|E(G)| + 14` edges. -/

namespace HilbertDB.E917Hajos

open Finset SimpleGraph

variable {n : ℕ}

/-- The old vertices. -/
def L : Fin n ↪ Fin (n + 5) :=
  ⟨Fin.castAdd 5, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

@[simp] lemma L_val (u : Fin n) : (L u).val = u.val := rfl

/-- The `K_6` part: position `0` is `x`, positions `1, …, 5` are new vertices. -/
def Mf (x : Fin n) (a : Fin 6) : Fin (n + 5) :=
  if a.val = 0 then L x else ⟨n + a.val - 1, by have := a.isLt; omega⟩

lemma Mf_val (x : Fin n) (a : Fin 6) :
    (Mf x a).val = if a.val = 0 then x.val else n + a.val - 1 := by
  unfold Mf; split_ifs <;> simp

lemma Mf_inj (x : Fin n) : Function.Injective (Mf x) := by
  intro a b h
  have h' := congrArg Fin.val h
  rw [Mf_val, Mf_val] at h'
  have := x.isLt
  apply Fin.ext
  split_ifs at h' <;> omega

def M (x : Fin n) : Fin 6 ↪ Fin (n + 5) := ⟨Mf x, Mf_inj x⟩

lemma M_val (x : Fin n) (a : Fin 6) :
    (M x a).val = if a.val = 0 then x.val else n + a.val - 1 := Mf_val x a

lemma M_zero (x : Fin n) : M x 0 = L x := Fin.ext (by rw [M_val]; simp)

/-- `K_6` minus the edge `{0, 1}`. -/
def K6' : SimpleGraph (Fin 6) := (⊤ : SimpleGraph (Fin 6)).deleteEdges {s(0, 1)}

/-- The Hajós sum. -/
def H (G : SimpleGraph (Fin n)) (x y : Fin n) : SimpleGraph (Fin (n + 5)) :=
  (G.deleteEdges {s(x, y)}).map L ⊔ K6'.map (M x) ⊔ edge (L y) (M x 1)

lemma s_ne {α : Type*} {a b c d : α} :
    s(a, b) ≠ s(c, d) ↔ ¬((a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
  rw [Ne, Sym2.eq_iff]

lemma H_adj (G : SimpleGraph (Fin n)) (x y : Fin n) (p q : Fin (n + 5)) :
    (H G x y).Adj p q ↔
      (∃ u w, (G.Adj u w ∧ s(u, w) ≠ s(x, y)) ∧ L u = p ∧ L w = q) ∨
      (∃ a b : Fin 6, (a ≠ b ∧ s(a, b) ≠ s(0, 1)) ∧ M x a = p ∧ M x b = q) ∨
      ((p = L y ∧ q = M x 1 ∨ p = M x 1 ∧ q = L y) ∧ p ≠ q) := by
  simp only [H, K6', sup_adj, map_adj, deleteEdges_adj, top_adj, edge_adj,
    Set.mem_singleton_iff, or_assoc]

/- ### Colourings glued from a colouring of `G` and a colouring of the `K_6` part -/

def glue {β : Type*} (g : Fin n → β) (κ : Fin 6 → β) (p : Fin (n + 5)) : β :=
  if h : p.val < n then g ⟨p.val, h⟩ else κ ⟨p.val - n + 1, by have := p.isLt; omega⟩

lemma glue_L {β : Type*} (g : Fin n → β) (κ : Fin 6 → β) (u : Fin n) : glue g κ (L u) = g u := by
  unfold glue; rw [dif_pos (by simp)]; rfl

lemma glue_M {β : Type*} (x : Fin n) (g : Fin n → β) (κ : Fin 6 → β) (h0 : κ 0 = g x) (a : Fin 6) :
    glue g κ (M x a) = κ a := by
  by_cases ha : a.val = 0
  · have : a = 0 := Fin.ext ha
    subst this; rw [M_zero, glue_L, h0]
  · unfold glue
    have hv := M_val x a
    rw [if_neg ha] at hv
    rw [dif_neg (by omega)]
    congr 1; apply Fin.ext; simp only [hv]; omega

theorem glue_proper {β : Type*} (G : SimpleGraph (Fin n)) (x y : Fin n) (g : Fin n → β)
    (κ : Fin 6 → β) (h0 : κ 0 = g x) (bad : Fin (n + 5) → Fin (n + 5) → Prop)
    (ha : ∀ u w, G.Adj u w → s(u, w) ≠ s(x, y) → ¬ bad (L u) (L w) → g u ≠ g w)
    (hb : ¬ bad (L y) (M x 1) → ¬ bad (M x 1) (L y) → g y ≠ κ 1)
    (hc : ∀ a b : Fin 6, a ≠ b → s(a, b) ≠ s(0, 1) → ¬ bad (M x a) (M x b) → κ a ≠ κ b) :
    ∀ p q, (H G x y).Adj p q → ¬ bad p q → ¬ bad q p → glue g κ p ≠ glue g κ q := by
  intro p q hpq h1 h2
  rw [H_adj] at hpq
  rcases hpq with ⟨u, w, ⟨hG, hne⟩, rfl, rfl⟩ | ⟨a, b, ⟨hab, hne⟩, rfl, rfl⟩ |
    ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), -⟩
  · rw [glue_L, glue_L]; exact ha u w hG hne h1
  · rw [glue_M x g κ h0, glue_M x g κ h0]; exact hc a b hab hne h1
  · rw [glue_L, glue_M x g κ h0]; exact hb h1 h2
  · rw [glue_L, glue_M x g κ h0]; exact (hb h2 h1).symm

lemma colorable_of {V : Type*} (G' : SimpleGraph V) (c : V → Fin 5)
    (h : ∀ u w, G'.Adj u w → c u ≠ c w) : G'.Colorable 5 :=
  ⟨Coloring.mk c (fun hh => h _ _ hh)⟩

/- ### Colourings of the `K_6` part (finite checks) -/

/-- Reduction mod 5. -/
def c5 (k : ℕ) : Fin 5 := ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩

/-- `x` and `k₁` both get `α`, the others `α+1, …, α+4`. -/
def kA (α : Fin 5) (a : Fin 6) : Fin 5 := if a.val ≤ 1 then α else α + (c5 (a.val - 1))

theorem kA_ok : ∀ α : Fin 5, kA α 0 = α ∧ kA α 1 = α ∧
    ∀ a b : Fin 6, a ≠ b → ¬((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) → kA α a ≠ kA α b := by
  decide +kernel

/-- Rank of `a` once `a'` and `b'` are merged. -/
def rk (a' b' a : Fin 6) : ℕ :=
  if a.val = max a'.val b'.val then min a'.val b'.val
  else if a.val < max a'.val b'.val then a.val else a.val - 1

/-- `a'` and `b'` share a colour; `x` gets `α` and `k₁` does not. -/
def kB (α : Fin 5) (a' b' a : Fin 6) : Fin 5 := α + (c5 (rk a' b' a))

set_option synthInstance.maxHeartbeats 0 in
set_option synthInstance.maxSize 1000 in
theorem kB_ok : ∀ α : Fin 5, ∀ a' b' : Fin 6, a' ≠ b' → ¬((a' = 0 ∧ b' = 1) ∨ (a' = 1 ∧ b' = 0)) →
    kB α a' b' 0 = α ∧ kB α a' b' 1 ≠ α ∧
    ∀ a b : Fin 6, a ≠ b → ¬((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) →
      ¬((a = a' ∧ b = b') ∨ (a = b' ∧ b = a')) → kB α a' b' a ≠ kB α a' b' b := by
  decide +kernel

/-- Vertex `a'` is deleted; the others get distinct colours, `x` gets `α`, `k₁` does not. -/
def kV (α : Fin 5) (a' a : Fin 6) : Fin 5 :=
  α + (c5 (if a.val < a'.val then a.val else a.val - 1))

set_option synthInstance.maxHeartbeats 0 in
set_option synthInstance.maxSize 1000 in
theorem kV_ok : ∀ α : Fin 5, ∀ a' : Fin 6, a' ≠ 0 →
    kV α a' 0 = α ∧ (a' ≠ 1 → kV α a' 1 ≠ α) ∧
    ∀ a b : Fin 6, a ≠ b → ¬((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) → a ≠ a' → b ≠ a' →
      kV α a' a ≠ kV α a' b := by
  decide +kernel

/-- `x` is deleted: `k₁` avoids `β`, the new vertices get distinct colours. -/
def kX (α β : Fin 5) (a : Fin 6) : Fin 5 := if a.val = 0 then α else β + (c5 a.val)

theorem kX_ok : ∀ α β : Fin 5, kX α β 0 = α ∧ kX α β 1 ≠ β ∧
    ∀ a b : Fin 6, a ≠ 0 → b ≠ 0 → a ≠ b → kX α β a ≠ kX α β b := by
  decide +kernel

/- ### Facts about the `6`-critical graph `G` -/

variable {G : SimpleGraph (Fin n)}

lemma col5_of_lt {V : Type*} {G' : SimpleGraph V} (h : G'.chromaticNumber < 6) :
    G'.Colorable 5 := by
  by_contra hc
  have h5 : ((5 : ℕ) : ℕ∞) < G'.chromaticNumber := by
    rw [← chromaticNumber_le_iff_colorable, not_le] at hc; exact hc
  have := Order.add_one_le_of_lt h5
  have h6 : (6 : ℕ∞) ≤ G'.chromaticNumber := by
    calc (6 : ℕ∞) = ((5 : ℕ) : ℕ∞) + 1 := by norm_num
      _ ≤ _ := this
  exact absurd h (not_lt.mpr h6)

lemma six_le_of_not {V : Type*} {G' : SimpleGraph V} (h : ¬ G'.Colorable 5) :
    6 ≤ G'.chromaticNumber := by
  have h5 : ¬ G'.chromaticNumber ≤ 5 := fun h' => h (chromaticNumber_le_iff_colorable.mp h')
  have := Order.add_one_le_of_lt (not_le.mp h5)
  calc (6 : ℕ∞) = 5 + 1 := by norm_num
    _ ≤ _ := this

lemma not_col (hG : Erdos917.IsKCritical G 6) : ¬ G.Colorable 5 := by
  intro h
  have h1 := chromaticNumber_le_iff_colorable.mpr h
  rw [hG.1.1] at h1
  norm_num at h1

lemma col6 (hG : Erdos917.IsKCritical G 6) : G.Colorable 6 :=
  chromaticNumber_le_iff_colorable.mp (by rw [hG.1.1])

lemma edge_col (hG : Erdos917.IsKCritical G 6) (e : Sym2 (Fin n)) (he : e ∈ G.edgeSet) :
    (G.deleteEdges {e}).Colorable 5 := by
  have h := hG.2 e he
  unfold IsCriticalEdge IsCriticalEdges at h
  rw [hG.1.1] at h
  exact col5_of_lt (by exact_mod_cast h)

lemma vert_col (hG : Erdos917.IsKCritical G 6) (v : Fin n) :
    ∃ g : Fin n → Fin 5, ∀ u w, G.Adj u w → u ≠ v → w ≠ v → g u ≠ g w := by
  have h1 := hG.1.2 v
  unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts at h1
  have htop : (⊤ : G.Subgraph).coe.chromaticNumber ≤ 6 :=
    chromaticNumber_le_iff_colorable.mpr ((col6 hG).of_hom (Subgraph.topIso).toHom)
  obtain ⟨C⟩ := col5_of_lt (lt_of_lt_of_le h1 htop)
  refine ⟨fun u => if h : u = v then 0 else C ⟨u, by simp [h]⟩, ?_⟩
  intro u w huw hu hw
  simp only [dif_neg hu, dif_neg hw]
  apply C.valid
  rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
  exact ⟨by simp, by simpa using hu, by simp, by simpa using hw, huw⟩

lemma xy_col (hG : Erdos917.IsKCritical G 6) {x y : Fin n} (hxy : G.Adj x y) :
    ∃ g : Fin n → Fin 5, (∀ u w, G.Adj u w → s(u, w) ≠ s(x, y) → g u ≠ g w) ∧ g x = g y := by
  obtain ⟨C⟩ := edge_col hG s(x, y) (by simpa using hxy)
  have gp : ∀ u w, G.Adj u w → s(u, w) ≠ s(x, y) → C u ≠ C w := fun u w h hne =>
    C.valid (by rw [deleteEdges_adj]; exact ⟨h, by simpa using hne⟩)
  refine ⟨fun u => C u, gp, ?_⟩
  by_contra hne
  apply not_col hG
  refine colorable_of _ (fun u => C u) (fun u w h => ?_)
  by_cases he : s(u, w) = s(x, y)
  · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact Ne.symm hne
  · exact gp u w h he

/- ### The Hajós sum is `6`-critical -/

variable {x y : Fin n}

lemma Ly_ne_M1 (x y : Fin n) : L y ≠ M x 1 := by
  intro h; have := congrArg Fin.val h; rw [M_val] at this; simp at this; omega

lemma L_eq_iff {u w : Fin n} : L u = L w ↔ u = w := L.injective.eq_iff

lemma M_eq_iff {a b : Fin 6} : M x a = M x b ↔ a = b := (M x).injective.eq_iff

theorem edge_crit (hG : Erdos917.IsKCritical G 6) (hxy : G.Adj x y) (e : Sym2 (Fin (n + 5)))
    (he : e ∈ (H G x y).edgeSet) : ((H G x y).deleteEdges {e}).Colorable 5 := by
  induction e using Sym2.ind with
  | h p q =>
  have hpq : (H G x y).Adj p q := he
  have wrap : ∀ (g : Fin n → Fin 5) (κ : Fin 6 → Fin 5), κ 0 = g x →
      (∀ u w, G.Adj u w → s(u, w) ≠ s(x, y) → s(L u, L w) ≠ s(p, q) → g u ≠ g w) →
      (s(L y, M x 1) ≠ s(p, q) → g y ≠ κ 1) →
      (∀ a b : Fin 6, a ≠ b → s(a, b) ≠ s(0, 1) → s(M x a, M x b) ≠ s(p, q) → κ a ≠ κ b) →
      ((H G x y).deleteEdges {s(p, q)}).Colorable 5 := by
    intro g κ h0 ha hb hc
    refine colorable_of _ (glue g κ) (fun u w h => ?_)
    rw [deleteEdges_adj] at h
    have hne : s(u, w) ≠ s(p, q) := by simpa using h.2
    exact glue_proper G x y g κ h0 (fun p' q' => s(p', q') = s(p, q)) ha (fun h1 _ => hb h1) hc
      u w h.1 hne (by rwa [Sym2.eq_swap])
  rw [H_adj] at hpq
  rcases hpq with ⟨u, w, ⟨hG', hne⟩, rfl, rfl⟩ | ⟨a, b, ⟨hab, hne⟩, rfl, rfl⟩ | ⟨hc', -⟩
  · obtain ⟨C⟩ := edge_col hG s(u, w) (by simpa using hG')
    have gp : ∀ u' w', G.Adj u' w' → s(u', w') ≠ s(u, w) → C u' ≠ C w' := fun u' w' h h' =>
      C.valid (by rw [deleteEdges_adj]; exact ⟨h, by simpa using h'⟩)
    have gxy : C x ≠ C y := gp x y hxy (Ne.symm hne)
    obtain ⟨k0, k1, kp⟩ := kA_ok (C x)
    apply wrap (fun z => C z) (kA (C x)) k0
    · intro u' w' h _ h2
      exact gp u' w' h (fun h3 => h2 (by simpa using congrArg (Sym2.map L) h3))
    · intro _; rw [k1]; exact Ne.symm gxy
    · intro a b hab hne' _; exact kp a b hab (s_ne.mp hne')
  · obtain ⟨g, gp, gxy⟩ := xy_col hG hxy
    obtain ⟨k0, k1, kp⟩ := kB_ok (g x) a b hab (s_ne.mp hne)
    apply wrap g (kB (g x) a b) k0
    · intro u' w' h h1 _; exact gp u' w' h h1
    · intro _; rw [← gxy]; exact Ne.symm k1
    · intro a' b' hab' hne' h3
      apply kp a' b' hab' (s_ne.mp hne')
      intro h4
      apply h3
      rcases h4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
  · obtain ⟨g, gp, _⟩ := xy_col hG hxy
    obtain ⟨k0, _, kp⟩ := kA_ok (g x)
    rcases hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply wrap g (kA (g x)) k0
      · intro u' w' h h1 _; exact gp u' w' h h1
      · intro h; exact absurd rfl h
      · intro a b hab hne' _; exact kp a b hab (s_ne.mp hne')
    · apply wrap g (kA (g x)) k0
      · intro u' w' h h1 _; exact gp u' w' h h1
      · intro h; exact absurd Sym2.eq_swap h
      · intro a b hab hne' _; exact kp a b hab (s_ne.mp hne')

theorem vert_crit (hG : Erdos917.IsKCritical G 6) (hxy : G.Adj x y) (v : Fin (n + 5)) :
    ((⊤ : (H G x y).Subgraph).deleteVerts {v}).coe.Colorable 5 := by
  have wrap : ∀ (g : Fin n → Fin 5) (κ : Fin 6 → Fin 5), κ 0 = g x →
      (∀ u w, G.Adj u w → s(u, w) ≠ s(x, y) → L u ≠ v → L w ≠ v → g u ≠ g w) →
      (L y ≠ v → M x 1 ≠ v → g y ≠ κ 1) →
      (∀ a b : Fin 6, a ≠ b → s(a, b) ≠ s(0, 1) → M x a ≠ v → M x b ≠ v → κ a ≠ κ b) →
      ((⊤ : (H G x y).Subgraph).deleteVerts {v}).coe.Colorable 5 := by
    intro g κ h0 ha hb hc
    refine colorable_of _ (fun z => glue g κ z.1) (fun z1 z2 hz => ?_)
    rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hz
    obtain ⟨-, h1, -, h2, hadj⟩ := hz
    simp only [Set.mem_singleton_iff] at h1 h2
    exact glue_proper G x y g κ h0 (fun p q => p = v ∨ q = v)
      (fun u w hh1 hh2 hh3 => ha u w hh1 hh2 (fun e => hh3 (Or.inl e)) (fun e => hh3 (Or.inr e)))
      (fun hh1 _ => hb (fun e => hh1 (Or.inl e)) (fun e => hh1 (Or.inr e)))
      (fun a b hh1 hh2 hh3 => hc a b hh1 hh2 (fun e => hh3 (Or.inl e)) (fun e => hh3 (Or.inr e)))
      z1.1 z2.1 hadj (by rintro (h | h) <;> contradiction) (by rintro (h | h) <;> contradiction)
  by_cases hv : v.val < n
  · obtain ⟨u, rfl⟩ : ∃ u : Fin n, v = L u := ⟨⟨v.val, hv⟩, Fin.ext (by simp)⟩
    obtain ⟨g, gp⟩ := vert_col hG u
    have ha : ∀ u' w', G.Adj u' w' → s(u', w') ≠ s(x, y) → L u' ≠ L u → L w' ≠ L u →
        g u' ≠ g w' := fun u' w' h _ h1 h2 =>
      gp u' w' h (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e]))
    by_cases hux : u = x
    · obtain ⟨k0, k1, kp⟩ := kX_ok (g x) (g y)
      apply wrap g (kX (g x) (g y)) k0 ha
      · intro _ _; exact Ne.symm k1
      · intro a b hab _ h1 h2
        refine kp a b (fun e => h1 ?_) (fun e => h2 ?_) hab
        · rw [e, M_zero, hux]
        · rw [e, M_zero, hux]
    · obtain ⟨k0, k1, kp⟩ := kA_ok (g x)
      apply wrap g (kA (g x)) k0 ha
      · intro h1 _
        rw [k1]
        by_cases huy : u = y
        · exact absurd (by rw [huy]) h1
        · exact Ne.symm (gp x y hxy (Ne.symm hux) (Ne.symm huy))
      · intro a b hab hne _ _; exact kp a b hab (s_ne.mp hne)
  · obtain ⟨a', ha0, rfl⟩ : ∃ a' : Fin 6, a' ≠ 0 ∧ v = M x a' := by
      refine ⟨⟨v.val - n + 1, by have := v.isLt; omega⟩, fun e => ?_, Fin.ext ?_⟩
      · have := congrArg Fin.val e; simp at this
      · rw [M_val]; show v.val = if v.val - n + 1 = 0 then x.val else n + (v.val - n + 1) - 1
        rw [if_neg (by omega)]; omega
    obtain ⟨g, gp, gxy⟩ := xy_col hG hxy
    obtain ⟨k0, k1, kp⟩ := kV_ok (g x) a' ha0
    apply wrap g (kV (g x) a') k0
    · intro u w h h1 _ _; exact gp u w h h1
    · intro _ h2
      rw [← gxy]
      exact Ne.symm (k1 (fun e => h2 (by rw [e])))
    · intro a b hab hne h1 h2
      exact kp a b hab (s_ne.mp hne) (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e]))

theorem H_not_col (hG : Erdos917.IsKCritical G 6) (hxy : G.Adj x y) : ¬ (H G x y).Colorable 5 := by
  rintro ⟨C⟩
  have hadjM : ∀ a b : Fin 6, a ≠ b → ¬((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) →
      (H G x y).Adj (M x a) (M x b) := by
    intro a b hab h
    rw [H_adj]; right; left; exact ⟨a, b, ⟨hab, s_ne.mpr h⟩, rfl, rfl⟩
  let τ : Fin 5 → Fin 5 := fun j => C (M x j.succ)
  have hτ : Function.Injective τ := by
    intro i j h
    by_contra hij
    exact C.valid (hadjM i.succ j.succ (fun e => hij (Fin.succ_injective _ e))
      (fun h => h.elim (fun h => Fin.succ_ne_zero _ h.1) (fun h => Fin.succ_ne_zero _ h.2))) h
  obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.mp hτ) (C (L x))
  have hj0 : j = 0 := by
    by_contra hj0
    refine C.valid (hadjM 0 j.succ (Fin.succ_ne_zero j).symm ?_) ?_
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hj0 (Fin.succ_injective _ (h.trans Fin.succ_zero_eq_one.symm))
      · exact absurd h (by decide)
    · rw [M_zero]; exact hj.symm
  subst hj0
  have h1 : C (M x 1) = C (L x) := hj
  have hy1 : C (L y) ≠ C (M x 1) := by
    apply C.valid; rw [H_adj]; right; right; exact ⟨Or.inl ⟨rfl, rfl⟩, Ly_ne_M1 x y⟩
  apply not_col hG
  refine colorable_of _ (fun z => C (L z)) (fun u w h => ?_)
  by_cases he : s(u, w) = s(x, y)
  · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [← h1]; exact Ne.symm hy1
    · rw [← h1]; exact hy1
  · apply C.valid; rw [H_adj]; left; exact ⟨u, w, ⟨h, he⟩, rfl, rfl⟩

lemma colorable_six_of {V : Type*} {G' : SimpleGraph V} (u w : V)
    (h : (G'.deleteEdges {s(u, w)}).Colorable 5) : G'.Colorable 6 := by
  classical
  obtain ⟨C⟩ := h
  refine ⟨Coloring.mk (fun z => if z = u then (5 : Fin 6) else Fin.castSucc (C z)) ?_⟩
  intro a b hab
  have la := (C a).isLt; have lb := (C b).isLt
  by_cases ha : a = u <;> by_cases hb : b = u
  · exact absurd (ha.trans hb.symm) hab.ne
  · simp only [if_pos ha, if_neg hb]; intro e; have := congrArg Fin.val e; simp at this; omega
  · simp only [if_neg ha, if_pos hb]; intro e; have := congrArg Fin.val e; simp at this; omega
  · simp only [if_neg ha, if_neg hb]
    intro e
    apply C.valid _ (Fin.castSucc_injective _ e)
    rw [deleteEdges_adj]
    refine ⟨hab, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    tauto

theorem chromaticNumber_H (hG : Erdos917.IsKCritical G 6) (hxy : G.Adj x y) :
    (H G x y).chromaticNumber = 6 := by
  apply le_antisymm
  · have hedge : s(L y, M x 1) ∈ (H G x y).edgeSet := by
      show (H G x y).Adj _ _
      rw [H_adj]; right; right; exact ⟨Or.inl ⟨rfl, rfl⟩, Ly_ne_M1 x y⟩
    exact chromaticNumber_le_iff_colorable.mpr
      (colorable_six_of _ _ (edge_crit hG hxy _ hedge))
  · exact six_le_of_not (H_not_col hG hxy)

theorem isKCritical_H (hG : Erdos917.IsKCritical G 6) (hxy : G.Adj x y) :
    Erdos917.IsKCritical (H G x y) 6 := by
  refine ⟨⟨by rw [chromaticNumber_H hG hxy]; rfl, fun v => ?_⟩, fun e he => ?_⟩
  · unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts
    have htop : 6 ≤ (⊤ : (H G x y).Subgraph).coe.chromaticNumber :=
      six_le_of_not (fun h => H_not_col hG hxy (h.of_hom (Subgraph.topIso).symm.toHom))
    refine lt_of_lt_of_le ?_ htop
    exact lt_of_le_of_lt (chromaticNumber_le_iff_colorable.mpr (vert_crit hG hxy v)) (by norm_num)
  · unfold IsCriticalEdge IsCriticalEdges
    rw [chromaticNumber_H hG hxy]
    exact lt_of_le_of_lt (chromaticNumber_le_iff_colorable.mpr (edge_crit hG hxy e he))
      (by norm_num)

/- ### Counting edges -/

lemma K6'_ncard : K6'.edgeSet.ncard = 14 := by
  rw [K6', edgeSet_deleteEdges, Set.ncard_sdiff_singleton_of_mem (by simp)]
  rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two]
  simp; decide

theorem ncard_H (hxy : G.Adj x y) : (H G x y).edgeSet.ncard = G.edgeSet.ncard + 14 := by
  have hmem : s(x, y) ∈ G.edgeSet := by simpa using hxy
  have hpos : 0 < G.edgeSet.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, hmem⟩
  rw [H, edgeSet_sup, edgeSet_sup, edgeSet_map, edgeSet_map, edgeSet_deleteEdges,
    edgeSet_edge_of_ne (Ly_ne_M1 x y)]
  have hd1 : Disjoint (L.sym2Map '' (G.edgeSet \ {s(x, y)})) ((M x).sym2Map '' K6'.edgeSet) := by
    rw [Set.disjoint_left]
    rintro z ⟨t, -, rfl⟩ ⟨t', ht', he⟩
    induction t using Sym2.ind with
    | h u w =>
    induction t' using Sym2.ind with
    | h a b =>
    have hab : a ≠ b := by
      intro e; subst e; simp [K6'] at ht'
    simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk, Sym2.eq_iff] at he
    have hu := u.isLt; have hw := w.isLt
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
      rw [M_val, L_val] at e1 e2
      exact hab (Fin.ext (by split_ifs at e1 e2 <;> omega))
    · have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
      rw [M_val, L_val] at e1 e2
      exact hab (Fin.ext (by split_ifs at e1 e2 <;> omega))
  have hd2 : Disjoint (L.sym2Map '' (G.edgeSet \ {s(x, y)}) ∪ (M x).sym2Map '' K6'.edgeSet)
      {s(L y, M x 1)} := by
    rw [Set.disjoint_singleton_right]
    rintro (⟨t, -, ht⟩ | ⟨t, ht', ht⟩)
    · induction t using Sym2.ind with
      | h u w =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk, Sym2.eq_iff] at ht
      have hu := u.isLt; have hw := w.isLt
      rcases ht with ⟨_, h2⟩ | ⟨h1, _⟩
      · have e2 := congrArg Fin.val h2; rw [M_val, L_val] at e2; simp at e2; omega
      · have e1 := congrArg Fin.val h1; rw [M_val, L_val] at e1; simp at e1; omega
    · induction t using Sym2.ind with
      | h a b =>
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk, Sym2.eq_iff] at ht
      have hne := hxy.ne
      rcases ht with ⟨h1, _⟩ | ⟨_, h2⟩
      · have e1 := congrArg Fin.val h1; rw [M_val, L_val] at e1
        have hy := y.isLt
        split_ifs at e1
        · exact hne (Fin.ext e1)
        · omega
      · have e2 := congrArg Fin.val h2; rw [M_val, L_val] at e2
        have hy := y.isLt
        split_ifs at e2
        · exact hne (Fin.ext e2)
        · omega
  rw [Set.ncard_union_eq hd2 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq hd1 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ L.sym2Map.injective,
    Set.ncard_image_of_injective _ (M x).sym2Map.injective,
    Set.ncard_sdiff_singleton_of_mem hmem, K6'_ncard, Set.ncard_singleton]
  omega

/-- The Hajós step: from a `6`-critical graph on `n` vertices with `e` edges to one on `n + 5`
vertices with `e + 14` edges. -/
theorem hajos_K6 : ∀ n e : ℕ,
    (∃ G : SimpleGraph (Fin n), Erdos917.IsKCritical G 6 ∧ G.edgeSet.ncard = e) →
    (∃ G : SimpleGraph (Fin (n + 5)), Erdos917.IsKCritical G 6 ∧ G.edgeSet.ncard = e + 14) := by
  rintro n e ⟨G, hG, rfl⟩
  have : ∃ x y, G.Adj x y := by
    by_contra h
    push Not at h
    exact not_col hG (colorable_of G (fun _ => 0) (fun u w huw => absurd huw (h u w)))
  obtain ⟨x, y, hxy⟩ := this
  exact ⟨H G x y, isKCritical_H hG hxy, ncard_H hxy⟩

end HilbertDB.E917Hajos

theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_three_dvd_R1.H3 :=
  HilbertDB.E917Hajos.hajos_K6

