import FormalConjectures.ErdosProblems.«559»

/-! Tikhomirov's size-Ramsey lower bound for graphs of maximum degree three. -/

open scoped BigOperators Classical
open Filter Real SimpleGraph

namespace OMA.Tikhomirov

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem exists_sparse_choices {J Ω : Type*} [Fintype J] [Fintype Ω] [DecidableEq Ω]
    [Nonempty Ω] (h r D : ℕ) (hr : r ≤ h) (good : J → Finset Ω)
    (hgood : ∀ j, (good j).card ≤ D)
    (hm : Fintype.card J * h^r * D^r < (Fintype.card Ω)^r) :
    ∃ a : Fin h → Ω, ∀ j, (Finset.univ.filter (fun i => a i ∈ good j)).card < r := by
  classical
  let subsets := (Finset.univ : Finset (Fin h)).powersetCard r
  let pairs := (Finset.univ : Finset J).product subsets
  let assignments (j : J) (s : Finset (Fin h)) : Finset (Fin h → Ω) :=
    Fintype.piFinset (fun i => if i ∈ s then good j else Finset.univ)
  let bad := pairs.biUnion (fun p => assignments p.1 p.2)
  have hsubsets : subsets.card ≤ h^r := by
    simpa [subsets, Finset.card_powersetCard] using Nat.choose_le_pow h r
  have hpairs : pairs.card ≤ Fintype.card J * h^r := by
    simpa [pairs, Finset.card_product] using Nat.mul_le_mul_left (Fintype.card J) hsubsets
  have hassignment (j : J) (s : Finset (Fin h)) (hs : s.card = r) :
      (assignments j s).card ≤ D^r * (Fintype.card Ω)^(h-r) := by
    have hsdiff : ((Finset.univ : Finset (Fin h)) \ s).card = h - r := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hs]
    change (Fintype.piFinset (fun i : Fin h => if i ∈ s then good j else Finset.univ)).card ≤ _
    rw [Fintype.card_piFinset]
    have hprod :
        (∏ i : Fin h, (if i ∈ s then good j else Finset.univ).card) =
            (good j).card^r * (Fintype.card Ω)^(h-r) := by
      have hpiece :=
        Finset.prod_piecewise (Finset.univ : Finset (Fin h)) s
          (fun _ => (good j).card) (fun _ => Fintype.card Ω)
      simpa only [Finset.piecewise, apply_ite Finset.card, Finset.card_univ,
        Finset.univ_inter, Finset.prod_const, hs, hsdiff] using hpiece
    rw [hprod]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (hgood j) _)
  have hbad₀ : bad.card ≤ pairs.card * (D^r * (Fintype.card Ω)^(h-r)) := by
    apply Finset.card_biUnion_le_card_mul
    intro p hp
    have hs : p.2 ∈ subsets := (Finset.mem_product.mp hp).2
    exact hassignment p.1 p.2 (Finset.mem_powersetCard.mp hs).2
  have hbad : bad.card < (Fintype.card Ω)^h := by
    calc
      bad.card ≤ (Fintype.card J * h^r) * (D^r * (Fintype.card Ω)^(h-r)) :=
        hbad₀.trans (Nat.mul_le_mul_right _ hpairs)
      _ = (Fintype.card J * h^r * D^r) * (Fintype.card Ω)^(h-r) := by ac_rfl
      _ < (Fintype.card Ω)^r * (Fintype.card Ω)^(h-r) :=
        Nat.mul_lt_mul_of_pos_right hm (pow_pos Fintype.card_pos _)
      _ = (Fintype.card Ω)^h := by rw [← pow_add, Nat.add_sub_of_le hr]
  have hex : ∃ a : Fin h → Ω, a ∉ bad := by
    by_contra! hall
    have huniv : (Finset.univ : Finset (Fin h → Ω)) ⊆ bad := fun a _ => hall a
    have hge := Finset.card_le_card huniv
    have hge' : (Fintype.card Ω)^h ≤ bad.card := by
      simpa [Fintype.card_fun] using hge
    exact (not_lt_of_ge hge') hbad
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, fun j => ?_⟩
  by_contra! hlarge
  obtain ⟨s, hsubset, hs⟩ := Finset.exists_subset_card_eq hlarge
  have hs' : s ∈ subsets := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hs⟩
  apply ha
  apply Finset.mem_biUnion.mpr
  refine ⟨(j,s), Finset.mem_product.mpr ⟨Finset.mem_univ _, hs'⟩, ?_⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  by_cases hi : i ∈ s
  · simpa only [if_pos hi] using (Finset.mem_filter.mp (hsubset hi)).2
  · simp [hi]

private def ParentMap {V : Type*} (G : SimpleGraph V) (v : V) {n : ℕ}
    (parent : Fin n → Fin (n+1)) :=
  {f : Fin (n+1) → V // f 0 = v ∧ ∀ i : Fin n, G.Adj (f (parent i)) (f i.succ)}

private noncomputable instance {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    {n : ℕ} (parent : Fin n → Fin (n+1)) : Fintype (ParentMap G v parent) := by
  classical
  unfold ParentMap
  infer_instance

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem parentMap_card {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    {n d : ℕ} (parent : Fin n → Fin (n+1))
    (hp : ∀ i, (parent i).val < i.succ.val) (hd : G.maxDegree ≤ d) :
    Fintype.card (ParentMap G v parent) ≤ d^n := by
  classical
  have hex (x : V) : Nonempty (G.neighborSet x ↪ Fin d) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [G.card_neighborSet_eq_degree, Fintype.card_fin]
    exact (G.degree_le_maxDegree x).trans hd
  let choice (x : V) : G.neighborSet x ↪ Fin d := Classical.choice (hex x)
  let code (f : ParentMap G v parent) (i : Fin n) : Fin d :=
    choice (f.val (parent i)) ⟨f.val i.succ, f.property.2 i⟩
  have hcode : Function.Injective code := by
    intro f g hfg
    apply Subtype.ext
    funext i
    suffices same : ∀ k : ℕ, ∀ i : Fin (n+1), i.val = k → f.val i = g.val i by
      exact same i.val i rfl
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      refine Fin.cases ?_ (fun j hj => ?_) i hi
      · intro _
        exact f.property.1.trans g.property.1.symm
      · have he : f.val (parent j) = g.val (parent j) :=
          ih _ ((hp j).trans_eq hj) _ rfl
        have hc := congrFun hfg j
        change choice (f.val (parent j)) ⟨f.val j.succ, f.property.2 j⟩ =
          choice (g.val (parent j)) ⟨g.val j.succ, g.property.2 j⟩ at hc
        let b : G.neighborSet (f.val (parent j)) :=
          ⟨g.val j.succ, he.symm ▸ g.property.2 j⟩
        have transport (u v w : V) (huv : u = v) (hw : G.Adj v w) :
            choice u ⟨w, huv.symm ▸ hw⟩ = choice v ⟨w, hw⟩ := by
          subst v
          rfl
        have hval : choice (f.val (parent j)) b =
            choice (g.val (parent j)) ⟨g.val j.succ, g.property.2 j⟩ :=
          transport _ _ _ he (g.property.2 j)
        rw [← hval] at hc
        exact congrArg Subtype.val ((choice _).injective hc)
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective code hcode

private def leafOrder {m : ℕ} (σ : Equiv.Perm (Fin m)) : Fin (m+1) → Fin (m+1) :=
  Fin.cases 0 (fun i => (σ i).succ)

private theorem leafOrder_injective {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    Function.Injective (leafOrder σ) := by
  intro i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j
    · intro _
      rfl
    · intro h
      have hnat := congrArg Fin.val h
      simp [leafOrder] at hnat
  · refine Fin.cases ?_ (fun b => ?_) j
    · intro h
      have hnat := congrArg Fin.val h
      simp [leafOrder] at hnat
    · intro h
      have he : (σ a).succ = (σ b).succ := h
      exact congrArg Fin.succ (σ.injective (Fin.succ_injective _ he))

private theorem card_matching_leaf_orders {V : Type*} [Fintype V]
    (G : SimpleGraph V) {m d : ℕ} (f : Fin (m+1) → V)
    (hf : Function.Injective f) (hd : G.maxDegree ≤ d) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin m) =>
      ∀ i : Fin m, G.Adj (f (leafOrder σ i.castSucc)) (f (leafOrder σ i.succ)))).card ≤ d^m := by
  classical
  let S := Finset.univ.filter (fun σ : Equiv.Perm (Fin m) =>
    ∀ i : Fin m, G.Adj (f (leafOrder σ i.castSucc)) (f (leafOrder σ i.succ)))
  let e (σ : S) : ParentMap (n := m) G (f 0) Fin.castSucc :=
    ⟨f ∘ leafOrder σ.val, rfl, (Finset.mem_filter.mp σ.property).2⟩
  have he : Function.Injective e := by
    intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have hz := congrArg (fun p : ParentMap (n := m) G (f 0) Fin.castSucc => p.val i.succ) h
    have hi : f ((σ.val i).succ) = f ((τ.val i).succ) := hz
    exact Fin.succ_injective _ (hf hi)
  have hc : S.card ≤ Fintype.card (ParentMap (n := m) G (f 0) Fin.castSucc) := by
    simpa using Fintype.card_le_of_injective e he
  exact hc.trans (parentMap_card G (f 0) Fin.castSucc (fun i => by simp) hd)

private noncomputable def rootedChoices {V Ω : Type*} [Fintype Ω] {n : ℕ}
    (U : Ω → SimpleGraph (Fin (n+1))) (G : SimpleGraph V) (v : V) : Finset Ω :=
  Finset.univ.filter (fun σ => ∃ f : (U σ).Copy G, f 0 = v)

private theorem mem_rootedChoices {V Ω : Type*} [Fintype Ω] {n : ℕ}
    {U : Ω → SimpleGraph (Fin (n+1))} {G : SimpleGraph V} {v : V} {σ : Ω} :
    σ ∈ rootedChoices U G v ↔ ∃ f : (U σ).Copy G, f 0 = v := by
  simp only [rootedChoices, Finset.mem_filter, Finset.mem_univ, true_and]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem card_compatible_components {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) {n m d : ℕ}
    (parent : Fin n → Fin (n+1)) (hp : ∀ i, (parent i).val < i.succ.val)
    (leaf : Fin (m+1) ↪ Fin (n+1))
    (U : Equiv.Perm (Fin m) → SimpleGraph (Fin (n+1)))
    (htree : ∀ σ i, (U σ).Adj (parent i) i.succ)
    (hpath : ∀ σ (i : Fin m),
       (U σ).Adj (leaf (leafOrder σ i.castSucc)) (leaf (leafOrder σ i.succ)))
    (hd : G.maxDegree ≤ d) :
    (rootedChoices U G v).card ≤ d^(n+m) := by
  classical
  let P := ParentMap G v parent
  let good (f : P) : Finset (Equiv.Perm (Fin m)) :=
    if Function.Injective f.val then
      Finset.univ.filter (fun σ =>
        ∀ i : Fin m,
          G.Adj (f.val (leaf (leafOrder σ i.castSucc))) (f.val (leaf (leafOrder σ i.succ))))
    else ∅
  let S := rootedChoices U G v
  let emb (σ : S) : (U σ.val).Copy G :=
    Classical.choose (mem_rootedChoices.mp σ.property)
  have hroot (σ : S) : emb σ 0 = v :=
    Classical.choose_spec (mem_rootedChoices.mp σ.property)
  let pref (σ : S) : P :=
    ⟨emb σ, hroot σ, fun i => (emb σ).toHom.map_rel' (htree σ.val i)⟩
  have hmem (σ : S) : σ.val ∈ good (pref σ) := by
    have hinj : Function.Injective (pref σ).val := (emb σ).injective
    simp only [good, if_pos hinj, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    exact (emb σ).toHom.map_rel' (hpath σ.val i)
  let code (σ : S) : Σ f : P, ↥(good f) := ⟨pref σ, ⟨σ.val, hmem σ⟩⟩
  have hi : Function.Injective code := by
    intro σ τ he
    exact Subtype.ext (congrArg (fun z : Σ f : P, ↥(good f) => z.2.val) he)
  have hcount (f : P) : (good f).card ≤ d^m := by
    by_cases hf : Function.Injective f.val
    · simpa only [good, if_pos hf, Function.comp_apply] using
        card_matching_leaf_orders G (f.val ∘ leaf) (hf.comp leaf.injective) hd
    · simp [good, hf]
  calc
    S.card ≤ Fintype.card (Σ f : P, ↥(good f)) := by
      simpa using Fintype.card_le_of_injective code hi
    _ = ∑ f : P, (good f).card := by simp [Fintype.card_sigma]
    _ ≤ ∑ _f : P, d^m := Finset.sum_le_sum (fun f _ => hcount f)
    _ = Fintype.card P * d^m := by simp [Nat.mul_comm]
    _ ≤ d^n * d^m := Nat.mul_le_mul_right _ (parentMap_card G v parent hp hd)
    _ = d^(n+m) := (pow_add _ _ _).symm

private def BallVertex {V : Type*} (G : SimpleGraph V) (v : V) (k : ℕ) :=
  {w : V // ∃ i : Fin (k+1), ∃ f : ParentMap (n := i.val) G v Fin.castSucc,
    f.val (Fin.last i.val) = w}

private noncomputable instance {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v : V) (k : ℕ) : Fintype (BallVertex G v k) := by
  classical
  unfold BallVertex
  infer_instance

private theorem sum_pow_ball (d : ℕ) (hd : 2 ≤ d) :
    ∀ k, (∑ i ∈ Finset.range (k+1), d^i) ≤ d^(k+1) := by
  intro k
  induction k with
  | zero => simpa using (show 1 ≤ d by omega)
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    calc
      (∑ i ∈ Finset.range (k+1), d^i) + d^(k+1) ≤ d^(k+1) + d^(k+1) :=
        Nat.add_le_add_right ih _
      _ = d^(k+1) * 2 := by omega
      _ ≤ d^(k+1) * d := Nat.mul_le_mul_left _ hd

private theorem card_ball {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    (k d : ℕ) (hd : 2 ≤ d) (hG : G.maxDegree ≤ d) :
    Fintype.card (BallVertex G v k) ≤ d^(k+1) := by
  classical
  let P (i : Fin (k+1)) := ParentMap (n := i.val) G v Fin.castSucc
  let lengthOf (w : BallVertex G v k) := Classical.choose w.property
  let pathOf (w : BallVertex G v k) : P (lengthOf w) :=
    Classical.choose (Classical.choose_spec w.property)
  have endpoint (w : BallVertex G v k) :
      (pathOf w).val (Fin.last (lengthOf w).val) = w.val :=
    Classical.choose_spec (Classical.choose_spec w.property)
  let code (w : BallVertex G v k) : Σ i, P i := ⟨lengthOf w, pathOf w⟩
  have hcode : Function.Injective code := by
    intro u w he
    apply Subtype.ext
    have h := congrArg (fun z : Σ i, P i => z.2.val (Fin.last z.1.val)) he
    simpa only [code, endpoint] using h
  calc
    Fintype.card (BallVertex G v k) ≤ Fintype.card (Σ i, P i) :=
      Fintype.card_le_of_injective code hcode
    _ = ∑ i, Fintype.card (P i) := by rw [Fintype.card_sigma]
    _ ≤ ∑ i : Fin (k+1), d^i.val := Finset.sum_le_sum (fun i _ =>
      parentMap_card G v Fin.castSucc (fun j => by simp) hG)
    _ ≤ d^(k+1) := by
      rw [Fin.sum_univ_eq_sum_range]
      exact sum_pow_ball d hd k

private def treeParent {n : ℕ} (i : Fin n) : Fin (n+1) :=
  ⟨i.val / 2, by have := Nat.div_le_self i.val 2; omega⟩

private theorem treeParent_lt {n : ℕ} (i : Fin n) :
    (treeParent i).val < i.succ.val := by
  change i.val / 2 < i.val + 1
  exact Nat.lt_succ_of_le (Nat.div_le_self _ _)

private def binaryTree (n : ℕ) : SimpleGraph (Fin (n+1)) where
  Adj u v := (∃ i : Fin n, u = treeParent i ∧ v = i.succ) ∨
    (∃ i : Fin n, v = treeParent i ∧ u = i.succ)
  symm.symm _ _ h := h.symm
  loopless.irrefl u h := by
    rcases h with ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩
    all_goals
      have h := congrArg Fin.val (h1.symm.trans h2)
      have hlt := treeParent_lt i
      omega

private def treeWithLeafCycle {n m : ℕ} (leaf : Fin (m+1) ↪ Fin (n+1))
    (σ : Equiv.Perm (Fin m)) : SimpleGraph (Fin (n+1)) :=
  binaryTree n ⊔
    (SimpleGraph.cycleGraph (m+1)).map (fun i => leaf (leafOrder σ i))

private theorem tree_edges_present {n m : ℕ} (leaf : Fin (m+1) ↪ Fin (n+1))
    (σ : Equiv.Perm (Fin m)) (i : Fin n) :
    (treeWithLeafCycle leaf σ).Adj (treeParent i) i.succ := by
  exact Or.inl (Or.inl ⟨i, rfl, rfl⟩)

private theorem leaf_path_present {n m : ℕ} (leaf : Fin (m+1) ↪ Fin (n+1))
    (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (treeWithLeafCycle leaf σ).Adj (leaf (leafOrder σ i.castSucc))
      (leaf (leafOrder σ i.succ)) := by
  apply Or.inr
  apply SimpleGraph.map_adj_apply'
  · apply SimpleGraph.cycleGraph_adj'.mpr
    right
    rw [Fin.sub_val_of_le (show i.castSucc ≤ i.succ by change i.val ≤ i.val+1; omega)]
    simp
  · apply leaf.injective.ne
    apply (leafOrder_injective σ).ne
    intro h
    have hv := congrArg Fin.val h
    simp at hv

private def treeLeaves (k : ℕ) :
    Fin ((2^k-1)+1) ↪ Fin ((2^(k+1)-2)+1) where
  toFun i := ⟨2^k-1 + i.val, by
    have hpos : 0 < (2 : ℕ)^k := by positivity
    have hlt := i.isLt
    rw [pow_succ]
    omega⟩
  inj' i j he := by
    apply Fin.ext
    have hv := congrArg Fin.val he
    change 2^k-1 + i.val = 2^k-1 + j.val at hv
    omega

private theorem tree_neighbor_indices {n : ℕ} {x y : Fin (n+1)}
    (h : (binaryTree n).Adj x y) :
    y.val = (x.val-1)/2 ∨ y.val = 2*x.val+1 ∨ y.val = 2*x.val+2 := by
  rcases h with ⟨i, hi, hj⟩ | ⟨i, hi, hj⟩
  · have h₁ := congrArg Fin.val hi
    have h₂ := congrArg Fin.val hj
    change x.val = i.val/2 at h₁
    change y.val = i.val+1 at h₂
    omega
  · left
    have h₁ := congrArg Fin.val hi
    have h₂ := congrArg Fin.val hj
    change y.val = i.val/2 at h₁
    change x.val = i.val+1 at h₂
    omega

private theorem treeDegree {n : ℕ} (x : Fin (n+1)) (c : Finset ℕ)
    (hc : ∀ y, (binaryTree n).Adj x y → y.val ∈ c) :
    (binaryTree n).degree x ≤ c.card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← Finset.card_image_of_injective _ Fin.val_injective]
  apply Finset.card_le_card
  rintro _ hy
  obtain ⟨y, hy', rfl⟩ := Finset.mem_image.mp hy
  exact hc y (((binaryTree n).mem_neighborFinset x y).mp hy')

private theorem degree_map_emb {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (e : V ↪ W) (x : V)
    [DecidableRel G.Adj] [instMap : DecidableRel (G.map e).Adj] :
    (G.map e).degree (e x) = G.degree x := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have he : (G.map e).neighborFinset (e x) = (G.neighborFinset x).map e := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.map_adj, Finset.mem_map]
    constructor
    · rintro ⟨u,v,huv,hu,rfl⟩
      exact ⟨v, e.injective hu ▸ huv, rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨x,v,hv,rfl,rfl⟩
  rw [he, Finset.card_map]

private theorem standard_cycle_degree {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    (SimpleGraph.cycleGraph n).degree v ≤ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j+2 := ⟨n-2, by omega⟩
  rw [SimpleGraph.cycleGraph_degree_two_le]
  exact Finset.card_le_two

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem treeWithLeafCycle_cubic (k : ℕ) (hk : 1 ≤ k)
    (σ : Equiv.Perm (Fin (2^k-1))) :
    (treeWithLeafCycle (treeLeaves k) σ).maxDegree ≤ 3 := by
  classical
  let n := 2^(k+1)-2
  let m := 2^k-1
  let f : Fin (m+1) ↪ Fin (n+1) :=
    ⟨fun i => treeLeaves k (leafOrder σ i),
      (treeLeaves k).injective.comp (leafOrder_injective σ)⟩
  let C := (SimpleGraph.cycleGraph (m+1)).map f
  let e : treeWithLeafCycle (treeLeaves k) σ ≃g (binaryTree n ⊔ C) :=
    ⟨Equiv.refl _, fun {_ _} => Iff.rfl⟩
  rw [e.maxDegree_eq]
  apply (binaryTree n ⊔ C).maxDegree_le_of_forall_degree_le 3
  intro x
  have hsup : (binaryTree n ⊔ C).degree x ≤ (binaryTree n).degree x + C.degree x := by
    simp only [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup]
    exact Finset.card_union_le _ _
  by_cases hleaf : ∃ y, f y = x
  · obtain ⟨y,rfl⟩ := hleaf
    have hx : 2^k-1 ≤ (f y).val := by
      change 2^k-1 ≤ 2^k-1 + (leafOrder σ y).val
      omega
    have htree : (binaryTree n).degree (f y) ≤ 1 := by
      have he := treeDegree (f y) ({((f y).val-1)/2} : Finset ℕ) (fun z hz => by
        have hzlt := z.isLt
        have hpow : 0 < (2 : ℕ)^k := by positivity
        have hn : n+1 = 2*2^k-1 := by dsimp [n]; rw [pow_succ]; omega
        rcases tree_neighbor_indices hz with he | he | he
        · exact Finset.mem_singleton.mpr he
        · omega
        · omega)
      simpa using he
    have hcycle : C.degree (f y) ≤ 2 := by
      have hm : 2 ≤ m+1 := by
        have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk
        dsimp [m]
        omega
      calc
        C.degree (f y) = (SimpleGraph.cycleGraph (m+1)).degree y :=
          degree_map_emb (SimpleGraph.cycleGraph (m+1)) f y
            (instMap := inferInstanceAs (DecidableRel C.Adj))
        _ ≤ 2 := standard_cycle_degree hm y
    omega
  · have hcycle : C.degree x = 0 := by
      apply (SimpleGraph.degree_eq_zero_iff_notMem_support C x).mpr
      rintro ⟨y, hy⟩
      obtain ⟨u, v, _, hu, _⟩ := (SimpleGraph.map_adj f _ _ _).mp hy
      exact hleaf ⟨u, hu⟩
    have htree : (binaryTree n).degree x ≤ 3 := by
      refine (treeDegree x ({(x.val-1)/2, 2*x.val+1, 2*x.val+2} : Finset ℕ) ?_).trans
        Finset.card_le_three
      intro y hy
      simpa using tree_neighbor_indices hy
    omega

private theorem tree_walk {n : ℕ} :
    ∀ k (v : Fin (n+1)), v.val < 2^(k+1)-1 →
      ∃ p : (binaryTree n).Walk 0 v, p.length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro v hv
    have he : v = 0 := Fin.ext (by norm_num at hv; omega)
    subst v
    exact ⟨.nil, Nat.zero_le _⟩
  | succ k ih =>
    intro v hv
    by_cases hz : v = 0
    · subst v
      exact ⟨.nil, Nat.zero_le _⟩
    · have hvpos : 0 < v.val := by
        by_contra! hz'
        apply hz
        apply Fin.ext
        change v.val = 0
        omega
      let i : Fin n := ⟨v.val-1, by have := v.isLt; omega⟩
      have hi : i.succ = v := by
        apply Fin.ext
        change v.val-1+1 = v.val
        omega
      have hparent : (treeParent i).val < 2^(k+1)-1 := by
        have hpow : 0 < (2 : ℕ)^(k+1) := by positivity
        rw [show 2^(k+1+1) = 2^(k+1)*2 by rw [pow_succ]] at hv
        change (v.val-1)/2 < 2^(k+1)-1
        omega
      obtain ⟨p, hp⟩ := ih (treeParent i) hparent
      have hadj : (binaryTree n).Adj (treeParent i) v := Or.inl ⟨i, rfl, hi.symm⟩
      exact ⟨p.concat hadj, by rw [SimpleGraph.Walk.length_concat]; omega⟩

private theorem leafCycle_walk (k : ℕ) (σ : Equiv.Perm (Fin (2^k-1)))
    (v : Fin ((2^(k+1)-2)+1)) :
    ∃ p : (treeWithLeafCycle (treeLeaves k) σ).Walk 0 v, p.length ≤ k := by
  have hpos : 0 < (2 : ℕ)^(k+1) := by positivity
  have hv := v.isLt
  obtain ⟨p,hp⟩ := tree_walk k v (by omega)
  have hle : binaryTree (2^(k+1)-2) ≤ treeWithLeafCycle (treeLeaves k) σ :=
    fun _ _ hab => Or.inl hab
  exact ⟨p.mapLe hle, (SimpleGraph.Walk.length_mapLe hle p).trans_le hp⟩

private theorem leafCycle_rootEdge (k : ℕ) (hk : 1 ≤ k)
    (σ : Equiv.Perm (Fin (2^k-1))) : ∃ v, (treeWithLeafCycle (treeLeaves k) σ).Adj 0 v := by
  have hpow : 4 ≤ (2 : ℕ)^(k+1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ k+1 by omega)
  let i : Fin (2^(k+1)-2) := ⟨0, by omega⟩
  refine ⟨i.succ, ?_⟩
  have hi : treeParent i = 0 := by
    apply Fin.ext
    change 0 / 2 = 0
    rfl
  rw [← hi]
  exact tree_edges_present (treeLeaves k) σ i

private theorem leafCycle_matching (k : ℕ) (hk : 1 ≤ k)
    (σ : Equiv.Perm (Fin (2^k-1))) :
    ∃ f : Fin (2^(k-1)) ↪ Fin ((2^(k+1)-2)+1),
      ∃ g : Fin (2^(k-1)) ↪ Fin ((2^(k+1)-2)+1),
      Disjoint (Set.range f) (Set.range g) ∧
        ∀ j, (treeWithLeafCycle (treeLeaves k) σ).Adj (f j) (g j) := by
  let M : ℕ := 2^(k-1)
  have hM : 0 < M := by positivity
  have h₁ : (2 : ℕ)^k = M*2 := by
    unfold M
    rw [← pow_succ, show k-1+1=k by omega]
  have h₂ : ((2 : ℕ)^(k+1)-2)+1 = 4*M-1 := by
    rw [pow_succ, h₁]
    omega
  let f : Fin M ↪ Fin ((2^(k+1)-2)+1) :=
    ⟨fun j => ⟨M-1+j.val, by rw [h₂]; have := j.isLt; omega⟩, by
      intro a b h
      apply Fin.ext
      have he := congrArg Fin.val h
      change M-1+a.val = M-1+b.val at he
      omega⟩
  let g : Fin M ↪ Fin ((2^(k+1)-2)+1) :=
    ⟨fun j => ⟨2*(M-1+j.val)+1, by rw [h₂]; have := j.isLt; omega⟩, by
      intro a b h
      apply Fin.ext
      have he := congrArg Fin.val h
      change 2*(M-1+a.val)+1 = 2*(M-1+b.val)+1 at he
      omega⟩
  refine ⟨f,g,Set.disjoint_left.mpr ?_,?_⟩
  · rintro z ⟨a, rfl⟩ ⟨b, he⟩
    have hh := congrArg Fin.val he
    change 2*(M-1+b.val)+1 = M-1+a.val at hh
    have := a.isLt
    omega
  · intro j
    let i : Fin (2^(k+1)-2) := ⟨2*(M-1+j.val), by have := j.isLt; omega⟩
    have he : treeParent i = f j := by
      apply Fin.ext
      change (2*(M-1+j.val))/2 = M-1+j.val
      omega
    have he' : i.succ = g j := rfl
    rw [← he, ← he']
    exact tree_edges_present (treeLeaves k) σ i

set_option maxHeartbeats 4000000 in
private theorem card_binary_components {V : Type*} [Fintype V] (G : SimpleGraph V)
    (x : V) (k d : ℕ) (hd : G.maxDegree ≤ d) :
    (rootedChoices (treeWithLeafCycle (treeLeaves k)) G x).card ≤
        d^((2^(k+1)-2)+(2^k-1)) := by
  classical
  let w := 2^(k+1)-2
  let m := 2^k-1
  let U (σ : Equiv.Perm (Fin m)) : SimpleGraph (Fin (w+1)) :=
    treeWithLeafCycle (treeLeaves k) σ
  exact card_compatible_components (n := w) (m := m) (d := d) G x
    (treeParent (n := w)) (fun i => treeParent_lt i) (treeLeaves k) U
    (fun σ i => tree_edges_present (treeLeaves k) σ i)
    (fun σ i => leaf_path_present (treeLeaves k) σ i) hd

private def SparseRoots {h w : ℕ} (U : Fin h → SimpleGraph (Fin (w+1)) )
    (d r : ℕ) : Prop :=
  ∀ (η : ℕ) (H : SimpleGraph (Fin η)) (v : Fin η), H.maxDegree ≤ d →
    (rootedChoices U H v).card < r

private def disjointTarget {h w : ℕ} (U : Fin h → SimpleGraph (Fin (w+1))) :
    SimpleGraph (Fin h × Fin (w+1)) where
  Adj x y := x.1 = y.1 ∧ (U x.1).Adj x.2 y.2
  symm.symm _ _ h := ⟨h.1.symm, h.1 ▸ h.2.symm⟩
  loopless.irrefl _ h := h.2.ne rfl

private def lowHost {V : Type*} [Fintype V] (H : SimpleGraph V) (d : ℕ) :
    SimpleGraph V where
  Adj u v := H.Adj u v ∧ H.degree u ≤ d ∧ H.degree v ≤ d
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl _ h := h.1.ne rfl

private def redHost {V : Type*} [Fintype V] (H : SimpleGraph V) (d : ℕ) (A : Set V) :
    SimpleGraph V where
  Adj u v := H.Adj u v ∧ ((d < H.degree u ∨ u ∈ A) ∨ (d < H.degree v ∨ v ∈ A))
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.1.ne rfl

private theorem blue_excludes_component {V : Type*} [Fintype V] {w : ℕ}
    (H : SimpleGraph V) (d : ℕ) (U : SimpleGraph (Fin (w+1)))
    (hedge : ∃ v, U.Adj 0 v) (A : Set V)
    (hA : ∀ f : U.Copy (lowHost H d), f 0 ∈ A) :
    ¬ U.IsContained (H \ redHost H d A) := by
  have sub : H \ redHost H d A ≤ lowHost H d := by
    intro x y hadj
    rw [SimpleGraph.sdiff_adj] at hadj
    refine ⟨hadj.1, ?_, ?_⟩
    · exact not_lt.mp (fun he => hadj.2 ⟨hadj.1, Or.inl (Or.inl he)⟩)
    · exact not_lt.mp (fun he => hadj.2 ⟨hadj.1, Or.inr (Or.inl he)⟩)
  rintro ⟨f⟩
  let g : U.Copy (lowHost H d) :=
    ⟨⟨f, fun {u v} h => sub ((f.toHom).map_rel' h)⟩, f.injective⟩
  obtain ⟨v, hv⟩ := hedge
  have he := f.toHom.map_rel' hv
  have ha : f 0 ∈ A := hA g
  rw [SimpleGraph.sdiff_adj] at he
  exact he.2 ⟨he.1, Or.inl (Or.inr ha)⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem red_copy_high_count {V : Type*} [Fintype V] {h w M : ℕ}
    (H : SimpleGraph V) (d : ℕ) (A : Finset V)
    (U : Fin h → SimpleGraph (Fin (w+1)))
    (hm : ∀ i, ∃ u : Fin M ↪ Fin (w+1), ∃ v : Fin M ↪ Fin (w+1),
      Disjoint (Set.range u) (Set.range v) ∧ ∀ j, (U i).Adj (u j) (v j))
    (f : (disjointTarget U).Copy (redHost H d A)) :
    (h - A.card)*M ≤ (Finset.univ.filter (fun v => d < H.degree v)).card := by
  classical
  let touches (i : Fin h) := ∃ x : Fin (w+1), f (i,x) ∈ A
  let B := Finset.univ.filter touches
  let C := (Finset.univ : Finset (Fin h)) \ B
  let high := Finset.univ.filter (fun v => d < H.degree v)
  have hb (i : B) : touches i.val := (Finset.mem_filter.mp i.property).2
  let touchMap (i : B) : A := ⟨f (i.val, (hb i).choose), (hb i).choose_spec⟩
  have htouch : Function.Injective touchMap := by
    intro i j he
    apply Subtype.ext
    exact congrArg Prod.fst (f.injective (congrArg Subtype.val he))
  have hB : B.card ≤ A.card := by simpa using Fintype.card_le_of_injective touchMap htouch
  have hC : h - A.card ≤ C.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  choose u v huv hAdj using hm
  have untouched (i : C) (x : Fin (w+1)) : f (i.val,x) ∉ A := by
    intro hx
    apply (Finset.mem_sdiff.mp i.property).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx⟩
  have hh (i : C) (j : Fin M) :
      d < H.degree (f (i.val,u i.val j)) ∨ d < H.degree (f (i.val,v i.val j)) := by
    have hEdge : (disjointTarget U).Adj (i.val,u i.val j) (i.val,v i.val j) :=
      ⟨rfl, hAdj i.val j⟩
    have hr := f.toHom.map_rel' hEdge
    change H.Adj _ _ ∧ ((_ ∨ _ ∈ (A : Set V)) ∨ (_ ∨ _ ∈ (A : Set V))) at hr
    rcases hr.2 with (hl | hl) | (hr | hr)
    · exact Or.inl hl
    · exact False.elim (untouched i _ hl)
    · exact Or.inr hr
    · exact False.elim (untouched i _ hr)
  let e (i : C) (j : Fin M) :=
    if d < H.degree (f (i.val,u i.val j)) then u i.val j else v i.val j
  have he (i : C) (j : Fin M) : f (i.val,e i j) ∈ high := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hl : d < H.degree (f (i.val,u i.val j))
    · have hchoice : e i j = u i.val j := if_pos hl
      rw [hchoice]
      exact hl
    · have hchoice : e i j = v i.val j := if_neg hl
      rw [hchoice]
      exact (hh i j).resolve_left hl
  have hinj (i : C) : Function.Injective (e i) := by
    intro j j' he'
    unfold e at he'
    split_ifs at he' with hj hj'
    · exact (u i.val).injective he'
    · exact False.elim (Set.disjoint_left.mp (huv i.val) ⟨j, rfl⟩ ⟨j', he'.symm⟩)
    · exact False.elim (Set.disjoint_left.mp (huv i.val) ⟨j', rfl⟩ ⟨j, he'⟩)
    · exact (v i.val).injective he'
  let code (p : C × Fin M) : high := ⟨f (p.1.val, e p.1 p.2), he p.1 p.2⟩
  have hc : Function.Injective code := by
    rintro ⟨i,j⟩ ⟨i',j'⟩ he'
    have heq := f.injective (congrArg Subtype.val he')
    have hi : i = i' := Subtype.ext (congrArg Prod.fst heq)
    subst i'
    exact Prod.ext rfl (hinj i (congrArg Prod.snd heq))
  have hcard : C.card * M ≤ high.card := by
    simpa [Fintype.card_prod] using Fintype.card_le_of_injective code hc
  exact (Nat.mul_le_mul_right M hC).trans hcard

private def BoundedHost (N d : ℕ) :=
  {G : SimpleGraph (Fin N) // G.maxDegree ≤ d}

private noncomputable instance (N d : ℕ) : Fintype (BoundedHost N d) := by
  classical
  unfold BoundedHost
  exact Fintype.ofFinite _

private theorem card_boundedHost (N d : ℕ) :
    Fintype.card (BoundedHost N d) ≤ (N+1)^(d*N) := by
  classical
  have ex (G : BoundedHost N d) (v : Fin N) :
      Nonempty (G.val.neighborSet v ↪ Fin d) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [G.val.card_neighborSet_eq_degree, Fintype.card_fin]
    exact (G.val.degree_le_maxDegree v).trans G.property
  let slot (G : BoundedHost N d) (v : Fin N) := Classical.choice (ex G v)
  let table (G : BoundedHost N d) (v : Fin N) (j : Fin d) : Option (Fin N) :=
    if hj : ∃ u : G.val.neighborSet v, slot G v u = j then some hj.choose.val else none
  have adj_iff (G : BoundedHost N d) (v w : Fin N) :
      G.val.Adj v w ↔ ∃ j, table G v j = some w := by
    constructor
    · intro hw
      let u : G.val.neighborSet v := ⟨w, hw⟩
      let j := slot G v u
      have hj : ∃ u' : G.val.neighborSet v, slot G v u' = j := ⟨u, rfl⟩
      refine ⟨j, ?_⟩
      have he : hj.choose = u := (slot G v).injective hj.choose_spec
      simp only [table, dif_pos hj, he, u]
    · rintro ⟨j, hj⟩
      by_cases h : ∃ u : G.val.neighborSet v, slot G v u = j
      · have he : h.choose.val = w := by simpa only [table, dif_pos h, Option.some.injEq] using hj
        exact he ▸ h.choose.property
      · have hnone : (none : Option (Fin N)) = some w := by
          simpa only [table, dif_neg h] using hj
        cases hnone
  have htable : Function.Injective table := by
    intro G H h
    apply Subtype.ext
    ext v w
    rw [adj_iff G, adj_iff H, h]
  have hc := Fintype.card_le_of_injective table htable
  simpa [Fintype.card_fun, Fintype.card_option, ← pow_mul] using hc

private theorem ball_of_walk {V : Type*} (G : SimpleGraph V) {u v : V}
    {k : ℕ} (p : G.Walk u v) (hp : p.length ≤ k) :
    ∃ i : Fin (k+1), ∃ f : ParentMap (n := i.val) G u Fin.castSucc,
      f.val (Fin.last i.val) = v := by
  let i : Fin (k+1) := ⟨p.length, by omega⟩
  let f : ParentMap (n := i.val) G u Fin.castSucc :=
    ⟨fun j => p.getVert j.val, p.getVert_zero, fun j => p.adj_getVert_succ j.isLt⟩
  exact ⟨i, f, p.getVert_length⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem reduce_to_test_host {η w : ℕ} {Ω : Type*}
    (U : Ω → SimpleGraph (Fin (w+1))) (k d : ℕ) (hd : 2 ≤ d)
    (radius : ∀ σ u, ∃ p : (U σ).Walk 0 u, p.length ≤ k)
    (G : SimpleGraph (Fin η)) (x : Fin η) (hG : G.maxDegree ≤ d) :
    ∃ (J : BoundedHost (d^(k+1)) d) (y : Fin (d^(k+1))),
      ∀ σ, (∃ f : (U σ).Copy G, f 0 = x) →
        ∃ f : (U σ).Copy J.val, f 0 = y := by
  classical
  let B : Set (Fin η) := {v | ∃ i : Fin (k+1),
    ∃ f : ParentMap (n := i.val) G x Fin.castSucc, f.val (Fin.last i.val) = v}
  letI : Fintype B := (inferInstance : Fintype (BallVertex G x k))
  let H := G.induce B
  have ex : Nonempty (B ↪ Fin (d^(k+1))) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin]
    exact card_ball G x k d hd hG
  let e := Classical.choice ex
  let H' := H.map e
  letI : DecidableRel H'.Adj := fun a b => Classical.propDecidable (H'.Adj a b)
  have hH : H.maxDegree ≤ d := (SimpleGraph.Copy.induce G B).isContained.maxDegree_mono.trans hG
  have hH' : H'.maxDegree ≤ d := by
    apply H'.maxDegree_le_of_forall_degree_le d
    intro v
    by_cases hv : ∃ w, e w = v
    · obtain ⟨w,rfl⟩ := hv
      calc
        H'.degree (e w) = H.degree w :=
          degree_map_emb H e w (instMap := inferInstanceAs (DecidableRel H'.Adj))
        _ ≤ d := (H.degree_le_maxDegree w).trans hH
    · have hz : H'.degree v = 0 := by
        apply (SimpleGraph.degree_eq_zero_iff_notMem_support H' v).mpr
        rintro ⟨w,hw⟩
        obtain ⟨a,b,hab,ha,hb⟩ := (SimpleGraph.map_adj e H v w).mp hw
        exact hv ⟨a,ha⟩
      simp [hz]
  let xB : B := ⟨x, ball_of_walk G SimpleGraph.Walk.nil (Nat.zero_le _)⟩
  refine ⟨⟨H', hH'⟩, e xB, ?_⟩
  intro σ hσ
  obtain ⟨f,hf⟩ := hσ
  have hmem (u : Fin (w+1)) : f u ∈ B := by
    obtain ⟨p,hp⟩ := radius σ u
    let q : G.Walk (f 0) (f u) := p.map f.toHom
    have hq : q.length ≤ k := (SimpleGraph.Walk.length_map f.toHom p).trans_le hp
    exact ball_of_walk G (q.copy hf rfl) ((q.length_copy hf rfl).trans_le hq)
  let g (u : Fin (w+1)) : B := ⟨f u, hmem u⟩
  have hg : Function.Injective g := fun _ _ h => f.injective (congrArg Subtype.val h)
  let copy : (U σ).Copy H' :=
    ⟨⟨e ∘ g, fun {_ _} hadj =>
      (SimpleGraph.map_adj_apply (f := e)).mpr (f.toHom.map_rel' hadj)⟩, e.injective.comp hg⟩
  refine ⟨copy, ?_⟩
  apply congrArg e
  exact Subtype.ext hf

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem sampling_margin (t : ℕ) (ht : 1 ≤ t) :
    let k := 100*t
    let h := 2^(1024*t*t)
    let w := 2^(k+1)-2
    let m := 2^k-1
    let d := 2^(8*t)
    let r := d^(k+2)
    let N := d^(k+1)
    Fintype.card (BoundedHost N d × Fin N) * h^r * (d^(w+m))^r <
      (Fintype.card (Equiv.Perm (Fin m)))^r := by
  let k := 100*t
  let b := 1024*t*t
  let h := 2^b
  let w := 2^(k+1)-2
  let m := 2^k-1
  let d := 2^(8*t)
  let r := d^(k+2)
  let N := d^(k+1)
  let a := 8*t*(k+1)
  let B := 2^(k-1)
  let J := BoundedHost N d × Fin N
  change Fintype.card J * h^r * (d^(w+m))^r < (Fintype.card (Equiv.Perm (Fin m)))^r
  have hBpos : 0 < B := by positivity
  have hr : 0 < r := by positivity
  have hd : 0 < d := by positivity
  have hNpos : 0 < N := by positivity
  have hB : 2048*t ≤ B := by
    calc
      2048*t ≤ 2048 * 2^t := Nat.mul_le_mul_left _ (Nat.lt_two_pow_self (n := t)).le
      _ = 2^(t+11) := by rw [pow_add]; norm_num; ac_rfl
      _ ≤ B := Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega)
  have hBt : 2048*t*t ≤ t*B := by
    simpa only [Nat.mul_comm t B] using Nat.mul_le_mul_right t hB
  have ht2 : t ≤ t*t := by simpa using Nat.mul_le_mul_left t ht
  have hk96 : 96*t ≤ k-1 := by dsimp [k]; omega
  have hB4 : 3*B ≤ 4*(B-1) := by omega
  have hscale := Nat.mul_le_mul hk96 hB4
  have hbase : a+2+b ≤ t*B := by
    dsimp [a,b,k]
    nlinarith only [hBt, ht2, ht]
  have hpositive : 0 < t*B := Nat.mul_pos (by omega) hBpos
  have hpower : a+2+b+48*t*B < (k-1)*(B-1) := by
    nlinarith only [hbase, hscale, hpositive]
  have hN : N = 2^a := by simp [N, d, a, pow_mul]
  have hrN : d*N = r := by simp [N, r, pow_succ']
  have har : a ≤ r := by
    calc
      a ≤ 2^a := (Nat.lt_two_pow_self (n := a)).le
      _ = N := hN.symm
      _ ≤ d*N := by
        simpa only [one_mul] using Nat.mul_le_mul_right N (show 1 ≤ d by omega)
      _ = r := hrN
  have hNp : N+1 ≤ 2^(a+1) := by
    rw [pow_succ, ← hN]
    omega
  have hcount : Fintype.card J ≤ 2^((a+2)*r) := by
    calc
      Fintype.card J = Fintype.card (BoundedHost N d)*N := by simp [J]
      _ ≤ (N+1)^(d*N)*N := Nat.mul_le_mul_right _ (card_boundedHost N d)
      _ ≤ (2^(a+1))^r * 2^a := by rw [hrN, ← hN]; gcongr
      _ = 2^((a+1)*r+a) := by rw [← pow_mul, ← pow_add]
      _ ≤ 2^((a+2)*r) := by
        apply Nat.pow_le_pow_right (by decide)
        nlinarith only [har]
  have hkB : (2 : ℕ)^k = 2*B := by
    change (2 : ℕ)^k = 2*2^(k-1)
    rw [← pow_succ', show k-1+1=k by dsimp [k]; omega]
  have hwB : (2 : ℕ)^(k+1) = 4*B := by rw [pow_succ,hkB]; ring
  have hwm : w+m ≤ 6*B := by dsimp [w,m]; omega
  have hD : d^(w+m) ≤ 2^(48*t*B) := by
    dsimp only [d]
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    calc
      8*t*(w+m) ≤ 8*t*(6*B) := Nat.mul_le_mul_left _ hwm
      _ = 48*t*B := by ring
  have hfac : B^(B-1) ≤ m.factorial := by
    have hBm : B ≤ m := by dsimp [m]; omega
    have hmB : m-B = B-1 := by dsimp [m]; omega
    have hF := Nat.factorial_mul_pow_sub_le_factorial hBm
    rw [hmB] at hF
    have hfacPos : 1 ≤ B.factorial := Nat.factorial_pos B
    have hp : B^(B-1) ≤ B.factorial * B^(B-1) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (B^(B-1)) hfacPos
    exact hp.trans hF
  calc
    Fintype.card J * h^r * (d^(w+m))^r ≤
      2^((a+2)*r) * h^r * (2^(48*t*B))^r :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hcount) (Nat.pow_le_pow_left hD _)
    _ = 2^((a+2+b+48*t*B)*r) := by
      dsimp only [h]
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1 <;> ring
    _ < 2^(((k-1)*(B-1))*r) :=
      Nat.pow_lt_pow_right (by decide) (Nat.mul_lt_mul_of_pos_right hpower hr)
    _ = (B^(B-1))^r := by simp [B, pow_mul]
    _ ≤ (Fintype.card (Equiv.Perm (Fin m)))^r := by
      simpa only [Fintype.card_perm, Fintype.card_fin] using Nat.pow_le_pow_left hfac r

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem binaryFamily (k h d : ℕ) (hk : 1 ≤ k) (hd : 2 ≤ d)
    (hr : d^(k+2) ≤ h)
    (margin :
      let w := 2^(k+1)-2
      let m := 2^k-1
      let r := d^(k+2)
      let N := d^(k+1)
      Fintype.card (BoundedHost N d × Fin N) * h^r * (d^(w+m))^r <
        (Fintype.card (Equiv.Perm (Fin m)))^r) :
    let w := 2^(k+1)-2
    ∃ U : Fin h → SimpleGraph (Fin (w+1)),
      (∀ i, (U i).maxDegree ≤ 3 ∧ ∃ v, (U i).Adj 0 v) ∧
      SparseRoots U d (d^(k+2)) ∧
      (∀ i, ∃ f : Fin (2^(k-1)) ↪ Fin (w+1), ∃ g : Fin (2^(k-1)) ↪ Fin (w+1),
        Disjoint (Set.range f) (Set.range g) ∧ ∀ j, (U i).Adj (f j) (g j)) := by
  classical
  let w := 2^(k+1)-2
  let m := 2^k-1
  let r := d^(k+2)
  let N := d^(k+1)
  let Ω := Equiv.Perm (Fin m)
  let J := BoundedHost N d × Fin N
  let U (σ : Ω) := treeWithLeafCycle (treeLeaves k) σ
  let good (j : J) := rootedChoices U j.1.val j.2
  have goodBound (j : J) : (good j).card ≤ d^(w+m) := by
    rcases j with ⟨⟨G, hG⟩, x⟩
    exact card_binary_components G x k d hG
  obtain ⟨φ,hφ⟩ := exists_sparse_choices h r (d^(w+m)) hr good goodBound margin
  refine ⟨U ∘ φ, ?_, ?_, ?_⟩
  · intro i
    exact ⟨treeWithLeafCycle_cubic k hk (φ i), leafCycle_rootEdge k hk (φ i)⟩
  · intro η G x hG
    obtain ⟨H,y,hy⟩ := reduce_to_test_host U k d hd (leafCycle_walk k) G x hG
    have hsub :
        rootedChoices (U ∘ φ) G x ⊆
          (Finset.univ.filter (fun i : Fin h => φ i ∈ good (H,y))) := by
      intro i hi
      have hi' : ∃ f : (U (φ i)).Copy G, f 0 = x :=
        (mem_rootedChoices (U := U ∘ φ) (σ := i)).mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (mem_rootedChoices (U := U) (v := y) (σ := φ i)).mpr (hy (φ i) hi')⟩
    have hlt : (Finset.univ.filter (fun i : Fin h => φ i ∈ good (H,y))).card < r := hφ (H,y)
    have hcard : (rootedChoices (U ∘ φ) G x).card < r :=
      (Finset.card_le_card hsub).trans_lt hlt
    change (rootedChoices (U ∘ φ) G x).card < r
    exact hcard
  · intro i
    exact leafCycle_matching k hk (φ i)

-- The Ramsey-host existence and handshaking facts are adapted from
-- the merged Rödl–Szemerédi proof in this project.
open scoped Classical

def IsRamseyFor {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∀ R : SimpleGraph V, R ≤ H → G ⊑ R ∨ G ⊑ (H \ R)

/-- The number of unordered edges of a finite simple graph. -/
noncomputable def edgeCount {V : Type*} [Finite V] (H : SimpleGraph V) : ℕ :=
  Nat.card H.edgeSet

lemma edgeCount_eq_card_edgeFinset {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] : edgeCount H = H.edgeFinset.card := by
  rw [edgeCount, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

lemma diagonalGraph (n : Nat) : ∃ N : Nat, ∀ R : SimpleGraph (Fin N),
    ¬ (R.CliqueFree n ∧ R.IndepSetFree n) := by
  classical
  let N := (n+n).choose n
  refine ⟨N,?_⟩
  intro R hBoth
  let colour (e : Finset (Fin N)) := decide (R.IsClique (e : Set (Fin N)))
  have hp := Combinatorics.Diagonal.hasRamseyProperty_choose n n colour
    (Finset.univ : Finset (Fin N)) (by simp [N])
  have pair (x y : Fin N) (hxy : x ≠ y) : colour {x,y} = true ↔ R.Adj x y := by
    simp [colour,hxy]
  rcases hp with ⟨S,_,hs,h⟩ | ⟨S,_,hs,h⟩
  · apply hBoth.2 S
    refine ⟨?_,hs⟩
    intro x hx y hy hxy hAdj
    have hpair := h {x,y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
      (by simp [hxy])
    rw [(pair x y hxy).2 hAdj] at hpair
    contradiction
  · apply hBoth.1 S
    refine ⟨?_,hs⟩
    intro x hx y hy hxy
    exact (pair x y hxy).1 (h {x,y}
      (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)) (by simp [hxy]))


/-- There is a finite Ramsey host for every finite graph. -/
lemma ramseyHost_exists {W : Type*} [Finite W] (G : SimpleGraph W) :
    ∃ (N : ℕ) (H : SimpleGraph (Fin N)), IsRamseyFor H G := by
  let _ : Fintype W := Fintype.ofFinite W
  let n := Fintype.card W
  obtain ⟨N, hN⟩ := diagonalGraph n
  refine ⟨N, ⊤, ?_⟩
  intro R _
  have hor : ¬ R.CliqueFree n ∨ ¬ R.IndepSetFree n := not_and_or.mp (hN R)
  let G' : SimpleGraph (Fin n) := G.overFin rfl
  let e : G ≃g G' := SimpleGraph.overFinIso (G := G) rfl
  have hGtop : G ⊑ (⊤ : SimpleGraph (Fin n)) :=
    e.isContained.trans (SimpleGraph.IsContained.of_le le_top)
  rcases hor with hred | hblue
  · left
    have htop : (⊤ : SimpleGraph (Fin n)) ⊑ R := by
      simpa only [SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained n).mp hred
    exact hGtop.trans htop
  · right
    have hblue' : ¬ Rᶜ.CliqueFree n := by
      simpa only [SimpleGraph.cliqueFree_compl] using hblue
    have htop : (⊤ : SimpleGraph (Fin n)) ⊑ Rᶜ := by
      simpa only [SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained n).mp hblue'
    have hdiff : (⊤ \ R : SimpleGraph (Fin N)) = Rᶜ := by
      ext u v
      simp [SimpleGraph.compl_adj]
    rw [hdiff]
    exact hGtop.trans htop

/-- Every vertex in the support accounts for at least one incidence. -/
lemma card_support_le_twice_edgeCount {V : Type*} [Fintype V] (H : SimpleGraph V) :
    H.support.toFinset.card ≤ 2 * edgeCount H := by
  classical
  rw [edgeCount_eq_card_edgeFinset]
  calc
    H.support.toFinset.card = ∑ _v ∈ H.support, 1 := by simp
    _ ≤ ∑ v ∈ H.support, H.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      exact (H.degree_pos_iff_mem_support v).mpr (by simpa using hv)
    _ = 2 * H.edgeFinset.card := H.sum_degrees_support_eq_twice_card_edges

lemma exists_card_mul_le_of_sum_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℕ) (S : ℕ) (h : ∑ a, f a ≤ S) :
    ∃ a : α, Fintype.card α * f a ≤ S := by
  by_contra! hn
  have hlt : (∑ _a : α, S) < ∑ a : α, Fintype.card α * f a := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro a _
    exact hn a
  have hlt' : Fintype.card α * S < Fintype.card α * ∑ a : α, f a := by
    simpa [Finset.mul_sum] using hlt
  have hle : Fintype.card α * ∑ a : α, f a ≤ Fintype.card α * S :=
    Nat.mul_le_mul_left _ h
  omega

private theorem lowHost_degree {V : Type*} [Fintype V] (H : SimpleGraph V) (d : ℕ) :
    (lowHost H d).maxDegree ≤ d := by
  apply (lowHost H d).maxDegree_le_of_forall_degree_le d
  intro v
  by_cases hv : H.degree v ≤ d
  · have hsub : (lowHost H d).neighborFinset v ⊆ H.neighborFinset v := by
      intro w hw
      have he : (lowHost H d).Adj v w := ((lowHost H d).mem_neighborFinset v w).mp hw
      exact (H.mem_neighborFinset v w).mpr he.1
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact (Finset.card_le_card hsub).trans hv
  · have hempty : (lowHost H d).neighborFinset v = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have he : (lowHost H d).Adj v w := ((lowHost H d).mem_neighborFinset v w).mp hw
      exact hv he.2.1
    simp [← SimpleGraph.card_neighborFinset_eq_degree, hempty]

private noncomputable def rootSet {V : Type*} [Fintype V] {w : ℕ}
    (H : SimpleGraph V) (G : SimpleGraph (Fin (w+1))) : Finset V :=
  Finset.univ.filter (fun v => ∃ f : G.Copy H, f 0 = v)

private theorem mem_rootSet {V : Type*} [Fintype V] {w : ℕ}
    {H : SimpleGraph V} {G : SimpleGraph (Fin (w+1))} {v : V} :
    v ∈ rootSet H G ↔ ∃ f : G.Copy H, f 0 = v := by
  simp only [rootSet, Finset.mem_filter, Finset.mem_univ, true_and]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem rareRoot {η h w d r : ℕ} (hh : 0 < h)
    (H : SimpleGraph (Fin η)) (U : Fin h → SimpleGraph (Fin (w+1)))
    (hU : ∀ i, ∃ v, (U i).Adj 0 v)
    (hSparse : SparseRoots U d r) (hH : H.maxDegree ≤ d) :
    ∃ i, h * (rootSet H (U i)).card ≤ 2 * edgeCount H * r := by
  classical
  let selectors (v : H.support) := rootedChoices U H v.val
  let pc : (Σ i : Fin h, rootSet H (U i)) → Σ v : H.support, selectors v := fun p => by
    have hr := mem_rootSet.mp p.2.property
    have hmem : p.2.val ∈ H.support := by
      obtain ⟨f,hf⟩ := hr
      obtain ⟨u,hu⟩ := hU p.1
      exact ⟨f u, hf ▸ f.toHom.map_rel' hu⟩
    exact ⟨⟨p.2.val, hmem⟩, ⟨p.1, mem_rootedChoices.mpr hr⟩⟩
  have hp : Function.Injective pc := by
    intro p q he
    have hi := congrArg (fun z : Σ v : H.support, selectors v => z.2.val) he
    have hv := congrArg (fun z : Σ v : H.support, selectors v => z.1.val) he
    rcases p with ⟨i, p⟩
    rcases q with ⟨j, q⟩
    change i = j at hi
    subst j
    congr 1
    exact Subtype.ext hv
  have hsum : (∑ i : Fin h, (rootSet H (U i)).card) ≤ 2 * edgeCount H * r := by
    calc
      (∑ i : Fin h, (rootSet H (U i)).card) = Fintype.card (Σ i : Fin h, rootSet H (U i)) := by
        simp [Fintype.card_sigma]
      _ ≤ Fintype.card (Σ v : H.support, selectors v) := Fintype.card_le_of_injective pc hp
      _ = ∑ v : H.support, (selectors v).card := by simp [Fintype.card_sigma]
      _ ≤ ∑ _v : H.support, r := Finset.sum_le_sum (fun v _ =>
        (hSparse η H v.val hH).le)
      _ = Fintype.card H.support * r := by simp [Nat.mul_comm]
      _ ≤ 2 * edgeCount H * r := by
        apply Nat.mul_le_mul_right
        simpa only [Set.toFinset_card] using card_support_le_twice_edgeCount H
  letI : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  simpa using exists_card_mul_le_of_sum_le (fun i => (rootSet H (U i)).card) _ hsum

private theorem high_degree_upper {V : Type*} [Fintype V] (H : SimpleGraph V) (d : ℕ) :
    d * (Finset.univ.filter (fun v => d < H.degree v)).card ≤ 2 * edgeCount H := by
  classical
  rw [edgeCount_eq_card_edgeFinset]
  calc
    _ = ∑ _v ∈ Finset.univ.filter (fun v => d < H.degree v), d := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v => d < H.degree v), H.degree v :=
      Finset.sum_le_sum (fun _ hv => (Finset.mem_filter.mp hv).2.le)
    _ ≤ ∑ v : V, H.degree v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem sizeOfSparseFamily (t : ℕ) (ht : 1 ≤ t) :
    let k := 100*t
    let h := 2^(1024*t*t)
    let w := 2^(k+1)-2
    let d := 2^(8*t)
    ∀ U : Fin h → SimpleGraph (Fin (w+1)),
      (∀ i, (U i).maxDegree ≤ 3 ∧ ∃ v, (U i).Adj 0 v) →
      SparseRoots U d (d^(k+2)) →
      (∀ i, ∃ f : Fin (2^(k-1)) ↪ Fin (w+1), ∃ g : Fin (2^(k-1)) ↪ Fin (w+1),
        Disjoint (Set.range f) (Set.range g) ∧ ∀ j, (U i).Adj (f j) (g j)) →
      h * (w+1) * 2^t ≤ sizeRamsey (disjointTarget U) (disjointTarget U) := by
  classical
  dsimp only
  intro U hcomp hSparse hmatch
  let k := 100*t
  let h := 2^(1024*t*t)
  let w := 2^(k+1)-2
  let d := 2^(8*t)
  let r := d^(k+2)
  let M := 2^(k-1)
  let L := h * (w+1) * 2^t
  let T := disjointTarget U
  let S : Set ℕ := {m | ∃ (η : ℕ) (H : SimpleGraph (Fin η)),
    H.edgeSet.ncard = m ∧ IsRamseyFor H T}
  have hS : S.Nonempty := by
    obtain ⟨η,H,hH⟩ := ramseyHost_exists T
    exact ⟨_,η,H,rfl,hH⟩
  obtain ⟨η,H,hcount,hRamsey⟩ := Nat.sInf_mem hS
  have hsize : edgeCount H = sInf S := by
    rw [edgeCount, Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard, hcount]
  change L ≤ sInf S
  by_contra! hL
  have hE : edgeCount H ≤ h * (w+1) * 2^t := by rw [hsize]; exact hL.le
  have hh : 0 < h := by positivity
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hwPos : 0 < (2 : ℕ)^(k+1) := by positivity
  have hw : w+1 ≤ 2^(k+1) := by dsimp [w]; omega
  have hroots : 4 * (w+1) * 2^t * r < h := by
    calc
      4 * (w+1) * 2^t * r ≤ 4 * 2^(k+1) * 2^t * r :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hw))
      _ = 2^(2+(k+1)+t+8*t*(k+2)) := by simp [r, d, pow_add, pow_mul]
      _ < h := by
        apply Nat.pow_lt_pow_right (by decide)
        dsimp [k]
        nlinarith
  have hM : 4 * (w+1) * 2^t < d*M := by
    calc
      4 * (w+1) * 2^t ≤ 4 * 2^(k+1) * 2^t :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hw)
      _ = 2^(2+(k+1)+t) := by simp [pow_add]
      _ < 2^(8*t+(k-1)) := by
        apply Nat.pow_lt_pow_right (by decide)
        omega
      _ = d*M := by simp [d, M, pow_add]
  let Q := lowHost H d
  obtain ⟨j,hj⟩ := rareRoot hh Q U (fun i => (hcomp i).2) hSparse (lowHost_degree H d)
  let A := rootSet Q (U j)
  have hQE : edgeCount Q ≤ edgeCount H := by
    rw [edgeCount_eq_card_edgeFinset, edgeCount_eq_card_edgeFinset]
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono (fun _ _ h => h.1))
  have h2A : 2*A.card < h := by
    have hhA : h*(2*A.card) < h*h := by
      calc
        h*(2*A.card) = 2*(h*A.card) := by ring
        _ ≤ 2*(2*edgeCount Q*r) := Nat.mul_le_mul_left _ hj
        _ ≤ 2*(2*edgeCount H*r) := by gcongr
        _ ≤ 2*(2*(h*(w+1)*2^t)*r) := by gcongr
        _ = h*(4*(w+1)*2^t*r) := by ring
        _ < h*h := Nat.mul_lt_mul_of_pos_left hroots hh
    exact Nat.lt_of_mul_lt_mul_left hhA
  let R := redHost H d A
  have hR : R ≤ H := fun _ _ e => e.1
  have hUsub : (U j).IsContained T := by
    refine ⟨⟨⟨fun x => (j,x), fun {_ _} e => ⟨rfl,e⟩⟩, ?_⟩⟩
    intro x y hxy
    exact congrArg Prod.snd hxy
  have hblue : ¬ T.IsContained (H \ R) := by
    intro hx
    exact blue_excludes_component H d (U j) (hcomp j).2 A
      (fun f => mem_rootSet.mpr ⟨f, rfl⟩) (hUsub.trans hx)
  have hred : ¬ T.IsContained R := by
    rintro ⟨red⟩
    let high := Finset.univ.filter (fun v => d < H.degree v)
    have hlow : (h-A.card)*M ≤ high.card := red_copy_high_count H d A U hmatch red
    have hhid : h*M ≤ 2*high.card := by
      calc
        h*M ≤ (2*(h-A.card))*M := Nat.mul_le_mul_right _ (by omega)
        _ = 2*((h-A.card)*M) := by ring
        _ ≤ 2*high.card := Nat.mul_le_mul_left _ hlow
    have hupper : d*(h*M) ≤ 4*edgeCount H := by
      calc
        d*(h*M) ≤ d*(2*high.card) := Nat.mul_le_mul_left _ hhid
        _ = 2*(d*high.card) := by ring
        _ ≤ 2*(2*edgeCount H) := Nat.mul_le_mul_left _ (high_degree_upper H d)
        _ = 4*edgeCount H := by ring
    have hstrict : 4*edgeCount H < d*(h*M) := by
      calc
        4*edgeCount H ≤ 4*(h*(w+1)*2^t) := Nat.mul_le_mul_left _ hE
        _ = h*(4*(w+1)*2^t) := by ring
        _ < h*(d*M) := Nat.mul_lt_mul_of_pos_left hM hh
        _ = d*(h*M) := by ring
    exact (not_lt_of_ge hupper) hstrict
  exact (hRamsey R hR).elim hred hblue

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem degree_disjointTarget {h w : ℕ}
    (U : Fin h → SimpleGraph (Fin (w+1))) (hU : ∀ i, (U i).maxDegree ≤ 3) :
    (disjointTarget U).maxDegree ≤ 3 := by
  classical
  apply (disjointTarget U).maxDegree_le_of_forall_degree_le 3
  intro x
  let code (y : (disjointTarget U).neighborSet x) : (U x.1).neighborSet x.2 :=
    ⟨y.val.2, y.property.2⟩
  have hc : Function.Injective code := by
    intro y z he
    apply Subtype.ext
    apply Prod.ext
    · exact y.property.1.symm.trans z.property.1
    · exact congrArg Subtype.val he
  have hcard := Fintype.card_le_of_injective code hc
  rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hcard
  exact hcard.trans (((U x.1).degree_le_maxDegree x.2).trans (hU x.1))

private theorem sizeRamsey_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    sizeRamsey G G = sizeRamsey H H := by
  unfold sizeRamsey
  apply congrArg sInf
  ext m
  constructor
  · rintro ⟨j, T, hm, hT⟩
    exact ⟨j, T, hm, fun R hR =>
      (hT R hR).imp (e.isContained'.trans) (e.isContained'.trans)⟩
  · rintro ⟨j, T, hm, hT⟩
    exact ⟨j, T, hm, fun R hR =>
      (hT R hR).imp (e.isContained.trans) (e.isContained.trans)⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem finite_family_bound :
    ∀ t : ℕ, 1 ≤ t → ∃ n : ℕ, t ≤ n ∧ n ≤ 2^(4096*t*t) ∧
      ∃ G : SimpleGraph (Fin n), G.maxDegree ≤ 3 ∧ n * 2^t ≤ sizeRamsey G G := by
  classical
  intro t ht
  let k := 100*t
  let h := 2^(1024*t*t)
  let w := 2^(k+1)-2
  let d := 2^(8*t)
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hd : 2 ≤ d :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 1 ≤ 8*t by omega)
  have hth : t ≤ t*t := by simpa using Nat.mul_le_mul_left t ht
  have hr : d^(k+2) ≤ h := by
    dsimp only [d,h]
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    dsimp [k]
    nlinarith only [hth]
  obtain ⟨U, hdeg, hS, hmatch⟩ := binaryFamily k h d hk hd hr (sampling_margin t ht)
  have hsize : h * (w+1) * 2^t ≤ sizeRamsey (disjointTarget U) (disjointTarget U) :=
    sizeOfSparseFamily t ht U hdeg hS hmatch
  let n := h*(w+1)
  have hncard : Fintype.card (Fin h × Fin (w+1)) = n := by simp [n]
  let G := (disjointTarget U).overFin hncard
  have hG : (disjointTarget U) ≃g G := (disjointTarget U).overFinIso hncard
  refine ⟨n, ?_, ?_, G, ?_, ?_⟩
  · have hle : t ≤ 1024*t*t := by nlinarith
    have hth : t ≤ h := (Nat.lt_two_pow_self (n := t)).le.trans (Nat.pow_le_pow_right (by decide) hle)
    exact hth.trans (Nat.le_mul_of_pos_right h (by omega))
  · have hpow : 0 < (2 : ℕ)^(k+1) := pow_pos (by decide) _
    have hw : w+1 ≤ 2^(k+1) := by dsimp [w]; omega
    calc
      n ≤ h * 2^(k+1) := Nat.mul_le_mul_left h hw
      _ = 2^(1024*t*t+(k+1)) := by simp only [h, pow_add]
      _ ≤ 2^(4096*t*t) := by
        apply Nat.pow_le_pow_right (by decide)
        dsimp [k]
        nlinarith
  · exact hG.isContained'.maxDegree_mono.trans
      (degree_disjointTarget U (fun i => (hdeg i).1))
  · rw [← sizeRamsey_iso hG]
    exact hsize

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
private theorem analytic_bound (n t : ℕ) (hpos : 0 < n)
    (hn : n ≤ 2^(4096*t*t)) :
    exp (log 2 / 64 * √(log (n : ℝ))) ≤ (2 : ℝ)^t := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hpos
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
  have hn' : (n : ℝ) ≤ (2 : ℝ) ^ (4096*t*t) := by exact_mod_cast hn
  have hlog : log (n : ℝ) ≤ 4096 * (t : ℝ)^2 := by
    have hl := Real.log_le_log hnpos hn'
    rw [Real.log_pow] at hl
    push_cast at hl
    have hlogtwo : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    calc
      log (n : ℝ) ≤ 4096 * (t : ℝ) * t * log 2 := hl
      _ ≤ 4096 * (t : ℝ) * t * 1 :=
        mul_le_mul_of_nonneg_left hlogtwo (mul_nonneg (mul_nonneg (by norm_num) ht) ht)
      _ = 4096 * (t : ℝ)^2 := by ring
  have hroot : √(log (n : ℝ)) ≤ 64 * (t : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (by norm_num) ht, ?_⟩
    calc
      log (n : ℝ) ≤ 4096 * (t : ℝ)^2 := hlog
      _ = (64 * (t : ℝ))^2 := by ring
  have h := mul_le_mul_of_nonneg_left hroot (show 0 ≤ log 2 / 64 by positivity)
  have h' : log 2 / 64 * √(log (n : ℝ)) ≤ (t : ℝ) * log 2 := by linarith
  apply (Real.exp_le_exp.mpr h').trans_eq
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : 0 < (2 : ℝ))]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem result : type_of% @Erdos559.erdos_559.variants.tikhomirov := by
  classical
  refine ⟨log 2 / 64, by positivity, 1, by norm_num, ?_⟩
  apply frequently_atTop.mpr
  intro N
  let t := N + 1
  obtain ⟨n, htn, hn, G, hdeg, hsize⟩ := finite_family_bound t (by omega)
  have he := analytic_bound n t (by omega) hn
  refine ⟨n, by omega, G, hdeg, ?_⟩
  have hsize' : (n : ℝ) * (2 : ℝ)^t ≤ sizeRamsey G G := by exact_mod_cast hsize
  simpa only [one_mul] using (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg n)).trans hsize'

end OMA.Tikhomirov

theorem OMA.solution : type_of% @Erdos559.erdos_559.variants.tikhomirov :=
  OMA.Tikhomirov.result
