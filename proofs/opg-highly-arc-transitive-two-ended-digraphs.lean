import OMAStatements.S_opg_highly_arc_transitive_two_ended_digraphs

-- Problem: Highly arc transitive two ended digraphs
-- Credit: @sobrien032

/-!
This is the two-ended counterexample from Construction 2 of
Highly arc-transitive digraphs – structure and counterexamples, by Matt DeVos,
Bojan Mohar and Robert Šámal (arXiv 1110.2945). The template is the directed
complete bipartite graph with three vertices per side and a matching removed.
Peter Cameron, Cheryl Praeger and Nicholas Wormald posed the conjecture.
David Ganz formalized the board statement. Lean proof by Codex.

Each integer layer carries two colors. An arc advances by one layer and
requires the first color of its source to differ from the second color of its
target. Independent color permutations at the integer layers act transitively
on arcs of each length. Removing a finite slab leaves connected positive and
negative tails, which determine exactly two ends.
-/

namespace TileExample

abbrev V := ℤ × Fin 3 × Fin 3

def D : Digraph V := ⟨fun u w ↦ w.1 = u.1 + 1 ∧ u.2.1 ≠ w.2.2⟩

abbrev G := OMA.S_opg_highly_arc_transitive_two_ended_digraphs.underlying D

theorem adj_of_arc {u w : V} (ha : D.Adj u w) : G.Adj u w := by
  refine ⟨?_, Or.inl ha⟩
  rintro rfl
  have := ha.1
  omega

theorem height_finite (i : ℤ) : {v : V | v.1 = i}.Finite := by
  let layer := ({i} : Finset ℤ) ×ˢ (Finset.univ : Finset (Fin 3 × Fin 3))
  apply layer.finite_toSet.subset
  intro x hx
  exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hx, Finset.mem_univ _⟩

theorem neighbors_finite (v : V) : {w | D.Adj v w ∨ D.Adj w v}.Finite := by
  apply ((height_finite (v.1 + 1)).union (height_finite (v.1 - 1))).subset
  intro w hw
  rcases hw with h | h
  · exact Or.inl h.1
  · right
    change w.1 = v.1 - 1
    have := h.1
    omega

end TileExample

namespace TileExample

noncomputable def slab (R : ℕ) : Finset V :=
  Finset.Icc (-(R : ℤ)) (R : ℤ) ×ˢ (Finset.univ : Finset (Fin 3 × Fin 3))

theorem mem_slab {v : V} {R : ℕ} : v ∈ slab R ↔ -(R : ℤ) ≤ v.1 ∧ v.1 ≤ R := by
  simp [slab]

theorem exists_slab (K : Finset V) : ∃ R : ℕ, K ⊆ slab R := by
  let R := K.sup (fun v ↦ v.1.natAbs)
  refine ⟨R, ?_⟩
  intro v hv
  have h : v.1.natAbs ≤ R := Finset.le_sup (f := fun v : V ↦ v.1.natAbs) hv
  have hz : (v.1.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at hz
  exact mem_slab.mpr (abs_le.mp hz)

theorem opposite_ne (K : Finset V) (hzero : ∀ z : V, z.1 = 0 → z ∈ K) {v w : V}
    (hv : 0 < v.1) (hw : w.1 < 0) (hvn : v ∉ K) (hwn : w ∉ K) :
    G.componentComplMk (K := (K : Set V)) hvn ≠ G.componentComplMk hwn := by
  let side : G.ComponentCompl (K : Set V) → Bool := SimpleGraph.ComponentCompl.lift
    (fun {z} _ ↦ decide (0 < z.1)) (by
      intro a b hna hnb hab
      have hza : a.1 ≠ 0 := fun he ↦ hna (hzero a he)
      have hzb : b.1 ≠ 0 := fun he ↦ hnb (hzero b he)
      have hheight : b.1 = a.1 + 1 ∨ a.1 = b.1 + 1 := hab.2.imp And.left And.left
      by_cases h : 0 < a.1
      · simp [h, show 0 < b.1 by omega]
      · simp [h, show ¬ 0 < b.1 by omega])
  intro he
  have h := congrArg side he
  change decide (0 < v.1) = decide (0 < w.1) at h
  simp [hv, show ¬ 0 < w.1 by omega] at h

end TileExample

namespace TileExample

private def rail (i : ℤ) : V := (i,0,1)

private theorem third_colour (a b : Fin 3) : ∃ c : Fin 3, a ≠ c ∧ b ≠ c := by
  revert a b
  decide

private theorem rail_chain (K : Finset V) (i j : ℤ) (hij : i ≤ j)
    (hs : ∀ t, i ≤ t → t ≤ j → rail t ∉ K) :
    G.componentComplMk (K := (K : Set V)) (hs i le_rfl hij) =
      G.componentComplMk (K := (K : Set V)) (hs j hij le_rfl) := by
  induction j, hij using Int.leInduction with
  | base => rfl
  | succ j hj ih =>
    have hs' : ∀ t, i ≤ t → t ≤ j → rail t ∉ K :=
      fun t ht ht' => hs t ht (by omega)
    have hj' := hs j hj (by omega)
    exact (ih hs').trans (G.componentComplMk_eq_of_adj (K := (K : Set V))
      hj' (hs (j+1) (by omega) le_rfl) (adj_of_arc ⟨rfl, by change (0 : Fin 3) ≠ 1; decide⟩))

private theorem high_anchor (K : Finset V) (r : ℤ) (hK : ∀ v ∈ K, v.1 ≤ r) (v : V)
    (hv : r < v.1) (hvn : v ∉ K) (hn : rail (r+1) ∉ K) :
    G.componentComplMk (K := (K : Set V)) hvn = G.componentComplMk (K := (K : Set V)) hn := by
  have safe (w : V) (hw : r < w.1) : w ∉ K := fun h => (not_le.mpr hw) (hK w h)
  obtain ⟨c, hvc, hrc⟩ := third_colour v.2.1 0
  let z : V := (v.1+1,0,c)
  have hz : z ∉ K := safe z (by change r < v.1+1; omega)
  have hrv : rail v.1 ∉ K := safe _ hv
  have ha : D.Adj v z := ⟨rfl,hvc⟩
  have hb : D.Adj (rail v.1) z := ⟨rfl,hrc⟩
  have ea := G.componentComplMk_eq_of_adj (K := (K : Set V)) hvn hz (adj_of_arc ha)
  have eb := G.componentComplMk_eq_of_adj (K := (K : Set V)) hrv hz (adj_of_arc hb)
  have er := rail_chain K (r+1) v.1 (by omega)
    (fun t ht _ => safe _ (show r < t by omega))
  exact (ea.trans eb.symm).trans er.symm

private theorem low_anchor (K : Finset V) (r : ℤ) (hK : ∀ v ∈ K, r ≤ v.1) (v : V)
    (hv : v.1 < r) (hvn : v ∉ K) (hn : rail (r-1) ∉ K) :
    G.componentComplMk (K := (K : Set V)) hvn = G.componentComplMk (K := (K : Set V)) hn := by
  have safe (w : V) (hw : w.1 < r) : w ∉ K := fun h => (not_le.mpr hw) (hK w h)
  obtain ⟨c, hvc, hrc⟩ := third_colour v.2.2 1
  let z : V := (v.1-1,c,0)
  have hz : z ∉ K := safe z (by change v.1-1 < r; omega)
  have hrv : rail v.1 ∉ K := safe _ hv
  have ha : D.Adj z v := ⟨by change v.1 = v.1-1+1; omega,hvc.symm⟩
  have hb : D.Adj z (rail v.1) := ⟨by change v.1 = v.1-1+1; omega,hrc.symm⟩
  have ea := G.componentComplMk_eq_of_adj (K := (K : Set V)) hz hvn (adj_of_arc ha)
  have eb := G.componentComplMk_eq_of_adj (K := (K : Set V)) hz hrv (adj_of_arc hb)
  have er := rail_chain K v.1 (r-1) (by omega)
    (fun t _ ht => safe _ (show t < r by omega))
  exact (ea.symm.trans eb).trans er

theorem high_eq (K : Finset V) (r : ℤ) (hK : ∀ v ∈ K, v.1 ≤ r) {v w : V}
    (hv : r < v.1) (hw : r < w.1) (hvn : v ∉ K) (hwn : w ∉ K) :
    G.componentComplMk (K := (K : Set V)) hvn = G.componentComplMk (K := (K : Set V)) hwn := by
  have h : rail (r+1) ∉ K := by
    intro hm
    have hh := hK _ hm
    change r+1 ≤ r at hh
    omega
  exact (high_anchor K r hK v hv hvn h).trans (high_anchor K r hK w hw hwn h).symm

theorem low_eq (K : Finset V) (r : ℤ) (hK : ∀ v ∈ K, r ≤ v.1) {v w : V}
    (hv : v.1 < r) (hw : w.1 < r) (hvn : v ∉ K) (hwn : w ∉ K) :
    G.componentComplMk (K := (K : Set V)) hvn = G.componentComplMk (K := (K : Set V)) hwn := by
  have h : rail (r-1) ∉ K := by
    intro hm
    have hh := hK _ hm
    change r ≤ r-1 at hh
    omega
  exact (low_anchor K r hK v hv hvn h).trans (low_anchor K r hK w hw hwn h).symm

theorem graph_connected : G.Connected := by
  refine ⟨?_⟩
  intro v w
  have heq := high_eq ∅ (min v.1 w.1 - 1) (by simp) (v := v) (w := w)
    (by omega) (by omega) (by simp) (by simp)
  have hpath := SimpleGraph.ConnectedComponent.eq.mp heq
  exact hpath.map (SimpleGraph.Embedding.induce (G := G) _).toHom

end TileExample

namespace TileExample

open OMA.S_opg_highly_arc_transitive_two_ended_digraphs

private theorem perm_two {a b c d : Fin 3} (h : a ≠ b) (k : c ≠ d) :
    ∃ σ : Equiv.Perm (Fin 3), σ a = c ∧ σ b = d := by
  let τ := Equiv.swap a c
  have hc : τ a = c := Equiv.swap_apply_left _ _
  have hn : c ≠ τ b := hc ▸ τ.injective.ne h
  refine ⟨τ.trans (Equiv.swap (τ b) d), ?_, ?_⟩
  · change Equiv.swap (τ b) d (τ a) = c
    rw [hc, Equiv.swap_apply_of_ne_of_ne hn k]
  · exact Equiv.swap_apply_left _ _

private theorem arc_height {s : ℕ} (v : Fin (s+1) → V) (hv : IsArc D s v)
    (i : Fin (s+1)) : (v i).1 = (v 0).1 + (i.val : ℤ) := by
  induction i using Fin.induction with
  | zero => simp
  | succ i h =>
    have he := (hv i).1
    simpa only [Fin.val_succ, Nat.cast_succ, ← add_assoc, Fin.val_castSucc] using
      he.trans (congrArg (fun z : ℤ ↦ z + 1) h)

private theorem layer_permutation {s : ℕ} (v w : Fin (s+1) → V)
    (hv : IsArc D s v) (hw : IsArc D s w) (t : ℤ) :
    ∃ σ : Equiv.Perm (Fin 3),
      (∀ i, (v i).1 = t → σ (v i).2.1 = (w i).2.1) ∧
      (∀ i, (v i).1 = t+1 → σ (v i).2.2 = (w i).2.2) := by
  have inj : Function.Injective (fun i ↦ (v i).1) := by
    intro i j h
    have hi := arc_height v hv i
    have hj := arc_height v hv j
    apply Fin.ext
    change (v i).1 = (v j).1 at h
    omega
  by_cases hA : ∃ i, (v i).1 = t
  · obtain ⟨i, hi⟩ := hA
    by_cases hB : ∃ j, (v j).1 = t+1
    · obtain ⟨j, hj⟩ := hB
      have hij : j.val = i.val+1 := by
        have ha := arc_height v hv i
        have hb := arc_height v hv j
        omega
      let k : Fin s := ⟨i.val, by have := j.isLt; omega⟩
      have hki : k.castSucc = i := Fin.ext rfl
      have hkj : k.succ = j := Fin.ext hij.symm
      have hn := (hv k).2
      have hn' := (hw k).2
      rw [hki, hkj] at hn hn'
      obtain ⟨σ, ha, hb⟩ := perm_two hn hn'
      refine ⟨σ, ?_, ?_⟩
      · intro x hx
        rw [inj (hx.trans hi.symm)]
        exact ha
      · intro x hx
        rw [inj (hx.trans hj.symm)]
        exact hb
    · refine ⟨Equiv.swap (v i).2.1 (w i).2.1, ?_, ?_⟩
      · intro x hx
        rw [inj (hx.trans hi.symm), Equiv.swap_apply_left]
      · exact fun x hx ↦ (hB ⟨x, hx⟩).elim
  · by_cases hB : ∃ j, (v j).1 = t+1
    · obtain ⟨j, hj⟩ := hB
      refine ⟨Equiv.swap (v j).2.2 (w j).2.2, fun x hx ↦ (hA ⟨x,hx⟩).elim, ?_⟩
      intro x hx
      rw [inj (hx.trans hj.symm), Equiv.swap_apply_left]
    · exact ⟨Equiv.refl _, fun x hx ↦ (hA ⟨x,hx⟩).elim, fun x hx ↦ (hB ⟨x,hx⟩).elim⟩

private def relabel (d : ℤ) (σ : ℤ → Equiv.Perm (Fin 3)) : V ≃ V where
  toFun x := (x.1+d, σ x.1 x.2.1, σ (x.1-1) x.2.2)
  invFun y := (y.1-d, (σ (y.1-d)).symm y.2.1, (σ (y.1-d-1)).symm y.2.2)
  left_inv := by rintro ⟨h,a,b⟩; simp
  right_inv := by rintro ⟨h,a,b⟩; simp

private theorem relabel_isAut (d : ℤ) (σ : ℤ → Equiv.Perm (Fin 3)) :
    IsAut D (relabel d σ) := by
  rintro ⟨i,a,b⟩ ⟨j,c,e⟩
  change (j = i+1 ∧ a ≠ e) ↔ (j+d = i+d+1 ∧ σ i a ≠ σ (j-1) e)
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨by omega, by simpa using (σ i).injective.ne h⟩
  · rintro ⟨hh, h⟩
    refine ⟨by omega, ?_⟩
    rw [show j-1=i by omega] at h
    exact fun he ↦ h (congrArg (σ i) he)

theorem highly : HighlyArcTransitive D := by
  intro s v w hv hw
  choose σ ha hb using layer_permutation v w hv hw
  let d : ℤ := (w 0).1 - (v 0).1
  refine ⟨relabel d σ, relabel_isAut d σ, ?_⟩
  intro i
  apply Prod.ext
  · change (v i).1 + ((w 0).1 - (v 0).1) = (w i).1
    have h := arc_height v hv i
    have k := arc_height w hw i
    omega
  · apply Prod.ext
    · exact ha _ i rfl
    · exact hb _ i (by omega)

end TileExample

namespace TileExample

open CategoryTheory Opposite

private noncomputable def cutBound (K : Finset V) : ℕ := (exists_slab K).choose

private theorem inCut (K : Finset V) : K ⊆ slab (cutBound K) :=
  (exists_slab K).choose_spec

private def far (b : Bool) (R : ℕ) (x : V) : Prop :=
  if b then (R : ℤ) < x.1 else x.1 < -(R : ℤ)

private def tip (b : Bool) (R : ℕ) : V :=
  (if b then (R : ℤ) + 1 else -((R : ℤ) + 1), 0, 0)

private theorem tip_far (b : Bool) {R N : ℕ} (h : R ≤ N) : far b R (tip b N) := by
  cases b <;> simp [far, tip] <;> omega

private theorem far_out {b : Bool} {K : Finset V} {R : ℕ} {x : V}
    (H : K ⊆ slab R) (hx : far b R x) : x ∉ (K : Set V) := by
  intro hxK
  have Hx := mem_slab.mp (H hxK)
  cases b <;> simp [far] at hx <;> omega

private theorem far_same (b : Bool) {K : Finset V} {R : ℕ} (H : K ⊆ slab R)
    {x y : V} (hx : far b R x) (hy : far b R y) :
    G.componentComplMk (far_out H hx) = G.componentComplMk (far_out H hy) := by
  cases b
  · exact low_eq K (-(R : ℤ)) (fun z hz => (mem_slab.mp (H hz)).1) hx hy _ _
  · exact high_eq K (R : ℤ) (fun z hz => (mem_slab.mp (H hz)).2) hx hy _ _

private noncomputable def side (b : Bool) (K : Finset V) : G.ComponentCompl (K : Set V) :=
  G.componentComplMk (far_out (inCut K) (tip_far b (le_refl (cutBound K))))

private theorem mk_eq_side {b : Bool} {K : Finset V} {R : ℕ} (H : K ⊆ slab R)
    {x : V} (hx : far b R x) : G.componentComplMk (far_out H hx) = side b K := by
  let N := max R (cutBound K)
  have h₁ : R ≤ N := le_max_left _ _
  have h₂ : cutBound K ≤ N := le_max_right _ _
  exact (far_same b H hx (tip_far b h₁)).trans
    (far_same b (inCut K) (tip_far b h₂) (tip_far b (le_refl _)))

private noncomputable def sideEnd (b : Bool) : G.end := by
  refine ⟨fun K => side b K.unop, ?_⟩
  intro L K f
  have H : K.unop ⊆ L.unop := le_of_op_hom f
  change (side b L.unop).hom H = side b K.unop
  unfold side
  rw [SimpleGraph.ComponentCompl.hom_mk _ (show (K.unop : Set V) ⊆ (L.unop : Set V) from H)]
  exact mk_eq_side (H.trans (inCut L.unop)) (tip_far b (le_refl _))

private theorem restrict_eq {e e' : G.end} {K L : Finset V} (H : K ⊆ L)
    (hh : e.val (op L) = e'.val (op L)) : e.val (op K) = e'.val (op K) := by
  let f : op L ⟶ op K := opHomOfLE H
  exact (e.property f).symm.trans ((congrArg (G.componentComplFunctor.map f) hh).trans
    (e'.property f))

private theorem at_full_slab (e : G.end) (R : ℕ) :
    ∃ b, e.val (op (slab R)) = (sideEnd b).val (op (slab R)) := by
  let C : G.ComponentCompl (slab R : Set V) := e.val (op (slab R))
  obtain ⟨x,hx,he⟩ := C.exists_eq_mk
  by_cases h : x.1 < -(R : ℤ)
  · exact ⟨false, he.symm.trans (mk_eq_side (subset_refl (slab R)) (show far false R x from h))⟩
  · have h' : (R : ℤ) < x.1 := by
      by_contra! hh
      exact hx (mem_slab.mpr ⟨le_of_not_gt h,hh⟩)
    exact ⟨true, he.symm.trans (mk_eq_side (subset_refl (slab R)) (show far true R x from h'))⟩

private theorem ends_separate :
    (sideEnd true).val (op (slab 0)) ≠ (sideEnd false).val (op (slab 0)) := by
  let K := slab 0
  have hk : ∀ v : V, v.1 = 0 → v ∈ K := fun v hv => mem_slab.mpr (by simp [hv])
  have hp : 0 < (tip true (cutBound K)).1 := by simp [tip]
  have hm : (tip false (cutBound K)).1 < 0 := by simp [tip]; omega
  exact opposite_ne K hk hp hm _ _

private theorem side_injective_zero :
    Function.Injective (fun b => (sideEnd b).val (op (slab 0))) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact (ends_separate h.symm).elim
  · exact (ends_separate h).elim
  · rfl

private theorem all_ends (e : G.end) : ∃ b, sideEnd b = e := by
  obtain ⟨b,hb⟩ := at_full_slab e 0
  refine ⟨b, Subtype.ext (funext (fun K => ?_))⟩
  obtain ⟨R,hR⟩ := exists_slab K.unop
  have hz : slab 0 ⊆ slab R := by
    intro v hv
    have hv₀ := mem_slab.mp hv
    exact mem_slab.mpr (by simp at hv₀; omega)
  obtain ⟨c,hc⟩ := at_full_slab e R
  have he : b = c := side_injective_zero (hb.symm.trans (restrict_eq hz hc))
  subst c
  exact (restrict_eq hR hc).symm

theorem endCard : Nat.card G.end = 2 := by
  classical
  have hinj : Function.Injective sideEnd := fun a b h =>
    side_injective_zero (congrArg (fun e : G.end => e.val (op (slab 0))) h)
  have hsur : Function.Surjective sideEnd := all_ends
  simpa [Nat.card_eq_fintype_card] using
    (Nat.card_congr (Equiv.ofBijective sideEnd ⟨hinj, hsur⟩).symm)

end TileExample

open TileExample in
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_highly_arc_transitive_two_ended_digraphs.main) := by
  intro h
  have rect := h V D graph_connected neighbors_finite highly endCard
    Prod.fst height_finite (fun _ _ h ↦ h.1)
    ((0,0,0) : V) ((0,1,0) : V) ((1,0,2) : V) ((1,0,1) : V)
    (by change (1 : ℤ) = 0 + 1 ∧ (0 : Fin 3) ≠ 2; decide)
    (by change (1 : ℤ) = 0 + 1 ∧ (1 : Fin 3) ≠ 2; decide)
    (by change (1 : ℤ) = 0 + 1 ∧ (0 : Fin 3) ≠ 1; decide)
  exact rect.2 rfl
