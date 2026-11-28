import OMAReductions.R_Erdos570_erdos_570_R1
import Mathlib

/-!
# Red neighborhood bounds for the connected cycle Ramsey problem

Following Cambie, Freschi, Morawski, Petrova and Pokrovskiy (arXiv:2601.10238,
Lemma 6, Corollary 7 and Claims 12–13), a red neighborhood large enough for
the path Ramsey estimate gives a blue copy of the entire target. A depth-first
search proves the path estimate directly for every finite graph.
-/

open SimpleGraph

namespace OMA.R_Erdos570_erdos_570_R1_H1_R2

/-- Lemma 8 of Cambie et al. A path on 2k vertices in the second red
neighborhood of a vertex forces a red k - cycle, for k at least five. -/
def H1 : Prop := ∀ (k : ℕ), 5 ≤ k → ∀ (V : Type) [Fintype V] (R : SimpleGraph V) (v : V),
  pathGraph (2 * k) ⊑ R.induce {x | x ≠ v ∧ ¬ R.Adj v x ∧ ∃ y, R.Adj v y ∧ R.Adj y x} →
  cycleGraph k ⊑ R

/-- The remaining connected-target extremal problem, restricted to hosts
where every first red neighborhood and (for k ≥ 5) every second red
neighborhood obeys its explicit upper bound. -/
def H2 : Prop := ∀ k : ℕ, 3 ≤ k → ∃ B : ℕ, ∀ (W V : Type) [Fintype W] [Fintype V]
  (H : SimpleGraph W) (R : SimpleGraph V), H.Connected → B ≤ Fintype.card V →
  2 * H.edgeSet.ncard + (k - 1) / 2 ≤ Fintype.card V → ¬ cycleGraph k ⊑ R →
  (∀ v, (R.neighborSet v).ncard < Fintype.card W + (k - 3) * Nat.sqrt (2 * H.edgeSet.ncard)) →
  (5 ≤ k → ∀ v, ({x | x ≠ v ∧ ¬ R.Adj v x ∧ ∃ y, R.Adj v y ∧ R.Adj y x} : Set V).ncard <
    Fintype.card W + (2 * k - 2) * Nat.sqrt (2 * H.edgeSet.ncard)) → H ⊑ Rᶜ


/-- The initial segment of a simple chain embeds the path graph. -/
lemma copy_of_chain {V : Type*} {G : SimpleGraph V} {p : List V}
    (nd : p.Nodup) (chain : p.IsChain G.Adj) {k : ℕ} (hk : k ≤ p.length) :
    pathGraph k ⊑ G := by
  let f (i : Fin k) := p.get (Fin.castLE hk i)
  have inj : Function.Injective f := by
    intro i j h
    have h' := nd.get_inj_iff.mp h
    exact Fin.ext (congrArg (fun a : Fin p.length => a.val) h')
  refine ⟨⟨⟨f, ?_⟩, inj⟩⟩
  intro i j hij
  have step (a b : Fin k) (hab : a.val + 1 = b.val) : G.Adj (f a) (f b) := by
    have h := (List.isChain_iff_getElem.mp chain) a.val (by omega : a.val + 1 < p.length)
    simpa [f, List.get_eq_getElem, hab] using h
  rcases pathGraph_adj.mp hij with h | h
  · exact step i j h
  · exact (step j i h).symm

/-- A path-free red graph contains an anticomplete pair with a prescribed first size.
At the last pop the depth-first search leaves at most k−2 vertices on its stack. -/
theorem separator {V : Type*} [Fintype V] (G : SimpleGraph V) {k : ℕ}
    (free : ¬ pathGraph k ⊑ G) (a : ℕ) (room : a ≤ Fintype.card V) :
    ∃ s u : Finset V, s.card = a ∧ Fintype.card V ≤ a + u.card + (k - 2) ∧
      Disjoint s u ∧ ∀ x ∈ s, ∀ y ∈ u, ¬ G.Adj x y := by
  classical
  let rec search (p : List V) (s u : Finset V)
      (nd : p.Nodup) (chain : p.IsChain G.Adj)
      (balance : s.card + u.card + p.length = Fintype.card V)
      (small : s.card ≤ a) (atGoal : s.card = a → p.length ≤ k - 2) (su : Disjoint s u)
      (apart : ∀ z ∈ p, z ∉ s ∧ z ∉ u)
      (cut : ∀ x ∈ s, ∀ y ∈ u, ¬ G.Adj x y) :
      ∃ s' u' : Finset V, s'.card = a ∧ Fintype.card V ≤ a + u'.card + (k - 2) ∧
        Disjoint s' u' ∧ ∀ x ∈ s', ∀ y ∈ u', ¬ G.Adj x y := by
    by_cases done : s.card = a
    · have short := atGoal done
      exact ⟨s, u, done, by omega, su, cut⟩
    have push (z : V) (hz : z ∈ u) (linked : (z :: p).IsChain G.Adj) := by
      have notmem : z ∉ p := fun hm => (apart z hm).2 hz
      have pos := Finset.card_pos.mpr ⟨z, hz⟩
      have cardU := Finset.card_erase_of_mem hz
      exact search (z :: p) s (u.erase z) (List.nodup_cons.mpr ⟨notmem, nd⟩) linked
        (by simp only [List.length_cons]; omega) small (fun eq => (done eq).elim) (su.mono_right (Finset.erase_subset _ _))
        (by
          intro w hw
          rcases List.mem_cons.mp hw with rfl | h
          · exact ⟨fun hs => Finset.disjoint_left.mp su hs hz, Finset.notMem_erase _ _⟩
          · exact ⟨(apart w h).1, fun hwu => (apart w h).2 (Finset.mem_of_mem_erase hwu)⟩)
        (fun x hx y hy => cut x hx y (Finset.mem_of_mem_erase hy))
    cases p with
    | nil =>
      have hU : u.Nonempty := Finset.card_pos.mp (by simp at balance; omega)
      obtain ⟨z, hz⟩ := hU
      exact push z hz (by simp)
    | cons v tail =>
      by_cases neighbor : ∃ z ∈ u, G.Adj z v
      · obtain ⟨z, hz, h⟩ := neighbor
        exact push z hz (List.isChain_cons_cons.mpr ⟨h, chain⟩)
      · have hv := apart v (by simp)
        have cs := Finset.card_insert_of_notMem hv.1
        have nodup := List.nodup_cons.mp nd
        have short : (v :: tail).length < k := lt_of_not_ge (fun h => free (copy_of_chain nd chain h))
        exact search tail (insert v s) u nodup.2 chain.tail
          (by simp only [List.length_cons] at balance; omega) (by omega)
          (fun _ => by simp only [List.length_cons] at short; omega)
          (Finset.disjoint_left.mpr (by
            intro x hx hu
            rcases Finset.mem_insert.mp hx with rfl | hs
            · exact hv.2 hu
            · exact Finset.disjoint_left.mp su hs hu))
          (by
            intro w hw
            have h := apart w (List.mem_cons_of_mem _ hw)
            exact ⟨fun hin => (Finset.mem_insert.mp hin).elim (fun he => nodup.1 (he ▸ hw)) h.1, h.2⟩)
          (by
            intro x hx y hy h
            rcases Finset.mem_insert.mp hx with rfl | hs
            · exact neighbor ⟨y, hy, h.symm⟩
            · exact cut x hs y hy h)
    termination_by 2 * u.card + p.length
    decreasing_by
      all_goals simp_all only [List.length_cons]
      all_goals omega
  exact search [] ∅ Finset.univ (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp)

/-- Embed a target with t + 1 colors in the blue graph when the red graph
has no k - vertex path. Each division between consecutive color classes costs
at most k−2 vertices. -/
theorem colored_copy (k t : ℕ) {W V : Type} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V) (c : H.Coloring (Fin (t + 1)))
    (room : Fintype.card W + (k - 2) * t ≤ Fintype.card V) (free : ¬ pathGraph k ⊑ G) :
    H ⊑ Gᶜ := by
  classical
  induction t generalizing W V with
  | zero =>
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (by simpa using room : Fintype.card W ≤ Fintype.card V)
    exact ⟨⟨⟨f, fun h => False.elim (c.valid h (Fin.ext (by omega)))⟩, f.injective⟩⟩
  | succ t ih =>
    let A : Set W := {w | c w = 0}
    have cardA : Fintype.card A ≤ Fintype.card W := Fintype.card_subtype_le _
    obtain ⟨s,u,hs,hu,dis,cut⟩ := separator G free (Fintype.card A) (by omega)
    obtain ⟨left⟩ : Nonempty (A ↪ ↥s) := Function.Embedding.nonempty_of_card_le (by simpa using hs.ge)
    let c' : (H.induce Aᶜ).Coloring (Fin (t + 1)) := Coloring.mk (fun w => (c w.val).pred w.property) (by
      intro i j e eq
      have h := congrArg Fin.succ eq
      simp only [Fin.succ_pred] at h
      exact c.valid e h)
    have remcard := Fintype.card_compl_set A
    have remain : Fintype.card ↥(Aᶜ) + (k - 2) * t ≤ Fintype.card ↥u := by
      simp only [Fintype.card_coe]; rw [Nat.mul_succ] at room; omega
    obtain ⟨right⟩ := ih (H.induce Aᶜ) (G.induce (u : Set V)) c' remain
      (fun h => free (h.trans (Embedding.induce _).isContained))
    let f (w : W) : V := if h : w ∈ A then (left ⟨w,h⟩).val else (right ⟨w,h⟩).val
    have fleft (w : W) (h : w ∈ A) : f w = (left ⟨w,h⟩).val := dif_pos h
    have fright (w : W) (h : w ∉ A) : f w = (right ⟨w,h⟩).val := dif_neg h
    have neCross {x y : W} (hx : x ∈ A) (hy : y ∉ A) : f x ≠ f y := by
      rw [fleft _ hx, fright _ hy]
      intro eq
      exact Finset.disjoint_left.mp dis (left ⟨x,hx⟩).property (eq ▸ (right ⟨y,hy⟩).property)
    have blue {x y : W} (hx : x ∈ A) (hy : y ∉ A) : Gᶜ.Adj (f x) (f y) := by
      refine ⟨neCross hx hy, ?_⟩
      rw [fleft _ hx, fright _ hy]
      exact cut _ (left ⟨x,hx⟩).property _ (right ⟨y,hy⟩).property
    refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
    · intro x y h
      by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
      · exact False.elim (c.valid h (hx.trans (Eq.symm hy)))
      · exact blue hx hy
      · exact (blue hy hx).symm
      · have edge := right.toHom.map_adj (show (H.induce Aᶜ).Adj ⟨x,hx⟩ ⟨y,hy⟩ from h)
        exact ⟨fun e => edge.1 (Subtype.ext ((fright _ hx).symm.trans (e.trans (fright _ hy)))),
          fun e => edge.2 (show G.Adj (right ⟨x,hx⟩).val (right ⟨y,hy⟩).val from (fright _ hx) ▸ (fright _ hy) ▸ e)⟩
    · intro x y h
      change f x = f y at h
      by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
      · rw [fleft _ hx, fleft _ hy] at h
        exact congrArg Subtype.val (left.injective (Subtype.ext h))
      · exact False.elim (neCross hx hy h)
      · exact False.elim (neCross hy hx h.symm)
      · rw [fright _ hx, fright _ hy] at h
        exact congrArg Subtype.val (right.injective (Subtype.ext h))


/-- Recoloring one optimal color class into another shows that each ordered
pair of distinct colors occurs on a dart. Counting darts bounds the number
of colors in terms of the edge count. -/
lemma few_colors {W : Type} [Fintype W] (H : SimpleGraph W) :
    H.Colorable (Nat.sqrt (2 * H.edgeSet.ncard) + 1) := by
  classical
  let n := H.chromaticNumber.toNat
  obtain ⟨c⟩ : H.Colorable n := H.colorable_chromaticNumber_of_fintype
  have onto : ∀ d : H.Coloring (Fin n), Function.Surjective d :=
    le_chromaticNumber_iff_forall_surjective.mp (ENat.natCast_toNat_le_self _)
  have witness (i j : Fin n) (ne : i ≠ j) : ∃ x y, H.Adj x y ∧ c x = i ∧ c y = j := by
    by_contra! missing
    let merge (a : Fin n) := if a = i then j else a
    let d : H.Coloring (Fin n) := Coloring.mk (fun x => merge (c x)) (by
      intro x y h
      by_cases hx : c x = i <;> by_cases hy : c y = i
      · exact False.elim (c.valid h (hx.trans hy.symm))
      · simpa only [merge, if_pos hx, if_neg hy] using Ne.symm (missing x y h hx)
      · simpa only [merge, if_neg hx, if_pos hy] using missing y x h.symm hy
      · simpa only [merge, if_neg hx, if_neg hy] using c.valid h)
    obtain ⟨x,hx⟩ := onto d i
    change merge (c x) = i at hx
    by_cases h : c x = i <;> simp [merge, h, ne.symm] at hx
  have surj : Function.Surjective c.mapDart := by
    intro d
    obtain ⟨x,y,h,hx,hy⟩ := witness d.fst d.snd d.fst_ne_snd
    exact ⟨⟨(x,y),h⟩, Dart.ext _ _ (Prod.ext hx hy)⟩
  have count := Fintype.card_le_of_surjective c.mapDart surj
  have estimate : n * (n - 1) ≤ 2 * H.edgeSet.ncard := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← H.edgeFinset_card]
    simpa [dart_card_eq_sum_degrees (G := completeGraph (Fin n)), H.dart_card_eq_twice_card_edges,
      Nat.mul_comm] using count
  have h₁ : n - 1 ≤ Nat.sqrt (2 * H.edgeSet.ncard) :=
    Nat.le_sqrt.mpr ((Nat.mul_le_mul_right _ (Nat.sub_le n 1)).trans estimate)
  exact ⟨c.colorable.toColoring (by simp; omega)⟩

/-- In particular this implies Corollary 7 of Cambie et al.
The parameter k counts vertices in the path. -/
theorem path_ramsey (k : ℕ) {W : Type} [Fintype W] (H : SimpleGraph W) :
    graphRamsey (pathGraph k) H ≤ Fintype.card W + (k - 2) * Nat.sqrt (2 * H.edgeSet.ncard) := by
  apply Nat.sInf_le
  intro G
  by_cases h : pathGraph k ⊑ G
  · exact Or.inl h
  · exact Or.inr (colored_copy k _ H G (few_colors H).some (by simp) h)

/-- Closing a path inside the neighborhood by its center makes a cycle. -/
lemma close_path {V : Type} (R : SimpleGraph V) (v : V) (l : ℕ)
    (h : pathGraph (l + 1) ⊑ R.induce (R.neighborSet v)) : cycleGraph (l + 2) ⊑ R := by
  classical
  obtain ⟨p⟩ := h
  let f : Fin (l + 2) → V := Fin.cases v (fun i => (p i).val)
  have adj (i : Fin (l + 1)) : R.Adj v (p i).val := (p i).property
  have consecutive (i j : Fin (l + 1)) (h : (i.succ - j.succ).val = 1) : j.val + 1=i.val := by
    by_cases hle : j.succ ≤ i.succ
    · rw [Fin.sub_val_of_le hle] at h
      simp only [Fin.val_succ] at h
      omega
    · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hle)] at h
      simp only [Fin.val_succ] at h
      omega
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro a b hab
    refine Fin.cases (motive := fun a => ∀ b, (cycleGraph (l + 2)).Adj a b → R.Adj (f a) (f b))
      (fun b => ?_) (fun i b => ?_) a b hab
    · refine Fin.cases (fun h => False.elim (h.ne rfl)) (fun j _ => adj j) b
    · refine Fin.cases (fun _ => (adj i).symm) (fun j h => ?_) b
      apply p.toHom.map_adj
      apply pathGraph_adj.mpr
      exact (cycleGraph_adj'.mp h).elim (fun e => Or.inr (consecutive i j e)) (fun e => Or.inl (consecutive j i e))
  · intro a b eq
    refine Fin.cases (motive := fun a => ∀ b, f a = f b → a = b)
      (fun b => ?_) (fun i b => ?_) a b eq
    · exact Fin.cases (fun _ => rfl) (fun j e => False.elim ((adj j).ne e)) b
    · exact Fin.cases (fun e => False.elim ((adj i).ne e.symm))
        (fun j e => congrArg Fin.succ (p.injective (Subtype.ext e))) b

/-- Every path-free set above the Corollary 7 threshold already contains a blue target. -/
lemma small_path_free_set {V W : Type} [Fintype V] [Fintype W] (R : SimpleGraph V)
    (H : SimpleGraph W) (s : Set V) (l : ℕ) (free : ¬ pathGraph l ⊑ R.induce s)
    (miss : ¬ H ⊑ Rᶜ) : s.ncard < Fintype.card W + (l - 2) * Nat.sqrt (2 * H.edgeSet.ncard) := by
  classical
  by_contra! h
  have size : Fintype.card W + (l - 2) * Nat.sqrt (2 * H.edgeSet.ncard) ≤ Fintype.card s := by
    simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using h
  exact miss ((colored_copy l _ H (R.induce s) (few_colors H).some size free).trans
    (Embedding.complEquiv (Embedding.induce s)).isContained)

theorem main : H1 → H2 → OMA.R_Erdos570_erdos_570_R1.H1 := by
  classical
  intro second extremal k hk
  obtain ⟨B, core⟩ := extremal k hk
  refine ⟨B, ?_⟩
  intro W V _ _ H G conn big size free
  by_contra miss
  have miss' : ¬ H ⊑ Gᶜᶜ := by simpa using miss
  apply miss'
  apply core W V H Gᶜ conn big size free
  · intro v
    obtain ⟨l, rfl⟩ : ∃ l, k = l + 2 := ⟨k - 2, by omega⟩
    simpa only [show l + 2 - 3 = l + 1 - 2 by omega] using
      small_path_free_set Gᶜ H (Gᶜ.neighborSet v) (l + 1)
        (fun h => free (close_path Gᶜ v l h)) miss'
  · intro five v
    exact small_path_free_set Gᶜ H _ (2 * k) (fun h => free (second k five V Gᶜ v h)) miss'

end OMA.R_Erdos570_erdos_570_R1_H1_R2
