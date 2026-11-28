import FormalConjectures.ErdosProblems.«640»

open SimpleGraph

namespace OMA.R_Erdos640_erdos_640_R1
theorem colorable_of_layers {V : Type*} (G : SimpleGraph V) (m : ℕ)
    (h : ∀ (r : V) (d : ℕ),
      (G.induce {v | G.Reachable r v ∧ G.dist r v = d}).Colorable m) :
    G.Colorable (2 * m) := by
  classical
  apply SimpleGraph.colorable_iff_forall_connectedComponent.mpr
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h r =>
    let S := (G.connectedComponentMk r).supp
    let C (d : ℕ) := (h r d).some
    let reach (v : S) : G.Reachable r v.val := by
      exact ConnectedComponent.eq.mp v.property.symm
    let color (v : S) : Fin 2 × Fin m :=
      (⟨G.dist r v.val % 2, Nat.mod_lt _ (by decide)⟩,
        C (G.dist r v.val) ⟨v.val, reach v, rfl⟩)
    let col : ((G.connectedComponentMk r).toSimpleGraph).Coloring (Fin 2 × Fin m) :=
      Coloring.mk color (by
        intro v w hvw heq
        have adj : G.Adj v.val w.val := hvw
        have hmod : G.dist r v.val % 2 = G.dist r w.val % 2 :=
          congrArg (fun x : Fin 2 × Fin m => x.1.val) heq
        have hd : G.dist r v.val = G.dist r w.val := by
          rcases (adj.diff_dist_adj (u := r)) with h' | h' | h' <;> omega
        have hne := (C (G.dist r v.val)).valid
          (show (G.induce {x | G.Reachable r x ∧ G.dist r x = G.dist r v.val}).Adj
            ⟨v.val, reach v, rfl⟩ ⟨w.val, reach w, hd.symm⟩ from adj)
        have recolor_eq (d e : ℕ) (he : d = e) (x : V)
            (hr : G.Reachable r x) (hxd : G.dist r x = d) :
            C d ⟨x,hr,hxd⟩ = C e ⟨x,hr,hxd.trans he⟩ := by
          subst e
          rfl
        exact hne ((congrArg Prod.snd heq).trans
          (recolor_eq _ _ hd.symm w.val (reach w) rfl)))
    simpa using col.colorable

theorem exists_high_layer {V : Type*} (G : SimpleGraph V) (m : ℕ)
    (h : ((2 * m + 1 : ℕ) : ℕ∞) ≤ G.chromaticNumber) :
    ∃ (r : V) (d : ℕ),
      (((m+1 : ℕ) : ℕ∞) ≤
      (G.induce {v | G.Reachable r v ∧ G.dist r v = d}).chromaticNumber) := by
  classical
  by_contra! hn
  have hc : G.Colorable (2*m) := colorable_of_layers G m (fun r d => by
    apply chromaticNumber_le_iff_colorable.mp
    exact Order.le_of_lt_add_one (by simpa using hn r d))
  have h' := le_trans h hc.chromaticNumber_le
  norm_cast at h'
  omega


/-- Path analogue of the Erdős-Hajnal conjecture, without the odd-cycle constraint.
The vertex span includes all ambient edges, not just the edges traversed by the path. -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ N : ℕ, ∀ (V : Type) (_ : Finite V) (G : SimpleGraph V),
    (N : ℕ∞) ≤ G.chromaticNumber →
    ∃ u v, ∃ p : G.Walk u v, p.IsPath ∧
      (k : ℕ∞) ≤ (G.induce {x | x ∈ p.support}).chromaticNumber

/-- The local BFS-level closure lemma: a (k+1)-rich path lying in a single level
can be shortened if necessary and joined through lower BFS levels to obtain a k-rich odd cycle. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (r : V) (d m : ℕ),
    let S := G.induce {x | G.Reachable r x ∧ G.dist r x = d}
    (∃ u v, ∃ p : S.Walk u v, p.IsPath ∧
      ((m+2 : ℕ) : ℕ∞) ≤ (S.induce {x | x ∈ p.support}).chromaticNumber) →
    Erdos640.HasHighChromaticOddCycle G (m+1)

theorem main : H1 → H2 → type_of% @Erdos640.erdos_640 := by
  intro h1 h2 k hk
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m+1 := ⟨k-1, by omega⟩
  obtain ⟨N,hN⟩ := h1 (m+2) (by omega)
  refine ⟨2*N+1, ?_⟩
  intro n G hG
  obtain ⟨r,d,hd⟩ := exists_high_layer G N hG
  apply h2 _ G r d m
  apply hN _ (inferInstance) _
  exact le_trans (by norm_cast; omega) hd

end OMA.R_Erdos640_erdos_640_R1
