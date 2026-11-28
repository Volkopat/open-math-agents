import OMAReductions.R_Erdos570_erdos_570_R1_H1_R2
import Mathlib

/-!
# A cycle from a path in a second neighborhood

This formalizes Lemma 8 of Cambie, Freschi, Morawski, Petrova and Pokrovskiy,
“Ramsey number of a cycle versus a graph of a given size” (arXiv:2601.10238).
The chosen common neighbors of the center and each path vertex determine which
of three explicit cycles to embed.
-/
open SimpleGraph
namespace SecondPath

lemma cyclic_order {V : Type*} (R : SimpleGraph V) {k : ℕ} (f : Fin k → V)
    (inj : Function.Injective f)
    (step : ∀ i j : Fin k, i.val + 1 = j.val → R.Adj (f i) (f j))
    (wrap : ∀ i j : Fin k, i.val + 1 = k → j.val = 0 → R.Adj (f i) (f j)) :
    cycleGraph k ⊑ R := by
  have forward (i j : Fin k) (h : (j - i).val = 1) : R.Adj (f i) (f j) := by
    by_cases le : i ≤ j
    · rw [Fin.sub_val_of_le le] at h
      exact step i j (by omega)
    · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge le)] at h
      exact wrap i j (by omega) (by omega)
  refine ⟨⟨⟨f, ?_⟩, inj⟩⟩
  intro i j h
  exact (cycleGraph_adj'.mp h).elim (fun e => (forward j i e).symm) (forward i j)

lemma close_interval {V : Type*} (R : SimpleGraph V) (p : ℕ → V) {L : ℕ}
    (inj : ∀ i j, i < L → j < L → p i = p j → i = j)
    (next : ∀ i, i + 1 < L → R.Adj (p i) (p (i+1)))
    (xs : List V) (a d k : ℕ) (hx : 0 < xs.length) (hd : 0 < d)
    (bound : a+d ≤ L) (length : xs.length+d = k)
    (nd : xs.Nodup) (chain : xs.IsChain R.Adj)
    (sep : ∀ x ∈ xs, ∀ j, a ≤ j → j < a+d → x ≠ p j)
    (enter : R.Adj xs[xs.length-1] (p a))
    (close : R.Adj (p (a+d-1)) xs[0]) : cycleGraph k ⊑ R := by
  let f (i : Fin k) := if h : i.val < xs.length then xs[i.val] else p (a+(i.val-xs.length))
  apply cyclic_order R f
  · intro i j h
    dsimp only [f] at h
    split at h <;> rename_i hi <;> split at h <;> rename_i hj
    · apply Fin.ext
      exact congrArg (fun t : Fin xs.length => t.val) (nd.get_inj_iff.mp h)
    · exact False.elim (sep _ (List.getElem_mem ..) _ (by omega) (by omega) h)
    · exact False.elim (sep _ (List.getElem_mem ..) _ (by omega) (by omega) h.symm)
    · have := inj _ _ (by omega) (by omega) h
      apply Fin.ext
      omega
  · intro i j h
    dsimp only [f]
    split <;> rename_i hi <;> split <;> rename_i hj
    · subst_vars
      simpa only [← h] using (List.isChain_iff_getElem.mp chain i.val (by omega))
    · have he : i.val = xs.length-1 := by omega
      have he' : a+(j.val-xs.length) = a := by omega
      simpa only [he, he'] using enter
    · omega
    · have he : a+(j.val-xs.length) = (a+(i.val-xs.length))+1 := by omega
      rw [he]
      exact next _ (by omega)
  · intro i j hi hj
    have hlast : ¬ i.val < xs.length := by omega
    have hfirst : j.val < xs.length := by omega
    have he : a+(i.val-xs.length) = a+d-1 := by omega
    simpa only [f, dif_neg hlast, dif_pos hfirst, he, hj] using close


/-- The three cycle constructions in Lemma 8 of Cambie et al. -/
lemma of_witnesses {V : Type} (R : SimpleGraph V) (v : V) (p u : ℕ → V)
    (k : ℕ) (hk : 5 ≤ k)
    (inj : ∀ i j, i < 2*k → j < 2*k → p i = p j → i = j)
    (next : ∀ i, i+1 < 2*k → R.Adj (p i) (p (i+1)))
    (center : ∀ i, i < 2*k → v ≠ p i)
    (far : ∀ i, i < 2*k → ¬ R.Adj v (p i))
    (near : ∀ i, i < 2*k → R.Adj v (u i))
    (link : ∀ i, i < 2*k → R.Adj (u i) (p i)) : cycleGraph k ⊑ R := by
  have apart (i j : ℕ) (hi : i < 2*k) (hj : j < 2*k) : u i ≠ p j := by
    intro e
    exact far j hj (e ▸ near i hi)
  have pdiff (i j : ℕ) (hi : i < 2*k) (hj : j < 2*k) (h : i ≠ j) : p i ≠ p j :=
    fun eq => h (inj i j hi hj eq)
  by_contra miss
  -- Different witnesses at distance k−4 close a cycle through the center.
  have per (j : ℕ) (hj : j+(k-4) < 2*k) : u j = u (j+(k-4)) := by
    by_contra neq
    apply miss
    let e := j+(k-4)
    have hj' : j < 2*k := by omega
    have he : e < 2*k := hj
    have huv := (near j hj').ne
    have hev := (near e he).ne
    have hne : u e ≠ u j := Ne.symm neq
    refine close_interval R p inj next [u e, v, u j] j (k-3) k ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp
    · omega
    · omega
    · simp; omega
    · simp [hne, Ne.symm hev, huv]
    · simpa using And.intro (near e he).symm (near j hj')
    · intro x hx t ht ht'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact apart _ _ he (by omega)
      · exact center _ (by omega)
      · exact apart _ _ hj' (by omega)
    · exact link j hj'
    · have : j+(k-3)-1=e := by dsimp [e]; omega
      change R.Adj (p (j+(k-3)-1)) (u e)
      rw [this]
      exact (link e he).symm
  -- Two unequal successive witnesses give a cycle using disjoint path intervals.
  have adjacent (j : ℕ) (hj : j ≤ 1) : u j = u (j+1) := by
    by_contra neq
    apply miss
    let a := (j+1)+(k-4)
    let e := (j+(k-4))+(k-4)
    have ha : a < 2*k := by dsimp [a]; omega
    have he : e < 2*k := by dsimp [e]; omega
    have h1 : j+1 < 2*k := by omega
    have h0 : j < 2*k := by omega
    have ua : u (j+1) = u a := per _ ha
    have ue : u j = u e := (per j (by omega)).trans (per _ he)
    have d01 := pdiff j (j+1) h0 h1 (by omega)
    refine close_interval R p inj next [u j, p j, p (j+1), u (j+1)] a (k-4) k ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp
    · omega
    · dsimp [a]; omega
    · simp; omega
    · simp [neq, apart _ _ h0 h0, apart _ _ h0 h1, d01,
        Ne.symm (apart _ _ h1 h0), Ne.symm (apart _ _ h1 h1)]
    · simpa using And.intro (link j h0) (And.intro (next j h1) (link (j+1) h1).symm)
    · intro x hx t ht ht'
      have htL : t < 2*k := by dsimp [a] at ht'; omega
      have hsep : j+1 < t := by dsimp [a] at ht; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact apart _ _ h0 htL
      · exact pdiff _ _ h0 htL (by omega)
      · exact pdiff _ _ h1 htL (by omega)
      · exact apart _ _ h1 htL
    · change R.Adj (u (j+1)) (p a)
      rw [ua]
      exact link a ha
    · have eind : a+(k-4)-1 = e := by dsimp [a,e]; omega
      change R.Adj (p (a+(k-4)-1)) (u j)
      rw [eind,ue]
      exact (link e he).symm
  have last : u 0 = u (k-2) := by
    have h := (adjacent 0 (by decide)).trans ((adjacent 1 (by decide)).trans (per 2 (by omega)))
    simpa only [show 2+(k-4)=k-2 by omega] using h
  apply miss
  refine close_interval R p inj next [u 0] 0 (k-1) k ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · omega
  · omega
  · simp; omega
  · simp
  · simp
  · intro x hx j _ hj
    simp only [List.mem_singleton] at hx
    exact hx ▸ apart 0 j (by omega) (by omega)
  · exact link 0 (by omega)
  · change R.Adj (p (0+(k-1)-1)) (u 0)
    rw [show 0+(k-1)-1=k-2 by omega,last]
    exact (link _ (by omega)).symm
end SecondPath

theorem OMA.solution : OMA.R_Erdos570_erdos_570_R1_H1_R2.H1 := by
  classical
  intro k hk V _ R v path
  obtain ⟨g⟩ := path
  let idx (i : ℕ) : Fin (2*k) := if hi : i < 2*k then ⟨i,hi⟩ else ⟨0,by omega⟩
  have idx_val (i : ℕ) (hi : i < 2*k) : (idx i).val = i := by simp [idx,hi]
  let p (i : ℕ) : V := (g (idx i)).val
  have hp (i : ℕ) : p i ≠ v ∧ ¬ R.Adj v (p i) ∧ ∃ y, R.Adj v y ∧ R.Adj y (p i) :=
    (g (idx i)).property
  let u (i : ℕ) := (hp i).2.2.choose
  apply SecondPath.of_witnesses R v p u k hk
  · intro i j hi hj eq
    have ei : idx i = idx j := g.injective (Subtype.ext eq)
    simpa only [idx_val i hi, idx_val j hj] using congrArg Fin.val ei
  · intro i hi
    apply g.toHom.map_adj
    apply pathGraph_adj.mpr
    exact Or.inl (by rw [idx_val _ (by omega), idx_val _ hi])
  · exact fun i _ => (hp i).1.symm
  · exact fun i _ => (hp i).2.1
  · exact fun i _ => (hp i).2.2.choose_spec.1
  · exact fun i _ => (hp i).2.2.choose_spec.2
