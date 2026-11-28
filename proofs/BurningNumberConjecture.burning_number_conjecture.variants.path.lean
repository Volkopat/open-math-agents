import FormalConjectures.Paper.BurningNumberConjecture

open SimpleGraph BurningNumberConjecture Finset

theorem OMA.solution : type_of% @BurningNumberConjecture.burning_number_conjecture.variants.path := by
  intro n hn
  let P := pathGraph n
  have hdl (a b : Fin n) : a.1 ≤ b.1 + P.dist a b ∧ b.1 ≤ a.1 + P.dist a b := by
    obtain ⟨p, hp⟩ := (pathGraph_preconnected n a b).exists_walk_length_eq_dist
    rw [← hp]; clear hp
    induction p with | nil => simp | cons h _ ih => have := pathGraph_adj.mp h; simp; omega
  have hdi (d : ℕ) : ∀ a b : Fin n, b.1 = a.1 + d → P.dist a b ≤ d := by
    induction d with
    | zero => intro a b h; simp [Fin.ext (by omega : a.1 = b.1)]
    | succ d ih =>
      intro a b h
      have e : P.Adj ⟨a.1 + d, by omega⟩ b := pathGraph_adj.mpr (.inl (by dsimp; omega))
      have := e.reachable.dist_triangle_right a; have := dist_eq_one_iff_adj.mpr e
      have := ih a ⟨a.1 + d, by omega⟩ rfl; omega
  let k := ⌈Real.sqrt n⌉₊
  have hc (t : ℕ) : k ≤ t ↔ n ≤ t ^ 2 := by
    rw [Nat.ceil_le, Real.sqrt_le_left (by positivity), ← Nat.cast_pow, Nat.cast_le]
  have hcov : ∃ x : Fin k → Fin n, IsBurningSequence P x := by
    let c (i : Fin k) : Fin n := ⟨min (i.rev.1 ^ 2 + i.rev.1) (n - 1), by omega⟩
    refine ⟨c, fun v => ?_⟩
    let r : Fin k := ⟨Nat.sqrt v.1, Nat.sqrt_lt'.mpr (v.2.trans_le ((hc k).1 le_rfl))⟩
    refine ⟨r.rev, pathGraph_preconnected n _ _, ?_⟩
    have : r.1 ^ 2 ≤ v.1 := Nat.sqrt_le' _
    have : v.1 ≤ r.1 ^ 2 + 2 * r.1 := by have := Nat.lt_succ_sqrt' v.1; dsimp [r]; nlinarith
    have : (c r.rev).1 = min (r.1 ^ 2 + r.1) (n - 1) := by simp [c]
    have hd : P.dist (c r.rev) v ≤ r.1 := by
      rcases le_total (c r.rev).1 v.1 with h | h
      · exact (hdi (v.1 - (c r.rev).1) _ v (by omega)).trans (by omega)
      · rw [SimpleGraph.dist_comm]; exact (hdi ((c r.rev).1 - v.1) v _ (by omega)).trans (by omega)
    have := Fin.val_rev r; omega
  refine le_antisymm (Nat.sInf_le hcov) ((hc _).2 ?_)
  let m := burningNumber P
  obtain ⟨x, hx⟩ : ∃ x : Fin m → Fin n, IsBurningSequence P x :=
    Nat.sInf_mem (s := {j | ∃ y : Fin j → Fin n, IsBurningSequence P y}) ⟨k, hcov⟩
  let I (r : Fin m) := Icc ((x r.rev).1 - r.1) ((x r.rev).1 + r.1)
  have hsub : range n ⊆ univ.biUnion I := fun v hv => by
    obtain ⟨i, _, hi⟩ := hx ⟨v, mem_range.mp hv⟩
    have h := hdl (x i) ⟨v, mem_range.mp hv⟩; dsimp at h; have := Fin.val_rev i; have := i.2
    exact mem_biUnion.mpr ⟨i.rev, mem_univ _, by simp [I]; omega⟩
  have hsum (t : ℕ) : ∑ j ∈ range t, (2 * j + 1) = t ^ 2 := by
    induction t with | zero => rfl | succ t ih => rw [sum_range_succ, ih]; ring
  exact ((card_range n).symm.trans_le (card_le_card hsub)).trans <| card_biUnion_le.trans <|
    (sum_le_sum fun r _ => by simp [I]; omega).trans
      ((Fin.sum_univ_eq_sum_range _ m).trans (hsum m)).le
