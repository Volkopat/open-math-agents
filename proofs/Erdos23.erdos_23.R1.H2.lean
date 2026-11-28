import OMAReductions.R_Erdos23_erdos_23_R1

-- Step Erdos23.erdos_23.R1.H2: hypothesis H2 of reduction Erdos23.erdos_23.R1
-- Credit: @JamesSlash. Averaging over all vertex sets S: for an edge uv, the map S -> S symmDiff {u} swaps the
-- sets that keep u, v on one side with those that separate them, so each edge is one-sided for exactly half
-- of the 2 ^ n sets. Hence the one-sided counts sum to |E| * 2 ^ (n - 1) and some S has at most |E| / 2.

theorem e23_same_iff {V : Type} (S : Finset V) (u v : V) :
    (∀ x ∈ s(u, v), ∀ y ∈ s(u, v), (x ∈ S ↔ y ∈ S)) ↔ (u ∈ S ↔ v ∈ S) := by
  simp only [Sym2.mem_iff]
  constructor
  · intro h
    exact h u (Or.inl rfl) v (Or.inr rfl)
  · rintro h x (rfl | rfl) y (rfl | rfl) <;> tauto

theorem e23_half_count {V : Type} [Fintype V] [DecidableEq V] (u v : V) (huv : u ≠ v) :
    2 * ((Finset.univ : Finset (Finset V)).filter (fun S => (u ∈ S ↔ v ∈ S))).card =
      2 ^ Fintype.card V := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Finset V)))
    (fun S => (u ∈ S ↔ v ∈ S))
  rw [Finset.card_univ, Fintype.card_finset] at hsplit
  have heq : ((Finset.univ : Finset (Finset V)).filter (fun S => (u ∈ S ↔ v ∈ S))).card =
      ((Finset.univ : Finset (Finset V)).filter (fun S => ¬ (u ∈ S ↔ v ∈ S))).card := by
    apply Finset.card_nbij' (fun S => symmDiff S {u}) (fun S => symmDiff S {u})
    · intro S hS
      simp only [Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hS ⊢
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, huv.symm, not_true_eq_false,
        and_false, false_or, true_and, and_true, not_false_eq_true] at hS ⊢
      tauto
    · intro S hS
      simp only [Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hS ⊢
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, huv.symm, not_true_eq_false,
        and_false, false_or, true_and, and_true, not_false_eq_true] at hS ⊢
      tauto
    · intro S _
      exact symmDiff_symmDiff_cancel_right {u} S
    · intro S _
      exact symmDiff_symmDiff_cancel_right {u} S
  omega

theorem e23_maxcut {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    ∃ S : Finset V, 2 * (E.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ E.card := by
  classical
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hsum : ∑ S : Finset V, 2 * (E.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card
      = ∑ e ∈ E, 2 * ((Finset.univ : Finset (Finset V)).filter
          (fun S => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card := by
    simp only [Finset.card_filter, Finset.mul_sum]
    exact Finset.sum_comm
  have hval : ∀ e ∈ E, 2 * ((Finset.univ : Finset (Finset V)).filter
      (fun S => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card = 2 ^ Fintype.card V := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      have huv : u ≠ v := fun h => hE _ he (Sym2.mk_isDiag_iff.mpr h)
      simp_rw [e23_same_iff]
      exact e23_half_count u v huv
  rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul] at hsum
  have hlt : ∑ _S : Finset V, E.card <
      ∑ S : Finset V, 2 * (E.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun S _ => hcon S)
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_finset, smul_eq_mul] at hlt
  rw [mul_comm] at hlt
  exact lt_irrefl _ hlt

theorem OMA.solution : OMA.R_Erdos23_erdos_23_R1.H2 := by
  intro V _ G
  classical
  obtain ⟨S, hS⟩ := e23_maxcut G.edgeFinset
    (fun e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he))
  refine ⟨S, ?_⟩
  rw [Nat.le_div_iff_mul_le two_pos, mul_comm]
  convert hS using 3
