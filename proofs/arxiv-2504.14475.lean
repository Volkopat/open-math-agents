import OMAStatements.S_arxiv_2504_14475

namespace OMA.P_arxiv_2504_14475

open OMA.S_arxiv_2504_14475

/-! ### Part 1: Soundness and completeness of the 31-operator IP Hasse diagram (`prop:ip-monoid`) -/

section IPSoundness

variable {L : Type*} [PartialOrder L] {i n : L → L}

private lemma le_nn (hn : IsPseudoComp n) (x : L) : x ≤ n (n x) :=
  (hn x (n x)).mpr le_rfl

private lemma n_anti (hn : IsPseudoComp n) : Antitone n := by
  intro a b hab
  exact (hn a (n b)).mp (le_trans hab (le_nn hn b))

private lemma nnn (hn : IsPseudoComp n) (x : L) : n (n (n x)) = n x :=
  le_antisymm (n_anti hn (le_nn hn x)) (le_nn hn (n x))

private lemma nn_mono (hn : IsPseudoComp n) : Monotone (fun x => n (n x)) :=
  fun _ _ h => n_anti hn (n_anti hn h)

private lemma nn_le_b (hi : IsInteriorOp i) (hn : IsPseudoComp n) (x : L) :
    n (n x) ≤ n (i (n x)) :=
  n_anti hn (hi.1 (n x))

private lemma le_b (hi : IsInteriorOp i) (hn : IsPseudoComp n) (x : L) :
    x ≤ n (i (n x)) :=
  le_trans (le_nn hn x) (nn_le_b hi hn x)

private lemma b_mono (hi : IsInteriorOp i) (hn : IsPseudoComp n) :
    Monotone (fun x => n (i (n x))) :=
  fun _ _ h => n_anti hn (hi.2.1 (n_anti hn h))

private lemma bb (hi : IsInteriorOp i) (hn : IsPseudoComp n) (x : L) :
    n (i (n (n (i (n x))))) = n (i (n x)) := by
  apply le_antisymm
  · apply n_anti hn
    calc i (n x) = i (i (n x)) := (hi.2.2 (n x)).symm
      _ ≤ i (n (n (i (n x)))) := hi.2.1 (le_nn hn (i (n x)))
  · exact le_b hi hn (n (i (n x)))

private lemma i_le_ibi (hi : IsInteriorOp i) (hn : IsPseudoComp n) (x : L) :
    i x ≤ i (n (i (n (i x)))) :=
  calc i x = i (i x) := (hi.2.2 x).symm
    _ ≤ i (n (i (n (i x)))) := hi.2.1 (le_b hi hn (i x))

private lemma bib_le_b (hi : IsInteriorOp i) (hn : IsPseudoComp n) (x : L) :
    n (i (n (i (n (i (n x)))))) ≤ n (i (n x)) := by
  calc n (i (n (i (n (i (n x))))))
      ≤ n (i (n (n (i (n x))))) := b_mono hi hn (hi.1 _)
    _ = n (i (n x)) := bb hi hn x

private lemma ipEdge_sound (hi : IsInteriorOp i) (hn : IsPseudoComp n)
    {u v : Fin 31} (huv : (u, v) ∈ ipHasseEdges) (x : L) :
    evalIPWord i n (ipOpWord u) x ≤ evalIPWord i n (ipOpWord v) x := by
  simp only [ipHasseEdges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at huv
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals dsimp only [evalIPWord, ipOpWord]
  -- 26 upper edges
  · calc i x = i (i x) := (hi.2.2 x).symm
      _ ≤ i (n (n (i x))) := hi.2.1 (le_nn hn (i x))
  · exact hi.2.1 (nn_mono hn (hi.1 x))
  · exact le_nn hn _
  · exact hi.2.1 (nn_le_b hi hn (i x))
  · exact hi.2.1 (b_mono hi hn (hi.2.1 (le_nn hn x)))
  · calc i (n (i (n (i (n (n x))))))
        ≤ i (n (i (n (n (n x))))) := hi.2.1 (b_mono hi hn (hi.1 _))
      _ = i (n (i (n x))) := by rw [nnn hn]
  · exact le_nn hn _
  · exact nn_le_b hi hn _
  · exact bib_le_b hi hn x
  · exact hi.1 _
  · exact nn_mono hn (hi.2.1 (le_nn hn x))
  · exact nn_mono hn (i_le_ibi hi hn (n (n x)))
  · calc n (n (i (n (i (n (i (n (n x))))))))
        ≤ n (n (i (n (i (n (n (n x))))))) := nn_mono hn (hi.2.1 (b_mono hi hn (hi.1 _)))
      _ = n (n (i (n (i (n x))))) := by rw [nnn hn]
  · exact le_nn hn _
  · exact nn_mono hn (hi.2.1 (b_mono hi hn (hi.2.1 (le_nn hn x))))
  · exact le_trans (nn_le_b hi hn _) (bib_le_b hi hn _)
  · exact b_mono hi hn (hi.2.1 (nn_le_b hi hn x))
  · exact le_nn hn _
  · exact le_trans (nn_le_b hi hn _) (bib_le_b hi hn _)
  · exact b_mono hi hn (hi.2.1 (le_nn hn x))
  · exact i_le_ibi hi hn (n (n x))
  · exact nn_mono hn (i_le_ibi hi hn x)
  · exact hi.1 x
  · exact le_nn hn x
  · exact nn_le_b hi hn x
  · calc n (n (i (n (n x)))) ≤ n (n (n (n x))) := nn_mono hn (hi.1 (n (n x)))
      _ = n (n x) := by rw [nnn hn]
  -- 20 lower edges
  · exact le_nn hn _
  · calc n (n (i (n x))) ≤ n (n (n x)) := nn_mono hn (hi.1 (n x))
      _ = n x := nnn hn x
  · exact le_b hi hn (n x)
  · exact n_anti hn (hi.2.1 (le_nn hn x))
  · exact n_anti hn (bib_le_b hi hn x)
  · exact n_anti hn (le_b hi hn _)
  · apply n_anti hn
    calc i (n (i (n (i (n (n x))))))
        ≤ i (n (i (n (n (n x))))) := hi.2.1 (b_mono hi hn (hi.1 _))
      _ = i (n (i (n x))) := by rw [nnn hn]
  · exact bib_le_b hi hn (n x)
  · exact i_le_ibi hi hn (n x)
  · exact le_nn hn _
  · exact n_anti hn (b_mono hi hn (hi.2.1 (nn_le_b hi hn x)))
  · exact n_anti hn (hi.1 _)
  · exact n_anti hn (hi.2.1 (b_mono hi hn (hi.2.1 (le_nn hn x))))
  · exact n_anti hn (i_le_ibi hi hn x)
  · exact hi.2.1 (b_mono hi hn (hi.1 (n x)))
  · exact le_nn hn _
  · exact n_anti hn (b_mono hi hn (hi.2.1 (le_nn hn x)))
  · exact n_anti hn (hi.1 _)
  · exact hi.2.1 (n_anti hn (hi.2.1 (le_nn hn x)))
  · exact le_nn hn _

private lemma ipOpLE_sound (hi : IsInteriorOp i) (hn : IsPseudoComp n)
    {u v : Fin 31} (h : IPOpLE u v) (x : L) :
    evalIPWord i n (ipOpWord u) x ≤ evalIPWord i n (ipOpWord v) x := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans ih (ipEdge_sound hi hn hstep x)

end IPSoundness

/-! ### Decidable transitive closure for `IPOpLE` and the 7 finite chain counterexamples -/

-- Generic DAG reachability soundness via heights (zero bitwise OR in kernel reduction!)
private lemma dag_le_sound {n : ℕ} (edges : List (Fin n × Fin n)) (leB : Fin n → Fin n → Bool)
    (ht : Fin n → ℕ) (M : ℕ)
    (hM : ∀ u : Fin n, ht u ≤ M)
    (hedge_ht : ∀ e ∈ edges, ht e.1 < ht e.2)
    (hstep : ∀ u v : Fin n, leB u v = true →
      u = v ∨ edges.any (fun e => e.1 == u && leB e.2 v) = true) :
    ∀ u v : Fin n, leB u v = true → Relation.ReflTransGen (fun a b => (a, b) ∈ edges) u v := by
  suffices ∀ d (u v : Fin n), M - ht u ≤ d → leB u v = true →
      Relation.ReflTransGen (fun a b => (a, b) ∈ edges) u v from
    fun u v h => this M u v (Nat.sub_le _ _) h
  intro d
  induction d with
  | zero =>
    intro u v hd huv
    rcases hstep u v huv with rfl | hany
    · exact Relation.ReflTransGen.refl
    · exfalso
      rw [List.any_eq_true] at hany
      obtain ⟨e, he_mem, he_cond⟩ := hany
      simp only [Bool.and_eq_true, beq_iff_eq] at he_cond
      have hlt := hedge_ht e he_mem
      have hle := hM e.2
      rw [he_cond.1] at hlt
      omega
  | succ d ih =>
    intro u v hd huv
    rcases hstep u v huv with rfl | hany
    · exact Relation.ReflTransGen.refl
    · rw [List.any_eq_true] at hany
      obtain ⟨e, he_mem, he_cond⟩ := hany
      simp only [Bool.and_eq_true, beq_iff_eq] at he_cond
      have hlt := hedge_ht e he_mem
      have hle := hM u
      rw [he_cond.1] at hlt
      have htail := ih e.2 v (by omega) he_cond.2
      exact Relation.ReflTransGen.head (by rwa [← he_cond.1]) htail

private def ipTable : List ℕ :=
  [131071, 98302, 97124, 32680, 98000, 31520, 96832, 32384, 26880, 31232, 29696, 26624, 28672,
   24576, 16384, 114688, 81920, 2147352576, 2107375616, 1342701568, 2106589184, 2146435072,
   2134900736, 1954545664, 2097152000, 1778384896, 1946157056, 1744830464, 1342177280,
   1610612736, 1073741824]

private def ipHeights : List ℕ :=
  [0, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 6, 7, 1, 4, 0, 1, 2, 2, 1, 2, 3, 3, 3, 4, 4, 5, 5, 6]

private def ipLEBool (u v : Fin 31) : Bool := ((ipTable.getD u.val 0) >>> v.val) % 2 == 1

private lemma ipLEBool_step_ok :
    (List.finRange 31).all (fun u =>
      (List.finRange 31).all (fun v =>
        !ipLEBool u v || (u == v) || ipHasseEdges.any (fun e => e.1 == u && ipLEBool e.2 v))) = true := by
  decide

private lemma ipLEBool_sound (u v : Fin 31) (h : ipLEBool u v = true) : IPOpLE u v := by
  have hht_le : ∀ x : Fin 31, ipHeights.getD x.val 0 ≤ 7 := by
    have h0 : (List.finRange 31).all (fun x => decide (ipHeights.getD x.val 0 ≤ 7)) = true := by decide
    intro x; exact of_decide_eq_true (List.all_eq_true.mp h0 x (List.mem_finRange x))
  have hht_edge : ∀ e ∈ ipHasseEdges, ipHeights.getD e.1.val 0 < ipHeights.getD e.2.val 0 := by
    have h0 : ipHasseEdges.all (fun e => decide (ipHeights.getD e.1.val 0 < ipHeights.getD e.2.val 0)) = true := by decide
    intro e he; exact of_decide_eq_true (List.all_eq_true.mp h0 e he)
  refine dag_le_sound ipHasseEdges ipLEBool (fun x => ipHeights.getD x.val 0) 7
    hht_le hht_edge (fun a b hab => ?_) u v h
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp ipLEBool_step_ok a (List.mem_finRange a)) b (List.mem_finRange b)
  simp only [hab, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  exact h1

-- The 7 finite chain counterexamples (all on `Fin 2`, `Fin 3`, `Fin 4`)
private def m0_i : Fin 2 → Fin 2 := fun x => x
private def m0_n : Fin 2 → Fin 2 := fun x => if x = 0 then 1 else 0

private def m1_i : Fin 2 → Fin 2 := fun x => x
private def m1_n : Fin 2 → Fin 2 := fun _ => 1

private def m2_i : Fin 3 → Fin 3 := fun x => if x.val ≤ 1 then 0 else 2
private def m2_n : Fin 3 → Fin 3 := fun x => if x.val = 0 then 2 else 0

private def m3_i : Fin 3 → Fin 3 := fun x => if x.val = 2 then 1 else x
private def m3_n : Fin 3 → Fin 3 := fun x => if x.val ≤ 1 then 2 else 1

private def m4_i : Fin 4 → Fin 4 := fun x => if x.val = 0 then 0 else 1
private def m4_n : Fin 4 → Fin 4 := fun x =>
  match x.val with | 0 => 3 | 1 => 2 | 2 => 2 | _ => 0

private def m5_i : Fin 4 → Fin 4 := fun x => if x.val = 1 then 0 else x
private def m5_n : Fin 4 → Fin 4 := fun x =>
  match x.val with | 0 => 3 | 1 => 1 | _ => 0

private def m6_i : Fin 2 → Fin 2 := fun _ => 0
private def m6_n : Fin 2 → Fin 2 := fun _ => 1

private lemma m0_valid : IsInteriorOp m0_i ∧ IsPseudoComp m0_n := by
  refine ⟨⟨by decide, fun a b h => h, by decide⟩, by unfold IsPseudoComp; decide⟩

private lemma m1_valid : IsInteriorOp m1_i ∧ IsPseudoComp m1_n := by
  refine ⟨⟨by decide, fun a b h => h, by decide⟩, by unfold IsPseudoComp; decide⟩

private lemma m2_valid : IsInteriorOp m2_i ∧ IsPseudoComp m2_n := by
  refine ⟨⟨by decide, fun a b h => by revert a b h; decide, by decide⟩, by unfold IsPseudoComp; decide⟩

private lemma m3_valid : IsInteriorOp m3_i ∧ IsPseudoComp m3_n := by
  refine ⟨⟨by decide, fun a b h => by revert a b h; decide, by decide⟩, by unfold IsPseudoComp; decide⟩

private lemma m4_valid : IsInteriorOp m4_i ∧ IsPseudoComp m4_n := by
  refine ⟨⟨by decide, fun a b h => by revert a b h; decide, by decide⟩, by unfold IsPseudoComp; decide⟩

private lemma m5_valid : IsInteriorOp m5_i ∧ IsPseudoComp m5_n := by
  refine ⟨⟨by decide, fun a b h => by revert a b h; decide, by decide⟩, by unfold IsPseudoComp; decide⟩

private lemma m6_valid : IsInteriorOp m6_i ∧ IsPseudoComp m6_n := by
  refine ⟨⟨by decide, fun a b h => by revert a b h; decide, by decide⟩, by unfold IsPseudoComp; decide⟩

private def ipRefuted (u v : Fin 31) : Bool :=
  (List.finRange 2).any (fun x => !(evalIPWord m0_i m0_n (ipOpWord u) x ≤ evalIPWord m0_i m0_n (ipOpWord v) x)) ||
  (List.finRange 2).any (fun x => !(evalIPWord m1_i m1_n (ipOpWord u) x ≤ evalIPWord m1_i m1_n (ipOpWord v) x)) ||
  (List.finRange 3).any (fun x => !(evalIPWord m2_i m2_n (ipOpWord u) x ≤ evalIPWord m2_i m2_n (ipOpWord v) x)) ||
  (List.finRange 3).any (fun x => !(evalIPWord m3_i m3_n (ipOpWord u) x ≤ evalIPWord m3_i m3_n (ipOpWord v) x)) ||
  (List.finRange 4).any (fun x => !(evalIPWord m4_i m4_n (ipOpWord u) x ≤ evalIPWord m4_i m4_n (ipOpWord v) x)) ||
  (List.finRange 4).any (fun x => !(evalIPWord m5_i m5_n (ipOpWord u) x ≤ evalIPWord m5_i m5_n (ipOpWord v) x)) ||
  (List.finRange 2).any (fun x => !(evalIPWord m6_i m6_n (ipOpWord u) x ≤ evalIPWord m6_i m6_n (ipOpWord v) x))

private lemma ip_all_refuted :
    (List.finRange 31).all (fun u =>
      (List.finRange 31).all (fun v => ipLEBool u v || ipRefuted u v)) = true := by
  decide

private lemma ip_part :
    ∀ u v : Fin 31,
      (∀ (L : Type) [PartialOrder L] (i n : L → L),
        IsInteriorOp i → IsPseudoComp n →
        ∀ x : L, evalIPWord i n (ipOpWord u) x ≤ evalIPWord i n (ipOpWord v) x) ↔
      IPOpLE u v := by
  intro u v
  constructor
  · intro huniv
    have hall := List.all_eq_true.mp (List.all_eq_true.mp ip_all_refuted u (List.mem_finRange u)) v (List.mem_finRange v)
    rcases Bool.or_eq_true_iff.mp hall with hle | href
    · exact ipLEBool_sound u v hle
    · exfalso
      simp only [ipRefuted, Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and,
        Bool.not_eq_true', decide_eq_false_iff_not] at href
      rcases href with (((((⟨x, hx⟩ | ⟨x, hx⟩) | ⟨x, hx⟩) | ⟨x, hx⟩) | ⟨x, hx⟩) | ⟨x, hx⟩) | ⟨x, hx⟩
      · exact hx (huniv (Fin 2) m0_i m0_n m0_valid.1 m0_valid.2 x)
      · exact hx (huniv (Fin 2) m1_i m1_n m1_valid.1 m1_valid.2 x)
      · exact hx (huniv (Fin 3) m2_i m2_n m2_valid.1 m2_valid.2 x)
      · exact hx (huniv (Fin 3) m3_i m3_n m3_valid.1 m3_valid.2 x)
      · exact hx (huniv (Fin 4) m4_i m4_n m4_valid.1 m4_valid.2 x)
      · exact hx (huniv (Fin 4) m5_i m5_n m5_valid.1 m5_valid.2 x)
      · exact hx (huniv (Fin 2) m6_i m6_n m6_valid.1 m6_valid.2 x)
  · intro hle L _ i n hi hn x
    exact ipOpLE_sound hi hn hle x

/-! ### Part 2: Localic closure--supplement monoid (`prop:locales` and `thm:localic`) -/

section LocalicSoundness

variable {L : Type*} [Order.Frame L]

private lemma closedNucleus_le_iff (a : L) (m : Nucleus L) :
    closedNucleus a ≤ m ↔ a ≤ m ⊥ := by
  constructor
  · intro h
    have := h ⊥
    simpa [closedNucleus] using this
  · intro h x
    exact sup_le (le_trans h (m.monotone bot_le)) m.le_apply

private lemma closedNucleus_compl (a : L) : (closedNucleus a)ᶜ = openNucleus a := by
  apply le_antisymm
  · intro x
    change (⨅ y ≥ x, (a ⊔ y) ⇨ y) ≤ a ⇨ x
    refine le_trans (iInf₂_le x le_rfl) ?_
    rw [le_himp_iff]
    calc ((a ⊔ x) ⇨ x) ⊓ a
        ≤ ((a ⊔ x) ⇨ x) ⊓ (a ⊔ x) := inf_le_inf_left _ le_sup_left
      _ ≤ x := himp_inf_le
  · rw [← himp_bot, le_himp_iff]
    intro x
    change (openNucleus a x ⊓ closedNucleus a x) ≤ x
    change (a ⇨ x) ⊓ (a ⊔ x) ≤ x
    rw [inf_sup_left, sup_le_iff]
    exact ⟨by rw [inf_comm]; exact inf_himp_le, inf_le_right⟩

private lemma openNucleus_compl (a : L) : (openNucleus a)ᶜ = closedNucleus a := by
  apply le_antisymm
  · intro x
    change (⨅ y ≥ x, (a ⇨ y) ⇨ y) ≤ a ⊔ x
    refine le_trans (iInf₂_le (a ⊔ x) le_sup_right) ?_
    have h1 : a ⇨ (a ⊔ x) = ⊤ := eq_top_iff.mpr (by rw [le_himp_iff]; exact inf_le_right.trans le_sup_left)
    rw [h1, top_himp]
  · rw [← himp_bot, le_himp_iff]
    intro x
    change (closedNucleus a x ⊓ openNucleus a x) ≤ x
    change (a ⊔ x) ⊓ (a ⇨ x) ≤ x
    rw [inf_sup_right, sup_le_iff]
    exact ⟨inf_himp_le, inf_le_left⟩

private lemma sublocaleClosure_isInterior : IsInteriorOp (sublocaleClosure (L := L)) := by
  refine ⟨fun m => (closedNucleus_le_iff (m ⊥) m).mpr le_rfl, ?_, ?_⟩
  · intro m1 m2 h x
    exact sup_le_sup_right (h ⊥) x
  · intro m
    ext x
    simp [sublocaleClosure, closedNucleus]

private lemma compl_isPseudoComp : IsPseudoComp (fun m : Nucleus L => mᶜ) :=
  fun _ _ => le_compl_iff_le_compl

private lemma sublocaleClosure_compl_compl (m : Nucleus L) :
    (sublocaleClosure m)ᶜᶜ = sublocaleClosure m := by
  simp [sublocaleClosure, closedNucleus_compl, openNucleus_compl]

/-- Bowron (arXiv:2504.14475), Proposition 3 (`prop:locales`):
the interior operator `sublocaleInterior` equals `m ↦ (sublocaleClosure mᶜ)ᶜ`. -/
private lemma sublocaleInterior_eq (m : Nucleus L) :
    sublocaleInterior m = (sublocaleClosure mᶜ)ᶜ := by
  rw [sublocaleClosure, closedNucleus_compl]
  apply le_antisymm
  · refine iInf₂_le (mᶜ ⊥) ?_
    rw [← closedNucleus_compl]
    exact le_compl_iff_le_compl.mp ((closedNucleus_le_iff (mᶜ ⊥) mᶜ).mpr le_rfl)
  · refine le_iInf₂ fun a ha => ?_
    have hca : closedNucleus a ≤ mᶜ := by
      rw [← openNucleus_compl]
      exact compl_anti ha
    have hal : a ≤ mᶜ ⊥ := (closedNucleus_le_iff a mᶜ).mp hca
    intro x
    exact himp_le_himp_right hal

private lemma evalLocWord_eq_ip : ∀ (w : List LocGen) (m : Nucleus L),
    evalLocWord w m =
      evalIPWord (sublocaleClosure (L := L)) (fun x => xᶜ)
        (w.flatMap fun g => match g with | .c => [false] | .i => [true, false, true] | .s => [true]) m := by
  intro w
  induction w with
  | nil => intro m; rfl
  | cons g w ih =>
    intro m
    cases g <;> simp [evalLocWord, evalIPWord, ih, sublocaleInterior_eq]

-- Map each of the 21 localic operators to its equivalent operator in the 31-op IP monoid
-- under the collapse `i = --i` (where `sublocaleClosure` plays `i` and `sublocaleInterior` plays `b`).
private def locToIP (k : Fin 21) : Fin 31 :=
  match k.val with
  | 0  => 14  -- i        -> b
  | 1  => 13  -- ici      -> bib
  | 2  => 12  -- ic--     -> bi--
  | 3  => 10  -- ic       -> bi
  | 4  => 8   -- ci       -> ib
  | 5  => 5   -- cic--    -> ibi--
  | 6  => 3   -- cic      -> ibi
  | 7  => 2   -- c--      -> i--
  | 8  => 0   -- c        -> i
  | 9  => 16  -- --       -> --
  | 10 => 15  -- id       -> id
  | 11 => 30  -- -c       -> -i
  | 12 => 28  -- i-       -> b-
  | 13 => 29  -- -cic     -> -ibi
  | 14 => 26  -- ici-     -> bib-
  | 15 => 27  -- -ic      -> -bi
  | 16 => 19  -- -        -> -
  | 17 => 23  -- -ci      -> -ib
  | 18 => 22  -- ci-      -> ib-
  | 19 => 21  -- -ici     -> ibi-
  | _  => 17  -- -i       -> i-

private lemma evalLocOp_eq_ip (u : Fin 21) (m : Nucleus L) :
    evalLocWord (locOpWord u) m = evalIPWord (sublocaleClosure (L := L)) (fun x => xᶜ) (ipOpWord (locToIP u)) m := by
  have hc : ∀ x : Nucleus L, (sublocaleClosure x)ᶜᶜ = sublocaleClosure x := sublocaleClosure_compl_compl
  fin_cases u <;> simp only [locOpWord, locToIP, ipOpWord, evalLocWord_eq_ip, List.flatMap_cons,
    List.flatMap_nil, List.cons_append, List.nil_append, evalIPWord]
  all_goals first
    | rfl
    | (simp only [hc]; rfl)

private lemma locEdge_sound {u v : Fin 21} (huv : (u, v) ∈ locHasseEdges) (m : Nucleus L) :
    evalLocWord (locOpWord v) m ≤ evalLocWord (locOpWord u) m := by
  rw [evalLocOp_eq_ip u m, evalLocOp_eq_ip v m]
  have hle : IPOpLE (locToIP v) (locToIP u) := by
    have hall : locHasseEdges.all (fun e => ipLEBool (locToIP e.2) (locToIP e.1)) = true := by decide
    exact ipLEBool_sound _ _ (List.all_eq_true.mp hall (u, v) huv)
  exact ipOpLE_sound sublocaleClosure_isInterior compl_isPseudoComp hle m

private lemma locOpLE_sound {u v : Fin 21} (h : LocOpLE u v) (m : Nucleus L) :
    evalLocWord (locOpWord v) m ≤ evalLocWord (locOpWord u) m := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans (locEdge_sound hstep m) ih

end LocalicSoundness

/-! ### Completeness of the 21-operator localic Hasse diagram via `(ω+1)^op` and `Opens ℝ` -/

private def locTable : List ℕ :=
  [2047, 510, 492, 328, 496, 480, 320, 384, 256, 1920, 1280, 2095104, 2052096, 2023424,
   1982464, 1867776, 1114112, 1703936, 1835008, 1572864, 1048576]

private def locHeights : List ℕ :=
  [0, 1, 2, 3, 2, 3, 4, 4, 5, 1, 2, 0, 1, 1, 2, 2, 2, 3, 3, 4, 5]

private def locLEBool (u v : Fin 21) : Bool := ((locTable.getD u.val 0) >>> v.val) % 2 == 1

private lemma locLEBool_step_ok :
    (List.finRange 21).all (fun u =>
      (List.finRange 21).all (fun v =>
        !locLEBool u v || (u == v) || locHasseEdges.any (fun e => e.1 == u && locLEBool e.2 v))) = true := by
  decide

private lemma locLEBool_sound (u v : Fin 21) (h : locLEBool u v = true) : LocOpLE u v := by
  have hht_le : ∀ x : Fin 21, locHeights.getD x.val 0 ≤ 5 := by
    have h0 : (List.finRange 21).all (fun x => decide (locHeights.getD x.val 0 ≤ 5)) = true := by decide
    intro x; exact of_decide_eq_true (List.all_eq_true.mp h0 x (List.mem_finRange x))
  have hht_edge : ∀ e ∈ locHasseEdges, locHeights.getD e.1.val 0 < locHeights.getD e.2.val 0 := by
    have h0 : locHasseEdges.all (fun e => decide (locHeights.getD e.1.val 0 < locHeights.getD e.2.val 0)) = true := by decide
    intro e he; exact of_decide_eq_true (List.all_eq_true.mp h0 e he)
  refine dag_le_sound locHasseEdges locLEBool (fun x => locHeights.getD x.val 0) 5
    hht_le hht_edge (fun a b hab => ?_) u v h
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp locLEBool_step_ok a (List.mem_finRange a)) b (List.mem_finRange b)
  simp only [hab, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  exact h1

/-! #### Witness Frame 1: `L1 = OrderDual (WithTop ℕ)` and its double-negation nucleus `X_{¬¬}` -/

private abbrev L1 := OrderDual (WithTop ℕ)

private def jNN : Nucleus L1 where
  toFun x := if x = ⊥ then ⊥ else ⊤
  map_inf' x y := by
    by_cases hx : x = ⊥ <;> by_cases hy : y = ⊥
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy]
    · have hne : x ⊓ y ≠ ⊥ := by
        intro h
        rcases le_total x y with hle | hle
        · rw [inf_eq_left.mpr hle] at h; exact hx h
        · rw [inf_eq_right.mpr hle] at h; exact hy h
      simp [hx, hy, hne]
  idempotent' x := by
    by_cases hx : x = ⊥
    · simp [hx]
    · simp [hx]
  le_apply' x := by
    by_cases hx : x = ⊥
    · simp [hx]
    · simp [hx]

private lemma jNN_bot : jNN ⊥ = ⊥ := by simp [jNN]

private lemma jNN_ne_bot : jNN ≠ ⊥ := by
  intro h
  have h1 := congrFun (congrArg DFunLike.coe h) (OrderDual.toDual (1 : WithTop ℕ))
  have hne : (OrderDual.toDual (1 : WithTop ℕ) : L1) ≠ ⊥ := by
    intro heq
    have : (1 : WithTop ℕ) = ⊤ := OrderDual.ofDual_inj.mp heq
    exact WithTop.coe_ne_top this
  simp only [jNN, Nucleus.coe_mk, InfHom.coe_mk, Nucleus.bot_apply, if_neg hne] at h1
  have : (0 : WithTop ℕ) = 1 := OrderDual.ofDual_inj.mp h1
  norm_cast at this

private lemma jNN_ne_top : jNN ≠ ⊤ := by
  intro h
  have h1 := congrFun (congrArg DFunLike.coe h) (⊥ : L1)
  rw [jNN_bot, Nucleus.top_apply] at h1
  have : (⊤ : WithTop ℕ) = 0 := OrderDual.ofDual_inj.mp h1
  exact WithTop.top_ne_coe this

private lemma jNN_compl : jNNᶜ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x
  change (⨅ y ≥ x, jNN y ⇨ y) ≤ x
  by_cases hx : x = ⊥
  · subst hx
    -- Show `(⨅ y ≥ ⊥, jNN y ⇨ y) ≤ (n : WithTop ℕ)` in `OrderDual`, i.e., `n ≤ ofDual (...)` for all `n`!
    change OrderDual.ofDual (⊥ : L1) ≤ OrderDual.ofDual (⨅ y ≥ (⊥ : L1), jNN y ⇨ y)
    -- Equivalently, `ofDual (...) = ⊤` in `WithTop ℕ`!
    rw [show OrderDual.ofDual (⊥ : L1) = (⊤ : WithTop ℕ) from rfl]
    rw [top_le_iff]
    cases hval : OrderDual.ofDual (⨅ y ≥ (⊥ : L1), jNN y ⇨ y) with
    | top => rfl
    | coe n =>
      exfalso
      let y0 : L1 := OrderDual.toDual ((n + 1 : ℕ) : WithTop ℕ)
      have hy0_ne : y0 ≠ ⊥ := by
        intro heq
        exact WithTop.coe_ne_top (OrderDual.ofDual_inj.mp heq)
      have hle : (⨅ y ≥ (⊥ : L1), jNN y ⇨ y) ≤ y0 := by
        refine le_trans (iInf₂_le y0 bot_le) ?_
        have hjy : jNN y0 = ⊤ := by simp [jNN, hy0_ne]
        rw [hjy, top_himp]
      have hle' : ((n + 1 : ℕ) : WithTop ℕ) ≤ (n : WithTop ℕ) := by
        have := OrderDual.ofDual_le_ofDual.mpr hle
        rwa [hval] at this
      have : n + 1 ≤ n := WithTop.coe_le_coe.mp hle'
      omega
  · refine le_trans (iInf₂_le x le_rfl) ?_
    have hjx : jNN x = ⊤ := by simp [jNN, hx]
    rw [hjx, top_himp]

private def phiL1 : Fin 3 → Nucleus L1
  | 0 => ⊥
  | 1 => jNN
  | 2 => ⊤

private lemma phiL1_le_iff (a b : Fin 3) : phiL1 a ≤ phiL1 b ↔ a ≤ b := by
  fin_cases a <;> fin_cases b <;> simp only [phiL1, le_refl, bot_le, le_top, true_iff]
  · decide
  · decide
  · exact ⟨fun h => absurd (le_antisymm h bot_le) jNN_ne_bot, fun h => absurd h (by decide)⟩
  · decide
  · exact ⟨fun h => absurd (le_antisymm h bot_le) (fun h0 => jNN_ne_top (le_antisymm le_top (h0 ▸ bot_le))), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd (le_antisymm le_top h) jNN_ne_top, fun h => absurd h (by decide)⟩

private def mL1_c : Fin 3 → Fin 3 := fun x => if x = 2 then 2 else 0
private def mL1_s : Fin 3 → Fin 3 := fun x => if x = 0 then 2 else 0
private def mL1_i : Fin 3 → Fin 3 := fun x => mL1_s (mL1_c (mL1_s x))

private lemma phiL1_c (a : Fin 3) : sublocaleClosure (phiL1 a) = phiL1 (mL1_c a) := by
  fin_cases a
  · ext x; simp [phiL1, mL1_c, sublocaleClosure, closedNucleus]
  · ext x; simp [phiL1, mL1_c, sublocaleClosure, closedNucleus, jNN_bot]
  · ext x; simp [phiL1, mL1_c, sublocaleClosure, closedNucleus]

private lemma phiL1_s (a : Fin 3) : (phiL1 a)ᶜ = phiL1 (mL1_s a) := by
  fin_cases a
  · simp [phiL1, mL1_s]
  · simp [phiL1, mL1_s, jNN_compl]
  · simp [phiL1, mL1_s]

private lemma phiL1_i (a : Fin 3) : sublocaleInterior (phiL1 a) = phiL1 (mL1_i a) := by
  rw [sublocaleInterior_eq, phiL1_s, phiL1_c, phiL1_s]; rfl

private def evalFinLoc {n : ℕ} (fc fi fs : Fin n → Fin n) : List LocGen → Fin n → Fin n
  | [], x => x
  | .c :: w, x => fc (evalFinLoc fc fi fs w x)
  | .i :: w, x => fi (evalFinLoc fc fi fs w x)
  | .s :: w, x => fs (evalFinLoc fc fi fs w x)

private lemma phiL1_eval (w : List LocGen) (a : Fin 3) :
    evalLocWord w (phiL1 a) = phiL1 (evalFinLoc mL1_c mL1_i mL1_s w a) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g <;> simp [evalLocWord, evalFinLoc, ih, phiL1_c, phiL1_i, phiL1_s]

/-! #### Witness Frame 2: `L2 = TopologicalSpace.Opens ℝ` and induced subspace nuclei -/

private def nucOfSet (Y : Set ℝ) : Nucleus (TopologicalSpace.Opens ℝ) where
  toFun U := ⟨interior (U.1 ∪ Yᶜ), isOpen_interior⟩
  map_inf' U V := by
    ext x
    change x ∈ interior ((U.1 ∩ V.1) ∪ Yᶜ) ↔ x ∈ interior (U.1 ∪ Yᶜ) ∩ interior (V.1 ∪ Yᶜ)
    rw [Set.inter_union_distrib_right, interior_inter]
  idempotent' U := by
    change interior (interior (U.1 ∪ Yᶜ) ∪ Yᶜ) ⊆ interior (U.1 ∪ Yᶜ)
    exact interior_mono (Set.union_subset interior_subset Set.subset_union_right)
  le_apply' U := by
    change U.1 ⊆ interior (U.1 ∪ Yᶜ)
    exact interior_maximal Set.subset_union_left U.2

private lemma nucOfSet_le_iff (Y Z : Set ℝ) : nucOfSet Y ≤ nucOfSet Z ↔ Z ⊆ Y := by
  constructor
  · intro h x hxZ
    by_contra hxY
    let U : TopologicalSpace.Opens ℝ := ⟨({x} : Set ℝ)ᶜ, isClosed_singleton.isOpen_compl⟩
    have hmem : x ∈ (nucOfSet Y U).1 := by
      change x ∈ interior (({x} : Set ℝ)ᶜ ∪ Yᶜ)
      have huniv : ({x} : Set ℝ)ᶜ ∪ Yᶜ = Set.univ := by
        ext y; simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        by_cases hy : y = x
        · right; subst hy; exact hxY
        · left; exact hy
      rw [huniv, interior_univ]; trivial
    have hmemZ : x ∈ (nucOfSet Z U).1 := h U hmem
    have hsub := interior_subset hmemZ
    rcases hsub with h1 | h2
    · exact h1 rfl
    · exact h2 hxZ
  · intro hZY U
    exact interior_mono (Set.union_subset_union_right U.1 (Set.compl_subset_compl.mpr hZY))

private lemma nucOfSet_closure (Y : Set ℝ) :
    sublocaleClosure (nucOfSet Y) = nucOfSet (closure Y) := by
  ext U x
  change x ∈ (interior (∅ ∪ Yᶜ) ∪ U.1) ↔ x ∈ interior (U.1 ∪ (closure Y)ᶜ)
  rw [Set.empty_union, interior_compl, Set.union_comm]
  have hopen : IsOpen (U.1 ∪ (closure Y)ᶜ) := U.2.union isClosed_closure.isOpen_compl
  rw [hopen.interior_eq]

private lemma nucOfSet_compl (Y : Set ℝ) : (nucOfSet Y)ᶜ = nucOfSet Yᶜ := by
  apply le_antisymm
  · intro U x hx
    change x ∈ (⨅ V ≥ U, nucOfSet Y V ⇨ V).1 at hx
    have hW : IsOpen (⨅ V ≥ U, nucOfSet Y V ⇨ V).1 := (⨅ V ≥ U, nucOfSet Y V ⇨ V).2
    refine mem_interior.mpr ⟨(⨅ V ≥ U, nucOfSet Y V ⇨ V).1, ?_, hW, hx⟩
    intro y hy
    by_cases hyU : y ∈ U.1
    · exact Or.inl hyU
    · right
      rw [compl_compl]
      by_contra hyY
      let V : TopologicalSpace.Opens ℝ := ⟨({y} : Set ℝ)ᶜ, isClosed_singleton.isOpen_compl⟩
      have hUV : U ≤ V := fun z hz hzy => hyU (hzy ▸ hz)
      have hyV : y ∈ (nucOfSet Y V ⇨ V).1 := by
        have hle : (⨅ W ≥ U, nucOfSet Y W ⇨ W) ≤ nucOfSet Y V ⇨ V := iInf₂_le V hUV
        exact hle hy
      have htop : nucOfSet Y V = ⊤ := by
        ext z; simp only [nucOfSet, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
        have huniv : ({y} : Set ℝ)ᶜ ∪ Yᶜ = Set.univ := by
          ext w; simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
          by_cases hw : w = y
          · right; subst hw; exact hyY
          · left; exact hw
        change z ∈ interior (({y} : Set ℝ)ᶜ ∪ Yᶜ)
        rw [huniv, interior_univ]; trivial
      rw [htop, top_himp] at hyV
      exact hyV rfl
  · rw [← himp_bot (nucOfSet Y), le_himp_iff]
    intro U x hx
    change x ∈ interior (U.1 ∪ (Yᶜ)ᶜ) ∩ interior (U.1 ∪ Yᶜ) at hx
    have h1 := interior_subset hx.1
    have h2 := interior_subset hx.2
    rw [compl_compl] at h1
    rcases h1 with hU | hY
    · exact hU
    · rcases h2 with hU | hnY
      · exact hU
      · exact absurd hY hnY

private lemma nucOfSet_interior (Y : Set ℝ) :
    sublocaleInterior (nucOfSet Y) = nucOfSet (interior Y) := by
  rw [sublocaleInterior_eq, nucOfSet_compl, nucOfSet_closure, nucOfSet_compl, closure_compl, compl_compl]

-- Finite Boolean subalgebras of `Set ℝ` for `ℚ`, `{0}`, and `(0, 1)`:
-- 1. `Q`: bit 0 = `ℚ`, bit 1 = `ℚᶜ`
private def setQ : Set ℝ := Set.range ((↑) : ℚ → ℝ)

private lemma setQ_closure : closure setQ = Set.univ :=
  Rat.denseRange_cast.closure_eq

private lemma setQ_compl_closure : closure setQᶜ = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, hy1, hy2⟩ := exists_irrational_btwn (show x < x + ε / 2 by linarith)
  refine ⟨y, ?_, ?_⟩
  · intro ⟨q, hq⟩; exact hy1 ⟨q, hq⟩
  · rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith

private def decodeQ (m : Fin 4) : Set ℝ :=
  (if m.val % 2 = 1 then setQ else ∅) ∪ (if (m.val / 2) % 2 = 1 then setQᶜ else ∅)

private def mQ_c : Fin 4 → Fin 4 := fun m => if m.val = 0 then 0 else 3
private def mQ_s : Fin 4 → Fin 4 := fun m => ⟨3 - m.val, by omega⟩
private def mQ_i : Fin 4 → Fin 4 := fun m => mQ_s (mQ_c (mQ_s m))

private lemma decodeQ_compl (m : Fin 4) : (decodeQ m)ᶜ = decodeQ (mQ_s m) := by
  fin_cases m <;> simp [decodeQ, mQ_s]

private lemma decodeQ_closure (m : Fin 4) : closure (decodeQ m) = decodeQ (mQ_c m) := by
  fin_cases m
  · simp [decodeQ, mQ_c]
  · change closure (setQ ∪ ∅) = setQ ∪ setQᶜ
    rw [Set.union_empty, setQ_closure, Set.union_compl_self]
  · change closure (∅ ∪ setQᶜ) = setQ ∪ setQᶜ
    rw [Set.empty_union, setQ_compl_closure, Set.union_compl_self]
  · simp [decodeQ, mQ_c]

private lemma decode2_subset_iff (S : Set ℝ) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (a b : Fin 4) :
    ((if a.val % 2 = 1 then S else ∅) ∪ (if (a.val / 2) % 2 = 1 then Sᶜ else ∅)) ⊆
    ((if b.val % 2 = 1 then S else ∅) ∪ (if (b.val / 2) % 2 = 1 then Sᶜ else ∅)) ↔
    (a.val &&& b.val) = a.val := by
  obtain ⟨xS, hxS⟩ := hS
  obtain ⟨xSc, hxSc⟩ := hSc
  fin_cases a <;> fin_cases b <;> simp
  all_goals first
    | (intro h; exact hxSc (by rw [h]; trivial))
    | (intro h; rw [h] at hxS; exact hxS)

private lemma decodeQ_subset_iff (a b : Fin 4) : decodeQ a ⊆ decodeQ b ↔ (a.val &&& b.val) = a.val :=
  decode2_subset_iff setQ ⟨0, ⟨0, by norm_num⟩⟩
    (by obtain ⟨y, hy⟩ := exists_irrational_btwn (show (0 : ℝ) < 1 by norm_num)
        exact ⟨y, fun ⟨q, hq⟩ => hy.1 ⟨q, hq⟩⟩) a b

-- 2. `{0}`: bit 0 = `{0}`, bit 1 = `{0}ᶜ`
private def decodeP (m : Fin 4) : Set ℝ :=
  (if m.val % 2 = 1 then ({0} : Set ℝ) else ∅) ∪ (if (m.val / 2) % 2 = 1 then ({0} : Set ℝ)ᶜ else ∅)

private def mP_c : Fin 4 → Fin 4 := fun m => if (m.val / 2) % 2 = 1 then 3 else m
private def mP_s : Fin 4 → Fin 4 := fun m => ⟨3 - m.val, by omega⟩
private def mP_i : Fin 4 → Fin 4 := fun m => mP_s (mP_c (mP_s m))

private lemma closure_zero_compl : closure (({0} : Set ℝ)ᶜ) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_cases hx : x = 0
  · refine ⟨ε / 2, by simp; linarith, ?_⟩
    rw [hx, Real.dist_eq, abs_of_neg (by linarith)]; linarith
  · exact ⟨x, hx, by simpa using hε⟩

private lemma decodeP_compl (m : Fin 4) : (decodeP m)ᶜ = decodeP (mP_s m) := by
  fin_cases m <;> simp [decodeP, mP_s]

private lemma decodeP_closure (m : Fin 4) : closure (decodeP m) = decodeP (mP_c m) := by
  fin_cases m
  · simp [decodeP, mP_c]
  · change closure (({0} : Set ℝ) ∪ ∅) = ({0} : Set ℝ) ∪ ∅
    rw [Set.union_empty, isClosed_singleton.closure_eq]
  · change closure (∅ ∪ ({0} : Set ℝ)ᶜ) = ({0} : Set ℝ) ∪ ({0} : Set ℝ)ᶜ
    rw [Set.empty_union, closure_zero_compl, Set.union_compl_self]
  · simp [decodeP, mP_c]

private lemma decodeP_subset_iff (a b : Fin 4) : decodeP a ⊆ decodeP b ↔ (a.val &&& b.val) = a.val :=
  decode2_subset_iff {0} ⟨0, rfl⟩ ⟨1, by norm_num⟩ a b

-- 3. `(0, 1)`: 4 disjoint atoms `A0 = (-∞, 0) ∪ (1, ∞)`, `A1 = {0}`, `A2 = (0, 1)`, `A3 = {1}`
private def atomI : Fin 4 → Set ℝ
  | 0 => {x : ℝ | x < 0 ∨ 1 < x}
  | 1 => {0}
  | 2 => Set.Ioo 0 1
  | 3 => {1}

private def decodeI (m : Fin 16) : Set ℝ :=
  (if (m.val >>> 0) % 2 = 1 then atomI 0 else ∅) ∪
  (if (m.val >>> 1) % 2 = 1 then atomI 1 else ∅) ∪
  (if (m.val >>> 2) % 2 = 1 then atomI 2 else ∅) ∪
  (if (m.val >>> 3) % 2 = 1 then atomI 3 else ∅)

private def mI_c (m : Fin 16) : Fin 16 :=
  ⟨if ((m.val >>> 0) % 2 = 1) ∨ ((m.val >>> 2) % 2 = 1) then m.val ||| 10 else m.val, by
    have := m.isLt; split_ifs
    · exact Nat.or_lt_two_pow (n := 4) this (by decide)
    · exact this⟩

private def mI_s (m : Fin 16) : Fin 16 := ⟨15 - m.val, by omega⟩
private def mI_i (m : Fin 16) : Fin 16 := mI_s (mI_c (mI_s m))

private noncomputable def repI : Fin 4 → ℝ
  | 0 => -1
  | 1 => 0
  | 2 => 1 / 2
  | 3 => 1

private lemma repI_mem (k j : Fin 4) : repI k ∈ atomI j ↔ k = j := by
  fin_cases k <;> fin_cases j <;> simp [repI, atomI, Set.Ioo] <;> norm_num

private lemma mem_decodeI_repI (m : Fin 16) (k : Fin 4) :
    repI k ∈ decodeI m ↔ (m.val >>> k.val) % 2 = 1 := by
  have h1 : ∀ j : Fin 4, repI k ∈ atomI j ↔ k = j := repI_mem k
  simp only [decodeI, Set.mem_union, Set.mem_ite_empty_right, h1]
  fin_cases k <;> simp

private lemma decodeI_part (x : ℝ) :
    ∃ k : Fin 4, x ∈ atomI k ∧ ∀ j : Fin 4, x ∈ atomI j → j = k := by
  rcases lt_trichotomy x 0 with hlt0 | rfl | hgt0
  · refine ⟨0, Or.inl hlt0, fun j hj => ?_⟩
    fin_cases j
    · rfl
    · simp [atomI] at hj; linarith
    · simp [atomI, Set.Ioo] at hj; linarith
    · simp [atomI] at hj; linarith
  · refine ⟨1, rfl, fun j hj => ?_⟩
    fin_cases j
    · simp [atomI] at hj; linarith
    · rfl
    · simp [atomI, Set.Ioo] at hj
    · simp [atomI] at hj
  · rcases lt_trichotomy x 1 with hlt1 | rfl | hgt1
    · refine ⟨2, ⟨hgt0, hlt1⟩, fun j hj => ?_⟩
      fin_cases j
      · simp [atomI] at hj; rcases hj with hj | hj <;> linarith
      · simp [atomI] at hj; linarith
      · rfl
      · simp [atomI] at hj; linarith
    · refine ⟨3, rfl, fun j hj => ?_⟩
      fin_cases j
      · simp [atomI] at hj; linarith
      · simp [atomI] at hj
      · simp [atomI, Set.Ioo] at hj
      · rfl
    · refine ⟨0, Or.inr hgt1, fun j hj => ?_⟩
      fin_cases j
      · rfl
      · simp [atomI] at hj; linarith
      · simp [atomI, Set.Ioo] at hj; linarith
      · simp [atomI] at hj; linarith

private lemma mem_decodeI_iff (m : Fin 16) (x : ℝ) (k : Fin 4) (hx : x ∈ atomI k) :
    x ∈ decodeI m ↔ (m.val >>> k.val) % 2 = 1 := by
  obtain ⟨k0, hk0, huniq⟩ := decodeI_part x
  have hkk : k = k0 := huniq k hx
  subst hkk
  simp only [decodeI, Set.mem_union]
  have hne : ∀ j : Fin 4, j ≠ k → x ∉ atomI j := fun j hjk hj => hjk (huniq j hj)
  fin_cases k
  · change x ∈ atomI 0 at hx; simp [hx, hne 1 (by decide), hne 2 (by decide), hne 3 (by decide)]
  · change x ∈ atomI 1 at hx; simp [hx, hne 0 (by decide), hne 2 (by decide), hne 3 (by decide)]
  · change x ∈ atomI 2 at hx; simp [hx, hne 0 (by decide), hne 1 (by decide), hne 3 (by decide)]
  · change x ∈ atomI 3 at hx; simp [hx, hne 0 (by decide), hne 1 (by decide), hne 2 (by decide)]

private lemma decodeI_compl (m : Fin 16) : (decodeI m)ᶜ = decodeI (mI_s m) := by
  ext x
  obtain ⟨k, hx, _⟩ := decodeI_part x
  simp only [Set.mem_compl_iff, mem_decodeI_iff _ x k hx]
  have : ∀ (a : Fin 16) (j : Fin 4), ¬ ((a.val >>> j.val) % 2 = 1) ↔ ((mI_s a).val >>> j.val) % 2 = 1 := by
    decide
  exact this m k

private lemma closure_atomI0 : closure (atomI 0) = atomI 0 ∪ atomI 1 ∪ atomI 3 := by
  ext x
  simp only [atomI, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    rw [Metric.mem_closure_iff] at hx
    by_contra hnot
    push Not at hnot
    have hgt0 : 0 < x := lt_of_le_of_ne hnot.1.1.1 (Ne.symm hnot.1.2)
    have hlt1 : x < 1 := lt_of_le_of_ne hnot.1.1.2 hnot.2
    let ε := min x (1 - x)
    have hε : 0 < ε := lt_min hgt0 (by linarith)
    obtain ⟨y, hy0 | hy1, hdist⟩ := hx ε hε
    · rw [Real.dist_eq, abs_lt] at hdist
      have := min_le_left x (1 - x); linarith
    · rw [Real.dist_eq, abs_lt] at hdist
      have := min_le_right x (1 - x); linarith
  · rintro (((hx | hx) | rfl) | rfl)
    · exact subset_closure (Or.inl hx)
    · exact subset_closure (Or.inr hx)
    · rw [Metric.mem_closure_iff]; intro ε hε
      exact ⟨-(ε / 2), Or.inl (by linarith), by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith⟩
    · rw [Metric.mem_closure_iff]; intro ε hε
      exact ⟨1 + ε / 2, Or.inr (by linarith), by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith⟩

private lemma closure_atomI2 : closure (atomI 2) = atomI 1 ∪ atomI 2 ∪ atomI 3 := by
  have h2 : atomI 2 = Set.Ioo 0 1 := rfl
  rw [h2, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  ext x
  simp only [atomI, Set.mem_Icc, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioo]
  constructor
  · rintro ⟨h0, h1⟩
    rcases eq_or_lt_of_le h0 with rfl | h0'
    · exact Or.inl (Or.inl rfl)
    · rcases eq_or_lt_of_le h1 with rfl | h1'
      · exact Or.inr rfl
      · exact Or.inl (Or.inr ⟨h0', h1'⟩)
  · rintro (((rfl | ⟨h0, h1⟩) | rfl)) <;> constructor <;> linarith

private lemma decodeI_closure (m : Fin 16) : closure (decodeI m) = decodeI (mI_c m) := by
  have hcl : closure (decodeI m) =
      (if (m.val >>> 0) % 2 = 1 then atomI 0 ∪ atomI 1 ∪ atomI 3 else ∅) ∪
      (if (m.val >>> 1) % 2 = 1 then atomI 1 else ∅) ∪
      (if (m.val >>> 2) % 2 = 1 then atomI 1 ∪ atomI 2 ∪ atomI 3 else ∅) ∪
      (if (m.val >>> 3) % 2 = 1 then atomI 3 else ∅) := by
    simp only [decodeI, closure_union]
    congr 1; congr 1; congr 1
    · split_ifs <;> simp [closure_atomI0]
    · split_ifs <;> simp [atomI]
    · split_ifs <;> simp [closure_atomI2]
    · split_ifs <;> simp [atomI]
  rw [hcl]
  ext x
  obtain ⟨k, hx, huniq⟩ := decodeI_part x
  rw [mem_decodeI_iff (mI_c m) x k hx]
  have hne : ∀ j : Fin 4, j ≠ k → x ∉ atomI j := fun j hjk hj => hjk (huniq j hj)
  have hbit : ∀ (a : Fin 16) (j : Fin 4),
      ((mI_c a).val >>> j.val) % 2 = 1 ↔
        (if j.val = 0 then (a.val >>> 0) % 2 = 1
         else if j.val = 1 then (a.val >>> 0) % 2 = 1 ∨ (a.val >>> 1) % 2 = 1 ∨ (a.val >>> 2) % 2 = 1
         else if j.val = 2 then (a.val >>> 2) % 2 = 1
         else (a.val >>> 0) % 2 = 1 ∨ (a.val >>> 2) % 2 = 1 ∨ (a.val >>> 3) % 2 = 1) := by
    decide
  rw [hbit m k]
  simp only [Set.mem_union, Set.mem_ite_empty_right]
  fin_cases k
  · change x ∈ atomI 0 at hx; simp [hx, hne 1 (by decide), hne 2 (by decide), hne 3 (by decide)]
  · change x ∈ atomI 1 at hx; simp [hx, hne 0 (by decide), hne 2 (by decide), hne 3 (by decide)]; tauto
  · change x ∈ atomI 2 at hx; simp [hx, hne 0 (by decide), hne 1 (by decide), hne 3 (by decide)]
  · change x ∈ atomI 3 at hx; simp [hx, hne 0 (by decide), hne 1 (by decide), hne 2 (by decide)]; tauto

private lemma decodeI_subset_iff (a b : Fin 16) : decodeI a ⊆ decodeI b ↔ (a.val &&& b.val) = a.val := by
  have hbits : ∀ x y : Fin 16, (∀ k : Fin 4, (x.val >>> k.val) % 2 = 1 → (y.val >>> k.val) % 2 = 1) ↔
      (x.val &&& y.val) = x.val := by decide
  rw [← hbits a b]
  constructor
  · intro h k hk
    exact (mem_decodeI_repI b k).mp (h ((mem_decodeI_repI a k).mpr hk))
  · intro h x hx
    obtain ⟨k, hxk, _⟩ := decodeI_part x
    exact (mem_decodeI_iff b x k hxk).mpr (h k ((mem_decodeI_iff a x k hxk).mp hx))

-- Lift finite evaluations to `Nucleus (Opens ℝ)`:
private lemma nucQ_eval (w : List LocGen) (m : Fin 4) :
    evalLocWord w (nucOfSet (decodeQ m)) = nucOfSet (decodeQ (evalFinLoc mQ_c mQ_i mQ_s w m)) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g
    · simp only [evalLocWord, evalFinLoc, ih, nucOfSet_closure, decodeQ_closure]
    · simp only [evalLocWord, evalFinLoc, ih, sublocaleInterior_eq, nucOfSet_compl, decodeQ_compl,
        nucOfSet_closure, decodeQ_closure]; rfl
    · simp only [evalLocWord, evalFinLoc, ih, nucOfSet_compl, decodeQ_compl]

private lemma nucP_eval (w : List LocGen) (m : Fin 4) :
    evalLocWord w (nucOfSet (decodeP m)) = nucOfSet (decodeP (evalFinLoc mP_c mP_i mP_s w m)) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g
    · simp only [evalLocWord, evalFinLoc, ih, nucOfSet_closure, decodeP_closure]
    · simp only [evalLocWord, evalFinLoc, ih, sublocaleInterior_eq, nucOfSet_compl, decodeP_compl,
        nucOfSet_closure, decodeP_closure]; rfl
    · simp only [evalLocWord, evalFinLoc, ih, nucOfSet_compl, decodeP_compl]

private lemma nucI_eval (w : List LocGen) (m : Fin 16) :
    evalLocWord w (nucOfSet (decodeI m)) = nucOfSet (decodeI (evalFinLoc mI_c mI_i mI_s w m)) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g
    · simp only [evalLocWord, evalFinLoc, ih, nucOfSet_closure, decodeI_closure]
    · simp only [evalLocWord, evalFinLoc, ih, sublocaleInterior_eq, nucOfSet_compl, decodeI_compl,
        nucOfSet_closure, decodeI_closure]; rfl
    · simp only [evalLocWord, evalFinLoc, ih, nucOfSet_compl, decodeI_compl]

private def locRefuted (u v : Fin 21) : Bool :=
  (List.finRange 3).any (fun x =>
    !(evalFinLoc mL1_c mL1_i mL1_s (locOpWord v) x ≤ evalFinLoc mL1_c mL1_i mL1_s (locOpWord u) x)) ||
  (List.finRange 4).any (fun x =>
    let a := evalFinLoc mQ_c mQ_i mQ_s (locOpWord u) x
    let b := evalFinLoc mQ_c mQ_i mQ_s (locOpWord v) x
    !(a.val &&& b.val == a.val)) ||
  (List.finRange 4).any (fun x =>
    let a := evalFinLoc mP_c mP_i mP_s (locOpWord u) x
    let b := evalFinLoc mP_c mP_i mP_s (locOpWord v) x
    !(a.val &&& b.val == a.val)) ||
  (List.finRange 16).any (fun x =>
    let a := evalFinLoc mI_c mI_i mI_s (locOpWord u) x
    let b := evalFinLoc mI_c mI_i mI_s (locOpWord v) x
    !(a.val &&& b.val == a.val))

private lemma loc_all_refuted :
    (List.finRange 21).all (fun u =>
      (List.finRange 21).all (fun v => locLEBool u v || locRefuted u v)) = true := by
  decide

private lemma loc_part :
    ∀ u v : Fin 21,
      (∀ (L : Type) [Order.Frame L] (m : Nucleus L),
        evalLocWord (locOpWord v) m ≤ evalLocWord (locOpWord u) m) ↔
      LocOpLE u v := by
  intro u v
  constructor
  · intro huniv
    have hall := List.all_eq_true.mp (List.all_eq_true.mp loc_all_refuted u (List.mem_finRange u)) v (List.mem_finRange v)
    rcases Bool.or_eq_true_iff.mp hall with hle | href
    · exact locLEBool_sound u v hle
    · exfalso
      simp only [locRefuted, Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and,
        Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne] at href
      rcases href with ((⟨x, hx⟩ | ⟨x, hx⟩) | ⟨x, hx⟩) | ⟨x, hx⟩
      · have h := huniv L1 (phiL1 x)
        rw [phiL1_eval, phiL1_eval, phiL1_le_iff] at h
        exact hx h
      · have h := huniv (TopologicalSpace.Opens ℝ) (nucOfSet (decodeQ x))
        rw [nucQ_eval, nucQ_eval, nucOfSet_le_iff, decodeQ_subset_iff] at h
        exact hx h
      · have h := huniv (TopologicalSpace.Opens ℝ) (nucOfSet (decodeP x))
        rw [nucP_eval, nucP_eval, nucOfSet_le_iff, decodeP_subset_iff] at h
        exact hx h
      · have h := huniv (TopologicalSpace.Opens ℝ) (nucOfSet (decodeI x))
        rw [nucI_eval, nucI_eval, nucOfSet_le_iff, decodeI_subset_iff] at h
        exact hx h
  · intro hle L _ m
    exact locOpLE_sound hle m

theorem main_proof : type_of% @OMA.S_arxiv_2504_14475.main :=
  ⟨ip_part, loc_part⟩

end OMA.P_arxiv_2504_14475

theorem OMA.solution : type_of% @OMA.S_arxiv_2504_14475.main :=
  OMA.P_arxiv_2504_14475.main_proof
