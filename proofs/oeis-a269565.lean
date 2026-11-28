import OMAStatements.S_oeis_a269565

-- Credit: @oh-meh
open OMA.S_oeis_a269565

private abbrev Labels (n m : ℕ) := Equiv.Perm (Fin n) × Equiv.Perm (Fin m)

private def relabel {n m : ℕ} (g : Labels n m) (p : HamPath n m) : HamPath n m := by
  let e := g.1.prodCongr g.2
  refine ⟨p.val.map e, ?_, List.Nodup.map e.injective p.property.2.1, ?_⟩
  · rw [List.isChain_map]
    apply p.property.1.imp
    intro v w h
    simpa [e, rook, SimpleGraph.boxProd_adj, SimpleGraph.top_adj] using h
  · intro v
    exact e.apply_symm_apply v ▸ (List.mem_map_of_mem (f := e) (p.property.2.2 (e.symm v)))

private instance {n m : ℕ} : MulAction (Labels n m) (HamPath n m) where
  smul := relabel
  one_smul p := by
    apply Subtype.ext
    change p.val.map _ = p.val
    simp
  mul_smul g h p := by
    apply Subtype.ext
    change p.val.map _ = (p.val.map _).map _
    rw [List.map_map]
    rfl

private theorem free {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (p : HamPath n m) :
    MulAction.stabilizer (Labels n m) p = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have heq : g • p = p := hg
  have h := congrArg (fun t : HamPath n m => t.val) heq
  change p.val.map (g.1.prodCongr g.2) = p.val at h
  have h' : ∀ v : Fin n × Fin m, (g.1.prodCongr g.2) v = v := by
    intro v
    apply (List.map_inj_left.mp (show p.val.map (g.1.prodCongr g.2) = p.val.map id by simpa using h)) v
    exact p.property.2.2 v
  apply Prod.ext
  · apply Equiv.ext
    intro i
    exact congrArg Prod.fst (h' (i, ⟨0, by omega⟩))
  · apply Equiv.ext
    intro j
    exact congrArg Prod.snd (h' (⟨0, by omega⟩, j))

theorem OMA.solution : type_of% @OMA.S_oeis_a269565.main := by
  intro n m hn hm
  let G := Labels n m
  let P := HamPath n m
  let Q := Quotient (MulAction.orbitRel G P)
  have e : P ≃ Q × G := (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G P).trans
    (Equiv.sigmaEquivProdOfEquiv fun q => by
      rw [free hn hm q.out]
      exact QuotientGroup.quotientBot.toEquiv)
  have h := Nat.card_congr e
  change _ ∣ Nat.card P
  rw [h, Nat.card_prod]
  have size : Nat.card G = n.factorial * m.factorial := by
    simp [G, Labels, Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [size]
  exact dvd_mul_left _ _
