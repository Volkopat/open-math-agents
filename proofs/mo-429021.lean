import OMAStatements.S_mo_429021

/-! Adapts @caa1982 pending #26211 and @cclyles merged #25595.
Uses standard product/subtype equivalences for the pair decomposition and
the fiberwise product simplification also used by @YOHSUKE-TAKAHASHI (#20639 companion). -/

theorem OMA.solution : type_of% @OMA.S_mo_429021.main := by
  intro a b c h
  let e : {p : (Fin a → Fin b) × (Fin b → Fin c) // p.2 ∘ p.1 = h} ≃
      Σ g : Fin b → Fin c, {f : Fin a → Fin b // g ∘ f = h} :=
    (Equiv.subtypeEquiv (Equiv.prodComm _ _) (fun _ => Iff.rfl)).trans
      (Equiv.subtypeProdEquivSigmaSubtype (fun g f => g ∘ f = h))
  rw [Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro g _
  have e2 : {f : Fin a → Fin b // g ∘ f = h} ≃ ((x : Fin a) → {y : Fin b // g y = h x}) :=
    (Equiv.subtypeEquivRight (fun f => by rw [funext_iff]; rfl)).trans Equiv.subtypePiEquivPi
  rw [Fintype.card_congr e2, Fintype.card_pi]
  simpa using (Fintype.prod_fiberwise' h
    (fun j => Fintype.card {y : Fin b // g y = j})).symm
