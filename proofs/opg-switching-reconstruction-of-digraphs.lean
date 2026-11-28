import OMAStatements.S_opg_switching_reconstruction_of_digraphs

-- Credit: @marcusbuffett
open OMA.S_opg_switching_reconstruction_of_digraphs

namespace SwitchingWitness

abbrev V := Fin 12

/-- Each row is the bit mask of the outgoing neighbors. These are switchings of
the eleven-vertex circulant tournament with differences 2, 6, 7, 8, 10,
together with the isolated vertex 11. The switching masks are 79 and 87. -/
private def R (a b : V) : Prop :=
  (![628, 1081, 162, 405, 1028, 216, 1694, 531, 1271, 318, 685, 0] a : ℕ).testBit b.val = true

private def S (a b : V) : Prop :=
  (![620, 1057, 186, 1650, 995, 192, 1670, 523, 1263, 294, 693, 0] a : ℕ).testBit b.val = true

private def matchCard : V → V := ![2, 0, 6, 4, 3, 11, 1, 8, 5, 9, 7, 10]

/-- Each card isomorphism fixes 11 and acts affinely on the other vertices. -/
private def relabel (v x : V) : V :=
  let a : ℕ := ![5, 3, 4, 1, 1, 9, 9, 4, 9, 3, 5, 9] v
  let b : ℕ := ![7, 6, 0, 0, 0, 9, 6, 0, 6, 6, 7, 9] v
  if x.val < 11 then ⟨(a*x.val + b) % 11, by omega⟩ else 11

private noncomputable def perm (f : V → V) (h : Function.Injective f) : V ≃ V :=
  Equiv.ofBijective f ⟨h, (Finite.injective_iff_surjective.mp h)⟩

set_option maxRecDepth 8192 in
private theorem deck : SameDeck R S := by
  have hm : ∀ x y, matchCard x = matchCard y → x = y := by decide
  have hf : ∀ v x y, relabel v x = relabel v y → x = y := by decide
  have hc : ∀ v a b, switch R v a b ↔
      switch S (matchCard v) (relabel v a) (relabel v b) := by
    unfold switch R S
    decide
  refine ⟨perm matchCard (fun {_ _} => hm _ _), fun v => ?_⟩
  exact ⟨perm (relabel v) (fun {_ _} => hf v _ _), hc v⟩

/-- A vertex whose outgoing neighborhood consists of a directed triangle. -/
private def TriangleNeighborhood (D : V → V → Prop) : Prop :=
  ∃ v a b c, D v a ∧ D v b ∧ D v c ∧ D a b ∧ D b c ∧ D c a ∧
    ∀ z, D v z → z = a ∨ z = b ∨ z = c

private theorem transport {D E : V → V → Prop} (h : Iso D E)
    (t : TriangleNeighborhood D) : TriangleNeighborhood E := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨v, a, b, c, ha, hb, hc, hab, hbc, hca, hall⟩ := t
  refine ⟨f v, f a, f b, f c, (hf _ _).mp ha, (hf _ _).mp hb,
    (hf _ _).mp hc, (hf _ _).mp hab, (hf _ _).mp hbc, (hf _ _).mp hca, ?_⟩
  intro z hz
  obtain ⟨u, rfl⟩ := f.surjective z
  rcases hall u ((hf _ _).mpr hz) with rfl | rfl | rfl <;> simp

set_option maxRecDepth 8192 in
private theorem notIso : ¬ Iso R S := by
  have hr : TriangleNeighborhood R := by
    refine ⟨2, 1, 5, 7, ?_⟩
    unfold R
    decide
  have hs : ¬ TriangleNeighborhood S := by
    unfold TriangleNeighborhood S
    decide
  exact fun h => hs (transport h hr)

theorem witness : ∃ r : V → V → Prop, Oriented r ∧ ¬ Reconstructible r := by
  have hr : Oriented R := by unfold Oriented R; decide
  have hs : Oriented S := by unfold Oriented S; decide
  exact ⟨R, hr, fun h => notIso (h S hs deck)⟩

end SwitchingWitness

theorem OMA.solution : type_of% @OMA.S_opg_switching_reconstruction_of_digraphs.main := by
  exact ⟨12, le_rfl, SwitchingWitness.witness⟩
