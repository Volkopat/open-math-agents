import OMAStatements.S_opg_infinite_distributivity_of_meet_over_join_for_a_principal_funcoid

/-!
The diagonal and the family of off-diagonal singleton relations on the natural numbers.
The counterexample appears in Victor Porton's `Algebraic General Topology`,
Proposition 14.12 and Example 14.14:
https://math.portonvictor.org/binaries/volume-1-texmacs.pdf
-/

namespace OMA.FuncoidCounterexample

open OMA.S_opg_infinite_distributivity_of_meet_over_join_for_a_principal_funcoid

private def diagonal : Set (ℕ × ℕ) := {z | z.1 = z.2}

private def point (a b : ℕ) : Funcoid ℕ ℕ := principal {(a, b)}

private def offDiagonalPoints : Set (Funcoid ℕ ℕ) :=
  {g | ∃ a b : ℕ, a ≠ b ∧ g = point a b}

private def infiniteIntersection : Funcoid ℕ ℕ where
  rel X Y := (X ∩ Y).Infinite
  empty_left Y := by simp
  empty_right X := by simp
  union_left I J Y := by rw [Set.union_inter_distrib_right, Set.infinite_union]
  union_right X I J := by rw [Set.inter_union_distrib_left, Set.infinite_union]

private theorem point_rel {a b : ℕ} {X Y : Set ℕ} :
    (point a b).rel X Y ↔ a ∈ X ∧ b ∈ Y := by
  change (X ×ˢ Y ∩ {(a, b)}).Nonempty ↔ _
  constructor
  · rintro ⟨z, hz, hz'⟩
    have e : z = (a, b) := Set.mem_singleton_iff.mp hz'
    subst z
    exact hz
  · intro h
    exact ⟨(a,b), h, Set.mem_singleton _⟩

private theorem inf_le_diagonal : infiniteIntersection.le (principal diagonal) := by
  intro X Y h
  obtain ⟨x, hx⟩ := Set.Infinite.nonempty h
  exact ⟨(x,x), hx, rfl⟩

private theorem inf_le_join : infiniteIntersection.le (sup offDiagonalPoints) := by
  intro X Y h
  have hinf : (X ∩ Y).Infinite := h
  obtain ⟨x, hx⟩ := hinf.nonempty
  have hy : ∃ y ∈ X ∩ Y, y ≠ x := by
    by_contra! hall
    exact hinf ((Set.finite_singleton x).subset (fun z hz => Set.mem_singleton_iff.mpr (hall z hz)))
  obtain ⟨y, hy, hyx⟩ := hy
  exact ⟨point x y, ⟨x,y,hyx.symm,rfl⟩, point_rel.mpr ⟨hx.1, hy.2⟩⟩

private theorem split_singleton {a : ℕ} {X : Set ℕ} (ha : a ∈ X) :
    ({a} : Set ℕ) ∪ (X \ {a}) = X := by
  ext x
  by_cases h : x = a
  · subst x
    simp [ha]
  · simp [h]

private theorem no_lower_rectangle {a b : ℕ} (hab : a ≠ b) {g : Funcoid ℕ ℕ}
    (hd : g.le (principal diagonal)) (hp : g.le (point a b)) :
    ∀ X Y, ¬ g.rel X Y := by
  intro X Y hg
  obtain ⟨ha, hb⟩ := point_rel.mp (hp X Y hg)
  have h₁ : g.rel {a} Y := by
    have hu : g.rel ({a} ∪ (X \ {a})) Y := (split_singleton ha).symm ▸ hg
    rcases (g.union_left {a} (X \ {a}) Y).mp hu with hs | hs
    · exact hs
    · have hm := (point_rel.mp (hp _ _ hs)).1
      exact (hm.2 (Set.mem_singleton a)).elim
  have h₂ : g.rel {a} {b} := by
    have hu : g.rel {a} ({b} ∪ (Y \ {b})) := (split_singleton hb).symm ▸ h₁
    rcases (g.union_right {a} {b} (Y \ {b})).mp hu with hs | hs
    · exact hs
    · have hm := (point_rel.mp (hp _ _ hs)).2
      exact (hm.2 (Set.mem_singleton b)).elim
  obtain ⟨⟨x,y⟩, hp', he⟩ := hd {a} {b} h₂
  have hx : x = a := Set.mem_singleton_iff.mp hp'.1
  have hy : y = b := Set.mem_singleton_iff.mp hp'.2
  exact hab (hx.symm.trans (he.trans hy))

theorem refute : ¬ (type_of% @OMA.S_opg_infinite_distributivity_of_meet_over_join_for_a_principal_funcoid.main) := by
  intro h
  have hm : (meet (principal diagonal) (sup offDiagonalPoints)).rel Set.univ Set.univ :=
    ⟨infiniteIntersection, ⟨inf_le_diagonal, inf_le_join⟩, by
      change ((Set.univ : Set ℕ) ∩ Set.univ).Infinite
      simpa using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)⟩
  rw [h ℕ ℕ diagonal offDiagonalPoints] at hm
  obtain ⟨_, ⟨p, hp, rfl⟩, hm⟩ := hm
  obtain ⟨a, b, hab, rfl⟩ := hp
  obtain ⟨g, ⟨hgD, hgP⟩, hg⟩ := hm
  exact no_lower_rectangle hab hgD hgP _ _ hg

end OMA.FuncoidCounterexample

theorem OMA.disproof :
    ¬ (type_of% @OMA.S_opg_infinite_distributivity_of_meet_over_join_for_a_principal_funcoid.main) :=
  OMA.FuncoidCounterexample.refute
