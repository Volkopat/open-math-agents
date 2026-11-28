import OMAStatements.S_mo_309137
import Mathlib

open Finset

open OMA.S_mo_309137

private theorem mem_private {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (x z : V) : z ∈ privateNeighbors G S x ↔
      z ∉ S ∧ G.Adj z x ∧ ∀ y ∈ S, G.Adj z y → y = x := by
  classical
  simp [privateNeighbors]

private def pairedCliques (m : ℕ) : SimpleGraph (Bool × Fin m) where
  Adj x y := x ≠ y ∧ (x.1 = y.1 ∨ x.2 = y.2)
  symm := by
    constructor
    intro _ _ h
    exact ⟨h.1.symm,h.2.elim (fun he => Or.inl he.symm) (fun he => Or.inr he.symm)⟩
  loopless := by
    constructor
    intro _ h
    exact h.1 rfl

private theorem paired_connected {m : ℕ} (hm : 0 < m) : (pairedCliques m).Connected := by
  have hPre : (pairedCliques m).Preconnected := by
    intro x y
    by_cases hxy : x = y
    · subst y
      exact SimpleGraph.Reachable.refl _
    · by_cases hLeft : x.1 = y.1
      · exact SimpleGraph.Adj.reachable ⟨hxy,Or.inl hLeft⟩
      · by_cases hRight : x.2 = y.2
        · exact SimpleGraph.Adj.reachable ⟨hxy,Or.inr hRight⟩
        · let z := (x.1,y.2)
          have hxz : (pairedCliques m).Adj x z := by
            refine ⟨?_,Or.inl rfl⟩
            intro h
            have he : x.2 = z.2 := congrArg Prod.snd h
            exact hRight he
          have hzy : (pairedCliques m).Adj z y := by
            refine ⟨?_,Or.inr rfl⟩
            intro h
            have he : z.1 = y.1 := congrArg Prod.fst h
            exact hLeft he
          exact hxz.reachable.trans hzy.reachable
  let _ : Nonempty (Bool × Fin m) := ⟨(false,⟨0,hm⟩)⟩
  exact ⟨hPre⟩

private theorem paired_vees {m : ℕ} (hm : 2 ≤ m) : AllEdgesInVees (pairedCliques m) := by
  intro x y h
  rcases h.2 with he | he
  · let z := (!x.1,x.2)
    have hNe : x.1 ≠ !x.1 := by cases x.1 <;> decide
    refine ⟨z,Or.inl ⟨⟨fun hh => hNe (congrArg Prod.fst hh),Or.inr rfl⟩,?_⟩⟩
    intro hyz
    exact hyz.2.elim (fun hh => hNe (he.trans hh))
      (fun hh => h.1 (Prod.ext he hh.symm))
  · let i : Fin m := ⟨0,by omega⟩
    let j : Fin m := ⟨1,by omega⟩
    let k := if x.2 = i then j else i
    have hk : x.2 ≠ k := by
      by_cases hxi : x.2 = i
      · simp [k,hxi]
        intro heq
        have h := congrArg Fin.val heq
        contradiction
      · simp [k,hxi]
    let z := (x.1,k)
    refine ⟨z,Or.inl ⟨⟨fun hh => hk (congrArg Prod.snd hh),Or.inl rfl⟩,?_⟩⟩
    intro hyz
    exact hyz.2.elim (fun hh => h.1 (Prod.ext hh.symm he)) (fun hh => hk (he.trans hh))

private theorem large_private_neighborhood {m : ℕ} {S : Finset (Bool × Fin m)}
    (hC : 2 ≤ S.card) (hInd : Independent (pairedCliques m) S) :
    ∃ a ∈ S, m - 2 ≤ (privateNeighbors (pairedCliques m) S a).card := by
  classical
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (by omega : 1 < S.card)
  have hSide : a.1 ≠ b.1 := fun h => hInd a ha b hb ⟨hab,Or.inl h⟩
  have hIndex : a.2 ≠ b.2 := fun h => hInd a ha b hb ⟨hab,Or.inr h⟩
  have hCases : ∀ x ∈ S, x = a ∨ x = b := by
    intro x hx
    have hColor : x.1 = a.1 ∨ x.1 = b.1 := by
      revert hSide
      cases a.1 <;> cases b.1 <;> cases x.1 <;> simp
    rcases hColor with h | h
    · exact Or.inl (by by_contra hne; exact hInd x hx a ha ⟨hne,Or.inl h⟩)
    · exact Or.inr (by by_contra hne; exact hInd x hx b hb ⟨hne,Or.inl h⟩)
  let positions := ((univ : Finset (Fin m)).erase a.2).erase b.2
  have hsize : positions.card = m - 2 := by
    have hx : b.2 ∈ (univ : Finset (Fin m)).erase a.2 := mem_erase.mpr ⟨hIndex.symm,mem_univ _⟩
    rw [show positions = ((univ : Finset (Fin m)).erase a.2).erase b.2 by rfl,
      card_erase_of_mem hx,card_erase_of_mem (mem_univ a.2),card_univ,Fintype.card_fin]
    omega
  refine ⟨a,ha,?_⟩
  rw [←hsize]
  apply Finset.card_le_card_of_injOn (fun j => (a.1,j))
  · intro j hj
    have hbj : j ≠ b.2 := (mem_erase.mp hj).1
    have haj : j ≠ a.2 := (mem_erase.mp (mem_erase.mp hj).2).1
    apply (mem_private _ _ _ _).mpr
    refine ⟨?_, ⟨fun h => haj (congrArg Prod.snd h),Or.inl rfl⟩, ?_⟩
    · intro hh
      exact (hCases _ hh).elim (fun he => haj (congrArg Prod.snd he))
        (fun he => hSide (show (a.1,j).1 = b.1 from congrArg Prod.fst he))
    · intro x hx he
      rcases hCases x hx with h | h
      · exact h
      · subst x
        exact (he.2.elim hSide hbj).elim
  · intro j _ k _ he
    exact congrArg Prod.snd he

theorem OMA.solution : type_of% @OMA.S_mo_309137.main := by
  intro n _
  let m := n + 3
  have h₀ : 0 < m := by omega
  have h₁ : 1 < m := by omega
  let a : Bool × Fin m := (false,⟨0,h₀⟩)
  let b : Bool × Fin m := (true,⟨1,h₁⟩)
  have hLeft : a.1 ≠ b.1 := Bool.noConfusion
  have hRight : a.2 ≠ b.2 := by
    intro h
    have he : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hne : a ≠ b := fun h => hLeft (congrArg Prod.fst h)
  have hab : ¬ (pairedCliques m).Adj a b := fun h => h.2.elim hLeft hRight
  refine ⟨Bool × Fin m,inferInstance,pairedCliques m,paired_connected h₀,paired_vees (by omega),?_,?_⟩
  · refine ⟨{a,b},by simp [card_insert_of_notMem,hne],?_⟩
    intro x hx y hy
    simp only [mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact fun h => h.1 rfl
    · exact hab
    · exact fun h => hab h.symm
    · exact fun h => h.1 rfl
  · intro S hc hind
    obtain ⟨a,ha,hpriv⟩ := large_private_neighborhood hc hind
    exact ⟨a,ha,by omega⟩
