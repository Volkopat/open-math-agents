import OMAStatements.S_mo_434476

open CategoryTheory CategoryTheory.Limits

noncomputable section

private def Diamond := Bool × Bool

local instance : CompleteLattice Diamond := inferInstanceAs (CompleteLattice (Bool × Bool))
local instance : DecidableEq Diamond := inferInstanceAs (DecidableEq (Bool × Bool))

private def leftAtom : Diamond := (true, false)
private def rightAtom : Diamond := (false, true)

private def shortArrow : MorphismProperty Diamond :=
  fun X Y _ => X ≠ ⊥ ∨ Y ≠ ⊤

private def joinCocone {X Y Z : Diamond} (f : X ⟶ Y) (g : X ⟶ Z) :
    PushoutCocone f g :=
  PushoutCocone.mk (W := Y ⊔ Z) (homOfLE le_sup_left) (homOfLE le_sup_right)
    (Subsingleton.elim _ _)

private def joinColimit {X Y Z : Diamond} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsColimit (joinCocone f g) :=
  PushoutCocone.IsColimit.mk _
    (fun s => homOfLE (sup_le (leOfHom s.inl) (leOfHom s.inr)))
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_434476.main) := by
  intro h
  let _ {X Y Z : Diamond} {f : X ⟶ Y} {g : X ⟶ Z} : HasColimit (span f g) :=
    ⟨⟨⟨joinCocone f g, joinColimit f g⟩⟩⟩
  let _ : HasPushouts Diamond := hasPushouts_of_hasColimit_span Diamond
  have hid : shortArrow.ContainsIdentities := by
    constructor
    intro X
    change X ≠ ⊥ ∨ X ≠ ⊤
    by_cases hX : X = ⊥
    · exact Or.inr (hX ▸ (by decide : (⊥ : Diamond) ≠ ⊤))
    · exact Or.inl hX
  have hbase : shortArrow.IsStableUnderCobaseChange := by
    constructor
    intro A A' B B' f g f' g' sq hf
    change A ≠ ⊥ ∨ A' ≠ ⊤ at hf
    change B ≠ ⊥ ∨ B' ≠ ⊤
    by_contra! hn
    have hA : A = ⊥ := le_bot_iff.mp (hn.1 ▸ leOfHom g)
    have hAtop : A' = ⊤ := by
      have hd : B' ≤ B ⊔ A' := leOfHom (sq.isColimit.desc (joinCocone g f))
      rw [hn.1, hn.2, bot_sup_eq] at hd
      exact top_le_iff.mp hd
    exact hf.elim (fun hne => hne hA) (fun hne => hne hAtop)
  have hcancel : shortArrow.HasOfPrecompProperty shortArrow := by
    constructor
    intro X Y Z f g _ hfg
    change X ≠ ⊥ ∨ Z ≠ ⊤ at hfg
    change Y ≠ ⊥ ∨ Z ≠ ⊤
    by_contra! hn
    have hx : X = ⊥ := le_bot_iff.mp (hn.1 ▸ leOfHom f)
    exact hfg.elim (fun hne => hne hx) (fun hne => hne hn.2)
  let u : (⊥ : Diamond) ⟶ leftAtom := homOfLE bot_le
  let v : (⊥ : Diamond) ⟶ rightAtom := homOfLE bot_le
  let e : (⊥ : Diamond) ⟶ ⊥ := 𝟙 _
  let τ : span e e ⟶ span u v :=
    { app := fun j => by
        rcases j with _ | ⟨⟨⟩⟩
        · exact e
        · exact u
        · exact v
      naturality := fun _ _ _ => Subsingleton.elim _ _ }
  have hτ : shortArrow.functorCategory WalkingSpan τ := by
    intro j
    rcases j with _ | ⟨⟨⟩⟩ <;> change (⊥ : Diamond) ≠ ⊥ ∨ _ ≠ ⊤
    · exact Or.inr (by decide : (⊥ : Diamond) ≠ ⊤)
    · exact Or.inr (by decide : leftAtom ≠ (⊤ : Diamond))
    · exact Or.inr (by decide : rightAtom ≠ (⊤ : Diamond))
  let φ : (joinCocone e e).pt ⟶ (joinCocone u v).pt := homOfLE (show (⊥ : Diamond) ≤ ⊤ from bot_le)
  have hφ := (h Diamond shortArrow hid hbase hcancel).condition
    _ _ _ _ (joinColimit e e) (joinColimit u v) τ hτ φ (fun _ => Subsingleton.elim _ _)
  change (⊥ : Diamond) ≠ ⊥ ∨ (⊤ : Diamond) ≠ ⊤ at hφ
  exact hφ.elim (fun hne => hne rfl) (fun hne => hne rfl)

end