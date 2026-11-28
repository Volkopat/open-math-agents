import OMAStatements.S_opg_another_conjecture_about_reloids_and_funcoids

-- Credit: @YlliBala
open Filter Set OMA.S_opg_another_conjecture_about_reloids_and_funcoids

namespace PortonRectangleAudit

private theorem primeMono {A : Type} {P : Set A → Prop}
    (hu : ∀ S T, P (S ∪ T) ↔ P S ∨ P T) {S T : Set A} (hst : S ⊆ T) : P S → P T := by
  intro hs
  simpa only [union_eq_right.mpr hst] using (hu S T).2 (Or.inl hs)

-- Choose a refinement containing X and avoiding every P-negative set.
private theorem choosePositive {A : Type} (P : Set A → Prop) (h0 : ¬ P ∅)
    (hu : ∀ S T, P (S ∪ T) ↔ P S ∨ P T) {X : Set A} (hX : P X) :
    ∃ a : Ultrafilter A, X ∈ a ∧ ∀ S ∈ a, P S := by
  classical
  let f : Filter A := comk (fun S => ¬ P (X ∩ S)) (by simpa using h0)
    (fun _ hn _ hsub hp => hn (primeMono hu (inter_subset_inter_right X hsub) hp))
    (by intro S hS T hT; rw [inter_union_distrib_left, hu]; exact not_or_intro hS hT)
  have : NeBot f := Filter.neBot_iff.mpr (by
    rw [Ne, ← empty_mem_iff_bot]
    change ¬ ¬ P (X ∩ (∅ : Set A)ᶜ)
    simpa using hX)
  refine ⟨Ultrafilter.of f, Ultrafilter.of_le f ?_, ?_⟩
  · change ¬ P (X ∩ Xᶜ)
    simpa using h0
  · intro S hS
    by_contra hn
    have hc : Sᶜ ∈ f := by
      change ¬ P (X ∩ Sᶜᶜ)
      simpa using (fun hp => hn (primeMono hu (inter_subset_right : X ∩ S ⊆ S) hp))
    exact (Ultrafilter.compl_mem_iff_notMem.mp (Ultrafilter.of_le f hc)) hS

private theorem compatiblePair {A B : Type} {δ : Set A → Set B → Prop} (hδ : IsFuncoid δ)
    {X : Set A} {Y : Set B} (hXY : δ X Y) :
    ∃ (a : Ultrafilter A) (b : Ultrafilter B), X ∈ a ∧ Y ∈ b ∧
      ∀ S ∈ a, ∀ T ∈ b, δ S T := by
  classical
  rcases hδ with ⟨heL, heR, huL, huR⟩
  obtain ⟨a, hXa, ha⟩ := choosePositive (fun S => δ S Y) (heL Y) (fun S T => huL S T Y) hXY
  let Q := fun T => ∀ S ∈ a, δ S T
  have h0 : ¬ Q ∅ := fun h => heR univ (h univ univ_mem)
  have hu (I J : Set B) : Q (I ∪ J) ↔ Q I ∨ Q J := by
    constructor
    · intro h
      by_contra! bad
      obtain ⟨nI, nJ⟩ := bad
      change ¬ (∀ S ∈ a, δ S I) at nI
      change ¬ (∀ S ∈ a, δ S J) at nJ
      push Not at nI nJ
      obtain ⟨S, hS, hSI⟩ := nI
      obtain ⟨T, hT, hTJ⟩ := nJ
      rcases (huR _ I J).mp (h (S ∩ T) (inter_mem hS hT)) with hi | hj
      · exact hSI (primeMono (P := fun K => δ K I) (fun K L => huL K L I) inter_subset_left hi)
      · exact hTJ (primeMono (P := fun K => δ K J) (fun K L => huL K L J) inter_subset_right hj)
    · rintro (hi | hj) S hS
      · exact (huR S I J).2 (Or.inl (hi S hS))
      · exact (huR S I J).2 (Or.inr (hj S hS))
  obtain ⟨b, hYb, hb⟩ := choosePositive Q h0 hu ha
  exact ⟨a, b, hXa, hYb, fun S hS T hT => hb T hT S hS⟩


private theorem gammaDecide {A B : Type} (a : Ultrafilter A) (b : Ultrafilter B)
    {K : Set (A × B)} (hK : IsGamma K) :
    K ∈ (a : Filter A) ×ˢ (b : Filter B) ∨ Kᶜ ∈ (a : Filter A) ×ˢ (b : Filter B) := by
  classical
  let F := (a : Filter A) ×ˢ (b : Filter B)
  have rect (X : Set A) (Y : Set B) : X ×ˢ Y ∈ F ∨ (X ×ˢ Y)ᶜ ∈ F := by
    rcases a.mem_or_compl_mem X with hx | hx
    · rcases b.mem_or_compl_mem Y with hy | hy
      · exact Or.inl (prod_mem_prod hx hy)
      · exact Or.inr (mem_prod_iff.mpr ⟨univ, univ_mem, Yᶜ, hy, fun _ hp h => hp.2 h.2⟩)
    · exact Or.inr (mem_prod_iff.mpr ⟨Xᶜ, hx, univ, univ_mem, fun _ hp h => hp.1 h.1⟩)
  obtain ⟨s, rfl⟩ := hK
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s _ ih =>
    simp only [Finset.set_biUnion_insert]
    rcases ih with hs | hs
    · exact Or.inl (mem_of_superset hs subset_union_right)
    · rcases rect p.1 p.2 with hp | hp
      · exact Or.inl (mem_of_superset hp subset_union_left)
      · exact Or.inr (by rw [compl_union]; exact inter_mem hp hs)


private theorem finiteHit {A B : Type} {δ : Set A → Set B → Prop} (hδ : IsFuncoid δ)
    {K : Set (A × B)} (hg : IsGamma K) :
    (∀ X Y, δ X Y → (X ×ˢ Y ∩ K).Nonempty) ↔ K ∈ rldIn δ := by
  simp only [rldIn, mem_iSup]
  constructor
  · intro hit a b hab
    rcases gammaDecide a b hg with hk | hc
    · exact hk
    · obtain ⟨S, hS, T, hT, hsub⟩ := mem_prod_iff.mp hc
      obtain ⟨p, hp, hpk⟩ := hit S T (hab S hS T hT)
      exact (hsub hp hpk).elim
  · intro inner X Y hxy
    obtain ⟨a, b, hx, hy, hab⟩ := compatiblePair hδ hxy
    have hK : K ∈ (a : Filter A) ×ˢ (b : Filter B) := inner a b hab
    exact Filter.nonempty_of_mem (inter_mem (prod_mem_prod hx hy) hK)

end PortonRectangleAudit

theorem OMA.solution : type_of% @OMA.S_opg_another_conjecture_about_reloids_and_funcoids.main := by
  intro A B δ hδ
  unfold rldGamma box
  apply congrArg Filter.generate
  ext K
  change (IsGamma K ∧ _) ↔ (IsGamma K ∧ _)
  exact and_congr_right (fun hg => PortonRectangleAudit.finiteHit hδ hg)
