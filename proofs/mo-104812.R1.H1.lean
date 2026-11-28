import OMAReductions.R_mo_104812_R1
import Mathlib

/- Compact case of MathOverflow 104812. We use the gluing argument from
reduction #19521 and Mathlib's classification of maximal ideals (Jireh Loreaux).
Passing to the Hausdorff quotient preserves the ring of real functions.
Credit: @my-other-github-account (Hermes, GPT-6.2 Astra). -/
open ContinuousMap OMA.S_mo_104812
namespace MO104812Compact
variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
private abbrev vanish (A : Set X) := idealOfSet ℝ Aᶜ
private theorem memvan (A : Set X) (f : C(X, ℝ)) : f ∈ vanish A ↔ ∀ x ∈ A, f x = 0 := by
  simp [vanish, mem_idealOfSet]
private theorem strong (A : Set X) : IsInfOfMaximal (vanish A) := by
  let pt := fun x : X => idealOfSet ℝ ({x}ᶜ : Set X)
  refine ⟨pt '' A, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact idealOf_compl_singleton_isMaximal ℝ x
  · ext f; simp [memvan, Submodule.mem_sInf, pt]
private theorem reprI (I : Ideal C(X, ℝ)) (h : IsInfOfMaximal I) :
    ∃ A : Set X, IsClosed A ∧ I = vanish A := by
  refine ⟨(setOfIdeal I)ᶜ, (setOfIdeal_open I).isClosed_compl, ?_⟩
  obtain ⟨S, hm, rfl⟩ := h
  have hc : IsClosed ((sInf S : Ideal C(X, ℝ)) : Set C(X, ℝ)) := by
    change IsClosed {f | f ∈ sInf S}
    simp only [Submodule.mem_sInf, Set.ofPred_forall]
    exact isClosed_iInter fun M => isClosed_iInter fun hM => by
      have := hm M hM
      exact (inferInstance : IsClosed (M : Set C(X, ℝ)))
  simpa [vanish] using (idealOfSet_ofIdeal_isClosed hc).symm
private theorem glue (A B : Set X) (ha : IsClosed A) (hb : IsClosed B) :
    vanish A ⊔ vanish B = vanish (A ∩ B) := by
  classical
  apply le_antisymm
  · exact sup_le (fun f hf => (memvan _ _).2 fun x hx => (memvan _ _).1 hf x hx.1)
      (fun f hf => (memvan _ _).2 fun x hx => (memvan _ _).1 hf x hx.2)
  intro f hf
  let g : X → ℝ := fun x => if x ∈ A then 0 else f x
  have ga : Set.EqOn g 0 A := fun x hx => if_pos hx
  have gb : Set.EqOn g f B := by
    intro x hx; by_cases h : x ∈ A
    · simp [g, h, (memvan _ _).1 hf x ⟨h, hx⟩]
    · simp [g, h]
  have hg : ContinuousOn g (A ∪ B) :=
    (continuousOn_const.congr ga).union_of_isClosed (f.continuous.continuousOn.congr gb) ha hb
  obtain ⟨u, hu⟩ := ContinuousMap.exists_restrict_eq (ha.union hb) (⟨_, continuousOn_iff_continuous_domRestrict.mp hg⟩ : C(↥(A ∪ B), ℝ))
  have he x (hx : x ∈ A ∪ B) : u x = g x := DFunLike.congr_fun hu ⟨x, hx⟩
  exact Submodule.mem_sup.2 ⟨u, (memvan _ _).2 (fun x hx => (he x (Or.inl hx)).trans (ga hx)),
    f-u, (memvan _ _).2 (fun x hx => sub_eq_zero.mpr ((he x (Or.inr hx)).trans (gb hx)).symm), by abel⟩
private theorem haus (I J : Ideal C(X, ℝ)) (hi : IsInfOfMaximal I) (hj : IsInfOfMaximal J) : IsInfOfMaximal (I ⊔ J) := by
  obtain ⟨A, ha, rfl⟩ := reprI I hi
  obtain ⟨B, hb, rfl⟩ := reprI J hj
  rw [glue A B ha hb]; exact strong _
private theorem transport {R S : Type*} [CommRing R] [CommRing S] (e : Ideal R ≃o Ideal S) {I : Ideal R} (h : IsInfOfMaximal I) : IsInfOfMaximal (e I) := by
  obtain ⟨T, ht, rfl⟩ := h
  refine ⟨e '' T, ?_, by rw [e.map_sInf, sInf_image]⟩
  rintro _ ⟨M, hm, rfl⟩
  exact Ideal.isMaximal_def.mpr ((e.isCoatom_iff M).mpr (Ideal.isMaximal_def.mp (ht M hm)))
end MO104812Compact
open MO104812Compact

theorem OMA.solution : OMA.R_mo_104812_R1.H1 := by
  intro X _ _ I J hi hj
  let q : C(X, T2Quotient X) := ⟨_, T2Quotient.continuous_mk X⟩
  let r : C(T2Quotient X, ℝ) →+* C(X, ℝ) :=
    { toFun := fun f => f.comp q, map_zero' := rfl, map_one' := rfl,
      map_add' := fun _ _ => rfl, map_mul' := fun _ _ => rfl }
  have bij : Function.Bijective r := by
    constructor
    · intro f g h; ext y; obtain ⟨x, rfl⟩ := T2Quotient.surjective_mk X y; exact DFunLike.congr_fun h x
    · intro f; exact ⟨⟨_, T2Quotient.continuous_lift f.continuous⟩, by ext; rfl⟩
  let e := Ideal.relIsoOfBijective r bij
  letI : CompactSpace (T2Quotient X) := Function.Surjective.compactSpace (T2Quotient.continuous_mk X) (T2Quotient.surjective_mk X)
  simpa using transport e.symm (haus (e I) (e J) (transport e hi) (transport e hj))
