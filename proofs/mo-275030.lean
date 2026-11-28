import OMAStatements.S_mo_275030
import Mathlib

-- Retains @AkiRA-COM-FP’s order-embedding constructions from PR #15775.
-- Function.cantor_injective supplies the same powerset obstruction directly.

open Function Set

open OMA.S_mo_275030

private noncomputable def downSetMap (P : Type) [PartialOrder P] : P ↪o (P → ℝ) := by
  classical
  let f (x : P) (a : P) : ℝ := if a ≤ x then 1 else 0
  have hle {a b : P} : f a ≤ f b ↔ a ≤ b := by
    constructor
    · intro h
      by_contra hab
      have h' : f a a ≤ f b a := h a
      norm_num [f, hab] at h'
    · intro h x
      by_cases hx : x ≤ a
      · simp [f,hx,hx.trans h]
      · by_cases hy : x ≤ b <;> norm_num [f,hx,hy]
  exact ⟨⟨f,fun _ _ h => le_antisymm (hle.mp h.le) (hle.mp h.ge)⟩,hle⟩

private structure Blocks where
  entry : Σ n : ℕ, Fin n
  side : Bool

private instance blockOrder : PartialOrder Blocks where
  le a b := a = b ∨ (a.1.1 = b.1.1 ∧ a.2 = false ∧ b.2 = true ∧ a.1 ≠ b.1)
  le_refl a := Or.inl rfl
  le_trans := by
    intro a b c hab hbc
    rcases hab with rfl | hab
    · exact hbc
    · rcases hbc with rfl | hbc
      · exact Or.inr hab
      · have h : true = false := hab.2.2.1.symm.trans hbc.2.1
        cases h
  le_antisymm := by
    intro a b hab hba
    rcases hab with hab | hab
    · exact hab
    · rcases hba with hba | hba
      · exact hba.symm
      · have h : true = false := hab.2.2.1.symm.trans hba.2.1
        cases h

private def lower {n : ℕ} (i : Fin n) : Blocks := ⟨⟨n,i⟩,false⟩
private def upper {n : ℕ} (i : Fin n) : Blocks := ⟨⟨n,i⟩,true⟩

private theorem lower_upper_iff {n : ℕ} (i j : Fin n) : lower i ≤ upper j ↔ i ≠ j := by
  change lower i = upper j ∨ (n = n ∧ false = false ∧ true = true ∧
    (⟨n,i⟩ : Σ n : ℕ, Fin n) ≠ ⟨n,j⟩) ↔ i ≠ j
  simp [lower,upper,Blocks.mk.injEq]

private theorem same_block {a b : Blocks} (h : a ≤ b) : a.1.1 = b.1.1 :=
  h.elim (congrArg fun k : Blocks => k.1.1) (fun h => h.1)

private theorem finite_block (n : ℕ) : {v : Blocks | v.1.1 = n}.Finite := by
  let f (x : Fin n × Bool) : Blocks := ⟨⟨n,x.1⟩,x.2⟩
  apply (Set.finite_range f).subset
  rintro ⟨⟨m,i⟩,b⟩ hm
  change m = n at hm
  subst m
  exact ⟨(i,b),rfl⟩

private theorem finite_principal : FinitePrincipalNeighborhoods Blocks := by
  intro u
  exact ⟨(finite_block u.1.1).subset (fun _ h => same_block h),
    (finite_block u.1.1).subset (fun _ h => (same_block h).symm)⟩

private theorem cube_dimension_bound (n d : ℕ) (f : Blocks ↪o (Fin d → ℝ)) : n ≤ d := by
  classical
  have hSep (i : Fin n) : ∃ j, f (upper i) j < f (lower i) j := by
    have hn : ¬ f (lower i) ≤ f (upper i) := by
      intro h
      exact ((lower_upper_iff i i).mp (f.le_iff_le.mp h)) rfl
    simpa only [Pi.le_def,not_forall,not_le] using hn
  choose coordinate hcoord using hSep
  have hInj : Injective coordinate := by
    intro i j he
    by_contra hne
    have hij := f.monotone ((lower_upper_iff i j).mpr hne) (coordinate i)
    have hji := f.monotone ((lower_upper_iff j i).mpr (fun h => hne h.symm)) (coordinate i)
    have hi := hcoord i
    have hj := hcoord j
    rw [← he] at hj
    exact (not_lt_of_ge (hij.trans (hj.le.trans hji))) hi
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective coordinate hInj

private abbrev FiniteTuple := Σ d : ℕ, Fin d → ℝ

private structure DiscreteSets where
  carrier : Set FiniteTuple

private instance discreteOrder : PartialOrder DiscreteSets where
  le := Eq
  le_refl := Eq.refl
  le_trans := fun _ _ _ => Eq.trans
  le_antisymm := fun _ _ h _ => h

private theorem discrete_finite_principal : FinitePrincipalNeighborhoods DiscreteSets := by
  intro x
  refine ⟨(finite_singleton x).subset ?_,(finite_singleton x).subset ?_⟩
  · intro y hy
    exact mem_singleton_iff.mpr hy
  · intro y hy
    exact mem_singleton_iff.mpr (show x = y from hy).symm

private theorem no_discrete_injection (d : ℕ) (f : DiscreteSets → Fin d → ℝ) : ¬ Injective f := by
  classical
  intro hf
  let g (A : Set FiniteTuple) : FiniteTuple := ⟨d,f ⟨A⟩⟩
  have hg : Injective g := by
    intro A B h
    have he : f ⟨A⟩ = f ⟨B⟩ := by simpa [g] using h
    exact congrArg DiscreteSets.carrier (hf he)
  exact cantor_injective g hg

private theorem countable_mono_real (P : Type) [PartialOrder P] [Countable P] :
    ∃ f : P → ℝ, Injective f ∧ Monotone f := by
  let _ : Countable (LinearExtension P) := by change Countable P; infer_instance
  obtain ⟨e⟩ := Order.embedding_from_countable_to_dense (α := LinearExtension P) (β := ℝ)
  have hInj : Injective (toLinearExtension : P → LinearExtension P) :=
    fun _ _ h => h
  exact ⟨fun x => e (toLinearExtension x),e.injective.comp hInj,
    e.monotone.comp toLinearExtension.monotone⟩

theorem OMA.solution : type_of% @OMA.S_mo_275030.main := by
  have hInj : Injective (fun v : Blocks => (v.entry,v.side)) := by
    intro a b h
    cases a
    cases b
    cases h
    rfl
  refine ⟨fun P _ => ⟨downSetMap P⟩, fun P _ _ => countable_mono_real P, ?_, ?_⟩
  · refine ⟨Blocks,blockOrder,hInj.countable,finite_principal,?_⟩
    intro d
    constructor
    intro f
    have := cube_dimension_bound (d+1) d f
    omega
  · refine ⟨DiscreteSets,discreteOrder,discrete_finite_principal,?_⟩
    rintro d ⟨f,hf,_⟩
    exact no_discrete_injection d f hf
