import OMAReductions.R_Erdos1119_erdos_1119_R1
import Mathlib

-- Step Erdos1119.erdos_1119.R1.H1 (the ZFC-positive easy case)
-- Credit: @arindale; proof ported from Boris Alexeev / Codex / GPT-5.6 Sol's
-- lean-proofs formalization of Erdős Problem 1119 (identity theorem plus cardinality).

open Cardinal Order
open scoped Cardinal

/-- Two distinct entire functions coincide at only countably many points. -/
lemma easy_coincidenceSet_countable {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hfg : f ≠ g) :
    {z : ℂ | f z = g z}.Countable := by
  have hdiff : Differentiable ℂ (fun z => f z - g z) := hf.sub hg
  obtain ⟨x, hx⟩ : ∃ x, f x - g x ≠ 0 := by
    by_contra h
    push Not at h
    apply hfg
    funext z
    exact sub_eq_zero.mp (h z)
  have han : AnalyticOnNhd ℂ (fun z => f z - g z) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2 hdiff
  have hcod :
      (fun z => f z - g z) ⁻¹' ({0} : Set ℂ)ᶜ ∈ Filter.codiscrete ℂ :=
    han.preimage_zero_mem_codiscrete hx
  have hcod' :
      ((fun z => f z - g z) ⁻¹' ({0} : Set ℂ))ᶜ ∈ Filter.codiscrete ℂ := by
    simpa only [Set.preimage_compl] using hcod
  have hdisc : IsDiscrete ((fun z => f z - g z) ⁻¹' ({0} : Set ℂ)) :=
    (compl_mem_codiscrete_iff.mp hcod').2
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  change IsDiscrete {z : ℂ | f z - g z = 0} at hdisc
  simpa only [sub_eq_zero] using hdisc

/-- The cardinal argument: if `succ m < 𝔠` then a family with at most `m` values at
each point has cardinality at most `m`. -/
lemma easy_cardinality_le_of_succ_lt_continuum (m : Cardinal.{0}) (hm : ℵ₀ ≤ m)
    (hsucc : succ m < 𝔠) (F : Set (ℂ → ℂ))
    (hF : ∀ f ∈ F, Differentiable ℂ f)
    (hval : ∀ z : ℂ, #{y : ℂ | ∃ f ∈ F, f z = y} ≤ m) :
    #F ≤ m := by
  by_contra hle
  have hmF : m < #F := lt_of_not_ge hle
  have hsuccF : succ m ≤ #F := Order.succ_le_iff.2 hmF
  obtain ⟨G, hG⟩ := Cardinal.le_mk_iff_exists_set.1 hsuccF
  let funOf : G → ℂ → ℂ := fun g => g.1.1
  let I : Set (G × G) := {p | p.1 ≠ p.2}
  let collision : I → Set ℂ := fun p => {z | funOf p.1.1 z = funOf p.1.2 z}
  let bad : Set ℂ := ⋃ p : I, collision p
  have hinf : ℵ₀ ≤ succ m := hm.trans (lt_succ m).le
  have hI : #I ≤ succ m := by
    calc
      #I ≤ #(G × G) := Cardinal.mk_set_le I
      _ = #G * #G := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
      _ = succ m * succ m := by rw [hG]
      _ = succ m := Cardinal.mul_eq_self hinf
  have hcollision : ∀ p : I, #(collision p) ≤ succ m := by
    intro p
    have hne : funOf p.1.1 ≠ funOf p.1.2 := by
      intro heq
      apply p.2
      apply Subtype.ext
      apply Subtype.ext
      exact heq
    have hc : (collision p).Countable := by
      apply easy_coincidenceSet_countable
      · exact hF _ p.1.1.1.2
      · exact hF _ p.1.2.1.2
      · exact hne
    exact hc.le_aleph0.trans hinf
  have hsup : (⨆ p : I, #(collision p)) ≤ succ m :=
    ciSup_le' hcollision
  have hbad : #bad ≤ succ m := by
    calc
      #bad ≤ #I * ⨆ p : I, #(collision p) := Cardinal.mk_iUnion_le collision
      _ ≤ succ m := Cardinal.mul_le_of_le hinf hI hsup
  have hbad_lt : #bad < #ℂ := by
    rw [Cardinal.mk_complex]
    exact hbad.trans_lt hsucc
  obtain ⟨z, hz⟩ := Cardinal.compl_nonempty_of_mk_lt_mk hbad_lt
  let V : Set ℂ := {y | ∃ f ∈ F, f z = y}
  let ev : G → V := fun g => ⟨funOf g z, g.1.1, g.1.2, rfl⟩
  have hev : Function.Injective ev := by
    intro a b hab
    by_contra hne
    let p : I := ⟨(a, b), hne⟩
    have habv : funOf a z = funOf b z := congrArg Subtype.val hab
    have hzcollision : z ∈ collision p := by
      exact habv
    have hzbad : z ∈ bad := Set.mem_iUnion.2 ⟨p, hzcollision⟩
    exact hz hzbad
  have hGV : #G ≤ #V := Cardinal.mk_le_of_injective hev
  have hcontra : succ m ≤ m := by
    calc
      succ m = #G := hG.symm
      _ ≤ #V := hGV
      _ ≤ m := by simpa only [V] using hval z
  exact (lt_succ m).2 hcontra

theorem OMA.solution : OMA.R_Erdos1119_erdos_1119_R1.H1 := by
  intro m hm hsucc F hF hval
  exact easy_cardinality_le_of_succ_lt_continuum m hm.le hsucc F hF hval
