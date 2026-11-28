import OMAStatements.S_mo_472264
import Mathlib

open Module

universe u v

private theorem dimensionContradiction
    (h : type_of% @OMA.S_mo_472264.main.{u, v})
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (hr : finrank K L = 2) : False := by
  let _ : Module.Finite K L := Module.finite_of_finrank_pos (show 0 < finrank K L by omega)
  have hp : Nat.Prime (finrank K L) := hr.symm ▸ Nat.prime_two
  let _ := IntermediateField.isSimpleOrder_of_finrank_prime K L hp
  have ht : finrank K (⊤ : Submodule K L) = 2 := by rw [finrank_top, hr]
  have hpos : 0 < finrank K (⊤ : Submodule K L) := by omega
  have hfinite : Module.Finite K (⊤ : Submodule K L) := Module.finite_of_finrank_pos hpos
  have specialized := @h K L ‹Field K› ‹Field L› ‹Algebra K L›
  have onTop := @specialized (⊤ : Submodule K L) (⊤ : Submodule K L)
  have onFinite := @onTop hfinite hfinite
  have positive := onFinite hpos hpos
  have hbound := positive (by
    intro a b M hbot htop _
    exact (eq_bot_or_eq_top M).elim (fun e => (hbot e).elim) (fun e => (htop e).elim))
  have hdim : finrank K ((⊤ : Submodule K L) * ⊤ : Submodule K L) ≤ 2 := by
    exact (Submodule.finrank_le ((⊤ : Submodule K L) * ⊤)).trans_eq hr
  omega

private theorem quadraticCounterexample (h : type_of% @OMA.S_mo_472264.main.{u, v}) : False := by
  let K := ULift.{u} ℝ
  let L := ULift.{v} ℂ
  let _ : Algebra K L := (RingHom.ulift.{u, v} (algebraMap ℝ ℂ)).toAlgebra
  apply dimensionContradiction h K L
  rw [← Complex.finrank_real_complex]
  exact Algebra.finrank_eq_of_equiv_equiv ULift.ringEquiv ULift.ringEquiv rfl

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_472264.main) :=
  quadraticCounterexample