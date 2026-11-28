import OMAStatements.S_oeis_a054390
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Weight-preserving bijection by @wtho704, pinned commit
1c01ffbf471b1aef4bd8c9e2fedce9f9d17091bd (linked from PR21186).
Original port by @rodolfoquint (#28309).

The binary digits of a multiplicity in {0,1,2,3} select the parts w and 2w.
For the powers of 3 the resulting parts are pairwise distinct.

Sources: https://oeis.org/A054390 and https://oeis.org/A038754
-/

open OMA.S_oeis_a054390

private def membershipEquiv {α : Type*} [Fintype α] [DecidableEq α] :
    Finset α ≃ (α → Bool) where
  toFun s i := decide (i ∈ s)
  invFun b := Finset.univ.filter fun i => b i
  left_inv s := by ext i; simp
  right_inv b := by funext i; simp

private def binaryDigit : (Bool → Bool) ≃ Fin 4 :=
  (Equiv.boolArrowEquivProd Bool).trans <| (Equiv.prodComm Bool Bool).trans <|
    (finTwoEquiv.symm.prodCongr finTwoEquiv.symm).trans finProdFinEquiv

private def selectionEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Finset (ι × Bool) ≃ (ι → Fin 4) :=
  membershipEquiv.trans <| (Equiv.curry ι Bool Bool).trans <|
    Equiv.piCongrRight fun _ => binaryDigit

private theorem selection_preserves {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℕ) (s : Finset (ι × Bool)) :
    distinctWeight w s = boundedWeight w (selectionEquiv s) := by
  unfold distinctWeight boundedWeight
  have sum_slots (f : ι × Bool → ℕ) :
      ∑ p ∈ s, f p = ∑ p : ι × Bool, if p ∈ s then f p else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [sum_slots, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  change _ = ((finTwoEquiv.symm (decide ((i, false) ∈ s)) : ℕ) +
    2 * (finTwoEquiv.symm (decide ((i, true) ∈ s)) : ℕ)) * w i
  by_cases h₁ : (i, false) ∈ s <;> by_cases h₂ : (i, true) ∈ s <;>
    simp [finTwoEquiv, h₁, h₂]
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a054390.main := by
  intro n
  refine Fintype.card_congr (selectionEquiv.subtypeEquiv ?_).symm
  intro s
  rw [selection_preserves]
