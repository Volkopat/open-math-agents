import Mathlib

/-!
# Dependence between comparisons to the maximum of row minima

The proposed negative correlation fails for fair independent bits and for an
array of independent continuous uniform entries. The finite example also
allows a separate independent threshold conditioned to equal the statistic.
The uniform example gives the two marginal probabilities and their joint
probability in a four-row, two-column array.

Source: David Smith, https://mathoverflow.net/questions/409243 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)
-/
namespace OMA.S_mo_409243
open MeasureTheory Set
abbrev Bits := Fin 2 → Fin 2 → Bool
def binaryHeight (a : Bits) : Bool := (a 0 0 && a 0 1) || (a 1 0 && a 1 1)
def binaryGood (i : Fin 2) (a : Bits) : Prop := a i 0 ≤ binaryHeight a
instance (i : Fin 2) (a : Bits) : Decidable (binaryGood i a) := by unfold binaryGood; infer_instance
def fair {α : Type*} [Fintype α] (S : Finset α) : ℚ := (S.card:ℚ)/Fintype.card α
/-- The first pair is the first column of the two distinguished rows, the
second pair is their second column, and the remaining s pairs are whole rows. -/
abbrev Sample (s : ℕ) := (ℝ × ℝ) × ((ℝ × ℝ) × (Fin s → ℝ × ℝ))
noncomputable def U : Measure ℝ := volume.restrict (Ioo 0 1)
noncomputable def law (s : ℕ) : Measure (Sample s) :=
  (U.prod U).prod ((U.prod U).prod (Measure.pi fun _ : Fin s => U.prod U))
def miss {s : ℕ} (x : Sample s) (t : ℝ) : Prop :=
  min x.1.1 x.2.1.1 < t ∧ min x.1.2 x.2.1.2 < t ∧ ∀ i,min (x.2.2 i).1 (x.2.2 i).2 < t
def leftEvent (s : ℕ) : Set (Sample s) := {x | ¬ miss x x.1.1}
def rightEvent (s : ℕ) : Set (Sample s) := {x | ¬ miss x x.1.2}

theorem main :
    (let A := Finset.univ.filter (binaryGood 0)
     let B := Finset.univ.filter (binaryGood 1)
     fair A=13/16 ∧ fair B=13/16 ∧ fair (A∩B)=11/16 ∧ fair A*fair B < fair (A∩B)) ∧
    (let E := (Finset.univ : Finset (Bits × Bool)).filter (fun p => p.2=binaryHeight p.1)
     let A := E.filter (fun p => p.1 0 0 ≤ p.2)
     let B := E.filter (fun p => p.1 1 0 ≤ p.2)
     fair E=1/2 ∧ (fair A/fair E)*(fair B/fair E) < fair (A∩B)/fair E) ∧
    (∀ s, (law s).real (leftEvent s)ᶜ = ∫ x in (0:ℝ)..1, x*(1-(1-x)^2)^(s+1)) ∧
    (∀ s, (law s).real ((leftEvent s)ᶜ ∩ (rightEvent s)ᶜ) =
      2*∫ x in (0:ℝ)..1,(1-x)*x^2*(1-(1-x)^2)^s) ∧
    (let μ := law 2
     let A := leftEvent 2
     let B := rightEvent 2
     μ.real A=187/280 ∧ μ.real B=187/280 ∧ μ.real (A∩B)=47/105 ∧
       μ.real A*μ.real B < μ.real (A∩B)) := by
  sorry
end OMA.S_mo_409243
