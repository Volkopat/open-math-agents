import FormalConjectures.ErdosProblems.«509»

open Polynomial

namespace OMA.R_Erdos509_erdos_509_R1

def H1 : Prop :=
  ∀ f : ℂ[X], f.Monic → f.natDegree ≠ 0 →
    IsConnected {z : ℂ | ‖f.eval z‖ ≤ 1} → (∃ ι : Type, Nonempty (Erdos509.BoundedDiscCover {z : ℂ | ‖f.eval z‖ ≤ 1} 2 ι))

def H2 : Prop :=
  ∀ f : ℂ[X], f.Monic → f.natDegree ≠ 0 → (∀ a ∈ f.roots, ‖a - f.roots.sum / (f.natDegree : ℂ)‖ ≤ Real.sqrt 3) → (∃ ι : Type, Nonempty (Erdos509.BoundedDiscCover {z : ℂ | ‖f.eval z‖ ≤ 1} 2 ι))

def H3 : Prop :=
  ∀ f : ℂ[X], f.Monic → f.natDegree ≠ 0 → (∃ g h : ℂ[X], g.Monic ∧ h.Monic ∧
    0 < g.natDegree ∧ g.natDegree < f.natDegree ∧
    0 < h.natDegree ∧ h.natDegree < f.natDegree ∧ f = g * h ∧
    ∀ a ∈ g.roots, ∀ b ∈ h.roots, (5 : ℝ) / 2 ≤ ‖a - b‖) →
    (∀ g : ℂ[X], g.Monic → g.natDegree ≠ 0 → g.natDegree < f.natDegree →
      (∃ ι : Type, Nonempty (Erdos509.BoundedDiscCover {z : ℂ | ‖g.eval z‖ ≤ 1} 2 ι))) → (∃ ι : Type, Nonempty (Erdos509.BoundedDiscCover {z : ℂ | ‖f.eval z‖ ≤ 1} 2 ι))

def H4 : Prop :=
  ∀ f : ℂ[X], f.Monic → f.natDegree ≠ 0 →
    ¬ IsConnected {z : ℂ | ‖f.eval z‖ ≤ 1} → ¬ (∀ a ∈ f.roots, ‖a - f.roots.sum / (f.natDegree : ℂ)‖ ≤ Real.sqrt 3) → ¬ (∃ g h : ℂ[X], g.Monic ∧ h.Monic ∧
    0 < g.natDegree ∧ g.natDegree < f.natDegree ∧
    0 < h.natDegree ∧ h.natDegree < f.natDegree ∧ f = g * h ∧
    ∀ a ∈ g.roots, ∀ b ∈ h.roots, (5 : ℝ) / 2 ≤ ‖a - b‖) → (∃ ι : Type, Nonempty (Erdos509.BoundedDiscCover {z : ℂ | ‖f.eval z‖ ≤ 1} 2 ι))

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos509.erdos_509 := by
  intro h1 h2 h3 h4
  classical
  have go : ∀ n : ℕ, ∀ f : ℂ[X], f.natDegree = n →
      f.Monic → f.natDegree ≠ 0 → (∃ ι : Type, Nonempty (Erdos509.BoundedDiscCover {z : ℂ | ‖f.eval z‖ ≤ 1} 2 ι)) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro f hdegree hmonic hnonzero
      by_cases hc : IsConnected {z : ℂ | ‖f.eval z‖ ≤ 1}
      · exact h1 f hmonic hnonzero hc
      by_cases ht : (∀ a ∈ f.roots, ‖a - f.roots.sum / (f.natDegree : ℂ)‖ ≤ Real.sqrt 3)
      · exact h2 f hmonic hnonzero ht
      by_cases hs : (∃ g h : ℂ[X], g.Monic ∧ h.Monic ∧
      0 < g.natDegree ∧ g.natDegree < f.natDegree ∧
      0 < h.natDegree ∧ h.natDegree < f.natDegree ∧ f = g * h ∧
      ∀ a ∈ g.roots, ∀ b ∈ h.roots, (5 : ℝ) / 2 ≤ ‖a - b‖)
      · apply h3 f hmonic hnonzero hs
        intro g hgmonic hgnonzero hlt
        exact ih g.natDegree (by simpa only [← hdegree] using hlt) g rfl hgmonic hgnonzero
      exact h4 f hmonic hnonzero hc ht hs
  intro f hmonic hnonzero
  exact go f.natDegree f rfl hmonic hnonzero

end OMA.R_Erdos509_erdos_509_R1
