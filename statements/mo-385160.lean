import Mathlib

/-!
# Doubly stochastic matrices with stochastically ordered rows

Source: user128095, https://mathoverflow.net/questions/385160 (CC BY-SA 4.0).
Credit: @connoranderson. Chris Ramsey and Toni Mhax discuss the connection with
majorization in the source. The initial vector (0,1,…,n−1) is a special case of
the strictly increasing source vector y below.
-/
namespace OMA.S_mo_385160
open Finset Matrix
abbrev V (n : ℕ) := Fin (n+1) → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin (n+1)) (Fin (n+1)) ℝ
def Ordered {n : ℕ} (M : Mat n) : Prop :=
  M ∈ doublyStochastic ℝ (Fin (n+1)) ∧
  ∀ k : Fin (n+1), Monotone fun i => ∑ j ∈ Ici k, M i j

theorem main : ∀ {n : ℕ} (x y : V n) (_ : Monotone x) (_ : StrictMono y),
    ((∑ i,x i) = ∑ i,y i) ∧ (∀ i, (∑ j ∈ Iic i, y j) ≤ ∑ j ∈ Iic i,x j) ↔
    ∃ M : Mat n, Ordered M ∧ M *ᵥ y = x := by
  sorry
end OMA.S_mo_385160
