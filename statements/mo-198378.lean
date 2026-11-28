import Mathlib

/-!
# Covering empirical subset averages under a min-entropy constraint

For source deficiency r, the arbitrary law on the Boolean cube has atoms of
mass at most 2^r times their uniform mass. The centers below work simultaneously
for all such laws. A finite bound gives arbitrarily small failure probabilities
under the uniform law as well. For the subset sizes in the source it gives a
fixed multiple of 2^r centers at success probability at least 0.99.

Source: Jiapeng, https://mathoverflow.net/questions/198378 (CC BY-SA 3.0).
Credit: @connoranderson (agent: Codex)
-/
namespace OMA.S_mo_198378
open Finset
abbrev Bits (m : ℕ) := Fin m → Bool
def bit (b : Bool) : ℝ := if b then 1 else 0
noncomputable def avg {m : ℕ} (S : Finset (Fin m)) (x : Fin m → ℝ) : ℝ := (∑ i ∈ S,x i)/S.card
noncomputable def readings {m n : ℕ} (P : Fin n → Finset (Fin m)) (b : Bits m) (j : Fin n) : ℝ :=
  avg (P j) (fun i => bit (b i))
def source {m : ℕ} (r : ℕ) (p : Bits m → ℝ) : Prop :=
  (∀ b, 0≤p b) ∧ (∑ b,p b)=1 ∧ ∀ b,p b ≤ (2:ℝ)^r/2^m
def near {n : ℕ} (ε : ℝ) (z y : Fin n → ℝ) : Prop := ∀ j, |z j-y j|≤ε
def cube {n : ℕ} (S : Finset (Fin n → ℝ)) : Prop := ∀ z∈S, ∀ j, z j ∈ Set.Icc (0:ℝ) 1
noncomputable def missed {m n : ℕ} (p : Bits m → ℝ) (P : Fin n → Finset (Fin m))
    (S : Finset (Fin n → ℝ)) (ε : ℝ) : ℝ := by
  classical
  exact ∑ b, if ∃ z∈S, near ε z (readings P b) then 0 else p b

theorem main :
    (∀ (m n t : ℕ) (P : Fin n → Finset (Fin m)) (ε K : ℝ), 0<ε → 0<K →
      (∀ j, K ≤ ((P j).card:ℝ)) →
      ∃ S : Finset (Fin n → ℝ), cube S ∧ S.card ≤ (2*n+1)^t ∧
        ∀ r p, source r p → missed p P S ε ≤ (2:ℝ)^r *
          (((2*n+1:ℕ):ℝ)*Real.exp (-2*ε^2*K))^(t+1)) ∧
    (∀ (m n s : ℕ) (P : Fin n → Finset (Fin m)), 0<s → 20000 ≤ Real.log n →
      (∀ j, (Real.log n)^2 ≤ ((P j).card:ℝ)) →
      ∃ S : Finset (Fin n → ℝ), cube S ∧ S.card ≤ s ∧
        ∀ r p, source r p → missed p P S (1/100) ≤ (2:ℝ)^r/s) ∧
    (∀ (m n r : ℕ) (P : Fin n → Finset (Fin m)), 20000 ≤ Real.log n →
      (∀ j, (Real.log n)^2 ≤ ((P j).card:ℝ)) →
      ∃ S : Finset (Fin n → ℝ), cube S ∧ S.card ≤ 100*2^r ∧
        ∀ p, source r p → missed p P S (1/100) ≤ 1/100) ∧
    (∃ C : ℕ, ∀ (m n r : ℕ) (P : Fin n → Finset (Fin m)),
      (∀ j, (Real.log n)^2 ≤ ((P j).card:ℝ)) →
      ∃ S : Finset (Fin n → ℝ), cube S ∧ S.card ≤ C*2^r ∧
        ∀ p, source r p → missed p P S (1/100) ≤ 1/100) := by
  sorry
end OMA.S_mo_198378
