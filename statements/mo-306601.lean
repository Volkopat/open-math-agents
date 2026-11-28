import Mathlib

/-!
# Additive concentration does not control all Hamming-Lipschitz functions

Take m independent fair bits, copy them into a second block, and complement
the whole second block according to one additional independent fair bit.
Any three distinct coordinates are independent fair bits. All
additive statistics with summands in [0,1] have squared-Gaussian tails with
exponent 1/(2m). The Hamming distance between the blocks has a deviation of
m/2 with probability one. Its optimal exponent is 4 log(2)/m².

Source: Aryeh Kontorovich, https://mathoverflow.net/questions/306601 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)
-/
namespace OMA.S_mo_306601
open Finset
abbrev Cube (m : ℕ) := Fin m×Bool → Bool
abbrev Sample (m : ℕ) := Bool × (Fin m → Bool)
def draw {m : ℕ} (s : Sample m) (i : Fin m×Bool) : Bool :=
  xor (s.2 i.1) (s.1 && i.2)
noncomputable def mean {α : Type*} [Fintype α] (f : α→ℝ) : ℝ := (∑ x,f x)/Fintype.card α
noncomputable def prob {α : Type*} [Fintype α] (E : α→Prop) : ℝ := by
  classical exact mean (fun x => if E x then 1 else 0)
noncomputable def tail {m : ℕ} (f : Cube m→ℝ) (t : ℝ) :=
  prob (fun s : Sample m => t≤|f (draw s)-mean (fun q : Sample m => f (draw q))|)
def hamming {m : ℕ} (x y : Cube m) : ℕ := ∑ i, if x i=y i then 0 else 1
def distance {m : ℕ} (x : Cube m) : ℝ := ∑ i : Fin m, if x (i,false)=x (i,true) then 0 else 1
noncomputable def additive {m : ℕ} (f : (Fin m×Bool)→Bool→ℝ) (x : Cube m) : ℝ := ∑ i,f i (x i)
theorem main :
    (∀ m : ℕ, 0 < m →
      (∀ (i : Fin m×Bool) (a : Bool), prob (fun s : Sample m => draw s i=a)=1/2) ∧
      (∀ (i j : Fin m×Bool), i≠j → ∀ a b : Bool, prob (fun s : Sample m => draw s i=a ∧ draw s j=b)=1/4) ∧
      (∀ (i j k : Fin m×Bool), i≠j → i≠k → j≠k → ∀ a b c : Bool,
        prob (fun s : Sample m => draw s i=a ∧ draw s j=b ∧ draw s k=c)=1/8) ∧
      (∀ f : (Fin m×Bool)→Bool→ℝ, (∀ i b, f i b ∈ Set.Icc (0:ℝ) 1) →
        ∀ t : ℝ, 0≤t → tail (additive f) t ≤ 2*Real.exp (-t^2/(2*m))) ∧
      (∀ x y : Cube m, |distance x-distance y|≤hamming x y) ∧
      mean (fun s : Sample m => distance (draw s)) = (m:ℝ)/2 ∧
      tail (distance (m := m)) ((m:ℝ)/2)=1 ∧
      (∀ C : ℝ, (∀ t : ℝ, 0≤t → tail (distance (m := m)) t ≤ 2*Real.exp (-C*t^2)) ↔
        C≤4*Real.log 2/(m:ℝ)^2)) ∧
    (tail (distance (m := 16)) 8 > 2*Real.exp (-(8:ℝ)^2/(2*16))) := by
  sorry
end OMA.S_mo_306601
