import Mathlib

/-!
# The least positive spectral norm of a signed row and column sum

Source: Wouter, https://mathoverflow.net/questions/242409 (CC BY-SA 3.0).
Exact reduced enumeration and Matching Cut reduction by @connoranderson.

For fixed column signs the search branches only on rows with two different
column signs in their support. It also tests the individual row cuts.
For signed zero–one magnitudes, deciding whether the minimum is 2 is
equivalent to a nonempty matching cut of the bipartite support graph. The
next possible value is at least 2√2. For the independent complexity of
bipartite Matching Cut see Van Bang Le and Bert Randerath, “On stable
cutsets in line graphs”, https://doi.org/10.1016/S0304-3975(03)00048-3.
-/

namespace OMA.S_mo_242409
open Matrix Finset
abbrev Rect (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
def sign (a : Bool) : ℝ := if a then 1 else -1
noncomputable def masked {m n : ℕ} (C : Rect m n) (a : Fin m→Bool) (b : Fin n→Bool) : Rect m n :=
  Matrix.diagonal (sign ∘ a)*C+C*Matrix.diagonal (sign ∘ b)
noncomputable def op {m n : ℕ} (D : Rect m n) : ℝ := ‖D.toEuclideanLin.toContinuousLinearMap‖
noncomputable def mixedRows {m n : ℕ} (C : Rect m n) (b : Fin n→Bool) : Finset (Fin m) := by
  classical
  exact univ.filter fun i => ∃ j l,C i j≠0 ∧ C i l≠0 ∧ b j≠b l
abbrev Plan {m n : ℕ} (C : Rect m n) :=
  Fin m ⊕ (Σ b : Fin n→Bool, (mixedRows C b → Bool))
noncomputable def rowSigns {m n : ℕ} (C : Rect m n) (b : Fin n→Bool)
    (f : mixedRows C b → Bool) (i : Fin m) : Bool := by
  classical
  exact if h : i∈mixedRows C b then f ⟨i,h⟩ else decide (¬∃j,C i j≠0 ∧ b j=true)
noncomputable def cost {m n : ℕ} (C : Rect m n) : Plan C → ℝ
  | .inl i => op (masked C (fun t => decide (t=i)) (fun _ => true))
  | .inr ⟨b,f⟩ => op (masked C (rowSigns C b f) b)
def values {m n : ℕ} (C : Rect m n) : Set ℝ :=
  {r | 0<r ∧ ∃ a b, op (masked C a b)=r}
def prices {m n : ℕ} (C : Rect m n) : Set ℝ := {r | 0<r ∧ ∃ p : Plan C,cost C p=r}
def crosses {m n : ℕ} (C : Rect m n) (a : Fin m→Bool) (b : Fin n→Bool)
    (i : Fin m) (j : Fin n) : Prop := C i j≠0 ∧ a i≠b j
def matchingCut {m n : ℕ} (C : Rect m n) : Prop :=
  ∃ a b, (∃ i j,crosses C a b i j) ∧
    (∀ i j l,crosses C a b i j → crosses C a b i l → j=l) ∧
    (∀ i t j,crosses C a b i j → crosses C a b t j → i=t)
def exampleInt : Matrix (Fin 8) (Fin 4) ℤ :=
  !![1,-1,0,0; -1,1,0,0; 0,0,1,-1; 0,0,-1,1; 1,0,-1,0; 0,1,0,-1; -1,0,1,0; 0,-1,0,1]
def exampleMatrix : Rect 8 4 := exampleInt.map (Int.castRingHom ℝ)
theorem main : (∀ (m n : ℕ) (C : Rect m n),
    (∀ r : ℝ, IsLeast (values C) r ↔ IsLeast (prices C) r) ∧
    (C≠0 → ∃ r,IsLeast (values C) r ∧ IsLeast (prices C) r) ∧
    Fintype.card (Plan C)=m+∑ b : Fin n→Bool,2^(mixedRows C b).card ∧
    ((∀ i j,C i j≠0 → |C i j|=1) →
      (IsLeast (values C) 2 ↔ matchingCut C) ∧
      ∀ r∈values C,r=2 ∨ 2*Real.sqrt 2 ≤ r)) ∧
    IsLeast (values exampleMatrix) 2 ∧ Fintype.card (Plan exampleMatrix)=714 := by
  sorry
end OMA.S_mo_242409
