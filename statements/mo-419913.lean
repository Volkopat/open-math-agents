import Mathlib

/-!
# Injectivity of a convex combination of operator squares on bounded sequences

Source: https://mathoverflow.net/questions/419913 (ARG, CC BY-SA 4.0).
Credit: @connoranderson

Use two copies of the natural numbers as the countable coordinate set. The adjoint
is the Hilbert adjoint on ℓ² extended by its same finite-row formula to every ℓᵖ,
including ℓ∞. Both triangular factors are invertible even on unrestricted sequences.
The constant bounded sequence belongs to the kernel of the average for A = I.
-/

namespace OMA.S_mo_419913
open scoped ENNReal
abbrev I := Bool × ℕ
abbrev Seq := I → ℝ
abbrev Space (p : ℝ≥0∞) := lp (fun _ : I => ℝ) p

def child (n : ℕ) (j : Fin 5) : ℕ := 5*n+j.val

def bAct (f : Seq) (i : I) : ℝ :=
  if i.1 then f i + (f (false,i.2/5) - 3*f (false,i.2)) else f i

def btAct (f : Seq) (i : I) : ℝ :=
  if i.1 then f i else f i + ((∑ j : Fin 5, f (true,child i.2 j)) - 3*f (true,i.2))

def extendsAt (T : Seq → Seq) (p : ℝ≥0∞) [Fact (1 ≤ p)] (L : Space p →L[ℝ] Space p) : Prop :=
  ∀ f : Space p, ∀ i : I, (L f) i = T (fun j => f j) i

theorem main :
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], ∃ B BT : Space p →L[ℝ] Space p,
      extendsAt bAct p B ∧ extendsAt btAct p BT) ∧
    (∀ B BT : Space 2 →L[ℝ] Space 2, extendsAt bAct 2 B → extendsAt btAct 2 BT →
      ∀ f g : Space 2, inner ℝ (B f) g = inner ℝ f (BT g)) ∧
    Function.Bijective bAct ∧ Function.Bijective btAct ∧
    (∃ x : Space ⊤, x ≠ 0 ∧ ∀ i : I,
      (1/2 : ℝ)*x i + (1-1/2 : ℝ)*btAct (bAct (fun j => x j)) i = 0) := by
  sorry
end OMA.S_mo_419913
