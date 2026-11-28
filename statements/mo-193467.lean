import Mathlib

/-!
# Existence of a matrix product from its eigenvalues

Source: ScienceSnake, https://mathoverflow.net/questions/193467 (CC BY-SA 3.0).
Credit: @connoranderson.

The question asks for two real symmetric positive definite matrices with
prescribed spectra, including the spectrum of their product. Use an
orthonormal eigenbasis of the second matrix and let O be the relative
orthogonal eigenbasis of the first. This coordinate choice preserves the
three spectra. A characteristic polynomial identity records multiplicities.

The source uses strong majorization in its question and suggests weak
majorization in a comment. In the strong reading equality of total sums
forces a scalar factor. The weak reading fails already in dimension three,
even with the two-sided partial product bounds and the determinant identity.
In dimension two the realizability condition has an exact trace interval.
-/

namespace OMA.S_mo_193467
open Matrix Finset
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Vec (n : ℕ) := Fin n → ℝ
def prefixSum {n : ℕ} (a : Vec n) (k : ℕ) : ℝ := ∑ i ∈ univ.filter (fun i : Fin n => i.val<k),a i
def aligned {n : ℕ} (a b : Vec n) : Vec n := fun i => a i*b i
def opposite {n : ℕ} (a b : Vec n) : Vec n := fun i => a i*b i.rev
def weakBounds {n : ℕ} (a b c : Vec n) : Prop :=
  (∀ S : Finset (Fin n), (∑ i ∈ S,opposite a b i) ≤ prefixSum c S.card) ∧
  (∀ k, prefixSum c k ≤ prefixSum (aligned a b) k)
def strongBounds {n : ℕ} (a b c : Vec n) : Prop := weakBounds a b c ∧
  (∑ i,opposite a b i)=(∑ i,c i) ∧ (∑ i,c i)=(∑ i,aligned a b i)
def realizes {n : ℕ} (a b c : Vec n) : Prop :=
  ∃ O : unitary (Mat n), ∀ t : ℝ,
    (t • (1:Mat n) - ((O:Mat n)*diagonal a*(O:Mat n)ᵀ)*diagonal b).det = ∏ i,(t-c i)
def leftSpec : Vec 3 := ![9,1,1]
def rightSpec : Vec 3 := ![4,3,1]
noncomputable def productSpec : Vec 3 := ![12,6,3/2]
def prefixProd {n : ℕ} (x : Vec n) (k : ℕ) : ℝ :=
  ∏ i ∈ univ.filter (fun i : Fin n => i.val < k),x i
def logBounds {n : ℕ} (a b c : Vec n) : Prop :=
  (∀ S : Finset (Fin n), (∏ i ∈ S,opposite a b i) ≤ prefixProd c S.card) ∧
  (∀ k, prefixProd c k ≤ prefixProd (aligned a b) k) ∧ (∏ i,c i)=(∏ i,aligned a b i)

theorem main :
    (∀ (n : ℕ) (a b c : Vec n), Antitone a → Antitone b → Antitone c →
      (∀ i,0<a i) → (∀ i,0<b i) → (∀ i,0<c i) → strongBounds a b c →
      ((∀ i j,a i=a j) ∨ (∀ i j,b i=b j)) ∧ c=aligned a b ∧ realizes a b c) ∧
    (Antitone leftSpec ∧ Antitone rightSpec ∧ Antitone productSpec ∧
      (∀ i,0<leftSpec i) ∧ (∀ i,0<rightSpec i) ∧ (∀ i,0<productSpec i) ∧
      weakBounds leftSpec rightSpec productSpec ∧
      logBounds leftSpec rightSpec productSpec ∧ ¬realizes leftSpec rightSpec productSpec) ∧
    (∀ (a b c : Vec 2), Antitone a → Antitone b →
      (realizes a b c ↔ c 0*c 1=(a 0*a 1)*(b 0*b 1) ∧
        a 0*b 1+a 1*b 0 ≤ c 0+c 1 ∧ c 0+c 1 ≤ a 0*b 0+a 1*b 1)) := by
  sorry
end OMA.S_mo_193467
