import Mathlib

/-!
# A closed form for the series of Hadamard products of matrix powers

Source: alcubierre-drive, https://mathoverflow.net/questions/336709 (CC BY-SA 4.0).
Credit: @connoranderson.

For unitary eigenvector matrices U,V with eigenvalues a,b, the mode (p,q)
has ratio a_p b_q and rank-one coefficient z z*, where z_i=U_ip V_iq.
The coefficient vanishes exactly when the two eigenvectors have disjoint
coordinate supports. Only active modes need a ratio of modulus below one.
Their geometric sums give the closed form; totalized division also handles
inactive modes at a singular denominator. The mode expansion holds for
every power, irrespective of convergence. In the inverse-transpose special
case asked about in the source, the series diverges in positive dimension.
-/

namespace OMA.S_mo_336709
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
def term {n : ℕ} (A B : Mat n) (k : ℕ) : Mat n := (A^k).hadamard (B^k)
def specData {n : ℕ} (A : Mat n) (U : unitary (Mat n)) (a : Fin n → ℝ) : Prop :=
  A=(U:Mat n)*diagonal (fun i => (a i:ℂ))*(U:Mat n)ᴴ
def vec {n : ℕ} (U V : unitary (Mat n)) (p q i : Fin n) : ℂ :=
  (U:Mat n) i p*(V:Mat n) i q
def coeff {n : ℕ} (U V : unitary (Mat n)) (p q : Fin n) : Mat n :=
  fun i j => vec U V p q i * star (vec U V p q j)
def activeBound {n : ℕ} (U V : unitary (Mat n)) (a b : Fin n → ℝ) : Prop :=
  ∀ p q, (∃ i,vec U V p q i≠0) → |a p*b q|<1
noncomputable def closedForm {n : ℕ} (U V : unitary (Mat n)) (a b : Fin n → ℝ) : Mat n :=
  ∑ p,∑ q, ((1-(a p*b q:ℝ):ℂ)⁻¹) • coeff U V p q

open Filter Topology
theorem main :
    (∀ (n : ℕ) (A : Mat n), A.IsHermitian → ∃ (U : unitary (Mat n)) (a : Fin n → ℝ), specData A U a) ∧
    (∀ (n : ℕ) (A B : Mat n) (U V : unitary (Mat n)) (a b : Fin n → ℝ),
      specData A U a → specData B V b →
      (∀ k : ℕ, term A B k = ∑ p,∑ q, (((a p*b q:ℝ):ℂ)^k) • coeff U V p q) ∧
      (Tendsto (term A B) atTop (𝓝 0) ↔ activeBound U V a b) ∧
      (Summable (term A B) ↔ activeBound U V a b) ∧
      (activeBound U V a b → HasSum (term A B) (closedForm U V a b))) ∧
    (∀ (n : ℕ), 0<n → ∀ (A B : Mat n), A.IsHermitian → B.IsHermitian → IsUnit A → A⁻¹=Bᵀ →
      ¬Tendsto (term A B) atTop (𝓝 0)) := by
  sorry
end OMA.S_mo_336709
