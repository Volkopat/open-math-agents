import Mathlib

/-!
# The homogeneous span of two positive definite matrices

Source: Wolfgang, https://mathoverflow.net/questions/321552 (CC BY-SA 4.0).
Credit: @connoranderson.

Word records the two formal exponents in a finite expression built from A
and B by real powers and the product X Y X. Positive real powers here mean
spectral functional calculus on a positive definite matrix, with arbitrary
real exponent. spanSet selects words of nonnegative bidegree adding to one.

For every real or complex positive definite pair the span is compact exactly
when the generators commute. In a common eigenbasis the span is the full
weighted geometric interpolation curve. If the pair fails to commute, even
the fixed midpoint bidegree (1/2,1/2) escapes every compact set (q=4); the
endpoint bidegree (0,1) does as well (q=2). Thus the proposed finite diameter
in the middle already fails. The last clause gives an example in which
allowing arithmetic averages strictly enlarges the convex hull. Since A is
the identity, the square root of the arithmetic midpoint is its geometric
midpoint with A. This point lies outside the convex hull of the original
span, as witnessed by a linear inequality valid on a moment curve.
-/

namespace OMA.S_mo_321552
open Matrix
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
abbrev Mat (𝕜 : Type) (n : ℕ) := Matrix (Fin n) (Fin n) 𝕜
def diagR (𝕜 : Type) [RCLike 𝕜] {n : ℕ} (d : Fin n → ℝ) : Mat 𝕜 n :=
  diagonal (fun i => (d i : 𝕜))
def powerRel (X : Mat 𝕜 n) (t : ℝ) (Y : Mat 𝕜 n) : Prop :=
  ∃ (U : unitary (Mat 𝕜 n)) (d : Fin n → ℝ), (∀ i,0<d i) ∧
    X=(U:Mat 𝕜 n)*diagR 𝕜 d*(U:Mat 𝕜 n)ᴴ ∧
    Y=(U:Mat 𝕜 n)*diagR 𝕜 (fun i => (d i)^t)*(U:Mat 𝕜 n)ᴴ
inductive Word (A B : Mat 𝕜 n) : ℝ → ℝ → Mat 𝕜 n → Prop
  | left : Word A B 1 0 A
  | right : Word A B 0 1 B
  | sandwich {u v p q X Y} : Word A B u v X → Word A B p q Y →
      Word A B (2*u+p) (2*v+q) (X*Y*X)
  | power {u v X t Y} : Word A B u v X → powerRel X t Y → Word A B (t*u) (t*v) Y
def spanSet (A B : Mat 𝕜 n) : Set (Mat 𝕜 n) :=
  {X | ∃ u v : ℝ, 0≤u ∧ 0≤v ∧ u+v=1 ∧ Word A B u v X}

open scoped ComplexOrder
theorem main :
    (∀ (K : Type) [RCLike K] (m : ℕ) (A B : Mat K m), A.PosDef → B.PosDef →
      (IsCompact (spanSet A B) ↔ Commute A B) ∧
      (¬Commute A B → ∀ (u : ℝ) (q : ℕ), 0<q → ∀ S : Set (Mat K m), IsCompact S →
        ∃ X, Word A B u (2/(q:ℝ)) X ∧ X∉S)) ∧
    (∀ (K : Type) [RCLike K] (m : ℕ) (a b : Fin m → ℝ), (∀ i,0<a i) → (∀ i,0<b i) →
      spanSet (diagR K a) (diagR K b) =
        (fun t : ℝ => diagR K (fun i => (a i)^t*(b i)^(1-t))) '' Set.Icc 0 1) ∧
    (∀ (K : Type) [RCLike K],
      let A := diagR K (fun _ : Fin 5 => 1)
      let B := diagR K (fun i : Fin 5 => (2:ℝ)^i.val)
      let Y := diagR K (fun i : Fin 5 => Real.sqrt ((1+(2:ℝ)^i.val)/2))
      powerRel ((1/2:ℝ) • (A+B)) (1/2) Y ∧ Y∉convexHull ℝ (spanSet A B)) := by
  sorry
end OMA.S_mo_321552
