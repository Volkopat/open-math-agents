import FormalConjectures.GreensOpenProblems.«92»

-- Credit: @garrytaulu
namespace OMA.R_Green92_green_92_variants_chase_upper_R2

open Finset Filter Green92
open scoped Classical

/-- Bound the summed overlap of single-trace laws at Chase's sample count.
A trace outside the support of x has zero contribution to the affinity. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    let m := ⌈Real.exp (C * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log n ^ 5)⌉₊
    let masks := (univ : Finset (Finset (Fin n)))
    let law (x : Fin n → Bool) (w : List Bool) : ℝ :=
      ((masks.filter fun S => Green92.trace x S = w).card : ℝ) / masks.card
    let affinity (x y : Fin n → Bool) : ℝ :=
      ∑ w ∈ masks.image (Green92.trace x),
        Real.sqrt (law x w) * Real.sqrt (law y w)
    ∀ x, (∑ y ∈ univ.erase x, (affinity x y) ^ m) ≤ (1 / 10 : ℝ)

/-- For every sample count, maximum likelihood bounds the error at each true
string by the sum of its pairwise affinities raised to the sample count.
An incorrect output y has likelihood at least that of the true x. On this
event, its probability under x is bounded by the geometric mean of the two
likelihoods. Independence factors the sum over trace tuples. -/
def H2 : Prop :=
  ∀ n m : ℕ,
    let masks := (univ : Finset (Finset (Fin n)))
    let law (x : Fin n → Bool) (w : List Bool) : ℝ :=
      ((masks.filter fun S => Green92.trace x S = w).card : ℝ) / masks.card
    let affinity (x y : Fin n → Bool) : ℝ :=
      ∑ w ∈ masks.image (Green92.trace x),
        Real.sqrt (law x w) * Real.sqrt (law y w)
    ∃ R : (Fin m → List Bool) → Fin n → Bool, ∀ x,
      1 - (∑ y ∈ univ.erase x, (affinity x y) ^ m) ≤ successProb R x

theorem main : H1 → H2 → type_of% @Green92.green_92.variants.chase_upper := by
  rintro ⟨C, hC, h⟩ hdecode
  refine ⟨C, hC, ?_⟩
  filter_upwards [h] with n hn
  let m := ⌈Real.exp (C * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log n ^ 5)⌉₊
  obtain ⟨R, hR⟩ := hdecode n m
  apply Nat.sInf_le
  refine ⟨R, fun x => ?_⟩
  have err := hn x
  have dec := hR x
  dsimp only [m] at dec
  linarith only [err, dec]

end OMA.R_Green92_green_92_variants_chase_upper_R2
