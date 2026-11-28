import Mathlib

namespace OMA.S_mo_415442

abbrev Generator (n : ℕ) := Fin (n - 1)

def artinRelators (n : ℕ) : Set (FreeGroup (Generator n)) :=
  {w | ∃ i j : Generator n,
    let a := FreeGroup.of i
    let b := FreeGroup.of j
    (i.val + 2 ≤ j.val ∧ w = a * b * (b * a)⁻¹) ∨
    (i.val + 1 = j.val ∧ w = a * b * a * (b * a * b)⁻¹)}

abbrev BraidGroup (n : ℕ) := PresentedGroup (artinRelators n)

abbrev IntegralGL (m : ℕ) := (Matrix (Fin m) (Fin m) ℤ)ˣ

/-- Are braid groups on sufficiently many strands non-linear over the integers? -/
theorem main :
    ∃ threshold : ℕ, ∀ n : ℕ, threshold ≤ n →
      ∀ m : ℕ, ¬ ∃ ρ : BraidGroup n →* IntegralGL m, Function.Injective ρ := by
  sorry

end OMA.S_mo_415442
