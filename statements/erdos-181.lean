import Mathlib

/-! Source: https://www.erdosproblems.com/181 . Credit: @jaredwilder. Adapted from the September 2026 archive. Two-colour Ramsey upper bound for the hypercube, with a positive constant. -/
namespace OMA.S_erdos_181
open scoped Classical
abbrev CubeVertex (n : ℕ) := Fin n → Fin 2

def cubeAdjacent (n : ℕ) (x y : CubeVertex n) : Prop :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card = 1

def cubeVertexCount (n : ℕ) : ℕ :=
  2 ^ n

def cubeEdgeCount (n : ℕ) : ℕ :=
  n * 2 ^ (n - 1)

def monochromaticCopy (n N : ℕ)
    (c : Fin N → Fin N → Bool)
    (f : CubeVertex n → Fin N) : Prop :=
  Function.Injective f ∧
    ∃ b : Bool, ∀ x y : CubeVertex n,
      cubeAdjacent n x y → c (f x) (f y) = b

def ramseyProperty (n N : ℕ) : Prop :=
  ∀ c : Fin N → Fin N → Bool,
    (∀ i j : Fin N, c i j = c j i) →
      ∃ f : CubeVertex n → Fin N, monochromaticCopy n N c f

def cubeRamseyBound : Prop :=
  ∃ C N : ℕ, 0 < C ∧ ∀ n : ℕ, N ≤ n → ramseyProperty n (C * 2 ^ n)


theorem main : cubeRamseyBound := by
  sorry
end OMA.S_erdos_181
