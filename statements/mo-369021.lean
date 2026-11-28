import Mathlib

/-!
# Mutually orthogonal Latin hypercubes of side `d + 1`

Source: https://mathoverflow.net/questions/369021
Asked by MathOverflow user BPP (Mutually orthogonal Latin hypercubes).

A `d`-dimensional Latin hypercube of side `n` is a `d`-dimensional array with `n` symbols
such that along any line parallel to an axis each symbol appears exactly once. An `(n, d)`
mutually orthogonal Latin hypercube (MOLH) is a set of `d` such hypercubes such that
overlaying them, every element of the Cartesian product of the symbols appears exactly
once. `(3, 2)` MOLHs exist (Graeco-Latin squares of order `3`); the question asks whether
there are `(d + 1, d)` MOLHs for `d ≥ 3`.

Translation choices.
* Cells are `x : Fin d → Fin n`, symbols are `Fin n`, and the `d` hypercubes are
  `L c : (Fin d → Fin n) → Fin n` for `c : Fin d`.
* Latin property: for every hypercube `c`, axis `a` and cell `x`, moving `x` along the line
  through `x` parallel to axis `a` (`s ↦ Function.update x a s`) hits every symbol exactly
  once (a bijection `Fin n → Fin n`).
* Mutual orthogonality: the overlay `x ↦ (c ↦ L c x)` is a bijection onto `Fin d → Fin n`.
* `main` is the first case `d = 3` (side `4`), which is the case settled on MathOverflow; the
  cases `d ≥ 4` are not formalized.
-/

namespace OMA.S_mo_369021

/-- `L` is an `(n, d)` system of mutually orthogonal Latin hypercubes. -/
def IsMOLH (n d : ℕ) (L : Fin d → (Fin d → Fin n) → Fin n) : Prop :=
  (∀ c : Fin d, ∀ a : Fin d, ∀ x : Fin d → Fin n,
      Function.Bijective (fun s : Fin n => L c (Function.update x a s))) ∧
    Function.Bijective (fun x : Fin d → Fin n => fun c : Fin d => L c x)

theorem main : ∃ L : Fin 3 → (Fin 3 → Fin 4) → Fin 4, IsMOLH 4 3 L := by
  sorry

end OMA.S_mo_369021
