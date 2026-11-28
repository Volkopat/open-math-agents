import Mathlib

/-!
# Zero runs of the fixed point of the morphism in A395088

The alphabet is Boolean, with false representing zero. The limit is specified
by its finite prefixes in the iterates starting from zero. For any input
prefix u the predicted output begins with one zero and two ones. Each bit
of u then specifies a complete zero run, followed by two ones. Thus this
prefix statement gives c(1) = 1 and c(i+2) = 3 - 2*a(i) at every index.

Source: https://oeis.org/A395088
Credit: @CubeJerry
-/

namespace OMA.S_oeis_a395088

def expand (u : List Bool) : List Bool :=
  u.flatMap fun b => if b then [false] else [false, true, true]

def stage : ℕ → List Bool
  | 0 => [false]
  | t + 1 => expand (stage t)

def LimitPrefix (u : List Bool) : Prop := ∃ t, u <+: stage t

def predicted (u : List Bool) : List Bool :=
  [false, true, true] ++ u.flatMap fun b =>
    List.replicate (if b then 1 else 3) false ++ [true, true]

theorem main :
    (∀ n : ℕ, ∃ u : List Bool, u.length = n ∧ LimitPrefix u) ∧
    (∀ u : List Bool, LimitPrefix u → LimitPrefix (predicted u)) := by
  sorry

end OMA.S_oeis_a395088
