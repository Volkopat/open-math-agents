import Mathlib

/-!
# The twelve-step growth law for OEIS A316316

Source: https://oeis.org/A316316
Credit: @etaubman

We use Colin Barker's sixth-order recurrence and the six initial positive-index
terms in OEIS to represent the coordination sequence of a tetravalent vertex
in the chamfered square grid. The initial term at radius zero is separate.
Rémy Sigrist proposed the twelve-step law in 2018. N. J. A. Sloane proved
it by the coloring-book method later that day.
-/

namespace OMA.S_oeis_a316316

structure Window where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  deriving DecidableEq

/-- Advance Barker's recurrence by one place. -/
def step (w : Window) : Window :=
  ⟨w.b, w.c, w.d, w.e, w.f, w.f - w.e + 2 * w.d - w.c + w.b - w.a⟩

def window : ℕ → Window
  | 0 => ⟨4, 8, 8, 12, 20, 20⟩
  | k + 1 => step (window k)

def term : ℕ → ℤ
  | 0 => 1
  | k + 1 => (window k).a

theorem main : ∀ n : ℕ, 0 < n → term (n + 12) = term n + 40 := by
  sorry

end OMA.S_oeis_a316316

