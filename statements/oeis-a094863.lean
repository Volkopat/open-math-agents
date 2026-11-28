import Mathlib

/-!
# OEIS A094863, the extremal distinct LCS conjecture

The words attaining the proposed maximum at even lengths are prefixes of
12341234... and 43214321... . We allow every relative starting phase, which
also covers reversing a finite prefix. A word is counted only once, regardless
of how often it embeds. Natural-number letters allow any finite alphabet.

Sources: https://oeis.org/A094863 and https://oeis.org/A094858.
-/

namespace OMA.S_oeis_a094863

def common (x y : List ℕ) : Finset (List ℕ) :=
  x.sublists.toFinset ∩ y.sublists.toFinset

def lcsLength (x y : List ℕ) : ℕ := (common x y).sup List.length

def lcsCount (x y : List ℕ) : ℕ :=
  ((common x y).filter fun w => w.length = lcsLength x y).card

def ascending (k n : ℕ) : List ℕ := (List.range n).map (· % k)

def descending (k phase n : ℕ) : List ℕ :=
  (List.range n).map fun i => (phase + k - i % k) % k

theorem main : ∀ m : ℕ, 0 < m → ∃ phase : Fin 4, ∀ x y : List ℕ,
    x.length = 2*m → y.length = 2*m →
    lcsCount x y ≤ lcsCount (ascending 4 (2*m)) (descending 4 phase.val (2*m)) := by
  sorry

end OMA.S_oeis_a094863
