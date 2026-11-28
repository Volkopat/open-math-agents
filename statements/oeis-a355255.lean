import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cyclic binary differences in A355255

Source: https://oeis.org/A355255
Credit: @blakestone-x

The initial necklace has a single one, as in the column k=1. A necklace
is the set of all cyclic rotations of a word, so reflections are not identified.
The set of iterates includes time zero.
-/

namespace OMA.S_oeis_a355255

abbrev Word (n : ℕ) := ZMod n → ZMod 2

def step {n : ℕ} (w : Word n) : Word n := fun i => w i - w (i-1)

def oneBead (n : ℕ) : Word n := fun i => if i = 0 then 1 else 0

def necklace {n : ℕ} (w : Word n) : Set (Word n) :=
  Set.range (fun j : ZMod n => fun i : ZMod n => w (i+j))

noncomputable def count (n : ℕ) : ℕ :=
  Nat.card (Set.range (fun t : ℕ => necklace ((step (n := n))^[t] (oneBead n))))

theorem main : (∀ m : ℕ, 1 < m → count (2^m) = 2^m + 1) ∧
    (∀ n : ℕ, 0 < n → (¬ ∃ j : ℕ, n = 2^j) → ∃ j : ℕ, count n = 2^j) := by
  sorry

end OMA.S_oeis_a355255
