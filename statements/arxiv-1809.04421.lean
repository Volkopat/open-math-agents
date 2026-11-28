import Mathlib

/-!
# Infinitely many infertility numbers

Source: https://arxiv.org/abs/1809.04421, Definition 1.1 and Conjecture 4.1 (Colin Defant)
Credit: @pyaf

West's stack-sorting map s reads the input left to right: the next entry is
pushed if the stack is empty or the entry is smaller than the top of the
stack; otherwise the top of the stack is popped to the output. When the input
is exhausted the stack is emptied. The fertility of a permutation π is
|s⁻¹(π)|, and f is a fertility number if some permutation has fertility f.
Since s commutes with order-preserving relabelling, it suffices to consider
permutations of {0, …, n−1}, written in one-line notation. The conjecture:
infinitely many natural numbers are not fertility numbers.
-/

namespace OMA.S_arxiv_1809_04421

/-- Pops the stack (head is the top) while its top is not larger than x;
returns the popped entries in output order and the remaining stack. -/
def popUntil (x : ℕ) : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | t :: st => if x < t then ([], t :: st) else
      let r := popUntil x st
      (t :: r.1, r.2)

/-- Stack-sorting with remaining input xs and stack st: each input entry is
pushed after popping every top entry that is not larger than it. -/
def stackSort : List ℕ → List ℕ → List ℕ
  | [], st => st
  | x :: xs, st =>
    let r := popUntil x st
    r.1 ++ stackSort xs (x :: r.2)

/-- One-line notation of a permutation of Fin n. -/
def word {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn (fun i => (σ i).val)

/-- The number of preimages of π under the stack-sorting map. -/
def fertility {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => stackSort (word σ) [] = word π)).card

def IsFertilityNumber (f : ℕ) : Prop := ∃ (n : ℕ) (π : Equiv.Perm (Fin n)), fertility π = f

theorem main : {f : ℕ | ¬ IsFertilityNumber f}.Infinite := by
  sorry

end OMA.S_arxiv_1809_04421
