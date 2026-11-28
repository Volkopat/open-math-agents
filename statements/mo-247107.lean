import Mathlib.Data.Fintype.BigOperators

/-!
# Strict up-down words with prescribed multiplicities
Source: https://mathoverflow.net/questions/247107 (hkju).
Formalization: @YOHSUKE-TAKAHASHI.
Labels 0,...,n-1 stand for the original labels 1,...,n in order.
-/

namespace OMA.S_mo_247107
open Finset

variable {n : ℕ}
abbrev Inventory (n : ℕ) := Fin n → ℕ

/-- Consume one copy of the chosen label. -/
def consume (r : Inventory n) (i j : Fin n) : ℕ :=
  if j = i then r j - 1 else r j

/-- Test the next strict comparison from i to j. -/
def compareNext (up : Bool) (i j : Fin n) : Bool :=
  if up then decide (i < j) else decide (j < i)

/-- The first letter must be allowed. The comparison after it is up or down
as specified, and successive comparisons alternate. -/
def alternating (allowed : Fin n → Bool) (up : Bool) : List (Fin n) → Bool
  | [] => true
  | i :: rest => allowed i && alternating (compareNext up i) (!up) rest

def heads (r : Inventory n) (allowed : Fin n → Bool) : Finset (Fin n) :=
  univ.filter fun i => 0 < r i ∧ allowed i = true

/-- A numerical recurrence. Its states need only the remaining counts, the
admissible first letters (determined by the previous letter), and the direction. -/
def count : ℕ → Inventory n → (Fin n → Bool) → Bool → ℕ
  | 0, r, _, _ => if ∀ j, r j = 0 then 1 else 0
  | k + 1, r, allowed, up =>
      ∑ i ∈ heads r allowed, count k (consume r i) (compareNext up i) (!up)

def answer (n : ℕ) := count (2 * n) (fun _ : Fin n => 2) (fun _ => true) true

theorem main : ∀ n : ℕ,
    ∃ s : Finset (List (Fin n)),
      (∀ w, w ∈ s ↔ w.length = 2 * n ∧ (∀ i, w.count i = 2) ∧
        alternating (fun _ => true) true w = true) ∧ s.card = answer n := by
  sorry

end OMA.S_mo_247107
