import Mathlib

/-!
# Israel's bounds for Murthy's greedy sequence of distinct composite sums

Source: https://oeis.org/A075077 (Amarnath Murthy, 2002; conjecture by Robert Israel, 2026).
Credit: @frido22
-/

namespace OMA.S_oeis_a075077

/-- The most recent term, all previous terms, and all previous adjacent sums. -/
structure History where
  last : ℕ
  terms : Finset ℕ
  sums : Finset ℕ
  deriving DecidableEq

/-- Adding a fresh positive term must also give a fresh composite sum. -/
def Allowed (s : History) (x : ℕ) : Prop :=
  0 < x ∧ x ∉ s.terms ∧ 1 < s.last + x ∧ ¬ (s.last + x).Prime ∧ s.last + x ∉ s.sums

instance (s : History) (x : ℕ) : Decidable (Allowed s x) := by unfold Allowed; infer_instance

/-- A large fresh term of the same parity as the last one bounds the search. -/
def bound (s : History) : ℕ := s.last + 2 * (s.terms.sup id + s.sums.sup id + 2)

def candidates (s : History) : Finset ℕ := (Finset.Iic (bound s)).filter (Allowed s)

/-- Choose the least admissible value, then record its adjacent sum. -/
def next (s : History) : ℕ :=
  if h : (candidates s).Nonempty then (candidates s).min' h else 0

def record (s : History) (x : ℕ) : History := ⟨x, insert x s.terms, insert (s.last + x) s.sums⟩

def state : ℕ → History
  | 0 => ⟨0, ∅, ∅⟩
  | 1 => ⟨1, {1}, ∅⟩
  | n + 2 => let s := state (n + 1); record s (next s)

def a (n : ℕ) : ℕ := (state n).last

theorem main : ∀ n : ℕ, 6 < n → n - 2 ≤ a n ∧ a n ≤ n + 1 := by
  sorry

end OMA.S_oeis_a075077
