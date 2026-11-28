import Mathlib

/-!
# Worst case performance of a simple averaging algorithm
Source: https://mathoverflow.net/questions/218359/worst-case-performance-of-a-simple-averaging-algorithm

At site i the two affected entries have zero-based indices i-1, i.
Only entries 0 through n-1 are observed. The upper bound holds also for real
inputs. The hard inputs have integer entries and hence finite binary expansions.
-/
namespace OMA.S_mo_218359

abbrev State := ℤ → ℝ

noncomputable def sites (n : ℕ) : Finset ℤ := Finset.Ioo 0 n
def gap (u : State) (i : ℤ) := u (i-1)-u i+1

noncomputable def step (u : State) (i : ℤ) : State := fun j =>
  if j=i-1 then (u (i-1)+u i-1)/2
  else if j=i then (u (i-1)+u i+1)/2
  else u j

def legal (n : ℕ) (u : State) (i : ℤ) := i∈sites n ∧ 1<gap u i

def greedy (n : ℕ) (u : State) (i : ℤ) :=
  legal n u i ∧ ∀ j ∈ sites n, gap u j ≤ gap u i ∧ (gap u j=gap u i → i≤j)

def sorted (n : ℕ) (u : State) := ∀ i ∈ sites n, gap u i ≤ 1

noncomputable def run (u : State) : List ℤ → State
  | [] => u
  | i::l => run (step u i) l

def follows (rule : State → ℤ → Prop) (u : State) : List ℤ → Prop
  | [] => True
  | i::l => rule u i ∧ follows rule (step u i) l

def weight (n : ℕ) (i : ℤ) : ℝ := (i:ℝ)*((n:ℝ)-i)
noncomputable def totalWeight (n : ℕ) : ℝ := ∑ i ∈ sites n, weight n i

def uniformInput (n : ℕ) (s : ℝ) (u : State) := ∀ k ∈ Finset.Ico (0:ℤ) n, |u k| ≤ s
def growingInput (n : ℕ) (s : ℝ) (u : State) :=
  ∀ k ∈ Finset.Ico (0:ℤ) n, |u k| ≤ ((k:ℝ)+1)*s

/-- The upper bound is achieved by the specified leftmost greedy rule on
every real input. A single integer input forces the lower bound for every
legal choice of sites leading to a sorted state. -/
def complexityBounds (n : ℕ) (inputs : State → Prop) (L U : ℝ) : Prop :=
  (∀ u, inputs u → ∃ l : List ℤ, follows (greedy n) u l ∧ sorted n (run u l) ∧ (l.length:ℝ) ≤ U) ∧
  (∃ u, inputs u ∧ (∀ k, ∃ z : ℤ, u k=z) ∧ ∀ l : List ℤ, follows (legal n) u l →
    sorted n (run u l) → L ≤ l.length)

/-- The first pair of estimates bounds the two worst-case running times in
the question. The final example tests whether greedy always uses the fewest
steps on an individual input. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → ∀ s : ℝ, 0 ≤ s →
      complexityBounds n (uniformInput n s)
        (totalWeight n*Real.log (1+(⌊s/n⌋₊:ℝ))/4)
        (2*(n:ℝ)^3+2*totalWeight n*Real.log (2+s/n)) ∧
      complexityBounds n (growingInput n s)
        (totalWeight n*Real.log (1+(⌊s⌋₊:ℝ))/4)
        (2*(n:ℝ)^3+2*totalWeight n*Real.log (2+s))) ∧
    (∀ n : ℕ, 6*totalWeight n=(n:ℝ)*(n-1)*(n+1)) ∧
    (∀ n : ℕ, n ≤ 2 → ∀ u : State,
      ∃ l : List ℤ, follows (greedy n) u l ∧ sorted n (run u l) ∧ l.length ≤ 1) ∧
    (∃ u : State, ∃ g l : List ℤ, (∀ k, ∃ z : ℤ, u k=z) ∧ follows (greedy 4) u g ∧ sorted 4 (run u g) ∧
      follows (legal 4) u l ∧ sorted 4 (run u l) ∧ l.length < g.length) := by
  sorry

end OMA.S_mo_218359
