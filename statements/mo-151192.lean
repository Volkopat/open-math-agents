import Mathlib

/-!
# Binary search with maximum consecutive lies about is X in subset S?

Source: Borislav Stanimirov, MathOverflow question 151192 (2013).
Credit: @LDJAI

The question asks for the smallest uniform number of survivors for each
positive k. The proposed answer is an explicit finite recurrence, not a
closed-form expression. The age k+1 is absorbing and represents a candidate
already contradicted by k+1 successive answers. The inductive predicate
Wins represents a finite adaptive strategy tree; any impossible response
branch has zero survivors and may stop. Fin N simply reindexes 1,...,N.
-/

namespace OMA.S_mo_151192

/-- Age k+1 denotes an eliminated candidate; it is absorbing. -/
abbrev State (k N : Nat) := Fin N → Fin (k + 2)
abbrev Query (N : Nat) := Fin N → Bool

def initial (k N : Nat) : State k N := fun _ => 0

def update (k : Nat) (a : Fin (k+2)) (truth answer : Bool) : Fin (k+2) :=
  if h : a.val = k+1 then a
  else if truth = answer then 0
  else ⟨a.val+1, by have ha := a.isLt; omega⟩

def move {k N : Nat} (a : State k N) (q : Query N) (b : Bool) : State k N :=
  fun i => update k (a i) (q i) b

def live {k N : Nat} (a : State k N) : Finset (Fin N) :=
  Finset.univ.filter fun i => (a i).val ≤ k

/-- A finite adaptive strategy achieving at most n remaining candidates. -/
inductive Wins (k N n : Nat) : State k N → Prop
  | stop (a) : (live a).card ≤ n → Wins k N n a
  | ask (a) (q : Query N) : Wins k N n (move a q false) →
      Wins k N n (move a q true) → Wins k N n a

/-- Independently evaluated finite backwards search. -/
def table (k N n : Nat) : Nat → State k N → Bool
  | 0, a => decide ((live a).card ≤ n)
  | t+1, a => decide ((live a).card ≤ n) ||
      decide (∃ q : Query N, table k N n t (move a q false) = true ∧
                               table k N n t (move a q true) = true)

def test (k s : Nat) : Bool :=
  table k (s+1) s ((k+2)^(s+1)) (initial k (s+1))

def scan (k : Nat) : Nat → Nat
  | 0 => 0
  | r+1 => let s := scan k r
           if test k s then s else r+1

def answer (k : Nat) : Nat := scan k (2^k)

theorem main : ∀ k : Nat, 0 < k →
    (∀ N : Nat, Wins k N (answer k) (initial k N)) ∧
    ∀ s : Nat, s < answer k → ∃ N : Nat, ¬ Wins k N s (initial k N) := by
  sorry

end OMA.S_mo_151192
