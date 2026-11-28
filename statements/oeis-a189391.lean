import Mathlib

/-!
# Cuts-resistance and the minimum apex of a sum triangle

N. J. A. Sloane's conjecture in https://oeis.org/A189391, with the strict
word transformation of https://oeis.org/A319416 and the row sum of A319420.
-/
namespace OMA.S_oeis_a189391

/-- Keep a bit exactly when it repeats its predecessor. -/
def keepRepeats : Bool → List Bool → List Bool
  | _,[]=>[]
  | a,b::w=>if a=b then b::keepRepeats b w else keepRepeats b w

/-- Delete the first bit of every maximal constant run. -/
def raboter : List Bool → List Bool
  | []=>[]
  | b::w=>keepRepeats b w

def steps : ℕ → List Bool → ℕ
  | 0,_=>0
  | _+1,[]=>0
  | n+1,b::w=>1+steps n (raboter (b::w))

/-- Every nonempty application deletes at least one bit. -/
def resistance (w : List Bool) := steps w.length w

/-- Sum f over all binary words of the indicated length, including leading zeros. -/
def wordSum : ℕ → (List Bool→ℕ) → ℕ
  | 0,f=>f []
  | n+1,f=>wordSum n (fun w=>f (true::w)+f (false::w))

/-- Form n successive rows by summing adjacent entries. Only base indices 0 through n occur. -/
def apex : ℕ → (ℕ→ℕ) → ℕ
  | 0,f=>f 0
  | n+1,f=>apex n (fun i=>f i+f (i+1))

def score (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) : ℕ :=
  apex n (fun i=>if h : i<n+1 then (σ ⟨i,h⟩).val else 0)

theorem main : ∀ n : ℕ,
    IsLeast (Set.range (fun σ : Equiv.Perm (Fin (n+1))=>2*score n σ))
      (wordSum n resistance) := by
  sorry

end OMA.S_oeis_a189391
