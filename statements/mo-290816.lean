import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.GCD.Basic

/-!
# Four-part partitions realizing every four-vertex graph

Source: Bernardo Recamán Santos, MathOverflow 290816, January 15, 2018.
https://mathoverflow.net/questions/290816/ (CC BY-SA 3.0).

The six binary digits index the unordered pairs 01, 02, 03, 12, 13, 23.
Every simple labeled graph has exactly one such mask. Taking the minimum
over all permutations gives the same canonical mask exactly for isomorphic graphs.
The four positive parts are the four vertex occurrences of a multiset.
-/

namespace OMA.S_mo_290816

def mask (a b c d : ℕ) : ℕ :=
  (if a.Coprime b then 0 else 1) + (if a.Coprime c then 0 else 2) +
  (if a.Coprime d then 0 else 4) + (if b.Coprime c then 0 else 8) +
  (if b.Coprime d then 0 else 16) + (if c.Coprime d then 0 else 32)

def edgeBit (g i j : ℕ) : ℕ :=
  let a := min i j
  let b := max i j
  let k := if a = 0 then b-1 else if a = 1 then b+1 else 5
  if g.testBit k then 1 else 0

def reordered (g : ℕ) : List ℕ → ℕ
  | [a,b,c,d] => edgeBit g a b + 2*edgeBit g a c + 4*edgeBit g a d +
      8*edgeBit g b c + 16*edgeBit g b d + 32*edgeBit g c d
  | _ => 64

def canonical (g : ℕ) : ℕ :=
  ([0,1,2,3] : List ℕ).permutations'.foldl (fun best p => min best (reordered g p)) 64

def represented (n g : ℕ) : Prop :=
  ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a+b+c+d = n ∧
    canonical (mask a b c d) = canonical g

theorem main : (¬ represented 311 30) ∧ ∀ n : ℕ, 311 < n →
    ∀ g : Fin 64, represented n g.val := by
  sorry

end OMA.S_mo_290816
