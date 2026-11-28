import OMAReductions.R_Erdos848_erdos_848_R1_H2_R1_H2_R1
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Squarefree

/-!
# Three-regime decomposition of Case III.2 (`Erdos848...R1.H4`)

Decomposes the single-odd-residue-class bounds (`160000000 ≤ N`) into three
quantitative prime-counting regimes matching the sibling Erdős 848 reductions:
* `H1` (`160000000 ≤ N < 1500000000`): bounded prime-factor support regime (`ω(b) ≤ 8` for odd `b`).
* `H2` (`1500000000 ≤ N < 2^2300`): intermediate Chebyshev + unitary-divisor regime above `1.5 × 10^9`.
* `H3` (`2^2300 ≤ N`): asymptotic primorial-sparsity regime (`1000 * π(N) ≤ N`).
-/

namespace OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1_H4_R1
open Finset Classical

def H1 : Prop := open scoped Classical in ∀ N : ℕ, 160000000 ≤ N → N < 1500000000 →
  let IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18
  let classCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter P).card
  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card
  let vCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*a+1))).card
  let Witness (b : ℕ) := b ∈ Icc 1 N ∧ ¬ Squarefree (b*b+1)
  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card
  (∀ b r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    classCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7) ∧
  (∀ b b' r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness b' → b' % 25 = 7 → b' % 2 = 0 →
    classCount (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +
    badCount (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount (fun a => a % 25 = 18) b' +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7) ∧
  (∀ b b' r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness b' → b' % 25 = 18 → b' % 2 = 0 →
    classCount (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +
    badCount (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount (fun a => a % 25 = 7) b' +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7)

def H2 : Prop := open scoped Classical in ∀ N : ℕ, 1500000000 ≤ N → N < 2^2300 →
  let IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18
  let classCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter P).card
  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card
  let vCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*a+1))).card
  let Witness (b : ℕ) := b ∈ Icc 1 N ∧ ¬ Squarefree (b*b+1)
  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card
  (∀ b r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    classCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7) ∧
  (∀ b b' r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness b' → b' % 25 = 7 → b' % 2 = 0 →
    classCount (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +
    badCount (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount (fun a => a % 25 = 18) b' +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7) ∧
  (∀ b b' r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness b' → b' % 25 = 18 → b' % 2 = 0 →
    classCount (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +
    badCount (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount (fun a => a % 25 = 7) b' +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7)

def H3 : Prop := open scoped Classical in ∀ N : ℕ, 2^2300 ≤ N →
  let IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18
  let classCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter P).card
  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card
  let vCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*a+1))).card
  let Witness (b : ℕ) := b ∈ Icc 1 N ∧ ¬ Squarefree (b*b+1)
  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card
  (∀ b r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    classCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 4 - r) +
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = r) b +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7) ∧
  (∀ b b' r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness b' → b' % 25 = 7 → b' % 2 = 0 →
    classCount (fun a => a % 25 = 7 ∧ a % 4 = 4 - r) +
    badCount (fun a => a % 25 = 7 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount (fun a => a % 25 = 18) b' +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7) ∧
  (∀ b b' r, Witness b → IsStar b → b % 4 = r → (r = 1 ∨ r = 3) →
    Witness b' → b' % 25 = 18 → b' % 2 = 0 →
    classCount (fun a => a % 25 = 18 ∧ a % 4 = 4 - r) +
    badCount (fun a => a % 25 = 18 ∧ (a % 4 = r ∨ a % 2 = 0)) b +
    badCount (fun a => a % 25 = 7) b' +
    vCount (fun x => IsStar x ∧ x % 4 = r) ≤ c7)

theorem main : H1 → H2 → H3 → OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1.H4 := by
  intro hLow hMid hHigh N hN
  by_cases h1 : N < 1500000000
  · exact hLow N hN h1
  · by_cases h2 : N < 2^2300
    · exact hMid N (Nat.le_of_not_gt h1) h2
    · exact hHigh N (Nat.le_of_not_gt h2)

end OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1_H4_R1
