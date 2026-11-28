import OMAReductions.R_Erdos848_erdos_848_R1_H2_R1_H2_R1
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Squarefree

/-!
# Three-regime decomposition of Cases II and III.1 (`Erdos848...R1.H3`)

Decomposes the mixed-parity and mixed-odd-residue bounds (`160000000 ≤ N`) into
three quantitative prime-counting regimes matching `Erdos848...R1.H4.R1`:
* `H1` (`160000000 ≤ N < 1500000000`): bounded prime-factor support regime.
* `H2` (`1500000000 ≤ N < 2^2300`): intermediate Chebyshev + unitary-divisor regime above `1.5 × 10^9`.
* `H3` (`2^2300 ≤ N`): asymptotic primorial-sparsity regime (`1000 * π(N) ≤ N`).
-/

namespace OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1_H3_R1
open Finset Classical

def H1 : Prop := open scoped Classical in ∀ N : ℕ, 160000000 ≤ N → N < 1500000000 →
  let IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18
  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card
  let vCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*a+1))).card
  let lemCCount (b : ℕ) := ((Icc 1 N).filter (fun a => IsStar a ∧ ¬ Squarefree (a*a+1) ∧ ¬ Squarefree (a*b+1))).card
  let Witness (b : ℕ) := b ∈ Icc 1 N ∧ ¬ Squarefree (b*b+1)
  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card
  (∀ b, Witness b → IsStar b → b % 2 = 0 →
    badCount (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount b ≤ c7) ∧
  (∀ b₁ b₃, Witness b₁ → IsStar b₁ → b₁ % 4 = 1 → Witness b₃ → IsStar b₃ → b₃ % 4 = 3 →
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
    vCount (fun x => IsStar x ∧ x % 2 = 1) ≤ c7)

def H2 : Prop := open scoped Classical in ∀ N : ℕ, 1500000000 ≤ N → N < 2^2300 →
  let IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18
  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card
  let vCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*a+1))).card
  let lemCCount (b : ℕ) := ((Icc 1 N).filter (fun a => IsStar a ∧ ¬ Squarefree (a*a+1) ∧ ¬ Squarefree (a*b+1))).card
  let Witness (b : ℕ) := b ∈ Icc 1 N ∧ ¬ Squarefree (b*b+1)
  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card
  (∀ b, Witness b → IsStar b → b % 2 = 0 →
    badCount (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount b ≤ c7) ∧
  (∀ b₁ b₃, Witness b₁ → IsStar b₁ → b₁ % 4 = 1 → Witness b₃ → IsStar b₃ → b₃ % 4 = 3 →
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
    vCount (fun x => IsStar x ∧ x % 2 = 1) ≤ c7)

def H3 : Prop := open scoped Classical in ∀ N : ℕ, 2^2300 ≤ N →
  let IsStar (a : ℕ) : Prop := a % 25 ≠ 7 ∧ a % 25 ≠ 18
  let badCount (P : ℕ → Prop) [DecidablePred P] (b : ℕ) := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*b+1))).card
  let vCount (P : ℕ → Prop) [DecidablePred P] := ((Icc 1 N).filter (fun a => P a ∧ ¬ Squarefree (a*a+1))).card
  let lemCCount (b : ℕ) := ((Icc 1 N).filter (fun a => IsStar a ∧ ¬ Squarefree (a*a+1) ∧ ¬ Squarefree (a*b+1))).card
  let Witness (b : ℕ) := b ∈ Icc 1 N ∧ ¬ Squarefree (b*b+1)
  let c7 := ((Icc 1 N).filter (fun a => a%25=7)).card
  (∀ b, Witness b → IsStar b → b % 2 = 0 →
    badCount (fun a => a % 25 = 7 ∨ a % 25 = 18) b + lemCCount b ≤ c7) ∧
  (∀ b₁ b₃, Witness b₁ → IsStar b₁ → b₁ % 4 = 1 → Witness b₃ → IsStar b₃ → b₃ % 4 = 3 →
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) b₁ +
    badCount (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) b₃ +
    vCount (fun x => IsStar x ∧ x % 2 = 1) ≤ c7)

theorem main : H1 → H2 → H3 → OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1.H3 := by
  intro hLow hMid hHigh N hN
  by_cases h1 : N < 1500000000
  · exact hLow N hN h1
  · by_cases h2 : N < 2^2300
    · exact hMid N (Nat.le_of_not_gt h1) h2
    · exact hHigh N (Nat.le_of_not_gt h2)

end OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1_H3_R1
