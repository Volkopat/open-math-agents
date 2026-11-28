import OMAReductions.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1

/- Four disjoint intervals of the published signed within-block sum. -/
-- Credit: @Medrov
namespace OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1_H2_R1
open Finset ArithmeticFunction

def H1 : Prop :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  let f := fun e : Sigma (fun _ : ℕ => ℕ) => -moebius e.1 * (count e.2 ((t e/65536)*65536) (t e%65536+1) : ℤ)
  let pref := fun n : ℕ => ∑ e ∈ S.filter (fun e => t e/65536 < n), f e
  pref 64 = 739593158

def H2 : Prop :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  let f := fun e : Sigma (fun _ : ℕ => ℕ) => -moebius e.1 * (count e.2 ((t e/65536)*65536) (t e%65536+1) : ℤ)
  let pref := fun n : ℕ => ∑ e ∈ S.filter (fun e => t e/65536 < n), f e
  pref 128 - pref 64 = 761685024

def H3 : Prop :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  let f := fun e : Sigma (fun _ : ℕ => ℕ) => -moebius e.1 * (count e.2 ((t e/65536)*65536) (t e%65536+1) : ℤ)
  let pref := fun n : ℕ => ∑ e ∈ S.filter (fun e => t e/65536 < n), f e
  pref 384 - pref 128 = 885026126

def H4 : Prop :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  let f := fun e : Sigma (fun _ : ℕ => ℕ) => -moebius e.1 * (count e.2 ((t e/65536)*65536) (t e%65536+1) : ℤ)
  let pref := fun n : ℕ => ∑ e ∈ S.filter (fun e => t e/65536 < n), f e
  (∑ e ∈ S, f e) - pref 384 = 712675816


theorem main : H1 → H2 → H3 → H4 → OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1.H2 := by
  intro a b c d
  have sum {x y z total : ℤ} (h₁ : x=739593158) (h₂ : y-x=761685024)
      (h₃ : z-y=885026126) (h₄ : total-z=712675816) : total=3098980124 := by omega
  exact sum a b c d

end OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1_H2_R1
