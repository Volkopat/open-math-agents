import OMAReductions.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1

/- Four contiguous intervals of the original complete-block sum. -/
-- Credit: @Medrov
namespace OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1_H3_R1
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
  let f := fun b : ℕ => ∑ p ∈ S.image (fun e => e.2),
    (count p (b*65536) 65536 : ℤ) *
      (∑ e ∈ S.filter (fun e => e.2=p ∧ b<(t e)/65536), -moebius e.1)
  (∑ b ∈ range 1024, f b) - (∑ b ∈ range 0, f b) = 1715916613893

def H2 : Prop :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  let f := fun b : ℕ => ∑ p ∈ S.image (fun e => e.2),
    (count p (b*65536) 65536 : ℤ) *
      (∑ e ∈ S.filter (fun e => e.2=p ∧ b<(t e)/65536), -moebius e.1)
  (∑ b ∈ range 5120, f b) - (∑ b ∈ range 1024, f b) = 994685847088

def H3 : Prop :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  let f := fun b : ℕ => ∑ p ∈ S.image (fun e => e.2),
    (count p (b*65536) 65536 : ℤ) *
      (∑ e ∈ S.filter (fun e => e.2=p ∧ b<(t e)/65536), -moebius e.1)
  (∑ b ∈ range 14336, f b) - (∑ b ∈ range 5120, f b) = 508165869103

def H4 : Prop :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  let f := fun b : ℕ => ∑ p ∈ S.image (fun e => e.2),
    (count p (b*65536) 65536 : ℤ) *
      (∑ e ∈ S.filter (fun e => e.2=p ∧ b<(t e)/65536), -moebius e.1)
  (∑ b ∈ range 28740, f b) - (∑ b ∈ range 14336, f b) = 141575259202

theorem main : H1 → H2 → H3 → H4 → OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1.H3 := by
  intro a b c d
  dsimp only [H1, H2, H3, H4, OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1.H3] at *
  simp only [range_zero, sum_empty, sub_zero] at a
  omega

end OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1_H3_R1
