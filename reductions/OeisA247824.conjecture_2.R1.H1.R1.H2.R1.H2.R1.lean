import OMAReductions.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1
import Mathlib.Algebra.BigOperators.Intervals

/-! Split the hard Lagarias–Miller–Odlyzko leaves into the first nine sieve stages,
prefixes inside a 65,536-integer block, and weighted complete blocks.
The parent definition and the signed Möbius convention come from PR #16352. -/

-- Credit: @Medrov
namespace OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1
open Finset ArithmeticFunction

/-- Complete contribution from the nine stages 2 through 23. -/
def H1 : Prop :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  ∑ e ∈ leaves.filter (fun e => e.2≤23), -moebius e.1 *
    (((Icc 1 (x/(e.1*e.2))).filter (fun n => good e.2 n)).card : ℤ) = 692145566297

/-- Within-block prefixes for every remaining edge, including the queried endpoint. -/
def H2 : Prop :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  ∑ e ∈ S, -moebius e.1 * (count e.2 ((t e/65536)*65536) (t e%65536+1) : ℤ) = 3098980124

/-- Each whole block is counted once per sieve stage and weighted by all later queries at that stage. -/
def H3 : Prop :=
  let x := 81744924555066
  let y := 43399
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let leaves := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := leaves.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  ∑ b ∈ range 28740, ∑ p ∈ S.image (fun e => e.2),
    (count p (b*65536) 65536 : ℤ) *
      (∑ e ∈ S.filter (fun e => e.2=p ∧ b<(t e)/65536), -moebius e.1) = 3360343589286

section

private theorem cutoff_interval (P : ℕ → Prop) [DecidablePred P] (t w : ℕ) :
    ((range (t+1)).filter P).card =
      (∑ a ∈ range (t/w), ((range w).filter (fun i => P (a*w+i))).card) +
        ((range (t%w+1)).filter (fun i => P ((t/w)*w+i))).card := by
  let count (lo n : ℕ) := ((range n).filter (fun i => P (lo+i))).card
  have add (lo u v : ℕ) : count lo (u+v) = count lo u + count (lo+u) v := by
    have e := sum_range_add (fun i => if P (lo+i) then (1:ℕ) else 0) u v
    simpa only [Nat.add_assoc,sum_boole,Nat.cast_id,count] using e
  have full (k : ℕ) : count 0 (k*w) = ∑ a ∈ range k, count (a*w) w := by
    induction k with
    | zero => simp [count]
    | succ k ih => rw [Nat.succ_mul,add,ih,Nat.zero_add,sum_range_succ]
  have cover : (t/w)*w+(t%w+1) = t+1 := by
    rw [Nat.mul_comm,← Nat.add_assoc,Nat.div_add_mod]
  have e := add 0 ((t/w)*w) (t%w+1)
  rw [cover,full,Nat.zero_add] at e
  simpa only [count,Nat.zero_add] using e

private theorem prefix_positive (P : ℕ → Bool) (t : ℕ) :
    ((Icc 1 t).filter (fun n => P n)).card = ((range (t+1)).filter (fun n => 0<n ∧ P n)).card := by
  congr 1
  ext n
  simp only [mem_filter,mem_Icc,mem_range,Nat.lt_succ_iff]
  tauto

private theorem weighted_prior_blocks {E : Type*} [DecidableEq E] (queries : Finset E)
    (widthCount : ℕ) (stage block : E → ℕ) (weight : E → ℤ) (size : ℕ → ℕ → ℤ)
    (inside : ∀ e ∈ queries, block e ≤ widthCount) :
    ∑ e ∈ queries, weight e * (∑ a ∈ range (block e), size (stage e) a) =
      ∑ a ∈ range widthCount, ∑ p ∈ queries.image stage, size p a *
        (∑ e ∈ queries.filter (fun e => stage e=p ∧ a<block e), weight e) := by
  classical
  have inner (e : E) (he : e ∈ queries) :
      weight e * (∑ a ∈ range (block e), size (stage e) a) =
      ∑ a ∈ range widthCount, if a < block e then weight e * size (stage e) a else 0 := by
    rw [mul_sum, ← sum_filter]
    congr 1
    ext a
    simp only [mem_range,mem_filter]
    have loc := inside e he
    omega
  calc
    _ = ∑ e ∈ queries, ∑ a ∈ range widthCount,
        if a < block e then weight e * size (stage e) a else 0 :=
      sum_congr rfl inner
    _ = ∑ a ∈ range widthCount, ∑ e ∈ queries,
        if a < block e then weight e * size (stage e) a else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro a _
      rw [← sum_fiberwise_of_maps_to (fun e (he : e ∈ queries) => mem_image_of_mem stage he)]
      apply sum_congr rfl
      intro p _
      rw [mul_sum]
      have combine : queries.filter (fun e => stage e=p ∧ a<block e) =
          (queries.filter (fun e => stage e=p)).filter (fun e => a<block e) := by
        ext e; simp only [mem_filter]; tauto
      rw [combine]
      conv_rhs => rw [sum_filter]
      apply sum_congr rfl
      intro e he
      have loc := (mem_filter.mp he).2
      simp only [loc, mul_comm (weight e) (size p a)]

end

theorem main : H1 → H2 → H3 → OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1.H2 := by
  intro low inners totals
  let x := 81744924555066
  let y := 43399
  let w := 65536
  let E := ((Icc 1 y).filter Squarefree).sigma (fun d => Nat.primesLE (if d=1 then y else d.minFac-1))
  let Eall := (E.filter (fun e => ¬ e.1*e.2 ≤ y)).filter (fun e => e.2^2 ≤ x/(e.1*e.2))
  let S := Eall.filter (fun e => 23<e.2)
  let t := fun e : Sigma (fun _ : ℕ => ℕ) => x/(e.1*e.2)
  let b := fun e => (t e)/w
  let p := fun e : Sigma (fun _ : ℕ => ℕ) => e.2
  let wt := fun e : Sigma (fun _ : ℕ => ℕ) => -moebius e.1
  let good := fun p n : ℕ => ((List.range (p-1+1)).filter (fun q : ℕ => decide q.Prime)).reverse.all (fun q => decide (¬q ∣ n))
  let count := fun p lo n : ℕ => ((range n).filter (fun i => 0<lo+i ∧ good p (lo+i))).card
  let f := fun e => wt e * (((Icc 1 (t e)).filter (fun n => good (p e) n)).card : ℤ)
  let size := fun p a => (count p (a*w) w : ℤ)
  let inner := fun e => wt e * (count (p e) (b e*w) (t e%w+1) : ℤ)
  let before := fun e => wt e * (∑ a ∈ range (b e), size (p e) a)
  have each (e) : f e = before e + inner e := by
    have h := (prefix_positive (good (p e)) (t e)).trans
      (cutoff_interval (fun n => 0<n ∧ good (p e) n) (t e) w)
    have c := congrArg Int.ofNat h
    simpa only [f,before,inner,size,count,b,Nat.cast_add,Nat.cast_sum,mul_add,Int.ofNat_eq_natCast]
      using congrArg (fun z : ℤ => wt e * z) c
  have bounded (e) (mem : e ∈ S) : b e ≤ 28740 := by
    have cross := (mem_filter.mp (mem_filter.mp (mem_filter.mp mem).1).1).2
    change ¬ e.1*e.2 ≤ 43399 at cross
    have lim : 43400 ≤ e.1*e.2 := by omega
    exact (Nat.div_le_div_right (c:=65536) (Nat.div_le_div_left (a:=81744924555066) lim (by decide))).trans (by decide)
  have rearr := weighted_prior_blocks S 28740 p b wt size bounded
  have main_sum : ∑ e ∈ S, f e = (∑ e ∈ S, before e) + (∑ e ∈ S, inner e) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun e _ => each e)
  have full : (∑ e ∈ S, before e) = 3360343589286 := rearr.trans totals
  have part : (∑ e ∈ S, inner e) = 3098980124 := inners
  have small : (∑ e ∈ Eall.filter (fun e => e.2≤23), f e) = 692145566297 := low
  have split := sum_filter_add_sum_filter_not Eall (fun e => e.2≤23) f
  simp only [not_le] at split
  change _ + (∑ e ∈ S, f e) = (∑ e ∈ Eall, f e) at split
  change (∑ e ∈ Eall, f e) = 4055588135707
  exact split.symm.trans (congrArg₂ (·+·) small (main_sum.trans (congrArg₂ (·+·) full part)))

end OMA.R_OeisA247824_conjecture_2_R1_H1_R1_H2_R1_H2_R1
