import OMAStatements.S_oeis_a331124
import Mathlib.Tactic

open OMA.S_oeis_a331124

namespace FibonacciEvaluationCost

private lemma oddCalls (n : ℕ) (hn : 1 ≤ n) :
    calls (2*n+1) = 1+calls n+calls (n+1) := by
  rw [calls]
  simp [show ¬2*n+1≤2 by omega, show (2*n+1)/2=n by omega]

private lemma evenCalls (n : ℕ) (hn : 1 ≤ n) :
    calls (2*n+2) = 1+calls n+calls (n+1)+calls (n+2) := by
  rw [calls]
  simp [show ¬2*n+2≤2 by omega, show (2*n+2)%2=0 by omega, show (2*n+2)/2=n+1 by omega]

private def frame (n p q r s : ℕ) : Prop :=
  p ≤ calls n ∧ q ≤ calls (n+1) ∧ r ≤ calls (n+2) ∧ s ≤ calls (n+3)

private def bump (n : ℕ) := 4*n+4

private lemma advance {n p q r s : ℕ} (hn : 1 ≤ n) (h : frame n p q r s) :
    frame (bump n) (2*p+3*q+2*r) (p+2*q+2*r) (p+3*q+3*r+s) (2*q+2*r+s) := by
  have a := oddCalls n hn
  have b := evenCalls n hn
  have c := oddCalls (n+1) (by omega)
  have d := evenCalls (n+1) (by omega)
  have e := evenCalls (2*n+1) (by omega)
  have f := oddCalls (2*n+2) (by omega)
  have g := evenCalls (2*n+2) (by omega)
  have i := oddCalls (2*n+3) (by omega)
  simp only [frame,bump,Nat.mul_add,←Nat.mul_assoc,Nat.reduceMul,Nat.mul_one,
    Nat.add_assoc,Nat.reduceAdd] at *
  omega

-- Three applications of the same block strictly outgrow the factor 256
-- predicted by the conjecture when the index is scaled by 64.
private lemma triple {n u : ℕ} (hn : 1 ≤ n) (h : frame n (8*u) (6*u) (9*u) (5*u)) :
    frame (bump (bump (bump n))) (8*(u*257)) (6*(u*257)) (9*(u*257)) (5*(u*257)) := by
  have h₁ := advance hn h
  have h₂ := advance (n := bump n) (by unfold bump; omega) h₁
  have h₃ := advance (n := bump (bump n)) (by unfold bump; omega) h₂
  unfold frame at h₃ ⊢
  omega

private def index : ℕ → ℕ
  | 0 => 6
  | k+1 => bump (bump (bump (index k)))

private lemma indexBounds (k : ℕ) : k+1 ≤ index k ∧ index k+2 ≤ 8*64^k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [index,bump,pow_succ]; omega

private lemma weights (k : ℕ) :
    frame (index k) (8*257^k) (6*257^k) (9*257^k) (5*257^k) := by
  induction k with
  | zero =>
    have h₁ : calls 1 = 1 := by rw [calls]; norm_num
    have h₂ : calls 2 = 1 := by rw [calls]; norm_num
    have h₃ := oddCalls 1 (by decide)
    have h₄ := evenCalls 1 (by decide)
    have h₅ := oddCalls 2 (by decide)
    have h₆ := evenCalls 2 (by decide)
    have h₇ := oddCalls 3 (by decide)
    have h₈ := evenCalls 3 (by decide)
    have h₉ := oddCalls 4 (by decide)
    norm_num [index,frame] at *
    omega
  | succ k ih =>
    have lk := (indexBounds k).1
    simpa only [index,pow_succ] using triple (show 1 ≤ index k by omega) ih

private lemma scale (k : ℕ) :
    ((8:ℝ)*64^k)^((4:ℝ)/3) = 16*256^k := by
  have cube (x : ℝ) (hx : 0≤x) : (x^3)^((4:ℝ)/3)=x^4 := by
    rw [←Real.rpow_natCast_mul hx]
    norm_num
  have small : (8:ℝ)^((4:ℝ)/3)=16 := by convert cube 2 (by norm_num) using 1 <;> norm_num
  have large : (64:ℝ)^((4:ℝ)/3)=256 := by convert cube 4 (by norm_num) using 1 <;> norm_num
  rw [Real.mul_rpow (by norm_num) (by positivity), ←Real.rpow_pow_comm (by norm_num : (0:ℝ)≤64),small,large]

private lemma growth (k : ℕ) : 1+(k:ℝ)/256 ≤ ((257:ℝ)/256)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ]
    nlinarith only [mul_le_mul_of_nonneg_right ih (by norm_num : 0≤(257:ℝ)/256),
      show (0:ℝ) ≤ k by positivity]

end FibonacciEvaluationCost

open FibonacciEvaluationCost

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a331124.main) := by
  rintro ⟨C,hC,N,h⟩
  obtain ⟨m,hm⟩ := exists_nat_gt (256*(16*C))
  let k := N+m
  obtain ⟨lb,ub⟩ := indexBounds k
  have nk : N ≤ index k := by dsimp [k] at lb ⊢; omega
  have hi := h (index k) nk
  have idx : (index k:ℝ) ≤ 8*64^k := by
    exact_mod_cast (show index k≤8*64^k by omega)
  have cost := (weights k).1
  have lo : (257:ℝ)^k ≤ calls (index k) := by
    exact_mod_cast (show 257^k≤calls (index k) by omega)
  have mono := Real.rpow_le_rpow (show (0:ℝ) ≤ index k by positivity) idx (by norm_num : (0:ℝ)≤4/3)
  rw [scale] at mono
  have upper : (257:ℝ)^k ≤ 16*C*256^k := by
    calc
      _ ≤ _ := lo.trans hi
      _ ≤ _ := mul_le_mul_of_nonneg_left mono hC.le
      _ = _ := by ring
  have ratio : ((257:ℝ)/256)^k ≤ 16*C := by
    rw [div_pow,div_le_iff₀ (by positivity)]
    exact upper
  have gm := (growth k).trans ratio
  have mk : (m:ℝ) ≤ k := by exact_mod_cast (show m≤k by dsimp [k]; omega)
  linarith
