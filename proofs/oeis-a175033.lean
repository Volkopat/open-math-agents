import OMAStatements.S_oeis_a175033
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open OMA.S_oeis_a175033

namespace OMA.A175033

private def Good (x y : ℤ) := 0 ≤ x ∧ 5 ≤ y ∧ 2*y^2 - x^2 = 17

private theorem good_iff (n : ℕ) : P n ↔ ∃ y : ℤ, Good n y := by
  let z : ℝ := (n : ℝ)*n/2
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hs := Real.sq_sqrt hz
  have hpos := Real.sqrt_nonneg z
  constructor
  · intro h
    let y : ℤ := ⌈Real.sqrt z⌉
    have hy := Int.le_ceil (Real.sqrt z)
    have hlt := (Int.ceil_eq_iff.mp (rfl : ⌈Real.sqrt z⌉ = y)).1
    change Real.sqrt z ≤ (y : ℝ) at hy
    change (y : ℝ) - 1 < Real.sqrt z at hlt
    change (y : ℝ)^2 - z = 17/2 at h
    have hy1 : (1:ℝ) ≤ y := by
      by_contra! hc
      nlinarith [mul_nonneg (sub_nonneg.mpr hc.le) (show 0 ≤ (y : ℝ)+1 by linarith)]
    have bound := mul_pos (sub_pos.mpr hlt)
      (show 0 < Real.sqrt z + ((y : ℝ)-1) by linarith)
    have hy5 : (4:ℝ) < y := by nlinarith
    refine ⟨y, by positivity, by exact_mod_cast (show (4:ℤ) < y by exact_mod_cast hy5), ?_⟩
    dsimp [z] at h
    exact_mod_cast (show 2*(y:ℝ)^2 - (n:ℝ)^2 = 17 by nlinarith)
  · rintro ⟨y, hx, hy, he⟩
    have hy' : (5:ℝ) ≤ y := by exact_mod_cast hy
    have he' : 2*(y:ℝ)^2-(n:ℝ)^2=17 := by exact_mod_cast he
    have hyz : (y:ℝ)^2 - z = 17/2 := by dsimp [z]; nlinarith
    have ceilEq : ⌈Real.sqrt z⌉ = y := by
      apply Int.ceil_eq_iff.mpr
      constructor
      · by_contra! hn
        have := mul_nonneg (sub_nonneg.mpr hn)
          (show 0 ≤ (y:ℝ)-1 + Real.sqrt z by linarith)
        nlinarith
      · by_contra! hn
        have := mul_pos (sub_pos.mpr hn) (show 0 < Real.sqrt z + (y:ℝ) by linarith)
        nlinarith
    change ((⌈Real.sqrt z⌉ : ℤ) : ℝ)^2-z=17/2
    simpa [ceilEq] using hyz

private def advance (s : ℤ × ℤ) : ℤ × ℤ := (3*s.1+4*s.2, 2*s.1+3*s.2)

private def orbit : ℕ → ℤ × ℤ
  | 0 => (9,7)
  | 1 => (15,11)
  | k+2 => advance (orbit k)

private theorem valid (k : ℕ) : Good (orbit k).1 (orbit k).2 := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [Good,orbit]
  | one => norm_num [Good,orbit]
  | more k ih _ =>
    obtain ⟨hx,hy,he⟩ := ih
    change Good (3*(orbit k).1+4*(orbit k).2) (2*(orbit k).1+3*(orbit k).2)
    exact ⟨by omega, by omega, by nlinarith only [he]⟩

private theorem ordered (k : ℕ) :
    (orbit k).1 < (orbit (k+1)).1 ∧ (orbit k).2 < (orbit (k+1)).2 := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k ih _ =>
    obtain ⟨hx,hy⟩ := ih
    change 3*(orbit k).1+4*(orbit k).2 < 3*(orbit (k+1)).1+4*(orbit (k+1)).2 ∧
      2*(orbit k).1+3*(orbit k).2 < 2*(orbit (k+1)).1+3*(orbit (k+1)).2
    constructor <;> omega

set_option maxRecDepth 12000 in
private theorem small :
    ∀ x : Fin 55, ∀ y : Fin 40, 5 ≤ y.val →
      2*(y.val : ℤ)^2-(x.val : ℤ)^2=17 →
        (x.val=9 ∧ y.val=7) ∨ (x.val=15 ∧ y.val=11) := by
  decide +kernel

private theorem complete (n : ℕ) (y : ℤ) (h : Good n y) :
    ∃ i, orbit i = ((n:ℤ),y) := by
  induction n using Nat.strong_induction_on generalizing y with
  | h n ih =>
    obtain ⟨hx,hy,he⟩ := h
    by_cases hn : n < 55
    · have hn' : (n:ℤ) ≤ 54 := by omega
      have hyy : y < 40 := by
        by_contra! hb
        nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ 54-n) (by omega : (0:ℤ) ≤ 54+n),
          mul_nonneg (by omega : 0 ≤ y-40) (by omega : 0 ≤ y+40)]
      have sy : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
      have v := small ⟨n,hn⟩ ⟨y.toNat, by omega⟩ (by change 5 ≤ y.toNat; omega) (by simpa only [sy] using he)
      change (n=9 ∧ y.toNat=7) ∨ (n=15 ∧ y.toNat=11) at v
      rcases v with v|v
      · exact ⟨0, Prod.ext (by change (9:ℤ) = n; omega) (by change (7:ℤ) = y; omega)⟩
      · exact ⟨1, Prod.ext (by change (15:ℤ) = n; omega) (by change (11:ℤ) = y; omega)⟩
    · let u : ℤ := 3*n-4*y
      let v : ℤ := 3*y-2*n
      have hn' : (55:ℤ) ≤ n := by omega
      have hu : 0 ≤ u := by
        dsimp [u]
        by_contra! hb
        nlinarith [mul_pos (by omega : (0:ℤ) < 4*y-3*n) (by omega : (0:ℤ) < 4*y+3*n),
          mul_nonneg (by omega : (0:ℤ) ≤ n-55) (by omega : (0:ℤ) ≤ n+55)]
      have hv : 5 ≤ v := by
        dsimp [v]
        by_contra! hb
        nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ 2*n+5-3*y) (by omega : (0:ℤ) ≤ 2*n+5+3*y),
          mul_nonneg (by omega : (0:ℤ) ≤ n-55) (by omega : (0:ℤ) ≤ n+15)]
      have hu' : u < n := by
        dsimp [u]
        by_contra! hb
        nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ n-2*y) (by omega : (0:ℤ) ≤ n+2*y), sq_nonneg y]
      have ue := Int.toNat_of_nonneg hu
      obtain ⟨i,hi⟩ := ih u.toNat (by omega) v
        (by rw [ue]; exact ⟨hu,hv,by dsimp [u,v]; nlinarith only [he]⟩)
      refine ⟨i+2, ?_⟩
      rw [orbit,hi,ue]
      apply Prod.ext <;> dsimp [advance,u,v] <;> ring

private def xs (i : ℕ) := (orbit i).1.toNat

private theorem nth_eq (i : ℕ) : Nat.nth P i = xs i := by
  have strict : StrictMono xs := strictMono_nat_of_lt_succ fun k => by
    have := (ordered k).1
    have := (valid k).1
    dsimp [xs]
    omega
  have hp (k : ℕ) : P (xs k) := (good_iff _).mpr ⟨(orbit k).2, by
    simpa only [xs,Int.toNat_of_nonneg (valid k).1] using valid k⟩
  have cov : ∀ k, P k → k ∈ Set.range xs := by
    intro k hk
    obtain ⟨y,hy⟩ := (good_iff k).mp hk
    obtain ⟨i,hi⟩ := complete k y hy
    exact ⟨i, by simp [xs,hi]⟩
  have inf : (Set.ofPred P).Infinite :=
    (Set.infinite_range_of_injective strict.injective).mono (by rintro _ ⟨k,rfl⟩; exact hp k)
  have eq := Nat.nth_comp_of_strictMono (n:=i) strict cov (fun hf => (inf hf).elim)
  rw [Nat.nth_of_forall (fun k _ => hp k)] at eq
  exact eq.symm

end OMA.A175033

theorem OMA.solution : type_of% @OMA.S_oeis_a175033.main := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n=k+5 := ⟨n-5,by omega⟩
  simp only [a,show k+5-1=k+4 by omega,show k+5-2-1=k+2 by omega,show k+5-4-1=k by omega,
    OMA.A175033.nth_eq,OMA.A175033.xs,Int.toNat_of_nonneg (OMA.A175033.valid _).1]
  change 3*(3*(OMA.A175033.orbit k).1+4*(OMA.A175033.orbit k).2)+
    4*(2*(OMA.A175033.orbit k).1+3*(OMA.A175033.orbit k).2) =
    6*(3*(OMA.A175033.orbit k).1+4*(OMA.A175033.orbit k).2)-(OMA.A175033.orbit k).1
  ring
