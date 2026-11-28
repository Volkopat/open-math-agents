import OMAStatements.S_oeis_a343917
import Mathlib

/-!
I prove Zhi-Wei Sun’s infinitude conjecture in OEIS A343917, posed as Question 2
at https://mathoverflow.net/q/391894 in 2021. The solutions constructed here
have odd coprime fourth roots and odd parameter. Scaling solutions of Question 1
by two also solves Question 2 and gives even fourth roots (see PR 26908).
Starting from (55,1), the map (x,y) ↦ (58x−y,x) preserves
x²−58xy+y²=−164. The required parameter is 41xy−116.
Source: https://oeis.org/A343917
Credit: @Aryan-Poonacha
-/
namespace SunQuartic

/-- The difference of the two fourth roots, followed by the smaller root. -/
private def pair : ℕ → ℕ × ℕ
  | 0 => (54,1)
  | n+1 => let (d,y) := pair n; (57*d+56*y,d+y)

private def good (n d y : ℕ) : Prop :=
  n+54 ≤ d ∧ 0<y ∧ d%2=0 ∧ y%2=1 ∧ d.Coprime y ∧
    (d:ℤ)^2+164=56*(y:ℤ)*(d+y)

private theorem step (n d y : ℕ) (h : good n d y) :
    good (n+1) (57*d+56*y) (d+y) := by
  obtain ⟨hd,hy,hpd,hpy,hg,hc⟩ := h
  refine ⟨by omega,by omega,by omega,by omega,?_,?_⟩
  · rw [show 57*d+56*y = d+56*(d+y) by ring]
    simpa using hg
  · push_cast
    linear_combination hc

private theorem all_good (n : ℕ) : good n (pair n).1 (pair n).2 := by
  induction n with
  | zero => unfold good; decide +kernel
  | succ n ih =>
    obtain ⟨d,y,h⟩ : ∃ d y, pair n=(d,y) := ⟨_,_,rfl⟩
    simpa only [pair,h] using step n d y (by simpa [h] using ih)

/-- The solutions have odd parameter and coprime odd fourth roots. -/
theorem primitive (B : ℕ) : ∃ m x y : ℕ, B < m ∧ m%2=1 ∧
    x%2=1 ∧ y%2=1 ∧ x.Coprime y ∧ 2 < |(x:ℤ)-y| ∧
    2*(m:ℤ)^2-2^4=(x:ℤ)^4+(y:ℤ)^4 := by
  obtain ⟨d,y,h⟩ : ∃ d y, pair B=(d,y) := ⟨_,_,rfl⟩
  have hg := all_good B
  rw [h] at hg
  obtain ⟨hd,hy,hpd,hpy,hcop,hc⟩ := hg
  let x := d+y
  have hx : B+55 ≤ x := by dsimp [x];omega
  have hxy : x ≤ x*y := by simpa using Nat.mul_le_mul_left x hy
  let m := 41*x*y-116
  have hm : m+116=41*x*y := by
    dsimp [m]
    apply Nat.sub_add_cancel
    nlinarith
  have hpx : x%2=1 := by dsimp [x];omega
  have hpm : m%2=1 := by
    have hodd : (x*y)%2=1 := by rw [Nat.mul_mod,hpx,hpy]
    rw [show 41*x*y=41*(x*y) by ring] at hm
    omega
  refine ⟨m,x,y,by nlinarith,hpm,hpx,hpy,?_,?_,?_⟩
  · simpa [x] using hcop
  · rw [abs_of_pos (by dsimp [x];omega : (0:ℤ)<x-y)]
    dsimp [x];omega
  · have hmi : (m:ℤ)+116=41*x*y := by exact_mod_cast hm
    have hn : (x:ℤ)^2-58*x*y+y^2+164=0 := by
      dsimp [x]
      linear_combination hc
    rw [show (m:ℤ)=41*x*y-116 by linarith]
    linear_combination -((x:ℤ)^2+y^2+58*x*y-164)*hn

end SunQuartic

theorem OMA.solution : type_of% @OMA.S_oeis_a343917.main := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨m,x,y,hm,_,_,_,_,hgap,he⟩ := SunQuartic.primitive B
  exact ⟨m,⟨by omega,x,y,he,hgap⟩,hm⟩
