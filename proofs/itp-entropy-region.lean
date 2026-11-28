import OMAStatements.S_itp_entropy_region
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Monotone

/-!
Disproof of semialgebraicity of the four-variable almost-entropic cone.
YOHSUKE TAKAHASHI, with OpenAI Codex. DFZ Theorem 10 is proved from finite laws.
-/

section
open Finset
namespace EntropyFiniteRows

variable {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y]
variable [DecidableEq X] [DecidableEq Y]
noncomputable def mass (f : Ω → X) (x : X) : ℝ := by
  classical
  exact ((univ.filter fun a => f a = x).card : ℝ) / Fintype.card Ω

/-- Summing the joint masses over complete configurations induces the same
marginal as counting directly in the row space. The restriction map of the
official statement is the special case g(x)=x restricted to the subset. -/
theorem marginal_count (f : Ω → X) (g : X → Y) (y : Y) :
    (∑ x : X, if g x = y then mass f x else 0) = mass (g ∘ f) y := by
  classical
  simp only [mass,Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,Nat.cast_zero]
  simp_rw [Finset.sum_div]
  calc
    _ = ∑ x : X, ∑ a : Ω, if g x = y then (if f a = x then (1:ℝ) else 0) / Fintype.card Ω else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : g x=y <;> simp only [h,if_true,if_false,Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (f a)]
      · by_cases h : g (f a)=y <;> simp [Function.comp_def,h]
      · intro x _ hx
        simp [Ne.symm hx]
      · simp

/-- Equal fibre sizes imply the required uniform probabilities. Zeros off the
support are allowed; C is the support cardinality and F the common fibre size. -/
theorem mass_flat (f : Ω → X) (S : Finset X) (F : ℕ)
    (hcard : Fintype.card Ω = S.card * F) (hF : 0<F)
    (hf : ∀ x, (Finset.univ.filter fun a => f a=x).card = if x∈S then F else 0)
    (x : X) : mass f x = if x∈S then (S.card:ℝ)⁻¹ else 0 := by
  classical
  rw [mass,hf,hcard]
  by_cases h : x∈S
  · simp only [h,if_true,Nat.cast_mul]
    have hf' : (F:ℝ) ≠ 0 := by exact_mod_cast hF.ne'
    have hs' : (S.card:ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨x,h⟩).ne'
    field_simp
  · simp [h]

end EntropyFiniteRows
end

section
namespace EntropySlice

abbrev Weights (R : Type*) := Fin 5 → R

/-- Coordinates of weights are f, l, m, δ=P/4 and v=V. Masks use A=1,B=2,C=4,D=8. -/
def profile {R : Type*} [CommRing R] (w : Weights R) (i : Fin 16) : R :=
  let f := w 0
  let L := w 1 + w 2
  let m := w 2
  let δ := w 3
  let v := w 4
  match i.val with
  | 0 => 0
  | 1 | 2 => 2*f+L
  | 3 => 2*f+2*L+3*δ+v
  | 4 | 8 => f+m
  | 5 | 6 | 9 | 10 => 2*f+L+m
  | 12 => 2*f+2*m-δ
  | 13 | 14 => 2*f+L+2*m-δ
  | _ => 2*f+2*L+m+2*δ+v

def J {R : Type*} [CommRing R] (h : Fin 16 → R) := h 1+h 2-h 3
def V {R : Type*} [CommRing R] (h : Fin 16 → R) :=
  J h - (h 5+h 6-h 4-h 7) - (h 9+h 10-h 8-h 11) - (h 4+h 8-h 12)
def P {R : Type*} [CommRing R] (h : Fin 16 → R) :=
  (h 3+h 6-h 2-h 7)+(h 3+h 5-h 1-h 7)+(h 3+h 10-h 2-h 11)+(h 3+h 9-h 1-h 11)

theorem profile_forms {R : Type*} [CommRing R] (w : Weights R) :
    J (profile w) = 2*w 0-3*w 3-w 4 ∧
    V (profile w) = w 4 ∧ P (profile w) = 4*w 3 := by
  refine ⟨?_,?_,?_⟩ <;> simp [J,V,P,profile] <;> ring

def cell {R : Type*} [Field R] (x y : R) : Weights R := ![1/2,1,1,x*y/4,y]

/-- Properties pulled back from an almost-entropic cone by the linear profile. -/
structure ConeInputs (E : Set (Weights ℝ)) : Prop where
  add : ∀ a ∈ E, ∀ b ∈ E, a+b ∈ E
  scale : ∀ a ∈ E, ∀ c : ℝ, 0 ≤ c → c • a ∈ E
  shared : ![1,0,0,0,0] ∈ E
  privateBits : ![0,1,0,0,0] ∈ E
  parity : ![0,0,1,0,0] ∈ E

theorem neutral_mem {E} (c : ConeInputs E) {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 ≤ m) : ![a,b,m,0,0] ∈ E := by
  have h := c.add _ (c.add _ (c.scale _ c.shared a ha) _ (c.scale _ c.privateBits b hb))
    _ (c.scale _ c.parity m hm)
  convert h using 1
  funext i
  fin_cases i <;> simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul]

theorem pad_ray {E} (c : ConeInputs E) {w : Weights ℝ} (hw : w ∈ E)
    {x : ℝ} (hpos : 0 < w 4) (hray : 4*w 3=x*w 4) :
    ∃ y : ℝ, 0 < y ∧ cell x y ∈ E := by
  let B := 1+|w 0|+|w 1|+|w 2|
  have hB : 0 < B := by dsimp [B]; linarith [abs_nonneg (w 0),abs_nonneg (w 1),abs_nonneg (w 2)]
  let t := 1/(2*B)
  have ht : 0 < t := div_pos zero_lt_one (by linarith)
  have bound (i : Fin 5) (hi : w i ≤ B) : t*w i ≤ 1/2 := by
    dsimp [t]; rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by linarith : 0 < 2*B)).mpr
    linarith
  have h₀ := bound 0 (by dsimp [B]; linarith [le_abs_self (w 0),abs_nonneg (w 1),abs_nonneg (w 2)])
  have h₁ := bound 1 (by dsimp [B]; linarith [abs_nonneg (w 0),le_abs_self (w 1),abs_nonneg (w 2)])
  have h₂ := bound 2 (by dsimp [B]; linarith [abs_nonneg (w 0),abs_nonneg (w 1),le_abs_self (w 2)])
  have hn := neutral_mem c (a:=1/2-t*w 0) (b:=1-t*w 1) (m:=1-t*w 2)
    (by linarith) (by linarith) (by linarith)
  refine ⟨t*w 4,mul_pos ht hpos,?_⟩
  have h := c.add _ (c.scale _ hw t ht.le) _ hn
  convert h using 1
  funext i
  fin_cases i <;> simp [cell,Pi.add_apply,Pi.smul_apply,smul_eq_mul] <;>
    nlinarith [congrArg (t * ·) hray]

/-- The positive and negative tables may be combined and padded to hit each desired ray. -/
theorem hit_ray {E} (c : ConeInputs E) {x : ℝ} (hx : 0 < x)
    {u v : Weights ℝ} (hu : u ∈ E) (hv : v ∈ E) (hup : 0 < u 3) (hvp : 0 < v 3)
    (huv : 4*u 3 < x*u 4) (hvv : x*v 4 < 4*v 3) :
    ∃ y : ℝ, 0 < y ∧ cell x y ∈ E := by
  let a := 4*v 3-x*v 4
  let b := x*u 4-4*u 3
  have ha : 0 < a := sub_pos.mpr hvv
  have hb : 0 < b := sub_pos.mpr huv
  let w := a • u + b • v
  have hw : w ∈ E := c.add _ (c.scale _ hu _ ha.le) _ (c.scale _ hv _ hb.le)
  have hw₃ : 0 < w 3 := add_pos (mul_pos ha hup) (mul_pos hb hvp)
  have hr : 4*w 3=x*w 4 := by dsimp [w,a,b,Pi.add_apply,Pi.smul_apply]; ring
  have hw₄ : 0 < w 4 := by by_contra! hn; nlinarith [mul_nonpos_of_nonneg_of_nonpos hx.le hn]
  exact pad_ray c hw hw₄ hr

/-- On the dyadic ray the symmetrized DFZ bound implies double-exponential thinness.
Only the single DFZ index s=2^n is used for a sample at n. -/
theorem dyadic_cap (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    let s := (2:ℕ)^n
    let T := (2:ℝ)^s
    let x := (1/2:ℝ)^(n+3)
    let h := profile (cell x y)
    (2*T-1)*V h ≤ J h+(((s:ℝ)-1)*T+1)*P h →
      y ≤ (1/2:ℝ)^s := by
  dsimp only
  let s := (2:ℕ)^n
  let T := (2:ℝ)^s
  let x := (1/2:ℝ)^(n+3)
  have hforms := profile_forms (cell x y)
  have hT : 1 ≤ T := one_le_pow₀ (by norm_num)
  have hs : 1 ≤ (s:ℝ) := by exact_mod_cast (Nat.pow_pos (by decide : 0<2) : 0<s)
  have hxy : 0 ≤ x*y := mul_nonneg (pow_nonneg (by norm_num) _) hy
  have hxs : (s:ℝ)*x = 1/8 := by
    dsimp [s,x]; push_cast
    rw [pow_add]
    calc (2:ℝ)^n * ((1/2:ℝ)^n*(1/2:ℝ)^3) = (2*(1/2:ℝ))^n*(1/2:ℝ)^3 := by rw [mul_pow]; ring
         _ = _ := by norm_num
  change (2*T-1)*V (profile (cell x y)) ≤ _ → _
  intro h
  rw [hforms.1,hforms.2.1,hforms.2.2] at h
  simp only [cell,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one] at h
  change (2*T-1)*y ≤ 2*(1/2)-3*(x*y/4)-y+(((s:ℝ)-1)*T+1)*(4*(x*y/4)) at h
  have haux : (((s:ℝ)-1)*T+1)*(x*y) ≤ T*y/8 := calc
    _ ≤ ((s:ℝ)*T)*(x*y) := mul_le_mul_of_nonneg_right (by nlinarith) hxy
    _ = _ := by nlinarith only [congrArg (fun t : ℝ => T*y*t) hxs]
  have hty : T*y ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hT) hy]
  rw [one_div,inv_pow]
  change y ≤ T⁻¹
  rw [← one_div]
  exact (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hT)).mpr (by simpa [mul_comm] using hty)

end EntropySlice
end

section
namespace EntropyThreshold

private theorem overhead (j : ℕ) : 8 * (j+3) + 1 ≤ 2 ^ (2*(j+3)) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [show 2*(j.succ+3) = 2*(j+3)+2 by omega, pow_add]
    norm_num
    omega

private theorem regroup (b d a : ℕ) :
    (2*b)^d * (a*b^2) = b^d * (a*(2^d*b^2)) := by rw [mul_pow]; ring

private theorem exponent_size (h : ℕ) :
    2^(2*h) * (2^(4*h) * (2^(4*h))^2) = (2:ℕ)^(14*h) := by
  rw [← pow_mul, ← pow_add, ← pow_add]
  congr 1
  omega

private theorem r_size (h : ℕ) : ((2:ℕ)^(4*h))^(4*h) = 2^(16*h^2) := by
  rw [← pow_mul]
  congr 1
  ring

private theorem raise_bound (a b n : ℕ) :
    2*((2:ℕ)^a*2^b)^n = 2^((a+b)*n+1) := by
  rw [← pow_add, ← pow_mul, pow_succ, Nat.mul_comm]

set_option maxHeartbeats 900000 in
/-- The explicit digit parameters beat every prescribed integer threshold.
The field size only enters through q ≥ 2 in the final comparison. -/
theorem all_integer_gaps (k q : ℕ) (hq : 2 ≤ q) :
    let h := 4*k+3
    let d := 4*h
    let b := 2^d
    let r := b^d
    let m := (2*b-1)^d * (2*d*(b-1)^2+1)
    q*m^(4*k+2) < (q-1)*r^(4*k+3) := by
  let h := 4*k+3
  let d := 4*h
  let b := 2^d
  let r := b^d
  let m := (2*b-1)^d * (2*d*(b-1)^2+1)
  change q*m^(4*k+2) < (q-1)*r^(4*k+3)
  have hb : 1 ≤ b^2 := Nat.pow_pos (Nat.pow_pos (by decide : 0 < 2))
  have hc : 2*d*(b-1)^2 + 1 ≤ (2*d+1)*b^2 := calc
    _ ≤ 2*d*b^2 + b^2 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le _ _) _)) hb
    _ = _ := by ring
  have hd : 2*d + 1 ≤ 2^(2*h) := by
    rw [show 2*d = 8*h by dsimp only [d]; omega]
    exact overhead (4*k)
  have hm : m ≤ r*2^(14*h) := calc
    m ≤ (2*b)^d * ((2*d+1)*b^2) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le _ _) _) hc
    _ = r * ((2*d+1)*(2^d*b^2)) := regroup b d (2*d+1)
    _ ≤ r * (2^(2*h)*(2^d*b^2)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hd)
    _ = r * 2^(14*h) := congrArg (r * ·) (exponent_size h)
  have hr : r = 2^(16*h^2) := r_size h
  have h1 : 2*m^(4*k+2) < r^(4*k+3) := calc
    _ ≤ 2*(r*2^(14*h))^(4*k+2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
    _ = 2^((16*h^2+14*h)*(4*k+2)+1) := by rw [hr]; exact raise_bound _ _ _
    _ < 2^((16*h^2)*(4*k+3)) := by
      apply Nat.pow_lt_pow_right (by decide : 1 < 2)
      dsimp [h]
      nlinarith
    _ = r^(4*k+3) := by rw [hr,pow_mul]
  calc
    q*m^(4*k+2) ≤ ((q-1)*2)*m^(4*k+2) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = (q-1)*(2*m^(4*k+2)) := Nat.mul_assoc _ _ _
    _ < (q-1)*r^(4*k+3) := Nat.mul_lt_mul_of_pos_left h1 (by omega)

end EntropyThreshold
end

section
open Finset
namespace EntropyPushforward

noncomputable def push {Ω X : Type*} [Fintype Ω] (p : Ω → ℝ) (f : Ω → X) (x : X) : ℝ := by
  classical exact ∑ a, if f a=x then p a else 0

theorem sum_push {Ω X : Type*} [Fintype Ω] [Fintype X] (p : Ω → ℝ) (f : Ω → X) :
    ∑ x, push p f x = ∑ a, p a := by classical simp [push,Finset.sum_comm]

theorem push_nonneg {Ω X : Type*} [Fintype Ω] (p : Ω → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : Ω → X) (x : X) : 0 ≤ push p f x := by
  classical exact Finset.sum_nonneg (fun a _ => by split <;> simp [hp a])

theorem push_comp {Ω X Y : Type*} [Fintype Ω] [Fintype X] (p : Ω → ℝ) (f : Ω → X)
    (g : X → Y) : push (push p f) g = push p (g ∘ f) := by
  classical
  funext y
  change (∑ x : X, if g x=y then push p f x else 0) = _
  calc
    _ = ∑ x : X, ∑ a : Ω, if g x=y then (if f a=x then p a else 0) else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases h : g x=y <;> simp [h,push]
    _ = _ := by
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro a _
      rw [sum_eq_single (f a)]
      · simp [Function.comp_def]
      · intro x _ h; simp [Ne.symm h]
      · simp

theorem push_prod {Ω Ξ X Y : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Ω → ℝ) (q : Ξ → ℝ) (f : Ω → X) (g : Ξ → Y) (x : X) (y : Y) :
    push (fun a : Ω × Ξ => p a.1*q a.2) (Prod.map f g) (x,y) = push p f x*push q g y := by
  classical
  simp only [push,Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases h : f a=x <;> by_cases k : g b=y <;> simp [Prod.map,h,k]

theorem push_injective {X Y : Type*} [Fintype X] (p : X → ℝ) (f : X → Y)
    (hf : Function.Injective f) (a : X) : push p f (f a) = p a := by
  classical simp [push,hf.eq_iff]
theorem push_off_image {X Y : Type*} [Fintype X] (p : X → ℝ) (f : X → Y)
    (y : Y) (hy : y ∉ Set.range f) : push p f y = 0 := by
  classical
  apply sum_eq_zero
  intro a _
  exact if_neg (fun h => hy ⟨a,h⟩)

end EntropyPushforward
end

section
open Polynomial

namespace EntropyPolynomialGraph

/-- Divide out the maximal power of X, retaining the first nonzero coefficient. -/
private theorem stripLow {R : Type*} [CommRing R] {p : R[X]} :
    p ≠ 0 → ∃ (d : ℕ) (a : R) (t : R[X]), a ≠ 0 ∧ p = X^d * (C a + X*t) := by
  induction p using Polynomial.recOnHorner with
  | M0 => simp
  | MC p a hc ha _ =>
    intro _
    refine ⟨0,a,p.divX,ha,?_⟩
    have he := X_mul_divX_add p
    rw [hc,C_0,add_zero] at he
    simp [he,add_comm]
  | MX p hp ih =>
    intro _
    obtain ⟨d,a,t,ha,hd⟩ := ih hp
    refine ⟨d+1,a,t,ha,?_⟩
    rw [hd,pow_succ]
    ring

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem boundedOne (p : K[X]) :
    ∃ M : K, 0 ≤ M ∧ ∀ x : K, 0 ≤ x → x ≤ 1 → |p.eval x| ≤ M := by
  induction p using Polynomial.induction_on' with
  | monomial n a =>
    refine ⟨|a|,abs_nonneg _,?_⟩
    intro x hx hx1
    rw [eval_monomial,abs_mul,abs_of_nonneg (pow_nonneg hx _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hx hx1)
  | add p q hp hq =>
    obtain ⟨M,hM,hm⟩ := hp
    obtain ⟨N,hN,hn⟩ := hq
    exact ⟨M+N,add_nonneg hM hN,fun x hx hx1 => by
      rw [eval_add]
      exact (abs_add_le ..).trans (add_le_add (hm _ hx hx1) (hn _ hx hx1))⟩

/-- Inner variable X is evaluated at x, outer variable Y at y. -/
noncomputable def value (p : (K[X])[X]) (x y : K) : K := (p.eval (C y)).eval x

private theorem boundedTwo (p : (K[X])[X]) :
    ∃ M : K, 0 ≤ M ∧ ∀ x y : K, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → |value p x y| ≤ M := by
  induction p using Polynomial.induction_on' with
  | monomial n a =>
    obtain ⟨M,hM,hm⟩ := boundedOne a
    refine ⟨M,hM,?_⟩
    intro x y hx hx1 hy hy1
    simp only [value,eval_monomial,eval_mul,eval_pow,eval_C,abs_mul,abs_of_nonneg (pow_nonneg hy n)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hy hy1)).trans (hm _ hx hx1)
  | add p q hp hq =>
    obtain ⟨M,hM,hm⟩ := hp
    obtain ⟨N,hN,hn⟩ := hq
    refine ⟨M+N,add_nonneg hM hN,?_⟩
    intro x y hx hx1 hy hy1
    simp only [value, eval_add]
    exact (abs_add_le ..).trans (add_le_add (hm _ _ hx hx1 hy hy1) (hn _ _ hx hx1 hy hy1))

/-- S contains positive points below every prescribed power near the origin. -/
def HasFlatPoints (S : Set (K × K)) : Prop :=
  ∀ (d : ℕ) (ε : K), 0 < ε → ∃ x y : K, (x,y) ∈ S ∧
    0 < x ∧ x ≤ 1 ∧ x < ε ∧ 0 < y ∧ y ≤ 1 ∧ y < ε*x^d

/-- The graph obtained by the substitution x=1/z in the cone argument
cannot lie in the zero set of any nonzero bivariate polynomial. -/
theorem flat_points_escape_polynomial {S : Set (K × K)} (hs : HasFlatPoints S)
    {p : (K[X])[X]} (hp : p ≠ 0) :
    ∃ x y : K, (x,y) ∈ S ∧ value p x y ≠ 0 := by
  obtain ⟨j,a,B,ha,hpform⟩ := stripLow hp
  obtain ⟨d,c,T,hc,haform⟩ := stripLow ha
  obtain ⟨M,hM,hT⟩ := boundedOne T
  obtain ⟨N,hN,hB⟩ := boundedTwo B
  let ε := |c| / (M+N+1)
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have hden : 0 < M+N+1 := by linarith
  have heps : 0 < ε := div_pos hcpos hden
  have hsmall : ε*(M+N) < |c| := by
    have h : ε*(M+N+1) = |c| := div_mul_cancel₀ _ hden.ne'
    linarith only [heps,h,show ε*(M+N+1)=ε*(M+N)+ε by ring]
  obtain ⟨x,y,hxy,hx,hx1,hxe,hy,hy1,hflat⟩ := hs d ε heps
  refine ⟨x,y,hxy,?_⟩
  intro hz
  rw [hpform] at hz
  simp only [value,eval_mul,eval_pow,eval_X,eval_add,eval_C] at hz
  have hzero := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hy.ne')
  rw [haform] at hzero
  simp only [eval_mul,eval_pow,eval_X,eval_add,eval_C] at hzero
  have hxd := pow_pos hx d
  have hq : y/x^d < ε := (div_lt_iff₀ hxd).mpr hflat
  have hq0 : 0 ≤ y/x^d := (div_pos hy hxd).le
  have hcancel : c = -(x*T.eval x + (y/x^d)*value B x y) := by
    apply (mul_right_cancel₀ hxd.ne')
    dsimp [value]
    field_simp [hxd.ne']
    nlinarith only [hzero]
  have hbad : |c| ≤ ε*(M+N) := calc
    |c| = |x*T.eval x + (y/x^d)*value B x y| := by
      calc |c| = |-(x*T.eval x + (y/x^d)*value B x y)| := congrArg abs hcancel
           _ = _ := abs_neg _
    _ ≤ |x*T.eval x| + |(y/x^d)*value B x y| := abs_add_le ..
    _ = x*|T.eval x| + (y/x^d)*|value B x y| := by rw [abs_mul,abs_mul,abs_of_pos hx,abs_of_nonneg hq0]
    _ ≤ ε*M+ε*N := add_le_add
      (mul_le_mul hxe.le (hT _ hx.le hx1) (abs_nonneg _) heps.le)
      (mul_le_mul hq.le (hB _ _ hx.le hx1 hy.le hy1) (abs_nonneg _) heps.le)
    _ = _ := by ring
  exact (not_lt_of_ge hbad) hsmall


/-- A dyadic version of exponential flatness, with no logarithms or limits.
For the normalized graph choose z=2^(n+3), x=1/z and y=g(z). -/
theorem dyadic_points_are_flat [Archimedean K] {S : Set (K × K)}
    (samples : ∀ n : ℕ, ∃ y : K, (((1/2 : K)^(n+3)),y) ∈ S ∧
      0 < y ∧ y ≤ (1/2 : K)^(2^n : ℕ)) : HasFlatPoints S := by
  intro d ε he
  let b : K := 1/2
  have hb : 0 < b := by dsimp [b]; norm_num
  have hb1 : b < 1 := by dsimp [b]; norm_num
  obtain ⟨u,hu⟩ := exists_pow_lt_of_lt_one he hb1
  let t := 3*d+u+10
  let n := 2*t
  have hun : u ≤ n+3 := by dsimp [n,t]; omega
  have hn : u+(n+3)*d ≤ 2^n := calc
    _ ≤ (t+1)*(t+1) := by dsimp [n,t]; nlinarith
    _ ≤ (2^t)*(2^t) := Nat.mul_le_mul Nat.lt_two_pow_self Nat.lt_two_pow_self
    _ = 2^n := by rw [← pow_add]; dsimp only [n]; congr 1; omega
  obtain ⟨y,hs,hy,hyb⟩ := samples n
  refine ⟨b^(n+3),y,hs,pow_pos hb _,pow_le_one₀ hb.le hb1.le,?_,hy,?_,?_⟩
  · exact (pow_le_pow_of_le_one hb.le hb1.le hun).trans_lt hu
  · exact hyb.trans (pow_le_one₀ hb.le hb1.le)
  · calc
      y ≤ b^(2^n : ℕ) := hyb
      _ ≤ b^(u+(n+3)*d) := pow_le_pow_of_le_one hb.le hb1.le hn
      _ = b^u*(b^(n+3))^d := by rw [pow_add,pow_mul]
      _ < ε*(b^(n+3))^d := mul_lt_mul_of_pos_right hu (pow_pos (pow_pos hb _) _)

/-- The non-algebraicity step with the bound needed from the entropy estimate. -/
theorem dyadic_samples_escape_polynomial [Archimedean K] {S : Set (K × K)}
    (samples : ∀ n : ℕ, ∃ y : K, (((1/2 : K)^(n+3)),y) ∈ S ∧
      0 < y ∧ y ≤ (1/2 : K)^(2^n : ℕ))
    {p : (K[X])[X]} (hp : p ≠ 0) :
    ∃ x y : K, (x,y) ∈ S ∧ value p x y ≠ 0 :=
  flat_points_escape_polynomial (dyadic_points_are_flat samples) hp


private theorem pos_near (p : (K[X])[X]) {x y : K}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hp : 0 < value p x y) :
    ∃ e : K, 0 < e ∧ ∀ δ : K, 0 < δ → δ < e → 0 < value p x (y+δ) := by
  let q := p.comp (X + C (C y))
  obtain ⟨M,hM,hm⟩ := boundedTwo q.divX
  have ht (δ : K) : value q x δ = value p x (y+δ) := by
    simp [value,q,eval_comp,map_add,add_comm]
  have he (δ : K) : value q x δ = δ * value q.divX x δ + (q.coeff 0).eval x := by
    conv_lhs => rw [← X_mul_divX_add q]
    simp only [value,eval_add,eval_mul,eval_X,eval_C]
  have hconst : (q.coeff 0).eval x = value p x y := by
    have h1 := he 0
    rw [ht] at h1
    simpa using h1.symm
  have hd : 0 < M+1 := by linarith
  refine ⟨min 1 (value p x y/(M+1)),lt_min zero_lt_one (div_pos hp hd),?_⟩
  intro δ hδ hδe
  have hδ1 := (lt_min_iff.mp hδe).1.le
  have hδm := (lt_div_iff₀ hd).mp (lt_min_iff.mp hδe).2
  have hlow := (abs_le.mp (hm x δ hx hx1 hδ.le hδ1)).1
  rw [← ht,he,hconst]
  nlinarith only [hδm,hδ,mul_le_mul_of_nonneg_left hlow hδ.le]

private theorem pos_list (qs : List ((K[X])[X])) {x y : K}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hq : ∀ p ∈ qs, 0 < value p x y) :
    ∃ e : K, 0 < e ∧ ∀ δ : K, 0 < δ → δ < e → ∀ p ∈ qs, 0 < value p x (y+δ) := by
  induction qs with
  | nil => exact ⟨1,zero_lt_one,by simp⟩
  | cons p qs ih =>
    obtain ⟨e,he,hep⟩ := pos_near p hx hx1 (hq p (by simp))
    obtain ⟨f,hf,hfq⟩ := ih (fun q hq' => hq q (by simp [hq']))
    refine ⟨min e f,lt_min he hf,?_⟩
    intro δ hδ hδef q hq'
    rcases List.mem_cons.mp hq' with rfl | h
    · exact hep δ hδ (lt_min_iff.mp hδef).1
    · exact hfq δ hδ (lt_min_iff.mp hδef).2 q h

/-- Every nonzero polynomial in a finite list is nonvanishing wherever this
single nonzero product is nonvanishing. Identically zero tests are skipped. -/
private theorem avoid_list (ps : List ((K[X])[X])) :
    ∃ p : (K[X])[X], p ≠ 0 ∧ ∀ x y, value p x y ≠ 0 →
      ∀ q ∈ ps, q ≠ 0 → value q x y ≠ 0 := by
  classical
  induction ps with
  | nil => exact ⟨1,one_ne_zero,by simp⟩
  | cons q qs ih =>
    obtain ⟨p,hp,hs⟩ := ih
    by_cases hq : q = 0
    · exact ⟨p,hp,fun x y hv t ht hne => by
        rcases List.mem_cons.mp ht with rfl | h
        · exact (hne hq).elim
        · exact hs x y hv t h hne⟩
    · refine ⟨q*p,mul_ne_zero hq hp,?_⟩
      intro x y hv t ht hne
      have hmult : value q x y * value p x y ≠ 0 := by simpa [value] using hv
      rcases List.mem_cons.mp ht with rfl | h
      · exact left_ne_zero_of_mul hmult
      · exact hs x y (right_ne_zero_of_mul hmult) t h hne

/-- Finite unions of basic sets defined by polynomial equalities and strict
positivities. The polynomials are in K[X][Y]. -/
def HasPlaneDescription (S : Set (K × K)) : Prop :=
  ∃ pieces : List (List ((K[X])[X]) × List ((K[X])[X])), ∀ x y,
    (x,y) ∈ S ↔ ∃ w ∈ pieces,
      (∀ p ∈ w.1, value p x y = 0) ∧ (∀ q ∈ w.2, 0 < value q x y)

/-- No single-valued planar set with the dyadic samples furnished by the
stability estimate admits a finite basic semialgebraic description. -/
theorem dyadic_graph_not_semialgebraic [Archimedean K] {S : Set (K × K)}
    (single : ∀ x y z, (x,y) ∈ S → (x,z) ∈ S → y = z)
    (samples : ∀ n : ℕ, ∃ y : K, (((1/2 : K)^(n+3)),y) ∈ S ∧
      0 < y ∧ y ≤ (1/2 : K)^(2^n : ℕ)) : ¬ HasPlaneDescription S := by
  rintro ⟨pieces,desc⟩
  let S' : Set (K × K) := {u | u ∈ S ∧ 0 ≤ u.1 ∧ u.1 ≤ 1}
  have samples' (n : ℕ) : ∃ y : K, (((1/2 : K)^(n+3)),y) ∈ S' ∧
      0 < y ∧ y ≤ (1/2 : K)^(2^n : ℕ) := by
    obtain ⟨y,h,hy,hyb⟩ := samples n
    exact ⟨y,⟨h,pow_nonneg (by norm_num) _,pow_le_one₀ (by norm_num) (by norm_num)⟩,hy,hyb⟩
  obtain ⟨p,hp,havoid⟩ := avoid_list (pieces.flatMap Prod.fst)
  obtain ⟨x,y,⟨hs,hx,hx1⟩,hv⟩ := dyadic_samples_escape_polynomial samples' hp
  obtain ⟨w,hw,heq,hpos⟩ := (desc x y).mp hs
  have hz : ∀ q ∈ w.1, q = 0 := by
    intro q hq
    by_contra hne
    exact (havoid x y hv q (List.mem_flatMap.mpr ⟨w,hw,hq⟩) hne) (heq q hq)
  obtain ⟨e,he,hnear⟩ := pos_list w.2 hx hx1 hpos
  have h1 : 0 < e/2 := by linarith
  have h2 : e/2 < e := by linarith
  have hother : (x,y+e/2) ∈ S := (desc _ _).mpr
    ⟨w,hw,fun q hq => by simp [hz q hq,value],hnear _ h1 h2⟩
  have := single _ _ _ hs hother
  linarith


/-- Boundary points of a basic description must be on its equation loci
when the only allowed one-sided motion is in the vertical direction. Only
the original set, not the set of its fibre maxima, needs a description. -/
theorem capped_fibres_not_semialgebraic [Archimedean K] {S : Set (K × K)}
    (samples : ∀ n : ℕ, let x := (1/2 : K)^(n+3)
      ∃ y : K, (x,y) ∈ S ∧ 0 < y ∧ y ≤ (1/2 : K)^(2^n : ℕ) ∧
        ∀ t, (x,t) ∈ S → t ≤ y) : ¬ HasPlaneDescription S := by
  rintro ⟨pieces,desc⟩
  let T : Set (K × K) := {u | u ∈ S ∧ 0 ≤ u.1 ∧ u.1 ≤ 1 ∧ ∀ t, (u.1,t) ∈ S → t ≤ u.2}
  have sam (n : ℕ) : ∃ y : K, (((1/2 : K)^(n+3)),y) ∈ T ∧
      0 < y ∧ y ≤ (1/2 : K)^(2^n : ℕ) := by
    obtain ⟨y,h,hp,hb,hm⟩ := samples n
    exact ⟨y,⟨h,pow_nonneg (by norm_num) _,pow_le_one₀ (by norm_num) (by norm_num),hm⟩,hp,hb⟩
  obtain ⟨p,hp,havoid⟩ := avoid_list (pieces.flatMap Prod.fst)
  obtain ⟨x,y,⟨hxy,hx,hx1,htop⟩,hv⟩ := dyadic_samples_escape_polynomial sam hp
  obtain ⟨w,hw,heq,hpos⟩ := (desc x y).mp hxy
  have hz (q) (hq : q ∈ w.1) : q = 0 := by
    by_contra hne
    exact (havoid x y hv q (List.mem_flatMap.mpr ⟨w,hw,hq⟩) hne) (heq q hq)
  obtain ⟨e,he,hnear⟩ := pos_list w.2 hx hx1 hpos
  have h₁ : 0 < e/2 := by linarith
  have h₂ : e/2 < e := by linarith
  have hother : (x,y+e/2) ∈ S := (desc _ _).mpr
    ⟨w,hw,fun q hq => by simp [hz q hq,value],hnear _ h₁ h₂⟩
  have := htop _ hother
  linarith

end EntropyPolynomialGraph
end

section
open Finset EntropyFiniteRows EntropySlice
namespace EntropyCounts

noncomputable def bits (n : ℕ) := Real.log n / Real.log 2

/-- Entropy of a uniform marginal, including all zero-mass configurations. -/
theorem flat_entropy {Y : Type*} [Fintype Y] [DecidableEq Y]
    (S : Finset Y) (hS : 0 < S.card) :
    (∑ y : Y, let p := if y∈S then (S.card : ℝ)⁻¹ else 0; -p*Real.log p)/Real.log 2
    = bits S.card := by
  classical
  have hn : (S.card:ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  have hterm (y : Y) :
      (let p := if y∈S then (S.card : ℝ)⁻¹ else 0; -p*Real.log p) =
      if y∈S then (S.card:ℝ)⁻¹*Real.log S.card else 0 := by
    by_cases hy : y∈S <;> simp [hy,Real.log_inv]
  simp_rw [hterm]
  simp [bits,Finset.sum_ite_mem, nsmul_eq_mul,← mul_assoc,hn]

noncomputable def weights (d q m : ℕ) : Weights ℝ :=
  ![(d:ℝ)*bits q,bits q-bits m,bits m,bits m-bits (d+1),
    bits (q-1)-bits q+3*bits (d+1)-2*bits m]

/-- d=r-1. All joint support orders, indexed by the mask of the marginal. -/
def supportCard (d q m : ℕ) (i : Fin 16) : ℕ :=
  let N := q^(2*d+1)
  match i.val with
  | 0 => 1
  | 1 | 2 => N
  | 3 => N*m*(q-1)
  | 4 | 8 => m*q^d
  | 5 | 6 | 9 | 10 => N*m
  | 12 => m*(d+1)*q^(2*d)
  | 13 | 14 => N*m*(d+1)
  | _ => N*m*(d+1)*(q-1)

theorem support_profile (d q m : ℕ) (hq : 2 ≤ q) (hm : 0 < m) (i : Fin 16) :
    bits (supportCard d q m i) = profile (weights d q m) i := by
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast (by omega : q≠0)
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have ht' : ((q-1:ℕ):ℝ) ≠ 0 := by exact_mod_cast (by omega : q-1≠0)
  have hr' : ((d+1:ℕ):ℝ) ≠ 0 := by exact_mod_cast (by omega : d+1≠0)
  have hr'' : (d:ℝ)+1 ≠ 0 := by exact_mod_cast (by omega : d+1≠0)
  fin_cases i <;> simp [supportCard,profile,weights,bits,Nat.cast_sub (show 1≤q by omega),
    Real.log_mul,Real.log_pow,hq',hm',ht',hr',hr'',sub_ne_zero.mpr (show (q:ℝ)≠1 by exact_mod_cast (by omega : q≠1))] <;> ring

/-- This conclusion uses the sixteen marginal entropies, with no MI assumptions. -/
theorem information_of_counts (d q m : ℕ) (hq : 2 ≤ q) (hm : 0 < m)
    (h : Fin 16 → ℝ) (counts : ∀ i, h i = bits (supportCard d q m i)) :
    V h = bits (q-1)-bits q+3*bits (d+1)-2*bits m ∧ P h=4*(bits m-bits (d+1)) := by
  have e : h=profile (weights d q m) := funext (fun i => (counts i).trans (support_profile _ _ _ hq hm i))
  rw [e]
  exact (profile_forms _).2

end EntropyCounts
end

section
open Finset
namespace EntropyFixtures

def code (S : Finset (Fin 4)) : Fin 16 := Fin.ofNat 16 (∑ i ∈ S, 2^i.val)
def decode (k : Fin 16) := univ.filter fun i : Fin 4 => k.val.testBit i.val
theorem decode_code : ∀ S : Finset (Fin 4), decode (code S) = S := by decide +kernel
theorem code_decode : ∀ i : Fin 16, code (decode i) = i := by decide +kernel

-- A sample is encoded by its low bits. Every variable has alphabet Fin 32.
def row (t : Fin 4) (a : Fin (if t=3 then 32 else 8)) (i : Fin 4) : Fin 32 :=
  let z := a.val
  let k := match t.val with
    | 0 => match i.val with | 0 | 1 => z%4 | 2 => z%2 | _ => (z/2)%2
    | 1 => match i.val with | 0 => z%2 | 1 => (z/2)%2 | _ => 0
    | 2 => match i.val with | 0 => z%2 | 1 => (z/2)%2 | 2 => (z/4)%2
                            | _ => (z%2+(z/2)%2+(z/4)%2)%2
    | _ => z &&& (![3,12,21,26] i : ℕ)
  Fin.ofNat 32 k

def view (t : Fin 4) (S : Finset (Fin 4)) (a : Fin (if t=3 then 32 else 8)) :=
  fun i : S => row t a i.1

-- Integer entropies in bits for each projected table. The order of masks is ABCD low-to-high.
def rank (t : Fin 4) (i : Fin 16) : ℕ :=
  match t.val with
  | 0 => ![0,2,2,2,1,2,2,2,1,2,2,2,2,2,2,2] i
  | 1 => ![0,1,1,2,0,1,1,2,0,1,1,2,0,1,1,2] i
  | 2 => ![0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,3] i
  | _ => ![0,2,2,4,3,4,4,5,3,4,4,5,5,5,5,5] i

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
/-- Exact finite enumeration of four small models, including all nonempty fibres. -/
theorem counts : ∀ (t : Fin 4) (S : Finset (Fin 4)),
    (univ.image (view t S)).card = 2^(rank t (code S)) ∧
    ∀ a, (univ.filter fun b => view t S b = view t S a).card * 2^(rank t (code S)) =
      (if t=3 then 32 else 8) := by decide +kernel

def wt (t : Fin 4) (j : Fin 5) : ℝ :=
  match t.val,j.val with
  | 0,0 | 1,1 | 2,2 | 3,0 | 3,3 => 1
  | 3,1 => -2
  | 3,2 => 2
  | 3,4 => -1
  | _,_ => 0

theorem rank_profile (t : Fin 4) (i : Fin 16) :
    (rank t i : ℝ) = EntropySlice.profile (wt t) i := by
  fin_cases t <;> fin_cases i <;> dsimp [rank,wt,EntropySlice.profile,Matrix.cons_val] <;> norm_num

end EntropyFixtures
end

section
open Finset EntropyPushforward Real
namespace EntropyOperations

noncomputable def ent {X : Type*} [Fintype X] (p : X → ℝ) : ℝ :=
  (∑ x, negMulLog (p x))/log 2
noncomputable def obs {Ω X : Type*} [Fintype Ω] [Fintype X] (p : Ω → ℝ) (f : Ω → X) : ℝ :=
  ent (push p f)

theorem ent_inj {X Y : Type*} [Fintype X] [Fintype Y] (p : X → ℝ) (f : X → Y)
    (hf : Function.Injective f) : ent (push p f) = ent p := by
  classical
  unfold ent
  congr 1
  calc
    _ = ∑ y ∈ univ.image f, negMulLog (push p f y) := by
      symm
      apply sum_subset (subset_univ _)
      intro y _ hy
      have h : y ∉ Set.range f := by simpa using hy
      simp [push_off_image p f y h]
    _ = _ := by rw [sum_image (fun _ _ _ _ h => hf h)]; simp [push_injective p f hf]

theorem obs_inj {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y] (p : Ω → ℝ)
    (f : Ω → X) (g : X → Y) (hg : Function.Injective g) : obs p (g ∘ f) = obs p f := by
  simpa only [obs,← push_comp] using ent_inj (push p f) g hg

theorem ent_prod {X Y : Type*} [Fintype X] [Fintype Y] (p : X → ℝ) (q : Y → ℝ)
    (hp : ∑ x,p x=1) (hq : ∑ y,q y=1) :
    ent (fun a : X × Y => p a.1*q a.2) = ent p + ent q := by
  unfold ent
  rw [← add_div]
  congr 1
  simp only [Fintype.sum_prod_type,negMulLog_mul,Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul,← Finset.mul_sum,hq,one_mul,← Finset.sum_mul,hp,one_mul]

theorem obs_prod {Ω Ξ X Y : Type*} [Fintype Ω] [Fintype Ξ] [Fintype X] [Fintype Y]
    (p : Ω → ℝ) (q : Ξ → ℝ) (hp : ∑ a,p a=1) (hq : ∑ b,q b=1)
    (f : Ω → X) (g : Ξ → Y) :
    obs (fun a : Ω × Ξ => p a.1*q a.2) (Prod.map f g) = obs p f+obs q g := by
  unfold obs
  have e : push (fun a : Ω × Ξ => p a.1*q a.2) (Prod.map f g) =
      fun z => push p f z.1 * push q g z.2 := funext fun ⟨x,y⟩ => push_prod p q f g x y
  rw [e]
  exact ent_prod _ _ ((sum_push p f).trans hp) ((sum_push q g).trans hq)

/-- Add a single common tag shared by all the nonempty marginals. -/
noncomputable def flagged {Ω : Type*} (t : ℝ) (p : Ω → ℝ) : Ω ⊕ Unit → ℝ :=
  Sum.elim (fun a => t*p a) (fun _ => 1-t)
noncomputable def tag (t : ℝ) := (negMulLog t+negMulLog (1-t))/log 2

theorem sum_flagged {Ω : Type*} [Fintype Ω] (t : ℝ) (p : Ω → ℝ) (hp : ∑ a,p a=1) :
    ∑ a,flagged t p a = 1 := by
  simp [flagged,Fintype.sum_sum_type,← Finset.mul_sum,hp]

theorem obs_flagged {Ω X : Type*} [Fintype Ω] [Fintype X] (p : Ω → ℝ)
    (hp : ∑ a,p a=1) (f : Ω → X) (t : ℝ) :
    obs (flagged t p) (Sum.map f (id : Unit → Unit)) = t*obs p f+tag t := by
  classical
  have e : push (flagged t p) (Sum.map f (id : Unit → Unit)) = flagged t (push p f) := by
    funext z
    cases z with
    | inr z => simp [push,Fintype.sum_sum_type,flagged]
    | inl x =>
      simp [push,Fintype.sum_sum_type,flagged,Finset.mul_sum,mul_ite]
  unfold obs ent tag
  rw [e]
  simp only [Fintype.sum_sum_type,flagged,Sum.elim_inl,Sum.elim_inr,negMulLog_mul,
    sum_add_distrib,Fintype.univ_punit,Finset.sum_singleton]
  simp_rw [← Finset.sum_mul,← Finset.mul_sum,sum_push,hp,one_mul]
  ring

end EntropyOperations
end

section
open Polynomial EntropyPolynomialGraph EntropySlice
namespace EntropyPullback

/-- This is the defining expression of the official IsSemialgebraic predicate. -/
def BasicDescription {ι : Type*} (A : Set (ι → ℝ)) : Prop :=
  ∃ (m : ℕ) (r s : Fin m → ℕ)
    (P : (i : Fin m) → Fin (r i) → MvPolynomial ι ℝ)
    (Q : (i : Fin m) → Fin (s i) → MvPolynomial ι ℝ),
    A = ⋃ i : Fin m, {x | (∀ j : Fin (r i), MvPolynomial.eval x (P i j) = 0) ∧
                            (∀ l : Fin (s i), 0 < MvPolynomial.eval x (Q i l))}

abbrev Bi := (ℝ[X])[X]
noncomputable def constants : ℝ →+* Bi := C.comp C
noncomputable def atPoint (x y : ℝ) : Bi →+* ℝ := (evalRingHom x).comp (evalRingHom (C y))
private theorem atPoint_eq (x y : ℝ) (p : Bi) : atPoint x y p = value p x y := rfl

theorem preimage {ι : Type*} (A : Set (ι → ℝ)) (φ : ι → Bi) (hA : BasicDescription A) :
    HasPlaneDescription {u : ℝ × ℝ | (fun i => value (φ i) u.1 u.2) ∈ A} := by
  classical
  obtain ⟨m,r,s,P,Q,hA⟩ := hA
  let liftP : MvPolynomial ι ℝ →+* Bi := MvPolynomial.eval₂Hom constants φ
  have he (x y : ℝ) (p : MvPolynomial ι ℝ) :
      value (liftP p) x y = MvPolynomial.eval (fun i => value (φ i) x y) p := by
    change atPoint x y (MvPolynomial.eval₂Hom constants φ p) = _
    rw [MvPolynomial.map_eval₂Hom]
    have hh : (atPoint x y).comp constants = RingHom.id ℝ := by
      ext t; simp [atPoint,constants]
    rw [hh]
    rfl
  refine ⟨List.ofFn (fun i : Fin m => (List.ofFn fun j => liftP (P i j),
                                          List.ofFn fun j => liftP (Q i j))),?_⟩
  intro x y
  simp only [Set.mem_setOf_eq,hA,Set.mem_iUnion,List.mem_ofFn,exists_exists_eq_and,
    forall_exists_index,forall_apply_eq_imp_iff,he]

noncomputable def polyWeights : Weights Bi :=
  ![constants (1/2),1,1,constants (1/4)*C X*X,X]

theorem weights_at (x y : ℝ) (j : Fin 5) : atPoint x y (polyWeights j) = cell x y j := by
  fin_cases j <;> simp [atPoint,polyWeights,constants,cell] <;> ring

theorem profile_at (x y : ℝ) (k : Fin 16) :
    value (profile polyWeights k) x y = profile (cell x y) k := by
  change atPoint x y (profile polyWeights k) = _
  fin_cases k <;> simp [profile,weights_at,map_ofNat]

/-- Polynomial substitution of the fixed slice into an arbitrary finite family
of polynomials in entropy coordinates. No projection or quantifier elimination. -/
theorem slice_preimage {ι : Type*} (mask : ι → Fin 16) (A : Set (ι → ℝ))
    (hA : BasicDescription A) :
    HasPlaneDescription {u : ℝ × ℝ | (fun i => profile (cell u.1 u.2) (mask i)) ∈ A} := by
  simpa only [profile_at] using preimage A (fun i => profile polyWeights (mask i)) hA

end EntropyPullback
end

section
open EntropyCounts EntropySlice
namespace EntropyLargeRatio

theorem large_ratio (k q m d : ℕ) (hq : 2≤q) (hr : d+1 < m)
    (hgap : q*m^(4*k+2) < (q-1)*(d+1)^(4*k+3)) :
    0 < weights d q m 3 ∧ (k:ℝ)*(4*weights d q m 3) < weights d q m 4 := by
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0<q)
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlog := Real.log_lt_log (by positivity : (0:ℝ)<(q:ℝ)*(m:ℝ)^(4*k+2)) (show
      (q:ℝ)*(m:ℝ)^(4*k+2) < ((q-1:ℕ):ℝ)*((d+1:ℕ):ℝ)^(4*k+3) by exact_mod_cast hgap)
  have hq' : (q:ℝ)≠0 := by exact_mod_cast (by omega : q≠0)
  have hm' : (m:ℝ)≠0 := by exact_mod_cast (by omega : m≠0)
  have hp' : ((q-1:ℕ):ℝ)≠0 := by exact_mod_cast (by omega : q-1≠0)
  have hd' : ((d+1:ℕ):ℝ)≠0 := by exact_mod_cast (by omega : d+1≠0)
  rw [Real.log_mul hq' (pow_ne_zero _ hm'),Real.log_mul hp' (pow_ne_zero _ hd'),
    Real.log_pow,Real.log_pow] at hlog
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmr := Real.log_lt_log (show (0:ℝ)<((d+1:ℕ):ℝ) by positivity) (show ((d+1:ℕ):ℝ) < m by exact_mod_cast hr)
  change 0 < bits m-bits (d+1) ∧ (k:ℝ)*(4*(bits m-bits (d+1))) <
    bits (q-1)-bits q+3*bits (d+1)-2*bits m
  unfold bits
  constructor
  · exact sub_pos.mpr ((div_lt_div_iff_of_pos_right h2).mpr hmr)
  · rw [← sub_div,← mul_div_assoc,← mul_div_assoc,← sub_div,← mul_div_assoc,
      ← add_div,← mul_div_assoc,← sub_div,div_lt_div_iff_of_pos_right h2]
    push_cast at hlog ⊢
    nlinarith only [hlog]

def alphabet (k : ℕ) := 2^(4*(4*k+3))
def digits (k : ℕ) := 4*(4*k+3)
def size (k : ℕ) := (alphabet k)^(digits k)
def modulus (k : ℕ) := (2*alphabet k-1)^(digits k)*(2*(digits k)*(alphabet k-1)^2+1)

theorem size_pos (k : ℕ) : 0 < size k := Nat.pow_pos (Nat.pow_pos (by decide : 0<2))
theorem size_lt_modulus (k : ℕ) : size k < modulus k := by
  let b := alphabet k
  let d := digits k
  have hb : 2 ≤ b := by
    change 2^1 ≤ (2:ℕ)^(4*(4*k+3))
    apply Nat.pow_le_pow_right (by decide); omega
  have hd : 0<d := by dsimp [d,digits]; omega
  have hpow : 0<b^d := Nat.pow_pos (by omega)
  have hfirst : b^d ≤ (2*b-1)^d := Nat.pow_le_pow_left (by omega) _
  have hextra : 0<2*d*(b-1)^2 := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  change b^d < (2*b-1)^d * (2*d*(b-1)^2+1)
  nlinarith [Nat.mul_pos (lt_of_lt_of_le hpow hfirst) hextra]

theorem thresholds (k q : ℕ) (hq : 2 ≤ q) :
    0 < weights (size k-1) q (modulus k) 3 ∧
      (k:ℝ)*(4*weights (size k-1) q (modulus k) 3) < weights (size k-1) q (modulus k) 4 := by
  apply large_ratio _ _ _ _ hq
  · simpa [Nat.sub_add_cancel (size_pos k)] using size_lt_modulus k
  · rw [Nat.sub_add_cancel (size_pos k)]
    exact EntropyThreshold.all_integer_gaps k q hq

end EntropyLargeRatio
end

section
open Finset Real EntropyOperations
namespace EntropyConditionalCopy

variable {X R : Type*} [Fintype X] [Fintype R]

/-- Conditional joining over one fixed value of the shared coordinates. -/
noncomputable def glue (p : X → ℝ) (c : R → ℝ) (x : X) (r : R) :=
  p x*(c r/(∑ y,p y))

theorem zero_row {Y : Type*} [Fintype Y] (p : Y → ℝ) (hp : ∀ y,0≤p y)
    (h : ∑ y,p y=0) (y : Y) : p y=0 :=
  (sum_eq_zero_iff_of_nonneg (fun i _ => hp i)).mp h y (mem_univ y)

theorem right_marginal (p : X → ℝ) (c : R → ℝ) (hc : ∀ r,0≤c r)
    (hs : ∑ r,c r=∑ x,p x) (r : R) : ∑ x,glue p c x r=c r := by
  by_cases h : ∑ x,p x=0
  · simp [glue,h,zero_row c hc (hs.trans h) r]
  · rw [show (∑ x,glue p c x r)=(∑ x,p x)*(c r/(∑ x,p x)) from (sum_mul ..).symm]
    field_simp

theorem left_marginal (p : X → ℝ) (c : R → ℝ) (hp : ∀ x,0≤p x)
    (hs : ∑ r,c r=∑ x,p x) (x : X) : ∑ r,glue p c x r=p x := by
  by_cases h : ∑ x,p x=0
  · simp [glue,h,zero_row p hp h x]
  · simp [glue,← mul_sum,div_eq_mul_inv,← sum_mul,hs,h]

theorem entropy_identity (p : X → ℝ) (c : R → ℝ)
    (hp : ∀ x,0≤p x) (hc : ∀ r,0≤c r) (hs : ∑ r,c r=∑ x,p x) :
    (∑ x,∑ r,negMulLog (glue p c x r)) + negMulLog (∑ x,p x) =
    (∑ x,negMulLog (p x)) + ∑ r,negMulLog (c r) := by
  let M := ∑ x,p x
  by_cases hm : M=0
  · have z := zero_row p hp hm
    have z' := zero_row c hc (hs.trans hm)
    simp [glue,z,z']
  · let k := fun r => c r/M
    have hk : ∑ r,k r=1 := by simp [k,div_eq_mul_inv,← sum_mul,hs,← show M=∑ x,p x from rfl,hm]
    have hrow (x : X) : (∑ r,negMulLog (glue p c x r)) =
        negMulLog (p x)+p x*∑ r,negMulLog (k r) := by
      change (∑ r,negMulLog (p x*k r))=_
      simp_rw [negMulLog_mul,sum_add_distrib,← sum_mul,← mul_sum,hk,one_mul]
    have hcol (r : R) : negMulLog (c r)=k r*negMulLog M+M*negMulLog (k r) := by
      rw [← negMulLog_mul]
      congr 1
      dsimp [k]
      field_simp
    simp_rw [hrow,hcol,sum_add_distrib,← sum_mul,← mul_sum,hk,one_mul]
    dsimp [M]
    ring

variable {I C D : Type*} [Fintype I] [Fintype C] [Fintype D]

noncomputable def marginal (p : I → C × D → ℝ) (i : I) (c : C) := ∑ d,p i (c,d)
noncomputable def copy (p : I → C × D → ℝ) (i : I) := glue (p i) (marginal p i)

theorem marginal_sum (p : I → C × D → ℝ) (i : I) :
    ∑ c,marginal p i c=∑ x,p i x := by simp [marginal,Fintype.sum_prod_type]

theorem preserves_law (p : I → C × D → ℝ) (hp : ∀ i x,0≤p i x) (i : I) :
    (∀ x, ∑ r,copy p i x r=p i x) ∧
    (∀ r, ∑ x,copy p i x r=marginal p i r) := by
  exact ⟨left_marginal _ _ (hp i) (marginal_sum p i),
    right_marginal _ _ (fun r => sum_nonneg fun _ _ => hp _ _) (marginal_sum p i)⟩

theorem copy_nonneg (p : I → C × D → ℝ) (hp : ∀ i x,0≤p i x) (i x r) :
    0≤copy p i x r := mul_nonneg (hp i x)
      (div_nonneg (sum_nonneg fun _ _ => hp _ _) (sum_nonneg fun _ _ => hp _ _))

/-- The conditional-independence identity, in the same bit entropy used by the official statement. -/
theorem copy_entropy (p : I → C × D → ℝ) (hp : ∀ i x,0≤p i x) :
    ent (fun z : I × (C × D) × C => copy p z.1 z.2.1 z.2.2) +
      ent (fun i => ∑ x,p i x) =
    ent (fun z : I × (C × D) => p z.1 z.2) +
      ent (fun z : I × C => marginal p z.1 z.2) := by
  unfold ent
  rw [← add_div,← add_div]
  congr 1
  simp only [Fintype.sum_prod_type,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  simpa only [copy,Fintype.sum_prod_type,← sum_add_distrib] using
    entropy_identity (p i) (marginal p i) (hp i) (fun c => sum_nonneg fun _ _ => hp _ _) (marginal_sum p i)

end EntropyConditionalCopy
end

section
open Finset EntropyPushforward EntropyOperations EntropyFiniteRows EntropyCounts
open OMA.S_itp_entropy_region
namespace EntropyOfficial

abbrev Idx (n : ℕ) := NonemptySubset n

def restr {n : ℕ} {X : Type*} (S : Idx n) (r : Fin n → X) : S.1 → X := fun i => r i.1

noncomputable def vec {n : ℕ} {Ω X : Type*} [Fintype Ω] [Fintype X]
    (p : Ω → ℝ) (r : Ω → Fin n → X) (S : Idx n) := obs p (restr S ∘ r)

theorem sub_eq {n k : ℕ} (p : (Fin n → Fin k) → ℝ) (S : Idx n) :
    subsetEntropy p S.1 = obs p (restr S)  := by
  classical
  unfold subsetEntropy obs ent
  congr 1
  apply sum_congr rfl
  intro y _
  congr 1
  unfold marginalMass push
  apply sum_congr rfl
  intro a _
  by_cases he : restr S a=y
  · simp [he,show (fun i : S.1 => a i.1)=y from he]
  · simp [he,show (fun i : S.1 => a i.1)≠y from he]

theorem realize {n : ℕ} {Ω X : Type*} [Fintype Ω] [Fintype X]
    (p : Ω → ℝ) (r : Ω → Fin n → X) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a,p a=1) :
    vec p r ∈ entropicVectors n := by
  classical
  let e := Fintype.equivFin X
  let f (a : Ω) (i : Fin n) := e (r a i)
  refine ⟨Fintype.card X,push p f,push_nonneg p hp f,(sum_push p f).trans hs,?_⟩
  intro S
  rw [sub_eq]
  let g (v : S.1 → X) := fun i => e (v i)
  have hg : Function.Injective g := fun a b h => funext fun i => e.injective (congrFun h i)
  have hc := obs_inj p (restr S ∘ r) g hg
  change obs p (restr S ∘ r) = ent (push (push p f) (restr S))
  rw [push_comp]
  exact hc.symm

theorem add_mem {n : ℕ} {h k : Idx n → ℝ} (hh : h ∈ entropicVectors n)
    (hk : k ∈ entropicVectors n) : h+k ∈ entropicVectors n := by
  classical
  obtain ⟨i,p,hp,hs,h₁⟩ := hh
  obtain ⟨j,q,hq,ht,h₂⟩ := hk
  let prob := fun a : (Fin n → Fin i) × (Fin n → Fin j) => p a.1*q a.2
  let r := fun (a : (Fin n → Fin i) × (Fin n → Fin j)) (l : Fin n) => (a.1 l,a.2 l)
  have hprob : ∑ a,prob a=1 := by simp [prob,Fintype.sum_prod_type,← Finset.mul_sum,ht,hs]
  have hv := realize prob r (fun a => mul_nonneg (hp _) (hq _)) hprob
  have e : vec prob r = h+k := by
    funext S
    let g (a : (S.1 → Fin i) × (S.1 → Fin j)) := fun l : S.1 => (a.1 l,a.2 l)
    have hg : Function.Injective g := by
      intro a b he
      exact Prod.ext (funext fun l => congrArg Prod.fst (congrFun he l))
        (funext fun l => congrArg Prod.snd (congrFun he l))
    change obs prob (g ∘ Prod.map (restr S) (restr S)) = h S+k S
    rw [obs_inj _ _ _ hg, h₁ S,h₂ S,sub_eq,sub_eq]
    exact obs_prod p q hs ht _ _
  rwa [e] at hv

theorem flag_mem {n : ℕ} {h : Idx n → ℝ} (hh : h ∈ entropicVectors n)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (fun S => t*h S+tag t) ∈ entropicVectors n := by
  classical
  obtain ⟨k,p,hp,hs,h₁⟩ := hh
  let r (a : (Fin n → Fin k) ⊕ Unit) (i : Fin n) : Fin k ⊕ Unit :=
    a.elim (fun b => Sum.inl (b i)) Sum.inr
  have hp' (a) : 0 ≤ flagged t p a := by
    cases a with
    | inl b => exact mul_nonneg ht (hp b)
    | inr b => exact sub_nonneg.mpr ht'
  have hv := realize (flagged t p) r hp' (sum_flagged t p hs)
  have e : vec (flagged t p) r = fun S : Idx n => t*h S+tag t := by
    funext S
    let g (v : (S.1 → Fin k) ⊕ Unit) (l : S.1) : Fin k ⊕ Unit :=
      v.elim (fun b => Sum.inl (b l)) Sum.inr
    obtain ⟨l,hl⟩ := S.2
    let t₀ : S.1 := ⟨l,hl⟩
    have hg : Function.Injective g := by
      rintro (a|a) (b|b) h₀
      · exact congrArg Sum.inl (funext fun j => Sum.inl.inj (congrFun h₀ j))
      · exact (Sum.inl_ne_inr (congrFun h₀ t₀)).elim
      · exact (Sum.inr_ne_inl (congrFun h₀ t₀)).elim
      · congr
    have hh : restr S ∘ r = g ∘ Sum.map (restr S) (id : Unit → Unit) := by
      funext a j
      cases a <;> rfl
    rw [vec,hh,obs_inj _ _ _ hg,obs_flagged _ hs,h₁ S,sub_eq]
  rwa [e] at hv

/-- Every marginal of a uniform list of rows is literally the marginal in
the frozen problem, after the row distribution is pushed to the joint alphabet. -/
theorem rows_subsetEntropy {n k : ℕ} {Ω : Type*} [Fintype Ω]
    (f : Ω → Fin n → Fin k) (S : Idx n) (support : Finset (S.1 → Fin k)) (F : ℕ)
    (hS : 0<support.card) (hF : 0<F) (hc : Fintype.card Ω = support.card*F)
    (hf : ∀ y, (univ.filter fun a => restr S (f a)=y).card = if y∈support then F else 0) :
    subsetEntropy (mass f) S.1 = bits support.card := by
  classical
  rw [sub_eq]
  unfold obs ent
  have he : push (mass f) (restr S) = fun y => if y∈support then (support.card:ℝ)⁻¹ else 0 := by
    funext y
    calc
      _ = ∑ x, if restr S x = y then mass f x else 0 := by
        unfold push
        apply sum_congr rfl
        intro a _
        by_cases h : restr S a = y <;> simp [h]
      _ = mass (restr S ∘ f) y := marginal_count f _ y
      _ = _ := mass_flat _ support F hc hF hf y
  rw [he]
  simpa only [Real.negMulLog] using flat_entropy support hS

end EntropyOfficial
end

section
open EntropySlice EntropyPullback EntropyPolynomialGraph
namespace EntropyConeBridge

def coords {ι : Type*} (mask : ι → Fin 16) (w : Weights ℝ) : ι → ℝ :=
  fun i => profile w (mask i)

private theorem coord_cts (k : Fin 16) : Continuous (fun w : Weights ℝ => profile w k) := by
  fin_cases k <;> simp only [profile] <;> fun_prop

private theorem cell_cts (x : ℝ) : Continuous (cell x) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [cell] <;> fun_prop

/-- The slightly weakened symmetrized DFZ estimate. -/
def Bound (s : ℕ) (h : Fin 16 → ℝ) : Prop :=
  (2*(2:ℝ)^s-1)*V h ≤ J h+(((s:ℝ)-1)*(2:ℝ)^s+1)*P h

theorem bound_closed (s : ℕ) : IsClosed {h : Fin 16 → ℝ | Bound s h} := by
  apply isClosed_le <;> simp only [V,J,P] <;> fun_prop

/-- Continuity extends each DFZ inequality from actual vectors to their closure. -/
theorem bound_on_closure (s : ℕ) {D : Set (Fin 16 → ℝ)}
    (hD : ∀ h ∈ D, Bound s h) : ∀ h ∈ closure D, Bound s h :=
  fun _ hh => closure_minimal hD (bound_closed s) hh

/-- The target dimension and number of inequalities are arbitrary. All
remaining entropy-specific inputs are stated explicitly. -/
theorem disproof_of_profiles {ι : Type*} (mask : ι → Fin 16) (A : Set (ι → ℝ))
    (hclosed : IsClosed A)
    (cone : ConeInputs {w | coords mask w ∈ A})
    (high : ∀ z : ℝ, 0 < z → ∃ w : Weights ℝ, coords mask w ∈ A ∧
      0 < w 3 ∧ z*(4*w 3) < w 4)
    (low : ∃ w : Weights ℝ, coords mask w ∈ A ∧ 0 < w 3 ∧ w 4 ≤ 0)
    (dfz : ∀ (w : Weights ℝ), coords mask w ∈ A → 0 ≤ w 3 → ∀ s : ℕ, 0 < s → Bound s (profile w)) :
    ¬ BasicDescription A := by
  intro hA
  let S : Set (ℝ × ℝ) := {u | coords mask (cell u.1 u.2) ∈ A}
  have hplane : HasPlaneDescription S := slice_preimage mask A hA
  apply capped_fibres_not_semialgebraic (S:=S) _ hplane
  intro n
  let x := (1/2:ℝ)^(n+3)
  have hx : 0<x := pow_pos (by norm_num) _
  obtain ⟨u,hu,hup,hur⟩ := high (1/x) (div_pos zero_lt_one hx)
  obtain ⟨v,hv,hvp,hvr⟩ := low
  have hu' : 4*u 3 < x*u 4 := by
    have he : (4*u 3)/x < u 4 := by simpa [div_eq_mul_inv,mul_comm,mul_assoc] using hur
    simpa only [mul_comm] using (div_lt_iff₀ hx).mp he
  have hv' : x*v 4 < 4*v 3 :=
    lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos hx.le hvr) (by linarith)
  obtain ⟨y,hy,hmem⟩ := hit_ray cone hx hu hv hup hvp hu' hv'
  let T : Set ℝ := {t | coords mask (cell x t) ∈ A}
  have ht : IsClosed T := by
    apply hclosed.preimage
    apply continuous_pi
    intro i
    exact (coord_cts (mask i)).comp (cell_cts x)
  let b := (1/2:ℝ)^(2^n : ℕ)
  have hcap : ∀ t ∈ T, t ≤ b := by
    intro t ht'
    by_cases h : 0 ≤ t
    · exact dyadic_cap n t h (dfz _ ht' (show 0 ≤ x*t/4 from by positivity) _ (Nat.pow_pos (by decide : 0 < 2)))
    · exact le_trans (le_of_not_ge h) (pow_nonneg (by norm_num) _)
  have htop := ht.csSup_mem (show T.Nonempty from ⟨y,hmem⟩) ⟨b,hcap⟩
  exact ⟨sSup T,htop,hy.trans_le (le_csSup ⟨b,hcap⟩ hmem),hcap _ htop,
    fun _ ht' => le_csSup ⟨b,hcap⟩ ht'⟩

end EntropyConeBridge
end

section
open Finset EntropyLargeRatio
namespace EntropyProgressionLabels

/-- Independent odd cyclic coordinates implement the digit and squared-norm checks. -/
abbrev S (b d : ℕ) := Fin d → Fin (b+1)
abbrev E (b d : ℕ) := (Fin d → ZMod (2*b+1)) × ZMod (2*d*b^2+1)

def energy {b d : ℕ} (s : S b d) := ∑ j,(s j).val^2

def col {b d : ℕ} (s : S b d) : E b d :=
  (fun i => ((s i).val : ZMod _),(energy s : ZMod _))

theorem energy_le {b d : ℕ} (s : S b d) : energy s≤d*b^2 := by
  calc
    energy s ≤ ∑ _j : Fin d,b^2 := sum_le_sum fun j _ => Nat.pow_le_pow_left (Nat.le_of_lt_succ (s j).isLt) _
    _ = _ := by simp

private theorem unwrap {m a b : ℕ} (ha : a < m) (hb : b < m) (hh : (a : ZMod m)=b) : a=b := by
  simpa only [ZMod.val_natCast_of_lt ha,ZMod.val_natCast_of_lt hb] using congrArg ZMod.val hh

theorem digit_eq {b d : ℕ} (x y z t : S b d) (h : col x+col y=col z+col t) (j : Fin d) :
    (x j).val+(y j).val=(z j).val+(t j).val := by
  have h₁ := (x j).isLt
  have h₂ := (y j).isLt
  have h₃ := (z j).isLt
  have h₄ := (t j).isLt
  apply unwrap (m:=2*b+1) (by omega) (by omega)
  simpa [col,Nat.cast_add] using congrArg (fun u : E b d => u.1 j) h

theorem no_ap {b d : ℕ} (x y z : S b d) (h : col x+col y=col z+col z) : x=z := by
  have hs : energy x+energy y=energy z+energy z := by
    have hx := energy_le x
    have hy := energy_le y
    have hz := energy_le z
    apply unwrap (m:=2*d*b^2+1) (by nlinarith only [hx,hy]) (by nlinarith only [hz])
    simpa [col,Nat.cast_add] using congrArg Prod.snd h
  have hs' : (∑ i,((x i).val : ℤ)^2)+(∑ i,((y i).val : ℤ)^2)=2*∑ i,((z i).val : ℤ)^2 := by
    change (∑ i,(x i).val^2)+(∑ i,(y i).val^2)=(∑ i,(z i).val^2)+(∑ i,(z i).val^2) at hs
    rw [two_mul]
    exact_mod_cast hs
  have localEq (j : Fin d) : (((x j).val : ℤ)-(z j).val)^2*2 =
      ((x j).val : ℤ)^2+((y j).val : ℤ)^2-2*((z j).val : ℤ)^2 := by
    have hj : ((x j).val : ℤ)+(y j).val=(z j).val+(z j).val := by exact_mod_cast digit_eq x y z z h j
    rw [show ((y j).val : ℤ) = 2*(z j).val-(x j).val by linarith]
    ring
  have ht : (∑ j,(((x j).val : ℤ)-(z j).val)^2*2)=0 := by
    simp_rw [localEq,sum_sub_distrib,sum_add_distrib,← mul_sum]
    linarith
  funext i
  apply Fin.ext
  have hzero := (sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (by decide : (0:ℤ)≤2))).mp ht i (mem_univ i)
  have hh : ((x i).val : ℤ)=(z i).val := by nlinarith [sq_nonneg (((x i).val : ℤ)-(z i).val)]
  exact_mod_cast hh

theorem edge {b d : ℕ} : Function.Injective fun x : E b d × S b d =>
    (x.1+(-col x.2),x.1+col x.2) := by
  rintro ⟨e,s⟩ ⟨f,t⟩ he
  obtain ⟨h₁,h₂⟩ := Prod.mk.inj he
  change e + -col s = f + -col t at h₁
  change e + col s = f + col t at h₂
  have h : col s+col s=col t+col t := by linear_combination (norm := abel) h₂ - h₁
  have st : s=t := funext fun j => Fin.ext (by have hj := digit_eq s s t t h j; omega)
  subst t
  exact Prod.ext (add_right_cancel h₂) rfl

theorem col_inj {b d : ℕ} : Function.Injective (@col b d) := by
  intro a v h
  exact no_ap a a v (by rw [h])

theorem sizes (b d : ℕ) :
    Nat.card (S b d)=(b+1)^d ∧ Nat.card (E b d)=(2*b+1)^d*(2*d*b^2+1) := by
  simp [S,E,Nat.card_eq_fintype_card]

end EntropyProgressionLabels
end

section
open Finset Real EntropyOperations EntropyConditionalCopy
namespace EntropyShannon

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem cell_bound {p q : ℝ} (hp : 0≤p) (hq : 0≤q) (hs : 0<p → 0<q) :
    negMulLog p+p*log q ≤ q-p := by
  rcases hp.eq_or_lt with he | hp
  · simp [← he,hq]
  · have hb := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos (hs hp) hp)) hp.le
    rw [log_div (hs hp).ne' hp.ne'] at hb
    have e : p*(q/p-1)=q-p := by field_simp
    rw [e] at hb
    simpa only [negMulLog_eq_neg] using (by linarith only [hb] : -(p*log p)+p*log q ≤ q-p)

private theorem en {Z : Type*} [Fintype Z] (v : Z → ℝ) : ∑ z,negMulLog (v z) = -(∑ z,v z*log (v z)) := by
  simp [negMulLog,neg_mul]

theorem subadd_row (p : X → Y → ℝ) (hp : ∀ x y,0≤p x y) :
    (∑ x,∑ y,negMulLog (p x y))+ negMulLog (∑ x,∑ y,p x y) ≤
      (∑ x,negMulLog (∑ y,p x y)) + ∑ y,negMulLog (∑ x,p x y) := by
  let a x := ∑ y,p x y
  let b y := ∑ x,p x y
  let M := ∑ x,a x
  change (∑ x,∑ y,negMulLog (p x y))+negMulLog M ≤ (∑ x,negMulLog (a x))+∑ y,negMulLog (b y)
  have ha (x : X) : 0≤a x := sum_nonneg fun _ _ => hp _ _
  have hb (y : Y) : 0≤b y := sum_nonneg fun _ _ => hp _ _
  have hm : 0≤M := sum_nonneg fun _ _ => ha _
  have bs : ∑ y,b y=M := sum_comm
  by_cases hz : M=0
  · have za := zero_row a ha hz
    have zb := zero_row b hb (bs.trans hz)
    have zp (x : X) := zero_row (p x) (hp x) (za x)
    simp [hz,za,zb,zp]
  let q (x : X) (y : Y) := glue a b x y
  have qa (x : X) : ∑ y,q x y=a x := left_marginal a b ha bs x
  have hs (x : X) (y : Y) :
      negMulLog (p x y) + (p x y*log (a x)+p x y*log (b y)-p x y*log M) ≤ q x y-p x y := by
    have ax : p x y≤a x := single_le_sum (f:=p x) (fun _ _ => hp _ _) (mem_univ y)
    have by' : p x y≤b y := single_le_sum (f:=fun t => p t y) (fun _ _ => hp _ _) (mem_univ x)
    have qpos (h : 0<p x y) : 0<q x y :=
      mul_pos (h.trans_le ax) (div_pos (h.trans_le by') (hm.lt_of_ne (Ne.symm hz)))
    have h := cell_bound (q:=q x y) (hp x y) (mul_nonneg (ha x) (div_nonneg (hb y) hm)) qpos
    by_cases he : p x y=0
    · simpa [he] using h
    · have hi := (hp x y).lt_of_ne (Ne.symm he)
      have logq : log (q x y)=log (a x)+log (b y)-log M := by
        change log (a x*(b y/M))=_
        rw [log_mul (hi.trans_le ax).ne' (div_ne_zero (hi.trans_le by').ne' hz),
          log_div (hi.trans_le by').ne' hz]
        ring
      change negMulLog (p x y)+p x y*log (q x y)≤_ at h
      rw [logq] at h
      simpa only [mul_sub,mul_add] using h
  have full := sum_le_sum (s:=univ) (fun x _ => sum_le_sum (s:=univ) (fun y _ => hs x y))
  have ea (x : X) : (∑ y,p x y*log (a x))=a x*log (a x) := (sum_mul ..).symm
  have eb : (∑ x,∑ y,p x y*log (b y))=∑ y,b y*log (b y) := by
    rw [sum_comm]; simp [b,← sum_mul]
  have em : (∑ x,∑ y,p x y*log M)=M*log M := by simp [M,a,← sum_mul]
  simp only [sum_add_distrib,sum_sub_distrib,qa,ea,eb,em] at full
  rw [en a,en b]
  simp only [negMulLog_eq_neg] at full ⊢
  linarith only [full,show (∑ x,a x)=∑ x,∑ y,p x y from rfl]

variable {I : Type*} [Fintype I]

theorem conditional (p : I → X → Y → ℝ) (hp : ∀ i x y,0≤p i x y) :
    ent (fun z : I × X × Y => p z.1 z.2.1 z.2.2) + ent (fun i => ∑ x,∑ y,p i x y) ≤
    ent (fun z : I × X => ∑ y,p z.1 z.2 y) + ent (fun z : I × Y => ∑ x,p z.1 x z.2) := by
  unfold ent
  rw [← add_div,← add_div]
  apply div_le_div_of_nonneg_right _ (log_nonneg (by norm_num))
  simpa only [Fintype.sum_prod_type,← sum_add_distrib] using
    sum_le_sum (s:=univ) (fun i _ => subadd_row (p i) (hp i))

end EntropyShannon
end

section
open OMA.S_itp_entropy_region EntropyOperations EntropyOfficial
open Filter Topology
namespace EntropyClosedCone

variable {n : ℕ}
abbrev cone (n : ℕ) := closure (entropicVectors n)

theorem add_closed {h k : Idx n → ℝ} (hh : h ∈ cone n) (hk : k ∈ cone n) :
    h+k ∈ cone n := by
  have step (a) (ha : a ∈ entropicVectors n) : a+k ∈ cone n := by
    have hc : IsClosed {b | a+b ∈ cone n} :=
      isClosed_closure.preimage (continuous_const.add continuous_id)
    have inc : entropicVectors n ⊆ {b | a+b ∈ cone n} := fun _ hb => subset_closure (add_mem ha hb)
    exact closure_minimal inc hc hk
  have hc : IsClosed {a | a+k ∈ cone n} :=
    isClosed_closure.preimage (continuous_id.add continuous_const)
  exact closure_minimal step hc hh

private theorem copies {h : Idx n → ℝ} (hh : h ∈ entropicVectors n) (j : ℕ) :
    ((j:ℝ)+1) • h ∈ entropicVectors n := by
  induction j with
  | zero => simpa using hh
  | succ j ih =>
    simpa only [Nat.cast_succ,add_smul,one_smul] using add_mem ih hh

theorem scale_actual {h : Idx n → ℝ} (hh : h ∈ entropicVectors n) {c : ℝ} (hc : 0≤c) :
    c • h ∈ cone n := by
  let t (j : ℕ) := c/((j:ℝ)+1)
  have ht : Tendsto t atTop (𝓝 0) := by
    simpa [t,div_eq_mul_inv] using
      (tendsto_const_nhds (x:=c)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  have tag0 : Tendsto (fun j => tag (t j)) atTop (𝓝 0) := by
    have hcont : Continuous tag := by unfold tag; fun_prop
    have hzero : tag 0=0 := by simp [tag]
    exact hzero ▸ (hcont.tendsto 0).comp ht
  let f (j : ℕ) (S : Idx n) := c*h S+tag (t j)
  have hlim : Tendsto f atTop (𝓝 (c • h)) := by
    apply tendsto_pi_nhds.mpr
    intro S
    simpa [f,Pi.smul_apply,smul_eq_mul] using (tendsto_const_nhds (x:=c*h S)).add tag0
  apply mem_closure_of_tendsto hlim
  filter_upwards [ht.eventually_lt_const zero_lt_one] with j hj
  have hd : 0 < (j:ℝ)+1 := by positivity
  have ht₀ : 0 ≤ t j := div_nonneg hc hd.le
  have eq : t j*((j:ℝ)+1) = c := div_mul_cancel₀ _ hd.ne'
  have hf := flag_mem (copies hh j) ht₀ hj.le
  simpa only [f,Pi.smul_apply,smul_eq_mul,← mul_assoc,eq] using hf

theorem scale_closed {h : Idx n → ℝ} (hh : h ∈ cone n) {c : ℝ} (hc : 0≤c) :
    c • h ∈ cone n := by
  have hs : IsClosed {b : Idx n → ℝ | c • b ∈ cone n} :=
    isClosed_closure.preimage (continuous_const_smul c)
  exact closure_minimal (fun _ hb => scale_actual hb hc) hs hh

theorem normalize {h : Idx n → ℝ} (hh : h ∈ cone n) (i : Idx n) (hi : 0<h i) :
    (h i)⁻¹ • h ∈ cone n ∧ ((h i)⁻¹ • h) i = 1 := by
  exact ⟨scale_closed hh (inv_nonneg.mpr hi.le),inv_mul_cancel₀ hi.ne'⟩

end EntropyClosedCone
end

section
open EntropySlice EntropyConeBridge EntropyFixtures
namespace EntropyStability

def U (h : Fin 16 → ℝ) := h 5+h 6-h 4-h 7
def W (h : Fin 16 → ℝ) := h 9+h 10-h 8-h 11
def Icd (h : Fin 16 → ℝ) := h 4+h 8-h 12
def CErr (h : Fin 16 → ℝ) := (h 3+h 6-h 2-h 7)+(h 3+h 5-h 1-h 7)
def DErr (h : Fin 16 → ℝ) := (h 3+h 10-h 2-h 11)+(h 3+h 9-h 1-h 11)

/-- DFZ Theorem 10 with its integer index equal to s+1. The arguments
a,b are I(A;B|C),I(A;B|D); c,d are the two conditional-error sums. -/
def Direction (s : ℕ) (j a b i c d : ℝ) :=
  let T := (2:ℝ)^s
  (T-1)*j ≤ T*a + ((s:ℝ)*T/2)*c + (T-1)*b +
    (((s:ℝ)-2)*T/2+1)*d + (T-1)*i

def Symmetric (s : ℕ) (h : Fin 16 → ℝ) :=
  2*((2:ℝ)^s-1)*V h ≤ U h+W h+(((s:ℝ)-1)*2^s+1)*P h

theorem symmetrize (s : ℕ) (h : Fin 16 → ℝ)
    (a : Direction s (J h) (U h) (W h) (Icd h) (CErr h) (DErr h))
    (b : Direction s (J h) (W h) (U h) (Icd h) (DErr h) (CErr h)) :
    Symmetric s h := by
  have p : P h=CErr h+DErr h := by unfold P CErr DErr; ring
  have v : V h=J h-U h-W h-Icd h := rfl
  unfold Direction at a b
  unfold Symmetric
  rw [p,v]
  nlinarith only [a,b]

theorem to_bound {s : ℕ} {w : Weights ℝ} (hw : 0 ≤ w 3)
    (hs : Symmetric s (profile w)) : Bound s (profile w) := by
  let h := profile w
  have hi : Icd h=w 3 := by simp [Icd,h,profile]; ring
  have hv : V h=J h-U h-W h-Icd h := rfl
  change 2*((2:ℝ)^s-1)*V h ≤ _ at hs
  change (2*(2:ℝ)^s-1)*V h ≤ _
  nlinarith only [hs,hv,hi,hw]

def maskOf (S : {S : Finset (Fin 4) // S.Nonempty}) := code S.1
noncomputable def inflate (h : {S : Finset (Fin 4) // S.Nonempty} → ℝ) (i : Fin 16) :=
  if hi : (decode i).Nonempty then h ⟨decode i,hi⟩ else 0

theorem inflate_coords (w : Weights ℝ) : inflate (coords maskOf w) = profile w := by
  funext i
  by_cases hi : (decode i).Nonempty
  · simp [inflate,hi,coords,maskOf,code_decode]
  · have h0 : i=0 := by
      rw [← code_decode i,Finset.not_nonempty_iff_eq_empty.mp hi]
      decide
    subst i
    simp [inflate,hi,profile]

/-- Both inequalities need only be proved for actual entropy vectors. -/
theorem on_closure {D : Set ({S : Finset (Fin 4) // S.Nonempty} → ℝ)}
    (s : ℕ) (actual : ∀ h ∈ D, let H := inflate h
      Direction s (J H) (U H) (W H) (Icd H) (CErr H) (DErr H) ∧
      Direction s (J H) (W H) (U H) (Icd H) (DErr H) (CErr H))
    {w : Weights ℝ} (hw : coords maskOf w ∈ closure D) (hp : 0 ≤ w 3) :
    Bound s (profile w) := by
  have hc : Continuous (inflate) := by
    apply continuous_pi
    intro i
    by_cases hi : (decode i).Nonempty <;> simp [inflate,hi] <;> fun_prop
  have hs : IsClosed {h : Fin 16 → ℝ | Symmetric s h} := by
    apply isClosed_le <;> simp only [V,J,P,U,W] <;> fun_prop
  have hh : ∀ h ∈ D, Symmetric s (inflate h) := fun h ha => symmetrize _ _ (actual h ha).1 (actual h ha).2
  have h' : Symmetric s (inflate (coords maskOf w)) := closure_minimal hh (hs.preimage hc) hw
  rw [inflate_coords] at h'
  exact to_bound hp h'

end EntropyStability
end

section
open Finset EntropyFiniteRows EntropyCounts EntropySlice EntropyOfficial
open EntropyStability EntropyConeBridge EntropyFixtures EntropyPushforward
open OMA.S_itp_entropy_region
namespace EntropyFixtureMembership

theorem uniform_realized {n k : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → Fin n → Fin k) :
    (fun S : Idx n => subsetEntropy (mass f) S.1) ∈ entropicVectors n := by
  classical
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hm : mass f = push (fun _ : Ω => (Fintype.card Ω:ℝ)⁻¹) f := by
    funext x
    unfold mass push
    rw [Finset.card_filter]
    simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_div]
    apply sum_congr rfl
    intro a _
    by_cases h : f a=x <;> simp [h]
  refine ⟨k,mass f,fun x => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),?_,fun _=>rfl⟩
  rw [hm,sum_push]; simp [nsmul_eq_mul,hN]

theorem fixture_mem (t : Fin 4) : coords maskOf (wt t) ∈ entropicVectors 4 := by
  classical
  letI : NeZero (if t=3 then 32 else 8) := ⟨by split <;> decide⟩
  have hv := uniform_realized (row t)
  have hh (S : Idx 4) : subsetEntropy (mass (row t)) S.1 = profile (wt t) (maskOf S) := by
    let S' := univ.image (view t S.1)
    let K := 2^rank t (code S.1)
    let a₀ : Fin (if t=3 then 32 else 8) := 0
    let F := (univ.filter fun b => view t S.1 b=view t S.1 a₀).card
    have hpK : 0 < K := Nat.pow_pos (by decide)
    have hSK : S'.card=K := (counts t S.1).1
    have hbasic (a) := (counts t S.1).2 a
    have he : F*K = (if t=3 then 32 else 8) := hbasic a₀
    have hf0 : 0 < F := card_pos.mpr ⟨a₀,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
    have hc : Fintype.card (Fin (if t=3 then 32 else 8)) = S'.card*F := by
      rw [Fintype.card_fin,hSK,mul_comm,he]
    have hall (y : S.1 → Fin 32) : (univ.filter fun b => restr S (row t b)=y).card =
        if y∈S' then F else 0 := by
      by_cases hy : y∈S'
      · rw [if_pos hy]
        obtain ⟨a,_,rfl⟩ := mem_image.mp hy
        apply Nat.eq_of_mul_eq_mul_right hpK
        exact (hbasic a).trans he.symm
      · rw [if_neg hy]
        apply card_eq_zero.mpr
        apply eq_empty_iff_forall_notMem.mpr
        intro b hb
        exact hy (mem_image.mpr ⟨b,mem_univ _,(mem_filter.mp hb).2⟩)
    rw [rows_subsetEntropy (row t) S S' F (hSK ▸ hpK) hf0 hc hall,hSK]
    change bits (2 ^ rank t (code S.1)) = _
    rw [← rank_profile]
    simp [bits,maskOf,Real.log_pow,Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)]
  convert hv using 1
  exact funext fun S => (hh S).symm

end EntropyFixtureMembership
end

section
open Finset OMA.S_itp_entropy_region
open EntropySlice EntropyConeBridge EntropyStability EntropyCounts EntropyFixtures EntropyOfficial
open EntropyLargeRatio EntropyFixtureMembership EntropyClosedCone
namespace EntropyFinalBridge

abbrev ProjectedTable (j k N : ℕ) := Fin N → Fin j → Fin k

/-- A finite combinatorial obligation. No entropy or inequalities occur in it.
For each subset, exhibit its image and identical positive fibre sizes. -/
def LargeTable (k : ℕ) : Prop := ∃ (q K N : ℕ) (_ : 2 ≤ q) (_ : 0 < N)
    (f : ProjectedTable 4 K N), ∀ S : Idx 4, ∃ (s : Finset (S.1 → Fin K)) (F : ℕ),
      s.card = supportCard (size k-1) q (modulus k) (maskOf S) ∧
      0 < s.card ∧ 0 < F ∧ N = s.card*F ∧
      ∀ y, (univ.filter fun a => restr S (f a)=y).card = if y∈s then F else 0

theorem high_tables_finite (tables : ∀ k, LargeTable k) (z : ℝ) (hz : 0<z) :
    ∃ w : Weights ℝ, coords maskOf w ∈ entropicVectors 4 ∧ 0<w 3 ∧ z*(4*w 3)<w 4 := by
  obtain ⟨k,hk⟩ := exists_nat_gt z
  obtain ⟨q,K,N,hq,hN,f,hf⟩ := tables k
  letI : NeZero N := ⟨hN.ne'⟩
  let w := weights (size k-1) q (modulus k)
  have hh (S : Idx 4) : subsetEntropy (EntropyFiniteRows.mass f) S.1 = coords maskOf w S := by
    obtain ⟨s,F,he,hs,hF,hc,hist⟩ := hf S
    rw [rows_subsetEntropy f S s F hs hF (by simpa using hc) hist,he]
    exact support_profile _ _ _ hq (lt_trans (size_pos k) (size_lt_modulus k)) _
  have hmem : coords maskOf w ∈ entropicVectors 4 := by
    have he := funext hh
    rw [← he]
    exact uniform_realized f
  obtain ⟨hp,hv⟩ := thresholds k q hq
  exact ⟨w,hmem,hp,(mul_lt_mul_of_pos_right hk (by linarith : 0<4*w 3)).trans hv⟩

theorem high_tables (tables : ∀ k, LargeTable k) (z : ℝ) (hz : 0<z) :
    ∃ w : Weights ℝ, coords maskOf w ∈ cone 4 ∧ 0<w 3 ∧ z*(4*w 3)<w 4 := by
  obtain ⟨w,hw,hp,hv⟩ := high_tables_finite tables z hz
  exact ⟨w,subset_closure hw,hp,hv⟩

theorem add_coords (a b : Weights ℝ) : coords maskOf (a+b)=coords maskOf a+coords maskOf b := by
  funext S
  change profile (a+b) (maskOf S) = profile a (maskOf S)+profile b (maskOf S)
  generalize maskOf S = i
  fin_cases i <;> simp [profile,Pi.add_apply] <;> ring

theorem scale_coords (a : Weights ℝ) (c : ℝ) : coords maskOf (c • a) = c • coords maskOf a := by
  funext S
  change profile (c • a) (maskOf S) = c * profile a (maskOf S)
  generalize maskOf S = i
  fin_cases i <;> simp [profile,Pi.smul_apply,smul_eq_mul] <;> ring

theorem cone_inputs : ConeInputs {w | coords maskOf w ∈ cone 4} := by
  constructor
  · intro a ha b hb
    change coords maskOf (a+b) ∈ cone 4
    rw [add_coords]; exact add_closed ha hb
  · intro a ha c hc
    change coords maskOf (c • a) ∈ cone 4
    rw [scale_coords]; exact scale_closed ha hc
  · have e : wt 0 = ![1,0,0,0,0] := by funext i; fin_cases i <;> rfl
    exact e ▸ subset_closure (fixture_mem 0)
  · have e : wt 1 = ![0,1,0,0,0] := by funext i; fin_cases i <;> rfl
    exact e ▸ subset_closure (fixture_mem 1)
  · have e : wt 2 = ![0,0,1,0,0] := by funext i; fin_cases i <;> rfl
    exact e ▸ subset_closure (fixture_mem 2)

/-- Precisely the two C/D orders of the published DFZ Theorem 10 on actual
finite distributions. Closure, symmetrization, and dyadic estimates are derived. -/
def FiniteDFZ : Prop :=
  ∀ (s : ℕ), 0<s → ∀ h ∈ entropicVectors 4, let H := inflate h
    Direction s (J H) (U H) (W H) (Icd H) (CErr H) (DErr H) ∧
    Direction s (J H) (W H) (U H) (Icd H) (DErr H) (CErr H)

theorem conditional_disproof (tables : ∀ k, LargeTable k) (dfz : FiniteDFZ) :
    ¬ IsSemialgebraic (closure (entropicVectors 4)) := by
  apply disproof_of_profiles maskOf _ isClosed_closure cone_inputs (high_tables tables)
  · exact ⟨wt 3,subset_closure (fixture_mem 3),by change (0:ℝ)<1; norm_num,
      by change (-1:ℝ)≤0; norm_num⟩
  · exact fun _ hw hp s hs => on_closure s (dfz s hs) hw hp

end EntropyFinalBridge
end

section
open EntropySlice EntropyStability EntropyFinalBridge OMA.S_itp_entropy_region
namespace EntropyCopyInduction

/-- Masks in ABCDR have weights 1,2,4,8,16. Mask 0 has entropy zero. -/
abbrev ArrayH := ℕ → ℝ

def mi (H : ArrayH) (a b k : ℕ) :=
  H (a ||| k) + H (b ||| k) - H k - H (a ||| b ||| k)

def err (H : ArrayH) (a b c : ℕ) := mi H a c b + mi H b c a

/-- Coefficients u = 2^s-1, d = (s-2) 2^s/2+1. -/
def gap (H : ArrayH) (a b c e : ℕ) (u d z : ℝ) :=
  (u+z)*mi H a b c + u*mi H a b e + u*mi H c e 0 +
  (d+u)*err H a b c + d*err H a b e - u*mi H a b 0

def copyLaw (H : ArrayH) : Prop :=
  H 16=H 4 ∧ H 17=H 5 ∧ H 18=H 6 ∧ H 19=H 7 ∧ mi H 16 12 3=0

def elemental (H : ArrayH) : Prop := ∀ a b k : ℕ, a &&& b = 0 →
  a &&& k = 0 → b &&& k = 0 → a ||| b ||| k < 32 → 0 ≤ mi H a b k

def cert0 (H : ArrayH) :=
  2*mi H 1 16 14 + 2*mi H 2 16 12 + 3*mi H 4 16 1 + 3*mi H 4 16 2 + 4*mi H 4 16 11 + 3*mi H 8 16 1 + 3*mi H 8 16 2 + 4*mi H 8 16 7

def cert1 (H : ArrayH) :=
  2*mi H 4 16 1 + 2*mi H 4 16 2 + 4*mi H 4 16 11 + 2*mi H 8 16 1 + 2*mi H 8 16 2 + 4*mi H 8 16 7

def cert2 (H : ArrayH) :=
  1*mi H 1 16 14 + 1*mi H 2 16 12 + 1*mi H 4 8 16 + 1*mi H 4 16 1 + 1*mi H 4 16 2 + 1*mi H 4 16 11 + 1*mi H 8 16 1 + 1*mi H 8 16 2 + 1*mi H 8 16 7

/-- Exact polynomial identity for the two substitutions in DFZ Section IX, Rule 6. -/
theorem step_identity (H : ArrayH) (hc : copyLaw H) (u d : ℝ) :
    gap H 1 2 4 8 (2*u+1) (2*d+u) 1 =
      gap H 17 18 24 4 u d 1 + gap H 17 18 20 8 u d 1 +
      u*cert0 H + d*cert1 H + cert2 H := by
  obtain ⟨e₀,e₁,e₂,e₃,ci⟩ := hc
  change H 19 + H 15 - H 3 - H 31 = 0 at ci
  have e₄ : H 31 = H 19 + H 15 - H 3 := by linarith
  simp only [gap,err,mi,cert0,cert1,cert2,Nat.reduceOr]
  rw [e₄,e₀,e₁,e₂,e₃]
  ring

theorem step (H : ArrayH) (hc : copyLaw H) (he : elemental H) (u d : ℝ)
    (hu : 0 ≤ u) (hd : 0 ≤ d) (left : 0 ≤ gap H 17 18 24 4 u d 1)
    (right : 0 ≤ gap H 17 18 20 8 u d 1) :
    0 ≤ gap H 1 2 4 8 (2*u+1) (2*d+u) 1 := by
  have t0 := he 1 16 14 (by decide) (by decide) (by decide) (by decide)
  have t1 := he 2 16 12 (by decide) (by decide) (by decide) (by decide)
  have t2 := he 4 8 16 (by decide) (by decide) (by decide) (by decide)
  have t3 := he 4 16 1 (by decide) (by decide) (by decide) (by decide)
  have t4 := he 4 16 2 (by decide) (by decide) (by decide) (by decide)
  have t5 := he 4 16 11 (by decide) (by decide) (by decide) (by decide)
  have t6 := he 8 16 1 (by decide) (by decide) (by decide) (by decide)
  have t7 := he 8 16 2 (by decide) (by decide) (by decide) (by decide)
  have t8 := he 8 16 7 (by decide) (by decide) (by decide) (by decide)
  have n₀ : 0 ≤ cert0 H := by unfold cert0; positivity
  have n₁ : 0 ≤ cert1 H := by unfold cert1; positivity
  have n₂ : 0 ≤ cert2 H := by unfold cert2; positivity
  rw [step_identity H hc]
  positivity

def u (s : ℕ) : ℝ := 2^s-1
noncomputable def d (s : ℕ) : ℝ := ((s:ℝ)-2)*2^s/2+1

theorem coefficients (s : ℕ) : u (s+1)=2*u s+1 ∧ d (s+1)=2*d s+u s := by
  simp [u,d,pow_succ]
  constructor <;> ring

theorem positive_coefficients (s : ℕ) : 0 ≤ u s ∧ 0 ≤ d s := by
  induction s with
  | zero => norm_num [u,d]
  | succ s ih =>
    rw [(coefficients s).1,(coefficients s).2]
    obtain ⟨h,k⟩ := ih
    constructor <;> positivity

/-- Read the entropy distribution of any four grouped coordinates of H. -/
def groupH (H : ArrayH) (a b c e : ℕ) (i : ℕ) :=
  H ((if i.testBit 0 then a else 0) ||| (if i.testBit 1 then b else 0) |||
    (if i.testBit 2 then c else 0) ||| (if i.testBit 3 then e else 0))

theorem group_gap (H : ArrayH) (a b c e : ℕ) (v w : ℝ) :
    gap (groupH H a b c e) 1 2 4 8 v w 1 = gap H a b c e v w 1 := by
  have lc (x y z : ℕ) : x ||| (y ||| z) = y ||| (x ||| z) := by
    rw [← Nat.or_assoc, Nat.or_comm x y, Nat.or_assoc]
  simp [gap,mi,err,groupH,Nat.or_comm,lc,Nat.testBit]

/-- Finite entropy models are closed under the two groupings of a conditional copy.
The base is ordinary CMI nonnegativity on four variables. -/
structure CopyInputs (D : Set ArrayH) : Prop where
  base : ∀ h ∈ D, 0 ≤ mi h 1 2 4
  extendCopy : ∀ h ∈ D, ∃ H : ArrayH, copyLaw H ∧ elemental H ∧
    (∀ i < 16, H i=h i) ∧ groupH H 17 18 24 4 ∈ D ∧ groupH H 17 18 20 8 ∈ D

theorem induction_on_copies {D : Set ArrayH} (laws : CopyInputs D) (s : ℕ) :
    ∀ h ∈ D, 0 ≤ gap h 1 2 4 8 (u s) (d s) 1 := by
  induction s with
  | zero =>
    intro h hh
    simpa [u,d,gap] using laws.base h hh
  | succ s ih =>
    intro h hh
    obtain ⟨H,hc,he,h₀,h₁,h₂⟩ := laws.extendCopy h hh
    have a := ih _ h₁
    have b := ih _ h₂
    rw [group_gap] at a b
    have hn := positive_coefficients s
    have hs := step H hc he _ _ hn.1 hn.2 a b
    rw [(coefficients s).1,(coefficients s).2]
    convert hs using 1
    simp only [gap,err,mi,Nat.reduceOr]
    simp only [h₀ 0 (by decide), h₀ 1 (by decide), h₀ 2 (by decide), h₀ 3 (by decide), h₀ 4 (by decide), h₀ 5 (by decide), h₀ 6 (by decide), h₀ 7 (by decide), h₀ 8 (by decide), h₀ 9 (by decide), h₀ 10 (by decide), h₀ 11 (by decide), h₀ 12 (by decide)]

noncomputable def arrayOf (h : EntropyOfficial.Idx 4 → ℝ) : ArrayH :=
  fun i => inflate h (Fin.ofNat 16 i)

def Models : Set ArrayH := {g | ∃ h ∈ entropicVectors 4,
  (∀ i < 16, g i=arrayOf h i) ∨ (∀ i < 16, g i=groupH (arrayOf h) 1 2 8 4 i)}

theorem direction_iff (H : Fin 16 → ℝ) (hz : H 0=0) (s : ℕ) (sw : Bool) :
    let h : ArrayH := fun i => H (Fin.ofNat 16 i)
    let c := if sw then 8 else 4
    let e := if sw then 4 else 8
    0 ≤ gap h 1 2 c e (u s) (d s) 1 ↔
      Direction s (J H) (if sw then W H else U H) (if sw then U H else W H)
        (Icd H) (if sw then DErr H else CErr H) (if sw then CErr H else DErr H) := by
  cases sw <;> simp only [Bool.false_eq_true,↓reduceIte,Bool.true_eq, gap,mi,err,
    Nat.reduceOr,Direction,J,W,U,Icd,DErr,CErr,u,d]
    <;> simp only [show Fin.ofNat 16 0 = 0 from rfl, show Fin.ofNat 16 1 = 1 from rfl, show Fin.ofNat 16 2 = 2 from rfl, show Fin.ofNat 16 3 = 3 from rfl, show Fin.ofNat 16 4 = 4 from rfl, show Fin.ofNat 16 5 = 5 from rfl, show Fin.ofNat 16 6 = 6 from rfl, show Fin.ofNat 16 7 = 7 from rfl, show Fin.ofNat 16 8 = 8 from rfl, show Fin.ofNat 16 9 = 9 from rfl, show Fin.ofNat 16 10 = 10 from rfl, show Fin.ofNat 16 11 = 11 from rfl, show Fin.ofNat 16 12 = 12 from rfl, hz, sub_zero]
    <;> constructor <;> intro ha <;> nlinarith only [ha,hz]

theorem finiteDFZ (laws : CopyInputs Models) : FiniteDFZ := by
  intro s _ h hh
  let H := arrayOf h
  have a : H ∈ Models := ⟨h,hh,Or.inl (fun _ _ => rfl)⟩
  have b : groupH H 1 2 8 4 ∈ Models := ⟨h,hh,Or.inr (fun _ _ => rfl)⟩
  have ha := induction_on_copies laws s H a
  have hb := induction_on_copies laws s _ b
  rw [group_gap] at hb
  have hz : inflate h 0=0 := by
    have he : ¬(EntropyFixtures.decode 0).Nonempty := by decide
    simp [inflate,he]
  exact ⟨(direction_iff _ hz s false).mp ha,(direction_iff _ hz s true).mp hb⟩

end EntropyCopyInduction
end

section
open Finset
namespace EntropyRegularRows

/-- Number of preimages at an observed value. -/
noncomputable def mult {Ω X : Type*} (f : Ω → X) (a : Ω) := Nat.card {b // f b=f a}

def Regular {Ω X : Type*} (f : Ω → X) (n : ℕ) := ∀ a, mult f a=n

theorem same {Ω X Y : Type*} {f : Ω → X} {g : Ω → Y} {n : ℕ}
    (h : ∀ x y, f x=f y ↔ g x=g y) (hr : Regular g n) : Regular f n := by
  intro a
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun b => h b a)).trans (hr a)

theorem chart {Ω Ω' X : Type*} (e : Ω ≃ Ω') (f : Ω' → X) {n : ℕ}
    (hr : Regular f n) : Regular (f ∘ e) n := by
  intro a
  exact (Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)).trans (hr (e a))

theorem ident (Ω : Type*) : Regular (id : Ω → Ω) 1 := by
  intro a
  let e : {b // id b=id a} ≃ Unit :=
    { toFun := fun _ => (), invFun := fun _ => ⟨a,rfl⟩
      left_inv := fun b => Subtype.ext b.2.symm, right_inv := fun _ => rfl }
  simpa [mult] using Nat.card_congr e

theorem const (Ω : Type*) : Regular (fun _ : Ω => Unit.unit) (Nat.card Ω) := by
  intro a
  exact Nat.card_congr (Equiv.subtypeUnivEquiv (by simp))

theorem product {Ω Ξ X Y : Type*} {f : Ω → X} {g : Ξ → Y} {m n : ℕ}
    (hf : Regular f m) (hg : Regular g n) : Regular (Prod.map f g) (m*n) := by
  intro ⟨a,b⟩
  let e : {y : Ω × Ξ // Prod.map f g y=Prod.map f g (a,b)} ≃
      {v // f v=f a} × {v // g v=g b} :=
    { toFun := fun y => (⟨y.1.1,congrArg Prod.fst y.2⟩,⟨y.1.2,congrArg Prod.snd y.2⟩)
      invFun := fun y => ⟨(y.1.1,y.2.1),Prod.ext y.1.2 y.2.2⟩
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [mult,Nat.card_congr e,Nat.card_prod]
  exact congrArg₂ (·*·) (hf a) (hg b)

/-- A tag is retained. Only the fibre over that fixed tag contributes. -/
theorem tagged {I Ω X : Type*} (f : I → Ω → X) {n : ℕ}
    (h : ∀ i, Regular (f i) n) : Regular (fun x : I × Ω => (x.1,f x.1 x.2)) n := by
  intro ⟨i,a⟩
  let e : {y : I × Ω // (y.1,f y.1 y.2)=(i,f i a)} ≃ {b // f i b=f i a} :=
    { toFun := fun ⟨⟨j,b⟩,hh⟩ => ⟨b, by
        obtain ⟨rfl,hb⟩ := Prod.mk.inj hh
        exact hb⟩
      invFun := fun b => ⟨(i,b.1),Prod.ext rfl b.2⟩
      left_inv := fun ⟨⟨j,b⟩,hh⟩ => by obtain ⟨rfl,_⟩ := Prod.mk.inj hh; rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (h i a)

theorem ignoreRight {Ω Ξ X : Type*} {f : Ω → X} {n : ℕ} (h : Regular f n) :
    Regular (fun x : Ω × Ξ => f x.1) (n*Nat.card Ξ) :=
  same (fun _ _ => by simp [Prod.map,Prod.ext_iff]) (product h (const Ξ))

theorem ignoreLeft {Ω Ξ Y : Type*} {g : Ξ → Y} {n : ℕ} (h : Regular g n) :
    Regular (fun x : Ω × Ξ => g x.2) (Nat.card Ω*n) :=
  same (fun _ _ => by simp [Prod.map,Prod.ext_iff]) (product (const Ω) h)

theorem inj_reg {Ω X : Type*} {f : Ω → X} (hf : Function.Injective f) : Regular f 1 :=
  same (fun _ _ => hf.eq_iff) (ident Ω)

/-- Uniformity on attained values gives the full histogram, including missing values. -/
theorem histogram {Ω X : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq X]
    (f : Ω → X) (n : ℕ) (h : Regular f n) :
    let s := univ.image f
    0 < s.card ∧ 0 < n ∧ Fintype.card Ω = s.card*n ∧
    ∀ y, (univ.filter fun x => f x=y).card=if y∈s then n else 0 := by
  classical
  let s := univ.image f
  have ha (a : Ω) : (univ.filter fun b => f b=f a).card=n := by
    simpa only [mult,Nat.card_eq_fintype_card,Fintype.card_subtype] using h a
  have hall (y : X) : (univ.filter fun x => f x=y).card=if y∈s then n else 0 := by
    split_ifs with hy
    · obtain ⟨a,_,rfl⟩ := mem_image.mp hy
      exact ha a
    · apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro a hh
      exact hy (mem_image.mpr ⟨a,mem_univ _,(mem_filter.mp hh).2⟩)
  have a := Classical.choice (inferInstance : Nonempty Ω)
  refine ⟨card_pos.mpr ⟨f a,mem_image_of_mem f (mem_univ a)⟩,?_,?_,hall⟩
  · rw [← ha a]; exact card_pos.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  · have hc := card_eq_sum_card_image f univ
    change univ.card=∑ y∈s,_ at hc
    have hc' : ∑ y∈s,(univ.filter fun x => f x=y).card=∑ _y∈s,n :=
      sum_congr rfl (fun y hy => (hall y).trans (if_pos hy))
    simpa [s] using hc.trans hc'

end EntropyRegularRows
end

section
open Finset EntropyOfficial EntropyOperations EntropyPushforward EntropyCopyInduction
namespace EntropyMaskLaws
variable {Ω X Y Z : Type} [Fintype Ω] [Fintype X] [Fintype Y] [Fintype Z]

theorem obs_same (p : Ω → ℝ) (f : Ω → X) (g : Ω → Y)
    (same : ∀ a b, f a=f b ↔ g a=g b) : obs p f=obs p g := by
  classical
  letI := Fintype.ofFinite (Set.range f)
  let r := Set.rangeFactorization f
  let v (x : Set.range f) := g x.2.choose
  have hv (x : Ω) : v (r x)=g x := (same _ _).mp (r x).2.choose_spec
  have inj : Function.Injective v := by
    intro x y h
    exact Subtype.ext (x.2.choose_spec.symm.trans (((same _ _).mpr h).trans y.2.choose_spec))
  have h₁ := obs_inj p r Subtype.val Subtype.val_injective
  have h₂ := obs_inj p r v inj
  have eq : v ∘ r=g := funext hv
  rw [eq] at h₂
  exact h₁.trans h₂.symm

theorem obs_push (p : Ω → ℝ) (f : Ω → X) (g : X → Y) :
    obs (push p f) g = obs p (g ∘ f) := by unfold obs; rw [push_comp]

theorem proj_left (p : X × Y → ℝ) : push p Prod.fst = fun x => ∑ y,p (x,y) := by
  classical
  funext x
  simp only [push,Fintype.sum_prod_type]
  rw [sum_eq_single x]
  · simp
  · intro y _ hn; simp [hn]
  · simp

theorem proj_right (p : X × Y → ℝ) : push p Prod.snd = fun y => ∑ x,p (x,y) := by
  classical funext y; simp [push,Fintype.sum_prod_type]

theorem proj12 (p : X × Y × Z → ℝ) :
    push p (fun t => (t.1,t.2.1)) = fun v => ∑ z,p (v.1,v.2,z) := by
  classical
  funext v
  obtain ⟨v₁,v₂⟩ := v
  simp only [push,Fintype.sum_prod_type,Prod.mk.injEq]
  rw [sum_eq_single v₁]
  · rw [sum_eq_single v₂]
    · simp
    · intro y _ hn; simp [hn]
    · simp
  · intro x _ hn; simp [hn]
  · simp

theorem proj13 (p : X × Y × Z → ℝ) :
    push p (fun t => (t.1,t.2.2)) = fun v => ∑ y,p (v.1,y,v.2) := by
  classical
  funext v
  obtain ⟨v₁,v₂⟩ := v
  simp only [push,Fintype.sum_prod_type,Prod.mk.injEq]
  rw [sum_eq_single v₁]
  · simp
  · intro x _ hn; simp [hn]
  · simp

variable {n : ℕ}

def mask (r : Ω → Fin n → X) (m : ℕ) (x : Ω) (j : Fin n) : Option X :=
  if m.testBit j.val then some (r x j) else none

noncomputable def H (p : Ω → ℝ) (r : Ω → Fin n → X) (m : ℕ) := obs p (mask r m)

theorem mask_eq (r : Ω → Fin n → X) (m : ℕ) (x y : Ω) :
    mask r m x=mask r m y ↔ ∀ j : Fin n, m.testBit j.val=true → r x j=r y j := by
  constructor
  · intro h j hj; simpa [mask,hj] using congrFun h j
  · intro h; funext j; by_cases e : m.testBit j.val=true <;> simp [mask,e,h]

theorem union_eq (r : Ω → Fin n → X) (a b : ℕ) (x y : Ω) :
    mask r (a ||| b) x=mask r (a ||| b) y ↔
    mask r a x=mask r a y ∧ mask r b x=mask r b y := by
  simp only [mask_eq,Nat.testBit_or,Bool.or_eq_true]
  constructor
  · intro h; exact ⟨fun j e => h j (Or.inl e),fun j e => h j (Or.inr e)⟩
  · rintro ⟨h,k⟩ j (e|e)
    exacts [h j e,k j e]

theorem mi_nonneg (p : Ω → ℝ) (hp : ∀ x,0≤p x) (r : Ω → Fin n → X)
    (a b k : ℕ) : 0 ≤ mi (H p r) a b k := by
  let f x := (mask r k x,mask r a x,mask r b x)
  let P := push p f
  have h := EntropyShannon.conditional (fun i j l => P (i,j,l))
    (fun i j l => push_nonneg p hp f (i,j,l))
  have full : H p r (a ||| b ||| k)=ent P := obs_same p _ f (fun x y => by
    simp only [union_eq,f,Prod.mk.injEq]; tauto)
  have h₀ : H p r k=obs P Prod.fst := by rw [obs_push]; rfl
  have h₁ : H p r (a ||| k)=obs P (fun z => (z.1,z.2.1)) := by
    rw [obs_push]; apply obs_same
    intro x y; simp only [Function.comp_apply,f,union_eq,Prod.mk.injEq]; tauto
  have h₂ : H p r (b ||| k)=obs P (fun z => (z.1,z.2.2)) := by
    rw [obs_push]; apply obs_same
    intro x y; simp only [Function.comp_apply,f,union_eq,Prod.mk.injEq]; tauto
  simp only [obs,proj_left,proj12,proj13,Fintype.sum_prod_type] at h₀ h₁ h₂
  unfold mi
  rw [full,h₀,h₁,h₂]
  linarith only [h]

end EntropyMaskLaws
end

section
open EntropyRegularRows
namespace EntropyCosetRows

variable {W E S T : Type*} [AddCommGroup W] [AddCommGroup E]

def cos (K : AddSubgroup W) (a : W) : Set W := {b | b-a ∈ K}

theorem cos_eq (K : AddSubgroup W) (x y : W) : cos K x=cos K y ↔ x-y∈K := by
  constructor
  · intro h
    have hx : x∈cos K x := by simp [cos]
    rw [h] at hx
    exact hx
  · intro h
    ext b
    change b-x∈K ↔ b-y∈K
    constructor
    · intro hh
      simpa using K.add_mem hh h
    · intro hh
      simpa using K.sub_mem hh h

theorem diff_count (K : AddSubgroup W) (a : W) :
    Nat.card {b : W // b-a∈K} = Nat.card K := by
  let e : {b : W // b-a∈K} ≃ K :=
    { toFun := fun b => ⟨b.1-a,b.2⟩
      invFun := fun b => ⟨b.1+a,by simpa using b.2⟩
      left_inv := fun b => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun b => Subtype.ext (add_sub_cancel_right _ _) }
  exact Nat.card_congr e

theorem single (K : AddSubgroup W) : Regular (cos K) (Nat.card K) := fun a =>
  (Nat.card_congr (Equiv.subtypeEquivRight fun b => cos_eq K b a)).trans (diff_count K a)

theorem joint (L R : AddSubgroup W) :
    Regular (fun a => (cos L a,cos R a)) (Nat.card (L ⊓ R : AddSubgroup W)) := by
  intro a
  apply Eq.trans _ (diff_count (L ⊓ R) a)
  apply Nat.card_congr (Equiv.subtypeEquivRight _)
  intro b
  exact Prod.mk.injEq .. ▸ (and_congr (cos_eq L b a) (cos_eq R b a))

abbrev Row (W E S T : Type*) := (E × S) × (W × T)
variable (shift : E → T → W) (p : S → E)

def point (x : Row W E S T) := x.2.1 + shift x.1.1 x.2.2
def tag (p : S → E) (x : Row W E S T) := x.1.1+p x.1.2
def side (p : S → E) (L : E → AddSubgroup W) (x : Row W E S T) :=
  (tag p x,cos (L (tag p x)) x.2.1)

/-- (edge, parameter, origin, scalar) may be sampled as (tag, endpoint, parameter, scalar). -/
def sideChart : Row W E S T ≃ E × (W × (S × T)) where
  toFun x := (tag p x, point shift x, x.1.2,x.2.2)
  invFun y := ((y.1-p y.2.2.1,y.2.2.1),
    (y.2.1-shift (y.1-p y.2.2.1) y.2.2.2,y.2.2.2))
  left_inv x := by rcases x with ⟨⟨e,s⟩,a,t⟩; simp [tag,point]
  right_inv y := by rcases y with ⟨i,b,s,t⟩; simp [tag,point]

theorem point_reg : Regular (point (S:=S) shift) (Nat.card E * (Nat.card S * Nat.card T)) := by
  have hh := chart (sideChart shift (fun _ : S => (0:E)))
    (fun y : E × (W × (S × T)) => y.2.1)
    (ignoreLeft (Ω:=E) (ignoreRight (Ξ:=S × T) (ident W)))
  change Regular (fun x : Row W E S T => point shift x) _
  simpa [Nat.card_prod,Function.comp_def,sideChart] using hh

theorem side_reg (L : E → AddSubgroup W) (l : ℕ) (h : ∀ i, Nat.card (L i)=l) :
    Regular (side (T:=T) p L) (l*(Nat.card S*Nat.card T)) := by
  have hh (i : E) : Regular (fun y : W × (S × T) => cos (L i) y.1) (l*(Nat.card S*Nat.card T)) := by
    simpa [Nat.card_prod,h] using ignoreRight (Ξ:=S × T) (single (L i))
  have hr := chart (sideChart (fun _ _ => (0:W)) p) _ (tagged _ hh)
  change Regular (fun x : Row W E S T => (tag p x,cos (L (tag p x)) x.2.1)) _
  simpa [Function.comp_def,sideChart,point] using hr

theorem point_side (L : E → AddSubgroup W)
    (mem : ∀ (e : E) (s : S) (t : T), shift e t ∈ L (e+p s)) :
    Regular (fun x => (point shift x,side p L x)) (Nat.card S*Nat.card T) := by
  have hh (i : E) : Regular (fun y : W × (S × T) => y.1) (Nat.card S*Nat.card T) := by
    simpa [Nat.card_prod] using ignoreRight (Ξ:=S × T) (ident W)
  have hr := chart (sideChart shift p) _ (tagged _ hh)
  apply same _ hr
  intro x y
  have inv (z : Row W E S T) : cos (L (tag p z)) (point shift z)=cos (L (tag p z)) z.2.1 :=
    (cos_eq _ _ _).mpr (by simpa [point,tag] using mem z.1.1 z.1.2 z.2.2)
  change (point shift x,side p L x)=(point shift y,side p L y) ↔
    (tag p x,point shift x)=(tag p y,point shift y)
  simp only [side,← inv,Prod.mk.injEq]
  constructor
  · rintro ⟨ha,hi,_⟩; exact ⟨hi,ha⟩
  · rintro ⟨hi,ha⟩; simp [hi,ha]

theorem side_pair (p r : S → E) (L R : E → AddSubgroup W)
    (decode : Function.Injective fun v : E × S => (v.1+p v.2,v.1+r v.2))
    (l : ℕ) (dim : ∀ (e : E) (s : S), Nat.card (L (e+p s) ⊓ R (e+r s) : AddSubgroup W)=l) :
    Regular (fun x : Row W E S T => (side p L x,side r R x)) (l*Nat.card T) := by
  let f (v : E × S) (a : W) := (cos (L (v.1+p v.2)) a,cos (R (v.1+r v.2)) a)
  have h (v : E × S) : Regular (fun z : W × T => f v z.1) (l*Nat.card T) := by
    rw [← dim v.1 v.2]
    exact ignoreRight (Ξ:=T) (joint (L (v.1+p v.2)) (R (v.1+r v.2)))
  apply same _ (tagged _ h)
  rintro ⟨v,ax,tx⟩ ⟨w,ay,ty⟩
  simp only [side,tag,f,Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hi,hl⟩,hj,hr⟩
    exact ⟨decode (Prod.ext hi hj),hl,hr⟩
  · rintro ⟨rfl,hl,hr⟩
    exact ⟨⟨rfl,hl⟩,rfl,hr⟩

/-- Keeping the two endpoints determines the edge label and scalar. -/
theorem endpoints (inj : Function.Injective fun z : E × T => shift z.1 z.2) :
    Regular (fun x : Row W E S T => (x.2.1,point shift x)) (Nat.card S) := by
  let e : Row W E S T ≃ (W × E × T) × S :=
    { toFun := fun x => ((x.2.1,x.1.1,x.2.2),x.1.2)
      invFun := fun y => ((y.1.2.1,y.2),y.1.1,y.1.2.2)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have h := chart e _ (ignoreRight (Ξ:=S) (ident (W × E × T)))
  rw [one_mul] at h
  apply same _ h
  rintro ⟨⟨i,s⟩,a,t⟩ ⟨⟨j,r⟩,b,u⟩
  change (a,a+shift i t)=(b,b+shift j u) ↔ (a,i,t)=(b,j,u)
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨rfl,hb⟩
    have he : (i,t)=(j,u) := inj (add_left_cancel hb)
    exact ⟨rfl,Prod.mk.inj he⟩
  · rintro ⟨rfl,rfl,rfl⟩; exact ⟨rfl,rfl⟩

theorem endpoints_side (L : E → AddSubgroup W)
    (inj : Function.Injective fun z : E × T => shift z.1 z.2)
    (hp : Function.Injective p) :
    Function.Injective fun x : Row W E S T => (x.2.1,point shift x,side p L x) := by
  rintro ⟨⟨e,s⟩,a,t⟩ ⟨⟨j,r⟩,b,u⟩ h
  obtain ⟨rfl,hrest⟩ := Prod.mk.inj h
  obtain ⟨hb,hc⟩ := Prod.mk.inj hrest
  have he : (e,t)=(j,u) := inj (add_left_cancel hb)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  have hh : e+p s=e+p r := congrArg Prod.fst hc
  obtain rfl := hp (add_left_cancel hh)
  rfl

theorem endpoint_both (p r : S → E) (L R : E → AddSubgroup W)
    (decode : Function.Injective fun v : E × S => (v.1+p v.2,v.1+r v.2))
    (ml : ∀ e s t, shift e t ∈ L (e+p s)) (mr : ∀ e s t, shift e t ∈ R (e+r s)) :
    Regular (fun x : Row W E S T => (point shift x,side p L x,side r R x)) (Nat.card T) := by
  let c : Row W E S T ≃ ((E × S) × W) × T :=
    { toFun := fun x => ((x.1,point shift x),x.2.2)
      invFun := fun y => (y.1.1,y.1.2-shift y.1.1.1 y.2,y.2)
      left_inv := fun x => by simp [point]
      right_inv := fun y => by simp [point] }
  have h := chart c _ (ignoreRight (Ξ:=T) (ident ((E × S) × W)))
  rw [one_mul] at h
  apply same _ h
  intro x y
  have inv (u : S → E) (K : E → AddSubgroup W)
      (m : ∀ e s t, shift e t ∈ K (e+u s)) (z : Row W E S T) :
      cos (K (tag u z)) (point shift z)=cos (K (tag u z)) z.2.1 :=
    (cos_eq _ _ _).mpr (by simpa [point,tag] using m z.1.1 z.1.2 z.2.2)
  change (point shift x,side p L x,side r R x)=(point shift y,side p L y,side r R y) ↔
    (x.1,point shift x)=(y.1,point shift y)
  simp only [side,← inv p L ml,← inv r R mr,Prod.mk.injEq]
  constructor
  · rintro ⟨ha,⟨hl,_⟩,hr,_⟩; exact ⟨decode (Prod.ext hl hr),ha⟩
  · rintro ⟨hk,ha⟩
    have hl : tag p x=tag p y := by simp [tag,hk]
    have hr : tag r x=tag r y := by simp [tag,hk]
    simp [hl,hr,ha]

end EntropyCosetRows
end

section
open Finset EntropyOperations EntropyPushforward EntropyMaskLaws EntropyCopyInduction
open EntropyOfficial EntropyStability EntropyFixtures OMA.S_itp_entropy_region
namespace EntropyMaskModels
variable {Ω X : Type} [Fintype Ω] [Fintype X]

theorem eq4 (r : Ω → Fin 4 → X) (m : ℕ) (x y : Ω) :
    mask r m x=mask r m y ↔
    (m.testBit 0=true → r x 0=r y 0) ∧ (m.testBit 1=true → r x 1=r y 1) ∧ (m.testBit 2=true → r x 2=r y 2) ∧ (m.testBit 3=true → r x 3=r y 3) := by
  rw [mask_eq]
  constructor
  · intro h; exact ⟨h 0,h 1,h 2,h 3⟩
  · rintro ⟨h0,h1,h2,h3⟩ j; fin_cases j
    exacts [h0,h1,h2,h3]

theorem eq5 (r : Ω → Fin 5 → X) (m : ℕ) (x y : Ω) :
    mask r m x=mask r m y ↔
    (m.testBit 0=true → r x 0=r y 0) ∧ (m.testBit 1=true → r x 1=r y 1) ∧ (m.testBit 2=true → r x 2=r y 2) ∧ (m.testBit 3=true → r x 3=r y 3) ∧ (m.testBit 4=true → r x 4=r y 4) := by
  rw [mask_eq]
  constructor
  · intro h; exact ⟨h 0,h 1,h 2,h 3,h 4⟩
  · rintro ⟨h0,h1,h2,h3,h4⟩ j; fin_cases j
    exacts [h0,h1,h2,h3,h4]

def Concrete : Set ArrayH := {h | ∃ (Ω X : Type) (_ : Fintype Ω) (_ : Fintype X)
  (p : Ω → ℝ) (r : Ω → Fin 4 → X), (∀ x,0≤p x) ∧ (∑ x,p x=1) ∧
    ∀ i < 16, h i = H p r i}

theorem group_real {n : ℕ} (p : Ω → ℝ) (r : Ω → Fin n → X) (a b c d : ℕ)
    (hp : ∀ x,0≤p x) (hs : ∑ x,p x=1) : groupH (H p r) a b c d ∈ Concrete := by
  let rows x := ![mask r a x,mask r b x,mask r c x,mask r d x]
  refine ⟨Ω,Fin n → Option X,inferInstance,inferInstance,p,rows,hp,hs,?_⟩
  intro i _
  apply obs_same
  intro x y
  change mask r ((if i.testBit 0 then a else 0) ||| (if i.testBit 1 then b else 0) |||
    (if i.testBit 2 then c else 0) ||| (if i.testBit 3 then d else 0)) x = _ ↔ _
  have h (j k : ℕ) : mask r (if i.testBit j then k else 0) x =
      mask r (if i.testBit j then k else 0) y ↔ (i.testBit j=true → mask r k x=mask r k y) := by
    cases h : i.testBit j <;> simp [mask_eq]
  rw [union_eq,union_eq,union_eq,eq4]
  simp only [h,rows,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  tauto

theorem obs_empty (p : Ω → ℝ) (hs : ∑ x,p x=1) {n : ℕ} (r : Ω → Fin n → X) :
    H p r 0=0 := by
  have e := obs_same p (mask r 0) (fun _ => ()) (fun x y => by simp [mask_eq])
  change obs p (mask r 0)=0
  rw [e]
  simp [obs,ent,push,hs]

theorem coordinates (p : Ω → ℝ) (hs : ∑ x,p x=1) (r : Ω → Fin 4 → X) (i : ℕ) (hi : i<16) :
    arrayOf (vec p r) i=H p r i := by
  let k := Fin.ofNat 16 i
  have ek : k.val=i := Nat.mod_eq_of_lt hi
  by_cases hn : (decode k).Nonempty
  · change (if hh : (decode k).Nonempty then vec p r ⟨decode k,hh⟩ else 0)=_
    rw [dif_pos hn]
    apply obs_same
    intro a b
    rw [mask_eq]
    constructor
    · intro hh j hj
      exact congrFun hh ⟨j,by simpa [decode,ek] using hj⟩
    · intro hh
      funext j
      exact hh j.1 (by simpa [decode,ek] using j.2)
  · have hk : k=0 := by
      rw [← code_decode k,Finset.not_nonempty_iff_eq_empty.mp hn]; decide
    have h0 : i=0 := ek.symm.trans (congrArg Fin.val hk)
    change (if hh : (decode k).Nonempty then vec p r ⟨decode k,hh⟩ else 0)=H p r i
    rw [dif_neg hn,h0,obs_empty p hs]

theorem actual {h : EntropyOfficial.Idx 4 → ℝ} (hh : h∈entropicVectors 4) :
    ∃ (Ω X : Type) (_ : Fintype Ω) (_ : Fintype X) (p : Ω → ℝ) (r : Ω → Fin 4 → X),
      (∀ x,0≤p x) ∧ (∑ x,p x=1) ∧ ∀ i<16, arrayOf h i=H p r i := by
  obtain ⟨k,p,hp,hs,h⟩ := hh
  have he : _ = vec p id := funext (fun S => (h S).trans (sub_eq p S))
  exact ⟨_,_,inferInstance,inferInstance,p,id,hp,hs,fun i hi => he ▸ coordinates p hs id i hi⟩

theorem in_models {h : ArrayH} (hh : h∈Concrete) : h∈Models := by
  obtain ⟨Ω,X,fo,fx,p,r,hp,hs,hg⟩ := hh
  exact ⟨vec p r,realize p r hp hs,Or.inl (fun i hi => (hg i hi).trans (coordinates p hs r i hi).symm)⟩

theorem concrete_replace {g h : ArrayH} (hg : g∈Concrete) (he : ∀ i<16, h i=g i) : h∈Concrete := by
  obtain ⟨Ω,X,fo,fx,p,r,hp,hs,hg⟩ := hg
  exact ⟨Ω,X,fo,fx,p,r,hp,hs,fun i hi => (he i hi).trans (hg i hi)⟩

theorem concrete_models : Concrete=Models := by
  ext h
  refine ⟨in_models,?_⟩
  rintro ⟨v,hv,hh⟩
  obtain ⟨Ω,X,fo,fx,p,r,hp,hs,ha⟩ := actual hv
  obtain h₁ | h₂ := hh
  · exact ⟨Ω,X,fo,fx,p,r,hp,hs,fun i hi => (h₁ i hi).trans (ha i hi)⟩
  · apply concrete_replace (group_real p r 1 2 8 4 hp hs)
    intro i hi
    rw [h₂ i hi]
    apply ha
    cases e₀ : i.testBit 0 <;> cases e₁ : i.testBit 1 <;> cases e₂ : i.testBit 2 <;>
      cases e₃ : i.testBit 3 <;> simp [e₀,e₁,e₂,e₃]

end EntropyMaskModels
end

section
open EntropyRegularRows EntropyCosetRows EntropyFinalBridge EntropyLargeRatio
open EntropyOfficial EntropyStability EntropyCounts EntropyFixtures Finset
namespace EntropyTableGeometry

def fibre (d q m : ℕ) (i : Fin 16) :=
  let r := d+1
  match i.val with
  | 0 => q^(2*d+1)*m*r*(q-1)
  | 1 | 2 => m*(r*(q-1))
  | 3 => r
  | 4 | 8 => q^(d+1)*(r*(q-1))
  | 5 | 6 | 9 | 10 => r*(q-1)
  | 12 => q*(q-1)
  | 13 | 14 => q-1
  | _ => 1

theorem total (d q m : ℕ) (i : Fin 16) :
    supportCard d q m i*fibre d q m i=q^(2*d+1)*m*(d+1)*(q-1) := by
  fin_cases i <;> simp [fibre,supportCard,two_mul,pow_add] <;> ring

structure Geometry (W E S T : Type) [AddCommGroup W] [AddCommGroup E] (d q m : ℕ) where
  colour : S → E
  shift : E → T → W
  L : E → AddSubgroup W
  R : E → AddSubgroup W
  edge : Function.Injective fun x : E × S => (x.1+(-colour x.2),x.1+colour x.2)
  jump : Function.Injective fun x : E × T => shift x.1 x.2
  left_mem : ∀ e s t, shift e t ∈ L (e+(-colour s))
  right_mem : ∀ e s t, shift e t ∈ R (e+colour s)
  left_size : ∀ i, Nat.card (L i)=q^(d+1)
  right_size : ∀ j, Nat.card (R j)=q^(d+1)
  overlap : ∀ e s, Nat.card (L (e+(-colour s)) ⊓ R (e+colour s) : AddSubgroup W)=q
  points : Nat.card W=q^(2*d+1)
  labels : Nat.card E=m
  colours : Nat.card S=d+1
  scalars : Nat.card T=q-1

abbrev Alphabet (W E : Type) := W ⊕ (E × Set W)
variable {W E S T : Type} [AddCommGroup W] [AddCommGroup E] {d q m : ℕ}

def row (g : Geometry W E S T d q m) (x : Row W E S T) : Fin 4 → Alphabet W E :=
  ![Sum.inl x.2.1,Sum.inl (point g.shift x),
    Sum.inr (side (fun s => -g.colour s) g.L x),Sum.inr (side g.colour g.R x)]

def view {Ω X : Type} (f : Ω → Fin 4 → X) (i : Fin 16) (a : Ω) :=
  fun t : decode i => f a t.1

theorem view_eq {Ω X : Type} (f : Ω → Fin 4 → X) (i : Fin 16) (a b : Ω) :
    view f i a=view f i b ↔
    (i.val.testBit 0=true → f a 0=f b 0) ∧ (i.val.testBit 1=true → f a 1=f b 1) ∧
    (i.val.testBit 2=true → f a 2=f b 2) ∧ (i.val.testBit 3=true → f a 3=f b 3) := by
  have hv (t : Fin 4) : t∈decode i ↔ i.val.testBit t.val=true := by simp [decode]
  constructor
  · intro h
    have u (t : Fin 4) (ht : i.val.testBit t.val=true) := congrFun h ⟨t,(hv t).mpr ht⟩
    exact ⟨u 0,u 1,u 2,u 3⟩
  · rintro ⟨h₀,h₁,h₂,h₃⟩
    funext ⟨t,ht⟩
    have hh := (hv t).mp ht
    fin_cases t
    exacts [h₀ hh,h₁ hh,h₂ hh,h₃ hh]

theorem regular (g : Geometry W E S T d q m) (i : Fin 16) :
    Regular (view (row g) i) (fibre d q m i) := by
  let p := fun s => -g.colour s
  let r := g.colour
  let z := fun (_ : E) (_ : T) => (0:W)
  have lc (e : E) (s : S) (t : T) : z e t ∈ g.L (e+p s) := (g.L _).zero_mem
  have rc (e : E) (s : S) (t : T) : z e t ∈ g.R (e+r s) := (g.R _).zero_mem
  have ci : Function.Injective r := by
    intro a b h
    have ee : ((0:E),a)=((0:E),b) := g.edge (by change (_,_) = (_,_); simp [r] at h; simp [h])
    exact congrArg Prod.snd ee
  have ni : Function.Injective p := fun _ _ h => ci (neg_inj.mp h)
  have both := endpoints_side g.shift p g.L g.jump ni
  have four : Function.Injective (fun x : Row W E S T =>
      (x.2.1,point g.shift x,side p g.L x,side r g.R x)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact both (Prod.ext h.1 (Prod.ext h.2.1 h.2.2.1))
  fin_cases i
  · have h := const (Row W E S T)
    have hh := same (f:=view (row g) 0) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := point_reg (S:=S) z
    have hh := same (f:=view (row g) 1) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq,point,z]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := point_reg (S:=S) g.shift
    have hh := same (f:=view (row g) 2) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := endpoints (S:=S) g.shift g.jump
    have hh := same (f:=view (row g) 3) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := side_reg (T:=T) p g.L _ g.left_size
    have hh := same (f:=view (row g) 4) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := point_side z p g.L lc
    have hh := same (f:=view (row g) 5) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq,point,z]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := point_side g.shift p g.L g.left_mem
    have hh := same (f:=view (row g) 6) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := inj_reg both
    have hh := same (f:=view (row g) 7) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := side_reg (T:=T) r g.R _ g.right_size
    have hh := same (f:=view (row g) 8) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := point_side z r g.R rc
    have hh := same (f:=view (row g) 9) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq,point,z]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := point_side g.shift r g.R g.right_mem
    have hh := same (f:=view (row g) 10) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := inj_reg (endpoints_side g.shift r g.R g.jump ci)
    have hh := same (f:=view (row g) 11) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := side_pair (T:=T) p r g.L g.R g.edge q g.overlap
    have hh := same (f:=view (row g) 12) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := endpoint_both z p r g.L g.R g.edge lc rc
    have hh := same (f:=view (row g) 13) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq,point,z]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := endpoint_both g.shift p r g.L g.R g.edge g.left_mem g.right_mem
    have hh := same (f:=view (row g) 14) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh
  · have h := inj_reg four
    have hh := same (f:=view (row g) 15) (n:=_) (g:=_) (fun x y => by
      simp [view_eq,row,Nat.testBit,p,r,Prod.mk.injEq]) h
    simpa [fibre,Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,mul_assoc,mul_left_comm,mul_comm] using hh

end EntropyTableGeometry
end

section
open EntropyRegularRows EntropyCosetRows EntropyFinalBridge EntropyLargeRatio
open EntropyOfficial EntropyStability EntropyCounts EntropyFixtures EntropyTableGeometry
open OMA.S_itp_entropy_region Finset

namespace EntropyGeometryBridge

/-- Existence of finite groups and the incidence geometry. All fifteen histograms are derived. -/
def FiniteGeometry (k : ℕ) : Prop := ∃ (q : ℕ) (_ : 2≤q) (W E S T : Type)
    (_ : Fintype W) (_ : Fintype E) (_ : Fintype S) (_ : Fintype T)
    (gw : AddCommGroup W) (ge : AddCommGroup E),
    Nonempty (@Geometry W E S T gw ge (size k-1) q (modulus k))

theorem largeTable (k : ℕ) (hg : FiniteGeometry k) : LargeTable k := by
  classical
  obtain ⟨q,hq,W,E,S,T,fw,fe,fs,ft,gw,ge,⟨g⟩⟩ := hg
  let Ω := Row W E S T
  let X := Alphabet W E
  let domain := Fintype.equivFin Ω
  let alphabet := Fintype.equivFin X
  let f (a : Fin (Fintype.card Ω)) (i : Fin 4) := alphabet (row g (domain.symm a) i)
  let d := size k-1
  let m := modulus k
  have hc : Fintype.card Ω = q^(2*d+1)*m*(d+1)*(q-1) := by
    change Fintype.card (Row W E S T)=_
    rw [← Nat.card_eq_fintype_card]
    simp only [Row,Nat.card_prod,g.points,g.labels,g.colours,g.scalars,d,m]
    ring
  have hm : 0 < m := lt_trans (size_pos k) (size_lt_modulus k)
  have hq0 : 0<q := lt_of_lt_of_le (by decide : 0<2) hq
  have hq1 : 0<q-1 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1<2) hq)
  have hN : 0<Fintype.card Ω := hc ▸ Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hq0) hm) (Nat.succ_pos d)) hq1
  refine ⟨q,Fintype.card X,Fintype.card Ω,hq,hN,f,?_⟩
  intro V
  let i := maskOf V
  have he : decode i=V.1 := decode_code _
  have hr := chart domain.symm (view (row g) i) (regular g i)
  have hh : Regular (fun a => restr V (f a)) (fibre d q m i) := by
    apply same _ hr
    intro a b
    constructor
    · intro h
      funext j
      exact alphabet.injective (congrFun h ⟨j.1,he ▸ j.2⟩)
    · intro h
      funext j
      exact congrArg alphabet (congrFun h ⟨j.1,he.symm ▸ j.2⟩)
  letI : NeZero (Fintype.card Ω) := ⟨hN.ne'⟩
  obtain ⟨hs,hF,hprod,hist⟩ := histogram _ _ hh
  rw [Fintype.card_fin] at hprod
  refine ⟨_,_,?_,hs,hF,hprod,hist⟩
  apply Nat.eq_of_mul_eq_mul_right hF
  exact hprod.symm.trans (hc.trans (total d q m i).symm)

/-- Negation of the official statement under finite geometry and the copy-model interface. -/
theorem disproof (geometry : ∀ k, FiniteGeometry k)
    (copies : EntropyCopyInduction.CopyInputs EntropyCopyInduction.Models) :
    ¬IsSemialgebraic (closure (entropicVectors 4)) :=
  conditional_disproof (fun k => largeTable k (geometry k)) (EntropyCopyInduction.finiteDFZ copies)

end EntropyGeometryBridge
end

section
open Finset Submodule Module EntropyTableGeometry
namespace EntropyVandermonde
variable {E S K : Type} [Field K] [AddCommGroup E] [Fintype E] [Fintype S] [Fintype K]

def v (n : ℕ) (lab : E → K) (e : E) (j : Fin n) := lab e ^ j.val

theorem independent {n : ℕ} (lab : E ↪ K) (F : Finset E) (hf : F.card≤n) :
    LinearIndependent K (fun e : F => v n lab e.val) := by
  classical
  let τ := Fintype.equivFin F
  have le : Fintype.card F≤n := by simpa using hf
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let label (k : Fin (Fintype.card F)) := lab (τ.symm k).val
  have hl : Function.Injective label := lab.injective.comp (Subtype.val_injective.comp τ.symm.injective)
  have hh : (fun i => c (τ.symm i)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f:=label) hl
    intro i
    have h := congrFun hc ⟨i.val,lt_of_lt_of_le i.isLt le⟩
    change (∑ e : F,c e • v n lab e.val) ⟨i.val,_⟩ = 0 at h
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,v] at h
    exact (τ.symm.sum_comp (fun e : F => c e * lab e.val ^ i.val)).trans h
  simpa using congrFun hh (τ j)

noncomputable def block (n : ℕ) (lab : E → K) (F : Finset E) :=
  Submodule.span K (v n lab '' (F : Set E))

theorem rank_block {n : ℕ} (lab : E ↪ K) (F : Finset E) (h : F.card≤n) :
    finrank K (block n lab F)=F.card := by
  have he : v n lab '' (F : Set E)=Set.range (fun e : F => v n lab e.val) := by ext; simp
  change finrank K (span K _) = _
  rw [he,finrank_span_eq_card (independent lab F h),Fintype.card_coe]

variable (col : S → E)
def left [DecidableEq E] (i : E) : Finset E := univ.image fun s => i+col s
def right [DecidableEq E] (j : E) : Finset E := univ.image fun s => j-col s

theorem left_card [DecidableEq E] (hc : Function.Injective col) (i : E) : (left col i).card=Fintype.card S := by
  classical
  rw [left,card_image_of_injective _ (fun _ _ h => hc (add_left_cancel h)),card_univ]

theorem right_card [DecidableEq E] (hc : Function.Injective col) (i : E) : (right col i).card=Fintype.card S := by
  classical
  rw [right,card_image_of_injective _ (fun _ _ h => hc (sub_right_inj.mp h)),card_univ]

theorem common (no_ap : ∀ x y z, col x+col y=col z+col z → x=z)
    (e : E) (s : S) [DecidableEq E] :
    left col (e+ -col s) ∩ right col (e+col s)={e} := by
  classical
  ext a
  simp only [mem_inter,mem_singleton]
  constructor
  · rintro ⟨hl,hr⟩
    obtain ⟨x,_,hx⟩ := mem_image.mp hl
    obtain ⟨y,_,hy⟩ := mem_image.mp hr
    change (e+ -col s)+col x=a at hx
    change (e+col s)-col y=a at hy
    have h : col x+col y=col s+col s := by linear_combination (norm := abel) hx - hy
    obtain rfl := no_ap x y s h
    simpa using hx.symm
  · intro ha
    subst a
    exact ⟨mem_image.mpr ⟨s,mem_univ _,by change (e+ -col s)+col s=e; abel⟩,
      mem_image.mpr ⟨s,mem_univ _,by change (e+col s)-col s=e; abel⟩⟩

theorem card_block (V : Submodule K (Fin n → K)) :
    Nat.card V = (Nat.card K)^(finrank K V) := by
  classical
  let := Fintype.ofFinite V
  simpa only [Nat.card_eq_fintype_card] using Module.card_eq_pow_finrank (K:=K) (V:=V)

theorem geometry (d : ℕ) (hd : 1≤d) (lab : E ↪ K)
    (hc : Function.Injective col) (hcard : Fintype.card S=d+1)
    (no_ap : ∀ x y z, col x+col y=col z+col z → x=z)
    (edge : Function.Injective fun x : E × S => (x.1+(-col x.2),x.1+col x.2)) :
    Nonempty (Geometry (Fin (2*d+1) → K) E S Kˣ d (Nat.card K) (Nat.card E)) := by
  classical
  let n := 2*d+1
  let L (i : E) := block n lab (left col i)
  let R (i : E) := block n lab (right col i)
  have lcard (i : E) := (left_card col hc i).trans hcard
  have rcard (i : E) := (right_card col hc i).trans hcard
  have lr (i : E) : finrank K (L i)=d+1 := (rank_block lab _ (by rw [lcard]; dsimp [n]; omega)).trans (lcard i)
  have rr (i : E) : finrank K (R i)=d+1 := (rank_block lab _ (by rw [rcard]; dsimp [n]; omega)).trans (rcard i)
  let jump (e : E) (t : Kˣ) := (t.val : K) • v n lab e
  refine ⟨⟨col,jump,(fun i => (L i).toAddSubgroup),(fun i => (R i).toAddSubgroup),edge,
    ?_,?_,?_,?_,?_,?_,?_,rfl,?_,Nat.card_units K⟩⟩
  · rintro ⟨a,t⟩ ⟨b,u⟩ he
    have h0 := congrFun he ⟨0,by dsimp [n]; omega⟩
    change (t:K)*lab a^0=(u:K)*lab b^0 at h0
    simp only [pow_zero,mul_one] at h0
    obtain rfl : t=u := Units.ext h0
    have h1 := congrFun he ⟨1,by dsimp [n]; omega⟩
    change (t:K)*lab a^1=(t:K)*lab b^1 at h1
    simp only [pow_one] at h1
    exact Prod.ext (lab.injective (mul_left_cancel₀ t.ne_zero h1)) rfl
  · intro e s t
    apply (L _).smul_mem
    apply subset_span
    exact ⟨e,mem_image.mpr ⟨s,mem_univ _,by change (e+ -col s)+col s=e; abel⟩,rfl⟩
  · intro e s t
    apply (R _).smul_mem
    apply subset_span
    exact ⟨e,mem_image.mpr ⟨s,mem_univ _,by change (e+col s)-col s=e; abel⟩,rfl⟩
  · intro i; exact (card_block (L i)).trans (by rw [lr])
  · intro i; exact (card_block (R i)).trans (by rw [rr])
  · intro e s
    let i := e+ -col s
    let j := e+col s
    let A := left col i
    let B := right col j
    have hu : (A∪B).card=n := by
      have eq := card_union_add_card_inter A B
      have one : (A∩B).card=1 := by change (left col _ ∩ right col _).card=1; rw [common col no_ap]; simp
      rw [one] at eq
      change _ = (left col i).card+(right col j).card at eq
      rw [lcard,rcard] at eq
      dsimp [n]; omega
    have sup : L i ⊔ R j=block n lab (A∪B) := by
      change span K _ ⊔ span K _=span K _
      rw [← span_union]; simp [A,B,Set.image_union]
    have dim := Submodule.finrank_sup_add_finrank_inf_eq (L i) (R j)
    rw [sup,rank_block lab _ hu.le,hu,lr,rr] at dim
    have one : finrank K ↥(L i⊓R j)=1 := by change 2*d+1 + finrank K ↥(L i⊓R j) = (d+1)+(d+1) at dim; omega
    change Nat.card ↥(L i ⊓ R j)=Nat.card K
    rw [card_block,one,pow_one]
  · simp [Nat.card_eq_fintype_card]
  · simpa [Nat.card_eq_fintype_card] using hcard

end EntropyVandermonde
end

section
open Finset EntropyOperations EntropyPushforward EntropyShannon EntropyMaskLaws
open EntropyMaskModels EntropyCopyInduction EntropyConditionalCopy EntropyFinalBridge
open OMA.S_itp_entropy_region
namespace EntropyFiniteDFZ
variable {Ω X : Type} [Fintype Ω] [Fintype X]

abbrev Four (X : Type) := (X × X) × (X × X)
abbrev Five (X : Type) := (X × X) × (X × X) × X
def pack (r : Ω → Fin 4 → X) (x : Ω) : Four X := ((r x 0,r x 1),(r x 2,r x 3))
def five (z : Five X) : Fin 5 → X := ![z.1.1,z.1.2,z.2.1.1,z.2.1.2,z.2.2]
def orig (z : Five X) : Four X := (z.1,z.2.1)
def clone (z : Five X) := (z.1,z.2.2)
def firstC (z : Four X) := (z.1,z.2.1)

theorem extend (p : Ω → ℝ) (r : Ω → Fin 4 → X) (hp : ∀ x,0≤p x) (hs : ∑ x,p x=1) :
    ∃ G, copyLaw G ∧ elemental G ∧ (∀ i < 16, G i=H p r i) ∧
      groupH G 17 18 24 4 ∈ Concrete ∧ groupH G 17 18 20 8 ∈ Concrete := by
  let P := push p (pack r)
  let law (i v : X × X) := P (i,v)
  let Q (z : Five X) := copy law z.1 z.2.1 z.2.2
  have hp' (i x) : 0≤law i x := push_nonneg p hp (pack r) (i,x)
  have pr := preserves_law law hp'
  have hQ x : 0≤Q x := copy_nonneg law hp' _ _ _
  have ho : push Q orig=P := by
    rw [show orig (X:=X)=(fun z => (z.1,z.2.1)) from rfl,proj12]
    exact funext fun ⟨i,x⟩ => (pr i).1 x
  have hc : push Q clone=fun z => marginal law z.1 z.2 := by
    rw [show clone (X:=X)=(fun z => (z.1,z.2.2)) from rfl,proj13]
    exact funext fun ⟨i,v⟩ => (pr i).2 v
  have hc₀ : push P firstC=fun z => marginal law z.1 z.2 := proj12 P
  have heq : push Q clone=push Q (firstC ∘ orig) := by rw [← push_comp,ho,hc,hc₀]
  have dist {Y : Type} [Fintype Y] (f : (X × X) × X → Y) :
      obs Q (f ∘ clone)=obs Q (f ∘ firstC ∘ orig) := by
    rw [← obs_push,← obs_push,heq]
  have norm : ∑ x,Q x=1 := (sum_push Q orig).symm.trans (ho ▸ (sum_push p (pack r)).trans hs)
  let G := H Q five
  have laws : copyLaw G := by
    have eqn {Y : Type} [Fintype Y] (a b : ℕ) (f : (X × X) × X → Y)
        (h₁ : ∀ x y, mask five a x=mask five a y ↔ (f ∘ clone) x=(f ∘ clone) y)
        (h₂ : ∀ x y, mask five b x=mask five b y ↔ (f ∘ firstC ∘ orig) x=(f ∘ firstC ∘ orig) y) :
        G a=G b :=
      (obs_same Q _ _ h₁).trans ((dist f).trans (obs_same Q _ _ h₂).symm)
    have e0 : G 16=G 4 := by
      apply eqn 16 4 Prod.snd <;> intro x y <;>
        simp [eq5,five,Nat.testBit,Function.comp_def,clone,firstC,orig,Prod.ext_iff,and_assoc]
    have e1 : G 17=G 5 := by
      apply eqn 17 5 (fun z => (z.1.1,z.2)) <;> intro x y <;>
        simp [eq5,five,Nat.testBit,Function.comp_def,clone,firstC,orig,Prod.ext_iff,and_assoc]
    have e2 : G 18=G 6 := by
      apply eqn 18 6 (fun z => (z.1.2,z.2)) <;> intro x y <;>
        simp [eq5,five,Nat.testBit,Function.comp_def,clone,firstC,orig,Prod.ext_iff,and_assoc]
    have e3 : G 19=G 7 := by
      apply eqn 19 7 id <;> intro x y <;>
        simp [eq5,five,Nat.testBit,Function.comp_def,clone,firstC,orig,Prod.ext_iff,and_assoc]

    have h19 : G 19=ent (fun z : (X × X) × X => marginal law z.1 z.2) := by
      rw [← hc]
      apply obs_same
      intro x y; simp [eq5,five,Nat.testBit,clone,Prod.ext_iff,and_assoc]
    have h15 : G 15=ent P := by
      rw [← ho]
      apply obs_same
      intro x y; simp [eq5,five,Nat.testBit,orig,Prod.ext_iff,and_assoc]
    have h3 : G 3=ent (fun i => ∑ v,law i v) := by
      have h := obs_same Q (mask five 3) (Prod.fst ∘ orig) (fun x y => by
        simp [eq5,five,Nat.testBit,orig,Prod.ext_iff,and_assoc])
      rw [← obs_push,ho] at h
      simp only [obs,proj_left] at h
      exact h
    have h31 : G 31=ent Q := by
      have e : push Q id=Q := funext fun z => push_injective Q id Function.injective_id z
      rw [← e]
      apply obs_same
      intro x y; simp [eq5,five,Nat.testBit,Prod.ext_iff,and_assoc]
    refine ⟨e0,e1,e2,e3,?_⟩
    change G 19+G 15-G 3-G 31=0
    rw [h19,h15,h3,h31]
    have hh := copy_entropy law hp'
    change ent Q + ent (fun i => ∑ v,law i v) = ent P +
      ent (fun z : (X × X) × X => marginal law z.1 z.2) at hh
    linarith only [hh]
  refine ⟨G,laws,fun a b k _ _ _ _ => mi_nonneg Q hQ five a b k,?_,
    group_real Q five _ _ _ _ hQ norm,group_real Q five _ _ _ _ hQ norm⟩
  intro i hi
  let four (v : Four X) : Fin 4 → X := ![v.1.1,v.1.2,v.2.1,v.2.2]
  have e₅ : G i=obs Q (mask four i ∘ orig) := by
    apply obs_same
    intro x y
    have e : i.testBit 4=false := Nat.testBit_lt_two_pow hi
    simp [eq5,eq4,Function.comp_def,five,four,orig,e]
  rw [e₅,← obs_push,ho,obs_push]
  apply obs_same
  intro a b
  simp [eq4,Function.comp_def,pack,four]

theorem probability_laws : CopyInputs Concrete where
  base h hh := by
    obtain ⟨Ω,X,fo,fx,p,r,hp,hs,hg⟩ := hh
    unfold mi
    simp only [Nat.reduceOr,hg 5 (by decide),hg 6 (by decide),hg 4 (by decide),hg 7 (by decide)]
    exact mi_nonneg p hp r 1 2 4
  extendCopy h hh := by
    obtain ⟨Ω,X,fo,fx,p,r,hp,hs,hg⟩ := hh
    obtain ⟨G,hc,he,h0,h1,h2⟩ := extend p r hp hs
    exact ⟨G,hc,he,fun i hi => (h0 i hi).trans (hg i hi).symm,h1,h2⟩

/-- DFZ Theorem 10 in both orders on the official finite-distribution vectors. -/
theorem verified : FiniteDFZ := EntropyCopyInduction.finiteDFZ (concrete_models ▸ probability_laws)

/-- The sole remaining hypothesis in this reduction is finite geometry. -/
theorem disproof (geometry : ∀ k, EntropyGeometryBridge.FiniteGeometry k) :
    ¬IsSemialgebraic (closure (entropicVectors 4)) :=
  conditional_disproof (fun k => EntropyGeometryBridge.largeTable k (geometry k)) verified

end EntropyFiniteDFZ
end

section
open EntropyLargeRatio EntropyGeometryBridge OMA.S_itp_entropy_region

namespace EntropyNonsemialgebraic

/-- A suitable finite geometry at every ratio threshold, using the Cartesian product
of the digit groups and one checksum group. No cyclic encoding is needed. -/
theorem all_geometry (k : ℕ) : FiniteGeometry k := by
  classical
  let B := alphabet k
  let t := digits k
  let b := B-1
  let G := EntropyProgressionLabels.E b t
  let S := EntropyProgressionLabels.S b t
  have hB : 2≤B := by
    change 2^1≤(2:ℕ)^(4*(4*k+3))
    apply Nat.pow_le_pow_right (by decide); omega
  have ht : 1≤t := by dsimp [t,digits]; omega
  have hbr : b+1=B := by dsimp [b]; omega
  have hsize : 2 ≤ size k :=
    hB.trans ((le_of_eq (pow_one B).symm).trans (Nat.pow_le_pow_right (by omega : 0<B) ht))
  obtain ⟨hs,hg⟩ := EntropyProgressionLabels.sizes b t
  have hgs : Nat.card G=modulus k := by
    change Nat.card (EntropyProgressionLabels.E b t)=_
    rw [hg]
    change (2*b+1)^t*(2*t*b^2+1)=(2*B-1)^t*(2*t*b^2+1)
    rw [show 2*b+1=2*B-1 by omega]
  have hss : Fintype.card S = size k-1+1 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (EntropyProgressionLabels.S b t)=_
    rw [hs,hbr,Nat.sub_add_cancel (size_pos k)]
    rfl
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (modulus k)
  letI : Fact q.Prime := ⟨hprime⟩
  let K := ZMod q
  have nk : Nat.card K=q := by simp [K,Nat.card_eq_fintype_card]
  have bound : Fintype.card G≤Fintype.card K := by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hgs,nk]
    exact hq
  obtain ⟨lab⟩ := Function.Embedding.nonempty_of_card_le bound
  let d := size k-1
  have ok : 1≤d := by dsimp [d]; omega
  have block := EntropyVandermonde.geometry (@EntropyProgressionLabels.col b t) d ok lab
    EntropyProgressionLabels.col_inj hss EntropyProgressionLabels.no_ap EntropyProgressionLabels.edge
  refine ⟨q,hprime.two_le,Fin (2*d+1) → K,G,S,Kˣ,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,inferInstance,?_⟩
  change Nonempty (EntropyTableGeometry.Geometry (Fin (2*d+1) → K) G S Kˣ d (Nat.card K) (Nat.card G)) at block
  rw [nk,hgs] at block
  exact block

/-- Arbitrary ratio on actual finite distributions before taking the closure. -/
theorem finite_ratio (z : ℝ) (hz : 0<z) : ∃ h ∈ entropicVectors 4,
    0 < EntropySlice.P (EntropyStability.inflate h) ∧
    z * EntropySlice.P (EntropyStability.inflate h) < EntropySlice.V (EntropyStability.inflate h) := by
  obtain ⟨w,hw,hp,hv⟩ := EntropyFinalBridge.high_tables_finite
    (fun k => largeTable k (all_geometry k)) z hz
  refine ⟨_,hw,?_⟩
  rw [EntropyStability.inflate_coords,(EntropySlice.profile_forms w).2.1,
    (EntropySlice.profile_forms w).2.2]
  exact ⟨mul_pos (by norm_num) hp,hv⟩

/-- The four-variable almost-entropic cone of the official finite-distribution
definition is not semialgebraic over the reals. -/
theorem not_semialgebraic :
    ¬ IsSemialgebraic (closure (entropicVectors 4)) :=
  EntropyFiniteDFZ.disproof all_geometry

end EntropyNonsemialgebraic
end

theorem OMA.disproof : ¬ (type_of% @OMA.S_itp_entropy_region.main) := by
  exact EntropyNonsemialgebraic.not_semialgebraic
