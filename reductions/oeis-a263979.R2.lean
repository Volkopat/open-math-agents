import OMAStatements.S_oeis_a263979

/-!
Sondow's 2015 conjecture, https://oeis.org/A263979.

The finite range is separated at n = 44721. The remaining hypotheses are
the constant mode and the first three real angular modes of the same
nonnegative split-prime sum. The radial function is the normalized
cross-section series of the exponentially tilted unit ball, written at
the geometrically centered radius of the annulus. The positive part
is redundant for that radial weight, and makes its positivity explicit.

The fourth-angle cosine of a positive pair is the rational expression
used below. A positive weighted angular polynomial forces a pair with
3a² > b² and 3b² > a². In the annulus for Y = 4n², both entries then
exceed n. The new split gives separate analytic targets for the explicit
prime-number estimate and the three nonconstant Hecke modes.
-/

namespace OMA.R_oeis_a263979_R2

open Finset
open scoped BigOperators Classical

private theorem moment_witness {S : Finset (ℕ × ℕ)} {w t : ℕ × ℕ → ℝ}
    (hw : ∀ v, 0 ≤ w v)
    (h0 : (995/1000:ℝ) < ∑ v ∈ S, w v)
    (h1 : |∑ v ∈ S, w v*t v| ≤ (112/1000:ℝ))
    (h2 : |∑ v ∈ S, w v*(2*(t v)^2-1)| ≤ (117/1000:ℝ))
    (h3 : |∑ v ∈ S, w v*(4*(t v)^3-3*t v)| ≤ (134/1000:ℝ)) :
    ∃ v ∈ S, t v < -(1/2:ℝ) := by
  let p (v : ℕ × ℕ) := w v * (-(1/2:ℝ)-t v)*(1-t v)^2
  have heq : (∑ v ∈ S, p v) =
      (1/4:ℝ)*(∑ v ∈ S, w v) - (3/4:ℝ)*(∑ v ∈ S, w v*t v) +
        (3/4:ℝ)*(∑ v ∈ S, w v*(2*(t v)^2-1)) -
        (1/4:ℝ)*(∑ v ∈ S, w v*(4*(t v)^3-3*t v)) := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [p]
    ring
  have hp : 0 < ∑ v ∈ S, p v := by
    rw [heq]
    linarith [(abs_le.mp h1).2,(abs_le.mp h2).1,(abs_le.mp h3).2]
  by_contra! h
  exact hp.not_ge (Finset.sum_nonpos fun v hv => by
    dsimp [p]
    apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    exact mul_nonpos_of_nonneg_of_nonpos (hw v) (by linarith [h v hv]))

private theorem coordinate_bound (a b n : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hl : 4*(n:ℝ)^2 < (a:ℝ)^2+(b:ℝ)^2)
    (ht : ((a:ℝ)^4 - 6*(a:ℝ)^2*(b:ℝ)^2 + (b:ℝ)^4) /
      ((a:ℝ)^2+(b:ℝ)^2)^2 < -(1/2:ℝ)) :
    n < a ∧ n < b := by
  have hap : 0 < (a:ℝ) := by exact_mod_cast ha
  have hbp : 0 < (b:ℝ) := by exact_mod_cast hb
  have hden : 0 < ((a:ℝ)^2+(b:ℝ)^2)^2 := by positivity
  have hx := (div_lt_iff₀ hden).mp ht
  have hp : 0 < (3*(a:ℝ)^2-(b:ℝ)^2)*(3*(b:ℝ)^2-(a:ℝ)^2) := by
    nlinarith only [hx]
  have hsum : 0 < (3*(a:ℝ)^2-(b:ℝ)^2)+(3*(b:ℝ)^2-(a:ℝ)^2) := by
    nlinarith only [sq_pos_of_pos hap,sq_pos_of_pos hbp]
  have hsign : 0 < 3*(a:ℝ)^2-(b:ℝ)^2 ∧ 0 < 3*(b:ℝ)^2-(a:ℝ)^2 := by
    rcases mul_pos_iff.mp hp with h | h
    · exact h
    · linarith [h.1,h.2]
  constructor
  · by_contra! h
    have hs : (a:ℝ)^2 ≤ (n:ℝ)^2 := by exact_mod_cast (Nat.pow_le_pow_left h 2)
    nlinarith only [hl,hs,hsign.1]
  · by_contra! h
    have hs : (b:ℝ)^2 ≤ (n:ℝ)^2 := by exact_mod_cast (Nat.pow_le_pow_left h 2)
    nlinarith only [hl,hs,hsign.2]

/-- The finite supplement to the analytic range beginning at norm 8·10^9. -/
def H1 : Prop :=
  ∀ n : ℕ, n ≤ 44721 → ∃ a b : ℕ, n < a ∧ n < b ∧ Nat.Prime (a^2+b^2) ∧
    a^2+b^2 ≤ 2*(2*n+1)^2

/-- A lower bound on the constant angular mode in each dyadic annulus. -/
def H2 : Prop :=
  ∀ Y : ℝ, 8000000000 ≤ Y →
  let cap := ⌊Real.sqrt (2*Y)⌋₊
  let S := ((Finset.Icc 1 cap) ×ˢ (Finset.Icc 1 cap)).filter
    (fun v : ℕ × ℕ => (v.1^2+v.2^2).Prime ∧
      Y < ((v.1^2+v.2^2:ℕ):ℝ) ∧ ((v.1^2+v.2^2:ℕ):ℝ) < 2*Y)
  let w := fun v : ℕ × ℕ =>
    let p : ℝ := ((v.1^2+v.2^2:ℕ):ℝ)
    let h := Real.log 2 / 2
    let b : ℝ := 13/2
    let ρ := max 0 (1-(Real.log (p/(Real.sqrt 2*Y))/h)^2)
    let D := (b*Real.cosh b-Real.sinh b)/b^3
    max 0 ((Real.log p/p) * (ρ*(∑' k : ℕ,
      ((b^2/4)*ρ)^k / ((k.factorial:ℝ)*((k+1).factorial:ℝ))))/(4*h*D))
  (995/1000:ℝ) < ∑ v ∈ S, w v

/-- Uniform upper bounds on the first three nonconstant modes. -/
def H3 : Prop :=
  ∀ Y : ℝ, 8000000000 ≤ Y →
  let cap := ⌊Real.sqrt (2*Y)⌋₊
  let S := ((Finset.Icc 1 cap) ×ˢ (Finset.Icc 1 cap)).filter
    (fun v : ℕ × ℕ => (v.1^2+v.2^2).Prime ∧
      Y < ((v.1^2+v.2^2:ℕ):ℝ) ∧ ((v.1^2+v.2^2:ℕ):ℝ) < 2*Y)
  let w := fun v : ℕ × ℕ =>
    let p : ℝ := ((v.1^2+v.2^2:ℕ):ℝ)
    let h := Real.log 2 / 2
    let b : ℝ := 13/2
    let ρ := max 0 (1-(Real.log (p/(Real.sqrt 2*Y))/h)^2)
    let D := (b*Real.cosh b-Real.sinh b)/b^3
    max 0 ((Real.log p/p) * (ρ*(∑' k : ℕ,
      ((b^2/4)*ρ)^k / ((k.factorial:ℝ)*((k+1).factorial:ℝ))))/(4*h*D))
  let t := fun v : ℕ × ℕ =>
    ((v.1:ℝ)^4-6*(v.1:ℝ)^2*(v.2:ℝ)^2+(v.2:ℝ)^4) /
      ((v.1:ℝ)^2+(v.2:ℝ)^2)^2
  |∑ v ∈ S, w v*t v| ≤ (112/1000:ℝ) ∧
    |∑ v ∈ S, w v*(2*(t v)^2-1)| ≤ (117/1000:ℝ) ∧
    |∑ v ∈ S, w v*(4*(t v)^3-3*t v)| ≤ (134/1000:ℝ)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a263979.main := by
  classical
  intro hfinite hmass hangular n
  by_cases hn : n ≤ 44721
  · exact hfinite n hn
  let Y : ℝ := 4*(n:ℝ)^2
  have hN : (44722:ℝ)^2 ≤ (n:ℝ)^2 := by
    exact_mod_cast (Nat.pow_le_pow_left (show 44722 ≤ n by omega) 2)
  have hY : (8000000000:ℝ) ≤ Y := by
    dsimp [Y]
    nlinarith only [hN]
  let cap := ⌊Real.sqrt (2*Y)⌋₊
  let S := ((Finset.Icc 1 cap) ×ˢ (Finset.Icc 1 cap)).filter
    (fun v : ℕ × ℕ => (v.1^2+v.2^2).Prime ∧
      Y < ((v.1^2+v.2^2:ℕ):ℝ) ∧ ((v.1^2+v.2^2:ℕ):ℝ) < 2*Y)
  let w := fun v : ℕ × ℕ =>
    let p : ℝ := ((v.1^2+v.2^2:ℕ):ℝ)
    let h := Real.log 2 / 2
    let b : ℝ := 13/2
    let ρ := max 0 (1-(Real.log (p/(Real.sqrt 2*Y))/h)^2)
    let D := (b*Real.cosh b-Real.sinh b)/b^3
    max 0 ((Real.log p/p) * (ρ*(∑' k : ℕ,
      ((b^2/4)*ρ)^k / ((k.factorial:ℝ)*((k+1).factorial:ℝ))))/(4*h*D))
  let t := fun v : ℕ × ℕ =>
    ((v.1:ℝ)^4-6*(v.1:ℝ)^2*(v.2:ℝ)^2+(v.2:ℝ)^4) /
      ((v.1:ℝ)^2+(v.2:ℝ)^2)^2
  have h0 : (995/1000:ℝ) < ∑ v ∈ S, w v := hmass Y hY
  obtain ⟨h1,h2,h3⟩ : |∑ v ∈ S, w v*t v| ≤ (112/1000:ℝ) ∧
      |∑ v ∈ S, w v*(2*(t v)^2-1)| ≤ (117/1000:ℝ) ∧
      |∑ v ∈ S, w v*(4*(t v)^3-3*t v)| ≤ (134/1000:ℝ) := hangular Y hY
  obtain ⟨v,hv,ht⟩ := moment_witness (S:=S) (w:=w) (t:=t)
      (fun _ => le_max_left _ _) h0 h1 h2 h3
  have hprod := Finset.mem_product.mp (Finset.mem_filter.mp hv).1
  obtain ⟨hp,hl,hu⟩ : (v.1^2+v.2^2).Prime ∧
      Y < ((v.1^2+v.2^2:ℕ):ℝ) ∧ ((v.1^2+v.2^2:ℕ):ℝ) < 2*Y :=
    (Finset.mem_filter.mp hv).2
  have hlo : 4*(n:ℝ)^2 < (v.1:ℝ)^2+(v.2:ℝ)^2 := by
    simpa only [Y, Nat.cast_add, Nat.cast_pow] using hl
  have hcoords := coordinate_bound _ _ n (Finset.mem_Icc.mp hprod.1).1
    (Finset.mem_Icc.mp hprod.2).1 hlo ht
  have hu' : v.1^2+v.2^2 < 8*n^2 := by
    exact_mod_cast (show ((v.1^2+v.2^2:ℕ):ℝ) < 8*(n:ℝ)^2 by
      calc
        _ < 2*Y := hu
        _ = _ := by dsimp [Y]; ring)
  exact ⟨v.1,v.2,hcoords.1,hcoords.2,hp,by nlinarith only [hu',Nat.zero_le n]⟩

end OMA.R_oeis_a263979_R2
