import FormalConjectures.OEIS.«229232»
import Mathlib

/-! Circular orderings of the nonzero elements of a finite field with primitive adjacent
products shifted by +1. The large-field graph argument follows Xin-Qi Luo and Yue-Feng She
(arXiv:2610.06289). We check concrete cycles or reflection certificates in every remaining
field order. For a prior computational classification including other shifts, see
https://evidencepress.org/releases/sun-circular-primitive-permutation/. -/


namespace SunCorrelation
open Finset

/-- The off-diagonal character correlation used in the large-field edge estimate. -/
theorem offDiag {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ)
    (hne : χ ≠ 1) {u v : F} (huv : u ≠ v) :
    ∑ x : F, χ (x-u) * star (χ (x-v)) = -1 := by
  classical
  let d := v-u
  have hd : d ≠ 0 := sub_ne_zero.mpr huv.symm
  have hχd : χ d ≠ 0 := χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hd)
  have hχ1 : χ (-1) ≠ 0 := χ.apply_ne_zero_iff.mpr (by simp)
  let e : F ≃ F := (Equiv.mulLeft₀ d hd).trans (Equiv.addLeft u)
  rw [← e.sum_comp (fun x : F => χ (x-u) * star (χ (x-v)))]
  have term (t : F) : χ (e t-u)*star (χ (e t-v)) =
      χ⁻¹ (-1) * (χ t * χ⁻¹ (1-t)) := by
    change χ (u+d*t-u)*star (χ (u+d*t-v)) = _
    have H : u+d*t-v = (-1)*d*(1-t) := by dsimp [d]; ring
    rw [H, add_sub_cancel_left, MulChar.star_apply']
    simp only [map_mul, MulChar.inv_apply_eq_inv']
    field_simp
  simp_rw [term]
  rw [← Finset.mul_sum]
  change χ⁻¹ (-1) * jacobiSum χ χ⁻¹ = -1
  rw [jacobiSum_nontrivial_inv hne,MulChar.inv_apply_eq_inv']
  field_simp

/-- Diagonal entry of the same correlation matrix. -/
theorem diag {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ) (u : F) :
    ∑ x : F, χ (x-u) * star (χ (x-u)) = (Fintype.card F : ℂ)-1 := by
  classical
  have aux (x : F) : χ (x-u) * star (χ (x-u)) = if x=u then 0 else 1 := by
    split_ifs with h
    · simp [h,χ.map_zero]
    · rw [MulChar.star_apply',MulChar.inv_apply_eq_inv',mul_inv_cancel₀]
      exact χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h))
  simp_rw [aux]
  have diff (x : F) : (if x=u then (0:ℂ) else 1) = 1 - (if x=u then 1 else 0) := by
    by_cases h : x=u <;> simp [h]
  simp_rw [diff]
  simp [Finset.sum_sub_distrib]
end SunCorrelation

namespace SunCorrelation
open Finset
theorem moment {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ) (hne : χ ≠ 1)
    (w : F → ℂ) :
    (∑ x : F, (∑ u : F, w u * χ (x-u)) * star (∑ v : F, w v * χ (x-v))) +
      (∑ u : F, w u) * star (∑ v : F, w v) =
    (Fintype.card F : ℂ) * ∑ u : F, w u * star (w u) := by
  classical
  have entry (u v : F) : (∑ x : F, χ (x-u) * star (χ (x-v))) + 1 =
      if u=v then (Fintype.card F : ℂ) else 0 := by
    by_cases h : u=v
    · subst v; rw [diag]; simp
    · rw [offDiag χ hne h]; simp [h]
  have exchange (f : F → F → F → ℂ) :
      (∑ x, ∑ u, ∑ v, f x u v) = ∑ u, ∑ v, ∑ x, f x u v := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro u _; rw [Finset.sum_comm]
  simp only [star_sum,star_mul',Finset.sum_mul,Finset.mul_sum]
  rw [exchange,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ v : F, (w v*star (w u))*((∑ x : F, χ (x-v)*star (χ (x-u)))+1) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [mul_add,Finset.mul_sum,mul_one]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by simp_rw [entry]; simp [mul_ite]; ring
end SunCorrelation

namespace SunCorrelation
open Finset
theorem translate_bound {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ) (hne : χ ≠ 1)
    (w : F → ℂ) (X : Finset F) :
    ‖∑ x ∈ X, ∑ u : F, w u * χ (x-u)‖ ^ 2 ≤
      X.card * ((Fintype.card F : ℝ) * ∑ u : F, ‖w u‖^2) := by
  classical
  let row (x : F) := ∑ u : F, w u * χ (x-u)
  have absSq (z : ℂ) : z * star z = ((‖z‖^2 : ℝ) : ℂ) := by
    simpa only [RCLike.star_def,Complex.ofReal_pow] using Complex.mul_conj' z
  have hm := moment χ hne w
  change (∑ x, row x * star (row x)) + _ = _ at hm
  simp_rw [absSq] at hm
  have realEq : (∑ x : F, ‖row x‖^2) + ‖∑ u : F, w u‖^2 =
      (Fintype.card F : ℝ)*(∑ u : F, ‖w u‖^2) := by exact_mod_cast hm
  have sub : (∑ x ∈ X, ‖row x‖^2) ≤ ∑ x : F, ‖row x‖^2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ X) (fun _ _ _ => sq_nonneg _)
  change ‖∑ x ∈ X, row x‖^2 ≤ _
  calc
    _ ≤ (∑ x ∈ X, ‖row x‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) 2
    _ ≤ (X.card : ℝ)*(∑ x ∈ X, ‖row x‖^2) := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [sq_nonneg ‖∑ u : F, w u‖]) (by positivity)
end SunCorrelation

namespace SunCorrelation
open Finset
theorem product_bound {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ) (hne : χ ≠ 1)
    (X Y : Finset F) (hY : 0 ∉ Y) :
    ‖∑ x ∈ X, ∑ y ∈ Y, χ (x*y+1)‖^2 ≤
      (X.card : ℝ)*((Fintype.card F : ℝ)*Y.card) := by
  classical
  let w (u : F) : ℂ := if -u⁻¹∈Y then χ (-u⁻¹) else 0
  let e : F ≃ F := ⟨fun u => -u⁻¹, fun u => -u⁻¹, by intro u; simp, by intro u; simp⟩
  have row (x : F) : (∑ u : F, w u * χ (x-u)) = ∑ y ∈ Y, χ (x*y+1) := by
    rw [← e.sum_comp (fun u : F => w u * χ (x-u))]
    calc
      _ = ∑ y : F, if y∈Y then χ (x*y+1) else 0 := by
        apply sum_congr rfl; intro y _
        change w (-y⁻¹) * χ (x-(-y⁻¹)) = _
        by_cases hy : y∈Y
        · have hy0 : y ≠ 0 := by rintro rfl; exact hY hy
          simp only [w, inv_neg, inv_inv, neg_neg, if_pos hy,← map_mul]
          congr 1
          rw [sub_neg_eq_add,mul_add,mul_inv_cancel₀ hy0,mul_comm]
        · simp [w,hy]
      _ = _ := by simp
  have mass : (∑ u : F, ‖w u‖^2) = (Y.card : ℝ) := by
    rw [← e.sum_comp (fun u : F => ‖w u‖^2)]
    calc
      _ = ∑ y : F, if y∈Y then (1:ℝ) else 0 := by
        apply sum_congr rfl; intro y _
        change ‖w (-y⁻¹)‖^2 = _
        by_cases hy : y∈Y
        · have hy0 : y ≠ 0 := by rintro rfl; exact hY hy
          have H : ‖χ y‖=1 := Complex.norm_eq_one_of_mem_rootsOfUnity
            (χ.apply_mem_rootsOfUnity (Units.mk0 y hy0))
          simp [w,hy,H]
        · simp [w,hy]
      _ = _ := by simp
  simpa only [row,mass] using translate_bound χ hne w X
end SunCorrelation

namespace SunCorrelation
open Finset
theorem principal {F : Type*} [Field F] [Fintype F] (X Y : Finset F)
    (hX : 0 ∉ X) [DecidableEq F] :
    (∑ x ∈ X, ∑ y ∈ Y, (1 : MulChar F ℂ) (x*y+1)) =
      (X.card:ℂ)*Y.card - (X.filter (fun x => -x⁻¹∈Y)).card := by
  classical
  have single (x : F) (hx : x∈X) (y : F) :
      (1 : MulChar F ℂ) (x*y+1) = 1 - (if y= -x⁻¹ then 1 else 0) := by
    have hx0 : x ≠ 0 := by rintro rfl; exact hX hx
    by_cases he : y= -x⁻¹
    · subst y; simp [hx0, MulChar.map_zero]
    · have hn : x*y+1 ≠ 0 := by intro h; apply he; field_simp; linear_combination h
      simp [he,MulChar.one_apply,isUnit_iff_ne_zero,hn]
  calc
    _ = ∑ x ∈ X, ∑ y ∈ Y, (1-(if y= -x⁻¹ then 1 else 0) : ℂ) :=
      sum_congr rfl (fun x hx => sum_congr rfl (fun y _ => single x hx y))
    _ = _ := by simp [sum_sub_distrib, Finset.sum_boole]
end SunCorrelation

namespace SunEdges
open Finset
variable {F : Type*} [Field F] [Fintype F]

noncomputable def hits (n : ℕ) (X Y : Finset F) : ℕ := by
  classical exact ∑ x ∈ X, (Y.filter (fun y => orderOf (x*y+1)=n)).card

/-- Count ordered pairs using a generator-indicator expansion on nonzero elements.
The principal term counts every pair except those with xy=−1. -/
theorem estimate [DecidableEq F] {ι : Type*} (T : Finset ι) (ψ : ι → MulChar F ℂ)
    (c : ℂ) (weight : ι → ℂ) (n : ℕ) (hn : n ≠ 0)
    (nontriv : ∀ i∈T, ψ i ≠ 1)
    (expansion : ∀ z : F, z ≠ 0 →
      (if orderOf z = n then (1:ℂ) else 0) = c + ∑ i ∈ T, weight i * ψ i z)
    (X Y : Finset F) (hX : 0∉X) (hY : 0∉Y) :
    ‖(hits n X Y : ℂ) -
      c*((X.card:ℂ)*Y.card - (X.filter (fun x => -x⁻¹∈Y)).card)‖ ≤
      (∑ i ∈ T, ‖weight i‖) *
        Real.sqrt ((X.card:ℝ)*((Fintype.card F:ℝ)*Y.card)) := by
  classical
  have allz (z : F) : (if orderOf z = n then (1:ℂ) else 0) =
      c * (1 : MulChar F ℂ) z + ∑ i ∈ T, weight i * ψ i z := by
    by_cases h : z=0
    · subst z; simp [orderOf_zero,hn.symm,MulChar.map_zero]
    · rw [expansion z h,MulChar.one_apply (isUnit_iff_ne_zero.mpr h),mul_one]
  let s (i : ι) := ∑ x ∈ X, ∑ y ∈ Y, ψ i (x*y+1)
  have count : (hits n X Y : ℂ) =
      ∑ x ∈ X, ∑ y ∈ Y, (if orderOf (x*y+1)=n then 1 else 0) := by
    simp [hits, Finset.sum_boole]
  have ident : (hits n X Y : ℂ) =
      c*((X.card:ℂ)*Y.card-(X.filter (fun x => -x⁻¹∈Y)).card) +
      ∑ i ∈ T, weight i*s i := by
    rw [count,← SunCorrelation.principal X Y hX]
    simp_rw [allz,Finset.sum_add_distrib]
    congr 1
    · simp [Finset.mul_sum]
    · calc
        _ = ∑ x ∈ X, ∑ i ∈ T, ∑ y ∈ Y, weight i * ψ i (x*y+1) := by
          apply sum_congr rfl; intro x _; rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]; simp [s, Finset.mul_sum]
  rw [ident,add_sub_cancel_left]
  calc
    _ ≤ ∑ i ∈ T, ‖weight i*s i‖ := norm_sum_le .. 
    _ ≤ ∑ i ∈ T, ‖weight i‖ * Real.sqrt ((X.card:ℝ)*((Fintype.card F:ℝ)*Y.card)) := by
      apply sum_le_sum
      intro i hi
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.le_sqrt_of_sq_le
      exact SunCorrelation.product_bound (ψ i) (nontriv i hi) X Y hY
    _ = _ := (Finset.sum_mul ..).symm
end SunEdges

namespace SunEdges
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem empty_rectangle {ι : Type*} (T : Finset ι) (ψ : ι → MulChar F ℂ)
    (c : ℝ) (hc : 0<c) (weight : ι → ℂ) (n : ℕ) (hn : n≠0)
    (nontriv : ∀ i∈T, ψ i ≠ 1)
    (expansion : ∀ z : F, z ≠ 0 →
      (if orderOf z = n then (1:ℂ) else 0) = (c:ℂ) + ∑ i ∈ T, weight i * ψ i z)
    (X Y : Finset F) (hX : 0∉X) (hY : 0∉Y) (empty : hits n X Y=0) :
    Real.sqrt ((X.card:ℝ)*Y.card) ≤ 1 +
      (∑ i ∈ T, ‖weight i‖)/c * Real.sqrt (Fintype.card F) := by
  classical
  let bad := X.filter (fun x => -x⁻¹∈Y)
  let t := Real.sqrt ((X.card:ℝ)*Y.card)
  let L := ∑ i∈T, ‖weight i‖
  have hx : bad.card ≤ X.card := card_filter_le ..
  have hy : bad.card ≤ Y.card := card_le_card_of_injOn (fun x : F => -x⁻¹)
    (fun _ ha => (mem_filter.mp ha).2) (neg_injective.comp inv_injective).injOn
  have hb : (bad.card:ℝ) ≤ t := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (show bad.card^2 ≤ X.card*Y.card by simpa [sq] using Nat.mul_le_mul hx hy)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t^2 = (X.card:ℝ)*Y.card := Real.sq_sqrt (by positivity)
  have h0 := estimate T ψ c weight n hn nontriv expansion X Y hX hY
  rw [empty,Nat.cast_zero,zero_sub,norm_neg] at h0
  have H : c*((X.card:ℝ)*Y.card-bad.card) ≤ L*(Real.sqrt (Fintype.card F)*t) := by
    calc
      _ ≤ |c*((X.card:ℝ)*Y.card-bad.card)| := le_abs_self _
      _ = ‖(c:ℂ)*((X.card:ℂ)*Y.card-(bad.card:ℂ))‖ := by
        norm_cast
      _ ≤ _ := by
        convert h0 using 1
        rw [show (X.card:ℝ)*((Fintype.card F:ℝ)*Y.card) =
            (Fintype.card F:ℝ)*((X.card:ℝ)*Y.card) by ring,Real.sqrt_mul (by positivity)]
  change t ≤ 1+L/c*Real.sqrt (Fintype.card F)
  by_cases h : t=0
  · rw [h]; have hl : 0 ≤ L := sum_nonneg (fun _ _ => norm_nonneg _)
    positivity
  have ht' : 0<t := lt_of_le_of_ne ht (Ne.symm h)
  rw [← ht2] at H
  have lower := mul_le_mul_of_nonneg_left hb hc.le
  have fin : c*t ≤ c+L*Real.sqrt (Fintype.card F) := by
    apply le_of_mul_le_mul_right (a := t) _ ht'
    nlinarith only [H,lower]
  field_simp [hc.ne']
  linarith
end SunEdges


namespace SunRamanujan
open Finset
abbrev P (n : ℕ) := {p // p ∈ n.primeFactors}
abbrev Digits (n : ℕ) := (p : P n) → Fin p.val
def zeroDigit (n : ℕ) : Digits n := fun p => ⟨0, Nat.pos_of_mem_primeFactors p.property⟩
def frequency {n : ℕ} (a : Digits n) : ℕ := ∑ p, (n/p.val)*(a p).val
def weight (p j : ℕ) : ℚ := (if j = 0 then 1 else 0) - (p : ℚ)⁻¹
def coeff {n : ℕ} (a : Digits n) : ℚ := ∏ p, weight p.val (a p).val
def density (n : ℕ) : ℚ := (n.totient : ℚ)/n

theorem coeff_zero {n : ℕ} (hn : 0 < n) : coeff (zeroDigit n) = density n := by
  have h := Nat.totient_eq_mul_prod_factors n
  have h₀ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [coeff, zeroDigit, weight, if_true, density]
  rw [h, mul_div_cancel_left₀ _ h₀]
  exact Finset.prod_attach n.primeFactors (fun p : ℕ => 1 - (p : ℚ)⁻¹)

theorem sum_abs_weight {p : ℕ} (hp : Nat.Prime p) :
    ∑ j : Fin p, |weight p j.val| = 2*(1-(p : ℚ)⁻¹) := by
  have h₂ : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have h₀ : (0 : ℚ) < p := by linarith
  let z : Fin p := ⟨0,hp.pos⟩
  have hw (j : Fin p) : |weight p j.val| =
      (if j = z then 1-2*(p : ℚ)⁻¹ else 0) + (p : ℚ)⁻¹ := by
    by_cases he : j = z
    · subst j
      have hi : (p : ℚ)⁻¹ ≤ 1 := (inv_le_one₀ h₀).mpr (by linarith)
      simp [z, weight,abs_of_nonneg (sub_nonneg.mpr hi)]
      ring
    · have hj : j.val ≠ 0 := fun h => he (Fin.ext h)
      simp [weight,he,hj,abs_of_nonneg (inv_nonneg.mpr h₀.le)]
  simp_rw [hw]
  simp [Finset.sum_add_distrib, h₀.ne']
  ring

theorem sum_abs_coeff {n : ℕ} (hn : 0 < n) :
    ∑ a : Digits n, |coeff a| = density n * 2^n.primeFactors.card := by
  classical
  simp only [coeff, Finset.abs_prod]
  rw [← Fintype.prod_sum (fun (p : P n) (j : Fin p.val) => |weight p.val j.val|)]
  simp_rw [fun (p : P n) => sum_abs_weight (Nat.prime_of_mem_primeFactors p.property)]
  rw [Finset.prod_mul_distrib, ← coeff_zero hn]
  simp [coeff,weight,zeroDigit,mul_comm]

theorem frequency_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun a : Digits n => (frequency a : ZMod n)) := by
  classical
  intro a b h
  funext p
  let m := ∏ q ∈ (Finset.univ.erase p), q.val
  have hpq : p.val.Coprime m := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.property)
      (Nat.prime_of_mem_primeFactors q.property)).mpr (fun he =>
        (Finset.mem_erase.mp hq).1 (Subtype.ext he.symm))
  have hmul (c : Digits n) :
      ((frequency c : ZMod n) * m) = ((n/p.val*(c p).val*m : ℕ) : ZMod n) := by
    simp only [frequency, Nat.cast_sum, Finset.sum_mul]
    rw [Finset.sum_eq_single p]
    · push_cast
      rfl
    · intro q _ hq
      have hqm : q.val ∣ m := Finset.dvd_prod_of_mem (fun q : P n => q.val)
        (Finset.mem_erase.mpr ⟨hq,Finset.mem_univ q⟩)
      obtain ⟨k,hk⟩ := hqm
      rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      use (c q).val*k
      rw [hk, show n/q.val*(c q).val*(q.val*k) = (n/q.val*q.val)*((c q).val*k) by ring,
        Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors q.property)]
    · simp
  have he := (hmul a).symm.trans ((congrArg (fun x : ZMod n => x*(m : ZMod n)) h).trans (hmul b))
  rw [ZMod.natCast_eq_natCast_iff, Nat.mul_assoc,Nat.mul_assoc] at he
  have hd := Nat.dvd_of_mem_primeFactors p.property
  have hm : n/p.val*p.val = n := Nat.div_mul_cancel hd
  have hc : n/p.val ≠ 0 := by intro hz; rw [hz,zero_mul] at hm; omega
  have ht : (a p).val*m ≡ (b p).val*m [MOD p.val] :=
    Nat.ModEq.mul_left_cancel' hc (hm.symm ▸ he : _ ≡ _ [MOD n/p.val*p.val])
  exact Fin.ext (by simpa [Nat.ModEq, Nat.mod_eq_of_lt (a p).isLt, Nat.mod_eq_of_lt (b p).isLt]
    using Nat.ModEq.cancel_right_of_coprime hpq ht)

theorem local_sum {p : ℕ} (hp : Nat.Prime p) (z : ℂ) (hz : z^p=1) :
    ∑ j : Fin p, (weight p j.val : ℂ) * z^j.val = if z=1 then 0 else 1 := by
  classical
  let j₀ : Fin p := ⟨0,hp.pos⟩
  have hterm (j : Fin p) : (weight p j.val : ℂ) * z^j.val =
      (if j = j₀ then 1 else 0) - (p : ℂ)⁻¹*z^j.val := by
    by_cases he : j = j₀
    · subst j; simp [j₀,weight]
    · have hj : j.val ≠ 0 := fun h => he (Fin.ext h)
      simp [weight,he,hj]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range]
  by_cases he : z=1
  · subst z
    have hp₀ : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    simp [hp₀]
  · have hg := geom_sum_mul z p
    rw [hz,sub_self,mul_eq_zero] at hg
    simp [he, hg.resolve_right (sub_ne_zero.mpr he)]

theorem expansion {G : Type*} [Monoid G] (χ : G →* ℂ) (hχ : Function.Injective χ)
    (x : G) {n : ℕ} (hn : 0<n) (hx : x^n=1) :
    (if orderOf x=n then (1:ℂ) else 0) =
    ∑ a : Digits n, (coeff a : ℂ) * χ x ^ frequency a := by
  classical
  have hfactor (p : P n) : (χ x ^ (n/p.val)) ^ p.val = 1 := by
    rw [← pow_mul,Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors p.property),← map_pow,hx,map_one]
  have hl (p : P n) : (∑ j : Fin p.val, (weight p.val j.val : ℂ) *
      (χ x ^ (n/p.val))^j.val) = (if χ x^(n/p.val)=1 then 0 else 1) :=
    local_sum (Nat.prime_of_mem_primeFactors p.property) _ (hfactor p)
  have he (a : Digits n) : (coeff a : ℂ) * χ x ^ frequency a =
      ∏ p, ((weight p.val (a p).val : ℂ) * (χ x^(n/p.val))^(a p).val) := by
    simp only [coeff,frequency,Rat.cast_prod,Finset.prod_mul_distrib,← pow_mul, Finset.prod_pow_eq_pow_sum]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun (p : P n) (j : Fin p.val) =>
    (weight p.val j.val : ℂ)*(χ x^(n/p.val))^j.val)]
  simp_rw [hl]
  by_cases ho : orderOf x = n
  · rw [if_pos ho]
    symm
    apply Finset.prod_eq_one
    intro p _
    have hp := Nat.prime_of_mem_primeFactors p.property
    have ht : χ x^(n/p.val) ≠ 1 := by
      intro h
      rw [← map_pow] at h
      have hd := orderOf_dvd_of_pow_eq_one (hχ (h.trans χ.map_one.symm))
      rw [ho] at hd
      exact (Nat.div_lt_self hn hp.one_lt).not_ge
        (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactors p.property)) hp.pos) hd)
    simp [ht]
  · rw [if_neg ho]
    symm
    by_contra h
    apply ho
    apply orderOf_eq_of_pow_and_pow_div_prime hn hx
    intro q hq hqd hpow
    let p : P n := ⟨q,Nat.mem_primeFactors.mpr ⟨hq,hqd,hn.ne'⟩⟩
    have hz : χ x^(n/p.val) = 1 := by rw [← map_pow,show p.val=q from rfl,hpow,map_one]
    exact h (Finset.prod_eq_zero (Finset.mem_univ p) (if_pos hz))

def nonzeroDigits (n : ℕ) : Finset (Digits n) := Finset.univ.erase (zeroDigit n)

theorem sum_abs_nonzero {n : ℕ} (hn : 0<n) :
    ∑ a ∈ nonzeroDigits n, |coeff a| = density n * (2^n.primeFactors.card-1) := by
  have h := Finset.sum_erase_add Finset.univ (fun a : Digits n => |coeff a|)
    (Finset.mem_univ (zeroDigit n))
  rw [sum_abs_coeff hn, coeff_zero hn, abs_of_nonneg (show 0 ≤ density n by unfold density; positivity)] at h
  unfold nonzeroDigits
  linarith

theorem finite_field_expansion (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    ∃ χ : MulChar F ℂ,
      (∀ a ∈ nonzeroDigits (Fintype.card Fˣ), χ ^ frequency a ≠ 1) ∧
      ∀ z : F, z ≠ 0 →
      (if orderOf z = Fintype.card Fˣ then (1:ℂ) else 0) =
        (density (Fintype.card Fˣ) : ℂ) +
        ∑ a ∈ nonzeroDigits (Fintype.card Fˣ), (coeff a : ℂ) * (χ ^ frequency a) z := by
  classical
  let n := Fintype.card Fˣ
  have hn : 0<n := Fintype.card_pos
  let _ : NeZero n := ⟨hn.ne'⟩
  let e : Fˣ ≃* rootsOfUnity n ℂ := mulEquivOfCyclicCardEq
    ((Nat.card_eq_fintype_card).trans (Complex.card_rootsOfUnity n).symm)
  let c : Fˣ →* ℂ := (Units.coeHom ℂ).comp ((rootsOfUnity n ℂ).subtype.comp e.toMonoidHom)
  have hc : Function.Injective c := Units.val_injective.comp (Subtype.val_injective.comp e.injective)
  let χ := MulChar.ofUnitHom c.toHomUnits
  have he (x : Fˣ) (k : ℕ) : (χ^k) (x:F) = c x ^ k := by
    simp only [χ,MulChar.pow_apply_coe,MulChar.ofUnitHom_coe, MonoidHom.coe_toHomUnits]
  have hz₀ : frequency (zeroDigit n) = 0 := by simp [frequency,zeroDigit]
  refine ⟨χ,?_,?_⟩
  · intro a ha h
    obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have ho : orderOf g = n := (orderOf_eq_card_of_forall_mem_zpowers hg).trans Nat.card_eq_fintype_card
    have hh : c g ^ frequency a = 1 := by rw [← he, h, MulChar.one_apply_coe]
    have hd := orderOf_dvd_of_pow_eq_one (hc (by rw [map_pow,hh,map_one] : c (g^frequency a)=c 1))
    rw [ho] at hd
    have hzero := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    exact (Finset.mem_erase.mp ha).1 (frequency_injective hn (by change (frequency a : ZMod n) = (frequency (zeroDigit n) : ZMod n); simpa [hz₀] using hzero))
  · intro z hz
    let u := Units.mk0 z hz
    have hs := expansion c hc u hn (show u^n=1 from pow_card_eq_one)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (zeroDigit n)), coeff_zero hn, hz₀, pow_zero, mul_one] at hs
    change (if orderOf (u:F) = n then (1:ℂ) else 0) = (density n : ℂ) + _
    rw [orderOf_units]
    simpa only [nonzeroDigits,he,show z=(u:F) from rfl] using hs

end SunRamanujan

namespace SunBridge
open Finset SunRamanujan

theorem empty_size {F : Type*} [Field F] [Fintype F] [DecidableEq F] (X Y : Finset F)
    (hX : 0∉X) (hY : 0∉Y) (he : SunEdges.hits (Fintype.card Fˣ) X Y=0) :
    Real.sqrt ((X.card:ℝ)*Y.card) ≤ 1+
        ((2:ℝ)^(Fintype.card Fˣ).primeFactors.card-1)*Real.sqrt (Fintype.card F) := by
  let n := Fintype.card Fˣ
  have hn : 0<n := Fintype.card_pos
  obtain ⟨χ,hnon,hexp⟩ := finite_field_expansion F
  have hc : 0 < density n := div_pos (by exact_mod_cast Nat.totient_pos.mpr hn) (by exact_mod_cast hn)
  have hexp' (z:F) (hz:z≠0) : (if orderOf z=n then (1:ℂ) else 0) =
      ((density n : ℝ):ℂ) + ∑ a ∈ nonzeroDigits n, (coeff a:ℂ)*(χ^frequency a) z := by
    simpa only [Complex.ofReal_ratCast] using hexp z hz
  have H := SunEdges.empty_rectangle (nonzeroDigits n) (fun a => χ^frequency a)
      (density n : ℝ) (by exact_mod_cast hc) (fun a => (coeff a:ℂ)) n hn.ne' hnon hexp' X Y hX hY he
  have mass : (∑ a ∈ nonzeroDigits n, ‖(coeff a : ℂ)‖) =
      (density n : ℝ)*((2:ℝ)^n.primeFactors.card-1) := by
    simp only [Complex.norm_ratCast]
    exact_mod_cast sum_abs_nonzero hn
  rw [mass,mul_div_cancel_left₀ _ (show (density n : ℝ) ≠ 0 by exact_mod_cast hc.ne')] at H
  exact H
end SunBridge


namespace SunGraph
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def graph (F : Type*) [Field F] [Fintype F] [DecidableEq F] : SimpleGraph Fˣ where
  Adj x y := x ≠ y ∧ IsPrimitiveRoot ((x : F)*(y : F)+1) (Fintype.card Fˣ)
  symm := ⟨by intro x y h; exact ⟨h.1.symm,by simpa only [mul_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance : DecidableRel (graph F).Adj := Classical.decRel _

theorem degree_lower (x : Fˣ) (hn : 2 < Fintype.card Fˣ) :
    (Fintype.card Fˣ).totient ≤ (graph F).degree x + 1 := by
  classical
  let n := Fintype.card Fˣ
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hg' : IsPrimitiveRoot (g:F) n := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    simpa only [orderOf_units,n,Nat.card_eq_fintype_card] using hg
  let T := primitiveRoots n F
  have hroot (w : T) : IsPrimitiveRoot (w:F) n :=
    (mem_primitiveRoots (by dsimp [n]; omega) : _ ↔ _).mp w.property
  have notneg (w : T) : (w:F)-1 ≠ 0 := by
    intro he
    have eq : (w:F) = 1 := by linear_combination he
    exact (hroot w).pow_ne_one_of_pos_of_lt (by decide : (2:ℕ)≠0) hn (by rw [eq]; ring)
  let f (w : T) : Fˣ := Units.mk0 ((w:F)-1) (notneg w) / x
  have invert (w : T) : (x:F)*(f w:F)+1 = (w:F) := by
    simp only [f,Units.val_div_eq_div_val,Units.val_mk0]
    field_simp <;> ring
  have inject : Function.Injective f := by
    intro a b eq
    exact Subtype.ext <| (invert a).symm.trans ((congrArg (fun y : Fˣ => (x:F)*(y:F)+1) eq).trans (invert b))
  have inc : T.attach.image f ⊆ insert x ((graph F).neighborFinset x) := by
    intro y hy
    obtain ⟨w,_,rfl⟩ := mem_image.mp hy
    by_cases eq : x=f w
    · simp [← eq]
    · apply mem_insert_of_mem
      rw [SimpleGraph.mem_neighborFinset]
      exact ⟨eq,by rw [invert]; exact hroot w⟩
  have H := Finset.card_le_card inc
  rw [card_image_of_injective _ inject,card_attach,card_insert_of_notMem (by simp),
    SimpleGraph.card_neighborFinset_eq_degree] at H
  simpa [T,hg'.card_primitiveRoots,n] using H
end SunGraph


namespace SunExpansion
open Finset SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two large disjoint vertex sets must have a crossing edge. -/
def crosses (M : ℕ) : Prop := ∀ A B : Finset V, Disjoint A B → M < A.card → M < B.card →
    ∃ a∈A, ∃ b∈B, G.Adj a b

theorem independent_bound {M : ℕ} (he : crosses G M) (S : Finset V)
    (hi : G.IsIndepSet (S : Set V)) : S.card ≤ 2*M+1 := by
  classical
  by_contra! hs
  obtain ⟨A,hAS,hA⟩ := Finset.exists_subset_card_eq (s := S) (show M+1 ≤ S.card by omega)
  have hB : (S \ A).card = S.card-A.card := card_sdiff_of_subset hAS
  have hd : Disjoint A (S \ A) := disjoint_sdiff_self_right
  obtain ⟨a,ha,b,hb,hab⟩ := he A _ hd (by omega) (by omega)
  exact hi (hAS ha) (mem_sdiff.mp hb).1 hab.ne hab

theorem connected_after {M k : ℕ} (he : crosses G M)
    (hdegree : ∀ v, M+k ≤ G.degree v+1) (T : Set V) (hT : T.ncard < k) :
    (G.induce Tᶜ).Preconnected := by
  classical
  intro x y
  by_contra bad
  let closed (v : V) := insert v (G.neighborFinset v) \ T.toFinset
  have large (v : V) : M < (closed v).card := by
    have ratio := Finset.card_le_card_sdiff_add_card (s := insert v (G.neighborFinset v)) (t := T.toFinset)
    have hv := hdegree v
    rw [card_insert_of_notMem (by simp), SimpleGraph.card_neighborFinset_eq_degree] at ratio
    have ht' : T.toFinset.card = T.ncard := (Set.ncard_eq_toFinset_card' T).symm
    change M < ((insert v (G.neighborFinset v)) \ T.toFinset).card
    omega
  have outside {v a : V} (ha : a ∈ closed v) : a ∈ Tᶜ := by
    simpa using (mem_sdiff.mp ha).2
  have near (v : ↥(Tᶜ : Set V)) {a : V} (ha : a ∈ closed v.val) :
      (G.induce Tᶜ).Reachable v ⟨a,outside ha⟩ := by
    rcases mem_insert.mp (mem_sdiff.mp ha).1 with rfl | h
    · exact Reachable.refl _
    · exact (show (G.induce Tᶜ).Adj v ⟨a,outside ha⟩ from
        (G.mem_neighborFinset v.val a).mp h).reachable
  have hd : Disjoint (closed x.val) (closed y.val) := by
    rw [Finset.disjoint_left]; intro a ha hb
    exact bad ((near x ha).trans (near y hb).symm)
  obtain ⟨a,ha,b,hb,hab⟩ := he _ _ hd (large _) (large _)
  exact bad ((near x ha).trans ((show (G.induce Tᶜ).Adj ⟨a,outside ha⟩ ⟨b,outside hb⟩ from hab).reachable.trans
    (near y hb).symm))
end SunExpansion

namespace SunFieldGraph
open Finset
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]
noncomputable def budget : ℝ :=
  1+((2:ℝ)^(Fintype.card Fˣ).primeFactors.card-1)*Real.sqrt (Fintype.card F)

theorem crossing : SunExpansion.crosses (SunGraph.graph F) ⌊budget F⌋₊ := by
  classical
  intro A B hdis hA hB
  by_contra! noedge
  let emb : Fˣ ↪ F := ⟨Units.val,Units.val_injective⟩
  let X := A.map emb
  let Y := B.map emb
  have nz (U : Finset Fˣ) : (0:F)∉U.map emb := by
    intro mem
    obtain ⟨u,_,hu⟩ := mem_map.mp mem
    exact u.ne_zero hu
  have he : SunEdges.hits (Fintype.card Fˣ) X Y = 0 := by
    unfold SunEdges.hits
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    intro y hy gen
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    have ne : a≠b := by rintro rfl; exact (Finset.disjoint_left.mp hdis ha hb)
    exact noedge a ha b hb ⟨ne, IsPrimitiveRoot.iff_orderOf.mpr gen⟩
  have H := SunBridge.empty_size X Y (nz A) (nz B) he
  change Real.sqrt ((X.card:ℝ)*Y.card) ≤ budget F at H
  have h0 : 0≤budget F := by
    dsimp [budget]
    have h : 1≤(2:ℝ)^(Fintype.card Fˣ).primeFactors.card := one_le_pow₀ (by norm_num)
    positivity
  have ha := Nat.lt_of_floor_lt hA
  have hb := Nat.lt_of_floor_lt hB
  have bigger : budget F * budget F < (A.card:ℝ)*B.card :=
    (mul_le_mul_of_nonneg_right ha.le h0).trans_lt (mul_lt_mul_of_pos_left hb (h0.trans_lt ha))
  simp only [X,Y,card_map] at H
  have hs := Real.sq_sqrt (show 0≤(A.card:ℝ)*B.card by positivity)
  nlinarith [sq_le_sq' (by linarith [Real.sqrt_nonneg ((A.card:ℝ)*B.card)]) H]

theorem parameters (hn : 2 < Fintype.card Fˣ)
    (hnum : 3*⌊budget F⌋₊+1 ≤ (Fintype.card Fˣ).totient) :
    (∀ S : Finset Fˣ, (SunGraph.graph F).IsIndepSet (S:Set Fˣ) →
       S.card ≤ 2*⌊budget F⌋₊+1) ∧
    (∀ T : Set Fˣ, T.ncard < 2*⌊budget F⌋₊+1 →
       ((SunGraph.graph F).induce Tᶜ).Preconnected) := by
  constructor
  · exact SunExpansion.independent_bound _ (crossing F)
  · apply SunExpansion.connected_after _ (crossing F)
    intro v
    have H := SunGraph.degree_lower v hn
    omega
end SunFieldGraph



namespace SunHamilton
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {a a' b b' : V}

/-- If two attachment successors are adjacent, an external ear reroutes a cycle
through all the original vertices and strictly increases its length. -/
theorem successor_chord_extends
    (aa : G.Adj a a') (bb : G.Adj b b') (p : G.Walk a' b) (q : G.Walk b' a)
    (hc : (Walk.cons aa (p.append (Walk.cons bb q))).IsCycle)
    (ear : G.Walk a b) (he : ear.IsPath) (hl : 1 < ear.length)
    (outside : ∀ x ∈ ear.support, x ∈ p.support ∨ x ∈ q.support → x = a ∨ x = b)
    (chord : G.Adj a' b') :
    ∃ c : G.Walk b b, c.IsCycle ∧
      (Walk.cons aa (p.append (Walk.cons bb q))).length < c.length ∧
      ∀ x ∈ (Walk.cons aa (p.append (Walk.cons bb q))).support, x ∈ c.support := by
  let r := p.reverse.append (Walk.cons chord q)
  have old : (p.support ++ q.support).Nodup := by
    have h := ((Walk.cons_isCycle_iff _ _).mp hc).1.support_nodup
    simpa [Walk.support_append] using h
  obtain ⟨hp,hq,hd⟩ := List.nodup_append'.mp old
  have rs : r.support = p.support.reverse ++ q.support := by simp [r, Walk.support_append]
  have hr : r.IsPath := by
    rw [Walk.isPath_def, rs, List.nodup_append']
    exact ⟨by simpa using hp, hq, fun x hx hy => hd (by simpa using hx) hy⟩
  have source_avoided {v w : V} {t : G.Walk v w} (ht : t.IsPath) : v ∉ t.support.tail := by
    have H := ht.support_nodup
    rw [← t.cons_tail_support, List.nodup_cons] at H
    exact H.1
  refine ⟨r.append ear, hr.isCycle_append he ?_ (Or.inr hl), ?_, ?_⟩
  · intro x hx hy
    have hx' := List.mem_of_mem_tail hx
    have hy' := List.mem_of_mem_tail hy
    rw [rs] at hx'
    have both : x ∈ p.support ∨ x ∈ q.support := by simpa using hx'
    rcases outside x hy' both with rfl | rfl
    · exact source_avoided he hy
    · exact source_avoided hr hx
  · simp [r]; omega
  · intro x hx
    apply Walk.support_subset_support_append_left r ear
    rw [rs, List.mem_append, List.mem_reverse]
    simp [Walk.support_append] at hx
    rcases hx with rfl | h | h
    · exact Or.inr q.end_mem_support
    · exact Or.inl h
    · exact Or.inr h
/-- An external ear replaces one edge when its endpoints are consecutive. -/
theorem edge_ear_extends (aa : G.Adj a a') (p : G.Walk a' a)
    (hc : (Walk.cons aa p).IsCycle) (ear : G.Walk a a') (he : ear.IsPath)
    (hl : 1 < ear.length) (outside : ∀ x ∈ ear.support, x ∈ p.support → x = a ∨ x = a') :
    (p.append ear).IsCycle ∧ (Walk.cons aa p).length < (p.append ear).length ∧
      ∀ x ∈ (Walk.cons aa p).support, x ∈ (p.append ear).support := by
  have hp := ((Walk.cons_isCycle_iff _ _).mp hc).1
  have avoid {v w : V} {t : G.Walk v w} (ht : t.IsPath) : v ∉ t.support.tail := by
    have H := ht.support_nodup
    rw [← t.cons_tail_support, List.nodup_cons] at H
    exact H.1
  refine ⟨hp.isCycle_append he ?_ (Or.inr hl), by simp; omega, ?_⟩
  · intro x hx hy
    rcases outside x (List.mem_of_mem_tail hy) (List.mem_of_mem_tail hx) with rfl | rfl
    · exact avoid he hy
    · exact avoid hp hx
  · intro x hx
    apply Walk.support_subset_support_append_left p ear
    rcases List.mem_cons.mp hx with rfl | hx
    · exact p.end_mem_support
    · exact hx

/-- The successors of two distinct attachments of one exterior component
cannot be adjacent on a longest cycle, given the exterior connecting ear. -/
theorem longest_successors_nonadjacent
    (aa : G.Adj a a') (bb : G.Adj b b') (p : G.Walk a' b) (q : G.Walk b' a)
    (hc : (Walk.cons aa (p.append (Walk.cons bb q))).IsCycle)
    (maximal : ∀ (v : V) (w : G.Walk v v), w.IsCycle →
      w.length ≤ (Walk.cons aa (p.append (Walk.cons bb q))).length)
    (ear : G.Walk a b) (he : ear.IsPath) (hl : 1 < ear.length)
    (outside : ∀ x ∈ ear.support, x ∈ p.support ∨ x ∈ q.support → x = a ∨ x = b) :
    ¬ G.Adj a' b' := by
  intro chord
  obtain ⟨c,hc',hlen,_⟩ := successor_chord_extends aa bb p q hc ear he hl outside chord
  exact (not_lt_of_ge (maximal _ c hc')) hlen

/-- Consecutive vertices of a longest cycle cannot be joined by an external ear. -/
theorem longest_no_consecutive_ear (aa : G.Adj a a') (p : G.Walk a' a)
    (hc : (Walk.cons aa p).IsCycle)
    (maximal : ∀ (v : V) (w : G.Walk v v), w.IsCycle → w.length ≤ (Walk.cons aa p).length)
    (ear : G.Walk a a') (he : ear.IsPath) (hl : 1 < ear.length)
    (outside : ∀ x ∈ ear.support, x ∈ p.support → x = a ∨ x = a') : False := by
  obtain ⟨hcy,hlt,_⟩ := edge_ear_extends aa p hc ear he hl outside
  exact (not_lt_of_ge (maximal _ _ hcy)) hlt

end SunHamilton


namespace SunHamilton
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {S : Set V}

/-- Deleting fewer than k vertices leaves the induced graph preconnected. -/
def survivesDeletion (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ T : Set V, T.ncard < k → (G.induce Tᶜ).Preconnected

/-- Vertices of S with a neighbor in a given component of the complement. -/
def attachments (C : (G.induce Sᶜ).ConnectedComponent) : Set V :=
  {v | v ∈ S ∧ ∃ x : ↥(Sᶜ : Set V), x ∈ C.supp ∧ G.Adj v x}

private theorem closed_walk {W : Type*} {H : SimpleGraph W} {P : W → Prop}
    (step : ∀ x y, H.Adj x y → P x → P y) {x y : W} (p : H.Walk x y) :
    P x → P y := by
  induction p with
  | nil => exact id
  | cons h _ ih => exact fun hx => ih (step _ _ h hx)

/-- Deleting the attachment set separates its exterior component from any
unattached vertex of S. This applies to arbitrary vertex sets S. -/
theorem card_attachments_or_full {k : ℕ} (hk : survivesDeletion G k)
    (C : (G.induce Sᶜ).ConnectedComponent) :
    k ≤ (attachments C).ncard ∨ S ⊆ attachments C := by
  classical
  by_contra! bad
  obtain ⟨v,hv,hn⟩ := Set.not_subset.mp bad.2
  let T := attachments C
  obtain ⟨x,hx⟩ := C.nonempty_supp
  have xT : x.val ∉ T := fun h => x.property h.1
  let P : ↥(Tᶜ : Set V) → Prop := fun y => ∃ h : y.val ∈ Sᶜ, (⟨y.val,h⟩ : ↥(Sᶜ : Set V)) ∈ C.supp
  have step (y z : ↥(Tᶜ : Set V)) (hyz : (G.induce Tᶜ).Adj y z) : P y → P z := by
    change G.Adj y.val z.val at hyz
    rintro ⟨hy,hC⟩
    have hz : z.val ∉ S := by
      intro h
      exact z.property ⟨h, ⟨⟨y.val,hy⟩,hC, hyz.symm⟩⟩
    exact ⟨hz, (C.mem_supp_congr_adj (v := ⟨y.val,hy⟩) (w := ⟨z.val,hz⟩) (show (G.induce Sᶜ).Adj ⟨y.val,hy⟩ ⟨z.val,hz⟩ from hyz)).mp hC⟩
  obtain ⟨p⟩ := hk T bad.1 ⟨x.val,xT⟩ ⟨v,hn⟩
  obtain ⟨h,_⟩ := closed_walk step p (show P ⟨x.val,xT⟩ from ⟨x.property,hx⟩)
  exact h hv

/-- Two distinct attachments are connected by a simple ear whose internal
vertices are outside S, even if they have the same exterior neighbor. -/
theorem ear_of_attachments (C : (G.induce Sᶜ).ConnectedComponent) {a b : V}
    (ha : a ∈ attachments C) (hb : b ∈ attachments C) (hab : a ≠ b) :
    ∃ p : G.Walk a b, p.IsPath ∧ 1 < p.length ∧
      ∀ x ∈ p.support, x ∈ S → x = a ∨ x = b := by
  obtain ⟨aS,x,hx,hax⟩ := ha
  obtain ⟨bS,y,hy,hby⟩ := hb
  have hxy : (G.induce Sᶜ).Reachable x y :=
    ConnectedComponent.exact ((C.mem_supp_iff _).mp hx |>.trans ((C.mem_supp_iff _).mp hy).symm)
  obtain ⟨t,ht⟩ := hxy.exists_isPath
  let f := Embedding.induce (G := G) Sᶜ
  let s : G.Walk x.val y.val := t.map f.toHom
  have hs : s.IsPath := (Walk.isPath_map_iff_of_injective (f := f.toHom) (p := t) f.injective).mpr ht
  have out (v : V) (hv : v ∈ s.support) : v ∉ S := by
    rw [show s.support = t.support.map f from Walk.support_map _ _] at hv
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
    exact u.property
  let p := (Walk.cons hax s).concat hby.symm
  refine ⟨p, ?_, ?_, ?_⟩
  · apply (Walk.concat_isPath_iff _).mpr
    refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hs,fun h => out _ h aS⟩, ?_⟩
    exact fun h => (List.mem_cons.mp h).elim hab.symm (fun h => out _ h bS)
  · dsimp only [p]; rw [Walk.length_concat, Walk.length_cons]; omega
  · intro z hz hzS
    dsimp only [p] at hz
    rw [Walk.support_concat, Walk.support_cons] at hz
    simp only [List.mem_append, List.mem_cons] at hz
    grind

/-- Every exterior component of a longest cycle has at least k attachments.
If every cycle vertex were an attachment, its first edge would admit an exterior ear. -/
theorem longest_cycle_attachment_bound {k : ℕ} (hk : survivesDeletion G k)
    {v : V} (w : G.Walk v v) (hc : w.IsCycle)
    (hm : ∀ (z : V) (u : G.Walk z z), u.IsCycle → u.length ≤ w.length)
    (C : (G.induce {x | x ∈ w.support}ᶜ).ConnectedComponent) :
    k ≤ (attachments C).ncard := by
  rcases card_attachments_or_full hk C with h | h
  · exact h
  cases w with
  | nil => exact (Walk.not_isCycle_nil hc).elim
  | cons aa p =>
    have ha := h (show v ∈ (Walk.cons aa p).support from (Walk.cons aa p).start_mem_support)
    have hb := h (show _ ∈ (Walk.cons aa p).support from List.mem_cons_of_mem _ p.start_mem_support)
    obtain ⟨ear,he,hl,hout⟩ := ear_of_attachments C ha hb aa.ne
    exact False.elim (longest_no_consecutive_ear aa p hc hm ear he hl
      (fun x hx hxp => hout x hx (List.mem_cons_of_mem _ hxp)))

end SunHamilton


namespace SunHamilton
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {v a b : V}

private theorem root_at_first (c : G.Walk a a) (hc : c.IsCycle)
    (ab : G.Adj a b) (hd : (⟨⟨a,b⟩,ab⟩ : G.Dart) ∈ c.darts) :
    ∃ tail : G.Walk b a, c = Walk.cons ab tail := by
  cases c with
  | nil => exact (Walk.not_isCycle_nil hc).elim
  | cons h t =>
    have H := hc.nodup_dropLast_support
    rw [← Walk.map_fst_darts] at H
    have eq := List.inj_on_of_nodup_map H List.mem_cons_self hd rfl
    have he := congrArg (fun D : G.Dart => D.snd) eq
    subst_vars
    exact ⟨_, rfl⟩

/-- Rotating at either of two darts splits a simple cycle into its two intervening arcs. -/
theorem two_dart_arcs [DecidableEq V] (w : G.Walk v v) (hc : w.IsCycle)
    (d e : G.Dart) (hd : d ∈ w.darts) (he : e ∈ w.darts) (hne : d.fst ≠ e.fst) :
    ∃ (p : G.Walk d.snd e.fst) (q : G.Walk e.snd d.fst),
      w.rotate d.fst (w.dart_fst_mem_support_of_mem_darts hd) =
        Walk.cons d.adj (p.append (Walk.cons e.adj q)) := by
  let s := w.rotate d.fst (w.dart_fst_mem_support_of_mem_darts hd)
  have mem (x : G.Dart) : x ∈ s.darts ↔ x ∈ w.darts := (w.rotate_darts _ _).mem_iff
  obtain ⟨t,ht⟩ := root_at_first s (hc.rotate _) d.adj ((mem d).mpr hd)
  have he' := (mem e).mpr he
  rw [ht, Walk.darts_cons, List.mem_cons] at he'
  rcases he' with h | h
  · exact (hne (congrArg (fun D : G.Dart => D.fst) h).symm).elim
  obtain ⟨p,q,hpq⟩ := (Walk.isSubwalk_toWalk_adj_iff_mem_darts t).mpr h
  refine ⟨p,q,?_⟩
  change s = _
  rw [ht,hpq,← Walk.append_assoc]
  rfl

section Longest
variable [DecidableEq V] (w : G.Walk v v) (hc : w.IsCycle)
  (hm : ∀ (z : V) (u : G.Walk z z), u.IsCycle → u.length ≤ w.length)
  (C : (G.induce {x | x ∈ w.support}ᶜ).ConnectedComponent)

include hc hm
theorem successor_not_attachment (d : G.Dart) (hd : d ∈ w.darts)
    (ha : d.fst ∈ attachments C) : d.snd ∉ attachments C := by
  intro hb
  obtain ⟨ear,he,hl,hout⟩ := ear_of_attachments C ha hb d.adj.ne
  let s := w.rotate d.fst ha.1
  obtain ⟨p,hp⟩ := root_at_first s (hc.rotate _) d.adj ((w.rotate_darts _ _).mem_iff.mpr hd)
  apply longest_no_consecutive_ear d.adj p (hp ▸ hc.rotate _) _ ear he hl
  · intro x hx hxp
    apply hout _ hx
    apply (w.mem_support_rotate_iff _ _).mp
    rw [show w.rotate d.fst ha.1 = _ from hp]
    exact List.mem_cons_of_mem _ hxp
  · intro z u hu
    rw [← hp]
    simpa [s] using hm z u hu

theorem successor_pair_nonadjacent (d e : G.Dart) (hd : d ∈ w.darts) (he : e ∈ w.darts)
    (ha : d.fst ∈ attachments C) (hb : e.fst ∈ attachments C) (hne : d.fst ≠ e.fst) :
    ¬ G.Adj d.snd e.snd := by
  obtain ⟨p,q,hs⟩ := two_dart_arcs w hc d e hd he hne
  obtain ⟨ear,he',hl,hout⟩ := ear_of_attachments C ha hb hne
  apply longest_successors_nonadjacent d.adj e.adj p q (hs ▸ hc.rotate _) _ ear he' hl
  · intro x hx hxp
    apply hout _ hx
    apply (w.mem_support_rotate_iff _ _).mp
    rw [hs]
    simp [Walk.support_append]
    tauto
  · intro z u hu
    rw [← hs, Walk.length_rotate]
    exact hm z u hu

include C
/-- A nonspanning longest cycle forces an independent set of at least k+1 vertices. -/
theorem indepNum_gt_of_external [Fintype V] {k : ℕ} (hk : survivesDeletion G k) :
    k < G.indepNum := by
  classical
  have starting (x : V) (hx : x ∈ w.support) : ∃ d ∈ w.darts, d.fst = x := by
    have h : x ∈ w.support.dropLast := by
      by_cases hv : x = v
      · rw [hv, ← w.support_dropLast hc.not_nil]
        exact w.dropLast.start_mem_support
      · rw [← w.map_fst_darts_append, List.mem_append, List.mem_singleton] at hx
        rw [← w.map_fst_darts]
        exact hx.resolve_right hv
    rw [← w.map_fst_darts, List.mem_map] at h
    exact h
  have dart_exists (a : attachments C) := starting a.val a.property.1
  choose d hd hfst using dart_exists
  let f (x : attachments C) := (d x).snd
  have hinj : Function.Injective f := by
    intro x y h
    have H := hc.2
    rw [← w.map_snd_darts] at H
    have eq := List.inj_on_of_nodup_map H (hd x) (hd y) h
    exact Subtype.ext ((hfst x).symm.trans (eq ▸ hfst y))
  let T := Finset.univ.image f
  obtain ⟨x,hx⟩ := C.nonempty_supp
  have inS (z : attachments C) : f z ∈ w.support := w.dart_snd_mem_support_of_mem_darts (hd z)
  have xT : x.val ∉ T := by
    intro h
    obtain ⟨z,_,hz⟩ := Finset.mem_image.mp h
    exact x.property (hz ▸ inS z)
  have nonadj (z : attachments C) : ¬ G.Adj x.val (f z) := by
    intro h
    have hA := z.property
    rw [← hfst z] at hA
    exact successor_not_attachment w hc hm C _ (hd z) hA ⟨inS z,x,hx,h.symm⟩
  have pairwise (i j : attachments C) (h : f i ≠ f j) : ¬ G.Adj (f i) (f j) := by
    apply successor_pair_nonadjacent w hc hm C _ _ (hd i) (hd j)
    · rw [hfst i]; exact i.property
    · rw [hfst j]; exact j.property
    · rw [hfst i, hfst j]
      exact fun e => h (congrArg f (Subtype.ext e))
  have indep : G.IsIndepSet (insert x.val T : Finset V) := by
    intro u hu v hv huv
    rcases Finset.mem_insert.mp hu with rfl | hu <;> rcases Finset.mem_insert.mp hv with rfl | hv
    · exact (huv rfl).elim
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
      exact nonadj j
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
      exact fun h => nonadj i h.symm
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
      exact pairwise i j huv
  have lower := indep.card_le_indepNum
  rw [Finset.card_insert_of_notMem xT, show T.card = Fintype.card (attachments C) from
    (Finset.card_image_of_injective _ hinj).trans Finset.card_univ] at lower
  have count := longest_cycle_attachment_bound hk w hc hm C
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at count
  omega

end Longest
private theorem exists_cycle_of_survives [Fintype V] {k : ℕ}
    (hcard : 2 < Fintype.card V) (h2 : 2 ≤ k) (hk : survivesDeletion G k) :
    ∃ (z : V) (w : G.Walk z z), w.IsCycle := by
  classical
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  by_contra! h
  have pre : G.Preconnected := by
    intro x y
    have hh := hk ∅ (by simp; omega) ⟨x,by simp⟩ ⟨y, by simp⟩
    exact hh.map (Embedding.induce (G := G) _).toHom
  have tree : G.IsTree := ⟨⟨pre⟩, fun _ w => h _ w⟩
  obtain ⟨x,hx⟩ := tree.exists_vert_degree_one_of_nontrivial
  obtain ⟨y,hxy,unique⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
  have third : ∃ z : V, z ≠ x ∧ z ≠ y := by
    obtain ⟨i,j,l,hij,hil,hjl⟩ := Fintype.two_lt_card_iff.mp hcard
    by_contra! no
    have ni := no i
    have nj := no j
    have nl := no l
    by_cases i = x <;> by_cases j = x <;> by_cases l = x <;> grind
  obtain ⟨z,hzx,hzy⟩ := third
  let T : Set V := {y}
  have xT : x ∈ Tᶜ := hxy.ne
  have zT : z ∈ Tᶜ := hzy
  obtain ⟨t,ht⟩ := (hk T (by simp [T]; omega) ⟨x,xT⟩ ⟨z,zT⟩).nonempty_neighborSet_left
    (fun e => hzx (congrArg Subtype.val e).symm)
  exact t.property (show t.val = y from unique _ ht)

theorem chvatal_erdos [Fintype V] [DecidableEq V] {k : ℕ} (hcard : 2 < Fintype.card V)
    (h2 : 2 ≤ k) (hk : survivesDeletion G k) (hi : G.indepNum ≤ k) : G.IsHamiltonian := by
  classical
  obtain ⟨a,c,hc⟩ := exists_cycle_of_survives hcard h2 hk
  let L : Set ℕ := {n | ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = n}
  have finite : L.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    (fun n ⟨_,_,hw,hn⟩ => hn ▸ hw.isTrail.length_le_card_edgeFinset)
  obtain ⟨_,⟨⟨v,w,hw,rfl⟩,maximal⟩⟩ := finite.exists_maximal ⟨c.length,a,c,hc,rfl⟩
  have hm (z : V) (u : G.Walk z z) (hu : u.IsCycle) : u.length ≤ w.length := by
    have hh := maximal (show u.length ∈ L from ⟨z,u,hu,rfl⟩)
    omega
  have all (x : V) : x ∈ w.support := by
    by_contra hx
    let S : Set V := {y | y ∈ w.support}
    let C := (G.induce Sᶜ).connectedComponentMk ⟨x,hx⟩
    exact (not_lt_of_ge hi) (indepNum_gt_of_external w hw hm C hk)
  intro _
  refine ⟨v,w,hw,hw.isPath_tail.isHamiltonian_of_mem ?_⟩
  intro x
  rw [w.support_tail_of_not_nil hw.not_nil]
  rcases (w.mem_support_iff.mp (all x)) with rfl | h
  · exact w.end_mem_tail_support hw.not_nil
  · exact h

end SunHamilton
namespace SunFieldGraph
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]
theorem hamiltonian (hn : 2 < Fintype.card Fˣ)
    (hnum : 3*⌊budget F⌋₊+1 ≤ (Fintype.card Fˣ).totient) :
    (SunGraph.graph F).IsHamiltonian := by
  classical
  obtain ⟨ind,conn⟩ := parameters F hn hnum
  have hW : 1 ≤ (2:ℝ)^(Fintype.card Fˣ).primeFactors.card := one_le_pow₀ (by norm_num)
  have hB : 1 ≤ budget F := by
    unfold budget
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hW) (Real.sqrt_nonneg _))
  have hM : 1 ≤ ⌊budget F⌋₊ := Nat.le_floor (by simpa using hB)
  apply SunHamilton.chvatal_erdos hn (k := 2*⌊budget F⌋₊+1) (by omega) conn
  obtain ⟨S,hS⟩ := (SunGraph.graph F).exists_isNIndepSet_indepNum
  rw [← hS.card_eq]
  exact ind S hS.isIndepSet
end SunFieldGraph

namespace SunHamilton
open SimpleGraph

/-- Index the vertices of a Hamiltonian graph in their order on a cycle. -/
theorem cycle_index {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hn : 1 < Fintype.card V) (hG : G.IsHamiltonian) :
    ∃ a : Fin (Fintype.card V) ≃ V, ∀ i : Fin (Fintype.card V),
      G.Adj (a i) (a ⟨(i.val + 1) % Fintype.card V, Nat.mod_lt _ (by omega)⟩) := by
  obtain ⟨v,w,hw⟩ := hG hn.ne'
  have hl := hw.length_eq
  let f (i : Fin (Fintype.card V)) := w.getVert i.val
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply hw.isCycle.getVert_injOn' _ _ hij
    · change i.val ≤ w.length - 1
      have := i.isLt
      omega
    · change j.val ≤ w.length - 1
      have := j.isLt
      omega
  refine ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,by simp⟩), ?_⟩
  intro i
  change G.Adj (w.getVert i.val) (w.getVert ((i.val + 1) % Fintype.card V))
  have hi := i.isLt
  have ha := w.adj_getVert_succ (i := i.val) (by omega)
  by_cases h : i.val + 1 = Fintype.card V
  · rw [h, Nat.mod_self, w.getVert_zero]
    rwa [h.trans hl.symm, w.getVert_length] at ha
  · rwa [Nat.mod_eq_of_lt (by omega)]

end SunHamilton

namespace SunGraph

theorem conjecture_of_hamiltonian (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F > 7) (hG : (graph F).IsHamiltonian) :
    let m := Fintype.card F - 1
    ∃ a : Fin m ≃ Fˣ, ∀ i : Fin m,
      IsPrimitiveRoot
        ((a i : F) * (a ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : F) + 1) m := by
  let P (n : ℕ) := ∃ a : Fin n ≃ Fˣ, ∀ i : Fin n, IsPrimitiveRoot
    ((a i : F) * (a ⟨(i.val + 1) % n, Nat.mod_lt _ (by have := i.isLt; omega)⟩ : F) + 1) n
  change P (Fintype.card F - 1)
  rw [← Fintype.card_units]
  obtain ⟨a,ha⟩ := SunHamilton.cycle_index (graph F) (by rw [Fintype.card_units]; omega) hG
  exact ⟨a,fun i => (ha i).2⟩

end SunGraph



/-
Kernel-checkable batch replay for prime field orders, offset +1.

For a prime `q = 2d+1`, a certificate is `(q, A, r, ps)` where `ps` lists the primes dividing `q-1`.
The cycle `1, A, r, A/r, r^2, A/r^2, ...` has neighbour products `A` and `A*r` alternately, so it
suffices that `A` is a non-square, `r` generates the squares, and `A+1`, `A*r+1` are primitive
roots. The checker works on `ℕ` literals only. Primality of `q` follows from Lucas' criterion
applied to `A+1`, whose order is `q-1`.
-/

namespace SunBatchPrime

/-- Alternately traverse the subgroup generated by r and its coset A times that subgroup. -/
def vertex {G : Type*} [CommGroup G] (A r : G) {d : ℕ} (i : Fin (2*d)) : G :=
  if i.val % 2 = 0 then r ^ (i.val / 2) else A / r ^ (i.val / 2)

theorem cycle {F : Type*} [Field F] [Fintype Fˣ] {d : ℕ} (hd : 0 < d)
    (hc : Fintype.card Fˣ = 2*d) (A r : Fˣ) (hr : IsPrimitiveRoot r d)
    (hcoset : ∀ k : ℕ, A ≠ r^k)
    (hA : IsPrimitiveRoot ((A : F) + 1) (2*d))
    (hB : IsPrimitiveRoot (((A*r : Fˣ) : F) + 1) (2*d)) :
    ∃ a : Fin (2*d) ≃ Fˣ, ∀ i : Fin (2*d),
      IsPrimitiveRoot ((a i : F) *
        (a ⟨(i.val + 1) % (2*d), Nat.mod_lt _ (by omega)⟩ : F) + 1) (2*d) := by
  have sep (i j : ℕ) : r^i ≠ A/r^j := by
    intro h
    exact hcoset (i+j) (by rw [pow_add]; rw [h]; simp)
  have inj : Function.Injective (vertex A r (d := d)) := by
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    unfold vertex at h
    split at h <;> split at h
    · have := hr.pow_inj (by omega) (by omega) h
      exact Fin.ext (by omega)
    · exact (sep _ _ h).elim
    · exact (sep _ _ h.symm).elim
    · have he : r ^ (i.val / 2) = r ^ (j.val / 2) := by simpa using h
      have := hr.pow_inj (by omega) (by omega) he
      exact Fin.ext (by omega)
  let a := Equiv.ofBijective (vertex A r (d := d))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨inj, by simp [hc]⟩)
  refine ⟨a, ?_⟩
  intro i
  let j : Fin (2*d) := ⟨(i.val+1)%(2*d), Nat.mod_lt _ (by omega)⟩
  change IsPrimitiveRoot (((vertex A r i : Fˣ) : F) * ((vertex A r j : Fˣ) : F) + 1) _
  rw [← Units.val_mul]
  have hi := i.isLt
  by_cases hlast : i.val+1 = 2*d
  · have hj : j.val = 0 := by simp [j, hlast]
    have ho : i.val % 2 ≠ 0 := by omega
    have he : i.val/2+1 = d := by omega
    have hpow : r^(i.val/2)*r=1 := by rw [← pow_succ, he]; exact hr.pow_eq_one
    have hprod : vertex A r i * vertex A r j = A*r := by
      simp [vertex, ho, hj]
      grind [div_eq_mul_inv, mul_eq_one_iff_inv_eq]
    rwa [hprod]
  · have hji : j.val=i.val+1 := Nat.mod_eq_of_lt (by omega)
    by_cases he : i.val%2=0
    · have ho : j.val%2≠0 := by omega
      have hdiv : j.val/2=i.val/2 := by omega
      have hp : vertex A r i * vertex A r j = A := by simp [vertex,he,ho,hdiv]
      rwa [hp]
    · have ho : j.val%2=0 := by omega
      have hdiv : j.val/2=i.val/2+1 := by omega
      have hp : vertex A r i * vertex A r j = A*r := by
        simp [vertex,he,ho,hdiv,pow_succ,← mul_assoc]
      rwa [hp]

/- Nat-level arithmetic -/

/-- Binary exponentiation; arguments are fuel, base, exponent, accumulator. -/
def powAux (q : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | f+1, b, e, acc =>
    if e = 0 then acc
    else powAux q f (b*b % q) (e/2) (if e % 2 = 1 then acc*b % q else acc)

theorem powAux_spec (q : ℕ) :
    ∀ f b e acc, e < 2^f → powAux q f b e acc % q = acc * b^e % q := by
  intro f
  induction f with
  | zero =>
    intro b e acc he
    have : e = 0 := by simpa using he
    subst this
    simp [powAux]
  | succ f ih =>
    intro b e acc he
    unfold powAux
    by_cases h0 : e = 0
    · simp [h0]
    · rw [if_neg h0, ih _ _ _ (by rw [pow_succ] at he; omega)]
      change _ ≡ _ [MOD q]
      have hb : (b*b % q)^(e/2) ≡ b^(2*(e/2)) [MOD q] := by
        rw [pow_mul, pow_two]
        exact (Nat.mod_modEq _ _).pow _
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1]
        have he2 : e = 2*(e/2) + 1 := by omega
        calc acc*b % q * (b*b % q)^(e/2) ≡ acc*b * b^(2*(e/2)) [MOD q] :=
              (Nat.mod_modEq _ _).mul hb
          _ = acc * b^(2*(e/2)+1) := by ring
          _ = acc * b^e := by rw [← he2]
      · rw [if_neg h1]
        have he2 : e = 2*(e/2) := by omega
        calc acc * (b*b % q)^(e/2) ≡ acc * b^(2*(e/2)) [MOD q] := (Nat.ModEq.refl _).mul hb
          _ = acc * b^e := by rw [← he2]

def powMod (a e q : ℕ) : ℕ := powAux q 64 a e 1 % q

theorem powMod_eq {a e q : ℕ} (he : e < 2^64) : powMod a e q = a^e % q := by
  rw [powMod, powAux_spec q 64 a e 1 he, one_mul]

theorem powMod_eq_one_iff {a e q : ℕ} (hq : 1 < q) (he : e < 2^64) :
    powMod a e q = 1 ↔ ((a : ℕ) : ZMod q)^e = 1 := by
  rw [powMod_eq he, ← Nat.cast_pow, ← Nat.cast_one (R := ZMod q), ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt hq]

/-- Trial division from `k` upwards; arguments are fuel and `k`. -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f+1, k => if p < k*k then true else if p % k = 0 then false else noDiv p f (k+1)

theorem noDiv_sound (p : ℕ) :
    ∀ f k, noDiv p f k = true → ∀ m, k ≤ m → m*m ≤ p → ¬ m ∣ p := by
  intro f
  induction f with
  | zero => intro k h; simp [noDiv] at h
  | succ f ih =>
    intro k h m hkm hmp hdvd
    unfold noDiv at h
    by_cases h1 : p < k*k
    · have := Nat.mul_le_mul hkm hkm
      omega
    · rw [if_neg h1] at h
      by_cases h2 : p % k = 0
      · simp [h2] at h
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hkm with rfl | hlt
        · exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact ih _ h m hlt hmp hdvd

def primeB (p : ℕ) : Bool := decide (2 ≤ p) && noDiv p p 2

theorem primeB_sound {p : ℕ} (h : primeB p = true) : p.Prime := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Nat.prime_def_le_sqrt.mpr ⟨h.1, fun m hm hs =>
    noDiv_sound p p 2 h.2 m hm (Nat.le_sqrt.mp hs)⟩

/-- `x` has order `n` modulo `q`, tested on the primes in `ps`. -/
def orderB (q x n : ℕ) (ps : List ℕ) : Bool :=
  decide (powMod x n q = 1) &&
    ps.all (fun p => decide (n % p ≠ 0) || decide (powMod x (n/p) q ≠ 1))

/-- Certificate check for the prime `q`, coset representative `A`, generator of squares `r`,
and the list `ps` of all primes dividing `q-1`. -/
def check (q A r : ℕ) (ps : List ℕ) : Bool :=
  decide (3 < q) && decide (q < 2^64) && decide ((q-1) % 2 = 0) &&
    ps.all primeB && decide (ps.prod ^ 64 % (q-1) = 0) &&
    decide (powMod A ((q-1)/2) q ≠ 1) &&
    orderB q r ((q-1)/2) ps &&
    orderB q (A+1) (q-1) ps &&
    orderB q (A*r+1) (q-1) ps

/-- The conclusion: `q` is prime and the units of `ZMod q` have a cyclic ordering in which
every product of neighbours, plus one, is a primitive root. -/
def Good (q : ℕ) : Prop :=
  q.Prime ∧ ∃ h : 0 < q-1, ∃ a : Fin (q-1) ≃ (ZMod q)ˣ, ∀ i : Fin (q-1),
    IsPrimitiveRoot ((a i : ZMod q) *
      (a ⟨(i.val + 1) % (q-1), Nat.mod_lt _ h⟩ : ZMod q) + 1) (q-1)

theorem mem_of_prime_dvd {ps : List ℕ} {n p : ℕ} (hps : ∀ x ∈ ps, x.Prime)
    (hn : ps.prod ^ 64 % n = 0) (hp : p.Prime) (hpn : p ∣ n) : p ∈ ps := by
  have h1 : p ∣ ps.prod := hp.dvd_of_dvd_pow (hpn.trans (Nat.dvd_of_mod_eq_zero hn))
  obtain ⟨a, ha, hpa⟩ := (Prime.dvd_prod_iff hp.prime).mp h1
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hps a ha)).mp hpa]

theorem orderB_sound {q x n : ℕ} {ps : List ℕ} (hq : 1 < q) (hn' : n < 2^64)
    (hps : ∀ p, p.Prime → p ∣ n → p ∈ ps) (h : orderB q x n ps = true) :
    ((x : ℕ) : ZMod q)^n = 1 ∧ ∀ p, p.Prime → p ∣ n → ((x : ℕ) : ZMod q)^(n/p) ≠ 1 := by
  simp only [orderB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at h
  refine ⟨(powMod_eq_one_iff hq hn').mp h.1, fun p hp hpn hx => ?_⟩
  rcases h.2 p (hps p hp hpn) with h1 | h1
  · exact h1 (Nat.mod_eq_zero_of_dvd hpn)
  · exact h1 ((powMod_eq_one_iff hq (lt_of_le_of_lt (Nat.div_le_self _ _) hn')).mpr hx)

theorem isPrimitiveRoot_of {M : Type*} [CommMonoid M] {x : M} {n : ℕ} (hn : 0 < n)
    (h : x^n = 1 ∧ ∀ p, p.Prime → p ∣ n → x^(n/p) ≠ 1) : IsPrimitiveRoot x n :=
  IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_of_pow_and_pow_div_prime hn h.1 h.2)

theorem check_sound {q A r : ℕ} {ps : List ℕ} (h : check q A r ps = true) : Good q := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hq3, hq64⟩, heven⟩, hprime⟩, hprod⟩, hAd⟩, hr⟩, hA⟩, hB⟩ := h
  have hq1 : 1 < q := by omega
  obtain ⟨d, hd⟩ : ∃ d, q - 1 = 2*d := ⟨(q-1)/2, by omega⟩
  have hdpos : 0 < d := by omega
  have hdiv : (q-1)/2 = d := by omega
  rw [hdiv] at hAd hr
  have hps : ∀ p, p.Prime → p ∣ q-1 → p ∈ ps := fun p hp hpn =>
    mem_of_prime_dvd (fun x hx => primeB_sound (hprime x hx)) hprod hp hpn
  have hpsd : ∀ p, p.Prime → p ∣ d → p ∈ ps := fun p hp hpd =>
    hps p hp (hd ▸ Dvd.dvd.mul_left hpd 2)
  have oA := orderB_sound hq1 (by omega) hps hA
  have oB := orderB_sound hq1 (by omega) hps hB
  have or := orderB_sound hq1 (by omega) hpsd hr
  have hqp : q.Prime := lucas_primality q _ oA.1 oA.2
  refine ⟨hqp, by omega, ?_⟩
  have : Fact q.Prime := ⟨hqp⟩
  have hAd' : ((A : ℕ) : ZMod q)^d ≠ 1 := fun hx =>
    hAd ((powMod_eq_one_iff hq1 (by omega)).mpr hx)
  have hr0 : ((r : ℕ) : ZMod q) ≠ 0 := by
    intro h0
    have := or.1
    rw [h0, zero_pow hdpos.ne'] at this
    exact zero_ne_one this
  have hA0 : ((A : ℕ) : ZMod q) ≠ 0 := by
    intro h0
    have h2 := oA.2 2 Nat.prime_two (by omega)
    simp [h0] at h2
  let A' : (ZMod q)ˣ := Units.mk0 _ hA0
  let r' : (ZMod q)ˣ := Units.mk0 _ hr0
  have key : ∀ n, n = 2*d → ∀ h : 0 < n, ∃ a : Fin n ≃ (ZMod q)ˣ, ∀ i : Fin n,
      IsPrimitiveRoot ((a i : ZMod q) *
        (a ⟨(i.val + 1) % n, Nat.mod_lt _ h⟩ : ZMod q) + 1) n := by
    rintro n rfl _
    refine cycle hdpos ?_ A' r' ?_ ?_ ?_ ?_
    · rw [ZMod.card_units_eq_totient, Nat.totient_prime hqp, hd]
    · exact IsPrimitiveRoot.coe_units_iff.mp (isPrimitiveRoot_of hdpos or)
    · intro k he
      apply hAd'
      have : ((A : ℕ) : ZMod q) = ((r : ℕ) : ZMod q)^k := by
        have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) he
        simpa [A', r'] using this
      rw [this, ← pow_mul, Nat.mul_comm, pow_mul, or.1, one_pow]
    · have := isPrimitiveRoot_of (x := ((A + 1 : ℕ) : ZMod q)) (n := q-1) (by omega) oA
      rw [hd] at this
      convert this using 1
      simp [A']
    · have := isPrimitiveRoot_of (x := ((A*r + 1 : ℕ) : ZMod q)) (n := q-1) (by omega) oB
      rw [hd] at this
      convert this using 1
      simp [A', r']
  exact key (q-1) hd (by omega)

/-- A batch of certificates `(q, A, r, ps)`. -/
def checkAll (l : List (ℕ × ℕ × ℕ × List ℕ)) : Bool :=
  l.all (fun c => check c.1 c.2.1 c.2.2.1 c.2.2.2)

theorem checkAll_sound {l : List (ℕ × ℕ × ℕ × List ℕ)} (h : checkAll l = true) :
    ∀ q ∈ l.map (·.1), Good q := by
  intro q hq
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
  exact check_sound (List.all_eq_true.mp h c hc)

end SunBatchPrime

namespace SunBatchPrime

def certs0 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (11,6,3,[2,5]),
  (17,5,2,[2]),
  (19,2,6,[2,3]),
  (23,10,2,[2,11]),
  (29,2,5,[2,7]),
  (31,11,18,[2,3,5]),
  (37,14,4,[2,3]),
  (41,6,2,[2,5]),
  (43,2,9,[2,3,7]),
  (47,10,3,[2,23]),
  (53,2,9,[2,13]),
  (59,10,3,[2,29]),
  (61,6,5,[2,3,5]),
  (67,11,10,[2,3,11]),
  (71,21,6,[2,5,7]),
  (73,10,19,[2,3]),
  (79,6,31,[2,3,13]),
  (83,5,9,[2,41]),
  (89,6,5,[2,11]),
  (97,13,3,[2,3]),
  (101,2,13,[2,5]),
  (103,5,2,[2,3,17]),
  (107,5,4,[2,53]),
  (109,10,60,[2,3]),
  (113,5,9,[2,7]),
  (127,5,9,[2,3,7]),
  (131,22,3,[2,5,13]),
  (137,5,9,[2,17]),
  (139,2,7,[2,3,23]),
  (149,2,7,[2,37]),
  (151,6,10,[2,3,5]),
  (157,5,36,[2,3,13]),
  (163,2,9,[2,3]),
  (167,34,2,[2,83]),
  (173,2,9,[2,43]),
  (179,6,9,[2,89]),
  (181,17,4,[2,3,5]),
  (191,21,12,[2,5,19]),
  (193,29,65,[2,3]),
  (197,2,10,[2,7]),
  (199,21,7,[2,3,11]),
  (211,2,20,[2,3,5,7]),
  (223,5,9,[2,3,37]),
  (227,5,9,[2,113]),
  (229,6,5,[2,3,19]),
  (233,5,30,[2,29]),
  (239,13,4,[2,7,17]),
  (241,13,12,[2,3,5]),
  (251,10,7,[2,5]),
  (263,14,2,[2,131]),
  (269,2,9,[2,67]),
  (271,42,18,[2,3,5]),
  (277,5,22,[2,3,23]),
  (281,11,18,[2,5,7]),
  (283,2,23,[2,3,47]),
  (293,2,6,[2,73]),
  (307,12,7,[2,3,17]),
  (311,22,5,[2,5,31]),
  (313,14,13,[2,3,13]),
  (317,2,6,[2,79]),
  (331,2,5,[2,3,5,11]),
  (337,19,14,[2,3,7]),
  (349,6,29,[2,3,29]),
  (353,12,19,[2,11]),
  (367,5,2,[2,3,61]),
  (373,5,37,[2,3,31]),
  (379,2,21,[2,3,7]),
  (397,5,42,[2,3,11]),
  (401,12,7,[2,5]),
  (409,21,10,[2,3,17]),
  (419,10,3,[2,11,19]),
  (421,13,4,[2,3,5,7]),
  (431,13,10,[2,5,43]),
  (433,14,6,[2,3]),
  (439,30,10,[2,3,73]),
  (443,5,4,[2,13,17]),
  (449,12,9,[2,7]),
  (457,22,38,[2,3,19]),
  (461,2,17,[2,5,23]),
  (463,10,4,[2,3,7,11]),
  (487,5,2,[2,3]),
  (491,6,11,[2,5,7]),
  (499,10,14,[2,3,83]),
  (521,6,11,[2,5,13]),
  (523,20,16,[2,3,29]),
  (541,13,19,[2,3,5]),
  (547,17,34,[2,3,7,13]),
  (571,2,9,[2,3,5,19]),
  (577,14,22,[2,3]),
  (599,21,2,[2,13,23]),
  (601,21,49,[2,3,5]),
  (607,20,11,[2,3,101]),
  (613,5,25,[2,3,17]),
  (617,12,9,[2,7,11]),
  (619,10,25,[2,3,103]),
  (631,6,10,[2,3,5,7]),
  (643,12,22,[2,3,107]),
  (647,10,6,[2,17,19]),
  (659,6,11,[2,7,47]),
  (661,22,5,[2,3,5,11])]

def orders0 : List ℕ := [11,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,263,269,271,277,281,283,293,307,311,313,317,331,337,349,353,367,373,379,397,401,409,419,421,431,433,439,443,449,457,461,463,487,491,499,521,523,541,547,571,577,599,601,607,613,617,619,631,643,647,659,661]

theorem certs0_ok : checkAll certs0 = true := by decide +kernel

theorem certs0_orders : certs0.map (·.1) = orders0 := by decide +kernel

theorem good0 : ∀ q ∈ orders0, Good q :=
  certs0_orders ▸ checkAll_sound certs0_ok

def certs1 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (673,10,6,[2,3,7]),
  (683,5,10,[2,11,31]),
  (691,2,6,[2,3,5,23]),
  (701,2,5,[2,5,7]),
  (709,13,35,[2,3,59]),
  (727,19,13,[2,3,11]),
  (733,5,14,[2,3,61]),
  (739,2,9,[2,3,41]),
  (743,13,3,[2,7,53]),
  (751,11,16,[2,3,5]),
  (757,5,19,[2,3,7]),
  (761,6,21,[2,5,19]),
  (787,12,15,[2,3,131]),
  (811,2,6,[2,3,5]),
  (821,2,5,[2,5,41]),
  (823,5,15,[2,3,137]),
  (827,5,4,[2,7,59]),
  (829,18,4,[2,3,23]),
  (853,5,19,[2,3,71]),
  (859,2,25,[2,3,11,13]),
  (877,13,25,[2,3,73]),
  (881,14,9,[2,5,11]),
  (883,18,10,[2,3,7]),
  (907,2,22,[2,3,151]),
  (911,28,3,[2,5,7,13]),
  (919,6,5,[2,3,17]),
  (937,10,19,[2,3,13]),
  (941,2,9,[2,5,47]),
  (947,5,4,[2,11,43]),
  (953,5,9,[2,7,17]),
  (967,5,34,[2,3,7,23]),
  (971,10,3,[2,5,97]),
  (991,6,53,[2,3,5,11]),
  (997,6,35,[2,3,83]),
  (1009,33,5,[2,3,7]),
  (1013,2,13,[2,11,23]),
  (1021,21,17,[2,3,5,17]),
  (1031,34,5,[2,5,103]),
  (1033,10,24,[2,3,43]),
  (1039,21,17,[2,3,173]),
  (1051,12,6,[2,3,5,7]),
  (1061,2,45,[2,5,53]),
  (1063,5,4,[2,3,59]),
  (1069,6,15,[2,3,89]),
  (1087,11,4,[2,3,181]),
  (1091,17,7,[2,5,109]),
  (1093,14,40,[2,3,7,13]),
  (1103,10,3,[2,19,29]),
  (1117,5,10,[2,3,31]),
  (1123,2,10,[2,3,11,17]),
  (1129,37,7,[2,3,47]),
  (1151,38,3,[2,5,23]),
  (1163,5,14,[2,7,83]),
  (1171,11,19,[2,3,5,13]),
  (1181,12,23,[2,5,59]),
  (1201,33,5,[2,3,5]),
  (1213,5,11,[2,3,101]),
  (1223,19,7,[2,13,47]),
  (1231,23,2,[2,3,5,41]),
  (1237,5,4,[2,3,103]),
  (1249,28,54,[2,3,13]),
  (1259,10,3,[2,17,37]),
  (1277,2,15,[2,11,29]),
  (1279,12,5,[2,3,71]),
  (1289,11,18,[2,7,23]),
  (1291,2,7,[2,3,5,43]),
  (1301,2,19,[2,5,13]),
  (1303,5,18,[2,3,7,31]),
  (1321,34,5,[2,3,5,11]),
  (1327,5,9,[2,3,13,17]),
  (1361,6,9,[2,5,17]),
  (1381,10,52,[2,3,5,23]),
  (1399,12,7,[2,3,233]),
  (1423,5,15,[2,3,79]),
  (1427,5,11,[2,23,31]),
  (1429,10,13,[2,3,7,17]),
  (1447,20,2,[2,3,241]),
  (1451,6,3,[2,5,29]),
  (1453,31,19,[2,3,11]),
  (1471,6,22,[2,3,5,7]),
  (1481,11,125,[2,5,37]),
  (1483,2,33,[2,3,13,19]),
  (1489,13,44,[2,3,31]),
  (1499,7,12,[2,7,107]),
  (1511,22,5,[2,5,151]),
  (1531,21,16,[2,3,5,17]),
  (1543,5,15,[2,3,257]),
  (1549,13,26,[2,3,43]),
  (1559,37,5,[2,19,41]),
  (1567,5,2,[2,3,29]),
  (1571,10,5,[2,5,157]),
  (1579,2,6,[2,3,263]),
  (1583,14,2,[2,7,113]),
  (1597,32,21,[2,3,7,19]),
  (1607,10,6,[2,11,73]),
  (1609,28,12,[2,3,67]),
  (1613,2,13,[2,13,31]),
  (1621,17,37,[2,3,5]),
  (1627,2,34,[2,3,271]),
  (1657,10,18,[2,3,23])]

def orders1 : List ℕ := [673,683,691,701,709,727,733,739,743,751,757,761,787,811,821,823,827,829,853,859,877,881,883,907,911,919,937,941,947,953,967,971,991,997,1009,1013,1021,1031,1033,1039,1051,1061,1063,1069,1087,1091,1093,1103,1117,1123,1129,1151,1163,1171,1181,1201,1213,1223,1231,1237,1249,1259,1277,1279,1289,1291,1301,1303,1321,1327,1361,1381,1399,1423,1427,1429,1447,1451,1453,1471,1481,1483,1489,1499,1511,1531,1543,1549,1559,1567,1571,1579,1583,1597,1607,1609,1613,1621,1627,1657]

theorem certs1_ok : checkAll certs1 = true := by decide +kernel

theorem certs1_orders : certs1.map (·.1) = orders1 := by decide +kernel

theorem good1 : ∀ q ∈ orders1, Good q :=
  certs1_orders ▸ checkAll_sound certs1_ok

def certs2 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (1663,5,21,[2,3,277]),
  (1667,5,4,[2,7,17]),
  (1669,6,5,[2,3,139]),
  (1693,6,3,[2,3,47]),
  (1699,2,7,[2,3,283]),
  (1709,2,7,[2,7,61]),
  (1721,6,18,[2,5,43]),
  (1723,2,37,[2,3,7,41]),
  (1741,17,65,[2,3,5,29]),
  (1747,2,23,[2,3,97]),
  (1753,13,12,[2,3,73]),
  (1759,6,11,[2,3,293]),
  (1777,19,3,[2,3,37]),
  (1783,10,7,[2,3,11]),
  (1787,6,3,[2,19,47]),
  (1789,13,3,[2,3,149]),
  (1801,38,5,[2,3,5]),
  (1811,40,12,[2,5,181]),
  (1831,6,23,[2,3,5,61]),
  (1847,19,6,[2,13,71]),
  (1861,10,31,[2,3,5,31]),
  (1867,12,6,[2,3,311]),
  (1871,22,16,[2,5,11,17]),
  (1873,29,2,[2,3,13]),
  (1877,11,4,[2,7,67]),
  (1879,11,2,[2,3,313]),
  (1901,2,7,[2,5,19]),
  (1931,13,3,[2,5,193]),
  (1933,14,37,[2,3,7,23]),
  (1951,41,16,[2,3,5,13]),
  (1973,2,19,[2,17,29]),
  (1979,17,4,[2,23,43]),
  (1987,2,6,[2,3,331]),
  (1993,20,24,[2,3,83]),
  (1999,14,9,[2,3,37]),
  (2003,6,10,[2,7,11,13]),
  (2011,2,5,[2,3,5,67]),
  (2017,19,25,[2,3,7]),
  (2029,17,4,[2,3,13]),
  (2053,5,22,[2,3,19]),
  (2069,2,6,[2,11,47]),
  (2081,22,8,[2,5,13]),
  (2083,2,19,[2,3,347]),
  (2087,13,3,[2,7,149]),
  (2089,21,6,[2,3,29]),
  (2111,13,8,[2,5,211]),
  (2113,13,3,[2,3,11]),
  (2129,21,28,[2,7,19]),
  (2131,14,4,[2,3,5,71]),
  (2137,30,2,[2,3,89]),
  (2141,2,5,[2,5,107]),
  (2143,5,17,[2,3,7,17]),
  (2161,37,5,[2,3,5]),
  (2179,12,21,[2,3,11]),
  (2203,13,7,[2,3,367]),
  (2213,2,13,[2,7,79]),
  (2221,10,4,[2,3,5,37]),
  (2239,23,10,[2,3,373]),
  (2251,27,20,[2,3,5]),
  (2269,13,36,[2,3,7]),
  (2281,13,6,[2,3,5,19]),
  (2287,20,7,[2,3,127]),
  (2293,5,25,[2,3,191]),
  (2297,5,13,[2,7,41]),
  (2311,27,9,[2,3,5,7,11]),
  (2339,6,5,[2,7,167]),
  (2341,6,11,[2,3,5,13]),
  (2347,2,21,[2,3,17,23]),
  (2351,51,10,[2,5,47]),
  (2371,2,11,[2,3,5,79]),
  (2377,19,14,[2,3,11]),
  (2381,2,6,[2,5,7,17]),
  (2383,33,23,[2,3,397]),
  (2389,10,4,[2,3,199]),
  (2411,13,3,[2,5,241]),
  (2423,10,2,[2,7,173]),
  (2437,5,10,[2,3,7,29]),
  (2441,11,33,[2,5,61]),
  (2467,2,22,[2,3,137]),
  (2473,29,11,[2,3,103]),
  (2503,5,11,[2,3,139]),
  (2521,22,103,[2,3,5,7]),
  (2531,6,9,[2,5,11,23]),
  (2539,2,42,[2,3,47]),
  (2549,2,7,[2,7,13]),
  (2551,30,2,[2,3,5,17]),
  (2557,5,25,[2,3,71]),
  (2591,28,2,[2,5,7,37]),
  (2617,14,18,[2,3,109]),
  (2621,7,20,[2,5,131]),
  (2647,6,2,[2,3,7]),
  (2659,2,16,[2,3,443]),
  (2671,6,5,[2,3,5,89]),
  (2677,6,13,[2,3,223]),
  (2683,2,16,[2,3,149]),
  (2689,38,6,[2,3,7]),
  (2707,2,9,[2,3,11,41]),
  (2711,28,5,[2,5,271]),
  (2713,10,32,[2,3,113]),
  (2719,12,16,[2,3,151])]

def orders2 : List ℕ := [1663,1667,1669,1693,1699,1709,1721,1723,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1831,1847,1861,1867,1871,1873,1877,1879,1901,1931,1933,1951,1973,1979,1987,1993,1999,2003,2011,2017,2029,2053,2069,2081,2083,2087,2089,2111,2113,2129,2131,2137,2141,2143,2161,2179,2203,2213,2221,2239,2251,2269,2281,2287,2293,2297,2311,2339,2341,2347,2351,2371,2377,2381,2383,2389,2411,2423,2437,2441,2467,2473,2503,2521,2531,2539,2549,2551,2557,2591,2617,2621,2647,2659,2671,2677,2683,2689,2707,2711,2713,2719]

theorem certs2_ok : checkAll certs2 = true := by decide +kernel

theorem certs2_orders : certs2.map (·.1) = orders2 := by decide +kernel

theorem good2 : ∀ q ∈ orders2, Good q :=
  certs2_orders ▸ checkAll_sound certs2_ok

def certs3 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (2731,2,5,[2,3,5,7,13]),
  (2741,2,23,[2,5,137]),
  (2749,17,3,[2,3,229]),
  (2767,5,25,[2,3,461]),
  (2791,23,35,[2,3,5,31]),
  (2797,5,25,[2,3,233]),
  (2801,11,10,[2,5,7]),
  (2803,11,6,[2,3,467]),
  (2833,19,39,[2,3,59]),
  (2851,17,13,[2,3,5,19]),
  (2857,10,24,[2,3,7,17]),
  (2861,2,30,[2,5,11,13]),
  (2887,5,4,[2,3,13,37]),
  (2927,10,18,[2,7,11,19]),
  (2953,14,22,[2,3,41]),
  (2971,10,17,[2,3,5,11]),
  (3001,13,10,[2,3,5]),
  (3011,7,3,[2,5,7,43]),
  (3019,10,4,[2,3,503]),
  (3037,20,26,[2,3,11,23]),
  (3041,6,5,[2,5,19]),
  (3049,33,19,[2,3,127]),
  (3061,13,55,[2,3,5,17]),
  (3067,17,34,[2,3,7,73]),
  (3079,12,39,[2,3,19]),
  (3109,10,15,[2,3,7,37]),
  (3121,33,15,[2,3,5,13]),
  (3163,2,9,[2,3,17,31]),
  (3169,28,2,[2,3,11]),
  (3181,6,49,[2,3,5,53]),
  (3187,12,16,[2,3,59]),
  (3191,43,7,[2,5,11,29]),
  (3217,39,6,[2,3,67]),
  (3221,14,5,[2,5,7,23]),
  (3229,10,17,[2,3,269]),
  (3251,22,3,[2,5,13]),
  (3253,5,4,[2,3,271]),
  (3259,2,36,[2,3,181]),
  (3271,6,5,[2,3,5,109]),
  (3301,18,35,[2,3,5,11]),
  (3307,2,10,[2,3,19,29]),
  (3313,10,3,[2,3,23]),
  (3319,14,25,[2,3,7,79]),
  (3331,2,29,[2,3,5,37]),
  (3343,6,22,[2,3,557]),
  (3361,33,73,[2,3,5,7]),
  (3373,18,22,[2,3,281]),
  (3391,11,18,[2,3,5,113]),
  (3433,28,2,[2,3,11,13]),
  (3463,5,9,[2,3,577]),
  (3469,22,15,[2,3,17]),
  (3499,10,4,[2,3,11,53]),
  (3511,6,5,[2,3,5,13]),
  (3517,5,4,[2,3,293]),
  (3529,51,29,[2,3,7]),
  (3541,6,66,[2,3,5,59]),
  (3547,2,10,[2,3,197]),
  (3559,29,2,[2,3,593]),
  (3571,2,25,[2,3,5,7,17]),
  (3583,5,4,[2,3,199]),
  (3607,6,11,[2,3,601]),
  (3613,14,89,[2,3,7,43]),
  (3631,30,13,[2,3,5,11]),
  (3637,14,13,[2,3,101]),
  (3643,2,10,[2,3,607]),
  (3673,10,19,[2,3,17]),
  (3691,18,5,[2,3,5,41]),
  (3697,29,54,[2,3,7,11]),
  (3709,29,19,[2,3,103]),
  (3727,10,2,[2,3,23]),
  (3733,5,28,[2,3,311]),
  (3739,22,6,[2,3,7,89]),
  (3769,22,6,[2,3,157]),
  (3793,19,26,[2,3,79]),
  (3823,5,13,[2,3,7,13]),
  (3847,5,13,[2,3,641]),
  (3851,7,17,[2,5,7,11]),
  (3853,5,4,[2,3,107]),
  (3877,45,4,[2,3,17,19]),
  (3907,17,4,[2,3,7,31]),
  (3911,78,5,[2,5,17,23]),
  (3919,11,17,[2,3,653]),
  (3931,2,25,[2,3,5,131]),
  (3943,5,18,[2,3,73]),
  (3967,5,4,[2,3,661]),
  (4003,2,16,[2,3,23,29]),
  (4021,10,4,[2,3,5,67]),
  (4027,2,19,[2,3,11,61]),
  (4051,11,30,[2,3,5]),
  (4057,19,14,[2,3,13]),
  (4093,5,4,[2,3,11,31]),
  (4111,27,5,[2,3,5,137]),
  (4129,28,17,[2,3,43]),
  (4159,28,9,[2,3,7,11]),
  (4177,10,37,[2,3,29]),
  (4201,22,54,[2,3,5,7]),
  (4219,2,7,[2,3,19,37]),
  (4231,12,16,[2,3,5,47]),
  (4243,2,16,[2,3,7,101]),
  (4261,6,49,[2,3,5,71])]

def orders3 : List ℕ := [2731,2741,2749,2767,2791,2797,2801,2803,2833,2851,2857,2861,2887,2927,2953,2971,3001,3011,3019,3037,3041,3049,3061,3067,3079,3109,3121,3163,3169,3181,3187,3191,3217,3221,3229,3251,3253,3259,3271,3301,3307,3313,3319,3331,3343,3361,3373,3391,3433,3463,3469,3499,3511,3517,3529,3541,3547,3559,3571,3583,3607,3613,3631,3637,3643,3673,3691,3697,3709,3727,3733,3739,3769,3793,3823,3847,3851,3853,3877,3907,3911,3919,3931,3943,3967,4003,4021,4027,4051,4057,4093,4111,4129,4159,4177,4201,4219,4231,4243,4261]

theorem certs3_ok : checkAll certs3 = true := by decide +kernel

theorem certs3_orders : certs3.map (·.1) = orders3 := by decide +kernel

theorem good3 : ∀ q ∈ orders3, Good q :=
  certs3_orders ▸ checkAll_sound certs3_ok

def certs4 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (4271,13,24,[2,5,7,61]),
  (4327,5,9,[2,3,7,103]),
  (4357,17,4,[2,3,11]),
  (4421,2,7,[2,5,13,17]),
  (4423,5,28,[2,3,11,67]),
  (4441,38,18,[2,3,5,37]),
  (4447,5,2,[2,3,13,19]),
  (4523,5,13,[2,7,17,19]),
  (4561,22,35,[2,3,5,19]),
  (4591,47,20,[2,3,5,17]),
  (4603,2,9,[2,3,13,59]),
  (4621,13,3,[2,3,5,7,11]),
  (4651,2,5,[2,3,5,31]),
  (4663,5,11,[2,3,7,37]),
  (4691,6,3,[2,5,7,67]),
  (4759,29,5,[2,3,13,61]),
  (4789,23,3,[2,3,7,19]),
  (4801,34,5,[2,3,5]),
  (4831,6,16,[2,3,5,7,23]),
  (4861,10,60,[2,3,5]),
  (4903,12,9,[2,3,19,43]),
  (4931,10,3,[2,5,17,29]),
  (4951,6,2,[2,3,5,11]),
  (4957,5,25,[2,3,7,59]),
  (4999,6,17,[2,3,7,17]),
  (5011,13,37,[2,3,5,167]),
  (5101,10,22,[2,3,5,17]),
  (5107,11,4,[2,3,23,37]),
  (5167,5,19,[2,3,7,41]),
  (5171,10,21,[2,5,11,47]),
  (5209,22,5,[2,3,7,31]),
  (5227,21,4,[2,3,13,67]),
  (5237,2,6,[2,7,11,17]),
  (5279,56,5,[2,7,13,29]),
  (5281,28,43,[2,3,5,11]),
  (5407,5,4,[2,3,17,53]),
  (5413,5,19,[2,3,11,41]),
  (5419,2,9,[2,3,7,43]),
  (5431,23,4,[2,3,5,181]),
  (5479,12,7,[2,3,11,83]),
  (5503,6,18,[2,3,7,131]),
  (5521,21,18,[2,3,5,23]),
  (5531,28,5,[2,5,7,79]),
  (5581,17,45,[2,3,5,31]),
  (5591,22,8,[2,5,13,43]),
  (5641,34,30,[2,3,5,47]),
  (5659,11,5,[2,3,23,41]),
  (5701,21,4,[2,3,5,19]),
  (5741,2,7,[2,5,7,41]),
  (5743,10,4,[2,3,11,29]),
  (5791,6,2,[2,3,5,193]),
  (5821,17,5,[2,3,5,97]),
  (5839,11,23,[2,3,7,139]),
  (5851,14,25,[2,3,5,13]),
  (5881,37,46,[2,3,5,7]),
  (5923,2,37,[2,3,7,47]),
  (5981,2,47,[2,5,13,23]),
  (6007,5,9,[2,3,7,11,13]),
  (6043,11,15,[2,3,19,53]),
  (6073,19,2,[2,3,11,23]),
  (6091,12,34,[2,3,5,7,29]),
  (6121,28,10,[2,3,5,17]),
  (6133,5,25,[2,3,7,73]),
  (6151,12,9,[2,3,5,41]),
  (6163,2,9,[2,3,13,79]),
  (6211,17,13,[2,3,5,23]),
  (6217,22,12,[2,3,7,37]),
  (6271,12,53,[2,3,5,11,19]),
  (6301,22,28,[2,3,5,7]),
  (6343,6,9,[2,3,7,151]),
  (6361,28,47,[2,3,5,53]),
  (6397,6,3,[2,3,13,41]),
  (6421,17,7,[2,3,5,107]),
  (6427,2,6,[2,3,7,17]),
  (6451,2,17,[2,3,5,43]),
  (6469,29,41,[2,3,7,11]),
  (6491,6,9,[2,5,11,59]),
  (6553,10,7,[2,3,7,13]),
  (6571,2,7,[2,3,5,73]),
  (6581,21,7,[2,5,7,47]),
  (6637,5,25,[2,3,7,79]),
  (6661,10,20,[2,3,5,37]),
  (6679,6,10,[2,3,7,53]),
  (6691,2,5,[2,3,5,223]),
  (6709,6,5,[2,3,13,43]),
  (6733,6,12,[2,3,11,17]),
  (6763,2,19,[2,3,7,23]),
  (6781,6,5,[2,3,5,113]),
  (6791,21,6,[2,5,7,97]),
  (6841,46,84,[2,3,5,19]),
  (6871,14,9,[2,3,5,229]),
  (6883,18,14,[2,3,31,37]),
  (6917,2,10,[2,7,13,19]),
  (6961,46,10,[2,3,5,29]),
  (6971,18,15,[2,5,17,41]),
  (6991,29,2,[2,3,5,233]),
  (6997,14,33,[2,3,11,53]),
  (7039,6,37,[2,3,17,23]),
  (7069,6,36,[2,3,19,31]),
  (7151,21,9,[2,5,11,13])]

def orders4 : List ℕ := [4271,4327,4357,4421,4423,4441,4447,4523,4561,4591,4603,4621,4651,4663,4691,4759,4789,4801,4831,4861,4903,4931,4951,4957,4999,5011,5101,5107,5167,5171,5209,5227,5237,5279,5281,5407,5413,5419,5431,5479,5503,5521,5531,5581,5591,5641,5659,5701,5741,5743,5791,5821,5839,5851,5881,5923,5981,6007,6043,6073,6091,6121,6133,6151,6163,6211,6217,6271,6301,6343,6361,6397,6421,6427,6451,6469,6491,6553,6571,6581,6637,6661,6679,6691,6709,6733,6763,6781,6791,6841,6871,6883,6917,6961,6971,6991,6997,7039,7069,7151]

theorem certs4_ok : checkAll certs4 = true := by decide +kernel

theorem certs4_orders : certs4.map (·.1) = orders4 := by decide +kernel

theorem good4 : ∀ q ∈ orders4, Good q :=
  certs4_orders ▸ checkAll_sound certs4_ok

def certs5 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (7177,19,6,[2,3,13,23]),
  (7211,6,5,[2,5,7,103]),
  (7243,2,17,[2,3,17,71]),
  (7309,18,67,[2,3,7,29]),
  (7321,13,6,[2,3,5,61]),
  (7333,5,36,[2,3,13,47]),
  (7351,6,5,[2,3,5,7]),
  (7393,29,21,[2,3,7,11]),
  (7411,2,23,[2,3,5,13,19]),
  (7459,2,9,[2,3,11,113]),
  (7477,5,10,[2,3,7,89]),
  (7481,6,23,[2,5,11,17]),
  (7541,2,28,[2,5,13,29]),
  (7549,6,37,[2,3,17,37]),
  (7561,38,12,[2,3,5,7]),
  (7591,11,18,[2,3,5,11,23]),
  (7603,2,29,[2,3,7,181]),
  (7621,21,4,[2,3,5,127]),
  (7639,6,21,[2,3,19,67]),
  (7687,5,2,[2,3,7,61]),
  (7723,2,9,[2,3,11,13]),
  (7741,6,69,[2,3,5,43]),
  (7753,30,6,[2,3,17,19]),
  (7789,6,46,[2,3,11,59]),
  (7867,2,6,[2,3,19,23]),
  (7879,6,10,[2,3,13,101]),
  (7951,11,51,[2,3,5,53]),
  (8009,30,2,[2,7,11,13]),
  (8011,37,17,[2,3,5,89]),
  (8053,6,29,[2,3,11,61]),
  (8059,2,11,[2,3,17,79]),
  (8161,21,6,[2,3,5,17]),
  (8171,6,3,[2,5,19,43]),
  (8179,2,6,[2,3,29,47]),
  (8191,30,21,[2,3,5,7,13]),
  (8221,6,86,[2,3,5,137]),
  (8269,17,29,[2,3,13,53]),
  (8311,23,4,[2,3,5,277]),
  (8317,5,13,[2,3,7,11]),
  (8419,2,6,[2,3,23,61]),
  (8431,11,34,[2,3,5,281]),
  (8443,2,37,[2,3,7,67]),
  (8461,17,76,[2,3,5,47]),
  (8467,2,11,[2,3,17,83]),
  (8521,22,21,[2,3,5,71]),
  (8527,5,18,[2,3,7,29]),
  (8581,6,36,[2,3,5,11,13]),
  (8647,5,2,[2,3,11,131]),
  (8681,29,45,[2,5,7,31]),
  (8731,2,14,[2,3,5,97]),
  (8737,30,13,[2,3,7,13]),
  (8741,2,6,[2,5,19,23]),
  (8761,37,20,[2,3,5,73]),
  (8779,10,33,[2,3,7,11,19]),
  (8807,13,9,[2,7,17,37]),
  (8821,32,73,[2,3,5,7]),
  (8863,5,11,[2,3,7,211]),
  (8867,14,3,[2,11,13,31]),
  (8893,6,25,[2,3,13,19]),
  (8933,12,17,[2,7,11,29]),
  (8941,22,3,[2,3,5,149]),
  (8971,2,41,[2,3,5,13,23]),
  (9007,11,16,[2,3,19,79]),
  (9011,6,11,[2,5,17,53]),
  (9043,2,28,[2,3,11,137]),
  (9049,21,2,[2,3,13,29]),
  (9091,2,5,[2,3,5,101]),
  (9103,5,4,[2,3,37,41]),
  (9109,29,21,[2,3,11,23]),
  (9151,6,22,[2,3,5,61]),
  (9157,5,74,[2,3,7,109]),
  (9181,10,4,[2,3,5,17]),
  (9199,11,16,[2,3,7,73]),
  (9241,51,14,[2,3,5,7,11]),
  (9283,2,9,[2,3,7,13,17]),
  (9311,21,2,[2,5,7,19]),
  (9349,23,3,[2,3,19,41]),
  (9391,12,9,[2,3,5,313]),
  (9421,17,4,[2,3,5,157]),
  (9431,13,24,[2,5,23,41]),
  (9439,21,37,[2,3,11,13]),
  (9461,2,13,[2,5,11,43]),
  (9463,5,15,[2,3,19,83]),
  (9491,10,3,[2,5,13,73]),
  (9511,23,36,[2,3,5,317]),
  (9521,11,18,[2,5,7,17]),
  (9547,2,10,[2,3,37,43]),
  (9619,10,16,[2,3,7,229]),
  (9631,12,9,[2,3,5,107]),
  (9661,38,60,[2,3,5,7,23]),
  (9769,38,48,[2,3,11,37]),
  (9781,17,66,[2,3,5,163]),
  (9787,2,26,[2,3,7,233]),
  (9791,38,3,[2,5,11,89]),
  (9811,2,17,[2,3,5,109]),
  (9829,10,92,[2,3,7,13]),
  (9859,10,4,[2,3,31,53]),
  (9871,6,10,[2,3,5,7,47]),
  (9901,18,44,[2,3,5,11]),
  (9907,2,14,[2,3,13,127])]

def orders5 : List ℕ := [7177,7211,7243,7309,7321,7333,7351,7393,7411,7459,7477,7481,7541,7549,7561,7591,7603,7621,7639,7687,7723,7741,7753,7789,7867,7879,7951,8009,8011,8053,8059,8161,8171,8179,8191,8221,8269,8311,8317,8419,8431,8443,8461,8467,8521,8527,8581,8647,8681,8731,8737,8741,8761,8779,8807,8821,8863,8867,8893,8933,8941,8971,9007,9011,9043,9049,9091,9103,9109,9151,9157,9181,9199,9241,9283,9311,9349,9391,9421,9431,9439,9461,9463,9491,9511,9521,9547,9619,9631,9661,9769,9781,9787,9791,9811,9829,9859,9871,9901,9907]

theorem certs5_ok : checkAll certs5 = true := by decide +kernel

theorem certs5_orders : certs5.map (·.1) = orders5 := by decide +kernel

theorem good5 : ∀ q ∈ orders5, Good q :=
  certs5_orders ▸ checkAll_sound certs5_ok

def certs6 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (9931,14,13,[2,3,5,331]),
  (9941,10,4,[2,5,7,71]),
  (9967,5,2,[2,3,11,151]),
  (10039,6,10,[2,3,7,239]),
  (10099,2,5,[2,3,11,17]),
  (10111,29,13,[2,3,5,337]),
  (10141,6,36,[2,3,5,13]),
  (10151,22,5,[2,5,7,29]),
  (10267,11,4,[2,3,29,59]),
  (10271,34,2,[2,5,13,79]),
  (10303,20,7,[2,3,17,101]),
  (10321,28,19,[2,3,5,43]),
  (10333,14,23,[2,3,7,41]),
  (10429,6,5,[2,3,11,79]),
  (10453,22,25,[2,3,13,67]),
  (10459,10,6,[2,3,7,83]),
  (10501,17,23,[2,3,5,7]),
  (10531,2,5,[2,3,5,13]),
  (10627,12,6,[2,3,7,11,23]),
  (10651,10,21,[2,3,5,71]),
  (10687,5,4,[2,3,13,137]),
  (10711,6,72,[2,3,5,7,17]),
  (10739,6,9,[2,7,13,59]),
  (10771,2,20,[2,3,5,359]),
  (10781,17,13,[2,5,7,11]),
  (10789,53,5,[2,3,29,31]),
  (10831,6,21,[2,3,5,19]),
  (10837,5,36,[2,3,7,43]),
  (10847,10,2,[2,11,17,29]),
  (10861,18,26,[2,3,5,181]),
  (10891,11,45,[2,3,5,11]),
  (10903,5,9,[2,3,23,79]),
  (10949,2,13,[2,7,17,23]),
  (10957,13,44,[2,3,11,83]),
  (11047,6,15,[2,3,7,263]),
  (11059,10,5,[2,3,19,97]),
  (11071,6,9,[2,3,5,41]),
  (11119,11,25,[2,3,17,109]),
  (11131,2,9,[2,3,5,7,53]),
  (11161,38,12,[2,3,5,31]),
  (11173,13,63,[2,3,7,19]),
  (11243,6,19,[2,7,11,73]),
  (11257,34,12,[2,3,7,67]),
  (11287,5,15,[2,3,11,19]),
  (11299,2,20,[2,3,7,269]),
  (11311,22,26,[2,3,5,13,29]),
  (11317,6,38,[2,3,23,41]),
  (11353,19,3,[2,3,11,43]),
  (11383,5,19,[2,3,7,271]),
  (11411,6,15,[2,5,7,163]),
  (11467,27,6,[2,3,7,13]),
  (11471,52,7,[2,5,31,37]),
  (11491,2,19,[2,3,5,383]),
  (11527,5,4,[2,3,17,113]),
  (11551,6,39,[2,3,5,7,11]),
  (11593,44,2,[2,3,7,23]),
  (11621,17,4,[2,5,7,83]),
  (11677,14,7,[2,3,7,139]),
  (11701,23,7,[2,3,5,13]),
  (11719,11,2,[2,3,7,31]),
  (11731,2,7,[2,3,5,17,23]),
  (11743,5,9,[2,3,19,103]),
  (11779,2,5,[2,3,13,151]),
  (11821,29,48,[2,3,5,197]),
  (11831,42,13,[2,5,7,13]),
  (11833,10,18,[2,3,17,29]),
  (11887,13,17,[2,3,7,283]),
  (11941,10,45,[2,3,5,199]),
  (11971,43,30,[2,3,5,7,19]),
  (12007,12,11,[2,3,23,29]),
  (12037,34,13,[2,3,17,59]),
  (12041,21,18,[2,5,7,43]),
  (12071,38,2,[2,5,17,71]),
  (12211,2,34,[2,3,5,11,37]),
  (12241,13,17,[2,3,5,17]),
  (12277,5,4,[2,3,11,31]),
  (12301,18,38,[2,3,5,41]),
  (12343,6,19,[2,3,11,17]),
  (12377,5,15,[2,7,13,17]),
  (12391,28,62,[2,3,5,7,59]),
  (12409,28,15,[2,3,11,47]),
  (12421,6,42,[2,3,5,23]),
  (12433,29,69,[2,3,7,37]),
  (12451,2,11,[2,3,5,83]),
  (12503,14,6,[2,7,19,47]),
  (12511,6,2,[2,3,5,139]),
  (12517,5,36,[2,3,7,149]),
  (12541,17,20,[2,3,5,11,19]),
  (12547,2,9,[2,3,17,41]),
  (12601,22,3,[2,3,5,7]),
  (12611,6,9,[2,5,13,97]),
  (12671,28,2,[2,5,7,181]),
  (12703,5,18,[2,3,29,73]),
  (12721,61,7,[2,3,5,53]),
  (12739,10,4,[2,3,11,193]),
  (12781,10,75,[2,3,5,71]),
  (12841,34,33,[2,3,5,107]),
  (12853,14,11,[2,3,7,17]),
  (12923,5,4,[2,7,13,71]),
  (12973,34,21,[2,3,23,47])]

def orders6 : List ℕ := [9931,9941,9967,10039,10099,10111,10141,10151,10267,10271,10303,10321,10333,10429,10453,10459,10501,10531,10627,10651,10687,10711,10739,10771,10781,10789,10831,10837,10847,10861,10891,10903,10949,10957,11047,11059,11071,11119,11131,11161,11173,11243,11257,11287,11299,11311,11317,11353,11383,11411,11467,11471,11491,11527,11551,11593,11621,11677,11701,11719,11731,11743,11779,11821,11831,11833,11887,11941,11971,12007,12037,12041,12071,12211,12241,12277,12301,12343,12377,12391,12409,12421,12433,12451,12503,12511,12517,12541,12547,12601,12611,12671,12703,12721,12739,12781,12841,12853,12923,12973]

theorem certs6_ok : checkAll certs6 = true := by decide +kernel

theorem certs6_orders : certs6.map (·.1) = orders6 := by decide +kernel

theorem good6 : ∀ q ∈ orders6, Good q :=
  certs6_orders ▸ checkAll_sound certs6_ok

def certs7 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (12979,12,26,[2,3,7,103]),
  (13003,18,17,[2,3,11,197]),
  (13063,56,22,[2,3,7,311]),
  (13099,2,26,[2,3,37,59]),
  (13147,2,51,[2,3,7,313]),
  (13159,11,7,[2,3,17,43]),
  (13171,10,22,[2,3,5,439]),
  (13267,2,6,[2,3,11,67]),
  (13291,10,4,[2,3,5,443]),
  (13331,17,16,[2,5,31,43]),
  (13339,17,13,[2,3,13,19]),
  (13381,37,17,[2,3,5,223]),
  (13399,11,5,[2,3,7,11,29]),
  (13411,2,11,[2,3,5,149]),
  (13417,10,69,[2,3,13,43]),
  (13421,12,17,[2,5,11,61]),
  (13441,66,10,[2,3,5,7]),
  (13469,2,13,[2,7,13,37]),
  (13567,6,2,[2,3,7,17,19]),
  (13591,6,36,[2,3,5,151]),
  (13597,5,36,[2,3,11,103]),
  (13669,6,49,[2,3,17,67]),
  (13681,21,2,[2,3,5,19]),
  (13693,5,13,[2,3,7,163]),
  (13711,11,2,[2,3,5,457]),
  (13729,46,2,[2,3,11,13]),
  (13781,27,11,[2,5,13,53]),
  (13807,5,26,[2,3,13,59]),
  (13831,11,20,[2,3,5,461]),
  (13903,12,11,[2,3,7,331]),
  (13921,13,6,[2,3,5,29]),
  (13931,7,4,[2,5,7,199]),
  (13963,2,9,[2,3,13,179]),
  (14011,17,29,[2,3,5,467]),
  (14029,13,3,[2,3,7,167]),
  (14071,6,5,[2,3,5,7,67]),
  (14197,33,7,[2,3,7,13]),
  (14221,22,4,[2,3,5,79]),
  (14251,2,30,[2,3,5,19]),
  (14281,38,71,[2,3,5,7,17]),
  (14323,11,25,[2,3,7,11,31]),
  (14341,6,59,[2,3,5,239]),
  (14389,22,4,[2,3,11,109]),
  (14411,10,16,[2,5,11,131]),
  (14431,27,9,[2,3,5,13,37]),
  (14449,46,57,[2,3,7,43]),
  (14461,6,5,[2,3,5,241]),
  (14479,11,10,[2,3,19,127]),
  (14533,32,17,[2,3,7,173]),
  (14551,11,16,[2,3,5,97]),
  (14561,11,8,[2,5,7,13]),
  (14621,2,9,[2,5,17,43]),
  (14629,10,13,[2,3,23,53]),
  (14653,14,53,[2,3,11,37]),
  (14731,14,29,[2,3,5,491]),
  (14741,2,43,[2,5,11,67]),
  (14767,5,42,[2,3,23,107]),
  (14771,6,15,[2,5,7,211]),
  (14821,70,11,[2,3,5,13,19]),
  (14827,12,16,[2,3,7,353]),
  (14851,2,14,[2,3,5,11]),
  (14869,10,4,[2,3,7,59]),
  (14947,2,15,[2,3,47,53]),
  (14951,61,3,[2,5,13,23]),
  (14983,5,2,[2,3,11,227]),
  (15031,23,4,[2,3,5,167]),
  (15061,13,3,[2,3,5,251]),
  (15091,12,7,[2,3,5,503]),
  (15121,86,34,[2,3,5,7]),
  (15199,6,5,[2,3,17,149]),
  (15241,43,29,[2,3,5,127]),
  (15271,14,5,[2,3,5,509]),
  (15277,5,49,[2,3,19,67]),
  (15289,22,28,[2,3,7,13]),
  (15313,19,6,[2,3,11,29]),
  (15319,23,11,[2,3,23,37]),
  (15331,18,11,[2,3,5,7,73]),
  (15373,5,25,[2,3,7,61]),
  (15391,29,2,[2,3,5,19]),
  (15401,23,5,[2,5,7,11]),
  (15439,6,5,[2,3,31,83]),
  (15451,2,6,[2,3,5,103]),
  (15511,11,2,[2,3,5,11,47]),
  (15541,13,20,[2,3,5,7,37]),
  (15583,23,18,[2,3,7,53]),
  (15601,34,13,[2,3,5,13]),
  (15619,12,20,[2,3,19,137]),
  (15643,18,15,[2,3,11,79]),
  (15661,10,3,[2,3,5,29]),
  (15667,2,6,[2,3,7,373]),
  (15679,21,51,[2,3,13,67]),
  (15731,6,9,[2,5,11,13]),
  (15733,5,13,[2,3,19,23]),
  (15739,10,20,[2,3,43,61]),
  (15901,10,3,[2,3,5,53]),
  (15907,11,57,[2,3,11,241]),
  (15913,19,74,[2,3,13,17]),
  (15919,6,2,[2,3,7,379]),
  (15991,33,41,[2,3,5,13,41]),
  (16069,23,4,[2,3,13,103])]

def orders7 : List ℕ := [12979,13003,13063,13099,13147,13159,13171,13267,13291,13331,13339,13381,13399,13411,13417,13421,13441,13469,13567,13591,13597,13669,13681,13693,13711,13729,13781,13807,13831,13903,13921,13931,13963,14011,14029,14071,14197,14221,14251,14281,14323,14341,14389,14411,14431,14449,14461,14479,14533,14551,14561,14621,14629,14653,14731,14741,14767,14771,14821,14827,14851,14869,14947,14951,14983,15031,15061,15091,15121,15199,15241,15271,15277,15289,15313,15319,15331,15373,15391,15401,15439,15451,15511,15541,15583,15601,15619,15643,15661,15667,15679,15731,15733,15739,15901,15907,15913,15919,15991,16069]

theorem certs7_ok : checkAll certs7 = true := by decide +kernel

theorem certs7_orders : certs7.map (·.1) = orders7 := by decide +kernel

theorem good7 : ∀ q ∈ orders7, Good q :=
  certs7_orders ▸ checkAll_sound certs7_ok

def certs8 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (16087,5,25,[2,3,7,383]),
  (16111,6,26,[2,3,5,179]),
  (16141,6,37,[2,3,5,269]),
  (16183,5,17,[2,3,29,31]),
  (16189,6,12,[2,3,19,71]),
  (16231,12,11,[2,3,5,541]),
  (16339,2,5,[2,3,7,389]),
  (16369,13,24,[2,3,11,31]),
  (16381,10,65,[2,3,5,7,13]),
  (16411,2,6,[2,3,5,547]),
  (16451,6,42,[2,5,7,47]),
  (16561,28,3,[2,3,5,23]),
  (16567,11,28,[2,3,11,251]),
  (16633,19,46,[2,3,7,11]),
  (16651,2,9,[2,3,5,37]),
  (16661,10,37,[2,5,7,17]),
  (16693,5,19,[2,3,13,107]),
  (16699,2,5,[2,3,11,23]),
  (16729,42,3,[2,3,17,41]),
  (16741,10,53,[2,3,5,31]),
  (16759,12,20,[2,3,7,19]),
  (16831,11,35,[2,3,5,11,17]),
  (16843,2,9,[2,3,7,401]),
  (16871,34,9,[2,5,7,241]),
  (16879,6,9,[2,3,29,97]),
  (16921,61,5,[2,3,5,47]),
  (16927,5,57,[2,3,7,13,31]),
  (16963,2,21,[2,3,11,257]),
  (16981,10,60,[2,3,5,283]),
  (16987,2,9,[2,3,19,149]),
  (17011,2,14,[2,3,5,7]),
  (17029,21,11,[2,3,11,43]),
  (17041,13,12,[2,3,5,71]),
  (17053,5,13,[2,3,7,29]),
  (17137,10,79,[2,3,7,17]),
  (17191,12,23,[2,3,5,191]),
  (17203,2,16,[2,3,47,61]),
  (17239,46,5,[2,3,13,17]),
  (17291,6,12,[2,5,7,13,19]),
  (17293,6,14,[2,3,11,131]),
  (17317,17,4,[2,3,13,37]),
  (17341,18,41,[2,3,5,17]),
  (17359,11,17,[2,3,11,263]),
  (17389,13,58,[2,3,7,23]),
  (17401,21,121,[2,3,5,29]),
  (17431,6,2,[2,3,5,7,83]),
  (17443,2,16,[2,3,17,19]),
  (17467,2,21,[2,3,41,71]),
  (17491,2,6,[2,3,5,11,53]),
  (17539,2,5,[2,3,37,79]),
  (17551,6,11,[2,3,5,13]),
  (17581,13,60,[2,3,5,293]),
  (17599,14,20,[2,3,7,419]),
  (17623,5,2,[2,3,11,89]),
  (17683,32,25,[2,3,7,421]),
  (17707,2,37,[2,3,13,227]),
  (17749,10,7,[2,3,17,29]),
  (17761,22,37,[2,3,5,37]),
  (17791,6,9,[2,3,5,593]),
  (17851,10,14,[2,3,5,7,17]),
  (17863,5,13,[2,3,13,229]),
  (17881,13,97,[2,3,5,149]),
  (17911,21,4,[2,3,5,199]),
  (17923,11,55,[2,3,29,103]),
  (17959,6,2,[2,3,41,73]),
  (17971,2,6,[2,3,5,599]),
  (17977,19,2,[2,3,7,107]),
  (18013,14,3,[2,3,19,79]),
  (18043,2,22,[2,3,31,97]),
  (18061,10,52,[2,3,5,7,43]),
  (18097,10,3,[2,3,13,29]),
  (18121,56,11,[2,3,5,151]),
  (18127,5,15,[2,3,19,53]),
  (18131,6,13,[2,5,7,37]),
  (18181,23,4,[2,3,5,101]),
  (18211,12,5,[2,3,5,607]),
  (18217,14,3,[2,3,11,23]),
  (18229,10,15,[2,3,7,31]),
  (18301,10,48,[2,3,5,61]),
  (18313,29,2,[2,3,7,109]),
  (18397,5,10,[2,3,7,73]),
  (18427,12,6,[2,3,37,83]),
  (18439,6,5,[2,3,7,439]),
  (18451,2,5,[2,3,5,41]),
  (18481,38,5,[2,3,5,7,11]),
  (18493,6,37,[2,3,23,67]),
  (18541,28,41,[2,3,5,103]),
  (18583,5,18,[2,3,19,163]),
  (18661,21,33,[2,3,5,311]),
  (18679,11,18,[2,3,11,283]),
  (18691,2,54,[2,3,5,7,89]),
  (18787,2,6,[2,3,31,101]),
  (18859,2,5,[2,3,7,449]),
  (18973,20,25,[2,3,17,31]),
  (19051,2,16,[2,3,5,127]),
  (19069,13,3,[2,3,7,227]),
  (19081,33,30,[2,3,5,53]),
  (19141,6,36,[2,3,5,11,29]),
  (19183,5,18,[2,3,23,139]),
  (19207,10,2,[2,3,11,97])]

def orders8 : List ℕ := [16087,16111,16141,16183,16189,16231,16339,16369,16381,16411,16451,16561,16567,16633,16651,16661,16693,16699,16729,16741,16759,16831,16843,16871,16879,16921,16927,16963,16981,16987,17011,17029,17041,17053,17137,17191,17203,17239,17291,17293,17317,17341,17359,17389,17401,17431,17443,17467,17491,17539,17551,17581,17599,17623,17683,17707,17749,17761,17791,17851,17863,17881,17911,17923,17959,17971,17977,18013,18043,18061,18097,18121,18127,18131,18181,18211,18217,18229,18301,18313,18397,18427,18439,18451,18481,18493,18541,18583,18661,18679,18691,18787,18859,18973,19051,19069,19081,19141,19183,19207]

theorem certs8_ok : checkAll certs8 = true := by decide +kernel

theorem certs8_orders : certs8.map (·.1) = orders8 := by decide +kernel

theorem good8 : ∀ q ∈ orders8, Good q :=
  certs8_orders ▸ checkAll_sound certs8_ok

def certs9 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (19231,22,4,[2,3,5,641]),
  (19237,31,21,[2,3,7,229]),
  (19267,2,9,[2,3,13,19]),
  (19273,29,7,[2,3,11,73]),
  (19381,6,91,[2,3,5,17,19]),
  (19423,20,25,[2,3,13,83]),
  (19447,5,9,[2,3,7,463]),
  (19471,14,41,[2,3,5,11,59]),
  (19483,2,11,[2,3,17,191]),
  (19489,33,18,[2,3,7,29]),
  (19501,6,29,[2,3,5,13]),
  (19531,12,21,[2,3,5,7,31]),
  (19597,5,25,[2,3,23,71]),
  (19609,61,2,[2,3,19,43]),
  (19681,33,14,[2,3,5,41]),
  (19687,12,19,[2,3,17,193]),
  (19699,10,21,[2,3,7,67]),
  (19717,6,31,[2,3,31,53]),
  (19801,13,66,[2,3,5,11]),
  (19813,5,4,[2,3,13,127]),
  (19861,10,21,[2,3,5,331]),
  (19867,2,14,[2,3,7,11,43]),
  (19891,2,9,[2,3,5,13,17]),
  (19993,29,50,[2,3,7,17]),
  (20011,14,17,[2,3,5,23,29]),
  (20021,2,11,[2,5,7,11,13]),
  (20047,11,4,[2,3,13,257]),
  (20071,14,2,[2,3,5,223]),
  (20101,17,34,[2,3,5,67]),
  (20149,30,41,[2,3,23,73]),
  (20161,52,7,[2,3,5,7]),
  (20287,5,19,[2,3,7,23]),
  (20341,10,113,[2,3,5,113]),
  (20359,21,14,[2,3,13,29]),
  (20407,6,13,[2,3,19,179]),
  (20431,11,14,[2,3,5,227]),
  (20521,46,3,[2,3,5,19]),
  (20551,21,10,[2,3,5,137]),
  (20593,20,25,[2,3,11,13]),
  (20611,2,7,[2,3,5,229]),
  (20641,34,52,[2,3,5,43]),
  (20707,12,21,[2,3,7,17,29]),
  (20731,2,16,[2,3,5,691]),
  (20749,46,4,[2,3,7,13,19]),
  (20857,19,14,[2,3,11,79]),
  (20959,6,21,[2,3,7,499]),
  (20983,5,11,[2,3,13,269]),
  (21001,51,12,[2,3,5,7]),
  (21031,23,4,[2,3,5,701]),
  (21061,6,62,[2,3,5,13]),
  (21121,68,3,[2,3,5,11]),
  (21139,14,11,[2,3,13,271]),
  (21187,11,4,[2,3,11,107]),
  (21211,2,5,[2,3,5,7,101]),
  (21319,27,2,[2,3,11,17,19]),
  (21379,17,16,[2,3,7,509]),
  (21391,23,16,[2,3,5,23,31]),
  (21481,34,15,[2,3,5,179]),
  (21517,6,19,[2,3,11,163]),
  (21529,33,47,[2,3,13,23]),
  (21589,31,36,[2,3,7,257]),
  (21649,42,24,[2,3,11,41]),
  (21661,6,14,[2,3,5,19]),
  (21673,38,17,[2,3,7,43]),
  (21751,6,2,[2,3,5,29]),
  (21757,5,10,[2,3,7,37]),
  (21799,6,25,[2,3,7,173]),
  (21841,22,65,[2,3,5,7,13]),
  (21961,58,5,[2,3,5,61]),
  (21991,6,11,[2,3,5,733]),
  (21997,6,14,[2,3,13,47]),
  (22051,2,9,[2,3,5,7]),
  (22093,5,12,[2,3,7,263]),
  (22111,11,14,[2,3,5,11,67]),
  (22171,17,4,[2,3,5,739]),
  (22291,2,5,[2,3,5,743]),
  (22303,5,11,[2,3,7,59]),
  (22381,18,28,[2,3,5,373]),
  (22441,73,15,[2,3,5,11,17]),
  (22531,10,25,[2,3,5,751]),
  (22543,5,2,[2,3,13,17]),
  (22573,5,46,[2,3,11,19]),
  (22621,30,87,[2,3,5,13,29]),
  (22639,11,21,[2,3,7,11]),
  (22651,2,6,[2,3,5,151]),
  (22741,6,126,[2,3,5,379]),
  (22807,5,15,[2,3,7,181]),
  (22861,22,4,[2,3,5,127]),
  (22921,33,57,[2,3,5,191]),
  (23011,27,23,[2,3,5,13,59]),
  (23017,19,12,[2,3,7,137]),
  (23059,2,5,[2,3,7,61]),
  (23071,21,9,[2,3,5,769]),
  (23131,2,5,[2,3,5,257]),
  (23143,33,29,[2,3,7,19,29]),
  (23167,11,15,[2,3,11,13]),
  (23227,2,9,[2,3,7,79]),
  (23251,2,16,[2,3,5,31]),
  (23269,29,5,[2,3,7,277]),
  (23311,6,11,[2,3,5,7,37])]

def orders9 : List ℕ := [19231,19237,19267,19273,19381,19423,19447,19471,19483,19489,19501,19531,19597,19609,19681,19687,19699,19717,19801,19813,19861,19867,19891,19993,20011,20021,20047,20071,20101,20149,20161,20287,20341,20359,20407,20431,20521,20551,20593,20611,20641,20707,20731,20749,20857,20959,20983,21001,21031,21061,21121,21139,21187,21211,21319,21379,21391,21481,21517,21529,21589,21649,21661,21673,21751,21757,21799,21841,21961,21991,21997,22051,22093,22111,22171,22291,22303,22381,22441,22531,22543,22573,22621,22639,22651,22741,22807,22861,22921,23011,23017,23059,23071,23131,23143,23167,23227,23251,23269,23311]

theorem certs9_ok : checkAll certs9 = true := by decide +kernel

theorem certs9_orders : certs9.map (·.1) = orders9 := by decide +kernel

theorem good9 : ∀ q ∈ orders9, Good q :=
  certs9_orders ▸ checkAll_sound certs9_ok

def certs10 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (23371,18,4,[2,3,5,19,41]),
  (23431,11,5,[2,3,5,11,71]),
  (23563,11,56,[2,3,7,11,17]),
  (23581,6,5,[2,3,5,131]),
  (23671,6,5,[2,3,5,263]),
  (23689,22,60,[2,3,7,47]),
  (23761,28,5,[2,3,5,11]),
  (23773,14,7,[2,3,7,283]),
  (23827,11,90,[2,3,11,19]),
  (23857,19,25,[2,3,7,71]),
  (23869,6,67,[2,3,13,17]),
  (23899,2,16,[2,3,7,569]),
  (23911,38,34,[2,3,5,797]),
  (23971,32,65,[2,3,5,17,47]),
  (24061,17,3,[2,3,5,401]),
  (24091,10,5,[2,3,5,11,73]),
  (24109,10,74,[2,3,7,41]),
  (24121,13,29,[2,3,5,67]),
  (24151,6,21,[2,3,5,7,23]),
  (24181,17,132,[2,3,5,13,31]),
  (24391,11,19,[2,3,5,271]),
  (24421,6,49,[2,3,5,11,37]),
  (24481,73,30,[2,3,5,17]),
  (24571,18,57,[2,3,5,7,13]),
  (24631,29,5,[2,3,5,821]),
  (24691,2,11,[2,3,5,823]),
  (24781,30,63,[2,3,5,7,59]),
  (24841,13,10,[2,3,5,23]),
  (24907,11,77,[2,3,7,593]),
  (25033,19,7,[2,3,7,149]),
  (25111,6,10,[2,3,5,31]),
  (25117,18,23,[2,3,7,13,23]),
  (25171,2,7,[2,3,5,839]),
  (25261,6,73,[2,3,5,421]),
  (25321,43,39,[2,3,5,211]),
  (25411,10,5,[2,3,5,7,11]),
  (25471,30,16,[2,3,5,283]),
  (25537,10,47,[2,3,7,19]),
  (25561,33,15,[2,3,5,71]),
  (25579,10,14,[2,3,7,29]),
  (25621,10,68,[2,3,5,7,61]),
  (25741,17,140,[2,3,5,11,13]),
  (25771,2,9,[2,3,5,859]),
  (25801,33,23,[2,3,5,43]),
  (25873,46,3,[2,3,7,11]),
  (25951,27,9,[2,3,5,173]),
  (25981,10,21,[2,3,5,433]),
  (26041,51,6,[2,3,5,7,31]),
  (26083,22,46,[2,3,7,23]),
  (26161,46,34,[2,3,5,109]),
  (26209,76,13,[2,3,7,13]),
  (26251,38,4,[2,3,5,7]),
  (26371,2,6,[2,3,5,293]),
  (26431,11,34,[2,3,5,881]),
  (26641,28,2,[2,3,5,37]),
  (26701,21,101,[2,3,5,89]),
  (26731,2,5,[2,3,5,11]),
  (26821,13,84,[2,3,5,149]),
  (26881,22,14,[2,3,5,7]),
  (27031,11,17,[2,3,5,17,53]),
  (27061,6,29,[2,3,5,11,41]),
  (27091,11,20,[2,3,5,7,43]),
  (27211,17,6,[2,3,5,907]),
  (27241,38,12,[2,3,5,227]),
  (27259,10,4,[2,3,7,11,59]),
  (27271,37,5,[2,3,5,101]),
  (27361,58,5,[2,3,5,19]),
  (27481,28,12,[2,3,5,229]),
  (27541,18,89,[2,3,5,17]),
  (27631,6,40,[2,3,5,307]),
  (27691,2,7,[2,3,5,13,71]),
  (27751,11,7,[2,3,5,37]),
  (27847,5,19,[2,3,7,13,17]),
  (27901,6,37,[2,3,5,31]),
  (27961,38,23,[2,3,5,233]),
  (28051,10,17,[2,3,5,11,17]),
  (28081,46,13,[2,3,5,13]),
  (28111,12,9,[2,3,5,937]),
  (28183,6,25,[2,3,7,11,61]),
  (28201,21,39,[2,3,5,47]),
  (28211,6,5,[2,5,7,13,31]),
  (28351,11,10,[2,3,5,7]),
  (28393,22,82,[2,3,7,13]),
  (28411,11,30,[2,3,5,947]),
  (28621,28,34,[2,3,5,53]),
  (28711,6,9,[2,3,5,11,29]),
  (28771,18,45,[2,3,5,7,137]),
  (28843,19,4,[2,3,11,19,23]),
  (29173,5,30,[2,3,11,13,17]),
  (29191,6,39,[2,3,5,7,139]),
  (29251,17,51,[2,3,5,13]),
  (29401,91,15,[2,3,5,7]),
  (29527,5,25,[2,3,7,19,37]),
  (29569,52,3,[2,3,7,11]),
  (29581,32,164,[2,3,5,17,29]),
  (29611,2,30,[2,3,5,7,47]),
  (29641,28,15,[2,3,5,13,19]),
  (29671,11,10,[2,3,5,23,43]),
  (29761,22,5,[2,3,5,31]),
  (29947,2,76,[2,3,7,23,31])]

def orders10 : List ℕ := [23371,23431,23563,23581,23671,23689,23761,23773,23827,23857,23869,23899,23911,23971,24061,24091,24109,24121,24151,24181,24391,24421,24481,24571,24631,24691,24781,24841,24907,25033,25111,25117,25171,25261,25321,25411,25471,25537,25561,25579,25621,25741,25771,25801,25873,25951,25981,26041,26083,26161,26209,26251,26371,26431,26641,26701,26731,26821,26881,27031,27061,27091,27211,27241,27259,27271,27361,27481,27541,27631,27691,27751,27847,27901,27961,28051,28081,28111,28183,28201,28211,28351,28393,28411,28621,28711,28771,28843,29173,29191,29251,29401,29527,29569,29581,29611,29641,29671,29761,29947]

theorem certs10_ok : checkAll certs10 = true := by decide +kernel

theorem certs10_orders : certs10.map (·.1) = orders10 := by decide +kernel

theorem good10 : ∀ q ∈ orders10, Good q :=
  certs10_orders ▸ checkAll_sound certs10_ok

def certs11 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (30091,32,67,[2,3,5,17,59]),
  (30211,2,29,[2,3,5,19,53]),
  (30241,94,17,[2,3,5,7]),
  (30661,17,60,[2,3,5,7,73]),
  (30703,5,17,[2,3,7,17,43]),
  (30781,23,11,[2,3,5,19]),
  (30871,6,9,[2,3,5,7]),
  (30941,2,52,[2,5,7,13,17]),
  (31051,10,7,[2,3,5,23]),
  (31081,51,23,[2,3,5,7,37]),
  (31123,2,9,[2,3,7,13,19]),
  (31981,21,11,[2,3,5,13,41]),
  (32191,21,4,[2,3,5,29,37]),
  (32341,17,41,[2,3,5,7,11]),
  (32371,10,19,[2,3,5,13,83]),
  (32719,13,4,[2,3,7,19,41]),
  (32803,19,24,[2,3,7,11,71]),
  (32971,10,65,[2,3,5,7,157]),
  (33151,42,50,[2,3,5,13,17]),
  (33181,17,11,[2,3,5,7,79]),
  (33331,2,9,[2,3,5,11,101]),
  (33391,12,11,[2,3,5,7,53]),
  (33601,73,38,[2,3,5,7]),
  (33811,22,44,[2,3,5,7,23]),
  (33931,32,52,[2,3,5,13,29]),
  (34171,2,5,[2,3,5,17,67]),
  (34231,12,19,[2,3,5,7,163]),
  (34511,42,30,[2,5,7,17,29]),
  (34651,37,21,[2,3,5,7,11]),
  (34981,13,36,[2,3,5,11,53]),
  (35281,58,10,[2,3,5,7]),
  (35311,21,17,[2,3,5,11,107]),
  (35491,10,21,[2,3,5,7,13]),
  (35531,10,25,[2,5,11,17,19]),
  (35671,21,2,[2,3,5,29,41]),
  (35911,13,119,[2,3,5,7,19]),
  (36037,5,25,[2,3,7,11,13]),
  (36191,22,9,[2,5,7,11,47]),
  (36541,13,29,[2,3,5,7,29]),
  (36571,2,16,[2,3,5,23,53]),
  (36583,6,17,[2,3,7,13,67]),
  (36709,10,34,[2,3,7,19,23]),
  (37171,2,9,[2,3,5,7,59]),
  (37507,28,38,[2,3,7,19,47]),
  (37591,6,18,[2,3,5,7,179]),
  (37831,57,19,[2,3,5,13,97]),
  (37951,14,2,[2,3,5,11,23]),
  (38011,18,11,[2,3,5,7,181]),
  (38039,34,3,[2,7,11,13,19]),
  (38281,62,12,[2,3,5,11,29]),
  (38431,6,11,[2,3,5,7,61]),
  (38611,2,20,[2,3,5,11,13]),
  (38767,6,33,[2,3,7,13,71]),
  (38851,2,81,[2,3,5,7,37]),
  (39607,5,9,[2,3,7,23,41]),
  (39733,5,23,[2,3,7,11,43]),
  (39901,53,5,[2,3,5,7,19]),
  (40111,11,10,[2,3,5,7,191]),
  (40471,12,9,[2,3,5,19,71]),
  (40531,2,14,[2,3,5,7,193]),
  (40591,12,73,[2,3,5,11,41]),
  (40699,2,9,[2,3,7,17,19]),
  (41231,13,4,[2,5,7,19,31]),
  (41341,6,33,[2,3,5,13,53]),
  (41413,5,11,[2,3,7,17,29]),
  (41539,2,9,[2,3,7,23,43]),
  (41611,10,16,[2,3,5,19,73]),
  (41911,11,57,[2,3,5,11,127]),
  (42043,11,15,[2,3,7,11,13]),
  (42181,10,20,[2,3,5,19,37]),
  (42331,2,5,[2,3,5,17,83]),
  (42571,11,14,[2,3,5,11,43]),
  (42841,22,6,[2,3,5,7,17]),
  (42901,6,36,[2,3,5,11,13]),
  (42967,6,2,[2,3,7,11,31]),
  (42979,2,9,[2,3,13,19,29]),
  (43051,2,11,[2,3,5,7,41]),
  (43261,37,5,[2,3,5,7,103]),
  (43291,2,9,[2,3,5,13,37]),
  (43711,12,11,[2,3,5,31,47]),
  (43759,11,10,[2,3,11,13,17]),
  (43891,2,73,[2,3,5,7,11,19]),
  (44071,11,10,[2,3,5,13,113]),
  (44221,13,3,[2,3,5,11,67]),
  (44269,29,3,[2,3,7,17,31]),
  (44371,12,16,[2,3,5,17,29]),
  (44773,5,11,[2,3,7,13,41]),
  (44851,18,5,[2,3,5,13,23]),
  (45319,23,22,[2,3,7,13,83]),
  (45403,2,6,[2,3,7,23,47]),
  (45541,21,60,[2,3,5,11,23]),
  (45943,5,18,[2,3,13,19,31]),
  (46021,10,107,[2,3,5,13,59]),
  (46399,21,4,[2,3,11,19,37]),
  (46411,2,66,[2,3,5,7,13,17]),
  (46663,11,4,[2,3,7,11,101]),
  (46691,7,3,[2,5,7,23,29]),
  (46831,6,10,[2,3,5,7,223]),
  (46861,23,36,[2,3,5,11,71]),
  (46957,17,21,[2,3,7,13,43])]

def orders11 : List ℕ := [30091,30211,30241,30661,30703,30781,30871,30941,31051,31081,31123,31981,32191,32341,32371,32719,32803,32971,33151,33181,33331,33391,33601,33811,33931,34171,34231,34511,34651,34981,35281,35311,35491,35531,35671,35911,36037,36191,36541,36571,36583,36709,37171,37507,37591,37831,37951,38011,38039,38281,38431,38611,38767,38851,39607,39733,39901,40111,40471,40531,40591,40699,41231,41341,41413,41539,41611,41911,42043,42181,42331,42571,42841,42901,42967,42979,43051,43261,43291,43711,43759,43891,44071,44221,44269,44371,44773,44851,45319,45403,45541,45943,46021,46399,46411,46663,46691,46831,46861,46957]

theorem certs11_ok : checkAll certs11 = true := by decide +kernel

theorem certs11_orders : certs11.map (·.1) = orders11 := by decide +kernel

theorem good11 : ∀ q ∈ orders11, Good q :=
  certs11_orders ▸ checkAll_sound certs11_ok

def certs12 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (47059,2,7,[2,3,11,23,31]),
  (47431,12,16,[2,3,5,17,31]),
  (47581,10,75,[2,3,5,13,61]),
  (47741,2,148,[2,5,7,11,31]),
  (47881,78,22,[2,3,5,7,19]),
  (48049,85,24,[2,3,7,11,13]),
  (48091,27,14,[2,3,5,7,229]),
  (48247,10,13,[2,3,11,17,43]),
  (48679,6,2,[2,3,7,19,61]),
  (48907,11,4,[2,3,11,13,19]),
  (48973,5,21,[2,3,7,11,53]),
  (48991,12,22,[2,3,5,23,71]),
  (49171,14,22,[2,3,5,11,149]),
  (49211,6,3,[2,5,7,19,37]),
  (49477,14,19,[2,3,7,19,31]),
  (49531,10,20,[2,3,5,13,127]),
  (49831,11,2,[2,3,5,11,151]),
  (49939,17,36,[2,3,7,29,41]),
  (50051,6,3,[2,5,7,11,13]),
  (50311,14,5,[2,3,5,13,43]),
  (50359,6,9,[2,3,7,11,109]),
  (50821,30,176,[2,3,5,7,11]),
  (51061,6,65,[2,3,5,23,37]),
  (51151,11,18,[2,3,5,11,31]),
  (51199,11,18,[2,3,7,23,53]),
  (51241,67,40,[2,3,5,7,61]),
  (51283,11,4,[2,3,7,11,37]),
  (51481,37,18,[2,3,5,11,13]),
  (51511,11,19,[2,3,5,17,101]),
  (51613,31,19,[2,3,11,17,23]),
  (51871,6,53,[2,3,5,7,13,19]),
  (52027,17,10,[2,3,13,23,29]),
  (52081,57,3,[2,3,5,7,31]),
  (52291,27,6,[2,3,5,7,83]),
  (52361,42,10,[2,5,7,11,17]),
  (52711,34,26,[2,3,5,7,251]),
  (52837,13,26,[2,3,7,17,37]),
  (52963,2,19,[2,3,7,13,97]),
  (53197,54,41,[2,3,11,13,31]),
  (53551,6,9,[2,3,5,7,17]),
  (53593,19,2,[2,3,7,11,29]),
  (53791,21,4,[2,3,5,11,163]),
  (53923,18,14,[2,3,11,19,43]),
  (54121,51,18,[2,3,5,11,41]),
  (54181,33,4,[2,3,5,7,43]),
  (54367,20,7,[2,3,13,17,41]),
  (54517,14,25,[2,3,7,11,59]),
  (54601,67,30,[2,3,5,7,13]),
  (54979,2,21,[2,3,7,11,17]),
  (55021,10,3,[2,3,5,7,131]),
  (55147,18,10,[2,3,7,13,101]),
  (55291,10,39,[2,3,5,19,97]),
  (55381,10,48,[2,3,5,13,71]),
  (55441,37,5,[2,3,5,7,11]),
  (55511,21,2,[2,5,7,13,61]),
  (55931,29,3,[2,5,7,17,47]),
  (55987,2,47,[2,3,7,31,43]),
  (56101,6,99,[2,3,5,11,17]),
  (56167,5,14,[2,3,11,23,37]),
  (56239,14,42,[2,3,7,13,103]),
  (56431,6,9,[2,3,5,11,19]),
  (56611,27,59,[2,3,5,17,37]),
  (56659,2,5,[2,3,7,19,71]),
  (56731,2,5,[2,3,5,31,61]),
  (56827,2,21,[2,3,7,11,41]),
  (56911,6,31,[2,3,5,7,271]),
  (56941,29,3,[2,3,5,13,73]),
  (57191,28,12,[2,5,7,19,43]),
  (57271,11,17,[2,3,5,23,83]),
  (57331,2,20,[2,3,5,7,13]),
  (57487,5,14,[2,3,11,13,67]),
  (57571,12,17,[2,3,5,19,101]),
  (57751,6,31,[2,3,5,7,11]),
  (58111,11,16,[2,3,5,13,149]),
  (58171,2,5,[2,3,5,7,277]),
  (58411,11,6,[2,3,5,11,59]),
  (58549,10,74,[2,3,7,17,41]),
  (58631,37,5,[2,5,11,13,41]),
  (58711,6,5,[2,3,5,19,103]),
  (58741,17,3,[2,3,5,11,89]),
  (58787,5,4,[2,7,13,17,19]),
  (58831,21,43,[2,3,5,37,53]),
  (59011,18,5,[2,3,5,7,281]),
  (59053,14,28,[2,3,7,19,37]),
  (59221,17,3,[2,3,5,7,47]),
  (59263,5,17,[2,3,7,17,83]),
  (59281,21,34,[2,3,5,13,19]),
  (59341,17,13,[2,3,5,23,43]),
  (59467,2,22,[2,3,11,17,53]),
  (59671,38,17,[2,3,5,13,17]),
  (60271,6,29,[2,3,5,7,41]),
  (60607,5,9,[2,3,7,13,37]),
  (60611,10,7,[2,5,11,19,29]),
  (60631,14,18,[2,3,5,43,47]),
  (60763,2,37,[2,3,13,19,41]),
  (60901,22,36,[2,3,5,7,29]),
  (60919,11,7,[2,3,11,13,71]),
  (61051,2,17,[2,3,5,11,37]),
  (61231,6,23,[2,3,5,13,157]),
  (61381,6,14,[2,3,5,11,31])]

def orders12 : List ℕ := [47059,47431,47581,47741,47881,48049,48091,48247,48679,48907,48973,48991,49171,49211,49477,49531,49831,49939,50051,50311,50359,50821,51061,51151,51199,51241,51283,51481,51511,51613,51871,52027,52081,52291,52361,52711,52837,52963,53197,53551,53593,53791,53923,54121,54181,54367,54517,54601,54979,55021,55147,55291,55381,55441,55511,55931,55987,56101,56167,56239,56431,56611,56659,56731,56827,56911,56941,57191,57271,57331,57487,57571,57751,58111,58171,58411,58549,58631,58711,58741,58787,58831,59011,59053,59221,59263,59281,59341,59467,59671,60271,60607,60611,60631,60763,60901,60919,61051,61231,61381]

theorem certs12_ok : checkAll certs12 = true := by decide +kernel

theorem certs12_orders : certs12.map (·.1) = orders12 := by decide +kernel

theorem good12 : ∀ q ∈ orders12, Good q :=
  certs12_orders ▸ checkAll_sound certs12_ok

def certs13 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (61909,17,48,[2,3,7,11,67]),
  (62011,14,25,[2,3,5,13,53]),
  (62119,6,11,[2,3,7,17,29]),
  (62131,10,5,[2,3,5,19,109]),
  (62311,6,2,[2,3,5,31,67]),
  (62323,22,15,[2,3,13,17,47]),
  (62581,10,28,[2,3,5,7,149]),
  (62701,13,78,[2,3,5,11,19]),
  (62731,10,23,[2,3,5,17,41]),
  (62791,14,13,[2,3,5,7,13,23]),
  (63031,12,23,[2,3,5,11,191]),
  (63211,10,21,[2,3,5,7,43]),
  (63241,21,13,[2,3,5,17,31]),
  (63337,10,72,[2,3,7,13,29]),
  (63421,10,46,[2,3,5,7,151]),
  (63493,5,4,[2,3,11,13,37]),
  (63691,14,7,[2,3,5,11,193]),
  (63727,5,30,[2,3,13,19,43]),
  (63841,51,42,[2,3,5,7,19]),
  (64091,10,20,[2,5,13,17,29]),
  (64171,27,5,[2,3,5,23,31]),
  (64381,38,5,[2,3,5,29,37]),
  (64891,22,45,[2,3,5,7,103]),
  (65011,10,59,[2,3,5,11,197]),
  (65101,23,113,[2,3,5,7,31]),
  (65437,5,65,[2,3,7,19,41]),
  (65521,73,21,[2,3,5,7,13]),
  (65551,12,5,[2,3,5,19,23]),
  (65731,32,13,[2,3,5,7,313]),
  (66067,2,34,[2,3,7,11,13]),
  (66221,2,28,[2,5,7,11,43]),
  (66301,22,39,[2,3,5,13,17]),
  (66361,37,20,[2,3,5,7,79]),
  (66403,2,16,[2,3,7,17,31]),
  (66431,34,9,[2,5,7,13,73]),
  (66463,11,2,[2,3,11,19,53]),
  (66571,22,36,[2,3,5,7,317]),
  (66931,2,26,[2,3,5,23,97]),
  (67211,6,16,[2,5,11,13,47]),
  (67261,10,19,[2,3,5,19,59]),
  (67411,2,73,[2,3,5,7,107]),
  (67453,5,10,[2,3,7,11,73]),
  (67651,10,13,[2,3,5,11,41]),
  (67783,5,18,[2,3,11,13,79]),
  (67891,2,7,[2,3,5,31,73]),
  (68311,11,66,[2,3,5,11,23]),
  (68371,27,11,[2,3,5,43,53]),
  (68443,28,17,[2,3,11,17,61]),
  (68531,6,17,[2,5,7,11,89]),
  (68821,18,13,[2,3,5,31,37]),
  (68881,52,21,[2,3,5,7,41]),
  (69031,14,9,[2,3,5,13,59]),
  (69191,52,5,[2,5,11,17,37]),
  (69259,12,26,[2,3,7,17,97]),
  (69427,2,9,[2,3,7,19,29]),
  (69691,12,25,[2,3,5,23,101]),
  (69763,2,14,[2,3,7,11,151]),
  (69931,2,23,[2,3,5,7,37]),
  (70111,12,11,[2,3,5,19,41]),
  (70123,2,22,[2,3,13,29,31]),
  (70141,13,5,[2,3,5,7,167]),
  (70351,6,10,[2,3,5,7,67]),
  (70381,28,5,[2,3,5,17,23]),
  (70621,23,43,[2,3,5,11,107]),
  (70687,6,2,[2,3,7,11,17]),
  (70841,30,10,[2,5,7,11,23]),
  (70891,2,14,[2,3,5,17,139]),
  (70951,11,49,[2,3,5,11,43]),
  (70981,17,23,[2,3,5,7,13]),
  (71023,5,11,[2,3,7,19,89]),
  (71191,33,10,[2,3,5,7,113]),
  (71341,10,20,[2,3,5,29,41]),
  (71347,11,4,[2,3,11,23,47]),
  (71527,19,13,[2,3,7,13,131]),
  (71707,11,4,[2,3,17,19,37]),
  (71761,43,23,[2,3,5,13,23]),
  (71821,10,51,[2,3,5,7,19]),
  (71941,23,4,[2,3,5,11,109]),
  (72073,29,2,[2,3,7,11,13]),
  (72211,2,16,[2,3,5,29,83]),
  (72271,11,7,[2,3,5,11,73]),
  (72421,10,77,[2,3,5,17,71]),
  (72661,10,145,[2,3,5,7,173]),
  (72727,6,29,[2,3,17,23,31]),
  (72733,6,42,[2,3,11,19,29]),
  (72871,12,5,[2,3,5,7,347]),
  (72931,39,33,[2,3,5,11,13,17]),
  (72997,13,77,[2,3,7,11,79]),
  (73039,12,22,[2,3,7,37,47]),
  (73141,6,49,[2,3,5,23,53]),
  (73291,2,17,[2,3,5,7,349]),
  (73417,29,61,[2,3,7,19,23]),
  (73459,2,5,[2,3,7,11,53]),
  (73471,12,18,[2,3,5,31,79]),
  (73951,23,19,[2,3,5,17,29]),
  (74047,19,2,[2,3,7,41,43]),
  (74101,21,11,[2,3,5,13,19]),
  (74131,12,56,[2,3,5,7,353]),
  (74257,29,61,[2,3,7,13,17]),
  (74383,5,17,[2,3,7,11,23])]

def orders13 : List ℕ := [61909,62011,62119,62131,62311,62323,62581,62701,62731,62791,63031,63211,63241,63337,63421,63493,63691,63727,63841,64091,64171,64381,64891,65011,65101,65437,65521,65551,65731,66067,66221,66301,66361,66403,66431,66463,66571,66931,67211,67261,67411,67453,67651,67783,67891,68311,68371,68443,68531,68821,68881,69031,69191,69259,69427,69691,69763,69931,70111,70123,70141,70351,70381,70621,70687,70841,70891,70951,70981,71023,71191,71341,71347,71527,71707,71761,71821,71941,72073,72211,72271,72421,72661,72727,72733,72871,72931,72997,73039,73141,73291,73417,73459,73471,73951,74047,74101,74131,74257,74383]

theorem certs13_ok : checkAll certs13 = true := by decide +kernel

theorem certs13_orders : certs13.map (·.1) = orders13 := by decide +kernel

theorem good13 : ∀ q ∈ orders13, Good q :=
  certs13_orders ▸ checkAll_sound certs13_ok

def certs14 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (74551,11,43,[2,3,5,7,71]),
  (74731,13,16,[2,3,5,47,53]),
  (74761,38,14,[2,3,5,7,89]),
  (74821,10,17,[2,3,5,29,43]),
  (75013,5,17,[2,3,7,19,47]),
  (75181,17,4,[2,3,5,7,179]),
  (75211,12,36,[2,3,5,23,109]),
  (75307,2,6,[2,3,7,11,163]),
  (75391,27,10,[2,3,5,7,359]),
  (75571,2,6,[2,3,5,11,229]),
  (75583,6,16,[2,3,13,17,19]),
  (75703,10,25,[2,3,11,31,37]),
  (75991,12,47,[2,3,5,17,149]),
  (76039,23,10,[2,3,19,23,29]),
  (76231,22,69,[2,3,5,7,11]),
  (76261,6,68,[2,3,5,31,41]),
  (76441,86,13,[2,3,5,7,13]),
  (76561,46,40,[2,3,5,11,29]),
  (76651,2,20,[2,3,5,7,73]),
  (76819,12,11,[2,3,7,31,59]),
  (76831,57,13,[2,3,5,13,197]),
  (77141,2,30,[2,5,7,19,29]),
  (77191,11,18,[2,3,5,31,83]),
  (77351,46,3,[2,5,7,13,17]),
  (77419,10,6,[2,3,11,17,23]),
  (77431,6,29,[2,3,5,29,89]),
  (77491,2,9,[2,3,5,7,41]),
  (77521,61,3,[2,3,5,17,19]),
  (77551,11,2,[2,3,5,11,47]),
  (77611,17,11,[2,3,5,13,199]),
  (78079,11,17,[2,3,7,11,13]),
  (78121,37,15,[2,3,5,7,31]),
  (78541,13,29,[2,3,5,7,11,17]),
  (78691,27,11,[2,3,5,43,61]),
  (78781,28,31,[2,3,5,13,101]),
  (79231,21,7,[2,3,5,19,139]),
  (79423,5,35,[2,3,7,31,61]),
  (79531,11,14,[2,3,5,11,241]),
  (79561,28,41,[2,3,5,13,17]),
  (79801,22,58,[2,3,5,7,19]),
  (80071,29,5,[2,3,5,17,157]),
  (80221,13,4,[2,3,5,7,191]),
  (80341,29,47,[2,3,5,13,103]),
  (80599,14,9,[2,3,7,19,101]),
  (80683,2,6,[2,3,7,17,113]),
  (80809,57,10,[2,3,7,13,37]),
  (80911,30,9,[2,3,5,29,31]),
  (81031,11,20,[2,3,5,37,73]),
  (81131,6,3,[2,5,7,19,61]),
  (81181,22,3,[2,3,5,11,41]),
  (81283,2,9,[2,3,19,23,31]),
  (81421,10,7,[2,3,5,23,59]),
  (81901,30,22,[2,3,5,7,13]),
  (82171,2,26,[2,3,5,11,83]),
  (82237,5,75,[2,3,7,11,89]),
  (82531,2,17,[2,3,5,7,131]),
  (82651,22,4,[2,3,5,19,29]),
  (82699,2,6,[2,3,7,11,179]),
  (83071,14,19,[2,3,5,13,71]),
  (83077,13,12,[2,3,7,23,43]),
  (83221,6,49,[2,3,5,19,73]),
  (83227,19,13,[2,3,11,13,97]),
  (83641,55,6,[2,3,5,17,41]),
  (83791,6,98,[2,3,5,7,19]),
  (84181,6,36,[2,3,5,23,61]),
  (84211,2,20,[2,3,5,7,401]),
  (84319,11,2,[2,3,13,23,47]),
  (84391,12,38,[2,3,5,29,97]),
  (84421,23,3,[2,3,5,7,67]),
  (84589,10,4,[2,3,7,19,53]),
  (84631,14,10,[2,3,5,7,13,31]),
  (84811,2,30,[2,3,5,11,257]),
  (84871,23,9,[2,3,5,23,41]),
  (85009,37,84,[2,3,7,11,23]),
  (85021,6,49,[2,3,5,13,109]),
  (85411,2,16,[2,3,5,13,73]),
  (85933,5,11,[2,3,7,11,31]),
  (86011,27,30,[2,3,5,47,61]),
  (86131,2,6,[2,3,5,11,29]),
  (86269,17,7,[2,3,7,13,79]),
  (86311,6,52,[2,3,5,7,137]),
  (86461,13,3,[2,3,5,11,131]),
  (86857,19,14,[2,3,7,11,47]),
  (87011,7,4,[2,5,7,11,113]),
  (87151,6,29,[2,3,5,7,83]),
  (87211,12,43,[2,3,5,17,19]),
  (87421,17,36,[2,3,5,31,47]),
  (87517,5,4,[2,3,11,13,17]),
  (87631,11,39,[2,3,5,23,127]),
  (87691,12,23,[2,3,5,37,79]),
  (87721,22,21,[2,3,5,17,43]),
  (87991,13,36,[2,3,5,7,419]),
  (88411,2,5,[2,3,5,7,421]),
  (88741,22,5,[2,3,5,17,29]),
  (88771,10,21,[2,3,5,11,269]),
  (88843,2,16,[2,3,13,17,67]),
  (89041,33,18,[2,3,5,7,53]),
  (89431,37,33,[2,3,5,11,271]),
  (89491,2,9,[2,3,5,19,157]),
  (89563,2,9,[2,3,11,23,59])]

def orders14 : List ℕ := [74551,74731,74761,74821,75013,75181,75211,75307,75391,75571,75583,75703,75991,76039,76231,76261,76441,76561,76651,76819,76831,77141,77191,77351,77419,77431,77491,77521,77551,77611,78079,78121,78541,78691,78781,79231,79423,79531,79561,79801,80071,80221,80341,80599,80683,80809,80911,81031,81131,81181,81283,81421,81901,82171,82237,82531,82651,82699,83071,83077,83221,83227,83641,83791,84181,84211,84319,84391,84421,84589,84631,84811,84871,85009,85021,85411,85933,86011,86131,86269,86311,86461,86857,87011,87151,87211,87421,87517,87631,87691,87721,87991,88411,88741,88771,88843,89041,89431,89491,89563]

theorem certs14_ok : checkAll certs14 = true := by decide +kernel

theorem certs14_orders : certs14.map (·.1) = orders14 := by decide +kernel

theorem good14 : ∀ q ∈ orders14, Good q :=
  certs14_orders ▸ checkAll_sound certs14_ok

def certs15 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (89611,2,9,[2,3,5,29,103]),
  (89671,27,41,[2,3,5,7,61]),
  (89839,6,5,[2,3,7,23,31]),
  (89959,6,9,[2,3,11,29,47]),
  (90271,11,10,[2,3,5,17,59]),
  (90403,2,15,[2,3,13,19,61]),
  (90481,21,24,[2,3,5,13,29]),
  (90511,6,18,[2,3,5,7,431]),
  (90631,13,16,[2,3,5,19,53]),
  (90679,23,22,[2,3,7,17,127]),
  (90931,10,17,[2,3,5,7,433]),
  (91081,58,13,[2,3,5,11,23]),
  (91141,10,89,[2,3,5,7,31]),
  (91183,5,19,[2,3,7,13,167]),
  (91291,12,53,[2,3,5,17,179]),
  (91411,2,6,[2,3,5,11,277]),
  (91591,12,5,[2,3,5,43,71]),
  (91631,21,31,[2,5,7,11,17]),
  (91771,10,20,[2,3,5,7,19,23]),
  (91807,10,41,[2,3,11,13,107]),
  (91939,2,9,[2,3,7,11,199]),
  (92041,106,24,[2,3,5,13,59]),
  (92107,2,31,[2,3,7,17,43]),
  (92221,6,109,[2,3,5,29,53]),
  (92311,6,29,[2,3,5,17,181]),
  (92401,102,6,[2,3,5,7,11]),
  (92431,11,7,[2,3,5,13,79]),
  (92461,6,12,[2,3,5,23,67]),
  (92569,46,14,[2,3,7,19,29]),
  (92821,41,11,[2,3,5,7,13,17]),
  (92863,5,18,[2,3,7,11,67]),
  (93241,38,6,[2,3,5,7,37]),
  (93481,77,68,[2,3,5,19,41]),
  (93523,17,4,[2,3,11,13,109]),
  (93703,22,53,[2,3,7,23,97]),
  (93787,11,6,[2,3,7,11,29]),
  (93811,2,19,[2,3,5,53,59]),
  (93871,23,5,[2,3,5,7,149]),
  (93913,10,37,[2,3,7,13,43]),
  (94117,17,10,[2,3,11,23,31]),
  (94291,27,11,[2,3,5,7,449]),
  (94351,30,14,[2,3,5,17,37]),
  (94531,12,25,[2,3,5,23,137]),
  (94621,10,4,[2,3,5,19,83]),
  (95083,2,9,[2,3,13,23,53]),
  (95131,34,46,[2,3,5,7,151]),
  (95191,12,22,[2,3,5,19,167]),
  (95239,6,16,[2,3,11,13,37]),
  (95461,40,55,[2,3,5,37,43]),
  (95701,23,20,[2,3,5,11,29]),
  (95791,30,19,[2,3,5,31,103]),
  (95881,61,10,[2,3,5,17,47]),
  (95911,23,37,[2,3,5,23,139]),
  (95971,2,30,[2,3,5,7,457]),
  (96097,19,23,[2,3,7,11,13]),
  (96181,10,31,[2,3,5,7,229]),
  (96223,5,13,[2,3,7,29,79]),
  (96331,10,17,[2,3,5,13,19]),
  (96493,20,90,[2,3,11,17,43]),
  (96601,33,18,[2,3,5,7,23]),
  (96643,2,9,[2,3,7,13,59]),
  (96799,29,7,[2,3,13,17,73]),
  (97021,23,4,[2,3,5,7,11]),
  (97171,18,5,[2,3,5,41,79]),
  (97231,6,22,[2,3,5,7,463]),
  (97441,52,10,[2,3,5,7,29]),
  (97651,40,5,[2,3,5,7,31]),
  (97813,5,12,[2,3,11,13,19]),
  (97861,22,19,[2,3,5,7,233]),
  (98041,69,151,[2,3,5,19,43]),
  (98407,5,36,[2,3,7,11,71]),
  (98491,27,13,[2,3,5,7,67]),
  (98533,14,4,[2,3,7,17,23]),
  (98869,17,39,[2,3,7,11,107]),
  (98911,13,23,[2,3,5,7,157]),
  (98953,10,18,[2,3,7,19,31]),
  (99139,2,7,[2,3,13,31,41]),
  (99181,6,5,[2,3,5,19,29]),
  (99529,34,6,[2,3,11,13,29]),
  (99661,29,65,[2,3,5,11,151]),
  (99859,11,19,[2,3,11,17,89]),
  (99877,13,29,[2,3,7,29,41]),
  (99961,122,65,[2,3,5,7,17]),
  (99991,11,33,[2,3,5,11,101]),
  (100591,14,10,[2,3,5,7,479]),
  (100621,21,67,[2,3,5,13,43]),
  (100741,30,52,[2,3,5,23,73]),
  (100981,6,11,[2,3,5,11,17]),
  (101221,17,58,[2,3,5,7,241]),
  (101347,11,38,[2,3,7,19,127]),
  (101599,11,2,[2,3,7,41,59]),
  (101641,37,77,[2,3,5,7,11]),
  (102031,12,18,[2,3,5,19,179]),
  (102103,10,4,[2,3,7,11,13,17]),
  (102121,28,23,[2,3,5,23,37]),
  (102181,10,41,[2,3,5,13,131]),
  (102259,2,9,[2,3,13,19,23]),
  (102301,6,15,[2,3,5,11,31]),
  (102397,5,23,[2,3,7,23,53]),
  (102481,51,30,[2,3,5,7,61])]

def orders15 : List ℕ := [89611,89671,89839,89959,90271,90403,90481,90511,90631,90679,90931,91081,91141,91183,91291,91411,91591,91631,91771,91807,91939,92041,92107,92221,92311,92401,92431,92461,92569,92821,92863,93241,93481,93523,93703,93787,93811,93871,93913,94117,94291,94351,94531,94621,95083,95131,95191,95239,95461,95701,95791,95881,95911,95971,96097,96181,96223,96331,96493,96601,96643,96799,97021,97171,97231,97441,97651,97813,97861,98041,98407,98491,98533,98869,98911,98953,99139,99181,99529,99661,99859,99877,99961,99991,100591,100621,100741,100981,101221,101347,101599,101641,102031,102103,102121,102181,102259,102301,102397,102481]

theorem certs15_ok : checkAll certs15 = true := by decide +kernel

theorem certs15_orders : certs15.map (·.1) = orders15 := by decide +kernel

theorem good15 : ∀ q ∈ orders15, Good q :=
  certs15_orders ▸ checkAll_sound certs15_ok

def certs16 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (102811,10,6,[2,3,5,23,149]),
  (102829,21,48,[2,3,11,19,41]),
  (102859,2,49,[2,3,7,31,79]),
  (102931,2,28,[2,3,5,47,73]),
  (103171,18,6,[2,3,5,19,181]),
  (103231,6,71,[2,3,5,31,37]),
  (103291,2,20,[2,3,5,11,313]),
  (103951,27,10,[2,3,5,7,11]),
  (104053,5,36,[2,3,13,23,29]),
  (104119,12,29,[2,3,7,37,67]),
  (104161,22,10,[2,3,5,7,31]),
  (104281,46,38,[2,3,5,11,79]),
  (104287,5,97,[2,3,7,13,191]),
  (104311,6,13,[2,3,5,19,61]),
  (104347,11,19,[2,3,11,17,31]),
  (104551,23,39,[2,3,5,17,41]),
  (104623,6,11,[2,3,7,47,53]),
  (104677,20,39,[2,3,11,13,61]),
  (104911,11,2,[2,3,5,13,269]),
  (105211,2,11,[2,3,5,7,167]),
  (105337,30,18,[2,3,7,11,19]),
  (105379,2,16,[2,3,7,13,193]),
  (105673,10,17,[2,3,7,17,37]),
  (105691,2,7,[2,3,5,13,271]),
  (106261,17,23,[2,3,5,7,11,23]),
  (106531,2,20,[2,3,5,53,67]),
  (106591,6,9,[2,3,5,11,17,19]),
  (106681,106,74,[2,3,5,7,127]),
  (106861,6,13,[2,3,5,13,137]),
  (107071,23,10,[2,3,5,43,83]),
  (107101,13,26,[2,3,5,7,17]),
  (107227,22,44,[2,3,7,23,37]),
  (107251,2,37,[2,3,5,11,13]),
  (107563,28,17,[2,3,7,13,197]),
  (107581,6,11,[2,3,5,11,163]),
  (107641,33,38,[2,3,5,13,23]),
  (107647,12,25,[2,3,7,11,233]),
  (107671,11,2,[2,3,5,37,97]),
  (107881,38,18,[2,3,5,29,31]),
  (107941,13,67,[2,3,5,7,257]),
  (107971,2,7,[2,3,5,59,61]),
  (108109,18,77,[2,3,7,11,13]),
  (108421,17,12,[2,3,5,13,139]),
  (108529,73,30,[2,3,7,17,19]),
  (108571,2,9,[2,3,5,7,11,47]),
  (108631,29,26,[2,3,5,17,71]),
  (108967,5,9,[2,3,11,13,127]),
  (108991,6,17,[2,3,5,7,173]),
  (109141,29,4,[2,3,5,17,107]),
  (109159,12,40,[2,3,7,23,113]),
  (109201,67,18,[2,3,5,7,13]),
  (109471,42,5,[2,3,5,41,89]),
  (109621,10,21,[2,3,5,7,29]),
  (109741,39,48,[2,3,5,31,59]),
  (109831,6,18,[2,3,5,7,523]),
  (109891,10,4,[2,3,5,11,37]),
  (110221,6,31,[2,3,5,11,167]),
  (110419,2,19,[2,3,7,11,239]),
  (110491,14,5,[2,3,5,29,127]),
  (110581,23,15,[2,3,5,19,97]),
  (110881,68,71,[2,3,5,7,11]),
  (110923,2,6,[2,3,7,19,139]),
  (111091,18,26,[2,3,5,7,23]),
  (111211,17,22,[2,3,5,11,337]),
  (111301,13,63,[2,3,5,7,53]),
  (111721,67,15,[2,3,5,7,19]),
  (111871,6,45,[2,3,5,11,113]),
  (111973,5,28,[2,3,7,31,43]),
  (112111,23,10,[2,3,5,37,101]),
  (112291,2,5,[2,3,5,19,197]),
  (112771,17,51,[2,3,5,7,179]),
  (113023,5,9,[2,3,7,13,23]),
  (113161,86,10,[2,3,5,23,41]),
  (113731,2,6,[2,3,5,17,223]),
  (113989,10,69,[2,3,7,23,59]),
  (114031,11,10,[2,3,5,7,181]),
  (114451,22,5,[2,3,5,7,109]),
  (114493,13,44,[2,3,7,29,47]),
  (114571,22,14,[2,3,5,19,67]),
  (114577,29,99,[2,3,7,11,31]),
  (114661,33,22,[2,3,5,7,13]),
  (115771,14,24,[2,3,5,17,227]),
  (115831,11,31,[2,3,5,11,13]),
  (115963,11,4,[2,3,7,11,251]),
  (116131,11,20,[2,3,5,7,79]),
  (116341,17,7,[2,3,5,7,277]),
  (116491,10,16,[2,3,5,11,353]),
  (116689,41,10,[2,3,11,13,17]),
  (116791,53,14,[2,3,5,17,229]),
  (117811,10,5,[2,3,5,7,11,17]),
  (117991,22,7,[2,3,5,19,23]),
  (118171,10,19,[2,3,5,13,101]),
  (118471,11,10,[2,3,5,11,359]),
  (118681,21,45,[2,3,5,23,43]),
  (118819,2,16,[2,3,7,23,41]),
  (118831,21,35,[2,3,5,17,233]),
  (118861,10,197,[2,3,5,7,283]),
  (118903,5,2,[2,3,7,19,149]),
  (119131,2,9,[2,3,5,11,19]),
  (119191,6,11,[2,3,5,29,137])]

def orders16 : List ℕ := [102811,102829,102859,102931,103171,103231,103291,103951,104053,104119,104161,104281,104287,104311,104347,104551,104623,104677,104911,105211,105337,105379,105673,105691,106261,106531,106591,106681,106861,107071,107101,107227,107251,107563,107581,107641,107647,107671,107881,107941,107971,108109,108421,108529,108571,108631,108967,108991,109141,109159,109201,109471,109621,109741,109831,109891,110221,110419,110491,110581,110881,110923,111091,111211,111301,111721,111871,111973,112111,112291,112771,113023,113161,113731,113989,114031,114451,114493,114571,114577,114661,115771,115831,115963,116131,116341,116491,116689,116791,117811,117991,118171,118471,118681,118819,118831,118861,118903,119131,119191]

theorem certs16_ok : checkAll certs16 = true := by decide +kernel

theorem certs16_orders : certs16.map (·.1) = orders16 := by decide +kernel

theorem good16 : ∀ q ∈ orders16, Good q :=
  certs16_orders ▸ checkAll_sound certs16_ok

def certs17 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (119311,11,7,[2,3,5,41,97]),
  (119659,2,5,[2,3,7,11,37]),
  (119701,33,28,[2,3,5,7,19]),
  (119851,2,36,[2,3,5,17,47]),
  (119971,2,5,[2,3,5,31,43]),
  (120121,37,88,[2,3,5,7,11,13]),
  (120331,2,55,[2,3,5,7,191]),
  (120511,30,16,[2,3,5,13,103]),
  (120871,22,17,[2,3,5,17,79]),
  (121171,17,39,[2,3,5,7,577]),
  (121291,10,6,[2,3,5,13,311]),
  (121441,51,15,[2,3,5,11,23]),
  (121507,2,19,[2,3,7,11,263]),
  (121591,6,40,[2,3,5,7,193]),
  (122011,2,16,[2,3,5,7,83]),
  (122131,37,31,[2,3,5,23,59]),
  (122611,11,25,[2,3,5,61,67]),
  (122761,37,6,[2,3,5,11,31]),
  (123091,10,16,[2,3,5,11,373]),
  (123397,14,21,[2,3,7,13,113]),
  (123631,14,5,[2,3,5,13,317]),
  (123817,37,11,[2,3,7,11,67]),
  (124021,17,46,[2,3,5,13,53]),
  (124231,23,22,[2,3,5,41,101]),
  (124489,87,28,[2,3,7,13,19]),
  (124951,12,36,[2,3,5,7,17]),
  (125131,2,29,[2,3,5,43,97]),
  (125371,18,36,[2,3,5,7,199]),
  (125731,10,5,[2,3,5,11,127]),
  (125791,6,13,[2,3,5,7,599]),
  (126127,6,15,[2,3,7,11,13]),
  (126211,17,11,[2,3,5,7,601]),
  (126271,23,44,[2,3,5,23,61]),
  (126421,70,28,[2,3,5,7,43]),
  (126481,28,33,[2,3,5,17,31]),
  (126541,17,5,[2,3,5,19,37]),
  (126631,12,11,[2,3,5,7,67]),
  (126691,2,7,[2,3,5,41,103]),
  (127051,17,4,[2,3,5,7,11]),
  (127261,32,101,[2,3,5,7,101]),
  (127681,78,6,[2,3,5,7,19]),
  (127711,11,20,[2,3,5,11,43]),
  (127921,21,51,[2,3,5,13,41]),
  (128311,6,16,[2,3,5,7,13,47]),
  (128341,18,33,[2,3,5,23,31]),
  (128437,5,184,[2,3,7,11,139]),
  (128521,22,30,[2,3,5,7,17]),
  (128761,43,20,[2,3,5,29,37]),
  (128941,32,23,[2,3,5,7,307]),
  (129361,52,3,[2,3,5,7,11]),
  (129631,12,5,[2,3,5,29,149]),
  (130021,21,15,[2,3,5,11,197]),
  (130201,38,17,[2,3,5,7,31]),
  (130261,6,5,[2,3,5,13,167]),
  (130411,2,6,[2,3,5,7,23]),
  (130531,10,34,[2,3,5,19,229]),
  (130621,17,20,[2,3,5,7,311]),
  (130651,2,29,[2,3,5,13,67]),
  (130981,13,3,[2,3,5,37,59]),
  (131011,11,45,[2,3,5,11,397]),
  (131041,46,14,[2,3,5,7,13]),
  (131071,51,14,[2,3,5,17,257]),
  (131101,17,55,[2,3,5,19,23]),
  (131371,2,5,[2,3,5,29,151]),
  (131431,11,26,[2,3,5,13,337]),
  (131581,23,36,[2,3,5,17,43]),
  (131671,12,33,[2,3,5,7,11,19]),
  (132241,61,7,[2,3,5,19,29]),
  (132331,10,22,[2,3,5,11,401]),
  (132511,11,31,[2,3,5,7,631]),
  (132661,17,37,[2,3,5,11,67]),
  (132721,66,30,[2,3,5,7,79]),
  (133321,41,182,[2,3,5,11,101]),
  (133351,27,26,[2,3,5,7,127]),
  (133519,6,10,[2,3,7,11,17]),
  (133981,30,91,[2,3,5,7,11,29]),
  (134161,62,49,[2,3,5,13,43]),
  (134191,6,67,[2,3,5,7,71]),
  (134851,2,28,[2,3,5,29,31]),
  (135151,22,81,[2,3,5,17,53]),
  (135241,37,46,[2,3,5,7,23]),
  (135301,22,55,[2,3,5,11,41]),
  (135661,13,29,[2,3,5,7,17,19]),
  (135721,34,75,[2,3,5,13,29]),
  (136111,29,5,[2,3,5,13,349]),
  (136501,41,4,[2,3,5,7,13]),
  (136621,66,19,[2,3,5,11,23]),
  (136711,14,29,[2,3,5,7,31]),
  (136951,11,7,[2,3,5,11,83]),
  (137131,2,5,[2,3,5,7,653]),
  (137191,12,18,[2,3,5,17,269]),
  (137341,29,12,[2,3,5,7,109]),
  (137941,6,49,[2,3,5,11,19]),
  (138139,18,13,[2,3,7,11,13,23]),
  (138181,10,48,[2,3,5,7,47]),
  (138451,2,7,[2,3,5,13,71]),
  (138841,37,18,[2,3,5,13,89]),
  (139021,17,48,[2,3,5,7,331]),
  (139591,6,9,[2,3,5,11,47]),
  (139861,10,60,[2,3,5,7,37])]

def orders17 : List ℕ := [119311,119659,119701,119851,119971,120121,120331,120511,120871,121171,121291,121441,121507,121591,122011,122131,122611,122761,123091,123397,123631,123817,124021,124231,124489,124951,125131,125371,125731,125791,126127,126211,126271,126421,126481,126541,126631,126691,127051,127261,127681,127711,127921,128311,128341,128437,128521,128761,128941,129361,129631,130021,130201,130261,130411,130531,130621,130651,130981,131011,131041,131071,131101,131371,131431,131581,131671,132241,132331,132511,132661,132721,133321,133351,133519,133981,134161,134191,134851,135151,135241,135301,135661,135721,136111,136501,136621,136711,136951,137131,137191,137341,137941,138139,138181,138451,138841,139021,139591,139861]

theorem certs17_ok : checkAll certs17 = true := by decide +kernel

theorem certs17_orders : certs17.map (·.1) = orders17 := by decide +kernel

theorem good17 : ∀ q ∈ orders17, Good q :=
  certs17_orders ▸ checkAll_sound certs17_ok

def certs18 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (139921,13,30,[2,3,5,11,53]),
  (140071,59,17,[2,3,5,7,23,29]),
  (140221,17,36,[2,3,5,19,41]),
  (140281,51,61,[2,3,5,7,167]),
  (140449,82,5,[2,3,7,11,19]),
  (140761,42,18,[2,3,5,17,23]),
  (141181,10,37,[2,3,5,13,181]),
  (141241,57,18,[2,3,5,11,107]),
  (141961,33,142,[2,3,5,7,13]),
  (142231,12,41,[2,3,5,11,431]),
  (142381,13,4,[2,3,5,7,113]),
  (142591,11,38,[2,3,5,7,97]),
  (143551,6,29,[2,3,5,11,29]),
  (143881,41,2,[2,3,5,11,109]),
  (144271,14,57,[2,3,5,7,229]),
  (144481,87,18,[2,3,5,7,43]),
  (144541,6,3,[2,3,5,11,73]),
  (145531,10,29,[2,3,5,7,11]),
  (145861,30,15,[2,3,5,11,13,17]),
  (146161,51,48,[2,3,5,7,29]),
  (146191,11,17,[2,3,5,11,443]),
  (146521,38,3,[2,3,5,11,37]),
  (146581,18,12,[2,3,5,7,349]),
  (147031,11,18,[2,3,5,13,29]),
  (147211,2,17,[2,3,5,7,701]),
  (148201,61,76,[2,3,5,13,19]),
  (148471,22,61,[2,3,5,7,101]),
  (148891,2,9,[2,3,5,7,709]),
  (149101,10,66,[2,3,5,7,71]),
  (149161,34,50,[2,3,5,11,113]),
  (149521,52,35,[2,3,5,7,89]),
  (149731,17,5,[2,3,5,7,23,31]),
  (150151,11,25,[2,3,5,7,11,13]),
  (150571,10,5,[2,3,5,7,239]),
  (150991,14,9,[2,3,5,7,719]),
  (151471,22,4,[2,3,5,11,17]),
  (152041,33,106,[2,3,5,7,181]),
  (152461,17,28,[2,3,5,7,11]),
  (152671,6,16,[2,3,5,7,727]),
  (153511,6,44,[2,3,5,7,17,43]),
  (154981,10,48,[2,3,5,7,41]),
  (155191,6,5,[2,3,5,7,739]),
  (155821,10,20,[2,3,5,7,53]),
  (156241,43,92,[2,3,5,7,31]),
  (157081,58,2,[2,3,5,7,11,17]),
  (157291,17,47,[2,3,5,7,107]),
  (158341,50,3,[2,3,5,7,13,29]),
  (158551,6,18,[2,3,5,7,151]),
  (158731,10,49,[2,3,5,11,13,37]),
  (159811,10,23,[2,3,5,7,761]),
  (160231,13,33,[2,3,5,7,109]),
  (160441,33,12,[2,3,5,7,191]),
  (160651,2,16,[2,3,5,7,17]),
  (160861,10,105,[2,3,5,7,383]),
  (161071,27,31,[2,3,5,7,13,59]),
  (161911,6,25,[2,3,5,7,257]),
  (162691,27,31,[2,3,5,11,17,29]),
  (162751,6,5,[2,3,5,7,31]),
  (163021,21,36,[2,3,5,11,13,19]),
  (163171,2,16,[2,3,5,7,37]),
  (164011,10,34,[2,3,5,7,11,71]),
  (164431,11,42,[2,3,5,7,29]),
  (165901,13,3,[2,3,5,7,79]),
  (167311,28,5,[2,3,5,11,13]),
  (168211,18,25,[2,3,5,7,89]),
  (168631,6,18,[2,3,5,7,11,73]),
  (171571,10,31,[2,3,5,7,19,43]),
  (174721,33,70,[2,3,5,7,13]),
  (174931,27,4,[2,3,5,7,17]),
  (175891,2,5,[2,3,5,11,13,41]),
  (176611,18,94,[2,3,5,7,29]),
  (178501,13,36,[2,3,5,7,17]),
  (180181,22,39,[2,3,5,7,11,13]),
  (185641,93,34,[2,3,5,7,13,17]),
  (186187,11,16,[2,3,7,11,13,31]),
  (187111,6,19,[2,3,5,7,11]),
  (187531,2,5,[2,3,5,7,19,47]),
  (188791,6,16,[2,3,5,7,29,31]),
  (189421,18,23,[2,3,5,7,11,41]),
  (192271,56,10,[2,3,5,13,17,29]),
  (194371,10,16,[2,3,5,11,19,31]),
  (197341,17,117,[2,3,5,11,13,23]),
  (198031,6,21,[2,3,5,7,23,41]),
  (200971,10,6,[2,3,5,7,11,29]),
  (202021,32,3,[2,3,5,7,13,37]),
  (207061,18,4,[2,3,5,7,17,29]),
  (207481,73,26,[2,3,5,7,13,19]),
  (210631,11,46,[2,3,5,7,17,59]),
  (213181,21,44,[2,3,5,11,17,19]),
  (214831,11,10,[2,3,5,7,11,31]),
  (214891,17,5,[2,3,5,13,19,29]),
  (217771,10,24,[2,3,5,7,17,61]),
  (219451,2,6,[2,3,5,7,11,19]),
  (224071,14,10,[2,3,5,7,11,97]),
  (227011,2,31,[2,3,5,7,23,47]),
  (227371,10,5,[2,3,5,11,13,53]),
  (229711,11,16,[2,3,5,13,19,31]),
  (232051,2,17,[2,3,5,7,13,17]),
  (234781,17,31,[2,3,5,7,13,43]),
  (235621,30,197,[2,3,5,7,11,17])]

def orders18 : List ℕ := [139921,140071,140221,140281,140449,140761,141181,141241,141961,142231,142381,142591,143551,143881,144271,144481,144541,145531,145861,146161,146191,146521,146581,147031,147211,148201,148471,148891,149101,149161,149521,149731,150151,150571,150991,151471,152041,152461,152671,153511,154981,155191,155821,156241,157081,157291,158341,158551,158731,159811,160231,160441,160651,160861,161071,161911,162691,162751,163021,163171,164011,164431,165901,167311,168211,168631,171571,174721,174931,175891,176611,178501,180181,185641,186187,187111,187531,188791,189421,192271,194371,197341,198031,200971,202021,207061,207481,210631,213181,214831,214891,217771,219451,224071,227011,227371,229711,232051,234781,235621]

theorem certs18_ok : checkAll certs18 = true := by decide +kernel

theorem certs18_orders : certs18.map (·.1) = orders18 := by decide +kernel

theorem good18 : ∀ q ∈ orders18, Good q :=
  certs18_orders ▸ checkAll_sound certs18_ok

def certs19 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (242971,2,21,[2,3,5,7,13,89]),
  (243391,13,9,[2,3,5,7,19,61]),
  (244861,17,74,[2,3,5,7,11,53]),
  (246247,10,25,[2,3,7,11,13,41]),
  (247381,29,7,[2,3,5,7,19,31]),
  (248821,22,75,[2,3,5,11,13,29]),
  (251791,12,16,[2,3,5,7,11,109]),
  (251941,10,31,[2,3,5,13,17,19]),
  (258061,6,11,[2,3,5,11,17,23]),
  (261031,11,2,[2,3,5,7,11,113]),
  (264811,2,36,[2,3,5,7,13,97]),
  (267961,51,31,[2,3,5,7,11,29]),
  (269179,2,5,[2,3,7,13,17,29]),
  (270271,6,42,[2,3,5,7,11,13]),
  (272581,29,23,[2,3,5,7,11,59]),
  (274171,18,29,[2,3,5,13,19,37]),
  (276277,14,63,[2,3,7,11,13,23]),
  (278071,23,5,[2,3,5,13,23,31]),
  (281191,6,19,[2,3,5,7,13,103]),
  (284131,10,6,[2,3,5,7,11,41]),
  (285091,2,21,[2,3,5,13,17,43]),
  (289381,29,58,[2,3,5,7,13,53]),
  (291271,14,83,[2,3,5,7,19,73]),
  (291721,28,40,[2,3,5,11,13,17]),
  (296011,11,19,[2,3,5,11,13,23]),
  (297991,14,4,[2,3,5,7,11,43]),
  (300301,40,189,[2,3,5,7,11,13]),
  (304981,6,41,[2,3,5,13,17,23]),
  (305971,2,16,[2,3,5,7,31,47]),
  (308491,18,47,[2,3,5,7,13,113]),
  (309541,17,44,[2,3,5,7,11,67]),
  (310591,6,45,[2,3,5,7,17,29]),
  (314161,158,5,[2,3,5,7,11,17]),
  (316471,27,13,[2,3,5,7,11,137]),
  (316681,33,28,[2,3,5,7,13,29]),
  (317731,2,46,[2,3,5,7,17,89]),
  (318319,6,42,[2,3,7,11,13,53]),
  (318781,17,21,[2,3,5,7,11,23]),
  (321091,2,49,[2,3,5,7,11,139]),
  (322771,2,6,[2,3,5,7,29,53]),
  (324871,6,26,[2,3,5,7,13,17]),
  (330331,11,54,[2,3,5,7,11,13]),
  (331171,10,6,[2,3,5,7,19,83]),
  (332011,11,54,[2,3,5,7,17,31]),
  (336491,10,5,[2,5,7,11,19,23]),
  (337261,37,4,[2,3,5,7,11,73]),
  (339151,6,47,[2,3,5,7,17,19]),
  (342211,2,19,[2,3,5,11,17,61]),
  (342343,10,21,[2,3,7,11,13,19]),
  (343141,32,12,[2,3,5,7,19,43]),
  (346711,14,4,[2,3,5,7,13,127]),
  (347131,10,21,[2,3,5,7,19,29]),
  (347821,6,29,[2,3,5,11,17,31]),
  (348811,10,31,[2,3,5,7,11,151]),
  (351121,67,14,[2,3,5,7,11,19]),
  (351391,29,14,[2,3,5,13,17,53]),
  (354091,2,9,[2,3,5,11,29,37]),
  (355111,11,31,[2,3,5,7,19,89]),
  (355811,7,4,[2,5,7,13,17,23]),
  (356731,2,9,[2,3,5,11,23,47]),
  (357421,18,12,[2,3,5,7,23,37]),
  (358051,2,14,[2,3,5,7,11,31]),
  (358531,2,9,[2,3,5,17,19,37]),
  (359311,6,13,[2,3,5,7,29,59]),
  (364183,6,9,[2,3,7,13,23,29]),
  (367711,12,9,[2,3,5,7,17,103]),
  (367771,2,9,[2,3,5,13,23,41]),
  (371071,27,41,[2,3,5,7,19,31]),
  (371281,82,14,[2,3,5,7,13,17]),
  (371491,2,11,[2,3,5,7,29,61]),
  (373231,11,7,[2,3,5,11,13,29]),
  (376531,11,52,[2,3,5,7,11,163]),
  (377581,10,5,[2,3,5,7,29,31]),
  (377911,6,43,[2,3,5,13,17,19]),
  (380563,31,21,[2,3,7,13,17,41]),
  (381991,14,21,[2,3,5,7,17,107]),
  (383839,14,17,[2,3,7,13,19,37]),
  (385771,11,25,[2,3,5,7,11,167]),
  (387031,6,2,[2,3,5,7,19,97]),
  (389299,10,21,[2,3,7,13,23,31]),
  (390391,14,13,[2,3,5,7,11,13]),
  (395851,2,9,[2,3,5,7,13,29]),
  (396061,37,52,[2,3,5,7,23,41]),
  (398311,11,34,[2,3,5,11,17,71]),
  (398581,10,13,[2,3,5,7,13,73]),
  (402403,11,4,[2,3,7,11,13,67]),
  (402991,6,18,[2,3,5,7,19,101]),
  (403261,6,23,[2,3,5,11,13,47]),
  (404431,30,46,[2,3,5,13,17,61]),
  (404671,6,105,[2,3,5,7,41,47]),
  (406981,40,7,[2,3,5,7,17,19]),
  (410411,7,4,[2,5,7,11,13,41]),
  (410551,6,5,[2,3,5,7,17,23]),
  (412567,6,15,[2,3,7,11,19,47]),
  (415141,6,46,[2,3,5,11,17,37]),
  (415381,10,20,[2,3,5,7,23,43]),
  (416263,5,9,[2,3,7,11,17,53]),
  (417691,41,19,[2,3,5,7,13,17]),
  (418471,6,16,[2,3,5,13,29,37]),
  (420421,17,20,[2,3,5,7,11,13])]

def orders19 : List ℕ := [242971,243391,244861,246247,247381,248821,251791,251941,258061,261031,264811,267961,269179,270271,272581,274171,276277,278071,281191,284131,285091,289381,291271,291721,296011,297991,300301,304981,305971,308491,309541,310591,314161,316471,316681,317731,318319,318781,321091,322771,324871,330331,331171,332011,336491,337261,339151,342211,342343,343141,346711,347131,347821,348811,351121,351391,354091,355111,355811,356731,357421,358051,358531,359311,364183,367711,367771,371071,371281,371491,373231,376531,377581,377911,380563,381991,383839,385771,387031,389299,390391,395851,396061,398311,398581,402403,402991,403261,404431,404671,406981,410411,410551,412567,415141,415381,416263,417691,418471,420421]

theorem certs19_ok : checkAll certs19 = true := by decide +kernel

theorem certs19_orders : certs19.map (·.1) = orders19 := by decide +kernel

theorem good19 : ∀ q ∈ orders19, Good q :=
  certs19_orders ▸ checkAll_sound certs19_ok

def certs20 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (424271,21,9,[2,5,7,11,19,29]),
  (426427,2,31,[2,3,7,11,13,71]),
  (426931,32,51,[2,3,5,7,19,107]),
  (426973,5,63,[2,3,7,13,17,23]),
  (427351,6,58,[2,3,5,7,11,37]),
  (429661,13,36,[2,3,5,7,11,31]),
  (432391,6,2,[2,3,5,7,29,71]),
  (432631,21,5,[2,3,5,11,19,23]),
  (433291,38,5,[2,3,5,11,13,101]),
  (434011,12,17,[2,3,5,17,23,37]),
  (435541,10,22,[2,3,5,7,17,61]),
  (436171,2,25,[2,3,5,7,31,67]),
  (437191,38,17,[2,3,5,13,19,59]),
  (438439,14,4,[2,3,7,11,13,73]),
  (439891,10,52,[2,3,5,11,31,43]),
  (440221,6,26,[2,3,5,11,23,29]),
  (445741,32,65,[2,3,5,17,19,23]),
  (447331,2,42,[2,3,5,13,31,37]),
  (448141,13,99,[2,3,5,7,11,97]),
  (450451,11,23,[2,3,5,7,11,13]),
  (453181,50,21,[2,3,5,7,13,83]),
  (454021,30,35,[2,3,5,7,23,47]),
  (455431,6,59,[2,3,5,17,19,47]),
  (456457,46,83,[2,3,7,11,13,19]),
  (457711,14,31,[2,3,5,11,19,73]),
  (459031,11,45,[2,3,5,11,13,107]),
  (459421,10,118,[2,3,5,13,19,31]),
  (459691,2,9,[2,3,5,7,11,199]),
  (460531,2,86,[2,3,5,7,17,43]),
  (462841,73,48,[2,3,5,7,19,29]),
  (463387,12,17,[2,3,7,11,17,59]),
  (463711,38,5,[2,3,5,13,29,41]),
  (464311,11,46,[2,3,5,7,11,67]),
  (464647,5,18,[2,3,7,13,23,37]),
  (465631,21,17,[2,3,5,11,17,83]),
  (467611,2,20,[2,3,5,11,13,109]),
  (467671,6,26,[2,3,5,7,17,131]),
  (469561,37,28,[2,3,5,7,13,43]),
  (470731,18,31,[2,3,5,13,17,71]),
  (471241,46,12,[2,3,5,7,11,17]),
  (473971,10,34,[2,3,5,7,37,61]),
  (474811,2,9,[2,3,5,7,17,19]),
  (478171,2,5,[2,3,5,7,11,23]),
  (483211,10,53,[2,3,5,7,13,59]),
  (483991,6,45,[2,3,5,13,17,73]),
  (485941,66,11,[2,3,5,7,13,89]),
  (486331,14,34,[2,3,5,13,29,43]),
  (486781,72,7,[2,3,5,7,19,61]),
  (486949,13,3,[2,3,7,11,17,31]),
  (487831,12,18,[2,3,5,7,23,101]),
  (489061,46,92,[2,3,5,11,13,19]),
  (490771,12,20,[2,3,5,7,19,41]),
  (493351,21,16,[2,3,5,11,13,23]),
  (494341,57,13,[2,3,5,7,11,107]),
  (494761,78,37,[2,3,5,7,19,31]),
  (496231,6,5,[2,3,5,7,17,139]),
  (496471,33,18,[2,3,5,13,19,67]),
  (497491,12,22,[2,3,5,7,23,103]),
  (499423,6,49,[2,3,7,11,23,47]),
  (499591,6,9,[2,3,5,7,13,61]),
  (501271,11,5,[2,3,5,7,11,31]),
  (502321,57,15,[2,3,5,7,13,23]),
  (505051,27,52,[2,3,5,7,13,37]),
  (506731,11,20,[2,3,5,7,19,127]),
  (506941,10,26,[2,3,5,7,17,71]),
  (507781,10,46,[2,3,5,7,13,31]),
  (508531,2,33,[2,3,5,11,23,67]),
  (512821,41,60,[2,3,5,7,11,37]),
  (514711,12,45,[2,3,5,7,19,43]),
  (516517,14,37,[2,3,7,11,13,43]),
  (516811,2,9,[2,3,5,7,23,107]),
  (520411,2,7,[2,3,5,11,19,83]),
  (522061,30,37,[2,3,5,7,11,113]),
  (522523,2,9,[2,3,7,11,13,29]),
  (523741,37,59,[2,3,5,7,29,43]),
  (523771,2,9,[2,3,5,13,17,79]),
  (526681,58,71,[2,3,5,7,11,19]),
  (527671,6,10,[2,3,5,11,13,41]),
  (528991,13,4,[2,3,5,7,11,229]),
  (531571,2,7,[2,3,5,13,29,47]),
  (532267,18,29,[2,3,7,19,23,29]),
  (532771,33,24,[2,3,5,7,43,59]),
  (532951,38,13,[2,3,5,11,17,19]),
  (533821,23,5,[2,3,5,7,31,41]),
  (534661,10,5,[2,3,5,7,19,67]),
  (537811,18,25,[2,3,5,7,13,197]),
  (538357,5,48,[2,3,7,13,17,29]),
  (540541,18,204,[2,3,5,7,11,13]),
  (541927,6,32,[2,3,7,11,17,23]),
  (543661,10,31,[2,3,5,13,17,41]),
  (544171,14,5,[2,3,5,11,17,97]),
  (545161,38,6,[2,3,5,7,11,59]),
  (545791,6,16,[2,3,5,7,23,113]),
  (546631,12,17,[2,3,5,7,19,137]),
  (547171,2,47,[2,3,5,13,23,61]),
  (547471,6,71,[2,3,5,7,11,79]),
  (547639,14,2,[2,3,7,13,17,59]),
  (549319,6,13,[2,3,7,11,29,41]),
  (550621,29,33,[2,3,5,7,19,23]),
  (550831,12,9,[2,3,5,7,43,61])]

def orders20 : List ℕ := [424271,426427,426931,426973,427351,429661,432391,432631,433291,434011,435541,436171,437191,438439,439891,440221,445741,447331,448141,450451,453181,454021,455431,456457,457711,459031,459421,459691,460531,462841,463387,463711,464311,464647,465631,467611,467671,469561,470731,471241,473971,474811,478171,483211,483991,485941,486331,486781,486949,487831,489061,490771,493351,494341,494761,496231,496471,497491,499423,499591,501271,502321,505051,506731,506941,507781,508531,512821,514711,516517,516811,520411,522061,522523,523741,523771,526681,527671,528991,531571,532267,532771,532951,533821,534661,537811,538357,540541,541927,543661,544171,545161,545791,546631,547171,547471,547639,549319,550621,550831]

theorem certs20_ok : checkAll certs20 = true := by decide +kernel

theorem certs20_orders : certs20.map (·.1) = orders20 := by decide +kernel

theorem good20 : ∀ q ∈ orders20, Good q :=
  certs20_orders ▸ checkAll_sound certs20_ok

def certs21 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (551311,12,5,[2,3,5,17,23,47]),
  (551461,37,21,[2,3,5,7,13,101]),
  (551671,6,25,[2,3,5,7,37,71]),
  (552091,2,81,[2,3,5,7,11,239]),
  (552553,19,34,[2,3,7,11,13,23]),
  (553351,6,5,[2,3,5,7,17,31]),
  (553411,2,9,[2,3,5,11,13,43]),
  (554269,22,12,[2,3,11,13,17,19]),
  (554611,27,16,[2,3,5,7,19,139]),
  (560281,51,31,[2,3,5,7,23,29]),
  (560491,2,17,[2,3,5,7,17,157]),
  (562021,21,126,[2,3,5,17,19,29]),
  (562591,6,51,[2,3,5,7,19,47]),
  (564061,18,39,[2,3,5,7,17,79]),
  (565111,27,5,[2,3,5,7,13,23]),
  (567631,27,2,[2,3,5,7,17,53]),
  (568231,22,28,[2,3,5,13,31,47]),
  (570181,6,43,[2,3,5,13,17,43]),
  (572461,23,35,[2,3,5,7,29,47]),
  (572881,57,43,[2,3,5,7,11,31]),
  (573343,5,32,[2,3,7,11,17,73]),
  (573871,6,73,[2,3,5,11,37,47]),
  (576031,14,23,[2,3,5,7,13,211]),
  (577831,6,19,[2,3,5,11,17,103]),
  (581197,5,33,[2,3,7,11,17,37]),
  (581491,27,4,[2,3,5,7,13,71]),
  (582541,22,21,[2,3,5,7,19,73]),
  (584971,22,19,[2,3,5,17,31,37]),
  (585391,14,33,[2,3,5,13,19,79]),
  (586741,18,116,[2,3,5,7,11,127]),
  (586951,14,36,[2,3,5,7,13,43]),
  (587731,2,5,[2,3,5,11,13,137]),
  (590071,11,7,[2,3,5,13,17,89]),
  (591091,2,9,[2,3,5,17,19,61]),
  (592621,10,43,[2,3,5,7,17,83]),
  (594091,11,43,[2,3,5,7,23,41]),
  (594511,6,2,[2,3,5,7,19,149]),
  (595141,17,39,[2,3,5,7,13,109]),
  (595981,17,41,[2,3,5,7,11,43]),
  (599611,2,9,[2,3,5,11,23,79]),
  (600601,58,55,[2,3,5,7,11,13]),
  (605221,18,36,[2,3,5,7,11,131]),
  (606607,5,18,[2,3,7,11,13,101]),
  (607531,12,5,[2,3,5,7,11,263]),
  (608191,11,2,[2,3,5,11,19,97]),
  (612613,5,28,[2,3,7,11,13,17]),
  (614041,22,3,[2,3,5,7,17,43]),
  (615031,6,49,[2,3,5,13,19,83]),
  (616171,2,7,[2,3,5,19,23,47]),
  (618619,11,33,[2,3,7,11,13,103]),
  (619711,6,23,[2,3,5,7,13,227]),
  (620311,41,4,[2,3,5,23,29,31]),
  (620491,2,19,[2,3,5,13,37,43]),
  (622051,10,7,[2,3,5,11,13,29]),
  (623071,6,21,[2,3,5,7,23,43]),
  (623221,42,15,[2,3,5,13,17,47]),
  (624031,6,69,[2,3,5,11,31,61]),
  (625171,2,14,[2,3,5,7,13,229]),
  (626011,17,13,[2,3,5,7,11,271]),
  (626341,17,20,[2,3,5,11,13,73]),
  (627271,14,9,[2,3,5,7,29,103]),
  (627901,10,4,[2,3,5,7,13,23]),
  (631471,11,20,[2,3,5,7,31,97]),
  (632941,40,100,[2,3,5,7,11,137]),
  (633271,6,2,[2,3,5,11,19,101]),
  (633931,2,5,[2,3,5,11,17,113]),
  (635461,39,36,[2,3,5,7,17,89]),
  (639211,11,28,[2,3,5,11,13,149]),
  (640771,14,24,[2,3,5,13,31,53]),
  (641131,17,14,[2,3,5,7,43,71]),
  (641551,6,21,[2,3,5,7,13,47]),
  (644491,2,5,[2,3,5,7,11,31]),
  (644671,41,5,[2,3,5,13,19,29]),
  (644911,12,9,[2,3,5,7,37,83]),
  (647011,27,5,[2,3,5,7,13,79]),
  (647131,10,6,[2,3,5,11,37,53]),
  (650761,42,33,[2,3,5,11,17,29]),
  (652081,41,141,[2,3,5,11,13,19]),
  (652741,6,36,[2,3,5,11,23,43]),
  (653311,6,29,[2,3,5,7,17,61]),
  (656371,11,14,[2,3,5,11,13,17]),
  (656671,11,51,[2,3,5,7,53,59]),
  (657931,59,6,[2,3,5,7,13,241]),
  (658351,6,34,[2,3,5,7,11,19]),
  (660661,18,63,[2,3,5,7,11,13]),
  (664621,6,115,[2,3,5,11,19,53]),
  (668221,18,78,[2,3,5,7,37,43]),
  (668611,2,5,[2,3,5,17,19,23]),
  (669901,30,17,[2,3,5,7,11,29]),
  (671161,92,10,[2,3,5,7,17,47]),
  (671581,46,4,[2,3,5,7,13,41]),
  (675511,6,25,[2,3,5,11,23,89]),
  (677041,73,18,[2,3,5,7,13,31]),
  (681451,11,14,[2,3,5,7,11,59]),
  (685231,14,4,[2,3,5,7,13,251]),
  (689131,10,4,[2,3,5,13,19,31]),
  (690271,6,5,[2,3,5,7,19,173]),
  (691531,11,37,[2,3,5,7,37,89]),
  (692581,18,3,[2,3,5,7,17,97]),
  (693421,66,19,[2,3,5,7,13,127])]

def orders21 : List ℕ := [551311,551461,551671,552091,552553,553351,553411,554269,554611,560281,560491,562021,562591,564061,565111,567631,568231,570181,572461,572881,573343,573871,576031,577831,581197,581491,582541,584971,585391,586741,586951,587731,590071,591091,592621,594091,594511,595141,595981,599611,600601,605221,606607,607531,608191,612613,614041,615031,616171,618619,619711,620311,620491,622051,623071,623221,624031,625171,626011,626341,627271,627901,631471,632941,633271,633931,635461,639211,640771,641131,641551,644491,644671,644911,647011,647131,650761,652081,652741,653311,656371,656671,657931,658351,660661,664621,668221,668611,669901,671161,671581,675511,677041,681451,685231,689131,690271,691531,692581,693421]

theorem certs21_ok : checkAll certs21 = true := by decide +kernel

theorem certs21_orders : certs21.map (·.1) = orders21 := by decide +kernel

theorem good21 : ∀ q ∈ orders21, Good q :=
  certs21_orders ▸ checkAll_sound certs21_ok

def certs22 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (694261,33,68,[2,3,5,7,19,29]),
  (695641,57,46,[2,3,5,11,17,31]),
  (699271,11,41,[2,3,5,11,13,163]),
  (699931,2,5,[2,3,5,7,11,101]),
  (701611,10,5,[2,3,5,7,13,257]),
  (703561,37,82,[2,3,5,11,13,41]),
  (704551,27,2,[2,3,5,7,11,61]),
  (705181,18,13,[2,3,5,7,23,73]),
  (705871,47,4,[2,3,5,11,23,31]),
  (707071,6,13,[2,3,5,7,13,37]),
  (710221,10,28,[2,3,5,7,19,89]),
  (712531,27,53,[2,3,5,7,13,29]),
  (714841,178,28,[2,3,5,7,23,37]),
  (718411,10,22,[2,3,5,7,11,311]),
  (718621,17,31,[2,3,5,7,29,59]),
  (719671,14,4,[2,3,5,7,23,149]),
  (721051,11,26,[2,3,5,11,19,23]),
  (721141,22,46,[2,3,5,7,17,101]),
  (722611,2,14,[2,3,5,7,31,37]),
  (723031,22,16,[2,3,5,7,11,313]),
  (723451,11,17,[2,3,5,7,13,53]),
  (725341,13,84,[2,3,5,7,11,157]),
  (726181,37,55,[2,3,5,7,13,19]),
  (728911,70,2,[2,3,5,7,13,89]),
  (729301,6,49,[2,3,5,11,13,17]),
  (729331,2,87,[2,3,5,7,23,151]),
  (731851,27,6,[2,3,5,7,17,41]),
  (732271,6,34,[2,3,5,7,11,317]),
  (733591,11,16,[2,3,5,11,13,19]),
  (735421,22,37,[2,3,5,7,17,103]),
  (738151,13,16,[2,3,5,7,19,37]),
  (740461,10,45,[2,3,5,7,41,43]),
  (742981,33,12,[2,3,5,7,29,61]),
  (748021,10,38,[2,3,5,7,13,137]),
  (750121,52,71,[2,3,5,7,19,47]),
  (755371,10,25,[2,3,5,7,11,109]),
  (758941,23,66,[2,3,5,7,13,139]),
  (760411,10,19,[2,3,5,7,17,71]),
  (761671,11,18,[2,3,5,7,13,31]),
  (763141,39,15,[2,3,5,7,23,79]),
  (764611,2,17,[2,3,5,7,11,331]),
  (767131,39,30,[2,3,5,7,13,281]),
  (767551,6,16,[2,3,5,7,17,43]),
  (769231,11,25,[2,3,5,7,11,37]),
  (772591,6,23,[2,3,5,7,13,283]),
  (774691,2,5,[2,3,5,7,17,31]),
  (778051,2,86,[2,3,5,7,13,19]),
  (787711,13,43,[2,3,5,7,11,31]),
  (788971,22,14,[2,3,5,7,13,17]),
  (790021,17,76,[2,3,5,7,11,19]),
  (794641,101,2,[2,3,5,7,11,43]),
  (796951,11,68,[2,3,5,7,11,23]),
  (797161,142,15,[2,3,5,7,13,73]),
  (799891,10,4,[2,3,5,7,13,293]),
  (801571,2,5,[2,3,5,7,11,347]),
  (802231,21,2,[2,3,5,11,13,17]),
  (808081,22,72,[2,3,5,7,13,37]),
  (813961,58,11,[2,3,5,7,17,19]),
  (815431,6,5,[2,3,5,7,11,353]),
  (816271,6,47,[2,3,5,7,13,23]),
  (820051,11,41,[2,3,5,7,11,71]),
  (821101,33,20,[2,3,5,7,17,23]),
  (822361,57,54,[2,3,5,7,11,89]),
  (824671,11,21,[2,3,5,7,11,17]),
  (840841,46,26,[2,3,5,7,11,13]),
  (850081,52,84,[2,3,5,7,11,23]),
  (852391,12,41,[2,3,5,7,11,41]),
  (857011,11,6,[2,3,5,7,11,53]),
  (859321,51,56,[2,3,5,7,11,31]),
  (870871,14,137,[2,3,5,7,11,13,29]),
  (903211,27,126,[2,3,5,7,11,17,23]),
  (930931,43,46,[2,3,5,7,11,13,31]),
  (960961,92,75,[2,3,5,7,11,13]),
  (1138831,11,16,[2,3,5,7,11,17,29]),
  (1193011,22,16,[2,3,5,7,13,19,23]),
  (1231231,14,10,[2,3,5,7,11,13,41]),
  (1272811,2,31,[2,3,5,7,11,19,29]),
  (1360591,12,25,[2,3,5,7,11,19,31]),
  (1381381,89,245,[2,3,5,7,11,13,23]),
  (1411411,2,134,[2,3,5,7,11,13,47]),
  (1452991,6,16,[2,3,5,7,11,17,37]),
  (1492261,22,21,[2,3,5,7,11,17,19]),
  (1504231,22,157,[2,3,5,7,13,19,29]),
  (1623931,28,20,[2,3,5,7,11,19,37]),
  (1647031,11,5,[2,3,5,7,11,23,31]),
  (1741741,42,67,[2,3,5,7,11,13,29]),
  (1806421,29,85,[2,3,5,7,11,17,23]),
  (1831831,14,13,[2,3,5,7,11,13,61]),
  (1861861,23,108,[2,3,5,7,11,13,31]),
  (1939939,10,4,[2,3,7,11,13,17,19]),
  (1967071,12,16,[2,3,5,7,17,19,29]),
  (2012011,10,83,[2,3,5,7,11,13,67]),
  (2081311,14,9,[2,3,5,7,11,17,53]),
  (2114971,14,82,[2,3,5,11,13,17,29]),
  (2134861,29,39,[2,3,5,7,13,17,23]),
  (2181271,43,2,[2,3,5,7,13,17,47]),
  (2230411,2,9,[2,3,5,7,13,19,43]),
  (2238391,6,18,[2,3,5,7,11,17,19]),
  (2277661,23,15,[2,3,5,7,11,17,29]),
  (2282281,68,26,[2,3,5,7,11,13,19])]

def orders22 : List ℕ := [694261,695641,699271,699931,701611,703561,704551,705181,705871,707071,710221,712531,714841,718411,718621,719671,721051,721141,722611,723031,723451,725341,726181,728911,729301,729331,731851,732271,733591,735421,738151,740461,742981,748021,750121,755371,758941,760411,761671,763141,764611,767131,767551,769231,772591,774691,778051,787711,788971,790021,794641,796951,797161,799891,801571,802231,808081,813961,815431,816271,820051,821101,822361,824671,840841,850081,852391,857011,859321,870871,903211,930931,960961,1138831,1193011,1231231,1272811,1360591,1381381,1411411,1452991,1492261,1504231,1623931,1647031,1741741,1806421,1831831,1861861,1939939,1967071,2012011,2081311,2114971,2134861,2181271,2230411,2238391,2277661,2282281]

theorem certs22_ok : checkAll certs22 = true := by decide +kernel

theorem certs22_orders : certs22.map (·.1) = orders22 := by decide +kernel

theorem good22 : ∀ q ∈ orders22, Good q :=
  certs22_orders ▸ checkAll_sound certs22_ok

def certs23 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (2323231,14,36,[2,3,5,7,13,23,37]),
  (2348347,2,9,[2,3,7,11,13,17,23]),
  (2372371,11,30,[2,3,5,7,11,13,79]),
  (2381191,12,45,[2,3,5,7,17,23,29]),
  (2437891,10,6,[2,3,5,7,13,19,47]),
  (2459731,2,29,[2,3,5,7,13,17,53]),
  (2478631,14,25,[2,3,5,7,11,29,37]),
  (2574391,75,52,[2,3,5,7,13,23,41]),
  (2582581,37,76,[2,3,5,7,11,13,43]),
  (2624623,5,57,[2,3,7,11,13,19,23]),
  (2631091,10,5,[2,3,5,7,11,17,67]),
  (2645371,11,6,[2,3,5,7,13,17,19]),
  (2661331,2,9,[2,3,5,7,19,23,29]),
  (2672671,6,10,[2,3,5,7,11,13,89]),
  (2677291,28,70,[2,3,5,7,11,19,61]),
  (2691781,57,15,[2,3,5,7,13,17,29]),
  (2699971,2,16,[2,3,5,7,13,23,43]),
  (2738191,6,34,[2,3,5,7,13,17,59]),
  (2762761,122,6,[2,3,5,7,11,13,23]),
  (2771341,6,49,[2,3,5,11,13,17,19]),
  (2831011,27,13,[2,3,5,7,13,17,61]),
  (2866711,11,46,[2,3,5,7,11,17,73]),
  (2897311,6,21,[2,3,5,13,17,19,23]),
  (2916691,2,9,[2,3,5,7,17,19,43]),
  (2940631,11,2,[2,3,5,7,11,19,67]),
  (2984521,86,138,[2,3,5,7,11,17,19]),
  (2990131,2,31,[2,3,5,11,13,17,41]),
  (3038071,6,18,[2,3,5,7,17,23,37]),
  (3091111,6,5,[2,3,5,11,17,19,29]),
  (3102331,12,21,[2,3,5,7,11,17,79]),
  (3109471,6,16,[2,3,5,7,13,17,67]),
  (3131311,69,41,[2,3,5,7,13,31,37]),
  (3134671,11,39,[2,3,5,7,11,23,59]),
  (3164071,11,47,[2,3,5,7,13,19,61]),
  (3209431,14,4,[2,3,5,7,17,29,31]),
  (3245971,11,85,[2,3,5,7,13,29,41]),
  (3295111,23,44,[2,3,5,7,13,17,71]),
  (3304291,11,16,[2,3,5,11,17,19,31]),
  (3327871,27,17,[2,3,5,7,13,23,53]),
  (3333331,2,21,[2,3,5,7,11,13,37]),
  (3354781,18,62,[2,3,5,11,13,17,23]),
  (3365671,6,26,[2,3,5,7,11,31,47]),
  (3366511,6,5,[2,3,5,7,17,23,41]),
  (3377221,61,41,[2,3,5,7,11,17,43]),
  (3387931,39,14,[2,3,5,7,13,17,73]),
  (3404311,14,31,[2,3,5,7,13,29,43]),
  (3453451,2,36,[2,3,5,7,11,13,23]),
  (3483481,93,7,[2,3,5,7,11,13,29]),
  (3530731,22,25,[2,3,5,7,17,23,43]),
  (3550471,43,68,[2,3,5,7,11,29,53]),
  (3559711,6,16,[2,3,5,7,11,23,67]),
  (3598981,70,3,[2,3,5,7,11,19,41]),
  (3663661,40,4,[2,3,5,7,11,13,61]),
  (3675211,27,16,[2,3,5,7,11,37,43]),
  (3693691,2,17,[2,3,5,7,11,13,41]),
  (3723721,68,13,[2,3,5,7,11,13,31]),
  (3730651,27,20,[2,3,5,7,11,17,19]),
  (3805621,10,3,[2,3,5,7,13,17,41]),
  (3813811,10,25,[2,3,5,7,11,13,127]),
  (3818431,6,98,[2,3,5,7,11,19,29]),
  (3873871,6,5,[2,3,5,7,11,13,43]),
  (3993991,14,51,[2,3,5,7,11,13,19]),
  (4024021,22,35,[2,3,5,7,11,13,67]),
  (4037881,58,96,[2,3,5,7,11,19,23]),
  (4084081,86,110,[2,3,5,7,11,13,17]),
  (13123111,11,10,[2,3,5,7,11,13,19,23]),
  (14804791,11,2,[2,3,5,7,11,13,17,29]),
  (16546531,27,20,[2,3,5,7,11,13,19,29]),
  (17160991,14,74,[2,3,5,7,11,17,19,23]),
  (18888871,6,13,[2,3,5,7,11,13,17,37])]

def orders23 : List ℕ := [2323231,2348347,2372371,2381191,2437891,2459731,2478631,2574391,2582581,2624623,2631091,2645371,2661331,2672671,2677291,2691781,2699971,2738191,2762761,2771341,2831011,2866711,2897311,2916691,2940631,2984521,2990131,3038071,3091111,3102331,3109471,3131311,3134671,3164071,3209431,3245971,3295111,3304291,3327871,3333331,3354781,3365671,3366511,3377221,3387931,3404311,3453451,3483481,3530731,3550471,3559711,3598981,3663661,3675211,3693691,3723721,3730651,3805621,3813811,3818431,3873871,3993991,4024021,4037881,4084081,13123111,14804791,16546531,17160991,18888871]

theorem certs23_ok : checkAll certs23 = true := by decide +kernel

theorem certs23_orders : certs23.map (·.1) = orders23 := by decide +kernel

theorem good23 : ∀ q ∈ orders23, Good q :=
  certs23_orders ▸ checkAll_sound certs23_ok

end SunBatchPrime

namespace SunBatchPrime

/-- The prime orders of the reduced exceptional set (13 excluded). -/
def primeOrders : List ℕ :=
  orders0 ++ orders1 ++ orders2 ++ orders3 ++ orders4 ++ orders5 ++ orders6 ++ orders7 ++ orders8 ++ orders9 ++ orders10 ++ orders11 ++ orders12 ++ orders13 ++ orders14 ++ orders15 ++ orders16 ++ orders17 ++ orders18 ++ orders19 ++ orders20 ++ orders21 ++ orders22 ++ orders23

theorem primeOrders_length : primeOrders.length = 2370 := by decide +kernel

theorem primeOrders_bounds : primeOrders.head? = some 11 ∧ primeOrders.getLast? = some 18888871 := by decide +kernel

theorem primeOrders_good : ∀ q ∈ primeOrders, Good q := by
  intro q h
  unfold primeOrders at h
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good23 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good22 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good21 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good20 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good19 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good18 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good17 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good16 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good15 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good14 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good13 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good12 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good11 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good10 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good9 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good8 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good7 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good6 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good5 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good4 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good3 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good2 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good1 q h'
  exact good0 q h

end SunBatchPrime


/- The order 13 has no reflection certificate for the offset +1; use an explicit cycle. -/
namespace SunBatchPrime

def nums13 : Fin 12 → ℕ := ![1,5,2,3,9,4,8,12,7,10,11,6]

def next13 (i : Fin 12) : Fin 12 := ⟨(i.val + 1) % 12, Nat.mod_lt _ (by norm_num)⟩

def unit13 (i : Fin 12) : (ZMod 13)ˣ :=
  ZMod.unitOfCoprime (nums13 i) ((by decide : ∀ j : Fin 12, (nums13 j).Coprime 13) i)

def value13 (i : Fin 12) : ZMod 13 := nums13 i * (nums13 (next13 i) : ZMod 13) + 1

theorem good_thirteen : Good 13 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have hinj : Function.Injective unit13 := by
    intro i j h
    exact (by decide : ∀ i j : Fin 12, (nums13 i : ZMod 13) = (nums13 j : ZMod 13) → i = j) i j
      (congrArg (fun x : (ZMod 13)ˣ => (x : ZMod 13)) h)
  have hc : Fintype.card (Fin 12) = Fintype.card (ZMod 13)ˣ := by
    rw [Fintype.card_fin, ZMod.card_units_eq_totient]; decide
  refine ⟨Equiv.ofBijective unit13
    ((Fintype.bijective_iff_injective_and_card unit13).mpr ⟨hinj, hc⟩), ?_⟩
  intro i
  change IsPrimitiveRoot (value13 i) 12
  apply IsPrimitiveRoot.mk_of_lt _ (by decide)
  · exact (by decide : ∀ j : Fin 12, (value13 j)^12 = 1) i
  · intro l hl hk
    exact (by decide : ∀ j r : Fin 12, 0 < r.val → (value13 j)^r.val ≠ 1) i ⟨l, hk⟩ hl

end SunBatchPrime



namespace SunFinish
def Circle (F : Type*) [Field F] (m : ℕ) : Prop :=
  ∃ a : Fin m ≃ Fˣ, ∀ i : Fin m,
    IsPrimitiveRoot ((a i : F) * (a ⟨(i.val+1)%m,Nat.mod_lt _ (by have := i.isLt; omega)⟩ : F) + 1) m

theorem transport {K F : Type*} [Field K] [Field F] {m : ℕ}
    (e : K ≃+* F) (h : Circle K m) : Circle F m := by
  obtain ⟨a,ha⟩ := h
  refine ⟨a.trans (Units.mapEquiv e.toMulEquiv).toEquiv, ?_⟩
  intro i
  change IsPrimitiveRoot (e (a i : K) * e (a _ : K) + 1) m
  simpa using (ha i).map_of_injective e.injective

theorem of_prime_certificate (F : Type*) [Field F] [Fintype F] {q : ℕ}
    (hc : Fintype.card F = q) (h : SunBatchPrime.Good q) : Circle F (Fintype.card F-1) := by
  obtain ⟨hq, _, a, ha⟩ := h
  letI : Fact q.Prime := ⟨hq⟩
  rw [hc]
  exact transport (FiniteField.ringEquivOfCardEq ((ZMod.card q).trans hc.symm)) ⟨a,ha⟩

end SunFinish

namespace SunBatchExtension.SunOddReflection

/-- Alternately traverse the subgroup generated by r and its coset A times that subgroup. -/
def vertex {G : Type*} [CommGroup G] (A r : G) {d : ℕ} (i : Fin (2*d)) : G :=
  if i.val % 2 = 0 then r ^ (i.val / 2) else A / r ^ (i.val / 2)

theorem cycle {F : Type*} [Field F] [Fintype Fˣ] {d : ℕ} (hd : 0 < d)
    (hc : Fintype.card Fˣ = 2*d) (A r : Fˣ) (hr : IsPrimitiveRoot r d)
    (hcoset : ∀ k : ℕ, A ≠ r^k)
    (hA : IsPrimitiveRoot ((A : F) + 1) (2*d))
    (hB : IsPrimitiveRoot (((A*r : Fˣ) : F) + 1) (2*d)) :
    ∃ a : Fin (2*d) ≃ Fˣ, ∀ i : Fin (2*d),
      IsPrimitiveRoot ((a i : F) *
        (a ⟨(i.val + 1) % (2*d), Nat.mod_lt _ (by omega)⟩ : F) + 1) (2*d) := by
  have sep (i j : ℕ) : r^i ≠ A/r^j := by
    intro h
    exact hcoset (i+j) (by rw [pow_add]; rw [h]; simp)
  have inj : Function.Injective (vertex A r (d := d)) := by
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    unfold vertex at h
    split at h <;> split at h
    · have := hr.pow_inj (by omega) (by omega) h
      exact Fin.ext (by omega)
    · exact (sep _ _ h).elim
    · exact (sep _ _ h.symm).elim
    · have he : r ^ (i.val / 2) = r ^ (j.val / 2) := by simpa using h
      have := hr.pow_inj (by omega) (by omega) he
      exact Fin.ext (by omega)
  let a := Equiv.ofBijective (vertex A r (d := d))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨inj, by simp [hc]⟩)
  refine ⟨a, ?_⟩
  intro i
  let j : Fin (2*d) := ⟨(i.val+1)%(2*d), Nat.mod_lt _ (by omega)⟩
  change IsPrimitiveRoot (((vertex A r i : Fˣ) : F) * ((vertex A r j : Fˣ) : F) + 1) _
  rw [← Units.val_mul]
  have hi := i.isLt
  by_cases hlast : i.val+1 = 2*d
  · have hj : j.val = 0 := by simp [j, hlast]
    have ho : i.val % 2 ≠ 0 := by omega
    have he : i.val/2+1 = d := by omega
    have hpow : r^(i.val/2)*r=1 := by rw [← pow_succ, he]; exact hr.pow_eq_one
    have hprod : vertex A r i * vertex A r j = A*r := by
      simp [vertex, ho, hj]
      grind [div_eq_mul_inv, mul_eq_one_iff_inv_eq]
    rwa [hprod]
  · have hji : j.val=i.val+1 := Nat.mod_eq_of_lt (by omega)
    by_cases he : i.val%2=0
    · have ho : j.val%2≠0 := by omega
      have hdiv : j.val/2=i.val/2 := by omega
      have hp : vertex A r i * vertex A r j = A := by simp [vertex,he,ho,hdiv]
      rwa [hp]
    · have ho : j.val%2=0 := by omega
      have hdiv : j.val/2=i.val/2+1 := by omega
      have hp : vertex A r i * vertex A r j = A*r := by
        simp [vertex,he,ho,hdiv,pow_succ,← mul_assoc]
      rwa [hp]

end SunBatchExtension.SunOddReflection

namespace SunBatchExtension.SunOddLength
/-- The path 0,1,-1,2,-2,...,h,-h in a cyclic group of order 2h+1. -/
def slot (h : ℕ) (i : Fin (2*h+1)) : Fin (2*h+1) :=
  if h0 : i.val=0 then 0
  else if h1 : i.val%2=1 then ⟨(i.val+1)/2,by omega⟩
  else ⟨2*h+1-i.val/2,by omega⟩

theorem slot_inj (h : ℕ) : Function.Injective (slot h) := by
  intro i j he
  have he' := congrArg Fin.val he
  apply Fin.ext
  dsimp [slot] at he'
  split at he' <;> split at he' <;> simp_all <;>
    (repeat' split at he') <;> simp_all <;> omega

noncomputable def circle (h : ℕ) : Equiv.Perm (Fin (2*h+1)) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (slot_inj h))

theorem neighbor (h : ℕ) (i : Fin (2*h+1)) (hi : i.val+1<2*h+1) :
    ((slot h i).val + (slot h ⟨i.val+1, hi⟩).val) % (2*h+1) = if i.val%2=0 then 1 else 0 := by
  dsimp [slot]
  split_ifs <;> simp_all <;> first | (subst i; simp_all) | omega | (rw [Nat.mod_eq_sub_mod (by omega)]; rw [Nat.mod_eq_of_lt (by omega)]; omega)

theorem endpoints (h : ℕ) : (slot h 0).val=0 ∧
    (2*(slot h ⟨2*h,by omega⟩).val) % (2*h+1) = 1 % (2*h+1) := by
  constructor
  · simp [slot]
  · by_cases hh : h=0
    · subst h; decide
    · simp [slot, hh]
      rw [show 2*(2*h+1-h) = 1+(2*h+1) by omega, Nat.add_mod_right]
end SunBatchExtension.SunOddLength

namespace SunBatchExtension.SunEvenReflection
open SunOddLength

theorem cycle {F : Type*} [Field F] [CharP F 2] [Fintype Fˣ]
    {h : ℕ} (hh : 0 < h) (hc : Fintype.card Fˣ = 2*h+1)
    (A B : Fˣ) (hr : IsPrimitiveRoot (B/A) (2*h+1))
    (hA : IsPrimitiveRoot ((A : F) + 1) (2*h+1))
    (hB : IsPrimitiveRoot ((B : F) + 1) (2*h+1))
    (hAB : IsPrimitiveRoot (((A*B : Fˣ) : F) + 1) (2*h+1)) :
    ∃ a : Fin (2*h+1) ≃ Fˣ, ∀ i : Fin (2*h+1),
      IsPrimitiveRoot ((a i : F) *
        (a ⟨(i.val+1)%(2*h+1),Nat.mod_lt _ (by omega)⟩ : F) + 1) (2*h+1) := by
  let r := B/A
  let s := A^(h+1)
  have hs : s*s=A := by
    dsimp [s]
    rw [← pow_add, show h+1+(h+1)= (2*h+1)+1 by omega, pow_succ, ← hc,
      pow_card_eq_one, one_mul]
  have hmod (z : ℕ) : r^(z%(2*h+1)) = r^z := by
    rw [hr.eq_orderOf]; exact pow_mod_orderOf r z
  let v (i : Fin (2*h+1)) := s*r^(slot h i).val
  have inj : Function.Injective v := by
    intro i j eq
    have hpow : r^(slot h i).val = r^(slot h j).val := mul_left_cancel eq
    exact slot_inj h (Fin.ext (hr.pow_inj (slot h i).isLt (slot h j).isLt hpow))
  let a := Equiv.ofBijective v ((Fintype.bijective_iff_injective_and_card _).mpr ⟨inj,by simp [hc]⟩)
  refine ⟨a,?_⟩
  intro i
  let j : Fin (2*h+1) := ⟨(i.val+1)%(2*h+1),Nat.mod_lt _ (by omega)⟩
  change IsPrimitiveRoot (((v i : Fˣ) : F)*((v j : Fˣ) : F) + 1) _
  rw [← Units.val_mul]
  have hp : v i * v j = A*r^((slot h i).val+(slot h j).val) := by
    dsimp [v]; rw [pow_add,← hs]; ac_rfl
  by_cases hi : i.val+1 < 2*h+1
  · have hj : j=⟨i.val+1,hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
    rw [hp, ← hmod, hj, neighbor h i hi]
    split
    · simpa [r] using hB
    · simpa using hA
  · have hi' : i=⟨2*h,by omega⟩ := Fin.ext (show i.val=2*h by omega)
    have hj : j=0 := by apply Fin.ext; simp [j,show i.val+1=2*h+1 by omega]
    let c := v i*v j
    have hc2 : c^2 = A*B := by
      dsimp [c]; rw [hp,hj, (endpoints h).1, add_zero, mul_pow, ← pow_mul, mul_comm _ 2,
        ← hmod,hi',(endpoints h).2,Nat.mod_eq_of_lt (by omega),pow_one]
      dsimp [r]; simp [sq,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
    apply IsPrimitiveRoot.of_map_of_injective (f := frobenius F 2) _ (frobenius_inj F 2)
    change IsPrimitiveRoot (frobenius F 2 ((c : F) + 1)) _
    rwa [map_add, map_one, frobenius_def, ← Units.val_pow_eq_pow_val, hc2]
end SunBatchExtension.SunEvenReflection

/-
Kernel-checkable replay for prime-power field orders `q = p^k`, `k ≥ 1`.

Elements of `F_p[x]/(x^k - c(x))` are coefficient lists over `ℕ` (low degree first); `c` is the
list with `x^k = Σ c_i x^i`. All arithmetic is structural recursion on lists with GMP-accelerated
`ℕ` operations, so `decide +kernel` evaluates it. Nothing about `c` is assumed: the quotient ring
`AdjoinRoot (X^k - c)` has `p^k` elements and the certificate exhibits an element of order
`p^k - 1` in it, which forces it to be a field. Uniqueness of finite fields then transports the
cyclic ordering to every field of that cardinality.
-/


namespace SunBatchExtension

open Polynomial

universe u

/- ### Coefficient-list arithmetic -/

def addL (p : ℕ) : List ℕ → List ℕ → List ℕ
  | [], b => b
  | x :: a, [] => x :: a
  | x :: a, y :: b => ((x + y) % p) :: addL p a b

def smulL (p x : ℕ) : List ℕ → List ℕ
  | [] => []
  | y :: b => (x * y % p) :: smulL p x b

def mulL (p : ℕ) : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | x :: a, b => addL p (smulL p x b) (0 :: mulL p a b)

/-- One reduction step: replace `l = lo + x^k * hi` by `lo + c * hi`. -/
def red1 (p k : ℕ) (c l : List ℕ) : List ℕ := addL p (l.take k) (mulL p c (l.drop k))

/-- Identity on lists; forces the kernel to evaluate every entry to a literal. -/
def strict : List ℕ → List ℕ
  | [] => []
  | 0 :: t => 0 :: strict t
  | (m+1) :: t => (m+1) :: strict t

theorem strict_eq (l : List ℕ) : strict l = l := by
  induction l with
  | nil => rfl
  | cons x t ih => cases x <;> simp [strict, ih]

/-- Multiplication modulo `x^k - c`. -/
def mulR (p k : ℕ) (c a b : List ℕ) : List ℕ := strict ((red1 p k c)^[k-1] (mulL p a b))

/-- Binary exponentiation; the first numeric argument is fuel. -/
def powL (p k : ℕ) (c x : List ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => [1]
  | f+1, e =>
    if e = 0 then [1]
    else if e % 2 = 1 then
      mulR p k c (mulR p k c (powL p k c x f (e/2)) (powL p k c x f (e/2))) x
    else mulR p k c (powL p k c x f (e/2)) (powL p k c x f (e/2))

def addOne (p : ℕ) (l : List ℕ) : List ℕ := addL p l [1]

def oneL (k : ℕ) : List ℕ := 1 :: List.replicate (k-1) 0

def zeroL (k : ℕ) : List ℕ := List.replicate k 0

/-- Canonical form: exactly `k` coefficients, each below `p`. -/
def normB (p k : ℕ) (l : List ℕ) : Bool := (l.length == k) && l.all (fun x => decide (x < p))

def notOneB (p k : ℕ) (l : List ℕ) : Bool := normB p k l && (l != oneL k)

/-- `x` has multiplicative order `n`, tested on the primes in `ps`. -/
def orderB (p k : ℕ) (c x : List ℕ) (n : ℕ) (ps : List ℕ) : Bool :=
  (powL p k c x 64 n == oneL k) &&
    ps.all (fun q => decide (n % q ≠ 0) || notOneB p k (powL p k c x 64 (n/q)))

/- ### Evaluation in a commutative ring of characteristic `p` -/

def ev {S : Type*} [CommRing S] (α : S) : List ℕ → S
  | [] => 0
  | x :: l => (x : S) + α * ev α l

theorem cast_mod {S : Type*} [CommRing S] {p : ℕ} (hp : (p : S) = 0) (n : ℕ) :
    ((n % p : ℕ) : S) = n := by
  conv_rhs => rw [← Nat.div_add_mod n p]
  push_cast
  rw [hp]; simp

theorem ev_addL {S : Type*} [CommRing S] (α : S) {p : ℕ} (hp : (p : S) = 0) (a b : List ℕ) :
    ev α (addL p a b) = ev α a + ev α b := by
  induction a generalizing b with
  | nil => simp [addL, ev]
  | cons x a ih =>
    cases b with
    | nil => simp [addL, ev]
    | cons y b =>
      simp only [addL, ev, ih, cast_mod hp]
      push_cast; ring

theorem ev_smulL {S : Type*} [CommRing S] (α : S) {p : ℕ} (hp : (p : S) = 0) (x : ℕ)
    (b : List ℕ) : ev α (smulL p x b) = x * ev α b := by
  induction b with
  | nil => simp [smulL, ev]
  | cons y b ih =>
    simp only [smulL, ev, ih, cast_mod hp]
    push_cast; ring

theorem ev_mulL {S : Type*} [CommRing S] (α : S) {p : ℕ} (hp : (p : S) = 0) (a b : List ℕ) :
    ev α (mulL p a b) = ev α a * ev α b := by
  induction a with
  | nil => simp [mulL, ev]
  | cons x a ih =>
    simp only [mulL, ev_addL α hp, ev_smulL α hp, ev, ih]
    push_cast; ring

theorem ev_take_drop {S : Type*} [CommRing S] (α : S) (k : ℕ) (l : List ℕ) :
    ev α (l.take k) + α^k * ev α (l.drop k) = ev α l := by
  induction k generalizing l with
  | zero => simp [ev]
  | succ k ih =>
    cases l with
    | nil => simp [ev]
    | cons x l =>
      simp only [List.take_succ_cons, List.drop_succ_cons, ev]
      rw [← ih l]; ring

theorem ev_red1 {S : Type*} [CommRing S] (α : S) {p k : ℕ} {c : List ℕ} (hp : (p : S) = 0)
    (hc : ev α c = α^k) (l : List ℕ) : ev α (red1 p k c l) = ev α l := by
  rw [red1, ev_addL α hp, ev_mulL α hp, hc, ev_take_drop]

theorem ev_iter {S : Type*} [CommRing S] (α : S) {p k : ℕ} {c : List ℕ} (hp : (p : S) = 0)
    (hc : ev α c = α^k) (m : ℕ) (l : List ℕ) : ev α ((red1 p k c)^[m] l) = ev α l := by
  induction m generalizing l with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih, ev_red1 α hp hc]

theorem ev_mulR {S : Type*} [CommRing S] (α : S) {p k : ℕ} {c : List ℕ} (hp : (p : S) = 0)
    (hc : ev α c = α^k) (a b : List ℕ) : ev α (mulR p k c a b) = ev α a * ev α b := by
  rw [mulR, strict_eq, ev_iter α hp hc, ev_mulL α hp]

theorem ev_powL {S : Type*} [CommRing S] (α : S) {p k : ℕ} {c : List ℕ} (hp : (p : S) = 0)
    (hc : ev α c = α^k) (x : List ℕ) :
    ∀ f e, e < 2^f → ev α (powL p k c x f e) = ev α x ^ e := by
  intro f
  induction f with
  | zero =>
    intro e he
    have : e = 0 := by simpa using he
    subst this
    simp [powL, ev]
  | succ f ih =>
    intro e he
    rw [powL]
    by_cases h0 : e = 0
    · simp [h0, ev]
    · have hlt : e/2 < 2^f := by rw [pow_succ] at he; omega
      rw [if_neg h0]
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1, ev_mulR α hp hc, ev_mulR α hp hc, ih _ hlt, ← pow_add, ← pow_succ]
        congr 1; omega
      · rw [if_neg h1, ev_mulR α hp hc, ih _ hlt, ← pow_add]
        congr 1; omega

theorem ev_addOne {S : Type*} [CommRing S] (α : S) {p : ℕ} (hp : (p : S) = 0)
    (l : List ℕ) : ev α (addOne p l) = ev α l + 1 := by
  simp [addOne, ev_addL α hp, ev]

theorem ev_replicate {S : Type*} [CommRing S] (α : S) (m : ℕ) :
    ev α (List.replicate m 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, ev, ih]

theorem ev_oneL {S : Type*} [CommRing S] (α : S) (k : ℕ) : ev α (oneL k) = 1 := by
  simp [oneL, ev, ev_replicate]

theorem normB_oneL {p k : ℕ} (hp : 1 < p) (hk : 0 < k) : normB p k (oneL k) = true := by
  simp only [normB, oneL, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.length_cons, List.length_replicate, List.mem_cons, List.mem_replicate]
  refine ⟨by omega, ?_⟩
  rintro x (rfl | ⟨-, rfl⟩) <;> omega

theorem normB_zeroL {p k : ℕ} (hp : 0 < p) : normB p k (zeroL k) = true := by
  simp only [normB, zeroL, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.length_replicate, List.mem_replicate, true_and]
  rintro x ⟨-, rfl⟩
  exact hp

theorem orderB_sound {S : Type*} [CommRing S] (α : S) {p k : ℕ} {c : List ℕ}
    (hp : (p : S) = 0) (hc : ev α c = α^k)
    (hone : ∀ l, normB p k l = true → ev α l = 1 → l = oneL k)
    {x : List ℕ} {n : ℕ} {ps : List ℕ} (hn : 0 < n) (hn' : n < 2^64)
    (hps : ∀ q, q.Prime → q ∣ n → q ∈ ps) (h : orderB p k c x n ps = true) :
    IsPrimitiveRoot (ev α x) n := by
  simp only [orderB, notOneB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at h
  refine IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_of_pow_and_pow_div_prime hn ?_ ?_)
  · rw [← ev_powL α hp hc x 64 n hn', h.1, ev_oneL]
  · intro q hq hqn hx
    rcases h.2 q (hps q hq hqn) with h1 | ⟨h1, h2⟩
    · exact h1 (Nat.mod_eq_zero_of_dvd hqn)
    · refine h2 (hone _ h1 ?_)
      rw [ev_powL α hp hc x 64 _ (lt_of_le_of_lt (Nat.div_le_self _ _) hn')]
      exact hx

/- ### Trial-division primality -/

/-- Trial division from `k` upwards; arguments are fuel and `k`. -/
def noDiv (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f+1, k => if p < k*k then true else if p % k = 0 then false else noDiv p f (k+1)

theorem noDiv_sound (p : ℕ) :
    ∀ f k, noDiv p f k = true → ∀ m, k ≤ m → m*m ≤ p → ¬ m ∣ p := by
  intro f
  induction f with
  | zero => intro k h; simp [noDiv] at h
  | succ f ih =>
    intro k h m hkm hmp hdvd
    unfold noDiv at h
    by_cases h1 : p < k*k
    · have := Nat.mul_le_mul hkm hkm
      omega
    · rw [if_neg h1] at h
      by_cases h2 : p % k = 0
      · simp [h2] at h
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hkm with rfl | hlt
        · exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact ih _ h m hlt hmp hdvd

def primeB (p : ℕ) : Bool := decide (2 ≤ p) && noDiv p p 2

theorem primeB_sound {p : ℕ} (h : primeB p = true) : p.Prime := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Nat.prime_def_le_sqrt.mpr ⟨h.1, fun m hm hs =>
    noDiv_sound p p 2 h.2 m hm (Nat.le_sqrt.mp hs)⟩

theorem mem_of_prime_dvd {ps : List ℕ} {n q : ℕ} (hps : ∀ x ∈ ps, x.Prime)
    (hn : ps.prod ^ 64 % n = 0) (hq : q.Prime) (hqn : q ∣ n) : q ∈ ps := by
  have h1 : q ∣ ps.prod := hq.dvd_of_dvd_pow (hqn.trans (Nat.dvd_of_mod_eq_zero hn))
  obtain ⟨a, ha, hqa⟩ := (Prime.dvd_prod_iff hq.prime).mp h1
  rwa [(Nat.prime_dvd_prime_iff_eq hq (hps a ha)).mp hqa]

/- ### The quotient ring is a field -/

theorem isField_of_primitive {R : Type*} [CommRing R] [Finite R] {x : R} {n : ℕ}
    (hcard : Nat.card R = n + 1) (hn : 0 < n) (hx : IsPrimitiveRoot x n) : IsField R := by
  classical
  haveI : Fintype R := Fintype.ofFinite R
  haveI : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hunit : ∀ i, i < n → x^i * x^(n-i) = 1 := fun i hi => by
    rw [← pow_add, Nat.add_sub_cancel' hi.le, hx.pow_eq_one]
  let T : Finset R := (Finset.range n).image (fun i => x^i)
  have hT : T.card = n := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj h
    exact hx.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  have hsub : T ⊆ Finset.univ.erase 0 := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_erase.mpr ⟨fun h0 => ?_, Finset.mem_univ _⟩
    have := hunit i (Finset.mem_range.mp hi)
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hEq : T = Finset.univ.erase 0 := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcard, hT]
    simp)
  refine ⟨exists_pair_ne R, mul_comm, fun {a} ha => ?_⟩
  have : a ∈ T := by rw [hEq]; exact Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp this
  exact ⟨_, hunit i (Finset.mem_range.mp hi)⟩

theorem coeff_ev (p : ℕ) (l : List ℕ) (i : ℕ) :
    (ev (X : (ZMod p)[X]) l).coeff i = ((l.getD i 0 : ℕ) : ZMod p) := by
  induction l generalizing i with
  | nil => simp [ev]
  | cons x l ih =>
    cases i with
    | zero => simp [ev, coeff_natCast_ite]
    | succ i => simp [ev, coeff_natCast_ite, ih]

theorem degree_ev_lt (p : ℕ) {k : ℕ} (l : List ℕ) (hl : l.length ≤ k) :
    (ev (X : (ZMod p)[X]) l).degree < k := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_ev, List.getD_eq_default _ _ (hl.trans hm), Nat.cast_zero]

theorem ev_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a : R) (l : List ℕ) :
    φ (ev a l) = ev (φ a) l := by
  induction l with
  | nil => simp [ev]
  | cons x l ih => simp [ev, ih]

/-- A field of `p^k` elements with a root `α` of `x^k - c` over which coefficient lists in
canonical form are faithful. -/
structure Model (p k : ℕ) (c : List ℕ) (K : Type) [Field K] (α : K) : Prop where
  finite : Finite K
  hp : (p : K) = 0
  hc : ev α c = α^k
  card : Nat.card K = p^k
  inj : ∀ l l', normB p k l = true → normB p k l' = true → ev α l = ev α l' → l = l'

theorem Model.one {p k : ℕ} {c : List ℕ} {K : Type} [Field K] {α : K} (M : Model p k c K α)
    (hp : 1 < p) (hk : 0 < k) : ∀ l, normB p k l = true → ev α l = 1 → l = oneL k :=
  fun l hl h1 => M.inj l (oneL k) hl (normB_oneL hp hk) (by rw [h1, ev_oneL])

theorem exists_model {p k : ℕ} {c : List ℕ} (hp : p.Prime) (hk : 0 < k) (hck : c.length = k)
    (x ps : List ℕ) {n : ℕ} (hn : p^k = n + 1) (hn0 : 0 < n) (hn' : n < 2^64)
    (hps : ∀ q, q.Prime → q ∣ n → q ∈ ps) (h : orderB p k c x n ps = true) :
    ∃ (K : Type) (_ : Field K) (α : K), Model p k c K α := by
  haveI : Fact p.Prime := ⟨hp⟩
  let f : (ZMod p)[X] := X^k - ev (X : (ZMod p)[X]) c
  have hdeg : (ev (X : (ZMod p)[X]) c).degree < k := degree_ev_lt p c hck.le
  have hmonic : f.Monic := monic_X_pow_sub hdeg
  have hfdeg : f.degree = k := by
    change (X^k - ev (X : (ZMod p)[X]) c).degree = (k : WithBot ℕ)
    rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  let α : AdjoinRoot f := AdjoinRoot.root f
  have hpS : ((p : ℕ) : AdjoinRoot f) = 0 := by
    rw [← map_natCast (AdjoinRoot.of f), ZMod.natCast_self, map_zero]
  have hmk : ∀ l, ev α l = AdjoinRoot.mk f (ev X l) := fun l => by
    rw [ev_map, AdjoinRoot.mk_X]
  have hcS : ev α c = α^k := by
    have h0 : AdjoinRoot.mk f (X^k - ev (X : (ZMod p)[X]) c) = 0 := AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, ← hmk, sub_eq_zero] at h0
    exact h0.symm
  have hinj : ∀ l l', normB p k l = true → normB p k l' = true → ev α l = ev α l' → l = l' := by
    intro l l' hl hl' h
    simp only [normB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
      at hl hl'
    rw [hmk, hmk, AdjoinRoot.mk_eq_mk] at h
    have hlt : (ev X l - ev X l' : (ZMod p)[X]).degree < f.degree := by
      rw [hfdeg]
      exact (degree_sub_le _ _).trans_lt
        (max_lt (degree_ev_lt p l hl.1.le) (degree_ev_lt p l' hl'.1.le))
    have hz := eq_zero_of_dvd_of_degree_lt h hlt
    apply List.ext_getElem (hl.1.trans hl'.1.symm)
    intro i h1 h2
    have hco := congrArg (fun g => Polynomial.coeff g i) hz
    simp only [coeff_sub, coeff_ev, coeff_zero, sub_eq_zero] at hco
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (hl.2 _ (List.getElem_mem h1)),
      Nat.mod_eq_of_lt (hl'.2 _ (List.getElem_mem h2))] at hco
    exact hco
  let pb := AdjoinRoot.powerBasis' hmonic
  have hdim : pb.dim = k := natDegree_eq_of_degree_eq_some hfdeg
  let e := pb.basis.equivFun
  haveI : Finite (AdjoinRoot f) := Finite.of_equiv _ e.toEquiv.symm
  have hcard : Nat.card (AdjoinRoot f) = p^k := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin, hdim]
  have hone : ∀ l, normB p k l = true → ev α l = 1 → l = oneL k :=
    fun l hl h1 => hinj l (oneL k) hl (normB_oneL hp.one_lt hk) (by rw [h1, ev_oneL])
  have hprim := orderB_sound α hpS hcS hone hn0 hn' hps h
  have hF : IsField (AdjoinRoot f) := isField_of_primitive (by rw [hcard, hn]) hn0 hprim
  letI : Field (AdjoinRoot f) := hF.toField
  exact ⟨AdjoinRoot f, inferInstance, α, ⟨inferInstance, hpS, hcS, hcard, hinj⟩⟩

/- ### Conclusions -/

/-- The units of `F` have a cyclic ordering of length `n` in which every product of neighbours,
plus one, is a primitive `n`-th root of unity. -/
def Good (F : Type*) [Field F] (n : ℕ) : Prop :=
  ∃ h : 0 < n, ∃ a : Fin n ≃ Fˣ, ∀ i : Fin n,
    IsPrimitiveRoot ((a i : F) * (a ⟨(i.val + 1) % n, Nat.mod_lt _ h⟩ : F) + 1) n

theorem Good.transport {K F : Type*} [Field K] [Field F] (e : K ≃+* F) {n : ℕ}
    (h : Good K n) : Good F n := by
  obtain ⟨hn, a, ha⟩ := h
  refine ⟨hn, a.trans (Units.mapEquiv e.toMulEquiv).toEquiv, fun i => ?_⟩
  have := (ha i).map_of_injective e.injective
  simpa using this

/-- Every field with `q` elements is `Good` with cycle length `q-1`. -/
def GoodOrder (q : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F], Fintype.card F = q → Good F (q-1)

theorem goodOrder_of_model {q : ℕ} {K : Type} [Field K] [Finite K] (hcard : Nat.card K = q)
    (h : Good K (q-1)) : GoodOrder.{u} q := by
  intro F _ _ hF
  haveI := Fintype.ofFinite K
  exact h.transport (FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, hcard, hF]))

/-- Shared side conditions: `p` prime, modulus of degree `k`, `ps` contains every prime
dividing `p^k - 1`. -/
def baseB (p k : ℕ) (c ps : List ℕ) : Bool :=
  primeB p && decide (0 < k) && (c.length == k) && decide (p^k < 2^64) && decide (3 < p^k) &&
    ps.all primeB && decide (ps.prod ^ 64 % (p^k-1) = 0)

theorem baseB_sound {p k : ℕ} {c ps : List ℕ} (h : baseB p k c ps = true) :
    p.Prime ∧ 0 < k ∧ c.length = k ∧ p^k < 2^64 ∧ 3 < p^k ∧
      ∀ q, q.Prime → q ∣ p^k-1 → q ∈ ps := by
  simp only [baseB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hp, hk⟩, hck⟩, h64⟩, h3⟩, hprime⟩, hprod⟩ := h
  exact ⟨primeB_sound hp, hk, hck, h64, h3, fun q hq hqn =>
    mem_of_prime_dvd (fun x hx => primeB_sound (hprime x hx)) hprod hq hqn⟩

theorem not_primitive_one {K : Type*} [Field K] {n : ℕ} (hn : 2 < n) :
    ¬ IsPrimitiveRoot (1 : K) n := fun h => by
  have := Nat.le_of_dvd (by norm_num) (h.dvd_of_pow_eq_one 2 (by simp))
  omega

/- ### Odd characteristic: reflection certificate -/

/-- `a` is a non-square, `r = b/a` generates the squares, and `a+1`, `b+1` are primitive. -/
def checkOdd (p k : ℕ) (c a r b ps : List ℕ) : Bool :=
  baseB p k c ps && decide ((p^k-1) % 2 = 0) &&
    (mulR p k c a r == b) &&
    notOneB p k (powL p k c a 64 ((p^k-1)/2)) &&
    orderB p k c r ((p^k-1)/2) ps &&
    orderB p k c (addOne p a) (p^k-1) ps &&
    orderB p k c (addOne p b) (p^k-1) ps

theorem checkOdd_sound {p k : ℕ} {c a r b ps : List ℕ} (h : checkOdd p k c a r b ps = true) :
    GoodOrder.{u} (p^k) := by
  simp only [checkOdd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hbase, heven⟩, hab⟩, hAd⟩, hr⟩, hA⟩, hB⟩ := h
  obtain ⟨hp, hk, hck, h64, h3, hps⟩ := baseB_sound hbase
  obtain ⟨d, hd⟩ : ∃ d, p^k - 1 = 2*d := ⟨(p^k-1)/2, by omega⟩
  have hdiv : (p^k-1)/2 = d := by omega
  rw [hdiv] at hAd hr
  have hpsd : ∀ q, q.Prime → q ∣ d → q ∈ ps := fun q hq hqd =>
    hps q hq (hd ▸ Dvd.dvd.mul_left hqd 2)
  obtain ⟨K, _, α, M⟩ := exists_model hp hk hck (addOne p a) ps (n := p^k-1)
    (by omega) (by omega) (by omega) hps hA
  haveI := M.finite
  have hone := M.one hp.one_lt hk
  have pA := orderB_sound α M.hp M.hc hone (by omega) (by omega) hps hA
  have pB := orderB_sound α M.hp M.hc hone (by omega) (by omega) hps hB
  have pr := orderB_sound α M.hp M.hc hone (n := d) (by omega) (by omega) hpsd hr
  rw [ev_addOne α M.hp] at pA pB
  have hmul : ev α a * ev α r = ev α b := by rw [← ev_mulR α M.hp M.hc, hab]
  simp only [notOneB, Bool.and_eq_true, bne_iff_ne] at hAd
  have hAd' : ev α a ^ d ≠ 1 := fun hx =>
    hAd.2 (hone _ hAd.1 (by rw [ev_powL α M.hp M.hc a 64 d (by omega)]; exact hx))
  have hA0 : ev α a ≠ 0 := by
    intro h0
    rw [h0, zero_add] at pA
    exact not_primitive_one (by omega) pA
  have hr0 : ev α r ≠ 0 := by
    intro h0
    have := pr.pow_eq_one
    rw [h0, zero_pow (by omega)] at this
    exact zero_ne_one this
  refine goodOrder_of_model M.card ?_
  let A' : Kˣ := Units.mk0 _ hA0
  let r' : Kˣ := Units.mk0 _ hr0
  haveI : Fintype Kˣ := Fintype.ofFinite _
  have key : ∀ m, m = 2*d → Good K m := by
    rintro m rfl
    refine ⟨by omega, ?_⟩
    refine SunOddReflection.cycle (by omega) ?_ A' r' ?_ ?_ ?_ ?_
    · rw [← Nat.card_eq_fintype_card, Nat.card_units, M.card]; omega
    · exact IsPrimitiveRoot.coe_units_iff.mp pr
    · intro j he
      apply hAd'
      have : ev α a = ev α r ^ j := by
        simpa [A', r'] using congrArg (fun u : Kˣ => (u : K)) he
      rw [this, ← pow_mul, Nat.mul_comm, pow_mul, pr.pow_eq_one, one_pow]
    · rw [← hd]; exact pA
    · rw [← hd]; simpa [A', r', hmul] using pB
  exact key _ hd

/- ### Characteristic two: reflection certificate -/

/-- `r = b/a`, and `r`, `a+1`, `b+1`, `ab+1` are all primitive. -/
def checkEven (k : ℕ) (c a r b ps : List ℕ) : Bool :=
  baseB 2 k c ps &&
    (mulR 2 k c a r == b) &&
    orderB 2 k c r (2^k-1) ps &&
    orderB 2 k c (addOne 2 a) (2^k-1) ps &&
    orderB 2 k c (addOne 2 b) (2^k-1) ps &&
    orderB 2 k c (addOne 2 (mulR 2 k c a b)) (2^k-1) ps

theorem checkEven_sound {k : ℕ} {c a r b ps : List ℕ} (h : checkEven k c a r b ps = true) :
    GoodOrder.{u} (2^k) := by
  simp only [checkEven, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hbase, hab⟩, hr⟩, hA⟩, hB⟩, hAB⟩ := h
  obtain ⟨hp, hk, hck, h64, h3, hps⟩ := baseB_sound hbase
  obtain ⟨m, hm⟩ : ∃ m, 2^k - 1 = 2*m + 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k-1, by omega⟩
    have : 0 < 2^j := by positivity
    exact ⟨2^j - 1, by rw [pow_succ]; omega⟩
  obtain ⟨K, _, α, M⟩ := exists_model hp hk hck (addOne 2 a) ps (n := 2^k-1)
    (by omega) (by omega) (by omega) hps hA
  haveI := M.finite
  have hone := M.one hp.one_lt hk
  have pA := orderB_sound α M.hp M.hc hone (by omega) (by omega) hps hA
  have pB := orderB_sound α M.hp M.hc hone (by omega) (by omega) hps hB
  have pr := orderB_sound α M.hp M.hc hone (by omega) (by omega) hps hr
  have pAB := orderB_sound α M.hp M.hc hone (by omega) (by omega) hps hAB
  rw [ev_addOne α M.hp] at pA pB pAB
  rw [ev_mulR α M.hp M.hc] at pAB
  have hmul : ev α a * ev α r = ev α b := by rw [← ev_mulR α M.hp M.hc, hab]
  have hA0 : ev α a ≠ 0 := by
    intro h0
    rw [h0, zero_add] at pA
    exact not_primitive_one (by omega) pA
  have hr0 : ev α r ≠ 0 := by
    intro h0
    have := pr.pow_eq_one
    rw [h0, zero_pow (by omega)] at this
    exact zero_ne_one this
  refine goodOrder_of_model M.card ?_
  let A' : Kˣ := Units.mk0 _ hA0
  let r' : Kˣ := Units.mk0 _ hr0
  haveI : Fintype Kˣ := Fintype.ofFinite _
  haveI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr M.hp
  have key : ∀ n, n = 2*m + 1 → Good K n := by
    rintro n rfl
    refine ⟨by omega, ?_⟩
    refine SunEvenReflection.cycle (by omega) ?_ A' (A' * r') ?_ ?_ ?_ ?_
    · rw [← Nat.card_eq_fintype_card, Nat.card_units, M.card]; omega
    · rw [mul_div_cancel_left, ← hm]
      exact IsPrimitiveRoot.coe_units_iff.mp pr
    · rw [← hm]; exact pA
    · rw [← hm]; simpa [A', r', hmul] using pB
    · rw [← hm]; simpa [A', r', hmul] using pAB
  exact key _ hm

/- ### Explicit Hamiltonian cycle -/

/-- `L` lists all nonzero elements once and every cyclic neighbour product plus one is
primitive. -/
def checkCycle (p k : ℕ) (c : List ℕ) (L : List (List ℕ)) (ps : List ℕ) : Bool :=
  baseB p k c ps && (L.length == p^k-1) && L.all (normB p k) && L.all (· != zeroL k) &&
    decide L.Nodup &&
    (List.range (p^k-1)).all (fun i =>
      orderB p k c (addOne p (mulR p k c (L.getD i []) (L.getD ((i+1) % (p^k-1)) [])))
        (p^k-1) ps)

theorem checkCycle_sound {p k : ℕ} {c : List ℕ} {L : List (List ℕ)} {ps : List ℕ}
    (h : checkCycle p k c L ps = true) : GoodOrder.{u} (p^k) := by
  simp only [checkCycle, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hbase, hlen⟩, hnorm⟩, hnz⟩, hnodup⟩, hedge⟩ := h
  obtain ⟨hp, hk, hck, h64, h3, hps⟩ := baseB_sound hbase
  obtain ⟨K, _, α, M⟩ := exists_model hp hk hck _ ps (n := p^k-1)
    (by omega) (by omega) (by omega) hps (hedge 0 (by omega))
  haveI := M.finite
  have hone := M.one hp.one_lt hk
  have hmem : ∀ i, i < p^k-1 → L.getD i [] ∈ L := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have h0 : ∀ i : Fin (p^k-1), ev α (L.getD i.val []) ≠ 0 := by
    intro i hz
    refine hnz _ (hmem i.val i.isLt) (M.inj _ _ (hnorm _ (hmem i.val i.isLt))
      (normB_zeroL hp.pos) ?_)
    rw [hz, zeroL, ev_replicate]
  let v : Fin (p^k-1) → Kˣ := fun i => Units.mk0 _ (h0 i)
  haveI : Fintype Kˣ := Fintype.ofFinite _
  have hinj : Function.Injective v := by
    intro i j hij
    have h1 : ev α (L.getD i.val []) = ev α (L.getD j.val []) :=
      congrArg (fun u : Kˣ => (u : K)) hij
    have h2 := M.inj _ _ (hnorm _ (hmem i.val i.isLt)) (hnorm _ (hmem j.val j.isLt)) h1
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at h2
    exact Fin.ext ((hnodup.getElem_inj_iff).mp h2)
  have hcard : Fintype.card (Fin (p^k-1)) = Fintype.card Kˣ := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_units, M.card]
  refine goodOrder_of_model M.card ⟨by omega,
    Equiv.ofBijective v ((Fintype.bijective_iff_injective_and_card v).mpr ⟨hinj, hcard⟩), ?_⟩
  intro i
  have := orderB_sound α M.hp M.hc hone (by omega) (by omega) hps (hedge i.val i.isLt)
  rw [ev_addOne α M.hp, ev_mulR α M.hp M.hc] at this
  exact this

/- ### Batches -/

/-- A certificate for one prime-power order. -/
inductive Cert where
  | odd (p k : ℕ) (c a r b ps : List ℕ)
  | even (k : ℕ) (c a r b ps : List ℕ)
  | cycle (p k : ℕ) (c : List ℕ) (L : List (List ℕ)) (ps : List ℕ)

def Cert.order : Cert → ℕ
  | .odd p k _ _ _ _ _ => p^k
  | .even k _ _ _ _ _ => 2^k
  | .cycle p k _ _ _ => p^k

def Cert.check : Cert → Bool
  | .odd p k c a r b ps => checkOdd p k c a r b ps
  | .even k c a r b ps => checkEven k c a r b ps
  | .cycle p k c L ps => checkCycle p k c L ps

theorem Cert.sound : ∀ {x : Cert}, x.check = true → GoodOrder.{u} x.order
  | .odd _ _ _ _ _ _ _, h => checkOdd_sound h
  | .even _ _ _ _ _ _, h => checkEven_sound h
  | .cycle _ _ _ _ _, h => checkCycle_sound h

def checkAll (l : List Cert) : Bool := l.all Cert.check

theorem checkAll_sound {l : List Cert} (h : checkAll l = true) :
    ∀ q ∈ l.map Cert.order, GoodOrder.{u} q := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
  exact Cert.sound (List.all_eq_true.mp h x hx)

end SunBatchExtension


namespace SunBatchExtension

universe u

def certs0 : List Cert := [
  .even 3 [1,1,0] [0,1,0] [0,0,1] [1,1,0] [7],
  .even 6 [1,1,0,0,0,0] [0,1,1,0,0,0] [1,0,1,1,1,1] [0,0,0,1,0,0] [3,7],
  .even 8 [1,0,1,1,1,0,0,0] [1,1,0,0,0,0,0,0] [1,1,0,0,1,1,1,1] [0,0,0,1,0,0,0,0] [3,5,17],
  .odd 3 6 [1,2,0,0,0,0] [2,2,0,0,0,0] [1,0,2,1,2,1] [1,0,1,0,0,0] [2,7,13],
  .odd 41 2 [29,40] [0,1] [25,24] [40,1] [2,3,5,7],
  .odd 59 2 [57,58] [0,1] [52,51] [16,1] [2,3,5,29],
  .odd 83 2 [81,82] [3,1] [23,72] [8,1] [2,3,7,41],
  .odd 113 2 [103,112] [0,1] [90,89] [14,1] [2,3,7,19],
  .odd 149 2 [146,148] [0,1] [146,145] [12,1] [2,3,5,37],
  .odd 239 2 [226,238] [0,1] [70,69] [59,1] [2,3,5,7,17],
  .odd 379 2 [369,378] [16,1] [277,209] [68,1] [2,3,5,7,19],
  .odd 911 2 [874,910] [32,1] [643,185] [66,1] [2,3,5,7,13,19]]

def orders0 : List ℕ := [8,64,256,729,1681,3481,6889,12769,22201,57121,143641,829921]

theorem certs0_ok : checkAll certs0 = true := by decide +kernel

theorem certs0_orders : certs0.map Cert.order = orders0 := by decide +kernel

theorem good0 : ∀ q ∈ orders0, GoodOrder.{u} q :=
  certs0_orders ▸ checkAll_sound certs0_ok

end SunBatchExtension


namespace SunBatchExtension

universe u

def certs1 : List Cert := [
  .odd 3 2 [1,2] [0,1] [1,2] [2,2] [2],
  .odd 3 4 [1,2,0,0] [0,1,0,0] [0,0,1,0] [0,0,0,1] [2,5],
  .odd 17 2 [14,16] [1,2] [16,14] [0,1] [2,3],
  .odd 29 2 [26,28] [7,2] [10,8] [22,2] [2,3,5,7],
  .odd 43 2 [40,42] [1,1] [1,31] [37,1] [2,3,7,11],
  .odd 61 2 [59,60] [0,1] [57,56] [10,1] [2,3,5,31],
  .odd 89 2 [83,88] [52,1] [42,69] [79,1] [2,3,5,11],
  .odd 11 4 [9,10,0,0] [3,3,0,0] [3,7,4,7] [0,9,0,0] [2,3,5,61],
  .odd 151 2 [139,150] [0,1] [50,49] [16,1] [2,3,5,19],
  .odd 281 2 [278,280] [13,1] [237,74] [49,1] [2,3,5,7,47],
  .odd 419 2 [417,418] [0,1] [203,202] [15,1] [2,3,5,7,11,19],
  .odd 1429 2 [1396,1428] [10,1] [176,1092] [20,1] [2,3,5,7,11,13,17]]

def orders1 : List ℕ := [9,81,289,841,1849,3721,7921,14641,22801,78961,175561,2042041]

theorem certs1_ok : checkAll certs1 = true := by decide +kernel

theorem certs1_orders : certs1.map Cert.order = orders1 := by decide +kernel

theorem good1 : ∀ q ∈ orders1, GoodOrder.{u} q :=
  certs1_orders ▸ checkAll_sound certs1_ok

end SunBatchExtension


namespace SunBatchExtension

universe u

def certs2 : List Cert := [
  .even 4 [1,1,0,0] [0,1,0,0] [0,1,0,0] [0,0,1,0] [3,5],
  .odd 11 2 [4,10] [0,1] [3,2] [8,1] [2,3,5],
  .odd 7 3 [5,4,0] [3,2,0] [1,2,1] [6,2,0] [2,3,19],
  .odd 31 2 [19,30] [8,1] [26,23] [25,1] [2,3,5],
  .odd 13 3 [7,12,0] [6,1,0] [4,9,5] [7,1,0] [2,3,61],
  .even 12 [1,1,0,0,1,0,1,0,0,0,0,0] [0,1,0,0,0,0,0,0,0,0,0,0] [0,1,0,0,0,0,0,0,0,0,0,0] [0,0,1,0,0,0,0,0,0,0,0,0] [3,5,7,13],
  .odd 101 2 [98,100] [10,1] [63,38] [11,1] [2,3,5,17],
  .odd 5 6 [3,4,0,0,0,0] [0,1,0,0,0,0] [4,1,0,0,0,4] [2,0,1,0,0,0] [2,3,7,31],
  .odd 13 4 [11,12,12,0] [2,1,0,0] [7,3,4,11] [5,2,0,0] [2,3,5,7,17],
  .odd 307 2 [302,306] [0,1] [61,60] [7,1] [2,3,7,11,17],
  .odd 461 2 [459,460] [6,1] [392,14] [19,1] [2,3,5,7,11,23]]

def orders2 : List ℕ := [16,121,343,961,2197,4096,10201,15625,28561,94249,212521]

theorem certs2_ok : checkAll certs2 = true := by decide +kernel

theorem certs2_orders : certs2.map Cert.order = orders2 := by decide +kernel

theorem good2 : ∀ q ∈ orders2, GoodOrder.{u} q :=
  certs2_orders ▸ checkAll_sound certs2_ok

end SunBatchExtension


namespace SunBatchExtension

universe u

def certs3 : List Cert := [
  .cycle 5 2 [3,4] [[1,0],[0,1],[4,2],[4,3],[1,1],[1,3],[4,0],[0,4],[1,2],[2,3],[3,2],[4,4],[3,1],[2,1],[2,0],[0,3],[4,1],[3,3],[3,0],[0,2],[1,4],[2,2],[2,4],[3,4]] [2,3],
  .odd 5 3 [3,2,0] [0,1,0] [2,0,2] [1,1,0] [2,31],
  .odd 19 2 [17,18] [3,1] [6,7] [4,1] [2,3,5],
  .even 10 [1,0,0,1,0,0,0,0,0,0] [1,1,0,0,0,0,0,0,0,0] [0,1,0,0,0,0,0,0,0,0] [0,1,1,0,0,0,0,0,0,0] [3,11,31],
  .odd 47 2 [34,46] [0,1] [4,3] [8,1] [2,3,23],
  .odd 67 2 [55,66] [27,1] [41,50] [38,1] [2,3,11,17],
  .odd 103 2 [98,102] [0,1] [78,77] [27,1] [2,3,13,17],
  .odd 131 2 [117,130] [0,1] [19,18] [10,1] [2,3,5,11,13],
  .odd 181 2 [163,180] [0,1] [141,140] [14,1] [2,3,5,7,13],
  .odd 311 2 [294,310] [0,1] [257,256] [2,1] [2,3,5,13,31],
  .odd 571 2 [568,570] [9,1] [397,236] [10,1] [2,3,5,11,13,19]]

def orders3 : List ℕ := [25,125,361,1024,2209,4489,10609,17161,32761,96721,326041]

theorem certs3_ok : checkAll certs3 = true := by decide +kernel

theorem certs3_orders : certs3.map Cert.order = orders3 := by decide +kernel

theorem good3 : ∀ q ∈ orders3, GoodOrder.{u} q :=
  certs3_orders ▸ checkAll_sound certs3_ok

end SunBatchExtension


namespace SunBatchExtension

universe u

def certs4 : List Cert := [
  .odd 3 3 [2,1,0] [1,1,0] [1,2,1] [0,1,0] [2,13],
  .odd 13 2 [11,12] [0,1] [1,12] [2,2] [2,3,7],
  .odd 23 2 [16,22] [0,1] [13,12] [8,1] [2,3,11],
  .odd 11 3 [7,10,0] [1,2,0] [4,1,9] [9,2,0] [2,5,7,19],
  .odd 7 4 [2,4,6,0] [4,1,0,0] [4,6,6,2] [6,1,0,0] [2,3,5],
  .odd 71 2 [60,70] [0,1] [52,51] [7,1] [2,3,5,7],
  .odd 109 2 [103,108] [0,1] [34,33] [20,1] [2,3,5,11],
  .odd 137 2 [131,136] [0,1] [114,113] [7,1] [2,3,17,23],
  .odd 211 2 [208,210] [12,1] [77,89] [24,1] [2,3,5,7,53],
  .odd 331 2 [320,330] [0,1] [325,324] [77,1] [2,3,5,11,83],
  .odd 659 2 [649,658] [0,1] [656,655] [40,1] [2,3,5,7,11,47]]

def orders4 : List ℕ := [27,169,529,1331,2401,5041,11881,18769,44521,109561,434281]

theorem certs4_ok : checkAll certs4 = true := by decide +kernel

theorem certs4_orders : certs4.map Cert.order = orders4 := by decide +kernel

theorem good4 : ∀ q ∈ orders4, GoodOrder.{u} q :=
  certs4_orders ▸ checkAll_sound certs4_ok

end SunBatchExtension


namespace SunBatchExtension

universe u

def certs5 : List Cert := [
  .odd 7 2 [4,6] [1,1] [1,3] [6,1] [2,3],
  .odd 3 5 [2,1,0,0,0] [1,1,0,0,0] [1,2,1,2,1] [0,1,0,0,0] [2,11],
  .odd 5 4 [3,3,4,0] [0,1,0,0] [3,3,0,3] [4,2,0,0] [2,3,13],
  .odd 37 2 [32,36] [16,1] [29,8] [17,1] [2,3,19],
  .odd 53 2 [48,52] [0,1] [41,40] [12,1] [2,3,13],
  .odd 79 2 [76,78] [10,1] [20,33] [22,1] [2,3,5,13],
  .odd 23 3 [20,22,0] [1,1,0] [17,15,8] [16,1,0] [2,7,11,79],
  .odd 139 2 [137,138] [0,1] [66,65] [9,1] [2,3,5,7,23],
  .odd 229 2 [223,228] [10,1] [9,50] [19,1] [2,3,5,19,23],
  .odd 349 2 [347,348] [0,1] [346,345] [8,1] [2,3,5,7,29],
  .odd 859 2 [857,858] [0,1] [851,850] [18,1] [2,3,5,11,13,43]]

def orders5 : List ℕ := [49,243,625,1369,2809,6241,12167,19321,52441,121801,737881]

theorem certs5_ok : checkAll certs5 = true := by decide +kernel

theorem certs5_orders : certs5.map Cert.order = orders5 := by decide +kernel

theorem good5 : ∀ q ∈ orders5, GoodOrder.{u} q :=
  certs5_orders ▸ checkAll_sound certs5_ok

end SunBatchExtension


namespace SunBatchExtension

universe u

/-- The nonprime prime-power orders of the reduced exceptional set. -/
def extensionOrders : List ℕ := [8,9,16,25,27,49,64,81,121,125,169,243,256,289,343,361,529,625,729,841,961,1024,1331,1369,1681,1849,2197,2209,2401,2809,3481,3721,4096,4489,5041,6241,6889,7921,10201,10609,11881,12167,12769,14641,15625,17161,18769,19321,22201,22801,28561,32761,44521,52441,57121,78961,94249,96721,109561,121801,143641,175561,212521,326041,434281,737881,829921,2042041]

theorem extensionOrders_length : extensionOrders.length = 68 := by decide +kernel

theorem extensionOrders_sorted : extensionOrders.Pairwise (· < ·) := by decide +kernel

theorem extensionOrders_perm : extensionOrders.Perm (orders0 ++ orders1 ++ orders2 ++ orders3 ++ orders4 ++ orders5) := by decide +kernel

theorem extensionOrders_good : ∀ q ∈ extensionOrders, GoodOrder.{u} q := by
  intro q h0
  have h := extensionOrders_perm.mem_iff.mp h0
  clear h0
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good5 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good4 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good3 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good2 q h'
  rcases List.mem_append.mp h with h | h'
  swap
  · exact good1 q h'
  exact good0 q h

end SunBatchExtension

namespace SunSieve
open Finset

def localFactor (p : ℕ) : ℚ := (p-1 : ℕ)^2 / (4*(p : ℚ))
def smallPart (p : ℕ) : ℚ := (if p=2 then 1/8 else 1) *
  (if p=3 then 1/3 else 1) * (if p=5 then 4/5 else 1)
def step (p e : ℕ) : ℚ := (p:ℚ)^(e-1) * (if p≤5 then 1 else localFactor p)
def cost (n : ℕ) : ℚ := ∏ p ∈ n.primeFactors, step p (n.factorization p)
def ratio (n : ℕ) : ℚ := (n.totient:ℚ)^2 / (4^n.primeFactors.card * n)

theorem local_ge_one {p : ℕ} (hp : p.Prime) (h : 5<p) : 1 ≤ localFactor p := by
  have h7 : 7 ≤ p := by
    by_contra! hh; have : p=6 := by omega
    subst p; exact (by decide : ¬ Nat.Prime 6) hp
  have hq : (7:ℚ) ≤ p := by exact_mod_cast h7
  unfold localFactor
  rw [Nat.cast_sub (by omega : 1≤p),Nat.cast_one,le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hq)]

theorem step_ge_pow {p : ℕ} (hp : p.Prime) (e : ℕ) : (p:ℚ)^(e-1) ≤ step p e := by
  unfold step; split_ifs with h
  · simp
  · exact le_mul_of_one_le_right (by positivity) (local_ge_one hp (by omega))

theorem step_ge_one {p : ℕ} (hp : p.Prime) (e : ℕ) : 1 ≤ step p e :=
  (one_le_pow₀ (by exact_mod_cast hp.one_le)).trans (step_ge_pow hp e)

theorem local_split {p : ℕ} (hp : p.Prime) (e : ℕ) :
    smallPart p * step p e = (p:ℚ)^(e-1)*localFactor p := by
  by_cases h : p≤5
  · interval_cases p <;> norm_num [smallPart,step,localFactor] at *
    all_goals ring
  · simp [step,smallPart,h,show p≠2 by omega,show p≠3 by omega,show p≠5 by omega]

theorem min_small (s : Finset ℕ) : (1:ℚ)/30 ≤ ∏ p ∈ s, smallPart p := by
  simp only [smallPart, prod_mul_distrib, prod_ite_eq']
  split_ifs <;> norm_num

theorem ratio_eq {n : ℕ} (hn : n≠0) :
    ratio n = (∏ p ∈ n.primeFactors, smallPart p) * cost n := by
  have hf : (n.totient:ℚ) = ∏ p ∈ n.primeFactors,
      ((p:ℚ)^(n.factorization p-1) * (p-1 : ℕ)) := by
    exact_mod_cast (Nat.totient_eq_prod_factorization hn)
  have hd : (n:ℚ) = ∏ p ∈ n.primeFactors, (p:ℚ)^n.factorization p := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn)
  unfold ratio cost
  rw [hf, ← prod_pow]
  nth_rw 1 [hd]
  rw [← Finset.prod_const (s := n.primeFactors) (b := (4:ℚ)), ← prod_mul_distrib,
    ← prod_div_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun p hp => ?_
  rw [local_split (Nat.prime_of_mem_primeFactors hp)]
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).ne'
  rw [hk, Nat.succ_sub_one, pow_succ (p:ℚ) k]
  unfold localFactor
  have h₀ : (p:ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'
  field_simp

theorem cost_lt {n : ℕ} (hn : 0<n) (hbad : n.totient^2 < 16*4^n.primeFactors.card*n) :
    cost n < 480 := by
  have hr : ratio n < 16 := by
    apply (div_lt_iff₀ (show 0 < (4:ℚ)^n.primeFactors.card*n by positivity)).mpr
    exact_mod_cast (by simpa [mul_assoc] using hbad : n.totient^2 < 16*(4^n.primeFactors.card*n))
  rw [ratio_eq hn.ne'] at hr
  have hc : 0 ≤ cost n := Finset.prod_nonneg fun p hp =>
    (step_ge_one (Nat.prime_of_mem_primeFactors hp) _).trans' (by norm_num)
  nlinarith [mul_nonneg (sub_nonneg.mpr (min_small n.primeFactors)) hc]

theorem step_le_cost {n p : ℕ} (hp : p ∈ n.primeFactors) :
    step p (n.factorization p) ≤ cost n := by
  have hs : {p} ⊆ n.primeFactors := Finset.singleton_subset_iff.mpr hp
  simpa [cost] using Finset.prod_le_prod_of_subset_of_one_le
    (f := fun q => step q (n.factorization q)) hs
    (fun q hq => (show 0 ≤ (1:ℚ) by norm_num).trans
      (step_ge_one (Nat.prime_of_mem_primeFactors (hs hq)) _))
    (fun q hq _ => step_ge_one (Nat.prime_of_mem_primeFactors hq) _)

theorem factor_bounds {n p : ℕ} (hp : p ∈ n.primeFactors) (hcost : cost n < 480) :
    p < 1922 ∧ n.factorization p < 10 := by
  have hs := (step_le_cost hp).trans_lt hcost
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpow := (step_ge_pow hprime (n.factorization p)).trans_lt hs
  constructor
  · by_contra! hh
    have hq : (1922:ℚ) ≤ p := by exact_mod_cast hh
    have hp0 : 0 < (p:ℚ) := by linarith
    have hge : 480 ≤ localFactor p := by
      unfold localFactor
      rw [Nat.cast_sub (by omega : 1≤p),Nat.cast_one,le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hq)]
    have hle : localFactor p ≤ step p (n.factorization p) := by
      rw [step,if_neg (by omega : ¬p≤5)]
      exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by exact_mod_cast hprime.one_le))
    linarith
  · by_contra! hh
    have h₁ : (2:ℚ)^9 ≤ (p:ℚ)^9 :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hprime.two_le) _
    have h₂ : (p:ℚ)^9 ≤ (p:ℚ)^(n.factorization p-1) :=
      pow_le_pow_right₀ (by exact_mod_cast hprime.one_le) (by omega)
    norm_num at h₁
    linarith

def budgetFactor (p e : ℕ) : ℚ := if e=0 then 1 else step p e

def candidates : List ℕ → ℚ → List ℕ
  | [], _ => [1]
  | p::ps, b => (List.range 10).flatMap fun e =>
      if budgetFactor p e < b then
        (candidates ps (b/budgetFactor p e)).map (p^e * ·)
      else []

theorem candidates_complete (ps : List ℕ) (e : ℕ → ℕ) (b : ℚ)
    (he : ∀ p ∈ ps, e p < 10) (hf : ∀ p ∈ ps, 1 ≤ budgetFactor p (e p))
    (hb : (ps.map (fun p => budgetFactor p (e p))).prod < b) :
    (ps.map (fun p => p^(e p))).prod ∈ candidates ps b := by
  induction ps generalizing b with
  | nil => simp [candidates]
  | cons p ps ih =>
    let w := budgetFactor p (e p)
    have hw : 1≤w := hf p (by simp)
    have ht : 1 ≤ (ps.map (fun q => budgetFactor q (e q))).prod := by
      apply List.one_le_prod
      intro z hz
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
      exact hf q (by simp [hq])
    have hw₀ : 0<w := by linarith
    change w * (ps.map (fun q => budgetFactor q (e q))).prod < b at hb
    have hwlt : w<b := lt_of_le_of_lt (le_mul_of_one_le_right hw₀.le ht) hb
    apply List.mem_flatMap.mpr
    refine ⟨e p,List.mem_range.mpr (he p (by simp)),?_⟩
    rw [if_pos hwlt]
    apply List.mem_map.mpr
    refine ⟨_,ih _ (fun q hq => he q (by simp [hq])) (fun q hq => hf q (by simp [hq])) ?_,rfl⟩
    exact (lt_div_iff₀ hw₀).mpr (by simpa [mul_comm] using hb)

def sievePrimes := ((List.range 1922).filter Nat.Prime).reverse

def fastTotient (n : ℕ) : ℕ :=
  if n=0 then 0 else n.factorization.prod fun p k => p^(k-1)*(p-1)

theorem fastTotient_eq (n : ℕ) : fastTotient n = n.totient := by
  by_cases hn : n=0
  · simp [fastTotient, hn]
  · simpa [fastTotient,hn] using (Nat.totient_eq_prod_factorization hn).symm

def exceptions := (candidates sievePrimes 480).filter fun n =>
  decide (0<n ∧ (fastTotient n)^2 < 16*4^n.primeFactors.card*n)

theorem exceptions_iff (n : ℕ) : n ∈ exceptions ↔
    0<n ∧ n.totient^2 < 16*4^n.primeFactors.card*n := by
  rw [exceptions,List.mem_filter]
  simp only [decide_eq_true_eq,fastTotient_eq,and_iff_right_iff_imp]
  rintro ⟨hn,hbad⟩
  have hcost := cost_lt hn hbad
  have hnodup : sievePrimes.Nodup := List.nodup_reverse.mpr (List.Nodup.filter _ List.nodup_range)
  have hsub : n.primeFactors ⊆ sievePrimes.toFinset := by
    intro p hp
    simpa [sievePrimes] using And.intro (factor_bounds hp hcost).1 (Nat.prime_of_mem_primeFactors hp)
  have hz (p : ℕ) (h : p ∉ n.primeFactors) : n.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (show p ∉ n.factorization.support from h)
  have hprod : (sievePrimes.map (fun p => p^(n.factorization p))).prod = n := by
    rw [← List.prod_toFinset _ hnodup, ← Finset.prod_subset hsub (fun x _ hx => by simp [hz x hx])]
    exact (Nat.prod_primeFactors_pow_factorization hn.ne').symm
  rw [← hprod]
  apply candidates_complete sievePrimes (fun p => n.factorization p)
  · intro p _
    by_cases hp : p ∈ n.primeFactors
    · exact (factor_bounds hp hcost).2
    · simp [hz p hp]
  · intro p hp
    have hprime : p.Prime := (show p < 1922 ∧ p.Prime by simpa [sievePrimes] using hp).2
    unfold budgetFactor
    split_ifs
    · exact le_rfl
    · exact step_ge_one hprime _
  · rw [← List.prod_toFinset _ hnodup, ← Finset.prod_subset hsub (fun x _ hx => by simp [budgetFactor,hz x hx])]
    convert hcost using 1
    unfold cost
    apply Finset.prod_congr rfl
    intro p hp
    have he := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hp)
    simp [budgetFactor,he.ne']

def graphM (n : ℕ) : ℕ := 1+Nat.sqrt ((2^n.primeFactors.card-1)^2*(n+1))

theorem floor_graphM (n : ℕ) : ⌊1+((2:ℝ)^n.primeFactors.card-1)*Real.sqrt (n+1:ℕ)⌋₊ = graphM n := by
  let w : ℕ := 2^n.primeFactors.card-1
  have hw₁ : 1≤(2:ℕ)^n.primeFactors.card := Nat.one_le_pow _ _ (by decide)
  have hw : (w : ℝ) = (2:ℝ)^n.primeFactors.card-1 := by
    simp [w,Nat.cast_sub hw₁]
  rw [← hw, show (w:ℝ)*Real.sqrt (n+1:ℕ) = Real.sqrt ((w^2*(n+1):ℕ):ℝ) by
    rw [Nat.cast_mul,Nat.cast_pow,Real.sqrt_mul (by positivity),Real.sqrt_sq (by positivity)]]
  rw [add_comm,Nat.floor_add_one (by positivity), Real.nat_floor_real_sqrt_eq_nat_sqrt]
  simp [w,graphM,Nat.add_comm]

theorem graph_bad_implies_bad {n : ℕ} (hn : 2≤n) (h : n.totient < 3*graphM n+1) :
    n.totient^2 < 16*4^n.primeFactors.card*n := by
  let W := (2:ℕ)^n.primeFactors.card
  let w := W-1
  let s := Nat.sqrt (w^2*(n+1))
  have hW : 1 ≤ W := Nat.one_le_pow _ _ (by decide)
  have hcast : (w:ℝ) = W-1 := by simp [w,Nat.cast_sub hW]
  have hs : (s:ℝ)^2 ≤ (w:ℝ)^2*((n:ℝ)+1) := by exact_mod_cast (Nat.sqrt_le' (w^2*(n+1)))
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hroot := Real.sq_sqrt (show 0≤(n:ℝ) by positivity)
  have hroot₁ : 1 ≤ Real.sqrt n := by nlinarith [Real.sqrt_nonneg (n:ℝ)]
  have hh : (3*(s:ℝ))^2 ≤ (4*(w:ℝ)*Real.sqrt n)^2 := by
    simp only [mul_pow,hroot]
    nlinarith [mul_nonneg (sq_nonneg (w:ℝ)) (show 0≤7*(n:ℝ)-9 by linarith)]
  have hbound := (sq_le_sq₀ (by positivity) (by positivity)).mp hh
  have hnum : n.totient < 3*s+4 := by change n.totient < 3*(1+s)+1 at h; omega
  have hr : (n.totient:ℝ) < 4*(W:ℝ)*Real.sqrt n := by
    have hh' : (n.totient:ℝ) < 3*(s:ℝ)+4 := by exact_mod_cast hnum
    rw [hcast] at hbound
    nlinarith
  have hsq := (sq_lt_sq₀ (by positivity) (by positivity)).mpr hr
  have hWsq : W^2 = 4^n.primeFactors.card := by
    dsimp [W]; rw [← pow_mul,Nat.mul_comm, pow_mul]; norm_num
  simp only [mul_pow,hroot] at hsq
  have hWreal : (W:ℝ)^2 = 4^n.primeFactors.card := by exact_mod_cast hWsq
  rw [hWreal] at hsq
  norm_num at hsq
  exact_mod_cast hsq

def fieldExceptions := (exceptions.filter fun n => decide
  (7<n+1 ∧ fastTotient n < 3*graphM n+1 ∧ (n+1).primeFactors.card=1)).map (·+1)

theorem fieldExceptions_iff (n : ℕ) : n+1 ∈ fieldExceptions ↔
    7<n+1 ∧ n.totient < 3*graphM n+1 ∧ IsPrimePow (n+1) := by
  simp only [fieldExceptions,List.mem_map,List.mem_filter,decide_eq_true_eq,Nat.add_left_inj,
    exists_eq_right,fastTotient_eq,exceptions_iff,isPrimePow_iff_card_primeFactors_eq_one]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨by omega,graph_bad_implies_bad (by omega) h.2.1⟩,h⟩

end SunSieve


namespace SunSieve
open Finset
/-- Integer numerator and denominator of the relaxed local factor. -/
def up (p e : Nat) : Nat :=
  if e=0 then 1 else p^(e-1)*(if p≤5 then 1 else (p-1)^2)
def down (p e : Nat) : Nat := if e=0 ∨ p≤5 then 1 else 4*p
def phiPart (p e : Nat) : Nat := if e=0 then 1 else p^(e-1)*(p-1)
def wPart (e : Nat) : Nat := if e=0 then 1 else 2

theorem down_pos {p e : Nat} : 0<down p e := by unfold down; split_ifs <;> omega
theorem budget_eq (p e : Nat) : budgetFactor p e = (up p e : ℚ)/(down p e : ℚ) := by
  by_cases he : e=0 <;> by_cases hp : p≤5 <;> simp [budgetFactor,step,localFactor,up,down,he,hp,mul_div_assoc]

theorem cutoff {p q e : Nat} (hp : 5<p) (hle : p≤q) (he : e≠0) :
    ((p-2:ℕ):ℚ)/4 ≤ budgetFactor q e := by
  have hq : ¬q≤5 := by omega
  have hq₀ : 0<(q:ℚ) := by exact_mod_cast (by omega : 0<q)
  have hq₁ : 1≤(q:ℚ) := by exact_mod_cast (by omega : 1≤q)
  have hlocal : ((p-2:ℕ):ℚ)/4 ≤ localFactor q := by
    unfold localFactor
    rw [Nat.cast_sub (by omega : 2≤p),Nat.cast_sub (by omega : 1≤q),le_div_iff₀ (by positivity)]
    push_cast
    have hle' : (p:ℚ)≤q := by exact_mod_cast hle
    nlinarith [mul_nonneg (sub_nonneg.mpr hle') hq₀.le]
  exact hlocal.trans (by simp only [budgetFactor,he,if_false,step,hq]
                         exact le_mul_of_one_le_left (by unfold localFactor; positivity) (one_le_pow₀ hq₁))

structure Node where
  value : Nat
  phi : Nat
  w : Nat
deriving DecidableEq, Repr

def Node.take (s : Node) (p e : Nat) : Node :=
  ⟨s.value*p^e,s.phi*phiPart p e,s.w*wPart e⟩

def visit (leaf : Node → Bool) : List Nat → Nat → Nat → Node → Bool
  | [], _, _, s => leaf s
  | p::ps, u,v,s =>
    if 5<p ∧ 4*u ≤ (p-2)*v then leaf s else
      (List.range 10).all fun e =>
        if up p e*v < u*down p e then
          visit leaf ps (u*down p e) (v*up p e) (s.take p e)
        else true

def finish (s : Node) (ps : List Nat) (e : Nat → Nat) : Node :=
  ⟨s.value * (ps.map fun q => q^(e q)).prod,
   s.phi * (ps.map fun q => phiPart q (e q)).prod,
   s.w * (ps.map fun q => wPart (e q)).prod⟩

theorem finish_cons (s : Node) (p : Nat) (ps : List Nat) (e : Nat → Nat) :
    finish s (p::ps) e = finish (s.take p (e p)) ps e := by
  simp [finish,Node.take,Nat.mul_assoc]

theorem finish_zero (s : Node) (ps : List Nat) (e : Nat → Nat) (hz : ∀ q∈ps,e q=0) :
    finish s ps e = s := by
  induction ps generalizing s with
  | nil => simp [finish]
  | cons p ps ih =>
    rw [finish_cons,ih _ (fun q hq => hz q (by simp [hq]))]
    simp [Node.take,hz p (by simp),phiPart,wPart]

theorem single_weight (ps : List Nat) (e : Nat → Nat)
    (hpos : ∀ q∈ps,1≤budgetFactor q (e q)) {p : Nat} (hp : p∈ps) :
    budgetFactor p (e p) ≤ (ps.map (fun q => budgetFactor q (e q))).prod := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    have ht : 1 ≤ (ps.map (fun r => budgetFactor r (e r))).prod := by
      apply List.one_le_prod; intro z hz
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hz; exact hpos r (by simp [hr])
    simp only [List.map_cons,List.prod_cons]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_mul_of_one_le_right (by linarith [hpos p (by simp)]) ht
    · exact (ih (fun r hr => hpos r (by simp [hr])) hp).trans
        (le_mul_of_one_le_left (by linarith) (hpos q (by simp)))

theorem visit_sound (leaf : Node → Bool) (ps : List Nat) (u v : Nat) (s : Node) (e : Nat → Nat)
    (hsort : ps.Pairwise (·≤·)) (hpos : ∀ q∈ps,1≤budgetFactor q (e q))
    (he : ∀ q∈ps,e q<10) (hv : 0<v)
    (hb : (ps.map (fun q => budgetFactor q (e q))).prod * (v:ℚ) < u)
    (hcheck : visit leaf ps u v s = true) : leaf (finish s ps e) = true := by
  induction ps generalizing s u v with
  | nil => simpa [visit,finish] using hcheck
  | cons p ps ih =>
    by_cases hstop : 5<p ∧ 4*u ≤ (p-2)*v
    · have hz : ∀ q∈p::ps,e q=0 := by
        intro q hq
        by_contra hne
        have hle : p≤q := by rcases List.mem_cons.mp hq with rfl | ht; exact le_rfl; exact (List.pairwise_cons.mp hsort).1 q ht
        have hl := (cutoff hstop.1 hle hne).trans (single_weight _ _ hpos hq)
        have hstop' : (4:ℚ)*u ≤ (p-2:ℕ)*(v:ℚ) := by exact_mod_cast hstop.2
        nlinarith [mul_nonneg (sub_nonneg.mpr hl) (show 0≤(v:ℚ) by positivity)]
      rw [finish_zero _ _ _ hz]
      simpa [visit,hstop] using hcheck
    · simp only [visit,if_neg hstop,List.all_eq_true] at hcheck
      have hw := single_weight _ _ hpos (List.mem_cons_self ..)
      have hw' := (mul_le_mul_of_nonneg_right hw (show 0≤(v:ℚ) by positivity)).trans_lt hb
      rw [budget_eq] at hw'
      have hd : 0<(down p (e p):ℚ) := by exact_mod_cast (@down_pos p (e p))
      have htest : up p (e p)*v < u*down p (e p) := by
        exact_mod_cast ((div_lt_iff₀ hd).mp (by simpa [div_mul_eq_mul_div] using hw' :
          ((up p (e p):ℚ)*v)/down p (e p)<u))
      have hrun := hcheck (e p) (List.mem_range.mpr (he p (by simp)))
      rw [if_pos htest] at hrun
      rw [finish_cons]
      apply ih _ _ _ (List.pairwise_cons.mp hsort).2 (fun q hq => hpos q (by simp [hq]))
        (fun q hq => he q (by simp [hq])) _ _ hrun
      · have hp' := hpos p (by simp)
        rw [budget_eq] at hp'
        have : (0:ℚ)<up p (e p) := (div_pos_iff_of_pos_right hd).mp (by linarith)
        exact Nat.mul_pos hv (by exact_mod_cast this)
      · simp only [List.map_cons,List.prod_cons,budget_eq p (e p)] at hb
        push_cast
        field_simp [hd.ne'] at hb
        linarith only [show (up p (e p):ℚ) * (ps.map (fun q => budgetFactor q (e q))).prod * v <
          u*down p (e p) by linarith only [hb]]

inductive KeyTree where
  | nil
  | node (k : Nat) (l r : KeyTree)
deriving Inhabited

def KeyTree.has : KeyTree → Nat → Bool
  | .nil,_ => false
  | .node k l r,q => if q<k then l.has q else if k<q then r.has q else true

def KeyTree.keys : KeyTree → List Nat
  | .nil => []
  | .node k l r => l.keys ++ k::r.keys

theorem KeyTree.mem_of_has (t : KeyTree) (q : Nat) (h : t.has q) : q∈t.keys := by
  induction t with
  | nil => simp [has] at h
  | node k l r hl hr =>
    simp only [has] at h
    simp only [keys,List.mem_append,List.mem_cons]
    split at h
    · exact Or.inl (hl h)
    · split at h
      · exact Or.inr (Or.inr (hr h))
      · exact Or.inr (Or.inl (by omega))

def seekDiv (q : Nat) : Nat → Nat → Nat
  | 0,_ => 1
  | f+1,d => if q%d=0 then d else if q<d*d then 1 else seekDiv q f (d+1)

def splitWitness (q : Nat) : Bool :=
  let d := Nat.gcd q ((seekDiv q 6000 2)^32)
  let c := q/d
  decide (1<d ∧ 1<c ∧ d*c=q ∧ Nat.gcd d c=1)

theorem splitWitness_sound {q : Nat} (hs : splitWitness q) : ¬IsPrimePow q := by
  intro hpow
  let d := Nat.gcd q ((seekDiv q 6000 2)^32)
  let c := q/d
  have hh : 1<d ∧ 1<c ∧ d*c=q ∧ d.Coprime c := of_decide_eq_true hs
  have hd := hh.2.2.2.isPrimePow_dvd_mul hpow
  obtain h|h := hd.mp (hh.2.2.1 ▸ dvd_rfl)
  · have hle := Nat.le_of_dvd (by omega : 0<d) h
    have hlt : d < d*c := by simpa using Nat.mul_lt_mul_of_pos_left hh.2.1 (by omega : 0<d)
    omega
  · have hle := Nat.le_of_dvd (by omega : 0<c) h
    have hlt : c < d*c := by simpa using Nat.mul_lt_mul_of_pos_right hh.1 (by omega : 0<c)
    omega

def leafTest (t : KeyTree) (s : Node) : Bool :=
  let q := s.value+1
  let cutoff := (s.phi - 4)/3+1
  decide (q≤7) || (decide (4 ≤ s.phi) && decide ((s.w-1)^2*q < cutoff^2)) || t.has q || splitWitness q

theorem leafTest_sound {t : KeyTree} {n : Nat} (h : leafTest t ⟨n,n.totient,2^n.primeFactors.card⟩)
    (hb : 7<n+1 ∧ n.totient < 3*graphM n+1 ∧ IsPrimePow (n+1)) : n+1 ∈ t.keys := by
  simp only [leafTest,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ((h|⟨hφ,hs⟩)|h)|h
  · omega
  · have hlt : Nat.sqrt ((2^n.primeFactors.card-1)^2*(n+1)) < (n.totient-4)/3+1 := Nat.sqrt_lt.mpr (by simpa only [← pow_two] using hs)
    unfold graphM at hb
    omega
  · exact t.mem_of_has _ h
  · exact (splitWitness_sound h hb.2.2).elim

theorem universal_coverage (t : KeyTree) (ps : List Nat)
    (hprimes : ps = sievePrimes.reverse) (hsort : ps.Pairwise (·≤·))
    (test : visit (leafTest t) ps 480 1 ⟨1,1,1⟩)
    {n : Nat} (hb : n+1 ∈ fieldExceptions) : n+1 ∈ t.keys := by
  have hfield := (fieldExceptions_iff n).mp hb
  have hn : 0<n := by omega
  have hc := cost_lt hn (graph_bad_implies_bad (by omega) hfield.2.1)
  have hdu : ps.Nodup := by rw [hprimes]; simp only [sievePrimes,List.reverse_reverse]; exact List.Nodup.filter _ List.nodup_range
  have hmem (p : Nat) : p ∈ ps ↔ p<1922 ∧ p.Prime := by simp [hprimes,sievePrimes]
  have hsub : n.primeFactors ⊆ ps.toFinset := by
    intro p hp
    exact List.mem_toFinset.mpr ((hmem p).mpr ⟨(factor_bounds hp hc).1,Nat.prime_of_mem_primeFactors hp⟩)
  have hz {p : Nat} (h : p ∉ n.primeFactors) : n.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (show p ∉ n.factorization.support from h)
  have hpos {p : Nat} (hp : p ∈ n.primeFactors) : n.factorization p ≠ 0 :=
    ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hp)).ne'
  have reduce (f : Nat → Nat → Nat) (h₀ : ∀ q, f q 0=1) :
      (ps.map (fun p => f p (n.factorization p))).prod =
      ∏ p ∈ n.primeFactors,f p (n.factorization p) := by
    rw [← List.prod_toFinset _ hdu,← Finset.prod_subset hsub (fun x _ hx => by rw [hz hx,h₀])]
  have result := visit_sound (leafTest t) ps 480 1 ⟨1,1,1⟩ (fun p => n.factorization p) hsort
    (fun p hp => by unfold budgetFactor; split_ifs; exact le_rfl; exact step_ge_one ((hmem p).mp hp).2 _)
    (fun p hp => by by_cases h : p∈n.primeFactors; exact (factor_bounds h hc).2; simp [hz h])
    (by decide) (by
      simp only [Nat.cast_one,mul_one,Nat.cast_ofNat]
      rw [← List.prod_toFinset _ hdu, ← Finset.prod_subset hsub (fun x _ hx => by simp [budgetFactor,hz hx])]
      convert hc using 1
      unfold cost; apply prod_congr rfl; intro p hp; simp [budgetFactor,hpos hp]) test
  have hv := reduce (fun p e => p^e) (by simp)
  have hφ := reduce phiPart (by simp [phiPart])
  have hw := reduce (fun _ e => wPart e) (by simp [wPart])
  rw [← Nat.prod_primeFactors_pow_factorization hn.ne'] at hv
  have hφ' : (ps.map (fun p => phiPart p (n.factorization p))).prod = n.totient := by
    rw [hφ,Nat.totient_eq_prod_factorization hn.ne',Nat.prod_factorization_eq_prod_primeFactors]
    apply prod_congr rfl; intro p hp; simp [phiPart,hpos hp]
  have hw' : (ps.map (fun p => wPart (n.factorization p))).prod = 2^n.primeFactors.card := by
    rw [hw,← Finset.prod_const (s:=n.primeFactors) (b:=2)]
    apply prod_congr rfl; intro p hp; simp [wPart,hpos hp]
  apply leafTest_sound _ hfield
  simpa only [finish,one_mul,hv,hφ',hw'] using result

end SunSieve

namespace SunSieve
theorem visit_small (p : Nat) (hp : p≤5) (leaf : Node → Bool) (ps : List Nat)
    (u v : Nat) (s : Node)
    (h : ∀ i : Fin 10, up p i.val*v < u*down p i.val →
      visit leaf ps (u*down p i.val) (v*up p i.val) (s.take p i.val)) :
    visit leaf (p::ps) u v s := by
  rw [visit,if_neg (by omega),List.all_eq_true]
  intro i hi
  split_ifs with he
  · exact h ⟨i,List.mem_range.mp hi⟩ he
  · rfl

end SunSieve

open SunSieve
namespace SunSieveLiteral
def t61 : KeyTree := (.node 61 (.node 27 (.node 16 (.node 11 (.node 9 (.node 8 .nil .nil) .nil) (.node 13 .nil .nil)) (.node 23 (.node 19 (.node 17 .nil .nil) .nil) (.node 25 .nil .nil))) (.node 43 (.node 37 (.node 31 (.node 29 .nil .nil) .nil) (.node 41 .nil .nil)) (.node 53 (.node 49 (.node 47 .nil .nil) .nil) (.node 59 .nil .nil)))) (.node 101 (.node 79 (.node 71 (.node 67 (.node 64 .nil .nil) .nil) (.node 73 .nil .nil)) (.node 89 (.node 83 (.node 81 .nil .nil) .nil) (.node 97 .nil .nil))) (.node 121 (.node 109 (.node 107 (.node 103 .nil .nil) .nil) (.node 113 .nil .nil)) (.node 127 (.node 125 .nil .nil) (.node 131 .nil .nil)))))
def t233 : KeyTree := (.node 233 (.node 181 (.node 163 (.node 151 (.node 149 (.node 139 .nil .nil) .nil) (.node 157 .nil .nil)) (.node 173 (.node 169 (.node 167 .nil .nil) .nil) (.node 179 .nil .nil))) (.node 211 (.node 197 (.node 193 (.node 191 .nil .nil) .nil) (.node 199 .nil .nil)) (.node 227 (.node 223 .nil .nil) (.node 229 .nil .nil)))) (.node 281 (.node 256 (.node 243 (.node 241 (.node 239 .nil .nil) .nil) (.node 251 .nil .nil)) (.node 271 (.node 269 (.node 263 .nil .nil) .nil) (.node 277 .nil .nil))) (.node 311 (.node 293 (.node 289 (.node 283 .nil .nil) .nil) (.node 307 .nil .nil)) (.node 317 (.node 313 .nil .nil) (.node 331 .nil .nil)))))
def t137 : KeyTree := (.node 137 t61 t233)
def t461 : KeyTree := (.node 461 (.node 409 (.node 367 (.node 353 (.node 349 (.node 343 .nil .nil) .nil) (.node 361 .nil .nil)) (.node 397 (.node 379 (.node 373 .nil .nil) .nil) (.node 401 .nil .nil))) (.node 439 (.node 431 (.node 421 (.node 419 .nil .nil) .nil) (.node 433 .nil .nil)) (.node 449 (.node 443 .nil .nil) (.node 457 .nil .nil)))) (.node 571 (.node 521 (.node 491 (.node 487 (.node 463 .nil .nil) .nil) (.node 499 .nil .nil)) (.node 541 (.node 529 (.node 523 .nil .nil) .nil) (.node 547 .nil .nil))) (.node 613 (.node 601 (.node 599 (.node 577 .nil .nil) .nil) (.node 607 .nil .nil)) (.node 619 (.node 617 .nil .nil) (.node 625 .nil .nil)))))
def t811 : KeyTree := (.node 811 (.node 727 (.node 673 (.node 659 (.node 647 (.node 643 .nil .nil) .nil) (.node 661 .nil .nil)) (.node 701 (.node 691 (.node 683 .nil .nil) .nil) (.node 709 .nil .nil))) (.node 751 (.node 739 (.node 733 (.node 729 .nil .nil) .nil) (.node 743 .nil .nil)) (.node 761 (.node 757 .nil .nil) (.node 787 .nil .nil)))) (.node 883 (.node 841 (.node 827 (.node 823 (.node 821 .nil .nil) .nil) (.node 829 .nil .nil)) (.node 877 (.node 859 (.node 853 .nil .nil) .nil) (.node 881 .nil .nil))) (.node 941 (.node 919 (.node 911 (.node 907 .nil .nil) .nil) (.node 937 .nil .nil)) (.node 953 (.node 947 .nil .nil) (.node 961 .nil .nil)))))
def t631 : KeyTree := (.node 631 t461 t811)
def t337 : KeyTree := (.node 337 t137 t631)
def t1117 : KeyTree := (.node 1117 (.node 1039 (.node 1013 (.node 997 (.node 991 (.node 971 .nil .nil) .nil) (.node 1009 .nil .nil)) (.node 1031 (.node 1024 (.node 1021 .nil .nil) .nil) (.node 1033 .nil .nil))) (.node 1087 (.node 1063 (.node 1061 (.node 1051 .nil .nil) .nil) (.node 1069 .nil .nil)) (.node 1093 (.node 1091 .nil .nil) (.node 1103 .nil .nil)))) (.node 1231 (.node 1171 (.node 1151 (.node 1129 (.node 1123 .nil .nil) .nil) (.node 1163 .nil .nil)) (.node 1213 (.node 1201 (.node 1181 .nil .nil) .nil) (.node 1223 .nil .nil))) (.node 1279 (.node 1259 (.node 1249 (.node 1237 .nil .nil) .nil) (.node 1277 .nil .nil)) (.node 1291 (.node 1289 .nil .nil) (.node 1301 .nil .nil)))))
def t1511 : KeyTree := (.node 1511 (.node 1429 (.node 1369 (.node 1331 (.node 1327 (.node 1321 .nil .nil) .nil) (.node 1361 .nil .nil)) (.node 1423 (.node 1399 (.node 1381 .nil .nil) .nil) (.node 1427 .nil .nil))) (.node 1481 (.node 1453 (.node 1451 (.node 1447 .nil .nil) .nil) (.node 1471 .nil .nil)) (.node 1489 (.node 1483 .nil .nil) (.node 1499 .nil .nil)))) (.node 1607 (.node 1567 (.node 1549 (.node 1543 (.node 1531 .nil .nil) .nil) (.node 1559 .nil .nil)) (.node 1583 (.node 1579 (.node 1571 .nil .nil) .nil) (.node 1597 .nil .nil))) (.node 1657 (.node 1621 (.node 1613 (.node 1609 .nil .nil) .nil) (.node 1627 .nil .nil)) (.node 1667 (.node 1663 .nil .nil) (.node 1669 .nil .nil)))))
def t1303 : KeyTree := (.node 1303 t1117 t1511)
def t1861 : KeyTree := (.node 1861 (.node 1777 (.node 1723 (.node 1709 (.node 1699 (.node 1693 .nil .nil) .nil) (.node 1721 .nil .nil)) (.node 1753 (.node 1747 (.node 1741 .nil .nil) .nil) (.node 1759 .nil .nil))) (.node 1811 (.node 1789 (.node 1787 (.node 1783 .nil .nil) .nil) (.node 1801 .nil .nil)) (.node 1847 (.node 1831 .nil .nil) (.node 1849 .nil .nil)))) (.node 1973 (.node 1879 (.node 1873 (.node 1871 (.node 1867 .nil .nil) .nil) (.node 1877 .nil .nil)) (.node 1933 (.node 1931 (.node 1901 .nil .nil) .nil) (.node 1951 .nil .nil))) (.node 2003 (.node 1993 (.node 1987 (.node 1979 .nil .nil) .nil) (.node 1999 .nil .nil)) (.node 2017 (.node 2011 .nil .nil) (.node 2029 .nil .nil)))))
def t2221 : KeyTree := (.node 2221 (.node 2137 (.node 2089 (.node 2083 (.node 2081 (.node 2069 .nil .nil) .nil) (.node 2087 .nil .nil)) (.node 2129 (.node 2113 (.node 2111 .nil .nil) .nil) (.node 2131 .nil .nil))) (.node 2197 (.node 2161 (.node 2143 (.node 2141 .nil .nil) .nil) (.node 2179 .nil .nil)) (.node 2209 (.node 2203 .nil .nil) (.node 2213 .nil .nil)))) (.node 2341 (.node 2287 (.node 2269 (.node 2251 (.node 2239 .nil .nil) .nil) (.node 2281 .nil .nil)) (.node 2311 (.node 2297 (.node 2293 .nil .nil) .nil) (.node 2339 .nil .nil))) (.node 2381 (.node 2371 (.node 2351 (.node 2347 .nil .nil) .nil) (.node 2377 .nil .nil)) (.node 2389 (.node 2383 .nil .nil) (.node 2401 .nil .nil)))))
def t2053 : KeyTree := (.node 2053 t1861 t2221)
def t1681 : KeyTree := (.node 1681 t1303 t2053)
def t967 : KeyTree := (.node 967 t337 t1681)
def t2683 : KeyTree := (.node 2683 (.node 2549 (.node 2473 (.node 2441 (.node 2437 (.node 2423 .nil .nil) .nil) (.node 2467 .nil .nil)) (.node 2531 (.node 2521 (.node 2503 .nil .nil) .nil) (.node 2539 .nil .nil))) (.node 2621 (.node 2591 (.node 2557 (.node 2551 .nil .nil) .nil) (.node 2617 .nil .nil)) (.node 2671 (.node 2659 (.node 2647 .nil .nil) .nil) (.node 2677 .nil .nil)))) (.node 2791 (.node 2719 (.node 2711 (.node 2707 (.node 2689 .nil .nil) .nil) (.node 2713 .nil .nil)) (.node 2749 (.node 2741 (.node 2731 .nil .nil) .nil) (.node 2767 .nil .nil))) (.node 2833 (.node 2803 (.node 2801 (.node 2797 .nil .nil) .nil) (.node 2809 .nil .nil)) (.node 2857 (.node 2851 .nil .nil) (.node 2861 .nil .nil)))))
def t3191 : KeyTree := (.node 3191 (.node 3061 (.node 3011 (.node 2971 (.node 2953 (.node 2927 .nil .nil) .nil) (.node 3001 .nil .nil)) (.node 3041 (.node 3037 (.node 3019 .nil .nil) .nil) (.node 3049 .nil .nil))) (.node 3163 (.node 3109 (.node 3079 (.node 3067 .nil .nil) .nil) (.node 3121 .nil .nil)) (.node 3181 (.node 3169 .nil .nil) (.node 3187 .nil .nil)))) (.node 3313 (.node 3253 (.node 3229 (.node 3221 (.node 3217 .nil .nil) .nil) (.node 3251 .nil .nil)) (.node 3301 (.node 3271 (.node 3259 .nil .nil) .nil) (.node 3307 .nil .nil))) (.node 3373 (.node 3343 (.node 3331 (.node 3319 .nil .nil) .nil) (.node 3361 .nil .nil)) (.node 3433 (.node 3391 .nil .nil) (.node 3463 .nil .nil)))))
def t2887 : KeyTree := (.node 2887 t2683 t3191)
def t3709 : KeyTree := (.node 3709 (.node 3583 (.node 3529 (.node 3511 (.node 3499 (.node 3481 .nil .nil) .nil) (.node 3517 .nil .nil)) (.node 3559 (.node 3547 (.node 3541 .nil .nil) .nil) (.node 3571 .nil .nil))) (.node 3643 (.node 3631 (.node 3613 (.node 3607 .nil .nil) .nil) (.node 3637 .nil .nil)) (.node 3691 (.node 3673 .nil .nil) (.node 3697 .nil .nil)))) (.node 3853 (.node 3769 (.node 3733 (.node 3727 (.node 3721 .nil .nil) .nil) (.node 3739 .nil .nil)) (.node 3847 (.node 3823 (.node 3793 .nil .nil) .nil) (.node 3851 .nil .nil))) (.node 3931 (.node 3911 (.node 3907 (.node 3877 .nil .nil) .nil) (.node 3919 .nil .nil)) (.node 3967 (.node 3943 .nil .nil) (.node 4003 .nil .nil)))))
def t4423 : KeyTree := (.node 4423 (.node 4201 (.node 4096 (.node 4057 (.node 4051 (.node 4027 .nil .nil) .nil) (.node 4093 .nil .nil)) (.node 4159 (.node 4129 (.node 4111 .nil .nil) .nil) (.node 4177 .nil .nil))) (.node 4271 (.node 4243 (.node 4231 (.node 4219 .nil .nil) .nil) (.node 4261 .nil .nil)) (.node 4357 (.node 4327 .nil .nil) (.node 4421 .nil .nil)))) (.node 4663 (.node 4561 (.node 4489 (.node 4447 (.node 4441 .nil .nil) .nil) (.node 4523 .nil .nil)) (.node 4621 (.node 4603 (.node 4591 .nil .nil) .nil) (.node 4651 .nil .nil))) (.node 4831 (.node 4789 (.node 4759 (.node 4691 .nil .nil) .nil) (.node 4801 .nil .nil)) (.node 4903 (.node 4861 .nil .nil) (.node 4931 .nil .nil)))))
def t4021 : KeyTree := (.node 4021 t3709 t4423)
def t3469 : KeyTree := (.node 3469 t2887 t4021)
def t5503 : KeyTree := (.node 5503 (.node 5227 (.node 5101 (.node 5011 (.node 4999 (.node 4957 .nil .nil) .nil) (.node 5041 .nil .nil)) (.node 5171 (.node 5167 (.node 5107 .nil .nil) .nil) (.node 5209 .nil .nil))) (.node 5413 (.node 5281 (.node 5279 (.node 5237 .nil .nil) .nil) (.node 5407 .nil .nil)) (.node 5431 (.node 5419 .nil .nil) (.node 5479 .nil .nil)))) (.node 5791 (.node 5641 (.node 5581 (.node 5531 (.node 5521 .nil .nil) .nil) (.node 5591 .nil .nil)) (.node 5741 (.node 5701 (.node 5659 .nil .nil) .nil) (.node 5743 .nil .nil))) (.node 5923 (.node 5851 (.node 5839 (.node 5821 .nil .nil) .nil) (.node 5881 .nil .nil)) (.node 6007 (.node 5981 .nil .nil) (.node 6043 .nil .nil)))))
def t6553 : KeyTree := (.node 6553 (.node 6301 (.node 6163 (.node 6133 (.node 6121 (.node 6091 .nil .nil) .nil) (.node 6151 .nil .nil)) (.node 6241 (.node 6217 (.node 6211 .nil .nil) .nil) (.node 6271 .nil .nil))) (.node 6427 (.node 6397 (.node 6361 (.node 6343 .nil .nil) .nil) (.node 6421 .nil .nil)) (.node 6469 (.node 6451 .nil .nil) (.node 6491 .nil .nil)))) (.node 6781 (.node 6679 (.node 6637 (.node 6581 (.node 6571 .nil .nil) .nil) (.node 6661 .nil .nil)) (.node 6733 (.node 6709 (.node 6691 .nil .nil) .nil) (.node 6763 .nil .nil))) (.node 6889 (.node 6871 (.node 6841 (.node 6791 .nil .nil) .nil) (.node 6883 .nil .nil)) (.node 6961 (.node 6917 .nil .nil) (.node 6971 .nil .nil)))))
def t6073 : KeyTree := (.node 6073 t5503 t6553)
def t7561 : KeyTree := (.node 7561 (.node 7333 (.node 7177 (.node 7069 (.node 7039 (.node 6997 .nil .nil) .nil) (.node 7151 .nil .nil)) (.node 7309 (.node 7243 (.node 7211 .nil .nil) .nil) (.node 7321 .nil .nil))) (.node 7477 (.node 7411 (.node 7393 (.node 7351 .nil .nil) .nil) (.node 7459 .nil .nil)) (.node 7541 (.node 7481 .nil .nil) (.node 7549 .nil .nil)))) (.node 7867 (.node 7687 (.node 7621 (.node 7603 (.node 7591 .nil .nil) .nil) (.node 7639 .nil .nil)) (.node 7753 (.node 7741 (.node 7723 .nil .nil) .nil) (.node 7789 .nil .nil))) (.node 8011 (.node 7951 (.node 7921 (.node 7879 .nil .nil) .nil) (.node 8009 .nil .nil)) (.node 8059 (.node 8053 .nil .nil) (.node 8161 .nil .nil)))))
def t8741 : KeyTree := (.node 8741 (.node 8461 (.node 8311 (.node 8221 (.node 8191 (.node 8179 .nil .nil) .nil) (.node 8269 .nil .nil)) (.node 8431 (.node 8419 (.node 8317 .nil .nil) .nil) (.node 8443 .nil .nil))) (.node 8647 (.node 8527 (.node 8521 (.node 8467 .nil .nil) .nil) (.node 8581 .nil .nil)) (.node 8731 (.node 8681 .nil .nil) (.node 8737 .nil .nil)))) (.node 8971 (.node 8863 (.node 8807 (.node 8779 (.node 8761 .nil .nil) .nil) (.node 8821 .nil .nil)) (.node 8933 (.node 8893 (.node 8867 .nil .nil) .nil) (.node 8941 .nil .nil))) (.node 9091 (.node 9043 (.node 9011 (.node 9007 .nil .nil) .nil) (.node 9049 .nil .nil)) (.node 9109 (.node 9103 .nil .nil) (.node 9151 .nil .nil)))))
def t8171 : KeyTree := (.node 8171 t7561 t8741)
def t6991 : KeyTree := (.node 6991 t6073 t8171)
def t4951 : KeyTree := (.node 4951 t3469 t6991)
def t2411 : KeyTree := (.node 2411 t967 t4951)
def t9769 : KeyTree := (.node 9769 (.node 9439 (.node 9311 (.node 9241 (.node 9199 (.node 9181 .nil .nil) .nil) (.node 9283 .nil .nil)) (.node 9421 (.node 9391 (.node 9349 .nil .nil) .nil) (.node 9431 .nil .nil))) (.node 9521 (.node 9491 (.node 9463 (.node 9461 .nil .nil) .nil) (.node 9511 .nil .nil)) (.node 9631 (.node 9619 (.node 9547 .nil .nil) .nil) (.node 9661 .nil .nil)))) (.node 9931 (.node 9829 (.node 9791 (.node 9787 (.node 9781 .nil .nil) .nil) (.node 9811 .nil .nil)) (.node 9901 (.node 9871 (.node 9859 .nil .nil) .nil) (.node 9907 .nil .nil))) (.node 10111 (.node 10039 (.node 9967 (.node 9941 .nil .nil) .nil) (.node 10099 .nil .nil)) (.node 10151 (.node 10141 .nil .nil) (.node 10201 .nil .nil)))))
def t10831 : KeyTree := (.node 10831 (.node 10609 (.node 10429 (.node 10321 (.node 10303 (.node 10271 .nil .nil) .nil) (.node 10333 .nil .nil)) (.node 10501 (.node 10459 (.node 10453 .nil .nil) .nil) (.node 10531 .nil .nil))) (.node 10739 (.node 10687 (.node 10651 (.node 10627 .nil .nil) .nil) (.node 10711 .nil .nil)) (.node 10781 (.node 10771 .nil .nil) (.node 10789 .nil .nil)))) (.node 11071 (.node 10903 (.node 10861 (.node 10847 (.node 10837 .nil .nil) .nil) (.node 10891 .nil .nil)) (.node 11047 (.node 10957 (.node 10949 .nil .nil) .nil) (.node 11059 .nil .nil))) (.node 11243 (.node 11161 (.node 11131 (.node 11119 .nil .nil) .nil) (.node 11173 .nil .nil)) (.node 11287 (.node 11257 .nil .nil) (.node 11299 .nil .nil)))))
def t10267 : KeyTree := (.node 10267 t9769 t10831)
def t11831 : KeyTree := (.node 11831 (.node 11593 (.node 11467 (.node 11383 (.node 11353 (.node 11317 .nil .nil) .nil) (.node 11411 .nil .nil)) (.node 11527 (.node 11491 (.node 11471 .nil .nil) .nil) (.node 11551 .nil .nil))) (.node 11731 (.node 11701 (.node 11677 (.node 11621 .nil .nil) .nil) (.node 11719 .nil .nil)) (.node 11779 (.node 11743 .nil .nil) (.node 11821 .nil .nil)))) (.node 12167 (.node 11971 (.node 11887 (.node 11881 (.node 11833 .nil .nil) .nil) (.node 11941 .nil .nil)) (.node 12041 (.node 12037 (.node 12007 .nil .nil) .nil) (.node 12071 .nil .nil))) (.node 12343 (.node 12277 (.node 12241 (.node 12211 .nil .nil) .nil) (.node 12301 .nil .nil)) (.node 12391 (.node 12377 .nil .nil) (.node 12409 .nil .nil)))))
def t12973 : KeyTree := (.node 12973 (.node 12671 (.node 12517 (.node 12503 (.node 12451 (.node 12433 .nil .nil) .nil) (.node 12511 .nil .nil)) (.node 12601 (.node 12547 (.node 12541 .nil .nil) .nil) (.node 12611 .nil .nil))) (.node 12781 (.node 12739 (.node 12721 (.node 12703 .nil .nil) .nil) (.node 12769 .nil .nil)) (.node 12853 (.node 12841 .nil .nil) (.node 12923 .nil .nil)))) (.node 13331 (.node 13147 (.node 13063 (.node 13003 (.node 12979 .nil .nil) .nil) (.node 13099 .nil .nil)) (.node 13267 (.node 13171 (.node 13159 .nil .nil) .nil) (.node 13291 .nil .nil))) (.node 13417 (.node 13399 (.node 13381 (.node 13339 .nil .nil) .nil) (.node 13411 .nil .nil)) (.node 13441 (.node 13421 .nil .nil) (.node 13469 .nil .nil)))))
def t12421 : KeyTree := (.node 12421 t11831 t12973)
def t11311 : KeyTree := (.node 11311 t10267 t12421)
def t14221 : KeyTree := (.node 14221 (.node 13831 (.node 13693 (.node 13669 (.node 13597 (.node 13591 .nil .nil) .nil) (.node 13681 .nil .nil)) (.node 13781 (.node 13729 (.node 13711 .nil .nil) .nil) (.node 13807 .nil .nil))) (.node 14011 (.node 13931 (.node 13921 (.node 13903 .nil .nil) .nil) (.node 13963 .nil .nil)) (.node 14071 (.node 14029 .nil .nil) (.node 14197 .nil .nil)))) (.node 14479 (.node 14389 (.node 14323 (.node 14281 (.node 14251 .nil .nil) .nil) (.node 14341 .nil .nil)) (.node 14449 (.node 14431 (.node 14411 .nil .nil) .nil) (.node 14461 .nil .nil))) (.node 14629 (.node 14561 (.node 14551 (.node 14533 .nil .nil) .nil) (.node 14621 .nil .nil)) (.node 14653 (.node 14641 .nil .nil) (.node 14731 .nil .nil)))))
def t15313 : KeyTree := (.node 15313 (.node 15031 (.node 14851 (.node 14821 (.node 14771 (.node 14767 .nil .nil) .nil) (.node 14827 .nil .nil)) (.node 14951 (.node 14947 (.node 14869 .nil .nil) .nil) (.node 14983 .nil .nil))) (.node 15241 (.node 15121 (.node 15091 (.node 15061 .nil .nil) .nil) (.node 15199 .nil .nil)) (.node 15277 (.node 15271 .nil .nil) (.node 15289 .nil .nil)))) (.node 15583 (.node 15401 (.node 15373 (.node 15331 (.node 15319 .nil .nil) .nil) (.node 15391 .nil .nil)) (.node 15511 (.node 15451 (.node 15439 .nil .nil) .nil) (.node 15541 .nil .nil))) (.node 15661 (.node 15625 (.node 15619 (.node 15601 .nil .nil) .nil) (.node 15643 .nil .nil)) (.node 15679 (.node 15667 .nil .nil) (.node 15731 .nil .nil)))))
def t14741 : KeyTree := (.node 14741 t14221 t15313)
def t16561 : KeyTree := (.node 16561 (.node 16141 (.node 15919 (.node 15907 (.node 15901 (.node 15739 .nil .nil) .nil) (.node 15913 .nil .nil)) (.node 16087 (.node 16069 (.node 15991 .nil .nil) .nil) (.node 16111 .nil .nil))) (.node 16369 (.node 16231 (.node 16189 (.node 16183 .nil .nil) .nil) (.node 16339 .nil .nil)) (.node 16411 (.node 16381 .nil .nil) (.node 16451 .nil .nil)))) (.node 16831 (.node 16693 (.node 16651 (.node 16633 (.node 16567 .nil .nil) .nil) (.node 16661 .nil .nil)) (.node 16741 (.node 16729 (.node 16699 .nil .nil) .nil) (.node 16759 .nil .nil))) (.node 16927 (.node 16879 (.node 16871 (.node 16843 .nil .nil) .nil) (.node 16921 .nil .nil)) (.node 16981 (.node 16963 .nil .nil) (.node 16987 .nil .nil)))))
def t17491 : KeyTree := (.node 17491 (.node 17293 (.node 17161 (.node 17053 (.node 17041 (.node 17029 .nil .nil) .nil) (.node 17137 .nil .nil)) (.node 17239 (.node 17203 (.node 17191 .nil .nil) .nil) (.node 17291 .nil .nil))) (.node 17401 (.node 17359 (.node 17341 (.node 17317 .nil .nil) .nil) (.node 17389 .nil .nil)) (.node 17443 (.node 17431 .nil .nil) (.node 17467 .nil .nil)))) (.node 17791 (.node 17623 (.node 17581 (.node 17551 (.node 17539 .nil .nil) .nil) (.node 17599 .nil .nil)) (.node 17749 (.node 17707 (.node 17683 .nil .nil) .nil) (.node 17761 .nil .nil))) (.node 17923 (.node 17881 (.node 17863 (.node 17851 .nil .nil) .nil) (.node 17911 .nil .nil)) (.node 17971 (.node 17959 .nil .nil) (.node 17977 .nil .nil)))))
def t17011 : KeyTree := (.node 17011 t16561 t17491)
def t15733 : KeyTree := (.node 15733 t14741 t17011)
def t13567 : KeyTree := (.node 13567 t11311 t15733)
def t18583 : KeyTree := (.node 18583 (.node 18229 (.node 18127 (.node 18097 (.node 18061 (.node 18043 .nil .nil) .nil) (.node 18121 .nil .nil)) (.node 18211 (.node 18181 (.node 18131 .nil .nil) .nil) (.node 18217 .nil .nil))) (.node 18439 (.node 18397 (.node 18313 (.node 18301 .nil .nil) .nil) (.node 18427 .nil .nil)) (.node 18493 (.node 18481 (.node 18451 .nil .nil) .nil) (.node 18541 .nil .nil)))) (.node 19081 (.node 18787 (.node 18691 (.node 18679 (.node 18661 .nil .nil) .nil) (.node 18769 .nil .nil)) (.node 19051 (.node 18973 (.node 18859 .nil .nil) .nil) (.node 19069 .nil .nil))) (.node 19237 (.node 19207 (.node 19183 (.node 19141 .nil .nil) .nil) (.node 19231 .nil .nil)) (.node 19273 (.node 19267 .nil .nil) (.node 19321 .nil .nil)))))
def t19993 : KeyTree := (.node 19993 (.node 19681 (.node 19489 (.node 19471 (.node 19447 (.node 19423 .nil .nil) .nil) (.node 19483 .nil .nil)) (.node 19597 (.node 19531 (.node 19501 .nil .nil) .nil) (.node 19609 .nil .nil))) (.node 19813 (.node 19717 (.node 19699 (.node 19687 .nil .nil) .nil) (.node 19801 .nil .nil)) (.node 19867 (.node 19861 .nil .nil) (.node 19891 .nil .nil)))) (.node 20359 (.node 20101 (.node 20047 (.node 20021 (.node 20011 .nil .nil) .nil) (.node 20071 .nil .nil)) (.node 20287 (.node 20161 (.node 20149 .nil .nil) .nil) (.node 20341 .nil .nil))) (.node 20593 (.node 20521 (.node 20431 (.node 20407 .nil .nil) .nil) (.node 20551 .nil .nil)) (.node 20641 (.node 20611 .nil .nil) (.node 20707 .nil .nil)))))
def t19381 : KeyTree := (.node 19381 t18583 t19993)
def t21649 : KeyTree := (.node 21649 (.node 21187 (.node 21001 (.node 20959 (.node 20857 (.node 20749 .nil .nil) .nil) (.node 20983 .nil .nil)) (.node 21121 (.node 21061 (.node 21031 .nil .nil) .nil) (.node 21139 .nil .nil))) (.node 21481 (.node 21379 (.node 21319 (.node 21211 .nil .nil) .nil) (.node 21391 .nil .nil)) (.node 21529 (.node 21517 .nil .nil) (.node 21589 .nil .nil)))) (.node 22051 (.node 21799 (.node 21751 (.node 21673 (.node 21661 .nil .nil) .nil) (.node 21757 .nil .nil)) (.node 21991 (.node 21961 (.node 21841 .nil .nil) .nil) (.node 21997 .nil .nil))) (.node 22291 (.node 22171 (.node 22111 (.node 22093 .nil .nil) .nil) (.node 22201 .nil .nil)) (.node 22381 (.node 22303 .nil .nil) (.node 22441 .nil .nil)))))
def t23251 : KeyTree := (.node 23251 (.node 22921 (.node 22651 (.node 22621 (.node 22573 (.node 22543 .nil .nil) .nil) (.node 22639 .nil .nil)) (.node 22807 (.node 22801 (.node 22741 .nil .nil) .nil) (.node 22861 .nil .nil))) (.node 23131 (.node 23059 (.node 23017 (.node 23011 .nil .nil) .nil) (.node 23071 .nil .nil)) (.node 23167 (.node 23143 .nil .nil) (.node 23227 .nil .nil)))) (.node 23773 (.node 23563 (.node 23371 (.node 23311 (.node 23269 .nil .nil) .nil) (.node 23431 .nil .nil)) (.node 23689 (.node 23671 (.node 23581 .nil .nil) .nil) (.node 23761 .nil .nil))) (.node 23911 (.node 23869 (.node 23857 (.node 23827 .nil .nil) .nil) (.node 23899 .nil .nil)) (.node 24061 (.node 23971 .nil .nil) (.node 24091 .nil .nil)))))
def t22531 : KeyTree := (.node 22531 t21649 t23251)
def t20731 : KeyTree := (.node 20731 t19381 t22531)
def t25411 : KeyTree := (.node 25411 (.node 24781 (.node 24421 (.node 24181 (.node 24151 (.node 24121 .nil .nil) .nil) (.node 24391 .nil .nil)) (.node 24631 (.node 24571 (.node 24481 .nil .nil) .nil) (.node 24691 .nil .nil))) (.node 25117 (.node 25033 (.node 24907 (.node 24841 .nil .nil) .nil) (.node 25111 .nil .nil)) (.node 25261 (.node 25171 .nil .nil) (.node 25321 .nil .nil)))) (.node 25951 (.node 25621 (.node 25561 (.node 25537 (.node 25471 .nil .nil) .nil) (.node 25579 .nil .nil)) (.node 25801 (.node 25771 (.node 25741 .nil .nil) .nil) (.node 25873 .nil .nil))) (.node 26209 (.node 26083 (.node 26041 (.node 25981 .nil .nil) .nil) (.node 26161 .nil .nil)) (.node 26371 (.node 26251 .nil .nil) (.node 26431 .nil .nil)))))
def t27901 : KeyTree := (.node 27901 (.node 27259 (.node 27031 (.node 26821 (.node 26731 (.node 26701 .nil .nil) .nil) (.node 26881 .nil .nil)) (.node 27211 (.node 27091 (.node 27061 .nil .nil) .nil) (.node 27241 .nil .nil))) (.node 27631 (.node 27481 (.node 27361 (.node 27271 .nil .nil) .nil) (.node 27541 .nil .nil)) (.node 27751 (.node 27691 .nil .nil) (.node 27847 .nil .nil)))) (.node 28411 (.node 28183 (.node 28081 (.node 28051 (.node 27961 .nil .nil) .nil) (.node 28111 .nil .nil)) (.node 28351 (.node 28211 (.node 28201 .nil .nil) .nil) (.node 28393 .nil .nil))) (.node 28843 (.node 28711 (.node 28621 (.node 28561 .nil .nil) .nil) (.node 28771 .nil .nil)) (.node 29191 (.node 29173 .nil .nil) (.node 29251 .nil .nil)))))
def t26641 : KeyTree := (.node 26641 t25411 t27901)
def t31123 : KeyTree := (.node 31123 (.node 30211 (.node 29641 (.node 29581 (.node 29569 (.node 29527 .nil .nil) .nil) (.node 29611 .nil .nil)) (.node 29947 (.node 29761 (.node 29671 .nil .nil) .nil) (.node 30091 .nil .nil))) (.node 30871 (.node 30703 (.node 30661 (.node 30241 .nil .nil) .nil) (.node 30781 .nil .nil)) (.node 31051 (.node 30941 .nil .nil) (.node 31081 .nil .nil)))) (.node 33181 (.node 32719 (.node 32341 (.node 32191 (.node 31981 .nil .nil) .nil) (.node 32371 .nil .nil)) (.node 32971 (.node 32803 (.node 32761 .nil .nil) .nil) (.node 33151 .nil .nil))) (.node 33931 (.node 33601 (.node 33391 (.node 33331 .nil .nil) .nil) (.node 33811 .nil .nil)) (.node 34231 (.node 34171 .nil .nil) (.node 34511 .nil .nil)))))
def t38011 : KeyTree := (.node 38011 (.node 36541 (.node 35531 (.node 35311 (.node 35281 (.node 34981 .nil .nil) .nil) (.node 35491 .nil .nil)) (.node 36037 (.node 35911 (.node 35671 .nil .nil) .nil) (.node 36191 .nil .nil))) (.node 37507 (.node 36709 (.node 36583 (.node 36571 .nil .nil) .nil) (.node 37171 .nil .nil)) (.node 37831 (.node 37591 .nil .nil) (.node 37951 .nil .nil)))) (.node 40111 (.node 38767 (.node 38431 (.node 38281 (.node 38039 .nil .nil) .nil) (.node 38611 .nil .nil)) (.node 39733 (.node 39607 (.node 38851 .nil .nil) .nil) (.node 39901 .nil .nil))) (.node 41231 (.node 40591 (.node 40531 (.node 40471 .nil .nil) .nil) (.node 40699 .nil .nil)) (.node 41413 (.node 41341 .nil .nil) (.node 41539 .nil .nil)))))
def t34651 : KeyTree := (.node 34651 t31123 t38011)
def t29401 : KeyTree := (.node 29401 t26641 t34651)
def t24109 : KeyTree := (.node 24109 t20731 t29401)
def t18013 : KeyTree := (.node 18013 t13567 t24109)
def t9157 : KeyTree := (.node 9157 t2411 t18013)
def t44521 : KeyTree := (.node 44521 (.node 43051 (.node 42571 (.node 42181 (.node 42043 (.node 41911 .nil .nil) .nil) (.node 42331 .nil .nil)) (.node 42967 (.node 42901 (.node 42841 .nil .nil) .nil) (.node 42979 .nil .nil))) (.node 43891 (.node 43711 (.node 43291 (.node 43261 .nil .nil) .nil) (.node 43759 .nil .nil)) (.node 44269 (.node 44221 (.node 44071 .nil .nil) .nil) (.node 44371 .nil .nil)))) (.node 46663 (.node 45541 (.node 45319 (.node 44851 (.node 44773 .nil .nil) .nil) (.node 45403 .nil .nil)) (.node 46399 (.node 46021 (.node 45943 .nil .nil) .nil) (.node 46411 .nil .nil))) (.node 47059 (.node 46861 (.node 46831 (.node 46691 .nil .nil) .nil) (.node 46957 .nil .nil)) (.node 47581 (.node 47431 .nil .nil) (.node 47741 .nil .nil)))))
def t51151 : KeyTree := (.node 51151 (.node 49477 (.node 48907 (.node 48247 (.node 48091 (.node 48049 .nil .nil) .nil) (.node 48679 .nil .nil)) (.node 49171 (.node 48991 (.node 48973 .nil .nil) .nil) (.node 49211 .nil .nil))) (.node 50311 (.node 49939 (.node 49831 (.node 49531 .nil .nil) .nil) (.node 50051 .nil .nil)) (.node 50821 (.node 50359 .nil .nil) (.node 51061 .nil .nil)))) (.node 52291 (.node 51511 (.node 51283 (.node 51241 (.node 51199 .nil .nil) .nil) (.node 51481 .nil .nil)) (.node 52027 (.node 51871 (.node 51613 .nil .nil) .nil) (.node 52081 .nil .nil))) (.node 52963 (.node 52711 (.node 52441 (.node 52361 .nil .nil) .nil) (.node 52837 .nil .nil)) (.node 53551 (.node 53197 .nil .nil) (.node 53593 .nil .nil)))))
def t47881 : KeyTree := (.node 47881 t44521 t51151)
def t56431 : KeyTree := (.node 56431 (.node 55291 (.node 54517 (.node 54181 (.node 54121 (.node 53923 .nil .nil) .nil) (.node 54367 .nil .nil)) (.node 55021 (.node 54979 (.node 54601 .nil .nil) .nil) (.node 55147 .nil .nil))) (.node 55987 (.node 55511 (.node 55441 (.node 55381 .nil .nil) .nil) (.node 55931 .nil .nil)) (.node 56167 (.node 56101 .nil .nil) (.node 56239 .nil .nil)))) (.node 57331 (.node 56911 (.node 56731 (.node 56659 (.node 56611 .nil .nil) .nil) (.node 56827 .nil .nil)) (.node 57191 (.node 57121 (.node 56941 .nil .nil) .nil) (.node 57271 .nil .nil))) (.node 58171 (.node 57751 (.node 57571 (.node 57487 .nil .nil) .nil) (.node 58111 .nil .nil)) (.node 58549 (.node 58411 .nil .nil) (.node 58631 .nil .nil)))))
def t61051 : KeyTree := (.node 61051 (.node 59467 (.node 59053 (.node 58831 (.node 58787 (.node 58741 .nil .nil) .nil) (.node 59011 .nil .nil)) (.node 59281 (.node 59263 (.node 59221 .nil .nil) .nil) (.node 59341 .nil .nil))) (.node 60631 (.node 60607 (.node 60271 (.node 59671 .nil .nil) .nil) (.node 60611 .nil .nil)) (.node 60901 (.node 60763 .nil .nil) (.node 60919 .nil .nil)))) (.node 62701 (.node 62119 (.node 61909 (.node 61381 (.node 61231 .nil .nil) .nil) (.node 62011 .nil .nil)) (.node 62323 (.node 62311 (.node 62131 .nil .nil) .nil) (.node 62581 .nil .nil))) (.node 63241 (.node 63031 (.node 62791 (.node 62731 .nil .nil) .nil) (.node 63211 .nil .nil)) (.node 63421 (.node 63337 .nil .nil) (.node 63493 .nil .nil)))))
def t58711 : KeyTree := (.node 58711 t56431 t61051)
def t53791 : KeyTree := (.node 53791 t47881 t58711)
def t66463 : KeyTree := (.node 66463 (.node 65521 (.node 64381 (.node 64091 (.node 63841 (.node 63727 .nil .nil) .nil) (.node 64171 .nil .nil)) (.node 65101 (.node 65011 (.node 64891 .nil .nil) .nil) (.node 65437 .nil .nil))) (.node 66301 (.node 66067 (.node 65731 (.node 65551 .nil .nil) .nil) (.node 66221 .nil .nil)) (.node 66403 (.node 66361 .nil .nil) (.node 66431 .nil .nil)))) (.node 68311 (.node 67411 (.node 67211 (.node 66931 (.node 66571 .nil .nil) .nil) (.node 67261 .nil .nil)) (.node 67783 (.node 67651 (.node 67453 .nil .nil) .nil) (.node 67891 .nil .nil))) (.node 68881 (.node 68531 (.node 68443 (.node 68371 .nil .nil) .nil) (.node 68821 .nil .nil)) (.node 69191 (.node 69031 .nil .nil) (.node 69259 .nil .nil)))))
def t71527 : KeyTree := (.node 71527 (.node 70687 (.node 70123 (.node 69931 (.node 69763 (.node 69691 .nil .nil) .nil) (.node 70111 .nil .nil)) (.node 70381 (.node 70351 (.node 70141 .nil .nil) .nil) (.node 70621 .nil .nil))) (.node 71023 (.node 70951 (.node 70891 (.node 70841 .nil .nil) .nil) (.node 70981 .nil .nil)) (.node 71341 (.node 71191 .nil .nil) (.node 71347 .nil .nil)))) (.node 72727 (.node 72073 (.node 71821 (.node 71761 (.node 71707 .nil .nil) .nil) (.node 71941 .nil .nil)) (.node 72421 (.node 72271 (.node 72211 .nil .nil) .nil) (.node 72661 .nil .nil))) (.node 73039 (.node 72931 (.node 72871 (.node 72733 .nil .nil) .nil) (.node 72997 .nil .nil)) (.node 73291 (.node 73141 .nil .nil) (.node 73417 .nil .nil)))))
def t69427 : KeyTree := (.node 69427 t66463 t71527)
def t75703 : KeyTree := (.node 75703 (.node 74761 (.node 74131 (.node 74047 (.node 73951 (.node 73471 .nil .nil) .nil) (.node 74101 .nil .nil)) (.node 74551 (.node 74383 (.node 74257 .nil .nil) .nil) (.node 74731 .nil .nil))) (.node 75307 (.node 75181 (.node 75013 (.node 74821 .nil .nil) .nil) (.node 75211 .nil .nil)) (.node 75571 (.node 75391 .nil .nil) (.node 75583 .nil .nil)))) (.node 77141 (.node 76441 (.node 76231 (.node 76039 (.node 75991 .nil .nil) .nil) (.node 76261 .nil .nil)) (.node 76819 (.node 76651 (.node 76561 .nil .nil) .nil) (.node 76831 .nil .nil))) (.node 77491 (.node 77419 (.node 77351 (.node 77191 .nil .nil) .nil) (.node 77431 .nil .nil)) (.node 77551 (.node 77521 .nil .nil) (.node 77611 .nil .nil)))))
def t81131 : KeyTree := (.node 81131 (.node 79801 (.node 78961 (.node 78691 (.node 78541 (.node 78121 .nil .nil) .nil) (.node 78781 .nil .nil)) (.node 79531 (.node 79423 (.node 79231 .nil .nil) .nil) (.node 79561 .nil .nil))) (.node 80683 (.node 80341 (.node 80221 (.node 80071 .nil .nil) .nil) (.node 80599 .nil .nil)) (.node 80911 (.node 80809 .nil .nil) (.node 81031 .nil .nil)))) (.node 83071 (.node 82171 (.node 81421 (.node 81283 (.node 81181 .nil .nil) .nil) (.node 81901 .nil .nil)) (.node 82651 (.node 82531 (.node 82237 .nil .nil) .nil) (.node 82699 .nil .nil))) (.node 83791 (.node 83227 (.node 83221 (.node 83077 .nil .nil) .nil) (.node 83641 .nil .nil)) (.node 84211 (.node 84181 .nil .nil) (.node 84319 .nil .nil)))))
def t78079 : KeyTree := (.node 78079 t75703 t81131)
def t73459 : KeyTree := (.node 73459 t69427 t78079)
def t63691 : KeyTree := (.node 63691 t53791 t73459)
def t87517 : KeyTree := (.node 87517 (.node 86011 (.node 84871 (.node 84631 (.node 84589 (.node 84421 .nil .nil) .nil) (.node 84811 .nil .nil)) (.node 85411 (.node 85021 (.node 85009 .nil .nil) .nil) (.node 85933 .nil .nil))) (.node 86857 (.node 86311 (.node 86269 (.node 86131 .nil .nil) .nil) (.node 86461 .nil .nil)) (.node 87211 (.node 87151 (.node 87011 .nil .nil) .nil) (.node 87421 .nil .nil)))) (.node 89431 (.node 88411 (.node 87721 (.node 87691 (.node 87631 .nil .nil) .nil) (.node 87991 .nil .nil)) (.node 88843 (.node 88771 (.node 88741 .nil .nil) .nil) (.node 89041 .nil .nil))) (.node 89839 (.node 89611 (.node 89563 (.node 89491 .nil .nil) .nil) (.node 89671 .nil .nil)) (.node 90271 (.node 89959 .nil .nil) (.node 90403 .nil .nil)))))
def t92401 : KeyTree := (.node 92401 (.node 91591 (.node 91081 (.node 90679 (.node 90631 (.node 90511 .nil .nil) .nil) (.node 90931 .nil .nil)) (.node 91291 (.node 91183 (.node 91141 .nil .nil) .nil) (.node 91411 .nil .nil))) (.node 92041 (.node 91807 (.node 91771 (.node 91631 .nil .nil) .nil) (.node 91939 .nil .nil)) (.node 92221 (.node 92107 .nil .nil) (.node 92311 .nil .nil)))) (.node 93787 (.node 92863 (.node 92569 (.node 92461 (.node 92431 .nil .nil) .nil) (.node 92821 .nil .nil)) (.node 93523 (.node 93481 (.node 93241 .nil .nil) .nil) (.node 93703 .nil .nil))) (.node 94249 (.node 93913 (.node 93871 (.node 93811 .nil .nil) .nil) (.node 94117 .nil .nil)) (.node 94351 (.node 94291 .nil .nil) (.node 94531 .nil .nil)))))
def t90481 : KeyTree := (.node 90481 t87517 t92401)
def t96799 : KeyTree := (.node 96799 (.node 95971 (.node 95461 (.node 95191 (.node 95131 (.node 95083 .nil .nil) .nil) (.node 95239 .nil .nil)) (.node 95881 (.node 95791 (.node 95701 .nil .nil) .nil) (.node 95911 .nil .nil))) (.node 96493 (.node 96223 (.node 96181 (.node 96097 .nil .nil) .nil) (.node 96331 .nil .nil)) (.node 96643 (.node 96601 .nil .nil) (.node 96721 .nil .nil)))) (.node 98491 (.node 97651 (.node 97231 (.node 97171 (.node 97021 .nil .nil) .nil) (.node 97441 .nil .nil)) (.node 98041 (.node 97861 (.node 97813 .nil .nil) .nil) (.node 98407 .nil .nil))) (.node 99139 (.node 98911 (.node 98869 (.node 98533 .nil .nil) .nil) (.node 98953 .nil .nil)) (.node 99529 (.node 99181 .nil .nil) (.node 99661 .nil .nil)))))
def t102481 : KeyTree := (.node 102481 (.node 101599 (.node 100621 (.node 99991 (.node 99961 (.node 99877 .nil .nil) .nil) (.node 100591 .nil .nil)) (.node 101221 (.node 100981 (.node 100741 .nil .nil) .nil) (.node 101347 .nil .nil))) (.node 102181 (.node 102103 (.node 102031 (.node 101641 .nil .nil) .nil) (.node 102121 .nil .nil)) (.node 102301 (.node 102259 .nil .nil) (.node 102397 .nil .nil)))) (.node 104119 (.node 103171 (.node 102859 (.node 102829 (.node 102811 .nil .nil) .nil) (.node 102931 .nil .nil)) (.node 103951 (.node 103291 (.node 103231 .nil .nil) .nil) (.node 104053 .nil .nil))) (.node 104347 (.node 104287 (.node 104281 (.node 104161 .nil .nil) .nil) (.node 104311 .nil .nil)) (.node 104623 (.node 104551 .nil .nil) (.node 104677 .nil .nil)))))
def t99859 : KeyTree := (.node 99859 t96799 t102481)
def t94621 : KeyTree := (.node 94621 t90481 t99859)
def t107671 : KeyTree := (.node 107671 (.node 106861 (.node 105691 (.node 105379 (.node 105337 (.node 105211 .nil .nil) .nil) (.node 105673 .nil .nil)) (.node 106591 (.node 106531 (.node 106261 .nil .nil) .nil) (.node 106681 .nil .nil))) (.node 107563 (.node 107227 (.node 107101 (.node 107071 .nil .nil) .nil) (.node 107251 .nil .nil)) (.node 107641 (.node 107581 .nil .nil) (.node 107647 .nil .nil)))) (.node 108991 (.node 108421 (.node 107971 (.node 107941 (.node 107881 .nil .nil) .nil) (.node 108109 .nil .nil)) (.node 108631 (.node 108571 (.node 108529 .nil .nil) .nil) (.node 108967 .nil .nil))) (.node 109561 (.node 109201 (.node 109159 (.node 109141 .nil .nil) .nil) (.node 109471 .nil .nil)) (.node 109741 (.node 109621 .nil .nil) (.node 109831 .nil .nil)))))
def t113989 : KeyTree := (.node 113989 (.node 111721 (.node 110881 (.node 110491 (.node 110419 (.node 110221 .nil .nil) .nil) (.node 110581 .nil .nil)) (.node 111211 (.node 111091 (.node 110923 .nil .nil) .nil) (.node 111301 .nil .nil))) (.node 112771 (.node 112111 (.node 111973 (.node 111871 .nil .nil) .nil) (.node 112291 .nil .nil)) (.node 113161 (.node 113023 .nil .nil) (.node 113731 .nil .nil)))) (.node 116131 (.node 114577 (.node 114493 (.node 114451 (.node 114031 .nil .nil) .nil) (.node 114571 .nil .nil)) (.node 115831 (.node 115771 (.node 114661 .nil .nil) .nil) (.node 115963 .nil .nil))) (.node 117811 (.node 116689 (.node 116491 (.node 116341 .nil .nil) .nil) (.node 116791 .nil .nil)) (.node 118171 (.node 117991 .nil .nil) (.node 118471 .nil .nil)))))
def t109891 : KeyTree := (.node 109891 t107671 t113989)
def t121507 : KeyTree := (.node 121507 (.node 119851 (.node 119131 (.node 118861 (.node 118831 (.node 118819 .nil .nil) .nil) (.node 118903 .nil .nil)) (.node 119659 (.node 119311 (.node 119191 .nil .nil) .nil) (.node 119701 .nil .nil))) (.node 120871 (.node 120331 (.node 120121 (.node 119971 .nil .nil) .nil) (.node 120511 .nil .nil)) (.node 121291 (.node 121171 .nil .nil) (.node 121441 .nil .nil)))) (.node 123817 (.node 122611 (.node 122011 (.node 121801 (.node 121591 .nil .nil) .nil) (.node 122131 .nil .nil)) (.node 123397 (.node 123091 (.node 122761 .nil .nil) .nil) (.node 123631 .nil .nil))) (.node 125131 (.node 124489 (.node 124231 (.node 124021 .nil .nil) .nil) (.node 124951 .nil .nil)) (.node 125731 (.node 125371 .nil .nil) (.node 125791 .nil .nil)))))
def t129361 : KeyTree := (.node 129361 (.node 127681 (.node 126541 (.node 126421 (.node 126271 (.node 126211 .nil .nil) .nil) (.node 126481 .nil .nil)) (.node 127051 (.node 126691 (.node 126631 .nil .nil) .nil) (.node 127261 .nil .nil))) (.node 128437 (.node 128311 (.node 127921 (.node 127711 .nil .nil) .nil) (.node 128341 .nil .nil)) (.node 128761 (.node 128521 .nil .nil) (.node 128941 .nil .nil)))) (.node 131011 (.node 130411 (.node 130201 (.node 130021 (.node 129631 .nil .nil) .nil) (.node 130261 .nil .nil)) (.node 130651 (.node 130621 (.node 130531 .nil .nil) .nil) (.node 130981 .nil .nil))) (.node 131431 (.node 131101 (.node 131071 (.node 131041 .nil .nil) .nil) (.node 131371 .nil .nil)) (.node 131671 (.node 131581 .nil .nil) (.node 132241 .nil .nil)))))
def t126127 : KeyTree := (.node 126127 t121507 t129361)
def t118681 : KeyTree := (.node 118681 t109891 t126127)
def t104911 : KeyTree := (.node 104911 t94621 t118681)
def t84391 : KeyTree := (.node 84391 t63691 t104911)
def t136951 : KeyTree := (.node 136951 (.node 134851 (.node 133351 (.node 132721 (.node 132661 (.node 132511 .nil .nil) .nil) (.node 133321 .nil .nil)) (.node 134161 (.node 133981 (.node 133519 .nil .nil) .nil) (.node 134191 .nil .nil))) (.node 135721 (.node 135301 (.node 135241 (.node 135151 .nil .nil) .nil) (.node 135661 .nil .nil)) (.node 136621 (.node 136501 (.node 136111 .nil .nil) .nil) (.node 136711 .nil .nil)))) (.node 139591 (.node 138139 (.node 137341 (.node 137191 (.node 137131 .nil .nil) .nil) (.node 137941 .nil .nil)) (.node 138841 (.node 138451 (.node 138181 .nil .nil) .nil) (.node 139021 .nil .nil))) (.node 140281 (.node 140071 (.node 139921 (.node 139861 .nil .nil) .nil) (.node 140221 .nil .nil)) (.node 140761 (.node 140449 .nil .nil) (.node 141181 .nil .nil)))))
def t148201 : KeyTree := (.node 148201 (.node 144541 (.node 143551 (.node 142381 (.node 142231 (.node 141961 .nil .nil) .nil) (.node 142591 .nil .nil)) (.node 144271 (.node 143881 (.node 143641 .nil .nil) .nil) (.node 144481 .nil .nil))) (.node 146521 (.node 146161 (.node 145861 (.node 145531 .nil .nil) .nil) (.node 146191 .nil .nil)) (.node 147031 (.node 146581 .nil .nil) (.node 147211 .nil .nil)))) (.node 151471 (.node 149521 (.node 149101 (.node 148891 (.node 148471 .nil .nil) .nil) (.node 149161 .nil .nil)) (.node 150571 (.node 150151 (.node 149731 .nil .nil) .nil) (.node 150991 .nil .nil))) (.node 154981 (.node 152671 (.node 152461 (.node 152041 .nil .nil) .nil) (.node 153511 .nil .nil)) (.node 155821 (.node 155191 .nil .nil) (.node 156241 .nil .nil)))))
def t141241 : KeyTree := (.node 141241 t136951 t148201)
def t167311 : KeyTree := (.node 167311 (.node 161071 (.node 159811 (.node 158551 (.node 158341 (.node 157291 .nil .nil) .nil) (.node 158731 .nil .nil)) (.node 160651 (.node 160441 (.node 160231 .nil .nil) .nil) (.node 160861 .nil .nil))) (.node 163171 (.node 162751 (.node 162691 (.node 161911 .nil .nil) .nil) (.node 163021 .nil .nil)) (.node 164431 (.node 164011 .nil .nil) (.node 165901 .nil .nil)))) (.node 180181 (.node 174931 (.node 171571 (.node 168631 (.node 168211 .nil .nil) .nil) (.node 174721 .nil .nil)) (.node 176611 (.node 175891 (.node 175561 .nil .nil) .nil) (.node 178501 .nil .nil))) (.node 188791 (.node 187111 (.node 186187 (.node 185641 .nil .nil) .nil) (.node 187531 .nil .nil)) (.node 192271 (.node 189421 .nil .nil) (.node 194371 .nil .nil)))))
def t235621 : KeyTree := (.node 235621 (.node 214891 (.node 207481 (.node 202021 (.node 200971 (.node 198031 .nil .nil) .nil) (.node 207061 .nil .nil)) (.node 213181 (.node 212521 (.node 210631 .nil .nil) .nil) (.node 214831 .nil .nil))) (.node 227371 (.node 224071 (.node 219451 (.node 217771 .nil .nil) .nil) (.node 227011 .nil .nil)) (.node 232051 (.node 229711 .nil .nil) (.node 234781 .nil .nil)))) (.node 261031 (.node 247381 (.node 244861 (.node 243391 (.node 242971 .nil .nil) .nil) (.node 246247 .nil .nil)) (.node 251941 (.node 251791 (.node 248821 .nil .nil) .nil) (.node 258061 .nil .nil))) (.node 272581 (.node 269179 (.node 267961 (.node 264811 .nil .nil) .nil) (.node 270271 .nil .nil)) (.node 276277 (.node 274171 .nil .nil) (.node 278071 .nil .nil)))))
def t197341 : KeyTree := (.node 197341 t167311 t235621)
def t157081 : KeyTree := (.node 157081 t141241 t197341)
def t318781 : KeyTree := (.node 318781 (.node 305971 (.node 291721 (.node 289381 (.node 285091 (.node 284131 .nil .nil) .nil) (.node 291271 .nil .nil)) (.node 300301 (.node 297991 (.node 296011 .nil .nil) .nil) (.node 304981 .nil .nil))) (.node 316471 (.node 310591 (.node 309541 (.node 308491 .nil .nil) .nil) (.node 314161 .nil .nil)) (.node 317731 (.node 316681 .nil .nil) (.node 318319 .nil .nil)))) (.node 339151 (.node 330331 (.node 324871 (.node 322771 (.node 321091 .nil .nil) .nil) (.node 326041 .nil .nil)) (.node 336491 (.node 332011 (.node 331171 .nil .nil) .nil) (.node 337261 .nil .nil))) (.node 347131 (.node 343141 (.node 342343 (.node 342211 .nil .nil) .nil) (.node 346711 .nil .nil)) (.node 348811 (.node 347821 .nil .nil) (.node 351121 .nil .nil)))))
def t380563 : KeyTree := (.node 380563 (.node 367711 (.node 357421 (.node 355811 (.node 355111 (.node 354091 .nil .nil) .nil) (.node 356731 .nil .nil)) (.node 359311 (.node 358531 (.node 358051 .nil .nil) .nil) (.node 364183 .nil .nil))) (.node 373231 (.node 371281 (.node 371071 (.node 367771 .nil .nil) .nil) (.node 371491 .nil .nil)) (.node 377581 (.node 376531 .nil .nil) (.node 377911 .nil .nil)))) (.node 398581 (.node 389299 (.node 385771 (.node 383839 (.node 381991 .nil .nil) .nil) (.node 387031 .nil .nil)) (.node 396061 (.node 395851 (.node 390391 .nil .nil) .nil) (.node 398311 .nil .nil))) (.node 404671 (.node 403261 (.node 402991 (.node 402403 .nil .nil) .nil) (.node 404431 .nil .nil)) (.node 410411 (.node 406981 .nil .nil) (.node 410551 .nil .nil)))))
def t351391 : KeyTree := (.node 351391 t318781 t380563)
def t436171 : KeyTree := (.node 436171 (.node 426973 (.node 418471 (.node 416263 (.node 415381 (.node 415141 .nil .nil) .nil) (.node 417691 .nil .nil)) (.node 426427 (.node 424271 (.node 420421 .nil .nil) .nil) (.node 426931 .nil .nil))) (.node 433291 (.node 432391 (.node 429661 (.node 427351 .nil .nil) .nil) (.node 432631 .nil .nil)) (.node 434281 (.node 434011 .nil .nil) (.node 435541 .nil .nil)))) (.node 454021 (.node 445741 (.node 439891 (.node 438439 (.node 437191 .nil .nil) .nil) (.node 440221 .nil .nil)) (.node 450451 (.node 448141 (.node 447331 .nil .nil) .nil) (.node 453181 .nil .nil))) (.node 459421 (.node 457711 (.node 456457 (.node 455431 .nil .nil) .nil) (.node 459031 .nil .nil)) (.node 460531 (.node 459691 .nil .nil) (.node 462841 .nil .nil)))))
def t487831 : KeyTree := (.node 487831 (.node 473971 (.node 467611 (.node 464647 (.node 464311 (.node 463711 .nil .nil) .nil) (.node 465631 .nil .nil)) (.node 470731 (.node 469561 (.node 467671 .nil .nil) .nil) (.node 471241 .nil .nil))) (.node 485941 (.node 483211 (.node 478171 (.node 474811 .nil .nil) .nil) (.node 483991 .nil .nil)) (.node 486781 (.node 486331 .nil .nil) (.node 486949 .nil .nil)))) (.node 499591 (.node 494761 (.node 493351 (.node 490771 (.node 489061 .nil .nil) .nil) (.node 494341 .nil .nil)) (.node 497491 (.node 496471 (.node 496231 .nil .nil) .nil) (.node 499423 .nil .nil))) (.node 506941 (.node 505051 (.node 502321 (.node 501271 .nil .nil) .nil) (.node 506731 .nil .nil)) (.node 508531 (.node 507781 .nil .nil) (.node 512821 .nil .nil)))))
def t463387 : KeyTree := (.node 463387 t436171 t487831)
def t412567 : KeyTree := (.node 412567 t351391 t463387)
def t281191 : KeyTree := (.node 281191 t157081 t412567)
def t541927 : KeyTree := (.node 541927 (.node 528991 (.node 522523 (.node 520411 (.node 516811 (.node 516517 .nil .nil) .nil) (.node 522061 .nil .nil)) (.node 526681 (.node 523771 (.node 523741 .nil .nil) .nil) (.node 527671 .nil .nil))) (.node 533821 (.node 532771 (.node 532267 (.node 531571 .nil .nil) .nil) (.node 532951 .nil .nil)) (.node 538357 (.node 537811 (.node 534661 .nil .nil) .nil) (.node 540541 .nil .nil)))) (.node 550621 (.node 546631 (.node 545161 (.node 544171 (.node 543661 .nil .nil) .nil) (.node 545791 .nil .nil)) (.node 547639 (.node 547471 (.node 547171 .nil .nil) .nil) (.node 549319 .nil .nil))) (.node 552091 (.node 551461 (.node 551311 (.node 550831 .nil .nil) .nil) (.node 551671 .nil .nil)) (.node 553351 (.node 552553 .nil .nil) (.node 553411 .nil .nil)))))
def t582541 : KeyTree := (.node 582541 (.node 570181 (.node 562591 (.node 560491 (.node 560281 (.node 554611 .nil .nil) .nil) (.node 562021 .nil .nil)) (.node 567631 (.node 565111 (.node 564061 .nil .nil) .nil) (.node 568231 .nil .nil))) (.node 576031 (.node 573343 (.node 572881 (.node 572461 .nil .nil) .nil) (.node 573871 .nil .nil)) (.node 581197 (.node 577831 .nil .nil) (.node 581491 .nil .nil)))) (.node 594511 (.node 587731 (.node 586741 (.node 585391 (.node 584971 .nil .nil) .nil) (.node 586951 .nil .nil)) (.node 592621 (.node 591091 (.node 590071 .nil .nil) .nil) (.node 594091 .nil .nil))) (.node 605221 (.node 599611 (.node 595981 (.node 595141 .nil .nil) .nil) (.node 600601 .nil .nil)) (.node 607531 (.node 606607 .nil .nil) (.node 608191 .nil .nil)))))
def t554269 : KeyTree := (.node 554269 t541927 t582541)
def t633271 : KeyTree := (.node 633271 (.node 623221 (.node 619711 (.node 616171 (.node 615031 (.node 614041 .nil .nil) .nil) (.node 618619 .nil .nil)) (.node 622051 (.node 620491 (.node 620311 .nil .nil) .nil) (.node 623071 .nil .nil))) (.node 627271 (.node 626011 (.node 625171 (.node 624031 .nil .nil) .nil) (.node 626341 .nil .nil)) (.node 631471 (.node 627901 .nil .nil) (.node 632941 .nil .nil)))) (.node 647011 (.node 641131 (.node 639211 (.node 635461 (.node 633931 .nil .nil) .nil) (.node 640771 .nil .nil)) (.node 644671 (.node 644491 (.node 641551 .nil .nil) .nil) (.node 644911 .nil .nil))) (.node 653311 (.node 652081 (.node 650761 (.node 647131 .nil .nil) .nil) (.node 652741 .nil .nil)) (.node 656671 (.node 656371 .nil .nil) (.node 657931 .nil .nil)))))
def t699271 : KeyTree := (.node 699271 (.node 681451 (.node 669901 (.node 668221 (.node 664621 (.node 660661 .nil .nil) .nil) (.node 668611 .nil .nil)) (.node 675511 (.node 671581 (.node 671161 .nil .nil) .nil) (.node 677041 .nil .nil))) (.node 692581 (.node 690271 (.node 689131 (.node 685231 .nil .nil) .nil) (.node 691531 .nil .nil)) (.node 694261 (.node 693421 .nil .nil) (.node 695641 .nil .nil)))) (.node 714841 (.node 705181 (.node 703561 (.node 701611 (.node 699931 .nil .nil) .nil) (.node 704551 .nil .nil)) (.node 710221 (.node 707071 (.node 705871 .nil .nil) .nil) (.node 712531 .nil .nil))) (.node 721141 (.node 719671 (.node 718621 (.node 718411 .nil .nil) .nil) (.node 721051 .nil .nil)) (.node 723031 (.node 722611 .nil .nil) (.node 723451 .nil .nil)))))
def t658351 : KeyTree := (.node 658351 t633271 t699271)
def t612613 : KeyTree := (.node 612613 t554269 t658351)
def t763141 : KeyTree := (.node 763141 (.node 738151 (.node 731851 (.node 729301 (.node 728911 (.node 726181 .nil .nil) .nil) (.node 729331 .nil .nil)) (.node 735421 (.node 733591 (.node 732271 .nil .nil) .nil) (.node 737881 .nil .nil))) (.node 755371 (.node 748021 (.node 742981 (.node 740461 .nil .nil) .nil) (.node 750121 .nil .nil)) (.node 760411 (.node 758941 .nil .nil) (.node 761671 .nil .nil)))) (.node 790021 (.node 772591 (.node 767551 (.node 767131 (.node 764611 .nil .nil) .nil) (.node 769231 .nil .nil)) (.node 787711 (.node 778051 (.node 774691 .nil .nil) .nil) (.node 788971 .nil .nil))) (.node 801571 (.node 797161 (.node 796951 (.node 794641 .nil .nil) .nil) (.node 799891 .nil .nil)) (.node 808081 (.node 802231 .nil .nil) (.node 813961 .nil .nil)))))
def t1272811 : KeyTree := (.node 1272811 (.node 857011 (.node 824671 (.node 821101 (.node 820051 (.node 816271 .nil .nil) .nil) (.node 822361 .nil .nil)) (.node 850081 (.node 840841 (.node 829921 .nil .nil) .nil) (.node 852391 .nil .nil))) (.node 960961 (.node 903211 (.node 870871 (.node 859321 .nil .nil) .nil) (.node 930931 .nil .nil)) (.node 1193011 (.node 1138831 .nil .nil) (.node 1231231 .nil .nil)))) (.node 1806421 (.node 1492261 (.node 1411411 (.node 1381381 (.node 1360591 .nil .nil) .nil) (.node 1452991 .nil .nil)) (.node 1647031 (.node 1623931 (.node 1504231 .nil .nil) .nil) (.node 1741741 .nil .nil))) (.node 2012011 (.node 1939939 (.node 1861861 (.node 1831831 .nil .nil) .nil) (.node 1967071 .nil .nil)) (.node 2081311 (.node 2042041 .nil .nil) (.node 2114971 .nil .nil)))))
def t815431 : KeyTree := (.node 815431 t763141 t1272811)
def t2672671 : KeyTree := (.node 2672671 (.node 2437891 (.node 2282281 (.node 2238391 (.node 2230411 (.node 2181271 .nil .nil) .nil) (.node 2277661 .nil .nil)) (.node 2372371 (.node 2348347 (.node 2323231 .nil .nil) .nil) (.node 2381191 .nil .nil))) (.node 2624623 (.node 2574391 (.node 2478631 (.node 2459731 .nil .nil) .nil) (.node 2582581 .nil .nil)) (.node 2645371 (.node 2631091 .nil .nil) (.node 2661331 .nil .nil)))) (.node 2916691 (.node 2762761 (.node 2699971 (.node 2691781 (.node 2677291 .nil .nil) .nil) (.node 2738191 .nil .nil)) (.node 2866711 (.node 2831011 (.node 2771341 .nil .nil) .nil) (.node 2897311 .nil .nil))) (.node 3091111 (.node 2990131 (.node 2984521 (.node 2940631 .nil .nil) .nil) (.node 3038071 .nil .nil)) (.node 3109471 (.node 3102331 .nil .nil) (.node 3131311 .nil .nil)))))
def t3598981 : KeyTree := (.node 3598981 (.node 3366511 (.node 3304291 (.node 3245971 (.node 3209431 (.node 3164071 .nil .nil) .nil) (.node 3295111 .nil .nil)) (.node 3354781 (.node 3333331 (.node 3327871 .nil .nil) .nil) (.node 3365671 .nil .nil))) (.node 3483481 (.node 3404311 (.node 3387931 (.node 3377221 .nil .nil) .nil) (.node 3453451 .nil .nil)) (.node 3550471 (.node 3530731 .nil .nil) (.node 3559711 .nil .nil)))) (.node 3993991 (.node 3730651 (.node 3693691 (.node 3675211 (.node 3663661 .nil .nil) .nil) (.node 3723721 .nil .nil)) (.node 3818431 (.node 3813811 (.node 3805621 .nil .nil) .nil) (.node 3873871 .nil .nil))) (.node 14804791 (.node 4084081 (.node 4037881 (.node 4024021 .nil .nil) .nil) (.node 13123111 .nil .nil)) (.node 17160991 (.node 16546531 .nil .nil) (.node 18888871 .nil .nil)))))
def t3134671 : KeyTree := (.node 3134671 t2672671 t3598981)
def t2134861 : KeyTree := (.node 2134861 t815431 t3134671)
def t725341 : KeyTree := (.node 725341 t612613 t2134861)
def t514711 : KeyTree := (.node 514711 t281191 t725341)
def t132331 : KeyTree := (.node 132331 t84391 t514711)
def t41611 : KeyTree := (.node 41611 t9157 t132331)
def table := t41611
def rest : List Nat := [7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913]
def primes := 2::3::5::rest
end SunSieveLiteral

open SunSieve Finset
namespace SunSieveLiteral
def divisorsToTry : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43]
def primeScreen (n : Nat) := decide (2≤n) && divisorsToTry.all fun d => decide (n=d ∨ n%d ≠ 0)

theorem primeScreen_of_prime {p : Nat} (hp : p.Prime) : primeScreen p := by
  simp only [primeScreen,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  refine ⟨hp.two_le,?_⟩
  intro d hd
  by_cases h : p=d
  · exact Or.inl h
  · refine Or.inr fun hm => ?_
    have hh : divisorsToTry.all (fun d => decide (1<d)) = true := by decide
    have hd' : 1<d := of_decide_eq_true (List.all_eq_true.mp hh d hd)
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hm) with he|he <;> omega

theorem quick_primes : primes = (List.range 1922).filter primeScreen := by decide +kernel
theorem prime_contains (p : Nat) (h : p<1922) (hp : p.Prime) : p∈primes := by
  rw [quick_primes]
  exact List.mem_filter.mpr ⟨List.mem_range.mpr h,primeScreen_of_prime hp⟩

theorem primes_sorted_lt : primes.Pairwise (·<·) := by
  rw [← List.isChain_iff_pairwise]
  decide +kernel
theorem primes_sorted : primes.Pairwise (·≤·) := primes_sorted_lt.imp (fun h => Nat.le_of_lt h)
theorem primes_nodup : primes.Nodup := primes_sorted_lt.imp (fun h => Nat.ne_of_lt h)
end SunSieveLiteral
namespace SunSieve
open Finset
theorem universal_quick_coverage (t : KeyTree) (ps : List Nat)
    (hdu : ps.Nodup) (hcontains : ∀ p, p<1922 → p.Prime → p∈ps) (hsort : ps.Pairwise (·≤·))
    (test : visit (leafTest t) ps 480 1 ⟨1,1,1⟩)
    {n : Nat} (hb : n+1 ∈ fieldExceptions) : n+1 ∈ t.keys := by
  have hfield := (fieldExceptions_iff n).mp hb
  have hn : 0<n := by omega
  have hc := cost_lt hn (graph_bad_implies_bad (by omega) hfield.2.1)
  have hsub : n.primeFactors ⊆ ps.toFinset := by
    intro p hp
    exact List.mem_toFinset.mpr (hcontains p (factor_bounds hp hc).1 (Nat.prime_of_mem_primeFactors hp))
  have hz {p : Nat} (h : p ∉ n.primeFactors) : n.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (show p ∉ n.factorization.support from h)
  have hpos {p : Nat} (hp : p ∈ n.primeFactors) : n.factorization p ≠ 0 :=
    ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hp)).ne'
  have reduce (f : Nat → Nat → Nat) (h₀ : ∀ q, f q 0=1) :
      (ps.map (fun p => f p (n.factorization p))).prod =
      ∏ p ∈ n.primeFactors,f p (n.factorization p) := by
    rw [← List.prod_toFinset _ hdu,← Finset.prod_subset hsub (fun x _ hx => by rw [hz hx,h₀])]
  have result := visit_sound (leafTest t) ps 480 1 ⟨1,1,1⟩ (fun p => n.factorization p) hsort
    (fun p _ => by
      by_cases hp : p ∈ n.primeFactors
      · simp [budgetFactor,hpos hp,step_ge_one (Nat.prime_of_mem_primeFactors hp)]
      · simp [budgetFactor,hz hp])
    (fun p hp => by by_cases h : p∈n.primeFactors; exact (factor_bounds h hc).2; simp [hz h])
    (by decide) (by
      simp only [Nat.cast_one,mul_one,Nat.cast_ofNat]
      rw [← List.prod_toFinset _ hdu, ← Finset.prod_subset hsub (fun x _ hx => by simp [budgetFactor,hz hx])]
      convert hc using 1
      unfold cost; apply prod_congr rfl; intro p hp; simp [budgetFactor,hpos hp]) test
  have hv := reduce (fun p e => p^e) (by simp)
  have hφ := reduce phiPart (by simp [phiPart])
  have hw := reduce (fun _ e => wPart e) (by simp [wPart])
  rw [← Nat.prod_primeFactors_pow_factorization hn.ne'] at hv
  have hφ' : (ps.map (fun p => phiPart p (n.factorization p))).prod = n.totient := by
    rw [hφ,Nat.totient_eq_prod_factorization hn.ne',Nat.prod_factorization_eq_prod_primeFactors]
    apply prod_congr rfl; intro p hp; simp [phiPart,hpos hp]
  have hw' : (ps.map (fun p => wPart (n.factorization p))).prod = 2^n.primeFactors.card := by
    rw [hw,← Finset.prod_const (s:=n.primeFactors) (b:=2)]
    apply prod_congr rfl; intro p hp; simp [wPart,hpos hp]
  apply leafTest_sound _ hfield
  simpa only [finish,one_mul,hv,hφ',hw'] using result

end SunSieve

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b000 : visit (leafTest table) rest 480 1 ⟨1,1,1⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b031 : visit (leafTest table) rest 480 9 ⟨135,72,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b110 : visit (leafTest table) rest 480 1 ⟨6,2,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b142 : visit (leafTest table) rest 480 135 ⟨4050,1080,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b220 : visit (leafTest table) rest 480 6 ⟨36,12,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b303 : visit (leafTest table) rest 480 100 ⟨1000,400,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b400 : visit (leafTest table) rest 480 8 ⟨16,8,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b500 : visit (leafTest table) rest 480 16 ⟨32,16,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b601 : visit (leafTest table) rest 480 32 ⟨320,128,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b721 : visit (leafTest table) rest 480 192 ⟨5760,1536,8⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b001 : visit (leafTest table) rest 480 1 ⟨5,4,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b032 : visit (leafTest table) rest 480 45 ⟨675,360,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b111 : visit (leafTest table) rest 480 1 ⟨30,8,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b150 : visit (leafTest table) rest 480 81 ⟨486,162,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b221 : visit (leafTest table) rest 480 6 ⟨180,48,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b310 : visit (leafTest table) rest 480 4 ⟨24,8,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b401 : visit (leafTest table) rest 480 8 ⟨80,32,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b501 : visit (leafTest table) rest 480 16 ⟨160,64,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b602 : visit (leafTest table) rest 480 160 ⟨1600,640,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b800 : visit (leafTest table) rest 480 128 ⟨256,128,2⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b002 : visit (leafTest table) rest 480 5 ⟨25,20,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b033 : visit (leafTest table) rest 480 225 ⟨3375,1800,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b112 : visit (leafTest table) rest 480 5 ⟨150,40,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b151 : visit (leafTest table) rest 480 81 ⟨2430,648,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b222 : visit (leafTest table) rest 480 30 ⟨900,240,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b311 : visit (leafTest table) rest 480 4 ⟨120,32,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b402 : visit (leafTest table) rest 480 40 ⟨400,160,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b502 : visit (leafTest table) rest 480 80 ⟨800,320,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b610 : visit (leafTest table) rest 480 32 ⟨192,64,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b801 : visit (leafTest table) rest 480 128 ⟨1280,512,4⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b003 : visit (leafTest table) rest 480 25 ⟨125,100,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b040 : visit (leafTest table) rest 480 27 ⟨81,54,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b113 : visit (leafTest table) rest 480 25 ⟨750,200,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b152 : visit (leafTest table) rest 480 405 ⟨12150,3240,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b223 : visit (leafTest table) rest 480 150 ⟨4500,1200,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b312 : visit (leafTest table) rest 480 20 ⟨600,160,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b403 : visit (leafTest table) rest 480 200 ⟨2000,800,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b503 : visit (leafTest table) rest 480 400 ⟨4000,1600,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b611 : visit (leafTest table) rest 480 32 ⟨960,256,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b810 : visit (leafTest table) rest 480 128 ⟨768,256,4⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b004 : visit (leafTest table) rest 480 125 ⟨625,500,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b041 : visit (leafTest table) rest 480 27 ⟨405,216,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b114 : visit (leafTest table) rest 480 125 ⟨3750,1000,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b160 : visit (leafTest table) rest 480 243 ⟨1458,486,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b230 : visit (leafTest table) rest 480 18 ⟨108,36,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b313 : visit (leafTest table) rest 480 100 ⟨3000,800,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b410 : visit (leafTest table) rest 480 8 ⟨48,16,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b510 : visit (leafTest table) rest 480 16 ⟨96,32,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b612 : visit (leafTest table) rest 480 160 ⟨4800,1280,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b811 : visit (leafTest table) rest 480 128 ⟨3840,1024,8⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b010 : visit (leafTest table) rest 480 1 ⟨3,2,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b042 : visit (leafTest table) rest 480 135 ⟨2025,1080,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b120 : visit (leafTest table) rest 480 3 ⟨18,6,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b161 : visit (leafTest table) rest 480 243 ⟨7290,1944,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b231 : visit (leafTest table) rest 480 18 ⟨540,144,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b320 : visit (leafTest table) rest 480 12 ⟨72,24,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b411 : visit (leafTest table) rest 480 8 ⟨240,64,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b511 : visit (leafTest table) rest 480 16 ⟨480,128,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b620 : visit (leafTest table) rest 480 96 ⟨576,192,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b820 : visit (leafTest table) rest 480 384 ⟨2304,768,4⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b011 : visit (leafTest table) rest 480 1 ⟨15,8,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b050 : visit (leafTest table) rest 480 81 ⟨243,162,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b121 : visit (leafTest table) rest 480 3 ⟨90,24,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b200 : visit (leafTest table) rest 480 2 ⟨4,2,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b232 : visit (leafTest table) rest 480 90 ⟨2700,720,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b321 : visit (leafTest table) rest 480 12 ⟨360,96,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b412 : visit (leafTest table) rest 480 40 ⟨1200,320,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b512 : visit (leafTest table) rest 480 80 ⟨2400,640,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b621 : visit (leafTest table) rest 480 96 ⟨2880,768,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b821 : visit (leafTest table) rest 480 384 ⟨11520,3072,8⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b012 : visit (leafTest table) rest 480 5 ⟨75,40,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b051 : visit (leafTest table) rest 480 81 ⟨1215,648,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b122 : visit (leafTest table) rest 480 15 ⟨450,120,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b201 : visit (leafTest table) rest 480 2 ⟨20,8,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b233 : visit (leafTest table) rest 480 450 ⟨13500,3600,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b322 : visit (leafTest table) rest 480 60 ⟨1800,480,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b413 : visit (leafTest table) rest 480 200 ⟨6000,1600,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b513 : visit (leafTest table) rest 480 400 ⟨12000,3200,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b630 : visit (leafTest table) rest 480 288 ⟨1728,576,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b900 : visit (leafTest table) rest 480 256 ⟨512,256,2⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b013 : visit (leafTest table) rest 480 25 ⟨375,200,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b052 : visit (leafTest table) rest 480 405 ⟨6075,3240,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b123 : visit (leafTest table) rest 480 75 ⟨2250,600,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b202 : visit (leafTest table) rest 480 10 ⟨100,40,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b240 : visit (leafTest table) rest 480 54 ⟨324,108,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b323 : visit (leafTest table) rest 480 300 ⟨9000,2400,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b420 : visit (leafTest table) rest 480 24 ⟨144,48,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b520 : visit (leafTest table) rest 480 48 ⟨288,96,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b631 : visit (leafTest table) rest 480 288 ⟨8640,2304,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b901 : visit (leafTest table) rest 480 256 ⟨2560,1024,4⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b014 : visit (leafTest table) rest 480 125 ⟨1875,1000,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b060 : visit (leafTest table) rest 480 243 ⟨729,486,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b124 : visit (leafTest table) rest 480 375 ⟨11250,3000,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b203 : visit (leafTest table) rest 480 50 ⟨500,200,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b241 : visit (leafTest table) rest 480 54 ⟨1620,432,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b330 : visit (leafTest table) rest 480 36 ⟨216,72,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b421 : visit (leafTest table) rest 480 24 ⟨720,192,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b521 : visit (leafTest table) rest 480 48 ⟨1440,384,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b700 : visit (leafTest table) rest 480 64 ⟨128,64,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b910 : visit (leafTest table) rest 480 256 ⟨1536,512,4⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b020 : visit (leafTest table) rest 480 3 ⟨9,6,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b061 : visit (leafTest table) rest 480 243 ⟨3645,1944,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b130 : visit (leafTest table) rest 480 9 ⟨54,18,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b204 : visit (leafTest table) rest 480 250 ⟨2500,1000,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b242 : visit (leafTest table) rest 480 270 ⟨8100,2160,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b331 : visit (leafTest table) rest 480 36 ⟨1080,288,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b422 : visit (leafTest table) rest 480 120 ⟨3600,960,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b522 : visit (leafTest table) rest 480 240 ⟨7200,1920,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b701 : visit (leafTest table) rest 480 64 ⟨640,256,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b911 : visit (leafTest table) rest 480 256 ⟨7680,2048,8⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b021 : visit (leafTest table) rest 480 3 ⟨45,24,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b100 : visit (leafTest table) rest 480 1 ⟨2,1,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b131 : visit (leafTest table) rest 480 9 ⟨270,72,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b210 : visit (leafTest table) rest 480 2 ⟨12,4,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b250 : visit (leafTest table) rest 480 162 ⟨972,324,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b332 : visit (leafTest table) rest 480 180 ⟨5400,1440,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b430 : visit (leafTest table) rest 480 72 ⟨432,144,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b530 : visit (leafTest table) rest 480 144 ⟨864,288,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b702 : visit (leafTest table) rest 480 320 ⟨3200,1280,4⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b022 : visit (leafTest table) rest 480 15 ⟨225,120,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b101 : visit (leafTest table) rest 480 1 ⟨10,4,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b132 : visit (leafTest table) rest 480 45 ⟨1350,360,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b211 : visit (leafTest table) rest 480 2 ⟨60,16,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b251 : visit (leafTest table) rest 480 162 ⟨4860,1296,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b340 : visit (leafTest table) rest 480 108 ⟨648,216,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b431 : visit (leafTest table) rest 480 72 ⟨2160,576,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b531 : visit (leafTest table) rest 480 144 ⟨4320,1152,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b710 : visit (leafTest table) rest 480 64 ⟨384,128,4⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b023 : visit (leafTest table) rest 480 75 ⟨1125,600,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b102 : visit (leafTest table) rest 480 5 ⟨50,20,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b133 : visit (leafTest table) rest 480 225 ⟨6750,1800,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b212 : visit (leafTest table) rest 480 10 ⟨300,80,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b300 : visit (leafTest table) rest 480 4 ⟨8,4,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b341 : visit (leafTest table) rest 480 108 ⟨3240,864,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b432 : visit (leafTest table) rest 480 360 ⟨10800,2880,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b540 : visit (leafTest table) rest 480 432 ⟨2592,864,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b711 : visit (leafTest table) rest 480 64 ⟨1920,512,8⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b024 : visit (leafTest table) rest 480 375 ⟨5625,3000,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b103 : visit (leafTest table) rest 480 25 ⟨250,100,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b140 : visit (leafTest table) rest 480 27 ⟨162,54,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b213 : visit (leafTest table) rest 480 50 ⟨1500,400,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b301 : visit (leafTest table) rest 480 4 ⟨40,16,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b350 : visit (leafTest table) rest 480 324 ⟨1944,648,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b440 : visit (leafTest table) rest 480 216 ⟨1296,432,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b541 : visit (leafTest table) rest 480 432 ⟨12960,3456,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b712 : visit (leafTest table) rest 480 320 ⟨9600,2560,8⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b030 : visit (leafTest table) rest 480 9 ⟨27,18,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b104 : visit (leafTest table) rest 480 125 ⟨1250,500,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b141 : visit (leafTest table) rest 480 27 ⟨810,216,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b214 : visit (leafTest table) rest 480 250 ⟨7500,2000,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b302 : visit (leafTest table) rest 480 20 ⟨200,80,4⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b351 : visit (leafTest table) rest 480 324 ⟨9720,2592,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b441 : visit (leafTest table) rest 480 216 ⟨6480,1728,8⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b600 : visit (leafTest table) rest 480 32 ⟨64,32,2⟩ = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
theorem b720 : visit (leafTest table) rest 480 192 ⟨1152,384,4⟩ = true := by decide +kernel
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
theorem b00 : visit (leafTest table) (5::rest) 480 1 ⟨1,1,1⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b000
  · exact b001
  · exact b002
  · exact b003
  · exact b004
  · exact False.elim ((by decide : ¬ (up 5 5 * 1 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 1 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 1 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 1 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 1 < 480 * down 5 9)) hi)
theorem b01 : visit (leafTest table) (5::rest) 480 1 ⟨3,2,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b010
  · exact b011
  · exact b012
  · exact b013
  · exact b014
  · exact False.elim ((by decide : ¬ (up 5 5 * 1 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 1 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 1 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 1 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 1 < 480 * down 5 9)) hi)
theorem b02 : visit (leafTest table) (5::rest) 480 3 ⟨9,6,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b020
  · exact b021
  · exact b022
  · exact b023
  · exact b024
  · exact False.elim ((by decide : ¬ (up 5 5 * 3 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 3 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 3 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 3 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 3 < 480 * down 5 9)) hi)
theorem b03 : visit (leafTest table) (5::rest) 480 9 ⟨27,18,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b030
  · exact b031
  · exact b032
  · exact b033
  · exact False.elim ((by decide : ¬ (up 5 4 * 9 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 9 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 9 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 9 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 9 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 9 < 480 * down 5 9)) hi)
theorem b04 : visit (leafTest table) (5::rest) 480 27 ⟨81,54,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b040
  · exact b041
  · exact b042
  · exact False.elim ((by decide : ¬ (up 5 3 * 27 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 27 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 27 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 27 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 27 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 27 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 27 < 480 * down 5 9)) hi)
theorem b05 : visit (leafTest table) (5::rest) 480 81 ⟨243,162,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b050
  · exact b051
  · exact b052
  · exact False.elim ((by decide : ¬ (up 5 3 * 81 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 81 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 81 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 81 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 81 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 81 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 81 < 480 * down 5 9)) hi)
theorem b06 : visit (leafTest table) (5::rest) 480 243 ⟨729,486,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b060
  · exact b061
  · exact False.elim ((by decide : ¬ (up 5 2 * 243 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 243 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 243 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 243 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 243 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 243 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 243 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 243 < 480 * down 5 9)) hi)
theorem b10 : visit (leafTest table) (5::rest) 480 1 ⟨2,1,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b100
  · exact b101
  · exact b102
  · exact b103
  · exact b104
  · exact False.elim ((by decide : ¬ (up 5 5 * 1 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 1 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 1 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 1 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 1 < 480 * down 5 9)) hi)
theorem b11 : visit (leafTest table) (5::rest) 480 1 ⟨6,2,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b110
  · exact b111
  · exact b112
  · exact b113
  · exact b114
  · exact False.elim ((by decide : ¬ (up 5 5 * 1 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 1 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 1 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 1 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 1 < 480 * down 5 9)) hi)
theorem b12 : visit (leafTest table) (5::rest) 480 3 ⟨18,6,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b120
  · exact b121
  · exact b122
  · exact b123
  · exact b124
  · exact False.elim ((by decide : ¬ (up 5 5 * 3 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 3 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 3 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 3 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 3 < 480 * down 5 9)) hi)
theorem b13 : visit (leafTest table) (5::rest) 480 9 ⟨54,18,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b130
  · exact b131
  · exact b132
  · exact b133
  · exact False.elim ((by decide : ¬ (up 5 4 * 9 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 9 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 9 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 9 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 9 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 9 < 480 * down 5 9)) hi)
theorem b14 : visit (leafTest table) (5::rest) 480 27 ⟨162,54,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b140
  · exact b141
  · exact b142
  · exact False.elim ((by decide : ¬ (up 5 3 * 27 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 27 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 27 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 27 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 27 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 27 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 27 < 480 * down 5 9)) hi)
theorem b15 : visit (leafTest table) (5::rest) 480 81 ⟨486,162,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b150
  · exact b151
  · exact b152
  · exact False.elim ((by decide : ¬ (up 5 3 * 81 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 81 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 81 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 81 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 81 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 81 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 81 < 480 * down 5 9)) hi)
theorem b16 : visit (leafTest table) (5::rest) 480 243 ⟨1458,486,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b160
  · exact b161
  · exact False.elim ((by decide : ¬ (up 5 2 * 243 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 243 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 243 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 243 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 243 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 243 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 243 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 243 < 480 * down 5 9)) hi)
theorem b20 : visit (leafTest table) (5::rest) 480 2 ⟨4,2,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b200
  · exact b201
  · exact b202
  · exact b203
  · exact b204
  · exact False.elim ((by decide : ¬ (up 5 5 * 2 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 2 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 2 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 2 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 2 < 480 * down 5 9)) hi)
theorem b21 : visit (leafTest table) (5::rest) 480 2 ⟨12,4,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b210
  · exact b211
  · exact b212
  · exact b213
  · exact b214
  · exact False.elim ((by decide : ¬ (up 5 5 * 2 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 2 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 2 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 2 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 2 < 480 * down 5 9)) hi)
theorem b22 : visit (leafTest table) (5::rest) 480 6 ⟨36,12,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b220
  · exact b221
  · exact b222
  · exact b223
  · exact False.elim ((by decide : ¬ (up 5 4 * 6 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 6 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 6 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 6 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 6 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 6 < 480 * down 5 9)) hi)
theorem b23 : visit (leafTest table) (5::rest) 480 18 ⟨108,36,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b230
  · exact b231
  · exact b232
  · exact b233
  · exact False.elim ((by decide : ¬ (up 5 4 * 18 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 18 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 18 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 18 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 18 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 18 < 480 * down 5 9)) hi)
theorem b24 : visit (leafTest table) (5::rest) 480 54 ⟨324,108,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b240
  · exact b241
  · exact b242
  · exact False.elim ((by decide : ¬ (up 5 3 * 54 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 54 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 54 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 54 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 54 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 54 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 54 < 480 * down 5 9)) hi)
theorem b25 : visit (leafTest table) (5::rest) 480 162 ⟨972,324,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b250
  · exact b251
  · exact False.elim ((by decide : ¬ (up 5 2 * 162 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 162 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 162 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 162 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 162 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 162 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 162 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 162 < 480 * down 5 9)) hi)
theorem b30 : visit (leafTest table) (5::rest) 480 4 ⟨8,4,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b300
  · exact b301
  · exact b302
  · exact b303
  · exact False.elim ((by decide : ¬ (up 5 4 * 4 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 4 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 4 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 4 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 4 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 4 < 480 * down 5 9)) hi)
theorem b31 : visit (leafTest table) (5::rest) 480 4 ⟨24,8,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b310
  · exact b311
  · exact b312
  · exact b313
  · exact False.elim ((by decide : ¬ (up 5 4 * 4 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 4 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 4 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 4 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 4 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 4 < 480 * down 5 9)) hi)
theorem b32 : visit (leafTest table) (5::rest) 480 12 ⟨72,24,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b320
  · exact b321
  · exact b322
  · exact b323
  · exact False.elim ((by decide : ¬ (up 5 4 * 12 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 12 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 12 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 12 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 12 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 12 < 480 * down 5 9)) hi)
theorem b33 : visit (leafTest table) (5::rest) 480 36 ⟨216,72,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b330
  · exact b331
  · exact b332
  · exact False.elim ((by decide : ¬ (up 5 3 * 36 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 36 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 36 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 36 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 36 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 36 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 36 < 480 * down 5 9)) hi)
theorem b34 : visit (leafTest table) (5::rest) 480 108 ⟨648,216,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b340
  · exact b341
  · exact False.elim ((by decide : ¬ (up 5 2 * 108 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 108 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 108 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 108 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 108 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 108 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 108 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 108 < 480 * down 5 9)) hi)
theorem b35 : visit (leafTest table) (5::rest) 480 324 ⟨1944,648,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b350
  · exact b351
  · exact False.elim ((by decide : ¬ (up 5 2 * 324 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 324 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 324 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 324 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 324 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 324 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 324 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 324 < 480 * down 5 9)) hi)
theorem b40 : visit (leafTest table) (5::rest) 480 8 ⟨16,8,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b400
  · exact b401
  · exact b402
  · exact b403
  · exact False.elim ((by decide : ¬ (up 5 4 * 8 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 8 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 8 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 8 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 8 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 8 < 480 * down 5 9)) hi)
theorem b41 : visit (leafTest table) (5::rest) 480 8 ⟨48,16,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b410
  · exact b411
  · exact b412
  · exact b413
  · exact False.elim ((by decide : ¬ (up 5 4 * 8 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 8 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 8 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 8 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 8 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 8 < 480 * down 5 9)) hi)
theorem b42 : visit (leafTest table) (5::rest) 480 24 ⟨144,48,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b420
  · exact b421
  · exact b422
  · exact False.elim ((by decide : ¬ (up 5 3 * 24 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 24 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 24 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 24 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 24 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 24 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 24 < 480 * down 5 9)) hi)
theorem b43 : visit (leafTest table) (5::rest) 480 72 ⟨432,144,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b430
  · exact b431
  · exact b432
  · exact False.elim ((by decide : ¬ (up 5 3 * 72 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 72 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 72 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 72 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 72 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 72 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 72 < 480 * down 5 9)) hi)
theorem b44 : visit (leafTest table) (5::rest) 480 216 ⟨1296,432,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b440
  · exact b441
  · exact False.elim ((by decide : ¬ (up 5 2 * 216 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 216 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 216 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 216 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 216 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 216 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 216 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 216 < 480 * down 5 9)) hi)
theorem b50 : visit (leafTest table) (5::rest) 480 16 ⟨32,16,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b500
  · exact b501
  · exact b502
  · exact b503
  · exact False.elim ((by decide : ¬ (up 5 4 * 16 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 16 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 16 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 16 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 16 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 16 < 480 * down 5 9)) hi)
theorem b51 : visit (leafTest table) (5::rest) 480 16 ⟨96,32,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b510
  · exact b511
  · exact b512
  · exact b513
  · exact False.elim ((by decide : ¬ (up 5 4 * 16 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 16 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 16 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 16 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 16 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 16 < 480 * down 5 9)) hi)
theorem b52 : visit (leafTest table) (5::rest) 480 48 ⟨288,96,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b520
  · exact b521
  · exact b522
  · exact False.elim ((by decide : ¬ (up 5 3 * 48 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 48 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 48 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 48 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 48 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 48 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 48 < 480 * down 5 9)) hi)
theorem b53 : visit (leafTest table) (5::rest) 480 144 ⟨864,288,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b530
  · exact b531
  · exact False.elim ((by decide : ¬ (up 5 2 * 144 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 144 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 144 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 144 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 144 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 144 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 144 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 144 < 480 * down 5 9)) hi)
theorem b54 : visit (leafTest table) (5::rest) 480 432 ⟨2592,864,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b540
  · exact b541
  · exact False.elim ((by decide : ¬ (up 5 2 * 432 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 432 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 432 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 432 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 432 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 432 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 432 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 432 < 480 * down 5 9)) hi)
theorem b60 : visit (leafTest table) (5::rest) 480 32 ⟨64,32,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b600
  · exact b601
  · exact b602
  · exact False.elim ((by decide : ¬ (up 5 3 * 32 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 32 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 32 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 32 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 32 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 32 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 32 < 480 * down 5 9)) hi)
theorem b61 : visit (leafTest table) (5::rest) 480 32 ⟨192,64,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b610
  · exact b611
  · exact b612
  · exact False.elim ((by decide : ¬ (up 5 3 * 32 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 32 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 32 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 32 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 32 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 32 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 32 < 480 * down 5 9)) hi)
theorem b62 : visit (leafTest table) (5::rest) 480 96 ⟨576,192,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b620
  · exact b621
  · exact False.elim ((by decide : ¬ (up 5 2 * 96 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 96 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 96 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 96 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 96 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 96 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 96 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 96 < 480 * down 5 9)) hi)
theorem b63 : visit (leafTest table) (5::rest) 480 288 ⟨1728,576,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b630
  · exact b631
  · exact False.elim ((by decide : ¬ (up 5 2 * 288 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 288 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 288 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 288 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 288 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 288 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 288 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 288 < 480 * down 5 9)) hi)
theorem b70 : visit (leafTest table) (5::rest) 480 64 ⟨128,64,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b700
  · exact b701
  · exact b702
  · exact False.elim ((by decide : ¬ (up 5 3 * 64 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 64 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 64 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 64 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 64 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 64 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 64 < 480 * down 5 9)) hi)
theorem b71 : visit (leafTest table) (5::rest) 480 64 ⟨384,128,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b710
  · exact b711
  · exact b712
  · exact False.elim ((by decide : ¬ (up 5 3 * 64 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 64 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 64 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 64 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 64 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 64 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 64 < 480 * down 5 9)) hi)
theorem b72 : visit (leafTest table) (5::rest) 480 192 ⟨1152,384,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b720
  · exact b721
  · exact False.elim ((by decide : ¬ (up 5 2 * 192 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 192 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 192 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 192 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 192 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 192 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 192 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 192 < 480 * down 5 9)) hi)
theorem b80 : visit (leafTest table) (5::rest) 480 128 ⟨256,128,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b800
  · exact b801
  · exact False.elim ((by decide : ¬ (up 5 2 * 128 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 128 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 128 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 128 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 128 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 128 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 128 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 128 < 480 * down 5 9)) hi)
theorem b81 : visit (leafTest table) (5::rest) 480 128 ⟨768,256,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b810
  · exact b811
  · exact False.elim ((by decide : ¬ (up 5 2 * 128 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 128 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 128 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 128 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 128 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 128 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 128 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 128 < 480 * down 5 9)) hi)
theorem b82 : visit (leafTest table) (5::rest) 480 384 ⟨2304,768,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b820
  · exact b821
  · exact False.elim ((by decide : ¬ (up 5 2 * 384 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 384 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 384 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 384 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 384 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 384 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 384 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 384 < 480 * down 5 9)) hi)
theorem b90 : visit (leafTest table) (5::rest) 480 256 ⟨512,256,2⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b900
  · exact b901
  · exact False.elim ((by decide : ¬ (up 5 2 * 256 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 256 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 256 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 256 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 256 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 256 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 256 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 256 < 480 * down 5 9)) hi)
theorem b91 : visit (leafTest table) (5::rest) 480 256 ⟨1536,512,4⟩ = true := by
  apply visit_small 5 (by decide)
  intro i hi
  fin_cases i
  · exact b910
  · exact b911
  · exact False.elim ((by decide : ¬ (up 5 2 * 256 < 480 * down 5 2)) hi)
  · exact False.elim ((by decide : ¬ (up 5 3 * 256 < 480 * down 5 3)) hi)
  · exact False.elim ((by decide : ¬ (up 5 4 * 256 < 480 * down 5 4)) hi)
  · exact False.elim ((by decide : ¬ (up 5 5 * 256 < 480 * down 5 5)) hi)
  · exact False.elim ((by decide : ¬ (up 5 6 * 256 < 480 * down 5 6)) hi)
  · exact False.elim ((by decide : ¬ (up 5 7 * 256 < 480 * down 5 7)) hi)
  · exact False.elim ((by decide : ¬ (up 5 8 * 256 < 480 * down 5 8)) hi)
  · exact False.elim ((by decide : ¬ (up 5 9 * 256 < 480 * down 5 9)) hi)
theorem b0 : visit (leafTest table) (3::5::rest) 480 1 ⟨1,1,1⟩ = true := by
  apply visit_small 3 (by decide)
  intro i hi
  fin_cases i
  · exact b00
  · exact b01
  · exact b02
  · exact b03
  · exact b04
  · exact b05
  · exact b06
  · exact False.elim ((by decide : ¬ (up 3 7 * 1 < 480 * down 3 7)) hi)
  · exact False.elim ((by decide : ¬ (up 3 8 * 1 < 480 * down 3 8)) hi)
  · exact False.elim ((by decide : ¬ (up 3 9 * 1 < 480 * down 3 9)) hi)
theorem b1 : visit (leafTest table) (3::5::rest) 480 1 ⟨2,1,2⟩ = true := by
  apply visit_small 3 (by decide)
  intro i hi
  fin_cases i
  · exact b10
  · exact b11
  · exact b12
  · exact b13
  · exact b14
  · exact b15
  · exact b16
  · exact False.elim ((by decide : ¬ (up 3 7 * 1 < 480 * down 3 7)) hi)
  · exact False.elim ((by decide : ¬ (up 3 8 * 1 < 480 * down 3 8)) hi)
  · exact False.elim ((by decide : ¬ (up 3 9 * 1 < 480 * down 3 9)) hi)
theorem b2 : visit (leafTest table) (3::5::rest) 480 2 ⟨4,2,2⟩ = true := by
  apply visit_small 3 (by decide)
  intro i hi
  fin_cases i
  · exact b20
  · exact b21
  · exact b22
  · exact b23
  · exact b24
  · exact b25
  · exact False.elim ((by decide : ¬ (up 3 6 * 2 < 480 * down 3 6)) hi)
  · exact False.elim ((by decide : ¬ (up 3 7 * 2 < 480 * down 3 7)) hi)
  · exact False.elim ((by decide : ¬ (up 3 8 * 2 < 480 * down 3 8)) hi)
  · exact False.elim ((by decide : ¬ (up 3 9 * 2 < 480 * down 3 9)) hi)
theorem b3 : visit (leafTest table) (3::5::rest) 480 4 ⟨8,4,2⟩ = true := by
  apply visit_small 3 (by decide)
  intro i hi
  fin_cases i
  · exact b30
  · exact b31
  · exact b32
  · exact b33
  · exact b34
  · exact b35
  · exact False.elim ((by decide : ¬ (up 3 6 * 4 < 480 * down 3 6)) hi)
  · exact False.elim ((by decide : ¬ (up 3 7 * 4 < 480 * down 3 7)) hi)
  · exact False.elim ((by decide : ¬ (up 3 8 * 4 < 480 * down 3 8)) hi)
  · exact False.elim ((by decide : ¬ (up 3 9 * 4 < 480 * down 3 9)) hi)
theorem b4 : visit (leafTest table) (3::5::rest) 480 8 ⟨16,8,2⟩ = true := by
  apply visit_small 3 (by decide)
  intro i hi
  fin_cases i
  · exact b40
  · exact b41
  · exact b42
  · exact b43
  · exact b44
  · exact False.elim ((by decide : ¬ (up 3 5 * 8 < 480 * down 3 5)) hi)
  · exact False.elim ((by decide : ¬ (up 3 6 * 8 < 480 * down 3 6)) hi)
  · exact False.elim ((by decide : ¬ (up 3 7 * 8 < 480 * down 3 7)) hi)
  · exact False.elim ((by decide : ¬ (up 3 8 * 8 < 480 * down 3 8)) hi)
  · exact False.elim ((by decide : ¬ (up 3 9 * 8 < 480 * down 3 9)) hi)
theorem b5 : visit (leafTest table) (3::5::rest) 480 16 ⟨32,16,2⟩ = true := by
  apply visit_small 3 (by decide)
  intro i hi
  fin_cases i
  · exact b50
  · exact b51
  · exact b52
  · exact b53
  · exact b54
  · exact False.elim ((by decide : ¬ (up 3 5 * 16 < 480 * down 3 5)) hi)
  · exact False.elim ((by decide : ¬ (up 3 6 * 16 < 480 * down 3 6)) hi)
  · exact False.elim ((by decide : ¬ (up 3 7 * 16 < 480 * down 3 7)) hi)
  · exact False.elim ((by decide : ¬ (up 3 8 * 16 < 480 * down 3 8)) hi)
  · exact False.elim ((by decide : ¬ (up 3 9 * 16 < 480 * down 3 9)) hi)
theorem b6 : visit (leafTest table) (3::5::rest) 480 32 ⟨64,32,2⟩ = true := by
  apply visit_small 3 (by decide)
  intro i hi
  fin_cases i
  · exact b60
  · exact b61
  · exact b62
  · exact b63
  · exact False.elim ((by decide : ¬ (up 3 4 * 32 < 480 * down 3 4)) hi)
  · exact False.elim ((by decide : ¬ (up 3 5 * 32 < 480 * down 3 5)) hi)
  · exact False.elim ((by decide : ¬ (up 3 6 * 32 < 480 * down 3 6)) hi)
  · exact False.elim ((by decide : ¬ (up 3 7 * 32 < 480 * down 3 7)) hi)
  · exact False.elim ((by decide : ¬ (up 3 8 * 32 < 480 * down 3 8)) hi)
  · exact False.elim ((by decide : ¬ (up 3 9 * 32 < 480 * down 3 9)) hi)
theorem b7 : visit (leafTest table) (3::5::rest) 480 64 ⟨128,64,2⟩ = true := by
  apply visit_small 3 (by decide)
  intro i hi
  fin_cases i
  · exact b70
  · exact b71
  · exact b72
  · exact False.elim ((by decide : ¬ (up 3 3 * 64 < 480 * down 3 3)) hi)
  · exact False.elim ((by decide : ¬ (up 3 4 * 64 < 480 * down 3 4)) hi)
  · exact False.elim ((by decide : ¬ (up 3 5 * 64 < 480 * down 3 5)) hi)
  · exact False.elim ((by decide : ¬ (up 3 6 * 64 < 480 * down 3 6)) hi)
  · exact False.elim ((by decide : ¬ (up 3 7 * 64 < 480 * down 3 7)) hi)
  · exact False.elim ((by decide : ¬ (up 3 8 * 64 < 480 * down 3 8)) hi)
  · exact False.elim ((by decide : ¬ (up 3 9 * 64 < 480 * down 3 9)) hi)
theorem b8 : visit (leafTest table) (3::5::rest) 480 128 ⟨256,128,2⟩ = true := by
  apply visit_small 3 (by decide)
  intro i hi
  fin_cases i
  · exact b80
  · exact b81
  · exact b82
  · exact False.elim ((by decide : ¬ (up 3 3 * 128 < 480 * down 3 3)) hi)
  · exact False.elim ((by decide : ¬ (up 3 4 * 128 < 480 * down 3 4)) hi)
  · exact False.elim ((by decide : ¬ (up 3 5 * 128 < 480 * down 3 5)) hi)
  · exact False.elim ((by decide : ¬ (up 3 6 * 128 < 480 * down 3 6)) hi)
  · exact False.elim ((by decide : ¬ (up 3 7 * 128 < 480 * down 3 7)) hi)
  · exact False.elim ((by decide : ¬ (up 3 8 * 128 < 480 * down 3 8)) hi)
  · exact False.elim ((by decide : ¬ (up 3 9 * 128 < 480 * down 3 9)) hi)
theorem b9 : visit (leafTest table) (3::5::rest) 480 256 ⟨512,256,2⟩ = true := by
  apply visit_small 3 (by decide)
  intro i hi
  fin_cases i
  · exact b90
  · exact b91
  · exact False.elim ((by decide : ¬ (up 3 2 * 256 < 480 * down 3 2)) hi)
  · exact False.elim ((by decide : ¬ (up 3 3 * 256 < 480 * down 3 3)) hi)
  · exact False.elim ((by decide : ¬ (up 3 4 * 256 < 480 * down 3 4)) hi)
  · exact False.elim ((by decide : ¬ (up 3 5 * 256 < 480 * down 3 5)) hi)
  · exact False.elim ((by decide : ¬ (up 3 6 * 256 < 480 * down 3 6)) hi)
  · exact False.elim ((by decide : ¬ (up 3 7 * 256 < 480 * down 3 7)) hi)
  · exact False.elim ((by decide : ¬ (up 3 8 * 256 < 480 * down 3 8)) hi)
  · exact False.elim ((by decide : ¬ (up 3 9 * 256 < 480 * down 3 9)) hi)
theorem b : visit (leafTest table) (2::3::5::rest) 480 1 ⟨1,1,1⟩ = true := by
  apply visit_small 2 (by decide)
  intro i hi
  fin_cases i
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5
  · exact b6
  · exact b7
  · exact b8
  · exact b9
end SunSieveLiteral

namespace SunSieveLiteral
open SunSieve
theorem coverage {n : Nat} (h : n+1 ∈ fieldExceptions) : n+1 ∈ table.keys :=
  universal_quick_coverage table primes primes_nodup prime_contains primes_sorted b h
end SunSieveLiteral

open SunSieve
namespace SunSieveLiteral
def pick : List Nat → List Bool → Bool → List Nat
  | [],_,_ => []
  | xs,[],b => if b then xs else []
  | x::xs,a::as',b => if a=b then x::pick xs as' b else pick xs as' b

theorem mem_pick {q : Nat} {xs : List Nat} (h : q ∈ xs) (m : List Bool) :
    q ∈ pick xs m true ∨ q ∈ pick xs m false := by
  induction xs generalizing m with
  | nil => simp at h
  | cons x xs ih =>
    cases m with
    | nil => simp [pick,h]
    | cons a as' =>
      rcases List.mem_cons.mp h with rfl|ht
      · cases a <;> simp [pick]
      · rcases ih ht as' with hl|hr
        · cases a <;> simp [pick,hl]
        · cases a <;> simp [pick,hr]

def marks := ([0, 0, 1, 0, 3, 0, 6, 3, 4, 8, 0, 9, 14, 1, 6, 7, 2, 21, 10, 11, 12, 12, 7, 33, 1, 32, 17, 34, 1, 19, 34, 43, 18, 22, 16, 19, 41, 25, 34, 82, 10, 48, 7, 22, 58, 34, 48, 56, 13, 71, 11, 98, 32, 70, 49, 32, 168, 105, 21, 91, 62, 99, 56, 19, 53, 69, 220, 34, 28]:List Nat).flatMap (fun k => List.replicate k true ++ [false])
def extensionOrders : List Nat := [8, 9, 16, 25, 27, 49, 64, 81, 121, 125, 169, 243, 256, 289, 343, 361, 529, 625, 729, 841, 961, 1024, 1331, 1369, 1681, 1849, 2197, 2209, 2401, 2809, 3481, 3721, 4096, 4489, 5041, 6241, 6889, 7921, 10201, 10609, 11881, 12167, 12769, 14641, 15625, 17161, 18769, 19321, 22201, 22801, 28561, 32761, 44521, 52441, 57121, 78961, 94249, 96721, 109561, 121801, 143641, 175561, 212521, 326041, 434281, 737881, 829921, 2042041]
def otherOrders : List Nat := [8, 9, 13, 16, 25, 27, 49, 64, 81, 121, 125, 169, 243, 256, 289, 343, 361, 529, 625, 729, 841, 961, 1024, 1331, 1369, 1681, 1849, 2197, 2209, 2401, 2809, 3481, 3721, 4096, 4489, 5041, 6241, 6889, 7921, 10201, 10609, 11881, 12167, 12769, 14641, 15625, 17161, 18769, 19321, 22201, 22801, 28561, 32761, 44521, 52441, 57121, 78961, 94249, 96721, 109561, 121801, 143641, 175561, 212521, 326041, 434281, 737881, 829921, 2042041]
set_option maxRecDepth 100000 in
theorem prime_keys : pick table.keys marks true = SunBatchPrime.primeOrders := by decide +kernel
set_option maxRecDepth 100000 in
theorem other_keys : pick table.keys marks false = otherOrders := by decide +kernel
theorem other_keys_split : ∀ q ∈ otherOrders, q ∈ extensionOrders ∨ q=13 := by
  have h : otherOrders.all (fun q => decide (q∈extensionOrders ∨ q=13)) = true := by decide +kernel
  exact fun q hq => of_decide_eq_true ((List.all_eq_true.mp h) q hq)
theorem keys_split : ∀ q ∈ table.keys, q ∈ SunBatchPrime.primeOrders ∨ q ∈ extensionOrders ∨ q=13 := by
  intro q h
  have hm := mem_pick h marks
  rw [prime_keys,other_keys] at hm
  exact hm.imp_right (other_keys_split q)
end SunSieveLiteral

namespace SunSieveLiteral
theorem fieldOrders {n : Nat} (h : n+1 ∈ SunSieve.fieldExceptions) :
    n+1 ∈ SunBatchPrime.primeOrders ∨ n+1 ∈ SunBatchExtension.extensionOrders ∨ n+1=13 := by
  exact keys_split _ (coverage h)
end SunSieveLiteral

namespace SunFieldGraph
theorem outside_exceptions (F : Type*) [Field F] [Fintype F]
    (hF : Fintype.card F > 7) (hout : Fintype.card F ∉ SunSieve.fieldExceptions) :
    let m := Fintype.card F - 1
    ∃ a : Fin m ≃ Fˣ, ∀ i : Fin m, IsPrimitiveRoot
      ((a i : F) * (a ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩ : F) + 1) m := by
  classical
  apply SunGraph.conjecture_of_hamiltonian F hF
  have hq : Fintype.card Fˣ + 1 = Fintype.card F := by rw [Fintype.card_units]; omega
  have hb : ⌊budget F⌋₊ = SunSieve.graphM (Fintype.card Fˣ) := by
    unfold budget
    conv_lhs => rw [← hq]
    exact SunSieve.floor_graphM _
  apply hamiltonian F (by omega)
  rw [hb]
  by_contra! bad
  apply hout
  rw [← hq]
  exact (SunSieve.fieldExceptions_iff _).mpr
    ⟨by omega,bad, hq.symm ▸ FiniteField.isPrimePow_card F⟩
end SunFieldGraph

theorem OMA.solution : type_of% @OeisA229232.conjecture_5 := by
  intro F _ _ hF
  classical
  by_cases he : Fintype.card F ∈ SunSieve.fieldExceptions
  · have hq : (Fintype.card F - 1) + 1 = Fintype.card F := by omega
    have h := SunSieveLiteral.fieldOrders (n := Fintype.card F - 1) (hq.symm ▸ he)
    rw [hq] at h
    rcases h with hp | hx | h13
    · exact SunFinish.of_prime_certificate F rfl (SunBatchPrime.primeOrders_good _ hp)
    · obtain ⟨_,a,ha⟩ := SunBatchExtension.extensionOrders_good _ hx F rfl
      exact ⟨a,ha⟩
    · exact SunFinish.of_prime_certificate F h13 SunBatchPrime.good_thirteen
  · exact SunFieldGraph.outside_exceptions F hF he
