import OMAReductions.R_riemannZeta_distinct_prop_lt_R1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Sum
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Finite packing for the Montgomery--Taylor kernel.
Exact target: riemannZeta.distinct_prop_lt.R1.H2.

The mathematical zero-set/compactness argument is described in
https://github.com/ainta/zeta-simple-zeros/blob/main/docs/proof.md, Section 3.
This is a formalization of that argument, not new analytic number theory.
The distinct weighted spectral theorem in Oliverds321/simple-zeros is not used.
Registration attempt returned HTTP 500; no current lease is asserted.
-/

open scoped BigOperators
open Set

namespace OMA.ZetaPacking


noncomputable def c : ℝ := 1 / Real.sqrt 2

noncomputable def K (x : ℝ) : ℝ :=
  (Real.sinc (Real.pi * x - c) + Real.sinc (Real.pi * x + c)) /
    (2 * Real.sinc c)

set_option maxHeartbeats 800000 in
lemma c_pos : 0 < c := by unfold c; positivity

set_option maxHeartbeats 800000 in
lemma c_lt_one : c < 1 := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs1 : 1 < Real.sqrt 2 := by nlinarith
  exact (div_lt_one hs).2 hs1

set_option maxHeartbeats 800000 in
lemma c_lt_pi_half : c < Real.pi / 2 := by
  linarith [c_lt_one, Real.pi_gt_three]

set_option maxHeartbeats 800000 in
lemma cos_c_pos : 0 < Real.cos c :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [c_pos, Real.pi_pos], c_lt_pi_half⟩

set_option maxHeartbeats 800000 in
lemma sinc_c_pos : 0 < Real.sinc c := by
  rw [Real.sinc_of_ne_zero c_pos.ne']
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi c_pos
    (by linarith [c_lt_pi_half, Real.pi_pos])) c_pos

set_option maxHeartbeats 800000 in
lemma sinc_mul (t : ℝ) : Real.sinc t * t = Real.sin t := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [Real.sinc_of_ne_zero ht, div_mul_cancel₀ _ ht]

noncomputable def beta : ℝ := c * Real.tan c

set_option maxHeartbeats 800000 in
lemma beta_pos : 0 < beta :=
  mul_pos c_pos (Real.tan_pos_of_pos_of_lt_pi_div_two c_pos c_lt_pi_half)

set_option maxHeartbeats 800000 in
lemma zero_equation {x : ℝ} (hx : K x = 0) :
    (Real.pi * x) * Real.sin (Real.pi * x) = beta * Real.cos (Real.pi * x) := by
  have hden : 2 * Real.sinc c ≠ 0 := ne_of_gt (mul_pos (by norm_num) sinc_c_pos)
  have hsum : Real.sinc (Real.pi * x - c) + Real.sinc (Real.pi * x + c) = 0 := by
    exact (div_eq_zero_iff.mp hx).resolve_right hden
  have hp : Real.sin (Real.pi*x-c)*(Real.pi*x+c) +
      Real.sin (Real.pi*x+c)*(Real.pi*x-c) = 0 := by
    calc
      _ = (Real.sinc (Real.pi*x-c) + Real.sinc (Real.pi*x+c)) *
          (Real.pi*x-c)*(Real.pi*x+c) := by
        rw [← sinc_mul (Real.pi*x-c), ← sinc_mul (Real.pi*x+c)]
        ring
      _ = 0 := by rw [hsum]; ring
  have he : (Real.pi * x) * Real.sin (Real.pi * x) * Real.cos c =
      c * Real.cos (Real.pi * x) * Real.sin c := by
    rw [Real.sin_sub, Real.sin_add] at hp
    nlinarith [hp]
  unfold beta
  rw [Real.tan_eq_sin_div_cos]
  field_simp [cos_c_pos.ne']
  nlinarith [he]

set_option maxHeartbeats 800000 in
lemma zero_tan {x : ℝ} (hx : K x = 0) :
    Real.pi * x ≠ 0 ∧ Real.cos (Real.pi * x) ≠ 0 ∧
      Real.tan (Real.pi * x) = beta / (Real.pi * x) := by
  have he := zero_equation hx
  have ht : Real.pi * x ≠ 0 := by
    intro h
    rw [h, Real.sin_zero, Real.cos_zero] at he
    nlinarith [beta_pos]
  have hc : Real.cos (Real.pi * x) ≠ 0 := by
    intro h
    have hs : Real.sin (Real.pi * x) = 0 := by
      have : (Real.pi * x) * Real.sin (Real.pi * x) = 0 := by simpa [h] using he
      exact (mul_eq_zero.mp this).resolve_left ht
    have := Real.sin_sq_add_cos_sq (Real.pi * x)
    simp [h, hs] at this
  refine ⟨ht, hc, ?_⟩
  rw [Real.tan_eq_sin_div_cos]
  apply (div_eq_div_iff hc ht).2
  nlinarith [he]

set_option maxHeartbeats 800000 in
lemma tangent_add_cross (t s : ℝ) (hct : Real.cos t ≠ 0)
    (hcs : Real.cos s ≠ 0) (hcu : Real.cos (t+s) ≠ 0) :
    Real.tan t + Real.tan s = Real.tan (t+s)*(1-Real.tan t*Real.tan s) := by
  simp only [Real.tan_eq_sin_div_cos]
  field_simp [hct, hcs, hcu]
  rw [Real.sin_add, Real.cos_add]

set_option maxHeartbeats 800000 in
lemma ratio_obstruction (t s b : ℝ) (hb : 0 < b)
    (ht : t ≠ 0) (hs : s ≠ 0) (hu : t+s ≠ 0)
    (he : b/t+b/s = b/(t+s)*(1-b/t*(b/s))) : False := by
  have hpoly : b*(t^2+t*s+s^2+b^2) = 0 := by
    field_simp [ht, hs, hu] at he
    nlinarith [he]
  have hzq := (mul_eq_zero.mp hpoly).resolve_left hb.ne'
  nlinarith [sq_nonneg (t+s), sq_nonneg t, sq_nonneg s, sq_pos_of_pos hb]

set_option maxHeartbeats 800000 in
lemma no_three_zeros (x y : ℝ) : ¬ (K x = 0 ∧ K y = 0 ∧ K (x + y) = 0) := by
  rintro ⟨hx, hy, hz⟩
  obtain ⟨ht, hct, htan⟩ := zero_tan hx
  obtain ⟨hs, hcs, hsan⟩ := zero_tan hy
  obtain ⟨hu, hcu, huan⟩ := zero_tan hz
  rw [mul_add] at hu hcu huan
  have hadd := tangent_add_cross (Real.pi*x) (Real.pi*y) hct hcs hcu
  rw [htan, hsan, huan] at hadd
  exact ratio_obstruction _ _ _ beta_pos ht hs hu hadd

set_option maxHeartbeats 800000 in
lemma continuous_K : Continuous K := by
  unfold K
  exact ((Real.continuous_sinc.comp ((continuous_const.mul continuous_id).sub continuous_const)).add
    (Real.continuous_sinc.comp ((continuous_const.mul continuous_id).add continuous_const))).div_const _

set_option maxHeartbeats 800000 in
lemma energy_pos (x y : ℝ) : 0 < (K x)^2 + (K y)^2 + (K (x+y))^2 := by
  have hx := sq_nonneg (K x)
  have hy := sq_nonneg (K y)
  have hz := sq_nonneg (K (x+y))
  by_contra h
  have hle : (K x)^2 + (K y)^2 + (K (x+y))^2 ≤ 0 := le_of_not_gt h
  have hx0 : K x = 0 := by nlinarith
  have hy0 : K y = 0 := by nlinarith
  have hz0 : K (x+y) = 0 := by nlinarith
  exact no_three_zeros x y ⟨hx0, hy0, hz0⟩

set_option maxHeartbeats 800000 in
lemma uniform_energy : ∃ η : ℝ, 0 < η ∧ ∀ u v w : ℝ,
    |u-v| ≤ 100 → |v-w| ≤ 100 →
      η ≤ (K (u-v))^2 + (K (v-w))^2 + (K (u-w))^2 := by
  let E : ℝ × ℝ → ℝ := fun p => (K p.1)^2 + (K p.2)^2 + (K (p.1+p.2))^2
  have hE : Continuous E := by
    exact (((continuous_K.comp continuous_fst).pow 2).add
      ((continuous_K.comp continuous_snd).pow 2)).add
        ((continuous_K.comp (continuous_fst.add continuous_snd)).pow 2)
  obtain ⟨η, hη, hbound⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_forall_le'
      (f := E) (s := Set.Icc (-100 : ℝ) 100 ×ˢ Set.Icc (-100 : ℝ) 100)
      hE.continuousOn (fun p _ => energy_pos p.1 p.2)
  refine ⟨η, hη, ?_⟩
  intro u v w huv hvw
  have hb := hbound (u-v, v-w) ⟨abs_le.mp huv, abs_le.mp hvw⟩
  dsimp [E] at hb
  have he : u-v+(v-w) = u-w := by ring
  simpa only [he] using hb

/- Group each fiber of a map into triples, losing at most two elements per fiber. -/
set_option maxHeartbeats 800000 in
lemma group_fibers {X B : Type*} [Fintype X] [Fintype B] (f : X → B) :
    ∃ (n : ℕ) (q : Fin n → Fin 3 → X),
      Function.Injective (fun p : Fin n × Fin 3 => q p.1 p.2) ∧
      (∀ i j k, f (q i j) = f (q i k)) ∧
      Fintype.card X ≤ 3*n + 2*Fintype.card B := by
  classical
  let C : B → Type _ := fun b => {x : X // f x = b}
  let I := (b : B) × Fin (Fintype.card (C b) / 3)
  let pick (i : I) (j : Fin 3) : C i.1 :=
    (Fintype.equivFin (C i.1)).symm ⟨3*i.2.val+j.val, by
      have hi := i.2.isLt
      have hj := j.isLt
      omega⟩
  let q (i : I) (j : Fin 3) : X := (pick i j).val
  have hf (i : I) (j : Fin 3) : f (q i j) = i.1 := (pick i j).property
  have hq : Function.Injective (fun p : I × Fin 3 => q p.1 p.2) := by
    rintro ⟨⟨b,i⟩,j⟩ ⟨⟨b',i'⟩,j'⟩ h
    have hb : b = b' := (hf ⟨b,i⟩ j).symm.trans ((congrArg f h).trans (hf ⟨b',i'⟩ j'))
    subst b'
    have he : pick ⟨b,i⟩ j = pick ⟨b,i'⟩ j' := Subtype.ext h
    have hv := congrArg (fun z => ((Fintype.equivFin (C b)) z).val) he
    simp only [pick, Equiv.apply_symm_apply] at hv
    have hi : i = i' := Fin.ext (by omega)
    have hj : j = j' := Fin.ext (by omega)
    subst i'
    subst j'
    rfl
  have hcard : Fintype.card X = ∑ b, Fintype.card (C b) := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
  have hI : Fintype.card I = ∑ b, Fintype.card (C b) / 3 := by
    simp [I]
  have hcount : Fintype.card X ≤ 3*Fintype.card I + 2*Fintype.card B := by
    rw [hcard, hI, Finset.mul_sum]
    calc
      ∑ b, Fintype.card (C b) ≤ ∑ b, (3*(Fintype.card (C b)/3)+2) := by
        apply Finset.sum_le_sum
        intro b _
        omega
      _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]
  refine ⟨Fintype.card I, fun i j => q ((Fintype.equivFin I).symm i) j, ?_, ?_, hcount⟩
  · intro p p' he
    have he' : ((Fintype.equivFin I).symm p.1, p.2) =
        ((Fintype.equivFin I).symm p'.1, p'.2) := hq he
    have hi := congrArg (fun z : I × Fin 3 => (Fintype.equivFin I) z.1) he'
    have hj := congrArg Prod.snd he'
    exact Prod.ext (by simpa using hi) hj
  · intro i j k
    exact (hf _ _).trans (hf _ _).symm

set_option maxHeartbeats 800000 in
lemma pack_interval (Y : Finset ℝ) (a : ℝ) (hm : 100 ≤ Y.card)
    (hY : ∀ y ∈ Y, a ≤ y ∧ y ≤ a+4*Y.card) :
    ∃ (n : ℕ) (x : Fin n → Fin 3 → ℝ),
      (∀ i j, x i j ∈ Y) ∧
      Function.Injective (fun p : Fin n × Fin 3 => x p.1 p.2) ∧
      (∀ i j k, |x i j-x i k| ≤ 100) ∧ Y.card ≤ 4*n := by
  classical
  let B := Y.card/25+1
  have htop : (4 : ℝ)*Y.card < 100*(B : ℝ) := by
    exact_mod_cast (show 4*Y.card < 100*B by dsimp [B]; omega)
  let bucket (y : Y) : Fin B := ⟨⌊((y:ℝ)-a)/100⌋₊, by
    apply (Nat.floor_lt (div_nonneg (sub_nonneg.mpr (hY y y.property).1)
      (by norm_num : (0:ℝ) ≤ 100))).2
    have hy := (hY y y.property).2
    apply (div_lt_iff₀ (by norm_num : (0:ℝ)<100)).2
    nlinarith⟩
  obtain ⟨n,q,hq,hb,hcount⟩ := group_fibers bucket
  refine ⟨n, fun i j => (q i j).val, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact (q i j).property
  · intro p p' he
    exact hq (Subtype.ext he)
  · intro i j k
    have he : ⌊((q i j : ℝ)-a)/100⌋₊ = ⌊((q i k : ℝ)-a)/100⌋₊ :=
      congrArg Fin.val (hb i j k)
    have hj0 := (hY (q i j) (q i j).property).1
    have hk0 := (hY (q i k) (q i k).property).1
    have hjlo := Nat.floor_le (div_nonneg (sub_nonneg.mpr hj0)
      (by norm_num : (0:ℝ) ≤ 100))
    have hklo := Nat.floor_le (div_nonneg (sub_nonneg.mpr hk0)
      (by norm_num : (0:ℝ) ≤ 100))
    have hjhi := Nat.lt_floor_add_one (((q i j : ℝ)-a)/100)
    have hkhi := Nat.lt_floor_add_one (((q i k : ℝ)-a)/100)
    rw [he] at hjlo hjhi
    apply abs_le.mpr
    constructor <;> linarith
  · simp only [Fintype.card_coe, Fintype.card_fin] at hcount
    dsimp [B] at hcount
    omega

set_option maxHeartbeats 800000 in
theorem packing :
    ∃ b : ℝ, 0 < b ∧ ∃ M : ℕ, ∀ (Y : Finset ℝ) (a : ℝ), M ≤ Y.card →
      (∀ y ∈ Y, a ≤ y ∧ y ≤ a+4*Y.card) →
      ∃ (n : ℕ) (x : Fin n → Fin 3 → ℝ),
        (∀ i j, x i j ∈ Y) ∧
        Function.Injective (fun p : Fin n × Fin 3 => x p.1 p.2) ∧
        (∀ i j k, |x i j-x i k| ≤ 100) ∧
        b*Y.card ≤ (∑ i, ((K (x i 0-x i 1))^2 +
          (K (x i 1-x i 2))^2 + (K (x i 0-x i 2))^2))/4 := by
  classical
  obtain ⟨η,hη,henergy⟩ := uniform_energy
  refine ⟨η/16, by positivity, 100, ?_⟩
  intro Y a hm hY
  obtain ⟨n,x,hx,hi,hd,hn⟩ := pack_interval Y a hm hY
  refine ⟨n,x,hx,hi,hd,?_⟩
  have hs : (n:ℝ)*η ≤ ∑ i, ((K (x i 0-x i 1))^2 +
      (K (x i 1-x i 2))^2 + (K (x i 0-x i 2))^2) := by
    calc
      (n:ℝ)*η = ∑ _i : Fin n, η := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => henergy _ _ _ (hd i 0 1) (hd i 1 2))
  have hn' : (Y.card:ℝ) ≤ 4*n := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_left hn' hη.le
  nlinarith

end OMA.ZetaPacking



set_option maxHeartbeats 800000 in
theorem OMA.solution : OMA.R_riemannZeta_distinct_prop_lt_R1.H2 :=
  OMA.ZetaPacking.packing
