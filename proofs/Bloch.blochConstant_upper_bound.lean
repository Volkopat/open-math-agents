import FormalConjectures.Wikipedia.Bloch
import Mathlib
/-! Ahlfors-Grunsky upper bound on Bloch's constant -/
open _root_.Complex hiding sqrt Gamma sin cos
open Real Metric Set Filter Topology Function
namespace BlochAG
noncomputable section
private lemma gP {x : ℝ} (h : 0 < x) : 0 < Gamma x := Gamma_pos_of_pos h
private abbrev T : ℂ →+* ℂ := starRingEnd ℂ
private abbrev Z := ℂ
private abbrev X := ℝ
private abbrev Y := sqrt
private abbrev W := normSq
lemma qa : (0 : X) ≤ 3 := by norm_num
lemma qb : (0 : X) < 3 := by norm_num
lemma qc : Y 3 ^ 2 = 3 := sq_sqrt qa
lemma qd : 0 < Y 3 := sqrt_pos.2 qb
lemma qe : 1 < Y 3 := by rw [lt_sqrt zero_le_one];norm_num
lemma qf : (17 / 10 : X) < Y 3 := by rw [lt_sqrt (by norm_num)];norm_num
def ω : Z := ⟨-1 / 2, Y 3 / 2⟩
lemma qg : ω.re = -1 / 2 := rfl
lemma qh : ω.im = Y 3 / 2 := rfl
lemma qi : ω ^ 2 + ω + 1 = 0 := by
 apply Complex.ext
 · simp only [ω,sq,add_re,mul_re,one_re,zero_re];nlinarith only [qc]
 · simp only [ω,sq,add_im,mul_im,one_im,add_zero,zero_im];ring
lemma qj : ω ^ 3 = 1 := by linear_combination (ω - 1) * qi
lemma qk : ‖ω‖ = 1 := by
 have hsq : ‖ω‖ ^ 2 = 1 := by
  rw [Complex.sq_norm, normSq_apply];simp only [ω];nlinarith only [qc]
 nlinarith only [hsq, norm_nonneg ω]
lemma ql : T ω = ω ^ 2 := by
 apply Complex.ext
 · simp only [ω,conj_re,sq,mul_re];nlinarith only [qc]
 · simp only [ω,conj_im,sq,mul_im];ring
lemma qm {z : Z} (hz : z ∈ ball (0 : Z) 1) : W z < 1 := by
 rw [mem_ball, dist_zero_right] at hz;rw [← Complex.sq_norm];nlinarith only [hz, norm_nonneg z]
def σ : X := 1 / Y (1 + Y 3)
lemma qn : 0 < σ := by dsimp [σ];positivity
lemma qo : σ ^ 2 = (Y 3 - 1) / 2 := by
 dsimp [σ]
 have hpos : (0 : X) < 1 + Y 3 := by positivity
 rw [div_pow, one_pow, sq_sqrt hpos.le];have h3 : Y 3 ^ 2 = 3 := qc;field_simp;nlinarith only [h3]
lemma qp : σ < 1 := by
 have h1 : σ ^ 2 < 1 := by
  rw [qo]
  nlinarith only [qc,
   qd]
 nlinarith only [h1, qn]
def tR : X := σ + 1 / σ
lemma qq : 0 < tR := by dsimp [tR];positivity [qn]
lemma qr : tR ^ 2 = (5 + 3 * Y 3) / 2 := by
 dsimp [tR]
 have h1 : (σ + 1 / σ) ^ 2 = σ ^ 2 + 1 / σ ^ 2 + 2 := by field_simp [qn.ne'];ring
 rw [h1, qo];have h3 : Y 3 ^ 2 = 3 := qc
 have hne : Y 3 - 1 ≠ 0 := by nlinarith only [h3, qd]
 field_simp [hne];nlinarith only [h3]
lemma qs : 1 < tR := by
 have h1 : 1 < tR ^ 2 := by rw [qr];nlinarith only [qd]
 nlinarith only [h1, qq]
def R2 : X := tR ^ 2 - 1
lemma qt : R2 = 3 * (1 + Y 3) / 2 := by dsimp [R2];rw [qr];ring
lemma qu : 0 < R2 := by rw [qt];positivity
def qv : X := Y R2
lemma qw : 0 < qv := sqrt_pos.2 qu
lemma qx : qv ^ 2 = R2 := sq_sqrt qu.le
def qy : Fin 3 → Z
 | 0 => -1
 | 1 => -ω ^ 2
 | 2 => -ω
lemma qz (i : Fin 3) : ‖qy i‖ = 1 := by
 fin_cases i
 · simp only [qy,norm_neg,norm_one]
 · simp only [qy,norm_neg,norm_pow,qk,one_pow]
 · simp only [qy,norm_neg,qk]
lemma qA (i : Fin 3) : W (qy i) = 1 := by rw [← Complex.sq_norm, qz];exact one_pow 2
lemma qB : (qy 0).re = -1 := by simp only [qy,neg_re,one_re]
lemma qC : (qy 0).im = 0 := by simp only [qy,neg_im,one_im,neg_zero]
lemma qD : (qy 1).re = 1 / 2 := by
 have h3 : Y 3 ^ 2 = 3 := qc;simp only [qy,ω,sq,neg_re,mul_re,neg_sub,one_div];nlinarith only [h3]
lemma qE : (qy 1).im = Y 3 / 2 := by simp only [qy,ω,sq,neg_im,mul_im,neg_add_rev];ring
lemma qF : (qy 2).re = 1 / 2 := by simp only [qy,ω,neg_re,one_div];ring
lemma qG : (qy 2).im = -Y 3 / 2 := by simp only [qy,ω,neg_im];ring
def qH (i : Fin 3) : Z := (tR : Z) * qy i
lemma qI (i : Fin 3) : W (qH i) = tR ^ 2 := by simp only [qH,normSq_mul,normSq_ofReal,qA,mul_one,sq]
lemma qJ (i : Fin 3) : ‖qH i‖ = tR := by simp only [qH,Complex.norm_mul,norm_real,Real.norm_of_nonneg qq.le,qz,mul_one]
lemma qK (i : Fin 3) : W (qH i) - R2 = 1 := by rw [qI];dsimp [R2];ring
def qL (i : Fin 3) (z : Z) : Z :=
 (qH i * T z - 1) / (T z - T (qH i))
lemma qM {i : Fin 3} {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  T z - T (qH i) ≠ 0 := by
 intro h
 have h1 : z = qH i := by
  have := congr_arg (T) (sub_eq_zero.1 h);simpa using this
 rw [mem_ball, dist_zero_right, h1, qJ] at hz;have ht1 : 1 < tR := qs;linarith
lemma qN {i : Fin 3} {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  qL i z ∈ ball (0 : Z) 1 := by
 have hden := qM (i := i) hz;have hz2 : W z < 1 := qm hz;rw [mem_ball, dist_zero_right]
 have hns : W (T z - T (qH i)) -
   W (qH i * T z - 1) =
   (tR ^ 2 - 1) * (1 - W z) := by
  have hc := qI i
  have key : ∀ a b : Z, W (T b - T a) -
    W (a * T b - 1) =
    (W a - 1) * (1 - W b) := by
   intro a b
   simp only [normSq_apply, sub_re, sub_im, mul_re,
    mul_im, conj_re, conj_im, one_re, one_im]
   ring
  rw [key (qH i) z, hc]
 have hpos : 0 < (tR ^ 2 - 1) * (1 - W z) :=
  mul_pos qu (sub_pos.2 hz2)
 have hlt : W (qH i * T z - 1) <
   W (T z - T (qH i)) := by linarith
 have hdiv : W (qL i z) < 1 := by
  dsimp [qL];rw [normSq_div];exact (div_lt_one (normSq_pos.2 hden)).2 hlt
 rw [← Complex.sq_norm] at hdiv;nlinarith only [hdiv, norm_nonneg (qL i z)]
lemma qO {i : Fin 3} {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  qL i (qL i z) = z := by
 have hden := qM (i := i) hz
 have hconj : T (qL i z) = (T (qH i) * z - 1) / (z - qH i) := by dsimp [qL];simp only [map_div₀,map_sub,map_mul,RingHomCompTriple.comp_apply,RingHom.id_apply,map_one]
 have hzc : z - qH i ≠ 0 := by intro h;apply hden;have := congr_arg (T) h;simpa using this
 have hne : T (qL i z) - T (qH i) ≠ 0 :=
  qM (i := i) (qN (i := i) hz)
 rw [hconj] at hne
 have hlhs : qL i (qL i z) = (qH i * T (qL i z) - 1) /
   (T (qL i z) - T (qH i)) := rfl
 rw [hlhs, hconj, div_eq_iff hne];field_simp [hzc]
 have hcs : qH i * T (qH i) = (tR ^ 2 : Z) := by
  have := qI i;rw [← ofReal_inj] at this;simpa [mul_conj] using this
 ring
lemma qP {i : Fin 3} {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  1 - W (qL i z) =
   R2 * (1 - W z) / W (T z - T (qH i)) := by
 have hden := qM (i := i) hz;dsimp [qL];rw [normSq_div, one_sub_div (normSq_pos.2 hden).ne'];congr 1;have hc := qI i
 have key : ∀ a b : Z, W (T b - T a) -
   W (a * T b - 1) =
   (W a - 1) * (1 - W b) := by
  intro a b
  simp only [normSq_apply, sub_re, sub_im, mul_re,
   mul_im, conj_re, conj_im, one_re, one_im]
  ring
 rw [key (qH i) z, hc, R2]
lemma qQ {i : Fin 3} {z w : Z}
  (hz : z ∈ ball (0 : Z) 1) (hw : w ∈ ball (0 : Z) 1) :
  W (qL i z - qL i w) =
   R2 ^ 2 * W (z - w) /
    (W (T z - T (qH i)) *
    W (T w - T (qH i))) := by
 have hdz := qM (i := i) hz;have hdw := qM (i := i) hw
 have hdiff : qL i z - qL i w =
   ((tR ^ 2 - 1 : Z) * (T w - T z)) /
    ((T z - T (qH i)) *
    (T w - T (qH i))) := by
  dsimp [qL];rw [div_sub_div _ _ hdz hdw];congr 1
  have hcs : qH i * T (qH i) = (tR ^ 2 : Z) := by
   have := qI i;rw [← ofReal_inj] at this;simpa [mul_conj] using this
  linear_combination (T w - T z) * hcs
 rw [hdiff, normSq_div, normSq_mul, normSq_mul]
 have hR : W (tR ^ 2 - 1 : Z) = R2 ^ 2 := by
  have : (tR ^ 2 - 1 : Z) = (R2 : Z) := by dsimp [R2];push_cast;rfl
  rw [this, normSq_ofReal, sq]
 have hzw : W (T w - T z) = W (z - w) := by
  rw [← map_sub, normSq_conj];simp only [normSq_apply,sub_re,sub_im];ring
 rw [hR, hzw]
def qR (z w : Z) : X :=
 W (z - w) / ((1 - W z) * (1 - W w))
lemma qS {i : Fin 3} {z w : Z}
  (hz : z ∈ ball (0 : Z) 1) (hw : w ∈ ball (0 : Z) 1) :
  qR (qL i z) (qL i w) = qR z w := by
 dsimp [qR];rw [qQ hz hw, qP hz, qP hw];have hdz := (normSq_pos.2 (qM (i := i) hz)).ne';have hdw := (normSq_pos.2 (qM (i := i) hw)).ne';have hz1 : 1 - W z ≠ 0 := (sub_pos.2 (qm hz)).ne';have hw1 : 1 - W w ≠ 0 := (sub_pos.2 (qm hw)).ne';have hR := qu.ne';field_simp [hdz, hdw, hz1, hw1, hR]
lemma qT {i : Fin 3} {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  W z ≤ W (qL i z) ↔ R2 ≤ W (z - qH i) := by
 have h1 : W z ≤ W (qL i z) ↔
   1 - W (qL i z) ≤ 1 - W z := by constructor <;> intro h <;> linarith
 rw [h1, qP hz]
 have hden_pos : 0 < W (T z - T (qH i)) :=
  normSq_pos.2 (qM hz)
 have hz1 : 0 < 1 - W z := sub_pos.2 (qm hz);rw [div_le_iff₀ hden_pos]
 have hconj : W (T z - T (qH i)) =
   W (z - qH i) := by
  rw [← map_sub, normSq_conj]
 rw [hconj]
 constructor <;> intro h <;> nlinarith only [h, hden_pos, hz1]
def T0 : Set Z :=
 { z ∈ ball (0 : Z) 1 | ∀ i : Fin 3, R2 ≤ W (z - qH i) }
def qU : Set Z :=
 { z ∈ ball (0 : Z) 1 | ∀ i : Fin 3, R2 < W (z - qH i) }
lemma qV : (0 : Z) ∈ qU := by
 refine ⟨mem_ball_self one_pos, fun i => ?_⟩
 simp only [R2,zero_sub,normSq_neg,qI,sub_lt_self_iff,zero_lt_one]
lemma qW : qU ⊆ T0 := fun _ ⟨h1, h2⟩ => ⟨h1, fun i => (h2 i).le⟩
def qX : Fin 3 → Z → Z
 | 0, w => -1 - T w
 | 1, w => -ω ^ 2 - ω * T w
 | 2, w => -ω - ω ^ 2 * T w
lemma qY : T (ω ^ 2) = ω := by rw [map_pow, ql];linear_combination ω * (ω - 1) * qi
lemma qZ : ω ^ 4 = ω := by linear_combination ω * qj
lemma q0 (i : Fin 3) (w : Z) : qX i (qX i w) = w := by
 have hc : T ω = ω ^ 2 := ql;have hc2 : T (ω ^ 2) = ω := qY;have hω4 : ω ^ 4 = ω := qZ
 rcases i with ⟨i, hi⟩
 interval_cases i
 · change qX 0 (qX 0 w) = w;simp only [qX,map_sub,map_neg,map_one,RingHomCompTriple.comp_apply,RingHom.id_apply,sub_sub_cancel]
 ·
  change qX 1 (qX 1 w) = w;simp only [qX,map_sub,map_neg,hc2,map_mul,hc,RingHomCompTriple.comp_apply,RingHom.id_apply];ring_nf;rw [qj];ring
 ·
  change qX 2 (qX 2 w) = w;simp only [qX,map_sub,map_neg,hc,map_mul,hc2,RingHomCompTriple.comp_apply,RingHom.id_apply];ring_nf;rw [qj, hω4];ring
lemma q1 {A B : Z} (h : (A = 1 ∧ B = 0) ∨ A ^ 2 + A + 1 = 0) (w : Z) :
  (fun z => A * z + B)^[3] w = w := by
 simp only [Function.iterate_succ,Function.iterate_zero,Function.comp_apply,id_eq]
 rcases h with ⟨rfl, rfl⟩ | hA
 · ring
 ·
  have hA3 : A ^ 3 = 1 := by linear_combination (A - 1) * hA
  linear_combination w * hA3 + B * hA
lemma q2 (i j : Fin 3) (w : Z) :
  (qX i ∘ qX j)^[3] w = w := by
 have hc : T ω = ω ^ 2 := ql;have hc2 : T (ω ^ 2) = ω := qY
 have hω2 : ω ^ 2 = -ω - 1 := by linear_combination qi
 have hω4 : ω ^ 4 = ω := qZ
 have hω5 : ω ^ 5 = ω ^ 2 := by linear_combination ω ^ 2 * qj
 have hω6 : ω ^ 6 = 1 := by linear_combination (ω ^ 3 + 1) * qj
 have hω2_sq : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by linear_combination (ω ^ 2 - ω + 1) * qi
 rcases i with ⟨i, hi⟩;rcases j with ⟨j, hj⟩
 interval_cases i <;> interval_cases j
 ·
  change (qX 0 ∘ qX 0)^[3] w = w
  have heq : (qX 0 ∘ qX 0) = fun z => 1 * z + 0 := by ext z;simp only [Fin.isValue,comp_apply,qX,map_sub,map_neg,map_one,RingHomCompTriple.comp_apply,RingHom.id_apply,sub_sub_cancel,one_mul,add_zero]
  rw [heq];exact q1 (Or.inl ⟨rfl, rfl⟩) w
 ·
  change (qX 0 ∘ qX 1)^[3] w = w
  have heq : (qX 0 ∘ qX 1) = fun z => ω ^ 2 * z + (ω - 1) := by ext z;simp only [Fin.isValue,comp_apply,qX,map_sub,map_neg,hc2,map_mul,hc,RingHomCompTriple.comp_apply,RingHom.id_apply];ring
  rw [heq];exact q1 (Or.inr hω2_sq) w
 ·
  change (qX 0 ∘ qX 2)^[3] w = w
  have heq : (qX 0 ∘ qX 2) = fun z => ω * z + (ω ^ 2 - 1) := by ext z;simp only [Fin.isValue,comp_apply,qX,map_sub,map_neg,hc,map_mul,hc2,RingHomCompTriple.comp_apply,RingHom.id_apply];ring
  rw [heq];exact q1 (Or.inr qi) w
 ·
  change (qX 1 ∘ qX 0)^[3] w = w
  have heq : (qX 1 ∘ qX 0) = fun z => ω * z + (ω - ω ^ 2) := by ext z;simp only [Fin.isValue,comp_apply,qX,map_sub,map_neg,map_one,RingHomCompTriple.comp_apply,RingHom.id_apply];ring
  rw [heq];exact q1 (Or.inr qi) w
 ·
  change (qX 1 ∘ qX 1)^[3] w = w
  have heq : (qX 1 ∘ qX 1) = fun z => 1 * z + 0 := by ext z;simp only [Fin.isValue,comp_apply,qX,map_sub,map_neg,map_pow,hc,map_mul,RingHomCompTriple.comp_apply,RingHom.id_apply,one_mul,add_zero];ring_nf;rw [hω5, qj];ring
  rw [heq];exact q1 (Or.inl ⟨rfl, rfl⟩) w
 ·
  change (qX 1 ∘ qX 2)^[3] w = w
  have heq : (qX 1 ∘ qX 2) = fun z => ω ^ 2 * z + (1 - ω ^ 2) := by ext z;simp only [Fin.isValue,comp_apply,qX,map_sub,map_neg,hc,map_mul,map_pow,RingHomCompTriple.comp_apply,RingHom.id_apply];ring_nf;rw [hω5, qj];ring
  rw [heq];exact q1 (Or.inr hω2_sq) w
 ·
  change (qX 2 ∘ qX 0)^[3] w = w
  have heq : (qX 2 ∘ qX 0) = fun z => ω ^ 2 * z + (ω ^ 2 - ω) := by ext z;simp only [Fin.isValue,comp_apply,qX,map_sub,map_neg,map_one,RingHomCompTriple.comp_apply,RingHom.id_apply];ring
  rw [heq];exact q1 (Or.inr hω2_sq) w
 ·
  change (qX 2 ∘ qX 1)^[3] w = w
  have heq : (qX 2 ∘ qX 1) = fun z => ω * z + (1 - ω) := by ext z;simp only [Fin.isValue,comp_apply,qX,map_sub,map_neg,map_pow,hc,map_mul,RingHomCompTriple.comp_apply,RingHom.id_apply];ring_nf;rw [hω4, hω6];ring
  rw [heq];exact q1 (Or.inr qi) w
 ·
  change (qX 2 ∘ qX 2)^[3] w = w
  have heq : (qX 2 ∘ qX 2) = fun z => 1 * z + 0 := by ext z;simp only [Fin.isValue,comp_apply,qX,map_sub,map_neg,hc,map_mul,map_pow,RingHomCompTriple.comp_apply,RingHom.id_apply,one_mul,add_zero];ring_nf;rw [hω4, hω6];ring
  rw [heq];exact q1 (Or.inl ⟨rfl, rfl⟩) w
lemma q3 : qy 0 + qy 1 + qy 2 = 0 := by simp only [qy];linear_combination -qi
lemma q4 : qH 0 + qH 1 + qH 2 = 0 := by simp only [qH,← mul_add,q3,mul_zero]
def q5 (z : Z) (i : Fin 3) : X :=
 -3 * (W (z - qH i) - R2) / (R2 * (1 - W z))
def Φ (z : Z) (i : Fin 3) : X :=
 (4 - 2 * Y 3) * q5 z i + ((Y 3 - 3) / 2) * (q5 z 0 + q5 z 1 + q5 z 2)
lemma q6 (i : Fin 3) : q5 0 i = 1 - Y 3 := by
 dsimp [q5]
 have h1 : W (0 - qH i) - R2 = 1 := by simpa [zero_sub, normSq_neg] using qK i
 rw [h1, qt];have h3 : Y 3 ^ 2 = 3 := qc
 have hpos : (0 : X) < 1 + Y 3 := by positivity
 simp only [normSq_zero,sub_zero,mul_one];field_simp [hpos.ne'];nlinarith only [h3]
lemma q7 (i : Fin 3) : Φ 0 i = 1 := by
 dsimp [Φ];simp only [q6];have h3 : Y 3 ^ 2 = 3 := qc;nlinarith only [h3]
lemma q8 {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  q5 z 0 + q5 z 1 + q5 z 2 =
   -9 * (1 + W z) / (R2 * (1 - W z)) := by
 dsimp [q5];have hz1 : 1 - W z ≠ 0 := (sub_pos.2 (qm hz)).ne';have hden : R2 * (1 - W z) ≠ 0 := mul_ne_zero qu.ne' hz1
 have hsum : W (z - qH 0) + W (z - qH 1) +
   W (z - qH 2) = 3 * W z + 3 * tR ^ 2 := by
  have hns : ∀ i, W (z - qH i) =
    W z + W (qH i) - 2 * (z * T (qH i)).re := by
   intro i
   simp only [normSq_apply, sub_re, sub_im, mul_re,
    conj_re, conj_im]
   ring
  rw [hns 0, hns 1, hns 2, qI 0, qI 1, qI 2]
  have hre : (z * T (qH 0)).re + (z * T (qH 1)).re +
    (z * T (qH 2)).re = 0 := by
   rw [← add_re, ← add_re, ← mul_add, ← mul_add, ← map_add, ← map_add,
    q4, map_zero, mul_zero, zero_re]
  linarith
 rw [← add_div, ← add_div];congr 1;dsimp [R2];linarith [hsum]
lemma q9 {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  (Φ z 0 + Φ z 1 + Φ z 2) / 3 = (1 + W z) / (1 - W z) := by
 have hsum := q8 hz;have hz1 : 1 - W z ≠ 0 := (sub_pos.2 (qm hz)).ne'
 have hpos : (0 : X) < 1 + Y 3 := by positivity
 have hfac : (Φ z 0 + Φ z 1 + Φ z 2) / 3 =
   (-(1 + Y 3) / 2) * (q5 z 0 + q5 z 1 + q5 z 2) / 3 := by
  dsimp [Φ];ring
 rw [hfac, hsum, qt];field_simp [hpos.ne', hz1];ring
lemma pa {z : Z} (i : Fin 3) :
  q5 z i = Φ z i - (Y 3 / 2) * (Φ z 0 + Φ z 1 + Φ z 2 - Φ z i) := by
 have h3 : Y 3 ^ 2 = 3 := qc
 fin_cases i <;> · simp only [Fin.isValue,Φ];ring_nf;rw [h3];ring
lemma pb {i : Fin 3} {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  q5 (qL i z) i = -q5 z i := by
 dsimp [q5];have hden := qM (i := i) hz;have h1 := qP (i := i) hz
 have hconj : W (T z - T (qH i)) =
   W (z - qH i) := by rw [← map_sub, normSq_conj]
 rw [hconj] at h1
 have hr_sub : qL i z - qH i =
   (qH i * T z - 1 - qH i * (T z - T (qH i))) /
    (T z - T (qH i)) := by
  dsimp [qL];field_simp [hden]
 have hr_num : qH i * T z - 1 - qH i * (T z - T (qH i)) =
   (R2 : Z) := by
  have hcs : qH i * T (qH i) = (tR ^ 2 : Z) := by
   have := qI i;rw [← ofReal_inj] at this;simpa [mul_conj] using this
  dsimp [R2];push_cast;linear_combination hcs
 rw [hr_num] at hr_sub
 have hr_ns : W (qL i z - qH i) - R2 =
   R2 * (R2 - W (z - qH i)) / W (z - qH i) := by
  have hnz2 : W (z - qH i) ≠ 0 := by rw [← hconj];exact (normSq_pos.2 hden).ne'
  rw [hr_sub, normSq_div, normSq_ofReal, hconj, ← sq];field_simp [hnz2]
 rw [hr_ns, h1];have hnz1 : 1 - W z ≠ 0 := (sub_pos.2 (qm hz)).ne'
 have hnz2 : W (z - qH i) ≠ 0 := by rw [← hconj];exact (normSq_pos.2 hden).ne'
 field_simp [qu.ne', hnz1, hnz2];ring
lemma pc {i j : Fin 3} (hij : i ≠ j) {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  q5 (qL i z) j = q5 z j + Y 3 * q5 z i := by
 dsimp [q5];have hden := qM (i := i) hz;have h1 := qP (i := i) hz
 have hconj : W (T z - T (qH i)) =
   W (z - qH i) := by rw [← map_sub, normSq_conj]
 rw [hconj] at h1
 have hip : (qH i * T (qH j)).re = -(tR ^ 2) / 2 := by
  have h3 : Y 3 ^ 2 = 3 := qc
  have hre_mul : ∀ a b : Z, ((tR : Z) * a * T ((tR : Z) * b)).re =
    tR ^ 2 * (a.re * b.re + a.im * b.im) := by
   intro a b
   simp only [map_mul, conj_ofReal, mul_re, mul_im, ofReal_re,
    ofReal_im, conj_re, conj_im, sub_zero, zero_mul]
   ring
  simp only [qH,hre_mul]
  rcases i with ⟨i, hi⟩;rcases j with ⟨j, hj⟩
  interval_cases i <;> interval_cases j <;> try contradiction
  ·
   change tR ^ 2 * ((qy 0).re * (qy 1).re + (qy 0).im * (qy 1).im) = -tR ^ 2 / 2;rw [qB, qC, qD, qE];ring
  ·
   change tR ^ 2 * ((qy 0).re * (qy 2).re + (qy 0).im * (qy 2).im) = -tR ^ 2 / 2;rw [qB, qC, qF, qG];ring
  ·
   change tR ^ 2 * ((qy 1).re * (qy 0).re + (qy 1).im * (qy 0).im) = -tR ^ 2 / 2;rw [qD, qE, qB, qC];ring
  ·
   change tR ^ 2 * ((qy 1).re * (qy 2).re + (qy 1).im * (qy 2).im) = -tR ^ 2 / 2;rw [qD, qE, qF, qG];nlinarith only [h3]
  ·
   change tR ^ 2 * ((qy 2).re * (qy 0).re + (qy 2).im * (qy 0).im) = -tR ^ 2 / 2;rw [qF, qG, qB, qC];ring
  ·
   change tR ^ 2 * ((qy 2).re * (qy 1).re + (qy 2).im * (qy 1).im) = -tR ^ 2 / 2;rw [qF, qG, qD, qE];nlinarith only [h3]
 have hc_dot : W (qH i - qH j) = 3 * tR ^ 2 := by
  have hns : W (qH i - qH j) =
    W (qH i) + W (qH j) -
     2 * (qH i * T (qH j)).re := by
   simp only [normSq_apply, sub_re, sub_im, mul_re,
    conj_re, conj_im]
   ring
  rw [hns, qI i, qI j, hip];ring
 have hr_sub : qL i z - qH i = (R2 : Z) / (T z - T (qH i)) := by
  dsimp [qL];field_simp [hden]
  have hcs : qH i * T (qH i) = (tR ^ 2 : Z) := by
   have := qI i;rw [← ofReal_inj] at this;simpa [mul_conj] using this
  dsimp [R2];push_cast;linear_combination hcs
 have hr_split : qL i z - qH j =
   (R2 : Z) / (T z - T (qH i)) + (qH i - qH j) := by
  linear_combination hr_sub
 have hns_j : W (z - qH j) =
   W (z - qH i) + 2 * ((qH i - qH j) * T (z - qH i)).re +
    W (qH i - qH j) := by
  have : z - qH j = (z - qH i) + (qH i - qH j) := by ring
  rw [this]
  simp only [normSq_apply, add_re, add_im, mul_re,
   conj_re, conj_im]
  ring
 have hns_rj : W (qL i z - qH j) * W (z - qH i) =
   R2 ^ 2 + 2 * R2 * ((qH i - qH j) * T (z - qH i)).re +
    W (qH i - qH j) * W (z - qH i) := by
  have hmul : (qL i z - qH j) * (T z - T (qH i)) =
    (R2 : Z) + (qH i - qH j) * (T z - T (qH i)) := by
   rw [hr_split, add_mul, div_mul_cancel₀ _ hden]
  have hns := congr_arg W hmul;rw [normSq_mul, hconj] at hns;rw [hns]
  simp only [normSq_apply, add_re, add_im, ofReal_re,
   ofReal_im, mul_re, mul_im, conj_re, conj_im,
   sub_re, sub_im]
  ring
 have h3R : 3 * tR ^ 2 - 2 * R2 = Y 3 * R2 := by rw [qr, qt];have h3 : Y 3 ^ 2 = 3 := qc;nlinarith only [h3]
 have hconst : R2 ^ 2 - 3 * R2 * tR ^ 2 = -(1 + Y 3) * R2 ^ 2 := by rw [qr, qt];have h3 : Y 3 ^ 2 = 3 := qc;nlinarith only [h3]
 have hkey : (W (qL i z - qH j) - R2) * W (z - qH i) =
   R2 * (W (z - qH j) - R2) +
    Y 3 * R2 * (W (z - qH i) - R2) := by
  have h2re : 2 * ((qH i - qH j) * T (z - qH i)).re =
    W (z - qH j) - W (z - qH i) - 3 * tR ^ 2 := by
   linarith [hns_j, hc_dot]
  calc (W (qL i z - qH j) - R2) * W (z - qH i)
      = W (qL i z - qH j) * W (z - qH i) -
          R2 * W (z - qH i) := by ring
    _ = R2 ^ 2 + R2 * (2 * ((qH i - qH j) * T (z - qH i)).re) +
          (3 * tR ^ 2 - R2) * W (z - qH i) := by rw [hns_rj, hc_dot];ring
    _ = R2 ^ 2 + R2 * (W (z - qH j) - W (z - qH i) - 3 * tR ^ 2) +
          (3 * tR ^ 2 - R2) * W (z - qH i) := by rw [h2re]
    _ = R2 * (W (z - qH j) - R2) +
          (3 * tR ^ 2 - 2 * R2) * (W (z - qH i) - R2) +
          (R2 ^ 2 - 3 * R2 * tR ^ 2 + (3 * tR ^ 2 - 2 * R2) * R2 + R2 ^ 2) := by ring
    _ = R2 * (W (z - qH j) - R2) +
          Y 3 * R2 * (W (z - qH i) - R2) := by
        rw [h3R, hconst];ring
 rw [h1];have hnz1 : 1 - W z ≠ 0 := (sub_pos.2 (qm hz)).ne'
 have hnz2 : W (z - qH i) ≠ 0 := by rw [← hconj];exact (normSq_pos.2 hden).ne'
 have hkey_div : (W (qL i z - qH j) - R2) =
   (R2 * (W (z - qH j) - R2) +
    Y 3 * R2 * (W (z - qH i) - R2)) / W (z - qH i) :=
  (eq_div_iff hnz2).mpr hkey
 rw [hkey_div];field_simp [qu.ne', hnz1, hnz2];ring
lemma pd (i : Fin 3) {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  q5 (qL i z) 0 + q5 (qL i z) 1 + q5 (qL i z) 2 =
   (q5 z 0 + q5 z 1 + q5 z 2) + (2 * Y 3 - 2) * q5 z i := by
 have hsame : ∀ k : Fin 3, q5 (qL k z) k = -q5 z k := fun k => pb hz
 have hother : ∀ k j : Fin 3, k ≠ j → q5 (qL k z) j = q5 z j + Y 3 * q5 z k :=
  fun k j hkj => pc hkj hz
 rcases i with ⟨i, hi⟩
 interval_cases i
 ·
  change q5 (qL 0 z) 0 + q5 (qL 0 z) 1 + q5 (qL 0 z) 2 =
   q5 z 0 + q5 z 1 + q5 z 2 + (2 * Y 3 - 2) * q5 z 0
  rw [hsame 0, hother 0 1 (by decide), hother 0 2 (by decide)];ring
 ·
  change q5 (qL 1 z) 0 + q5 (qL 1 z) 1 + q5 (qL 1 z) 2 =
   q5 z 0 + q5 z 1 + q5 z 2 + (2 * Y 3 - 2) * q5 z 1
  rw [hother 1 0 (by decide), hsame 1, hother 1 2 (by decide)];ring
 ·
  change q5 (qL 2 z) 0 + q5 (qL 2 z) 1 + q5 (qL 2 z) 2 =
   q5 z 0 + q5 z 1 + q5 z 2 + (2 * Y 3 - 2) * q5 z 2
  rw [hother 2 0 (by decide), hother 2 1 (by decide), hsame 2];ring
lemma pe {i : Fin 3} {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  Φ (qL i z) i = -Φ z i + Y 3 * (Φ z 0 + Φ z 1 + Φ z 2 - Φ z i) := by
 have h3 : Y 3 ^ 2 = 3 := qc;have hsame := pb (i := i) hz;have hsum := pd i hz
 have h2 : Φ z 0 + Φ z 1 + Φ z 2 = (-(1 + Y 3) / 2) * (q5 z 0 + q5 z 1 + q5 z 2) := by dsimp [Φ];ring
 rw [h2];dsimp [Φ];rw [hsame, hsum];ring_nf;rw [h3];ring
lemma pf {i j : Fin 3} (hij : i ≠ j) {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  Φ (qL i z) j = Φ z j := by
 have h3 : Y 3 ^ 2 = 3 := qc;have hother := pc hij hz;have hsum := pd i hz;dsimp [Φ];rw [hother, hsum];ring_nf;rw [h3];ring
end
structure Z3 where
 a : ℤ
 b : ℤ
 deriving DecidableEq, Repr
namespace Z3
def zero : Z3 := ⟨0, 0⟩
def one : Z3 := ⟨1, 0⟩
def pg : Z3 := ⟨0, 1⟩
def ph (n : ℤ) : Z3 := ⟨n, 0⟩
def add (x y : Z3) : Z3 := ⟨x.a + y.a, x.b + y.b⟩
def sub (x y : Z3) : Z3 := ⟨x.a - y.a, x.b - y.b⟩
def neg (x : Z3) : Z3 := ⟨-x.a, -x.b⟩
def mul (x y : Z3) : Z3 := ⟨x.a * y.a + 3 * x.b * y.b, x.a * y.b + x.b * y.a⟩
def smul (k : ℤ) (x : Z3) : Z3 := ⟨k * x.a, k * x.b⟩
def conj (x : Z3) : Z3 := ⟨x.a, -x.b⟩
noncomputable def t0 (x : Z3) : X := (x.a : X) + (x.b : X) * Y 3
noncomputable def pj (x : Z3) : X := (x.a : X) - (x.b : X) * Y 3
lemma pk (n : ℤ) : (ph n).t0 = (n : X) := by simp only [t0,ph,Int.cast_zero,zero_mul,add_zero]
lemma pl : zero.t0 = 0 := by simp only [t0,zero,Int.cast_zero,zero_mul,add_zero]
lemma pm : one.t0 = 1 := by simp only [t0,one,Int.cast_one,Int.cast_zero,zero_mul,add_zero]
lemma pn : pg.t0 = Y 3 := by simp only [t0,pg,Int.cast_zero,Int.cast_one,one_mul,zero_add]
lemma po (x y : Z3) : (add x y).t0 = x.t0 + y.t0 := by simp only [t0,add,Int.cast_add];ring
lemma pp (x y : Z3) : (sub x y).t0 = x.t0 - y.t0 := by simp only [t0,sub,Int.cast_sub];ring
lemma pq (x : Z3) : (neg x).t0 = -x.t0 := by simp only [t0,neg,Int.cast_neg,neg_mul,neg_add_rev];ring
lemma pr (x y : Z3) : (mul x y).t0 = x.t0 * y.t0 := by
 have h3 : Y 3 ^ 2 = 3 := qc;simp only [mul,t0,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
 rw [show (3 : X) * (x.b : X) * (y.b : X) = Y 3 ^ 2 * x.b * y.b by rw [h3]];ring
lemma ps (k : ℤ) (x : Z3) : (smul k x).t0 = (k : X) * x.t0 := by simp only [t0,smul,Int.cast_mul];ring
lemma pt (x : Z3) : x.pj = x.conj.t0 := by simp only [pj,t0,conj,Int.cast_neg,neg_mul];ring
lemma pu : one.pj = 1 := by simp only [pj,one,Int.cast_one,Int.cast_zero,zero_mul,sub_zero]
lemma pv : pg.pj = -Y 3 := by simp only [pj,pg,Int.cast_zero,Int.cast_one,one_mul,zero_sub]
lemma pw (x y : Z3) : (add x y).pj = x.pj + y.pj := by simp only [pj,add,Int.cast_add];ring
lemma px (x y : Z3) : (sub x y).pj = x.pj - y.pj := by simp only [pj,sub,Int.cast_sub];ring
lemma py (k : ℤ) (x : Z3) : (smul k x).pj = (k : X) * x.pj := by simp only [pj,smul,Int.cast_mul];ring
lemma pz (x y : Z3) : (mul x y).pj = x.pj * y.pj := by
 have h3 : Y 3 ^ 2 = 3 := qc;simp only [mul,pj,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
 rw [show (3 : X) * (x.b : X) * (y.b : X) = Y 3 ^ 2 * x.b * y.b by rw [h3]];ring
def n0 (x : Z3) : Bool :=
 if 0 ≤ x.a then
  if 0 ≤ x.b then true else decide (3 * x.b * x.b ≤ x.a * x.a)
 else
  if 0 ≤ x.b then decide (x.a * x.a ≤ 3 * x.b * x.b) else false
def pB (x : Z3) : Bool := (neg x).n0
def l0 (x : Z3) : Bool := !(x.n0)
lemma pD (x : Z3) : x.n0 = true ↔ 0 ≤ x.t0 := by
 have h3 : Y 3 ^ 2 = 3 := qc;have h3p : 0 < Y 3 := qd;dsimp [n0, t0]
 split_ifs with ha hb hb2
 ·
  have ha' : (0 : X) ≤ x.a := by exact_mod_cast ha
  have hb' : (0 : X) ≤ x.b := by exact_mod_cast hb
  constructor <;> intro _
  · positivity
  · rfl
 ·
  simp only [decide_eq_true_eq]
  have ha' : (0 : X) ≤ x.a := by exact_mod_cast ha
  have hb' : (x.b : X) < 0 := by exact_mod_cast (lt_of_not_ge hb)
  have hsq : 3 * (x.b : X) * (x.b : X) ≤ (x.a : X) * (x.a : X) ↔
    (-(x.b : X) * Y 3) ≤ (x.a : X) := by
   have h1 : (-(x.b : X) * Y 3) ^ 2 = 3 * (x.b : X) * (x.b : X) := by nlinarith only [h3]
   have h2 : (0 : X) ≤ -(x.b : X) * Y 3 := by nlinarith only [hb', h3p]
   constructor <;> intro h <;> nlinarith only [h, h1, h2, ha']
  have hcast : 3 * x.b * x.b ≤ x.a * x.a ↔ 3 * (x.b : X) * (x.b : X) ≤ (x.a : X) * (x.a : X) := by exact_mod_cast Iff.rfl
  rw [hcast, hsq];constructor <;> intro h <;> linarith
 ·
  simp only [decide_eq_true_eq]
  have ha' : (x.a : X) < 0 := by exact_mod_cast (lt_of_not_ge ha)
  have hb' : (0 : X) ≤ x.b := by exact_mod_cast hb2
  have hsq : (x.a : X) * (x.a : X) ≤ 3 * (x.b : X) * (x.b : X) ↔
    -(x.a : X) ≤ (x.b : X) * Y 3 := by
   have h1 : ((x.b : X) * Y 3) ^ 2 = 3 * (x.b : X) * (x.b : X) := by nlinarith only [h3]
   have hxb0 : 0 ≤ (x.b : X) * Y 3 := mul_nonneg hb' h3p.le
   constructor <;> intro h <;> nlinarith only [h, h1, hxb0, ha']
  have hcast : x.a * x.a ≤ 3 * x.b * x.b ↔ (x.a : X) * (x.a : X) ≤ 3 * (x.b : X) * (x.b : X) := by exact_mod_cast Iff.rfl
  rw [hcast, hsq];constructor <;> intro h <;> linarith
 ·
  have ha' : (x.a : X) < 0 := by exact_mod_cast (lt_of_not_ge ha)
  have hb' : (x.b : X) < 0 := by exact_mod_cast (lt_of_not_ge hb2)
  constructor
  · intro h;simp only at h
  · intro h;exfalso;nlinarith only [h, ha', hb', h3p]
lemma pE (x : Z3) : x.pB = true ↔ x.t0 ≤ 0 := by rw [pB, pD, pq];constructor <;> intro h <;> linarith
lemma pF (x : Z3) : x.l0 = true ↔ x.t0 < 0 := by rw [l0, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, pD, not_le]
end Z3
structure V3 where
 v0 : Z3
 v1 : Z3
 v2 : Z3
 deriving DecidableEq, Repr
namespace V3
def get (v : V3) : Fin 3 → Z3
 | 0 => v.v0
 | 1 => v.v1
 | 2 => v.v2
def pG : V3 := ⟨Z3.one, Z3.one, Z3.one⟩
def sum (v : V3) : Z3 := Z3.add v.v0 (Z3.add v.v1 v.v2)
def pH (i : Fin 3) (v : V3) : V3 :=
 match i with
 | 0 => ⟨Z3.add (Z3.neg v.v0) (Z3.mul Z3.pg (Z3.add v.v1 v.v2)), v.v1, v.v2⟩
 | 1 => ⟨v.v0, Z3.add (Z3.neg v.v1) (Z3.mul Z3.pg (Z3.add v.v0 v.v2)), v.v2⟩
 | 2 => ⟨v.v0, v.v1, Z3.add (Z3.neg v.v2) (Z3.mul Z3.pg (Z3.add v.v0 v.v1))⟩
def qform (v : V3) : Z3 :=
 let ssq := Z3.add (Z3.mul v.v0 v.v0)
  (Z3.add (Z3.mul v.v1 v.v1) (Z3.mul v.v2 v.v2))
 let spair := Z3.add (Z3.mul v.v0 v.v1)
  (Z3.add (Z3.mul v.v1 v.v2) (Z3.mul v.v2 v.v0))
 Z3.sub ssq (Z3.mul Z3.pg spair)
def pI (v u : V3) : Z3 :=
 let d := Z3.add (Z3.mul v.v0 u.v0)
  (Z3.add (Z3.mul v.v1 u.v1) (Z3.mul v.v2 u.v2))
 let c := Z3.add
  (Z3.mul v.v0 (Z3.add u.v1 u.v2))
  (Z3.add (Z3.mul v.v1 (Z3.add u.v0 u.v2))
   (Z3.mul v.v2 (Z3.add u.v0 u.v1)))
 Z3.sub (Z3.smul 2 d) (Z3.mul Z3.pg c)
lemma pJ : qform pG = ⟨3, -3⟩ := by decide
lemma pK (i : Fin 3) (v : V3) : qform (pH i v) = qform v := by
 have hsq : ∀ x y : Z3,
   Z3.mul (Z3.add (Z3.neg x) (Z3.mul Z3.pg y))
    (Z3.add (Z3.neg x) (Z3.mul Z3.pg y)) =
   Z3.add (Z3.sub (Z3.mul x x)
    (Z3.smul 2 (Z3.mul Z3.pg (Z3.mul x y))))
    (Z3.smul 3 (Z3.mul y y)) := by
  intro ⟨a1, b1⟩ ⟨a2, b2⟩;simp only [Z3.mul,Z3.add,Z3.neg,Z3.pg,zero_mul,mul_one,zero_add,one_mul,Z3.sub,Z3.smul,Z3.mk.injEq]
  constructor <;> ring
 rcases v with ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩
 fin_cases i <;> ·
  simp only [qform,pH,Z3.add,Z3.sub,Z3.neg,Z3.mul,Z3.pg]
  simp only [Z3.mk.injEq];exact ⟨by ring, by ring⟩
lemma pL (i : Fin 3) (v u : V3) : pI (pH i v) (pH i u) = pI v u := by
 rcases v with ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩
 rcases u with ⟨⟨c0, d0⟩, ⟨c1, d1⟩, ⟨c2, d2⟩⟩
 fin_cases i <;> ·
  simp only [pI,pH,Z3.add,Z3.sub,Z3.neg,Z3.mul,Z3.smul,Z3.pg]
  simp only [Z3.mk.injEq];exact ⟨by ring, by ring⟩
lemma pM (v : V3) : (qform v).t0 =
  v.v0.t0 ^ 2 + v.v1.t0 ^ 2 + v.v2.t0 ^ 2 -
   Y 3 * (v.v0.t0 * v.v1.t0 + v.v1.t0 * v.v2.t0 + v.v2.t0 * v.v0.t0) := by
 simp only [qform,Z3.pp,Z3.po,Z3.pr,Z3.pn];ring
lemma pN (v : V3) : (qform v).pj =
  v.v0.pj ^ 2 + v.v1.pj ^ 2 + v.v2.pj ^ 2 +
   Y 3 * (v.v0.pj * v.v1.pj + v.v1.pj * v.v2.pj +
    v.v2.pj * v.v0.pj) := by
 simp only [qform,Z3.px,Z3.pw,Z3.pz,Z3.pv];ring
end V3
structure M3 where
 r0 : V3
 r1 : V3
 r2 : V3
 deriving DecidableEq, Repr
namespace M3
def id : M3 :=
 ⟨⟨Z3.one,Z3.zero,Z3.zero⟩,
 ⟨Z3.zero,Z3.one,Z3.zero⟩,
 ⟨Z3.zero,Z3.zero,Z3.one⟩⟩
def row (M : M3) : Fin 3 → V3
 | 0 => M.r0
 | 1 => M.r1
 | 2 => M.r2
def get (M : M3) (r c : Fin 3) : Z3 := (M.row r).get c
def col (M : M3) (c : Fin 3) : V3 := ⟨M.get 0 c, M.get 1 c, M.get 2 c⟩
def pO (M : M3) (v : V3) : V3 :=
 let dot (r : V3) : Z3 :=
  Z3.add (Z3.mul r.v0 v.v0) (Z3.add (Z3.mul r.v1 v.v1) (Z3.mul r.v2 v.v2))
 ⟨dot M.r0,dot M.r1,dot M.r2⟩
def pP (M : M3) : V3 := ⟨M.r0.sum, M.r1.sum, M.r2.sum⟩
lemma pQ (M : M3) : M.pP = M.pO V3.pG := by
 rcases M with ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩, ⟨c0, c1, c2⟩⟩
 simp only [pP,V3.sum,Z3.add,pO,Z3.mul,V3.pG,Z3.one,mul_one,mul_zero,add_zero,zero_add]
def pH (i : Fin 3) (M : M3) : M3 :=
 let addVec (u v : V3) : V3 :=
  ⟨Z3.add u.v0 v.v0,Z3.add u.v1 v.v1,Z3.add u.v2 v.v2⟩
 let negSqrtVec (u v : V3) : V3 :=
  let f (x y : Z3) := Z3.add (Z3.neg x) (Z3.mul Z3.pg y)
  ⟨f u.v0 v.v0,f u.v1 v.v1,f u.v2 v.v2⟩
 match i with
 | 0 => ⟨negSqrtVec M.r0 (addVec M.r1 M.r2), M.r1, M.r2⟩
 | 1 => ⟨M.r0, negSqrtVec M.r1 (addVec M.r0 M.r2), M.r2⟩
 | 2 => ⟨M.r0, M.r1, negSqrtVec M.r2 (addVec M.r0 M.r1)⟩
def pR (i : Fin 3) (N : M3) : M3 :=
 let negVec (u : V3) : V3 := ⟨Z3.neg u.v0, Z3.neg u.v1, Z3.neg u.v2⟩
 let addSqrtVec (u v : V3) : V3 :=
  let f (x y : Z3) := Z3.add x (Z3.mul Z3.pg y)
  ⟨f u.v0 v.v0,f u.v1 v.v1,f u.v2 v.v2⟩
 match i with
 | 0 => ⟨negVec N.r0, addSqrtVec N.r1 N.r0, addSqrtVec N.r2 N.r0⟩
 | 1 => ⟨addSqrtVec N.r0 N.r1, negVec N.r1, addSqrtVec N.r2 N.r1⟩
 | 2 => ⟨addSqrtVec N.r0 N.r2, addSqrtVec N.r1 N.r2, negVec N.r2⟩
lemma pS (i c : Fin 3) (M : M3) :
  (pH i M).col c = V3.pH i (M.col c) := by
 fin_cases i <;> fin_cases c <;> rfl
lemma pT (i : Fin 3) (M : M3) (v : V3) :
  (pH i M).pO v = V3.pH i (M.pO v) := by
 fin_cases i <;> ·
  rcases M with ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩, ⟨c0, c1, c2⟩⟩
  rcases v with ⟨v0, v1, v2⟩
  simp only [pH,pO,V3.pH,Z3.add,Z3.neg,Z3.mul,Z3.pg];congr 1
  all_goals first | rfl | (simp only [Z3.mk.injEq];exact ⟨by ring, by ring⟩)
def pU (M : M3) : Prop :=
 ∀ r c : Fin 3, (r = c → (M.get r c).a % 3 ≠ 0) ∧ (r ≠ c → (M.get r c).a % 3 = 0)
lemma pV : pU id := by intro r c;fin_cases r <;> fin_cases c <;> simp only [Fin.zero_eta,Fin.isValue,get,V3.get,row,id,Z3.one,Z3.zero,Int.reduceMod,ne_eq,one_ne_zero,not_false_eq_true,not_true_eq_false,and_self,imp_self,Fin.mk_one,zero_ne_one,EuclideanDomain.zero_mod,Fin.reduceFinMk,Fin.reduceEq]
lemma pW {M : M3} (hM : pU M) (i : Fin 3) :
  pU (pH i M) := by
 intro r c;have hrc := hM r c
 have hneg : ∀ x y : Z3,
   (Z3.add (Z3.neg x) (Z3.mul Z3.pg y)).a % 3 = (-x.a) % 3 := by
  intro x y;dsimp [Z3.add, Z3.neg, Z3.mul, Z3.pg];omega
 fin_cases i <;> fin_cases r <;>
  first
  | exact hrc
  | (fin_cases c <;> dsimp [pH, get, row, V3.get] at hrc ⊢ <;> rw [hneg] <;>
    exact ⟨fun h h0 => (hrc.1 (by exact h)).elim (by omega), fun h => by have := hrc.2 (by exact h);omega⟩)
end M3
def pX : List (Fin 3) → M3
 | [] => M3.id
 | i :: w => M3.pH i (pX w)
def pY : List (Fin 3) → M3
 | [] => M3.id
 | i :: w => M3.pR i (pY w)
lemma pZ (w : List (Fin 3)) : M3.pU (pX w) := by
 induction w with
 | nil => exact M3.pV
 | cons i w ih => exact M3.pW ih i
lemma p3 (w : List (Fin 3)) :
  V3.qform (pX w).pP = ⟨3, -3⟩ := by
 rw [M3.pQ]
 induction w with
 | nil =>
  have : M3.id.pO V3.pG = V3.pG := by decide
  dsimp [pX];rw [this];exact V3.pJ
 | cons i w ih =>
  change V3.qform ((M3.pH i (pX w)).pO V3.pG) = ⟨3, -3⟩;rw [M3.pT, V3.pK, ih]
lemma p4 (w : List (Fin 3)) (c : Fin 3) :
  V3.qform ((pX w).col c) = Z3.one := by
 induction w with
 | nil => fin_cases c <;> decide
 | cons i w ih =>
  change V3.qform ((M3.pH i (pX w)).col c) = Z3.one;rw [M3.pS, V3.pK, ih]
lemma p5 (w : List (Fin 3)) (c : Fin 3) :
  V3.pI ((pX w).col c) (pX w).pP = ⟨2, -2⟩ := by
 rw [M3.pQ]
 induction w with
 | nil => fin_cases c <;> decide
 | cons i w ih =>
  change V3.pI ((M3.pH i (pX w)).col c) ((M3.pH i (pX w)).pO V3.pG) = ⟨2, -2⟩;rw [M3.pS, M3.pT, V3.pL, ih]
private lemma p6 (x y z : ℤ) (hsq : x ^ 2 + y ^ 2 + z ^ 2 = 1)
  (hx : x % 3 = 0) : x = 0 := by
 have hlin : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith only [hsq, sq_nonneg y, sq_nonneg z]
 omega
lemma p7 (w : List (Fin 3))
  (h1 : (pX w).pP = V3.pG) : pX w = M3.id := by
 have h3 : Y 3 ^ 2 = 3 := qc;have h3p : 0 < Y 3 := qd
 have hcol : ∀ c : Fin 3, (pX w).col c = M3.id.col c := by
  intro c;set v := (pX w).col c with hv_def;have hq : V3.qform v = Z3.one := p4 w c;have hb : V3.pI v (pX w).pP = ⟨2, -2⟩ := p5 w c;rw [h1] at hb
  have hsum : v.sum = Z3.one := by
   have hb_eq : V3.pI v V3.pG = Z3.mul ⟨2, -2⟩ v.sum := by
    rcases v with ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩
    simp only [V3.pI,Z3.sub,Z3.smul,Z3.add,Z3.mul,V3.pG,Z3.one,mul_one,mul_zero,add_zero,zero_add,Z3.pg,Int.reduceAdd,zero_mul,one_mul,V3.sum,Int.reduceNeg,mul_neg,Int.reduceMul,neg_mul,Z3.mk.injEq]
    exact ⟨by ring, by ring⟩
   rw [hb_eq] at hb
   have hre : (Z3.mul ⟨2, -2⟩ v.sum).t0 = (⟨2, -2⟩ : Z3).t0 := by rw [hb]
   rw [Z3.pr] at hre
   have hne : (⟨2, -2⟩ : Z3).t0 ≠ 0 := by dsimp [Z3.t0];intro h;push_cast at h;nlinarith only [h, h3]
   have hs1 : v.sum.t0 = 1 :=
    mul_left_cancel₀ hne (by rw [hre, mul_one])
   have hconj : (Z3.mul ⟨2, -2⟩ v.sum).pj = (⟨2, -2⟩ : Z3).pj := by rw [hb]
   rw [Z3.pz] at hconj
   have hnec : (⟨2, -2⟩ : Z3).pj ≠ 0 := by dsimp [Z3.pj];intro h;push_cast at h;nlinarith only [h, h3, h3p]
   have hsc : v.sum.pj = 1 :=
    mul_left_cancel₀ hnec (by rw [hconj, mul_one])
   have ha : v.sum.a = 1 := by
    have : (v.sum.a : X) = 1 := by dsimp [Z3.t0] at hs1;dsimp [Z3.pj] at hsc;linarith
    exact_mod_cast this
   have hb_zero : v.sum.b = 0 := by
    have : (v.sum.b : X) * Y 3 = 0 := by dsimp [Z3.t0] at hs1;dsimp [Z3.pj] at hsc;linarith
    rcases mul_eq_zero.mp this with hb0 | hrt
    · exact_mod_cast hb0
    · exfalso;linarith
   rcases hv : v.sum with ⟨sa, sb⟩
   rw [hv] at ha hb_zero;simp only at ha hb_zero;rw [ha, hb_zero];rfl
  have hq_real : v.v0.t0 ^ 2 + v.v1.t0 ^ 2 + v.v2.t0 ^ 2 = 1 := by
   have hqt : (V3.qform v).t0 = 1 := by rw [hq, Z3.pm]
   rw [V3.pM] at hqt
   have hsr : v.v0.t0 + v.v1.t0 + v.v2.t0 = 1 := by
    have := congr_arg Z3.t0 hsum;simp only [V3.sum,Z3.po,Z3.pm] at this;linarith
   have hid : 2 * (v.v0.t0 ^ 2 + v.v1.t0 ^ 2 + v.v2.t0 ^ 2 -
     Y 3 * (v.v0.t0 * v.v1.t0 + v.v1.t0 * v.v2.t0 +
      v.v2.t0 * v.v0.t0)) =
     (2 + Y 3) * (v.v0.t0 ^ 2 + v.v1.t0 ^ 2 + v.v2.t0 ^ 2) -
      Y 3 * (v.v0.t0 + v.v1.t0 + v.v2.t0) ^ 2 := by ring
   rw [hqt, hsr] at hid
   have hpos : 0 < 2 + Y 3 := by positivity
   nlinarith only [hid, hpos]
  have hqc_real : v.v0.pj ^ 2 + v.v1.pj ^ 2 + v.v2.pj ^ 2 = 1 := by
   have hqc : (V3.qform v).pj = 1 := by rw [hq, Z3.pu]
   rw [V3.pN] at hqc
   have hsc : v.v0.pj + v.v1.pj + v.v2.pj = 1 := by
    have := congr_arg Z3.pj hsum;simp only [V3.sum,Z3.pw,Z3.pu] at this;linarith
   have hid : 2 * (v.v0.pj ^ 2 + v.v1.pj ^ 2 + v.v2.pj ^ 2 +
     Y 3 * (v.v0.pj * v.v1.pj + v.v1.pj * v.v2.pj +
      v.v2.pj * v.v0.pj)) =
     (2 - Y 3) * (v.v0.pj ^ 2 + v.v1.pj ^ 2 + v.v2.pj ^ 2) +
      Y 3 * (v.v0.pj + v.v1.pj + v.v2.pj) ^ 2 := by ring
   rw [hqc, hsc] at hid
   have hpos : 0 < 2 - Y 3 := by nlinarith only [h3, h3p]
   nlinarith only [hid, hpos]
  have hsum_int : v.v0.a ^ 2 + 3 * v.v0.b ^ 2 + (v.v1.a ^ 2 + 3 * v.v1.b ^ 2) +
    (v.v2.a ^ 2 + 3 * v.v2.b ^ 2) = 1 := by
   have hR : ((v.v0.a ^ 2 + 3 * v.v0.b ^ 2 + (v.v1.a ^ 2 + 3 * v.v1.b ^ 2) +
     (v.v2.a ^ 2 + 3 * v.v2.b ^ 2) : ℤ) : X) = 1 := by
    push_cast
    have hcomb : (v.v0.t0 ^ 2 + v.v1.t0 ^ 2 + v.v2.t0 ^ 2) +
      (v.v0.pj ^ 2 + v.v1.pj ^ 2 + v.v2.pj ^ 2) = 2 := by linarith
    have hid2 : (v.v0.t0 ^ 2 + v.v1.t0 ^ 2 + v.v2.t0 ^ 2) +
      (v.v0.pj ^ 2 + v.v1.pj ^ 2 + v.v2.pj ^ 2) =
      2 * ((v.v0.a : X) ^ 2 + Y 3 ^ 2 * (v.v0.b : X) ^ 2 +
       ((v.v1.a : X) ^ 2 + Y 3 ^ 2 * (v.v1.b : X) ^ 2) +
       ((v.v2.a : X) ^ 2 + Y 3 ^ 2 * (v.v2.b : X) ^ 2)) := by
     dsimp [Z3.t0, Z3.pj];ring
    rw [hid2, h3] at hcomb;linarith
   exact_mod_cast hR
  have hmod := pZ w
  have hb0 : v.v0.b = 0 := by
   have h3b : 3 * v.v0.b ^ 2 ≤ 1 := by
    linarith [sq_nonneg v.v0.a, sq_nonneg v.v1.a, sq_nonneg v.v2.a,
     sq_nonneg v.v1.b, sq_nonneg v.v2.b, hsum_int]
   nlinarith only [h3b]
  have hb1 : v.v1.b = 0 := by
   have h3b : 3 * v.v1.b ^ 2 ≤ 1 := by
    linarith [sq_nonneg v.v0.a, sq_nonneg v.v1.a, sq_nonneg v.v2.a,
     sq_nonneg v.v0.b, sq_nonneg v.v2.b, hsum_int]
   nlinarith only [h3b]
  have hb2 : v.v2.b = 0 := by
   have h3b : 3 * v.v2.b ^ 2 ≤ 1 := by
    linarith [sq_nonneg v.v0.a, sq_nonneg v.v1.a, sq_nonneg v.v2.a,
     sq_nonneg v.v0.b, sq_nonneg v.v1.b, hsum_int]
   nlinarith only [h3b]
  have ha_sum : v.v0.a + v.v1.a + v.v2.a = 1 := by
   have := congr_arg Z3.a hsum;simp only [V3.sum,Z3.add,Z3.one] at this;linarith
  have ha_sq : v.v0.a ^ 2 + v.v1.a ^ 2 + v.v2.a ^ 2 = 1 := by rw [hb0, hb1, hb2] at hsum_int;linarith
  fin_cases c
  ·
   have h0 := (hmod 0 0).1 rfl;have h1' := (hmod 1 0).2 (by decide);have h2' := (hmod 2 0).2 (by decide)
   have hv1_eq : v.v1 = (pX w).get 1 0 := by rw [hv_def];rfl
   have hv2_eq : v.v2 = (pX w).get 2 0 := by rw [hv_def];rfl
   rw [← hv1_eq] at h1';rw [← hv2_eq] at h2'
   have ha1 : v.v1.a = 0 := p6 v.v1.a v.v0.a v.v2.a (by linarith [ha_sq]) h1'
   have ha2 : v.v2.a = 0 := p6 v.v2.a v.v0.a v.v1.a (by linarith [ha_sq]) h2'
   have ha0 : v.v0.a = 1 := by linarith
   rcases v with ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩
   simp only at hb0 hb1 hb2 ha0 ha1 ha2;simp only [M3.col,M3.get,M3.row,V3.get,M3.id,Z3.one,Z3.zero];rw [ha0, hb0, ha1, hb1, ha2, hb2]
  ·
   have h0 := (hmod 0 1).2 (by decide);have h1' := (hmod 1 1).1 rfl;have h2' := (hmod 2 1).2 (by decide)
   have hv0_eq : v.v0 = (pX w).get 0 1 := by rw [hv_def];rfl
   have hv2_eq : v.v2 = (pX w).get 2 1 := by rw [hv_def];rfl
   rw [← hv0_eq] at h0;rw [← hv2_eq] at h2';have ha0 : v.v0.a = 0 := p6 v.v0.a v.v1.a v.v2.a ha_sq h0
   have ha2 : v.v2.a = 0 := p6 v.v2.a v.v0.a v.v1.a (by linarith [ha_sq]) h2'
   have ha1 : v.v1.a = 1 := by linarith
   rcases v with ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩
   simp only at hb0 hb1 hb2 ha0 ha1 ha2;simp only [M3.col,M3.get,M3.row,V3.get,M3.id,Z3.one,Z3.zero];rw [ha0, hb0, ha1, hb1, ha2, hb2]
  ·
   have h0 := (hmod 0 2).2 (by decide);have h1' := (hmod 1 2).2 (by decide);have h2' := (hmod 2 2).1 rfl
   have hv0_eq : v.v0 = (pX w).get 0 2 := by rw [hv_def];rfl
   have hv1_eq : v.v1 = (pX w).get 1 2 := by rw [hv_def];rfl
   rw [← hv0_eq] at h0;rw [← hv1_eq] at h1';have ha0 : v.v0.a = 0 := p6 v.v0.a v.v1.a v.v2.a ha_sq h0
   have ha1 : v.v1.a = 0 := p6 v.v1.a v.v0.a v.v2.a (by linarith [ha_sq]) h1'
   have ha2 : v.v2.a = 1 := by linarith
   rcases v with ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩
   simp only at hb0 hb1 hb2 ha0 ha1 ha2;simp only [M3.col,M3.get,M3.row,V3.get,M3.id,Z3.one,Z3.zero];rw [ha0, hb0, ha1, hb1, ha2, hb2]
 have c0 := hcol 0;have c1 := hcol 1;have c2 := hcol 2
 rcases hM : pX w with ⟨⟨x00, x01, x02⟩, ⟨x10, x11, x12⟩, ⟨x20, x21, x22⟩⟩
 rw [hM] at c0 c1 c2;simp only [M3.col,M3.get,M3.row,V3.get,M3.id] at c0 c1 c2;obtain ⟨rfl, rfl, rfl⟩ := V3.mk.inj c0;obtain ⟨rfl, rfl, rfl⟩ := V3.mk.inj c1;obtain ⟨rfl, rfl, rfl⟩ := V3.mk.inj c2;rfl
def p8 (n lo hi : ℕ) : ℕ → ℕ
 | 0 => lo
 | fuel + 1 =>
  if hi ≤ lo + 1 then lo
  else
   let mid := (lo + hi) / 2
   if mid * mid ≤ n then p8 n mid hi fuel else p8 n lo mid fuel
def p9 (n : ℕ) : ℕ := p8 n 0 (min (n + 1) (2 ^ 12)) 13
lemma ja (k fuel lo hi : ℕ) (hlo : lo ≤ k) (hhi : k < hi) (hpow : hi - lo ≤ 2 ^ fuel) :
  p8 (k * k) lo hi fuel = k := by
 induction fuel generalizing lo hi with
 | zero =>
  dsimp [p8]
  have : hi - lo ≤ 1 := by simpa using hpow
  omega
 | succ f ih =>
  dsimp [p8]
  by_cases hstop : hi ≤ lo + 1
  · rw [if_pos hstop];omega
  ·
   rw [if_neg hstop];let mid := (lo + hi) / 2
   have hmid_lo : lo ≤ mid := by omega
   have hmid_hi : mid < hi := by omega
   by_cases hle : mid * mid ≤ k * k
   ·
    rw [if_pos hle]
    have hmk : mid ≤ k := by nlinarith only [hle]
    refine ih mid hi hmk hhi ?_
    have h2p : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
    omega
   ·
    rw [if_neg hle]
    have hkm : k < mid := by nlinarith only [hle]
    refine ih lo mid hlo hkm ?_
    have h2p : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
    omega
lemma jb (k : ℕ) (hk : k < 2 ^ 12) : p9 (k * k) = k := by
 dsimp [p9]
 refine ja k 13 0 (min (k * k + 1) (2 ^ 12)) (Nat.zero_le k) ?_ ?_
 · exact lt_min (by nlinarith only []) hk
 · exact (min_le_right _ _).trans (by decide)
def jc (P Q : ℤ) : List Z3 :=
 if P < 0 || Q % 2 ≠ 0 then []
 else
  let q := Q / 2;let disc := P * P - 3 * Q * Q
  if disc < 0 || disc % 5 = 2 || disc % 5 = 3 || disc % 7 = 3 || disc % 7 = 5 || disc % 7 = 6 then []
  else
   let d := Int.ofNat (p9 disc.natAbs)
   if d * d ≠ disc then []
   else
    let forSdet (sdet : ℤ) : List Z3 :=
     if P + sdet < 0 || (P + sdet) % 2 ≠ 0 then []
     else
      let u0 := Int.ofNat (p9 ((P + sdet) / 2).natAbs)
      if u0 = 0 then
       if q ≠ 0 || P % 3 ≠ 0 then []
       else
        let v0 := Int.ofNat (p9 (P / 3).natAbs)
        [⟨0, v0⟩, ⟨0, -v0⟩]
      else
       if q % u0 ≠ 0 then []
       else
        let v0 := q / u0
        [⟨u0, v0⟩, ⟨-u0, -v0⟩]
    forSdet d ++ forSdet (-d)
lemma jd {u v P Q : ℤ}
  (h1 : u ^ 2 + 3 * v ^ 2 = P) (h2 : 2 * u * v = Q)
  (hu_bd : u.natAbs < 2 ^ 12) (hv_bd : v.natAbs < 2 ^ 12)
  (hd_bd : (u ^ 2 - 3 * v ^ 2).natAbs < 2 ^ 12) :
  (⟨u, v⟩ : Z3) ∈ jc P Q := by
 have hP0 : 0 ≤ P := by nlinarith only [h1, sq_nonneg u, sq_nonneg v]
 have hQ2 : Q % 2 = 0 := by rw [← h2, mul_assoc];omega
 have hq : Q / 2 = u * v := by
  have : 2 * (u * v) = Q := by linarith
  omega
 have hdisc : P * P - 3 * Q * Q = (u ^ 2 - 3 * v ^ 2) ^ 2 := by rw [← h1, ← h2];ring
 have hdisc0 : 0 ≤ P * P - 3 * Q * Q := by rw [hdisc];exact sq_nonneg _
 have hsq57 : ∀ k : ℤ, k ^ 2 % 5 ≠ 2 ∧ k ^ 2 % 5 ≠ 3 ∧ k ^ 2 % 7 ≠ 3 ∧ k ^ 2 % 7 ≠ 5 ∧ k ^ 2 % 7 ≠ 6 := by
  intro k
  have h5d : (List.range 5).all (fun r => r * r % 5 != 2 && r * r % 5 != 3) = true := by decide
  have h7d : (List.range 7).all (fun r => r * r % 7 != 3 && r * r % 7 != 5 && r * r % 7 != 6) = true := by decide
  have hm5 : (k % 5).toNat < 5 := by omega
  have hm7 : (k % 7).toNat < 7 := by omega
  have h5r := (List.all_eq_true.1 h5d) _ (List.mem_range.2 hm5);have h7r := (List.all_eq_true.1 h7d) _ (List.mem_range.2 hm7)
  have hc5 : ((k % 5).toNat : ℤ) = k % 5 := Int.toNat_of_nonneg (Int.emod_nonneg k (by decide))
  have hc7 : ((k % 7).toNat : ℤ) = k % 7 := Int.toNat_of_nonneg (Int.emod_nonneg k (by decide))
  have hs5 : k ^ 2 % 5 = ((k % 5).toNat * (k % 5).toNat % 5 : ℕ) := by rw [sq, Int.mul_emod, ← hc5];norm_cast
  have hs7 : k ^ 2 % 7 = ((k % 7).toNat * (k % 7).toNat % 7 : ℕ) := by rw [sq, Int.mul_emod, ← hc7];norm_cast
  simp only [Bool.and_eq_true,bne_iff_ne,ne_eq] at h5r h7r;omega
 have hm57 := hsq57 (u ^ 2 - 3 * v ^ 2);let disc := P * P - 3 * Q * Q;let d : ℤ := Int.ofNat (p9 disc.natAbs)
 have hd_nat : disc.natAbs = (u ^ 2 - 3 * v ^ 2).natAbs * (u ^ 2 - 3 * v ^ 2).natAbs := by
  have hmul : disc = (u ^ 2 - 3 * v ^ 2) * (u ^ 2 - 3 * v ^ 2) := by dsimp [disc];rw [hdisc, sq]
  rw [hmul, Int.natAbs_mul]
 have hd_eq_abs : d = ((u ^ 2 - 3 * v ^ 2).natAbs : ℤ) := by dsimp [d];rw [hd_nat, jb _ hd_bd]
 have hd2 : d * d = disc := by
  rw [hd_eq_abs]
  have hmul : ((u ^ 2 - 3 * v ^ 2).natAbs : ℤ) * ((u ^ 2 - 3 * v ^ 2).natAbs : ℤ) =
    (u ^ 2 - 3 * v ^ 2) ^ 2 := by
   rw [← Nat.cast_mul, ← Int.natAbs_mul, ← sq, Int.natAbs_of_nonneg (sq_nonneg _)]
  rw [hmul];exact hdisc.symm
 have hd_cases : u ^ 2 - 3 * v ^ 2 = d ∨ u ^ 2 - 3 * v ^ 2 = -d := by
  rw [hd_eq_abs];exact Int.natAbs_eq_iff.1 rfl
 have hfor : ∀ sdet : ℤ, u ^ 2 - 3 * v ^ 2 = sdet →
   (⟨u, v⟩ : Z3) ∈
    if P + sdet < 0 || (P + sdet) % 2 ≠ 0 then []
    else
     let u0 := Int.ofNat (p9 ((P + sdet) / 2).natAbs)
     if u0 = 0 then
      if Q / 2 ≠ 0 || P % 3 ≠ 0 then []
      else
       let v0 := Int.ofNat (p9 (P / 3).natAbs)
       [⟨0, v0⟩, ⟨0, -v0⟩]
     else
      if (Q / 2) % u0 ≠ 0 then []
      else
       let v0 := (Q / 2) / u0
       [⟨u0, v0⟩, ⟨-u0, -v0⟩] := by
  intro sdet hs
  have hPs : P + sdet = 2 * u ^ 2 := by linarith
  have hPs0 : ¬ (P + sdet < 0) := by linarith [sq_nonneg u]
  have hPs2 : ¬ ((P + sdet) % 2 ≠ 0) := by omega
  rw [if_neg (by simp only [hPs0,decide_false,hPs2,Bool.or_self,Bool.false_eq_true,not_false_eq_true])]
  have hdiv : ((P + sdet) / 2).natAbs = u.natAbs * u.natAbs := by
   have hdv : (P + sdet) / 2 = u * u := by rw [hPs, show 2 * u ^ 2 = 2 * (u * u) by ring, Int.mul_ediv_cancel_left _ (by decide)]
   rw [hdv, Int.natAbs_mul]
  have hu0 : Int.ofNat (p9 ((P + sdet) / 2).natAbs) = (u.natAbs : ℤ) := by rw [hdiv, jb _ hu_bd];rfl
  dsimp only;rw [hu0]
  by_cases hu : u = 0
  ·
   subst hu
   have hQ0 : Q / 2 = 0 := by rw [hq];simp only [zero_mul]
   have hP3 : P = 3 * v ^ 2 := by linarith
   have hP3m : P % 3 = 0 := by rw [hP3];omega
   rw [if_pos (by simp only [Int.natAbs_zero,CharP.cast_eq_zero]), if_neg (by simp only [hQ0,ne_eq,not_true_eq_false,decide_false,hP3m,Bool.or_self,Bool.false_eq_true,not_false_eq_true])]
   have hP3div : (P / 3).natAbs = v.natAbs * v.natAbs := by
    have hdv : P / 3 = v * v := by rw [hP3, show 3 * v ^ 2 = 3 * (v * v) by ring, Int.mul_ediv_cancel_left _ (by decide)]
    rw [hdv, Int.natAbs_mul]
   have hv0 : Int.ofNat (p9 (P / 3).natAbs) = (v.natAbs : ℤ) := by rw [hP3div, jb _ hv_bd];rfl
   rw [hv0]
   rcases Int.natAbs_eq v with hveq | hveq
   · rw [← hveq];exact List.Mem.head _
   ·
    have hvn : (v.natAbs : ℤ) = -v := by omega
    rw [hvn, neg_neg];exact List.Mem.tail _ (List.Mem.head _)
  ·
   have hu_ne : (u.natAbs : ℤ) ≠ 0 := by omega
   rw [if_neg hu_ne]
   have hqm : (Q / 2) % (u.natAbs : ℤ) = 0 := by
    rw [hq]
    rcases Int.natAbs_eq u with hueq | hueq
    · rw [← hueq];exact Int.mul_emod_right u v
    · rw [show (u.natAbs : ℤ) = -u by omega, Int.emod_neg];exact Int.mul_emod_right u v
   rw [if_neg (by simpa using hqm)]
   rcases Int.natAbs_eq u with hueq | hueq
   ·
    have hv0 : (Q / 2) / (u.natAbs : ℤ) = v := by rw [hq, ← hueq];exact Int.mul_ediv_cancel_left v hu
    rw [hv0, ← hueq];exact List.Mem.head _
   ·
    have hu_neg : (u.natAbs : ℤ) = -u := by omega
    have hv0 : (Q / 2) / (u.natAbs : ℤ) = -v := by
     rw [hq, hu_neg]
     have : u * v = (-u) * (-v) := by ring
     rw [this];exact Int.mul_ediv_cancel_left (-v) (by omega)
    rw [hv0, hu_neg, neg_neg, neg_neg];exact List.Mem.tail _ (List.Mem.head _)
 dsimp only [jc]
 rw [if_neg (by simp only [not_lt.2 hP0,decide_false,hQ2,ne_eq,not_true_eq_false,Bool.or_self,Bool.false_eq_true,not_false_eq_true]),
  if_neg (by simp only [Bool.or_eq_true,decide_eq_true_eq,not_or,not_lt];rw [hdisc];exact ⟨⟨⟨⟨⟨sq_nonneg _, hm57.1⟩, hm57.2.1⟩, hm57.2.2.1⟩, hm57.2.2.2.1⟩, hm57.2.2.2.2⟩)]
 change (⟨u, v⟩ : Z3) ∈ if d * d ≠ disc then [] else _;rw [if_neg (not_ne_iff.2 hd2)];rw [List.mem_append]
 rcases hd_cases with hcase | hcase
 · exact Or.inl (hfor d hcase)
 · exact Or.inr (hfor (-d) hcase)
def je (D w0 : Z3) (diff : Z3) : List V3 :=
 if (D.a + diff.a) % 2 ≠ 0 || (D.b + diff.b) % 2 ≠ 0 then []
 else
  let w1 : Z3 := ⟨(D.a + diff.a) / 2, (D.b + diff.b) / 2⟩;let w2 := Z3.sub D w1;let v : V3 := ⟨w0, w1, w2⟩
  if w1.a % 3 ≠ 0 && w2.a % 3 ≠ 0 &&
    (Z3.neg w0).l0 && (Z3.neg w1).l0 &&
    (Z3.neg w2).l0 &&
    V3.qform v == ⟨3, -3⟩ then [v]
  else []
def jf (S w0 : Z3) : Z3 :=
 let D := Z3.sub S w0;let S2 := Z3.mul S S;let rhs1 := Z3.add ⟨12, -12⟩ (Z3.mul ⟨0, 2⟩ S2);let rhs2 := Z3.mul ⟨2, -1⟩ rhs1
 Z3.sub (Z3.sub rhs2 (Z3.mul D D)) (Z3.smul 2 (Z3.mul w0 w0))
def jg : List Z3 := [
 ⟨1,2⟩,⟨2,1⟩,⟨2,2⟩,⟨3,0⟩,⟨3,1⟩,⟨3,2⟩,⟨3,3⟩,⟨4,1⟩,⟨4,2⟩,⟨4,3⟩,⟨4,4⟩,
 ⟨5,2⟩,⟨5,3⟩,⟨5,4⟩,⟨6,2⟩,⟨6,3⟩,⟨6,4⟩,⟨6,5⟩,⟨7,3⟩,⟨7,4⟩,⟨7,5⟩,⟨8,3⟩,
 ⟨8,4⟩,⟨8,5⟩,⟨8,6⟩,⟨9,4⟩,⟨9,5⟩,⟨9,6⟩,⟨10,5⟩,⟨10,6⟩,⟨10,7⟩,⟨11,5⟩,
 ⟨11,6⟩,⟨11,7⟩,⟨11,8⟩,⟨12,6⟩,⟨12,7⟩,⟨13,6⟩
]
def jh : List Z3 := [
 ⟨-2,2⟩,⟨-2,3⟩,⟨-1,1⟩,⟨-1,2⟩,⟨-1,3⟩,⟨-1,4⟩,⟨1,0⟩,⟨1,1⟩,⟨1,2⟩,⟨1,3⟩,
 ⟨1,4⟩,⟨1,5⟩,⟨2,-1⟩,⟨2,0⟩,⟨2,1⟩,⟨2,2⟩,⟨2,3⟩,⟨2,4⟩,⟨2,5⟩,⟨4,-2⟩,
 ⟨4,-1⟩,⟨4,0⟩,⟨4,1⟩,⟨4,2⟩,⟨4,3⟩,⟨4,4⟩,⟨4,5⟩,⟨4,6⟩,⟨5,-1⟩,⟨5,0⟩,
 ⟨5,1⟩,⟨5,2⟩,⟨5,3⟩,⟨5,4⟩,⟨5,5⟩,⟨5,6⟩,⟨5,7⟩,⟨7,0⟩,⟨7,1⟩,⟨7,2⟩,
 ⟨7,3⟩,⟨7,4⟩,⟨7,5⟩,⟨7,6⟩,⟨7,7⟩,⟨7,8⟩,⟨8,0⟩,⟨8,1⟩,⟨8,2⟩,⟨8,3⟩,
 ⟨8,4⟩,⟨8,5⟩,⟨8,6⟩,⟨8,7⟩,⟨8,8⟩,⟨8,9⟩,⟨10,2⟩,⟨10,3⟩,⟨10,4⟩,⟨10,5⟩,
 ⟨10,6⟩,⟨10,7⟩,⟨10,8⟩,⟨11,2⟩,⟨11,3⟩,⟨11,4⟩,⟨11,5⟩,⟨11,6⟩,⟨11,7⟩,
 ⟨11,8⟩,⟨13,3⟩,⟨13,4⟩,⟨13,5⟩,⟨13,6⟩,⟨14,4⟩,⟨14,5⟩,⟨14,6⟩,⟨16,5⟩
]
lemma ji {A B : ℕ} (hA : A < 15) (hB : B < 9)
  (h1 : (Z3.sub ⟨(A : ℤ), (B : ℤ)⟩ (Z3.ph 3)).n0 = true)
  (h2 : (Z3.sub (Z3.ph 25) ⟨(A : ℤ), (B : ℤ)⟩).n0 = true)
  (h3 : (Z3.sub (Z3.ph 9)
   (Z3.mul (⟨(A : ℤ), (B : ℤ)⟩ : Z3).conj (⟨(A : ℤ), (B : ℤ)⟩ : Z3).conj)).n0 = true) :
  (⟨(A : ℤ), (B : ℤ)⟩ : Z3) ∈ jg := by
 have hdec : (List.range 15).all (fun A => (List.range 9).all fun B =>
   let S : Z3 := ⟨(A : ℤ), (B : ℤ)⟩
   !((Z3.sub S (Z3.ph 3)).n0 &&
    (Z3.sub (Z3.ph 25) S).n0 &&
    (Z3.sub (Z3.ph 9) (Z3.mul S.conj S.conj)).n0) ||
   jg.any (· == S)) = true := by decide
 rw [List.all_eq_true] at hdec;have h1' := hdec A (List.mem_range.2 hA);rw [List.all_eq_true] at h1';have h2' := h1' B (List.mem_range.2 hB)
 simp only [Bool.or_eq_true, h1, h2, h3, Bool.and_true, Bool.not_true,
  Bool.false_eq_true, false_or, List.any_eq_true, beq_iff_eq] at h2'
 obtain ⟨_, hy, rfl⟩ := h2';exact hy
lemma jj {i0 j0 : ℕ} (hi : i0 < 20) (hj : j0 < 12)
  (hm : ((i0 : ℤ) - 3) % 3 ≠ 0)
  (h1 : (⟨(i0 : ℤ) - 3, (j0 : ℤ) - 2⟩ : Z3).n0 = true)
  (h2 : (⟨(i0 : ℤ) - 3, (j0 : ℤ) - 2⟩ : Z3).l0 = false)
  (h3 : (Z3.sub (Z3.ph 25) ⟨(i0 : ℤ) - 3, (j0 : ℤ) - 2⟩).n0 = true)
  (h4 : (Z3.sub (Z3.ph 64)
   (Z3.mul (⟨(i0 : ℤ) - 3, (j0 : ℤ) - 2⟩ : Z3).conj
    (⟨(i0 : ℤ) - 3, (j0 : ℤ) - 2⟩ : Z3).conj)).n0 = true) :
  (⟨(i0 : ℤ) - 3, (j0 : ℤ) - 2⟩ : Z3) ∈ jh := by
 have hdec : (List.range 20).all (fun i0 => (List.range 12).all fun j0 =>
   let a0 : ℤ := (i0 : ℤ) - 3;let w0 : Z3 := ⟨a0, (j0 : ℤ) - 2⟩
   !(a0 % 3 ≠ 0 && w0.n0 && !w0.l0 &&
    (Z3.sub (Z3.ph 25) w0).n0 &&
    (Z3.sub (Z3.ph 64) (Z3.mul w0.conj w0.conj)).n0) ||
   jh.any (· == w0)) = true := by decide
 rw [List.all_eq_true] at hdec;have h1' := hdec i0 (List.mem_range.2 hi);rw [List.all_eq_true] at h1';have h2' := h1' j0 (List.mem_range.2 hj)
 simp only [Bool.or_eq_true, decide_eq_true hm, h1, h2, h3, h4, Bool.and_true, Bool.not_false,
  Bool.not_true, Bool.false_eq_true, false_or, List.any_eq_true, beq_iff_eq] at h2'
 obtain ⟨_, hy, rfl⟩ := h2';exact hy
def jk (S w0 : Z3) : List V3 :=
 let D := Z3.sub S w0;let RHS := jf S w0
 (jc RHS.a RHS.b).flatMap (je D w0)
def jl (S : Z3) : List V3 :=
 jh.flatMap (jk S)
def jm : List V3 :=
 jg.flatMap jl
def jn : List (List (Fin 3)) :=
 [[],[0],[1],[2],[1,0],[2,0],[0,1],[2,1],[0,2],[1,2],
 [0,1,0],[2,1,0],[0,2,0],[1,2,0],[1,0,1],[2,0,1],
 [0,2,1],[1,2,1],[1,0,2],[2,0,2],[0,1,2],[2,1,2],
 [1,0,1,0],[2,0,2,0],[0,1,0,1],[2,1,2,1],[0,2,0,2],
 [1,2,1,2],[0,1,0,1,0],[0,2,0,2,0],[1,0,1,0,1],
 [1,2,1,2,1],[2,0,2,0,2],[2,1,2,1,2],[1,0,1,0,1,0],
 [2,0,2,0,2,0],[2,1,2,1,2,1]]
def jo : List V3 := [
 ⟨⟨1,0⟩,⟨1,0⟩,⟨1,0⟩⟩,⟨⟨-1,2⟩,⟨1,0⟩,⟨1,0⟩⟩,⟨⟨1,0⟩,⟨-1,2⟩,⟨1,0⟩⟩,
 ⟨⟨1,0⟩,⟨1,0⟩,⟨-1,2⟩⟩,⟨⟨-1,2⟩,⟨5,0⟩,⟨1,0⟩⟩,⟨⟨-1,2⟩,⟨1,0⟩,⟨5,0⟩⟩,
 ⟨⟨5,0⟩,⟨-1,2⟩,⟨1,0⟩⟩,⟨⟨1,0⟩,⟨-1,2⟩,⟨5,0⟩⟩,⟨⟨5,0⟩,⟨1,0⟩,⟨-1,2⟩⟩,
 ⟨⟨1,0⟩,⟨5,0⟩,⟨-1,2⟩⟩,⟨⟨1,4⟩,⟨5,0⟩,⟨1,0⟩⟩,⟨⟨-1,2⟩,⟨5,0⟩,⟨5,4⟩⟩,
 ⟨⟨1,4⟩,⟨1,0⟩,⟨5,0⟩⟩,⟨⟨-1,2⟩,⟨5,4⟩,⟨5,0⟩⟩,⟨⟨5,0⟩,⟨1,4⟩,⟨1,0⟩⟩,
 ⟨⟨5,0⟩,⟨-1,2⟩,⟨5,4⟩⟩,⟨⟨5,4⟩,⟨-1,2⟩,⟨5,0⟩⟩,⟨⟨1,0⟩,⟨1,4⟩,⟨5,0⟩⟩,
 ⟨⟨5,0⟩,⟨5,4⟩,⟨-1,2⟩⟩,⟨⟨5,0⟩,⟨1,0⟩,⟨1,4⟩⟩,⟨⟨5,4⟩,⟨5,0⟩,⟨-1,2⟩⟩,
 ⟨⟨1,0⟩,⟨5,0⟩,⟨1,4⟩⟩,⟨⟨1,4⟩,⟨7,2⟩,⟨1,0⟩⟩,⟨⟨1,4⟩,⟨1,0⟩,⟨7,2⟩⟩,
 ⟨⟨7,2⟩,⟨1,4⟩,⟨1,0⟩⟩,⟨⟨1,0⟩,⟨1,4⟩,⟨7,2⟩⟩,⟨⟨7,2⟩,⟨1,0⟩,⟨1,4⟩⟩,
 ⟨⟨1,0⟩,⟨7,2⟩,⟨1,4⟩⟩,⟨⟨5,4⟩,⟨7,2⟩,⟨1,0⟩⟩,⟨⟨5,4⟩,⟨1,0⟩,⟨7,2⟩⟩,
 ⟨⟨7,2⟩,⟨5,4⟩,⟨1,0⟩⟩,⟨⟨1,0⟩,⟨5,4⟩,⟨7,2⟩⟩,⟨⟨7,2⟩,⟨1,0⟩,⟨5,4⟩⟩,
 ⟨⟨1,0⟩,⟨7,2⟩,⟨5,4⟩⟩,⟨⟨5,4⟩,⟨5,4⟩,⟨1,0⟩⟩,⟨⟨5,4⟩,⟨1,0⟩,⟨5,4⟩⟩,
 ⟨⟨1, 0⟩, ⟨5, 4⟩, ⟨5, 4⟩⟩
]
lemma jp :
  jn.map (fun w => (pX w).pP) = jo := by
 decide
lemma jq :
  jm.all (fun v => jn.any (fun w => (pX w).pP == v)) = true := by
 have hpts : jm.all (fun v => jo.any (fun u => u == v)) = true := by decide
 rw [← jp] at hpts;simp only [List.any_map,Function.comp_def] at hpts;exact hpts
noncomputable section
def jr : List (Fin 3) → Z → Z
 | [], z => z
 | i :: w, z => qL i (jr w z)
def js : List (Fin 3) → Z → Z
 | [], z => z
 | i :: w, z => qX i (js w z)
lemma jt (w₁ w₂ : List (Fin 3)) (z : Z) :
  jr (w₁ ++ w₂) z = jr w₁ (jr w₂ z) := by
 induction w₁ with
 | nil => rfl
 | cons i w₁ ih => simp only [List.cons_append,jr,ih]
lemma ju (w₁ w₂ : List (Fin 3)) (z : Z) :
  js (w₁ ++ w₂) z = js w₁ (js w₂ z) := by
 induction w₁ with
 | nil => rfl
 | cons i w₁ ih => simp only [List.cons_append,js,ih]
lemma jv (w : List (Fin 3)) {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  jr w z ∈ ball (0 : Z) 1 := by
 induction w with
 | nil => exact hz
 | cons i w ih => exact qN ih
lemma jw (w : List (Fin 3)) {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  jr w.reverse (jr w z) = z := by
 induction w with
 | nil => rfl
 | cons i w ih =>
  simp only [List.reverse_cons,jt,jr];have hmem : jr w z ∈ ball (0 : Z) 1 := jv w hz;rw [qO hmem, ih]
lemma jx (w : List (Fin 3)) (z : Z) :
  js w.reverse (js w z) = z := by
 induction w with
 | nil => rfl
 | cons i w ih =>
  simp only [List.reverse_cons,ju,js,q0,ih]
lemma jy (w : List (Fin 3)) {z u : Z} (hz : z ∈ ball (0 : Z) 1) (hu : u ∈ ball (0 : Z) 1) :
  qR (jr w z) (jr w u) = qR z u := by
 induction w with
 | nil => rfl
 | cons i w ih =>
  exact (qS (jv w hz) (jv w hu)).trans ih
lemma jz (w : List (Fin 3)) {z : Z} (hz : z ∈ ball (0 : Z) 1) (r : Fin 3) :
  Φ (jr w z) r =
   ((pX w).get r 0).t0 * Φ z 0 + ((pX w).get r 1).t0 * Φ z 1 +
    ((pX w).get r 2).t0 * Φ z 2 := by
 induction w generalizing r with
 | nil =>
  fin_cases r <;> simp only [jr,Fin.zero_eta,Fin.isValue,M3.get,V3.get,M3.row,pX,M3.id,Z3.pm,one_mul,Z3.pl,zero_mul,add_zero,Fin.mk_one,zero_add,Fin.reduceFinMk]
 | cons i w ih =>
  have hmem := jv w hz
  have hsum : ∀ x : Z, Φ x 0 + Φ x 1 + Φ x 2 - Φ x 0 = Φ x 1 + Φ x 2 := fun x => by ring
  have hsum1 : ∀ x : Z, Φ x 0 + Φ x 1 + Φ x 2 - Φ x 1 = Φ x 0 + Φ x 2 := fun x => by ring
  have hsum2 : ∀ x : Z, Φ x 0 + Φ x 1 + Φ x 2 - Φ x 2 = Φ x 0 + Φ x 1 := fun x => by ring
  change Φ (qL i (jr w z)) r = _
  rcases i with ⟨i, hi⟩;rcases r with ⟨r, hr⟩
  interval_cases i <;> interval_cases r
  ·
   change Φ (qL 0 (jr w z)) 0 = _;rw [pe hmem, hsum, ih 0, ih 1, ih 2];simp only [M3.get,V3.get,M3.row,Fin.isValue,neg_add_rev,pX,M3.pH,Z3.po,Z3.pq,Z3.pr,Z3.pn];ring
  · change Φ (qL 0 (jr w z)) 1 = _;rw [pf (by decide) hmem, ih 1];rfl
  · change Φ (qL 0 (jr w z)) 2 = _;rw [pf (by decide) hmem, ih 2];rfl
  · change Φ (qL 1 (jr w z)) 0 = _;rw [pf (by decide) hmem, ih 0];rfl
  ·
   change Φ (qL 1 (jr w z)) 1 = _;rw [pe hmem, hsum1, ih 0, ih 1, ih 2];simp only [M3.get,V3.get,M3.row,Fin.isValue,neg_add_rev,pX,M3.pH,Z3.po,Z3.pq,Z3.pr,Z3.pn];ring
  · change Φ (qL 1 (jr w z)) 2 = _;rw [pf (by decide) hmem, ih 2];rfl
  · change Φ (qL 2 (jr w z)) 0 = _;rw [pf (by decide) hmem, ih 0];rfl
  · change Φ (qL 2 (jr w z)) 1 = _;rw [pf (by decide) hmem, ih 1];rfl
  ·
   change Φ (qL 2 (jr w z)) 2 = _;rw [pe hmem, hsum2, ih 0, ih 1, ih 2];simp only [M3.get,V3.get,M3.row,Fin.isValue,neg_add_rev,pX,M3.pH,Z3.po,Z3.pq,Z3.pr,Z3.pn];ring
lemma jA (w : List (Fin 3)) (r : Fin 3) :
  Φ (jr w 0) r = ((pX w).pP.get r).t0 := by
 rw [jz w (mem_ball_self one_pos) r, q7 0, q7 1, q7 2]
 fin_cases r <;> simp only [M3.get,V3.get,M3.row,mul_one,M3.pP,V3.sum,Z3.po] <;> ring
lemma jB (w : List (Fin 3)) {z : Z} (hz : z ∈ ball (0 : Z) 1) (r : Fin 3) :
  q5 (jr w z) r =
   ((pY w).get r 0).t0 * q5 z 0 + ((pY w).get r 1).t0 * q5 z 1 +
    ((pY w).get r 2).t0 * q5 z 2 := by
 induction w generalizing r with
 | nil =>
  fin_cases r <;> simp only [jr,Fin.zero_eta,Fin.isValue,M3.get,V3.get,M3.row,pY,M3.id,Z3.pm,one_mul,Z3.pl,zero_mul,add_zero,Fin.mk_one,zero_add,Fin.reduceFinMk]
 | cons i w ih =>
  have hmem := jv w hz;change q5 (qL i (jr w z)) r = _
  rcases i with ⟨i, hi⟩;rcases r with ⟨r, hr⟩
  interval_cases i <;> interval_cases r
  ·
   change q5 (qL 0 (jr w z)) 0 = _;rw [pb hmem, ih 0];simp only [M3.get,V3.get,M3.row,Fin.isValue,neg_add_rev,pY,M3.pR,Z3.pq,neg_mul];ring
  ·
   change q5 (qL 0 (jr w z)) 1 = _;rw [pc (by decide) hmem, ih 1, ih 0]
   simp only [M3.get,V3.get,M3.row,Fin.isValue,pY,M3.pR,Z3.po,Z3.pr,Z3.pn];ring
  ·
   change q5 (qL 0 (jr w z)) 2 = _;rw [pc (by decide) hmem, ih 2, ih 0]
   simp only [M3.get,V3.get,M3.row,Fin.isValue,pY,M3.pR,Z3.po,Z3.pr,Z3.pn];ring
  ·
   change q5 (qL 1 (jr w z)) 0 = _;rw [pc (by decide) hmem, ih 0, ih 1]
   simp only [M3.get,V3.get,M3.row,Fin.isValue,pY,M3.pR,Z3.po,Z3.pr,Z3.pn];ring
  ·
   change q5 (qL 1 (jr w z)) 1 = _;rw [pb hmem, ih 1];simp only [M3.get,V3.get,M3.row,Fin.isValue,neg_add_rev,pY,M3.pR,Z3.pq,neg_mul];ring
  ·
   change q5 (qL 1 (jr w z)) 2 = _;rw [pc (by decide) hmem, ih 2, ih 1]
   simp only [M3.get,V3.get,M3.row,Fin.isValue,pY,M3.pR,Z3.po,Z3.pr,Z3.pn];ring
  ·
   change q5 (qL 2 (jr w z)) 0 = _;rw [pc (by decide) hmem, ih 0, ih 2]
   simp only [M3.get,V3.get,M3.row,Fin.isValue,pY,M3.pR,Z3.po,Z3.pr,Z3.pn];ring
  ·
   change q5 (qL 2 (jr w z)) 1 = _;rw [pc (by decide) hmem, ih 1, ih 2]
   simp only [M3.get,V3.get,M3.row,Fin.isValue,pY,M3.pR,Z3.po,Z3.pr,Z3.pn];ring
  ·
   change q5 (qL 2 (jr w z)) 2 = _;rw [pb hmem, ih 2];simp only [M3.get,V3.get,M3.row,Fin.isValue,neg_add_rev,pY,M3.pR,Z3.pq,neg_mul];ring
lemma jC {z : Z} (hz : z ∈ ball (0 : Z) 1) (i : Fin 3) : 0 < Φ z i := by
 have h3 : Y 3 ^ 2 = 3 := qc;have hden : 0 < R2 * (1 - W z) := mul_pos qu (sub_pos.2 (qm hz))
 have hnum : Φ z i * (R2 * (1 - W z)) =
   R2 * ((1 + W z) +
    (2 * (6 * Y 3 - 10) * tR) * (z * T (qy i)).re) := by
  have hsum := q8 hz
  have hns : W (z - qH i) - R2 =
    W z + 1 - 2 * tR * (z * T (qy i)).re := by
   have hc := qI i
   have hre : (z * T (qH i)).re = tR * (z * T (qy i)).re := by simp only [qH,map_mul,conj_ofReal,mul_re,ofReal_re,conj_re,ofReal_im,conj_im,mul_neg,zero_mul,neg_zero,sub_zero,mul_im,add_zero,sub_neg_eq_add];ring
   have hns0 : W (z - qH i) =
     W z + W (qH i) - 2 * (z * T (qH i)).re := by
    simp only [normSq_apply, sub_re, sub_im, mul_re,
     conj_re, conj_im]
    ring
   rw [hns0, hc, hre];dsimp [R2];ring
  have hR2 : R2 = 3 * (1 + Y 3) / 2 := qt
  have hmul : (1 + Y 3) * (6 * Y 3 - 10) = 2 * (4 - 2 * Y 3) := by linear_combination 6 * h3
  dsimp [Φ];rw [hsum]
  have hip : q5 z i * (R2 * (1 - W z)) =
    -3 * (W (z - qH i) - R2) := by
   dsimp [q5];rw [div_mul_cancel₀ _ hden.ne']
  have hsum_mul : (-9 * (1 + W z) / (R2 * (1 - W z))) *
    (R2 * (1 - W z)) = -9 * (1 + W z) := by
   rw [div_mul_cancel₀ _ hden.ne']
  have hc : 3 * (1 + Y 3) / 2 * (2 * (6 * Y 3 - 10) * tR) =
    6 * (4 - 2 * Y 3) * tR := by linear_combination 3 * tR * hmul
  calc ((4 - 2 * Y 3) * q5 z i +
        (Y 3 - 3) / 2 * (-9 * (1 + W z) / (R2 * (1 - W z)))) *
        (R2 * (1 - W z))
      = (4 - 2 * Y 3) * (q5 z i * (R2 * (1 - W z))) +
        (Y 3 - 3) / 2 * ((-9 * (1 + W z) / (R2 * (1 - W z))) *
          (R2 * (1 - W z))) := by ring
    _ = (4 - 2 * Y 3) * (-3 * (W z + 1 - 2 * tR * (z * T (qy i)).re)) +
        (Y 3 - 3) / 2 * (-9 * (1 + W z)) := by rw [hip, hns, hsum_mul]
    _ = (3 * (1 + Y 3) / 2) * (1 + W z) +
        (6 * (4 - 2 * Y 3) * tR) * (z * T (qy i)).re := by ring
    _ = (3 * (1 + Y 3) / 2) * (1 + W z) +
        (3 * (1 + Y 3) / 2 * (2 * (6 * Y 3 - 10) * tR)) * (z * T (qy i)).re := by
        rw [hc]
    _ = R2 * ((1 + W z) + (2 * (6 * Y 3 - 10) * tR) * (z * T (qy i)).re) := by rw [hR2];ring
 have hcoeff_sq : (2 * (6 * Y 3 - 10) * tR) ^ 2 = 48 * Y 3 - 80 := by
  rw [show (2 * (6 * Y 3 - 10) * tR) ^ 2 = 4 * (6 * Y 3 - 10) ^ 2 * tR ^ 2 by ring,
   qr]
  nlinarith only [h3]
 have hcoeff_lt : (2 * (6 * Y 3 - 10) * tR) ^ 2 < 4 := by
  rw [hcoeff_sq]
  have : Y 3 < 7 / 4 := by rw [Real.sqrt_lt' (by norm_num)];norm_num
  linarith
 have hre_le : |(z * T (qy i)).re| ≤ ‖z‖ := by
  calc |(z * T (qy i)).re| ≤ ‖z * T (qy i)‖ := abs_re_le_norm _
    _ = ‖z‖ * ‖qy i‖ := by rw [norm_mul, norm_conj]
    _ = ‖z‖ := by rw [qz, mul_one]
 have hnz : 0 < 1 + W z + (2 * (6 * Y 3 - 10) * tR) * (z * T (qy i)).re := by
  have h1 : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
  have hns : W z = ‖z‖ ^ 2 := (Complex.sq_norm z).symm
  have h2 : |(2 * (6 * Y 3 - 10) * tR) * (z * T (qy i)).re| ≤
    |2 * (6 * Y 3 - 10) * tR| * ‖z‖ := by
   rw [abs_mul];exact mul_le_mul_of_nonneg_left hre_le (abs_nonneg _)
  have h3' : |2 * (6 * Y 3 - 10) * tR| < 2 := by nlinarith only [sq_abs (2 * (6 * Y 3 - 10) * tR), hcoeff_lt]
  have h4 : (1 - ‖z‖) ^ 2 > 0 := sq_pos_of_pos (sub_pos.2 h1);nlinarith only [abs_le.1 h2, norm_nonneg z, h1, hns, h3']
 nlinarith only [qu, hden, hnum, hnz]
lemma jD : InjOn Φ (ball (0 : Z) 1) := by
 intro z hz u hu hΦ
 have hip : ∀ i : Fin 3, q5 z i = q5 u i := fun i => by
  rw [pa, pa, hΦ]
 have hns : W z = W u := by
  have h1 : (1 + W z) / (1 - W z) =
    (1 + W u) / (1 - W u) := by
   rw [← q9 hz, ← q9 hu, hΦ]
  have hz1 : 1 - W z ≠ 0 := (sub_pos.2 (qm hz)).ne';have hu1 : 1 - W u ≠ 0 := (sub_pos.2 (qm hu)).ne';rw [div_eq_div_iff hz1 hu1] at h1;linarith
 have hdiff : ∀ i : Fin 3, W (z - qH i) = W (u - qH i) := by
  intro i;have hi := hip i;dsimp [q5] at hi;rw [hns] at hi
  have hden : R2 * (1 - W u) ≠ 0 :=
   mul_ne_zero qu.ne' (sub_pos.2 (qm hu)).ne'
  have := mul_right_cancel₀ (inv_ne_zero hden) (by simpa [div_eq_mul_inv] using hi)
  linarith
 have hre_eq : ∀ i : Fin 3, (z * T (qH i)).re = (u * T (qH i)).re := by
  intro i
  have hnsi : ∀ x : Z, W (x - qH i) =
    W x + W (qH i) - 2 * (x * T (qH i)).re := by
   intro x;simp only [normSq_apply, sub_re, sub_im, mul_re,
    conj_re, conj_im];ring
  have := hdiff i;rw [hnsi z, hnsi u, hns] at this;linarith
 have hre0 := hre_eq 0;have hre1 := hre_eq 1
 have hc0 : qH 0 = (-tR : X) := by simp only [qH,qy,mul_neg,mul_one,ofReal_neg]
 have hzre : z.re = u.re := by
  have h0 : (z * T (qH 0)).re = -tR * z.re := by rw [hc0];simp only [ofReal_neg,map_neg,conj_ofReal,mul_neg,neg_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero,neg_mul,neg_inj];ring
  have h1' : (u * T (qH 0)).re = -tR * u.re := by rw [hc0];simp only [ofReal_neg,map_neg,conj_ofReal,mul_neg,neg_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero,neg_mul,neg_inj];ring
  rw [h0, h1'] at hre0;exact mul_left_cancel₀ (neg_ne_zero.2 qq.ne') hre0
 have hzim : z.im = u.im := by
  have hc1r : (qH 1).re = tR / 2 := by simp only [qH,Fin.isValue,mul_re,ofReal_re,qD,one_div,ofReal_im,zero_mul,sub_zero];ring
  have hc1i : (qH 1).im = tR * (Y 3 / 2) := by simp only [qH,Fin.isValue,mul_im,ofReal_re,qE,ofReal_im,zero_mul,add_zero]
  have hz1 : (z * T (qH 1)).re = z.re * (tR / 2) + z.im * (tR * (Y 3 / 2)) := by simp only [mul_re,conj_re,conj_im,hc1r,hc1i];ring
  have hu1 : (u * T (qH 1)).re = u.re * (tR / 2) + u.im * (tR * (Y 3 / 2)) := by simp only [mul_re,conj_re,conj_im,hc1r,hc1i];ring
  rw [hz1, hu1, hzre] at hre1
  have hne : tR * (Y 3 / 2) ≠ 0 := mul_ne_zero qq.ne' (by positivity)
  exact mul_right_cancel₀ hne (by linarith)
 exact Complex.ext hzre hzim
lemma jE (v : V3) (hq : V3.qform v = ⟨3, -3⟩) :
  v.v0.pj ^ 2 ≤ 64 ∧ v.v1.pj ^ 2 ≤ 64 ∧ v.v2.pj ^ 2 ≤ 64 := by
 have h3 : Y 3 ^ 2 = 3 := qc;have h3p : 0 < Y 3 := qd
 have hqc : (V3.qform v).pj = 3 + 3 * Y 3 := by rw [hq];simp only [Z3.pj,Int.cast_ofNat,Int.reduceNeg,Int.cast_neg,neg_mul,sub_neg_eq_add]
 rw [V3.pN] at hqc
 have hid : v.v0.pj ^ 2 + v.v1.pj ^ 2 + v.v2.pj ^ 2 +
   Y 3 * (v.v0.pj * v.v1.pj + v.v1.pj * v.v2.pj +
    v.v2.pj * v.v0.pj) =
   (1 - Y 3 / 2) * (v.v0.pj ^ 2 + v.v1.pj ^ 2 + v.v2.pj ^ 2) +
    (Y 3 / 2) * (v.v0.pj + v.v1.pj + v.v2.pj) ^ 2 := by ring
 have hnonneg : 0 ≤ (Y 3 / 2) * (v.v0.pj + v.v1.pj + v.v2.pj) ^ 2 := by positivity
 have hc1 : (1 - Y 3 / 2) * (v.v0.pj ^ 2 + v.v1.pj ^ 2 + v.v2.pj ^ 2) ≤
   3 + 3 * Y 3 := by linarith [hqc, hid, hnonneg]
 have hpos : 0 < 2 - Y 3 := by nlinarith only [h3, h3p]
 have hmult : v.v0.pj ^ 2 + v.v1.pj ^ 2 + v.v2.pj ^ 2 ≤ 30 + 18 * Y 3 := by nlinarith only [hc1, h3, hpos]
 have hrt : Y 3 < 17 / 9 := by rw [Real.sqrt_lt' (by norm_num)];norm_num
 refine ⟨?_, ?_, ?_⟩ <;> nlinarith only [sq_nonneg v.v0.pj, sq_nonneg v.v1.pj,
  sq_nonneg v.v2.pj, hmult, hrt]
lemma jF (v : V3) (hq : V3.qform v = ⟨3, -3⟩) :
  Z3.mul (Z3.sub v.v1 v.v2) (Z3.sub v.v1 v.v2) = jf v.sum v.v0 := by
 have h3 : Y 3 ^ 2 = 3 := qc;have h3p : 0 < Y 3 := qd
 have hdiff_real : (Z3.mul (Z3.sub v.v1 v.v2) (Z3.sub v.v1 v.v2)).t0 =
   (jf v.sum v.v0).t0 := by
  have hq_real : (V3.qform v).t0 = 3 - 3 * Y 3 := by rw [hq];simp only [Z3.t0,Int.cast_ofNat,Int.reduceNeg,Int.cast_neg,neg_mul];ring
  have hS_eq : v.sum.t0 = v.v0.t0 + v.v1.t0 + v.v2.t0 := by simp only [V3.sum,Z3.po];ring
  have hc1 : (⟨12, -12⟩ : Z3).t0 = 12 - 12 * Y 3 := by dsimp [Z3.t0];push_cast;ring
  have hc2 : (⟨0, 2⟩ : Z3).t0 = 2 * Y 3 := by dsimp [Z3.t0];push_cast;ring
  have hc3 : (⟨2, -1⟩ : Z3).t0 = 2 - Y 3 := by dsimp [Z3.t0];push_cast;ring
  have hRHS_eq : (jf v.sum v.v0).t0 =
    (2 - Y 3) * (12 - 12 * Y 3 + 2 * Y 3 * v.sum.t0 ^ 2) -
     (v.sum.t0 - v.v0.t0) ^ 2 - 2 * v.v0.t0 ^ 2 := by
   dsimp only [jf]
   simp only [Z3.pp, Z3.po, Z3.pr, Z3.ps,
    hc1, hc2, hc3]
   ring
  rw [hRHS_eq, hS_eq];rw [V3.pM] at hq_real
  have hprod : (2 - Y 3) * (2 + Y 3) = 1 := by linear_combination -h3
  have hq4 : 4 * (v.v0.t0 ^ 2 + v.v1.t0 ^ 2 + v.v2.t0 ^ 2 -
    Y 3 * (v.v0.t0 * v.v1.t0 + v.v1.t0 * v.v2.t0 + v.v2.t0 * v.v0.t0)) =
    (2 + Y 3) * (2 * v.v0.t0 ^ 2 + (v.v1.t0 + v.v2.t0) ^ 2 +
     (v.v1.t0 - v.v2.t0) ^ 2) -
     2 * Y 3 * (v.v0.t0 + v.v1.t0 + v.v2.t0) ^ 2 := by ring
  rw [hq_real] at hq4
  have hid2 : 12 - 12 * Y 3 + 2 * Y 3 * (v.v0.t0 + v.v1.t0 + v.v2.t0) ^ 2 =
    (2 + Y 3) * (2 * v.v0.t0 ^ 2 + (v.v1.t0 + v.v2.t0) ^ 2 +
     (v.v1.t0 - v.v2.t0) ^ 2) := by linarith
  rw [hid2, ← mul_assoc, hprod, one_mul, Z3.pr, Z3.pp];ring
 have hdiff_conj : (Z3.mul (Z3.sub v.v1 v.v2) (Z3.sub v.v1 v.v2)).pj =
   (jf v.sum v.v0).pj := by
  have hqc : (V3.qform v).pj = 3 + 3 * Y 3 := by rw [hq];simp only [Z3.pj,Int.cast_ofNat,Int.reduceNeg,Int.cast_neg,neg_mul,sub_neg_eq_add]
  rw [V3.pN] at hqc
  have hSc_eq : v.sum.pj = v.v0.pj + v.v1.pj + v.v2.pj := by simp only [V3.sum,Z3.pw];ring
  have hc1 : (⟨12, -12⟩ : Z3).pj = 12 + 12 * Y 3 := by dsimp [Z3.pj];push_cast;ring
  have hc2 : (⟨0, 2⟩ : Z3).pj = -2 * Y 3 := by dsimp [Z3.pj];push_cast;ring
  have hc3 : (⟨2, -1⟩ : Z3).pj = 2 + Y 3 := by dsimp [Z3.pj];push_cast;ring
  have hRHS_c : (jf v.sum v.v0).pj =
    (2 + Y 3) * (12 + 12 * Y 3 - 2 * Y 3 * v.sum.pj ^ 2) -
     (v.sum.pj - v.v0.pj) ^ 2 - 2 * v.v0.pj ^ 2 := by
   dsimp only [jf]
   simp only [Z3.px, Z3.pw, Z3.pz, Z3.py,
    hc1, hc2, hc3]
   ring
  rw [hRHS_c, hSc_eq, Z3.pz, Z3.px]
  have hprod : (2 + Y 3) * (2 - Y 3) = 1 := by linear_combination -h3
  have hq4 : 4 * (v.v0.pj ^ 2 + v.v1.pj ^ 2 + v.v2.pj ^ 2 +
    Y 3 * (v.v0.pj * v.v1.pj + v.v1.pj * v.v2.pj +
     v.v2.pj * v.v0.pj)) =
    (2 - Y 3) * (2 * v.v0.pj ^ 2 + (v.v1.pj + v.v2.pj) ^ 2 +
     (v.v1.pj - v.v2.pj) ^ 2) +
     2 * Y 3 * (v.v0.pj + v.v1.pj + v.v2.pj) ^ 2 := by ring
  rw [hqc] at hq4
  have hid2 : 12 + 12 * Y 3 - 2 * Y 3 * (v.v0.pj + v.v1.pj + v.v2.pj) ^ 2 =
    (2 - Y 3) * (2 * v.v0.pj ^ 2 + (v.v1.pj + v.v2.pj) ^ 2 +
     (v.v1.pj - v.v2.pj) ^ 2) := by linarith
  rw [hid2, ← mul_assoc, hprod, one_mul];ring
 have ha : (Z3.mul (Z3.sub v.v1 v.v2) (Z3.sub v.v1 v.v2)).a = (jf v.sum v.v0).a := by
  have : ((Z3.mul (Z3.sub v.v1 v.v2) (Z3.sub v.v1 v.v2)).a : X) =
    ((jf v.sum v.v0).a : X) := by
   dsimp [Z3.t0] at hdiff_real;dsimp [Z3.pj] at hdiff_conj;linarith
  exact_mod_cast this
 have hb : (Z3.mul (Z3.sub v.v1 v.v2) (Z3.sub v.v1 v.v2)).b = (jf v.sum v.v0).b := by
  have : ((Z3.mul (Z3.sub v.v1 v.v2) (Z3.sub v.v1 v.v2)).b : X) * Y 3 =
    ((jf v.sum v.v0).b : X) * Y 3 := by
   dsimp [Z3.t0] at hdiff_real;dsimp [Z3.pj] at hdiff_conj;linarith
  exact_mod_cast mul_right_cancel₀ h3p.ne' this
 rcases hm : Z3.mul (Z3.sub v.v1 v.v2) (Z3.sub v.v1 v.v2) with ⟨ma, mb⟩
 rcases hr : jf v.sum v.v0 with ⟨ra, rb⟩
 rw [hm, hr] at ha hb;simp only at ha hb;rw [ha, hb]
lemma jG {x : Z3} (hx0 : 0 < x.t0) (hx25 : x.t0 ≤ 25)
  (hxc : (-8 : X) ≤ x.pj ∧ x.pj ≤ 8) :
  (-20 : ℤ) ≤ x.a ∧ x.a ≤ 20 ∧ (-15 : ℤ) ≤ x.b ∧ x.b ≤ 15 := by
 have hrt : 17 / 10 < Y 3 := qf
 have ha : (2 : X) * x.a = x.t0 + x.pj := by simp only [Z3.t0,Z3.pj,add_add_sub_cancel];ring
 have hb : (2 : X) * x.b * Y 3 = x.t0 - x.pj := by simp only [Z3.t0,Z3.pj,add_sub_sub_cancel];ring
 have ha_lo : (-21 : ℤ) < x.a := by exact_mod_cast (by linarith [hx0, hxc.1, ha] : (-21 : X) < x.a)
 have ha_hi : x.a < (21 : ℤ) := by exact_mod_cast (by linarith [hx25, hxc.2, ha] : (x.a : X) < 21)
 have hb_lo : (-16 : ℤ) < x.b := by exact_mod_cast (by nlinarith only [hrt, hx0, hxc.2, hb] : (-16 : X) < x.b)
 have hb_hi : x.b < (16 : ℤ) := by exact_mod_cast (by nlinarith only [hrt, hx25, hxc.1, hb] : (x.b : X) < 16)
 omega
lemma jH (diff RHS : Z3) (hsq : Z3.mul diff diff = RHS)
  (ha_bd : -40 ≤ diff.a ∧ diff.a ≤ 40) (hb_bd : -30 ≤ diff.b ∧ diff.b ≤ 30) :
  diff ∈ jc RHS.a RHS.b := by
 have ha1 : diff.a ^ 2 + 3 * diff.b ^ 2 = RHS.a := by
  have h0 := congr_arg Z3.a hsq
  dsimp [Z3.mul] at h0;linarith [show diff.a ^ 2 = diff.a * diff.a by ring,
   show diff.b ^ 2 = diff.b * diff.b by ring]
 have hb1 : 2 * diff.a * diff.b = RHS.b := by
  have h0 := congr_arg Z3.b hsq;dsimp [Z3.mul] at h0;linarith
 have hda : diff.a.natAbs < 2 ^ 12 := by omega
 have hdb : diff.b.natAbs < 2 ^ 12 := by omega
 have hdd : (diff.a ^ 2 - 3 * diff.b ^ 2).natAbs < 2 ^ 12 := by
  have ha_le : diff.a ^ 2 ≤ 40 ^ 2 := by nlinarith only [ha_bd]
  have hb_le : diff.b ^ 2 ≤ 30 ^ 2 := by nlinarith only [hb_bd]
  have hbdz : (-4096 : ℤ) < diff.a ^ 2 - 3 * diff.b ^ 2 ∧ diff.a ^ 2 - 3 * diff.b ^ 2 < 4096 := by constructor <;> nlinarith only [ha_le, hb_le, sq_nonneg diff.a, sq_nonneg diff.b]
  omega
 exact jd ha1 hb1 hda hdb hdd
lemma jI (w : List (Fin 3))
  (hS : (pX w).pP.sum.t0 ≤ 25) :
  (pX w).pP ∈ jm := by
 set v := (pX w).pP;set S := v.sum
 have hv_pos : ∀ i : Fin 3, 0 < (v.get i).t0 := fun i => by
  rw [← jA w i];exact jC (jv w (mem_ball_self one_pos)) i
 have hv0p : 0 < v.v0.t0 := hv_pos 0;have hv1p : 0 < v.v1.t0 := hv_pos 1;have hv2p : 0 < v.v2.t0 := hv_pos 2;have h3 : Y 3 ^ 2 = 3 := qc;have h3p : 0 < Y 3 := qd
 have hS_ge : 3 ≤ S.t0 := by
  have hsum := q9 (jv w (mem_ball_self one_pos));have hns0 : 0 ≤ W (jr w 0) := normSq_nonneg _;have hns1 : 0 < 1 - W (jr w 0) := sub_pos.2 (qm (jv w (mem_ball_self one_pos)))
  have hdiv : 1 ≤ (1 + W (jr w 0)) / (1 - W (jr w 0)) := by rw [le_div_iff₀ hns1];linarith
  have hseq : S.t0 = Φ (jr w 0) 0 + Φ (jr w 0) 1 + Φ (jr w 0) 2 := by
   simp only [S,V3.sum,Z3.po]
   change ((pX w).pP.get 0).t0 +
     (((pX w).pP.get 1).t0 + ((pX w).pP.get 2).t0) = _
   rw [← jA w 0, ← jA w 1, ← jA w 2];ring
  rw [hseq];linarith [hsum, hdiv]
 have hq : V3.qform v = ⟨3, -3⟩ := p3 w
 have hqc : (V3.qform v).pj = 3 + 3 * Y 3 := by rw [hq];simp only [Z3.pj,Int.cast_ofNat,Int.reduceNeg,Int.cast_neg,neg_mul,sub_neg_eq_add]
 have hSc_sq : S.pj ^ 2 ≤ 9 := by
  rw [V3.pN] at hqc
  have hsc : S.pj = v.v0.pj + v.v1.pj + v.v2.pj := by simp only [Z3.pj,V3.sum,Z3.add,Int.cast_add,S];ring
  have hid : 6 * (3 + 3 * Y 3) =
    2 * (1 + Y 3) * S.pj ^ 2 +
     (2 - Y 3) * ((v.v0.pj - v.v1.pj) ^ 2 +
      (v.v1.pj - v.v2.pj) ^ 2 + (v.v2.pj - v.v0.pj) ^ 2) := by
   rw [hsc, ← hqc];ring
  have hnonneg : 0 ≤ (2 - Y 3) * ((v.v0.pj - v.v1.pj) ^ 2 +
    (v.v1.pj - v.v2.pj) ^ 2 + (v.v2.pj - v.v0.pj) ^ 2) :=
   mul_nonneg (by nlinarith only [h3, h3p]) (by positivity)
  have h1p : 0 < 2 * (1 + Y 3) := by positivity
  nlinarith only [hid, hnonneg, h1p]
 have hconj_bd := jE v hq;have hv0c_sq : v.v0.pj ^ 2 ≤ 64 := hconj_bd.1;have hv1c_sq : v.v1.pj ^ 2 ≤ 64 ∧ v.v2.pj ^ 2 ≤ 64 := ⟨hconj_bd.2.1, hconj_bd.2.2⟩
 have hSc_abs : -3 ≤ S.pj ∧ S.pj ≤ 3 := by constructor <;> nlinarith only [hSc_sq]
 have hv0c_abs : -8 ≤ v.v0.pj ∧ v.v0.pj ≤ 8 := by constructor <;> nlinarith only [hv0c_sq]
 have hv0_le : v.v0.t0 ≤ 25 := by
  have hS_eq : S.t0 = v.v0.t0 + v.v1.t0 + v.v2.t0 := by simp only [V3.sum,Z3.po,S];ring
  linarith [hv1p, hv2p, hS_eq, hS]
 have hSA_bd : 0 ≤ S.a ∧ S.a ≤ 14 := by
  have haR : (2 : X) * S.a = S.t0 + S.pj := by simp only [Z3.t0,Z3.pj,add_add_sub_cancel];ring
  constructor
  ·
   have : (-1 : ℤ) < S.a := by exact_mod_cast (by linarith [hS_ge, hSc_abs.1, haR] : (-1 : X) < S.a)
   omega
  ·
   have : (S.a : X) < 15 := by linarith [hS, hSc_abs.2, haR]
   have : S.a < 15 := by exact_mod_cast this
   omega
 have hSB_bd : 0 ≤ S.b ∧ S.b ≤ 8 := by
  have hbR : (2 : X) * S.b * Y 3 = S.t0 - S.pj := by simp only [Z3.t0,Z3.pj,add_sub_sub_cancel];ring
  constructor
  ·
   have hSb0 : 0 ≤ (S.b : X) * Y 3 := by linarith [hS_ge, hSc_abs.2, hbR]
   have hSbR : (0 : X) ≤ S.b := nonneg_of_mul_nonneg_left hSb0 h3p;exact_mod_cast hSbR
  ·
   have : (S.b : X) * Y 3 ≤ 14 := by linarith [hS, hSc_abs.1, hbR]
   have hrt : 17 / 10 < Y 3 := qf
   have : (S.b : X) < 9 := by nlinarith only [hrt, this]
   have : S.b < 9 := by exact_mod_cast this
   omega
 have ha0_bd : -3 ≤ v.v0.a ∧ v.v0.a ≤ 16 := by
  have haR : (2 : X) * v.v0.a = v.v0.t0 + v.v0.pj := by simp only [Z3.t0,Z3.pj,add_add_sub_cancel];ring
  constructor
  ·
   have : (-4 : X) < v.v0.a := by linarith [hv0p, hv0c_abs.1, haR]
   have : -4 < v.v0.a := by exact_mod_cast this
   omega
  ·
   have : (v.v0.a : X) < 17 := by linarith [hv0_le, hv0c_abs.2, haR]
   have : v.v0.a < 17 := by exact_mod_cast this
   omega
 have hb0_bd : -2 ≤ v.v0.b ∧ v.v0.b ≤ 9 := by
  have hbR : (2 : X) * v.v0.b * Y 3 = v.v0.t0 - v.v0.pj := by simp only [Z3.t0,Z3.pj,add_sub_sub_cancel];ring
  have hrt : 17 / 10 < Y 3 := qf;constructor
  ·
   have : -(8 : X) < 2 * v.v0.b * Y 3 := by linarith only [hv0p, hv0c_abs.2, hbR]
   have : (-3 : X) < v.v0.b := by nlinarith only [hrt, this]
   have : -3 < v.v0.b := by exact_mod_cast this
   omega
  ·
   have : 2 * (v.v0.b : X) * Y 3 ≤ 33 := by linarith only [hv0_le, hv0c_abs.1, hbR]
   have : (v.v0.b : X) < 10 := by nlinarith only [hrt, this]
   have : v.v0.b < 10 := by exact_mod_cast this
   omega
 have hmod := pZ w
 have ha_mod : ∀ i : Fin 3, (v.get i).a % 3 ≠ 0 := by
  have hadd_mod : ∀ x y z : ℤ, x % 3 ≠ 0 → y % 3 = 0 → z % 3 = 0 → (x + y + z) % 3 ≠ 0 := by intro x y z hx hy hz;omega
  intro i
  have hsum_a : (v.get i).a =
    ((pX w).get i 0).a + ((pX w).get i 1).a + ((pX w).get i 2).a := by
   fin_cases i <;> simp only [V3.get,M3.pP,V3.sum,Z3.add,M3.get,M3.row,v] <;> ring
  rw [hsum_a]
  rcases i with ⟨i, hi⟩
  interval_cases i
  ·
   have h0 := (hmod 0 0).1 rfl;have h1 := (hmod 0 1).2 (by decide);have h2 := (hmod 0 2).2 (by decide)
   change (((pX w).get 0 0).a + ((pX w).get 0 1).a + ((pX w).get 0 2).a) % 3 ≠ 0;exact hadd_mod _ _ _ h0 h1 h2
  ·
   have h0 := (hmod 1 0).2 (by decide);have h1 := (hmod 1 1).1 rfl;have h2 := (hmod 1 2).2 (by decide)
   change (((pX w).get 1 0).a + ((pX w).get 1 1).a + ((pX w).get 1 2).a) % 3 ≠ 0
   rw [show ((pX w).get 1 0).a + ((pX w).get 1 1).a + ((pX w).get 1 2).a =
     ((pX w).get 1 1).a + ((pX w).get 1 0).a + ((pX w).get 1 2).a by ring]
   exact hadd_mod _ _ _ h1 h0 h2
  ·
   have h0 := (hmod 2 0).2 (by decide);have h1 := (hmod 2 1).2 (by decide);have h2 := (hmod 2 2).1 rfl
   change (((pX w).get 2 0).a + ((pX w).get 2 1).a + ((pX w).get 2 2).a) % 3 ≠ 0
   rw [show ((pX w).get 2 0).a + ((pX w).get 2 1).a + ((pX w).get 2 2).a =
     ((pX w).get 2 2).a + ((pX w).get 2 0).a + ((pX w).get 2 1).a by ring]
   exact hadd_mod _ _ _ h2 h0 h1
 let D := Z3.sub S v.v0;let RHS := jf S v.v0;let diff := Z3.sub v.v1 v.v2;have hdiff_sq : Z3.mul diff diff = RHS := jF v hq
 have hS_eq' : S.t0 = v.v0.t0 + v.v1.t0 + v.v2.t0 := by simp only [V3.sum,Z3.po,S];ring
 have hv1_le : v.v1.t0 ≤ 25 := by linarith [hv0p, hv2p, hS_eq', hS]
 have hv2_le : v.v2.t0 ≤ 25 := by linarith [hv0p, hv1p, hS_eq', hS]
 have hv12_bd : -20 ≤ v.v1.a ∧ v.v1.a ≤ 20 ∧ -20 ≤ v.v2.a ∧ v.v2.a ≤ 20 ∧
   -15 ≤ v.v1.b ∧ v.v1.b ≤ 15 ∧ -15 ≤ v.v2.b ∧ v.v2.b ≤ 15 := by
  have h1c : -8 ≤ v.v1.pj ∧ v.v1.pj ≤ 8 := by constructor <;> nlinarith only [hv1c_sq.1]
  have h2c : -8 ≤ v.v2.pj ∧ v.v2.pj ≤ 8 := by constructor <;> nlinarith only [hv1c_sq.2]
  have h1b := jG hv1p hv1_le h1c;have h2b := jG hv2p hv2_le h2c;exact ⟨h1b.1, h1b.2.1, h2b.1, h2b.2.1, h1b.2.2.1, h1b.2.2.2, h2b.2.2.1, h2b.2.2.2⟩
 have hmem_sq : diff ∈ jc RHS.a RHS.b :=
  jH diff RHS hdiff_sq
   (by dsimp [diff, Z3.sub];omega) (by dsimp [diff, Z3.sub];omega)
 have hdiff_mem : v ∈ je D v.v0 diff := by
  have hD_a : D.a + diff.a = 2 * v.v1.a := by simp only [Z3.sub,V3.sum,Z3.add,add_sub_cancel_left,add_add_sub_cancel,D,S,diff];ring
  have hD_b : D.b + diff.b = 2 * v.v1.b := by simp only [Z3.sub,V3.sum,Z3.add,add_sub_cancel_left,add_add_sub_cancel,D,S,diff];ring
  have hw1_eq : (⟨(D.a + diff.a) / 2, (D.b + diff.b) / 2⟩ : Z3) = v.v1 := by rw [hD_a, hD_b];rcases hv1 : v.v1 with ⟨a1, b1⟩;simp only;congr 1 <;> omega
  have hw2_eq : Z3.sub D v.v1 = v.v2 := by
   have h2a : (Z3.sub D v.v1).a = v.v2.a := by simp only [Z3.sub,V3.sum,Z3.add,add_sub_cancel_left,D,S]
   have h2b : (Z3.sub D v.v1).b = v.v2.b := by simp only [Z3.sub,V3.sum,Z3.add,add_sub_cancel_left,D,S]
   rcases hz : Z3.sub D v.v1 with ⟨da, db⟩
   rcases hv2 : v.v2 with ⟨va, vb⟩
   rw [hz, hv2] at h2a h2b;simp only at h2a h2b;rw [h2a, h2b]
  have ha1_mod : v.v1.a % 3 ≠ 0 := ha_mod 1
  have ha1_mod' : (D.a + diff.a) / 2 % 3 ≠ 0 := by omega
  have ha2_mod : v.v2.a % 3 ≠ 0 := ha_mod 2
  have hn0 : (Z3.neg v.v0).l0 = true := by rw [Z3.pF, Z3.pq];linarith [hv_pos 0]
  have hn1 : (Z3.neg v.v1).l0 = true := by rw [Z3.pF, Z3.pq];linarith [hv_pos 1]
  have hn2 : (Z3.neg v.v2).l0 = true := by rw [Z3.pF, Z3.pq];linarith [hv_pos 2]
  have hveq : (⟨v.v0, v.v1, v.v2⟩ : V3) = v := rfl;dsimp only [je]
  rw [if_neg (by simp only [Bool.or_eq_true,decide_eq_true_eq,ne_eq,not_or,not_not];exact ⟨by omega, by omega⟩)]
  simp only [hw1_eq,hw2_eq,hveq]
  rw [if_pos (by simp only [ne_eq,ha1_mod',not_false_eq_true,decide_true,ha2_mod,Bool.and_self,hn0,hn1,hn2,hq,Int.reduceNeg,BEq.rfl])]
  simp only [List.mem_cons,List.not_mem_nil,or_false]
 have hw0_mem : v.v0 ∈ jh := by
  have ha0_mod : v.v0.a % 3 ≠ 0 := ha_mod 0
  have hv0_nn : v.v0.n0 = true := by rw [Z3.pD];exact (hv_pos 0).le
  have hv0_nlt : v.v0.l0 = false := by rw [Bool.eq_false_iff, ne_eq, Z3.pF];linarith [hv_pos 0]
  have hv0_25 : (Z3.sub (Z3.ph 25) v.v0).n0 = true := by rw [Z3.pD, Z3.pp, Z3.pk];push_cast;linarith [hv0_le]
  have hv0_64 : (Z3.sub (Z3.ph 64) (Z3.mul v.v0.conj v.v0.conj)).n0 = true := by
   rw [Z3.pD, Z3.pp, Z3.pk, Z3.pr, ← Z3.pt];push_cast;linarith [hv0c_sq]
  have ha0_eq : ((v.v0.a + 3).toNat : ℤ) - 3 = v.v0.a := by omega
  have hb0_eq : ((v.v0.b + 2).toNat : ℤ) - 2 = v.v0.b := by omega
  have hv0_cast : (⟨((v.v0.a + 3).toNat : ℤ) - 3, ((v.v0.b + 2).toNat : ℤ) - 2⟩ : Z3) = v.v0 := by rw [ha0_eq, hb0_eq]
  rw [← hv0_cast]
  exact jj (by exact_mod_cast (by omega : ((v.v0.a + 3).toNat : ℤ) < 20))
   (by exact_mod_cast (by omega : ((v.v0.b + 2).toNat : ℤ) < 12))
   (by rw [ha0_eq];exact ha0_mod) (by rw [ha0_eq, hb0_eq];exact hv0_nn)
   (by rw [ha0_eq, hb0_eq];exact hv0_nlt) (by rw [ha0_eq, hb0_eq];exact hv0_25)
   (by rw [ha0_eq, hb0_eq];exact hv0_64)
 have hS_mem : S ∈ jg := by
  have hb1 : (Z3.sub S (Z3.ph 3)).n0 = true := by rw [Z3.pD, Z3.pp, Z3.pk];push_cast;linarith [hS_ge]
  have hb2 : (Z3.sub (Z3.ph 25) S).n0 = true := by rw [Z3.pD, Z3.pp, Z3.pk];push_cast;linarith [hS]
  have hb3 : (Z3.sub (Z3.ph 9) (Z3.mul S.conj S.conj)).n0 = true := by
   rw [Z3.pD, Z3.pp, Z3.pk, Z3.pr, ← Z3.pt];push_cast;linarith [hSc_sq]
  have hSa_toNat : (S.a.toNat : ℤ) = S.a := Int.toNat_of_nonneg hSA_bd.1;have hSb_toNat : (S.b.toNat : ℤ) = S.b := Int.toNat_of_nonneg hSB_bd.1
  have hS_cast : (⟨(S.a.toNat : ℤ), (S.b.toNat : ℤ)⟩ : Z3) = S := by
   rcases S with ⟨sa, sb⟩;simp only at hSA_bd hSB_bd
   exact congrArg₂ Z3.mk (Int.toNat_of_nonneg hSA_bd.1) (Int.toNat_of_nonneg hSB_bd.1)
  rw [← hS_cast]
  exact ji (by exact_mod_cast (by omega : (S.a.toNat : ℤ) < 15))
   (by exact_mod_cast (by omega : (S.b.toNat : ℤ) < 9))
   (by rw [hS_cast];exact hb1) (by rw [hS_cast];exact hb2) (by rw [hS_cast];exact hb3)
 have hstep1 : v ∈ jk S v.v0 :=
  List.mem_flatMap.2 ⟨diff, hmem_sq, hdiff_mem⟩
 have hstep2 : v ∈ jl S :=
  List.mem_flatMap.2 ⟨v.v0, hw0_mem, hstep1⟩
 exact List.mem_flatMap.2 ⟨S, hS_mem, hstep2⟩
lemma Z3.eq_one_of_toReal_eq_one {x : Z3} (hx : x.t0 = 1) : x = Z3.one := by
 have h3 : Y 3 ^ 2 = 3 := qc
 have hsq : (1 - x.a) ^ 2 = 3 * x.b ^ 2 := by
  have hR : ((1 - x.a : ℤ) : X) ^ 2 = ((3 * x.b ^ 2 : ℤ) : X) := by
   push_cast
   have h1 : (x.b : X) * Y 3 = 1 - (x.a : X) := by dsimp [Z3.t0] at hx;linarith
   calc (1 - (x.a : X)) ^ 2 = ((x.b : X) * Y 3) ^ 2 := by rw [h1]
     _ = 3 * (x.b : X) ^ 2 := by nlinarith only [h3]
  exact_mod_cast hR
 have hb0 : x.b = 0 := by
  have hnat : ∀ n m : ℕ, m ^ 2 = 3 * n ^ 2 → n = 0 := by
   intro n
   induction n using Nat.strong_induction_on with
   | _ n ih =>
    intro m hm
    by_cases hn : n = 0
    · exact hn
    ·
     have hm3 : 3 ∣ m := by
      have hd : (m % 3) ^ 2 % 3 = 0 := by
       have : m ^ 2 % 3 = 0 := by omega
       simpa [Nat.pow_mod] using this
      have hlt : m % 3 < 3 := Nat.mod_lt _ (Nat.zero_lt_succ 2)
      interval_cases hmod : m % 3
      · exact Nat.dvd_of_mod_eq_zero hmod
      · simp only [one_pow,Nat.one_mod,one_ne_zero] at hd
      · simp only [Nat.reducePow,Nat.reduceMod,one_ne_zero] at hd
     obtain ⟨m', rfl⟩ := hm3
     have hn3 : 3 ∣ n := by
      have hm' : 3 * m' ^ 2 = n ^ 2 := by linarith
      have hd : (n % 3) ^ 2 % 3 = 0 := by
       have : n ^ 2 % 3 = 0 := by omega
       simpa [Nat.pow_mod] using this
      have hlt : n % 3 < 3 := Nat.mod_lt _ (Nat.zero_lt_succ 2)
      interval_cases hmod : n % 3
      · exact Nat.dvd_of_mod_eq_zero hmod
      · simp only [one_pow,Nat.one_mod,one_ne_zero] at hd
      · simp only [Nat.reducePow,Nat.reduceMod,one_ne_zero] at hd
     obtain ⟨n', rfl⟩ := hn3
     have hlt : n' < 3 * n' := by omega
     have hm'2 : m' ^ 2 = 3 * n' ^ 2 := by linarith
     have hn'0 := ih n' hlt m' hm'2;omega
  have hnat_sq : (1 - x.a).natAbs ^ 2 = 3 * x.b.natAbs ^ 2 := by
   have : ((1 - x.a).natAbs ^ 2 : ℤ) = (3 * x.b.natAbs ^ 2 : ℤ) := by simpa [Int.natAbs_sq] using hsq
   exact_mod_cast this
  have := hnat x.b.natAbs (1 - x.a).natAbs hnat_sq;omega
 have ha1 : x.a = 1 := by
  rw [hb0] at hsq;nlinarith only [hsq]
 rcases x with ⟨xa, xb⟩
 simp only at ha1 hb0;subst ha1 hb0;rfl
lemma Z3.toReal_inj {x y : Z3} (h : x.t0 = y.t0) : x = y := by
 have h1 : (Z3.add (Z3.sub x y) Z3.one).t0 = 1 := by rw [Z3.po, Z3.pp, Z3.pm, h];ring
 have heq := Z3.eq_one_of_toReal_eq_one h1
 rcases x with ⟨xa, xb⟩;rcases y with ⟨ya, yb⟩
 simp only [Z3.add,Z3.sub,Z3.one,Z3.mk.injEq] at heq
 exact congrArg₂ Z3.mk (by omega) (by omega)
lemma jJ {w₁ w₂ : List (Fin 3)}
  (heq : (pX w₁).pP = (pX w₂).pP) :
  ∀ z ∈ ball (0 : Z) 1, jr w₁ z = jr w₂ z := by
 intro z hz;let u := w₂.reverse ++ w₁
 have hu_apply : (pX u).pP = V3.pG := by
  have hev : jr u 0 = 0 := by
   simp only [u,jt]
   have h0 : jr w₁ 0 = jr w₂ 0 := by
    apply jD (jv w₁ (mem_ball_self one_pos))
     (jv w₂ (mem_ball_self one_pos))
    funext r
    rw [jA, jA, heq]
   rw [h0, jw w₂ (mem_ball_self one_pos)]
  have hΦ_ones : ∀ r : Fin 3, (pX u).pP.get r = Z3.one := by
   intro r;apply Z3.eq_one_of_toReal_eq_one
   rw [← jA u r, hev, q7 r]
  have h0 := hΦ_ones 0;have h1 := hΦ_ones 1;have h2 := hΦ_ones 2
  rcases hv : (pX u).pP with ⟨a0, a1, a2⟩
  rw [hv] at h0 h1 h2;simp only [V3.get] at h0 h1 h2;rw [h0, h1, h2];rfl
 have hu_id : pX u = M3.id := p7 u hu_apply
 have huz : jr u z = z := by
  apply jD (jv u hz) hz
  funext r
  rw [jz u hz r, hu_id]
  fin_cases r <;> simp only [M3.get,V3.get,M3.row,M3.id,Z3.pm,Fin.isValue,one_mul,Z3.pl,zero_mul,add_zero,Fin.zero_eta,zero_add,Fin.mk_one,Fin.reduceFinMk]
 have hz' : jr u z = jr w₂.reverse (jr w₁ z) := by simp only [jt,u]
 rw [hz'] at huz;have hres := congr_arg (jr w₂) huz
 have hcanc : jr w₂ (jr w₂.reverse (jr w₁ z)) = jr w₁ z := by
  have hr := jw w₂.reverse (jv w₁ hz);simpa [List.reverse_reverse] using hr
 rw [hcanc] at hres;exact hres
lemma jK (w : List (Fin 3))
  (hS : Φ (jr w 0) 0 + Φ (jr w 0) 1 + Φ (jr w 0) 2 ≤ 25) :
  ∃ w₀ ∈ jn, ∀ z ∈ ball (0 : Z) 1, jr w z = jr w₀ z := by
 have hSr : (pX w).pP.sum.t0 ≤ 25 := by
  simp only [V3.sum,Z3.po]
  change ((pX w).pP.get 0).t0 +
    (((pX w).pP.get 1).t0 + ((pX w).pP.get 2).t0) ≤ 25
  rw [← jA w 0, ← jA w 1, ← jA w 2];linarith
 have hmem := jI w hSr;have hall := jq;rw [List.all_eq_true] at hall;have hAny := hall _ hmem;rw [List.any_eq_true] at hAny;obtain ⟨w₀, hw₀, heq⟩ := hAny;simp only [beq_iff_eq] at heq;exact ⟨w₀, hw₀, jJ heq.symm⟩
def jL (z : Z) : X := (1 + W z) / (1 - W z)
lemma jM {z : Z} (hz : z ∈ ball (0 : Z) 1) : 1 ≤ jL z := by
 have h1 : 0 < 1 - W z := sub_pos.2 (qm hz);have hns : 0 ≤ W z := normSq_nonneg z;dsimp [jL];rw [le_div_iff₀ h1];linarith
lemma jN {z w : Z} (hz : z ∈ ball (0 : Z) 1) (hw : w ∈ ball (0 : Z) 1)
  (hle : W z ≤ W w) : jL z ≤ jL w := by
 have hz1 : 0 < 1 - W z := sub_pos.2 (qm hz);have hw1 : 0 < 1 - W w := sub_pos.2 (qm hw);dsimp [jL];rw [div_le_div_iff₀ hz1 hw1];nlinarith only [hle]
lemma jO {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  jL z = (Φ z 0 + Φ z 1 + Φ z 2) / 3 :=
 (q9 hz).symm
def jP : X := (1 + σ ^ 2) / (1 - σ ^ 2)
lemma jQ : jP = 1 + 2 * Y 3 / 3 := by
 dsimp [jP];rw [qo];have h3 : Y 3 ^ 2 = 3 := qc
 have hne : 3 - Y 3 ≠ 0 := by nlinarith only [h3]
 have hnum : 1 + (Y 3 - 1) / 2 = (1 + Y 3) / 2 := by ring
 have hden : 1 - (Y 3 - 1) / 2 = (3 - Y 3) / 2 := by ring
 rw [hnum, hden, div_div_div_cancel_right₀ two_ne_zero];field_simp [hne];linear_combination 2 * h3
lemma jR : 1 ≤ jP := by rw [jQ];have : 0 < Y 3 := qd;linarith
lemma jS : 3 * (2 * jP ^ 2 - 1) ≤ 25 := by
 rw [jQ];have h3 : Y 3 ^ 2 = 3 := qc
 have h3le : Y 3 ≤ 7 / 4 := by rw [Real.sqrt_le_left (by norm_num)];norm_num
 have hid : 3 * (2 * (1 + 2 * Y 3 / 3) ^ 2 - 1) = 11 + 8 * Y 3 := by ring_nf;rw [h3];ring
 rw [hid];linarith
lemma jT {x : Z} (hx : x ∈ T0) : ‖x‖ ≤ σ := by
 have hx1 : ‖x‖ < 1 := by simpa [mem_ball, dist_zero_right] using hx.1
 have h3 : Y 3 ^ 2 = 3 := qc;let u0 : X := (x * T (qy 0)).re;let u1 : X := (x * T (qy 1)).re;let u2 : X := (x * T (qy 2)).re
 have hu0 : u0 = -x.re := by simp only [mul_re,Fin.isValue,conj_re,qB,mul_neg,mul_one,conj_im,qC,neg_zero,mul_zero,sub_zero,u0]
 have hu1 : u1 = x.re / 2 + x.im * (Y 3 / 2) := by
  simp only [u1,mul_re,conj_re,conj_im,qD,qE];ring
 have hu2 : u2 = x.re / 2 - x.im * (Y 3 / 2) := by
  simp only [u2,mul_re,conj_re,conj_im,qF,qG];ring
 have hsum : u0 + u1 + u2 = 0 := by rw [hu0, hu1, hu2];ring
 have hsq : u0 ^ 2 + u1 ^ 2 + u2 ^ 2 = 3 / 2 * W x := by
  rw [hu0, hu1, hu2, normSq_apply];linear_combination (x.im ^ 2 / 2) * h3
 let m : X := max u0 (max u1 u2);have hm0 : u0 ≤ m := le_max_left _ _;have hm1 : u1 ≤ m := le_trans (le_max_left _ _) (le_max_right _ _);have hm2 : u2 ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
 have hquad : 0 ≤ (m - u0) * (m - u1) + (m - u1) * (m - u2) + (m - u2) * (m - u0) := by nlinarith only [sub_nonneg.2 hm0, sub_nonneg.2 hm1, sub_nonneg.2 hm2]
 have hnorm_le_2m : ‖x‖ ^ 2 ≤ 4 * m ^ 2 := by
  rw [Complex.sq_norm]
  have hsum2 : (u0 + u1 + u2) ^ 2 = 0 := by rw [hsum];exact zero_pow two_ne_zero
  have he1 : (u0 + u1 + u2) ^ 2 = u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + 2 * (u0 * u1 + u1 * u2 + u2 * u0) := by ring
  have he2 : (m - u0) * (m - u1) + (m - u1) * (m - u2) + (m - u2) * (m - u0) =
    3 * m ^ 2 - 2 * m * (u0 + u1 + u2) + (u0 * u1 + u1 * u2 + u2 * u0) := by ring
  rw [hsum] at he2;linarith only [hsum2, he1, he2, hquad, hsq]
 have hm_nonneg : 0 ≤ m := by linarith only [hm0, hm1, hm2, hsum]
 have hx_le_2m : ‖x‖ ≤ 2 * m := by nlinarith only [norm_nonneg x, hm_nonneg, hnorm_le_2m]
 have hex : ∃ i : Fin 3, (x * T (qy i)).re = m := by
  rcases le_total u1 u2 with h12 | h21
  ·
   rcases le_total u0 u2 with h02 | h20
   ·
    refine ⟨2, ?_⟩
    change u2 = m;simp only [max_eq_right h12,max_eq_right h02,m]
   ·
    refine ⟨0, ?_⟩
    change u0 = m;simp only [max_eq_right h12,max_eq_left h20,m]
  ·
   rcases le_total u0 u1 with h01 | h10
   ·
    refine ⟨1, ?_⟩
    change u1 = m;simp only [max_eq_left h21,max_eq_right h01,m]
   ·
    refine ⟨0, ?_⟩
    change u0 = m;simp only [max_eq_left h21,max_eq_left h10,m]
 obtain ⟨i, hi⟩ := hex;have hside := hx.2 i
 have hns : W (x - qH i) =
   W x + tR ^ 2 - 2 * tR * (x * T (qy i)).re := by
  have hre : (x * T (qH i)).re = tR * (x * T (qy i)).re := by simp only [qH,map_mul,conj_ofReal,mul_re,ofReal_re,conj_re,ofReal_im,conj_im,mul_neg,zero_mul,neg_zero,sub_zero,mul_im,add_zero,sub_neg_eq_add];ring
  have hns0 : W (x - qH i) =
    W x + W (qH i) - 2 * (x * T (qH i)).re := by
   simp only [normSq_apply, sub_re, sub_im, mul_re,
    conj_re, conj_im];ring
  rw [hns0, qI, hre];ring
 rw [hns, hi] at hside
 have hpoly : 0 ≤ ‖x‖ ^ 2 - tR * ‖x‖ + 1 := by
  have : W x = ‖x‖ ^ 2 := (Complex.sq_norm x).symm;dsimp [R2] at hside;nlinarith only [qq, hx_le_2m, this, hside]
 have hfac : (σ - ‖x‖) * (1 / σ - ‖x‖) = ‖x‖ ^ 2 - tR * ‖x‖ + 1 := by dsimp [tR];field_simp [qn.ne'];ring
 have hinv_pos : 0 < 1 / σ - ‖x‖ := by
  have : 1 < 1 / σ := by rw [lt_div_iff₀ qn, one_mul];exact qp
  linarith
 nlinarith only [hpoly, hfac, hinv_pos]
lemma jU {x : Z} (hx : x ∈ T0) : jL x ≤ jP := by
 have hle : W x ≤ σ ^ 2 := by
  rw [← Complex.sq_norm]
  exact sq_le_sq' (by linarith [norm_nonneg x, qn]) (jT hx)
 have hσ1 : 0 < 1 - σ ^ 2 := sub_pos.2 (by nlinarith only [qn, qp])
 have hx1 : 0 < 1 - W x := sub_pos.2 (qm hx.1);dsimp [jL, jP];rw [div_le_div_iff₀ hx1 hσ1];nlinarith only [hle]
lemma jV {p z : Z} (hp : p ∈ ball (0 : Z) 1) (hz : z ∈ ball (0 : Z) 1)
  {M : X} (hM1 : 1 ≤ M) (hzM : jL z ≤ M) (hd : 1 + 2 * qR p z ≤ M) :
  jL p ≤ 2 * M ^ 2 - 1 := by
 by_cases huv : ‖p‖ ≤ ‖z‖
 ·
  have hns : W p ≤ W z := by
   rw [← Complex.sq_norm, ← Complex.sq_norm]
   exact sq_le_sq' (by linarith [norm_nonneg p, norm_nonneg z]) huv
  have h1 : jL p ≤ M := (jN hp hz hns).trans hzM;nlinarith only [hM1, h1]
 ·
  push Not at huv;set u := ‖p‖;set v := ‖z‖;have hu0 : 0 ≤ u := norm_nonneg p;have hv0 : 0 ≤ v := norm_nonneg z
  have hu1 : u < 1 := by simpa [u, mem_ball, dist_zero_right] using hp
  have hv1 : v < 1 := by simpa [v, mem_ball, dist_zero_right] using hz
  have hpu : W p = u ^ 2 := (Complex.sq_norm p).symm;have hzv : W z = v ^ 2 := (Complex.sq_norm z).symm
  have h1u2 : 0 < 1 - u ^ 2 := by nlinarith only [hu0, hu1]
  have h1v2 : 0 < 1 - v ^ 2 := by nlinarith only [hv0, hv1]
  have hden_pos : 0 < (1 - u ^ 2) * (1 - v ^ 2) := mul_pos h1u2 h1v2;let Dmin : X := ((1 + u ^ 2) * (1 + v ^ 2) - 4 * u * v) / ((1 - u ^ 2) * (1 - v ^ 2))
  have hDmin_ge_1 : 1 ≤ Dmin := by dsimp [Dmin];rw [le_div_iff₀ hden_pos];nlinarith only [sq_nonneg (u - v)]
  have hDmin_le_hd : Dmin ≤ 1 + 2 * qR p z := by
   have hsub_norm : (u - v) ^ 2 ≤ W (p - z) := by
    rw [← Complex.sq_norm (p - z)];have h1 : |u - v| ≤ ‖p - z‖ := abs_norm_sub_norm_le p z;rw [← sq_abs (u - v)]
    exact sq_le_sq' (by linarith [abs_nonneg (u - v)]) h1
   have h1 : 1 + 2 * qR p z =
     ((1 - u ^ 2) * (1 - v ^ 2) + 2 * W (p - z)) / ((1 - u ^ 2) * (1 - v ^ 2)) := by
    dsimp [qR];rw [hpu, hzv];field_simp [hden_pos.ne']
   rw [h1];dsimp [Dmin];rw [div_le_div_iff₀ hden_pos hden_pos];nlinarith only [hsub_norm, hden_pos]
  have hDmin_le_M : Dmin ≤ M := hDmin_le_hd.trans hd
  have hdiff_nn : 0 ≤ jL p - jL z * Dmin := by
   dsimp [jL, Dmin];rw [hpu, hzv]
   have hnum : (1 + u ^ 2) / (1 - u ^ 2) -
     (1 + v ^ 2) / (1 - v ^ 2) * (((1 + u ^ 2) * (1 + v ^ 2) - 4 * u * v) / ((1 - u ^ 2) * (1 - v ^ 2))) =
     4 * v * (u - v) * (1 - u * v) / ((1 - u ^ 2) * (1 - v ^ 2) ^ 2) := by
    field_simp [h1u2.ne', h1v2.ne'];ring
   rw [hnum]
   have h1uv : 0 < 1 - u * v := by nlinarith only [hu0, hu1, hv0, hv1]
   have hnum_nn : 0 ≤ 4 * v * (u - v) * (1 - u * v) := by positivity [hv0, sub_pos.2 huv, h1uv]
   exact div_nonneg hnum_nn (mul_nonneg h1u2.le (sq_nonneg (1 - v ^ 2)))
  have hdiff_sq : (jL p - jL z * Dmin) ^ 2 = (jL z ^ 2 - 1) * (Dmin ^ 2 - 1) := by
   dsimp [jL, Dmin];rw [hpu, hzv];field_simp [h1u2.ne', h1v2.ne'];ring
  have hcz_ge_1 : 1 ≤ jL z := jM hz
  have hM2_nn : 0 ≤ M ^ 2 - 1 := by nlinarith only [hM1]
  have hsq_le : (jL p - jL z * Dmin) ^ 2 ≤ (M ^ 2 - 1) ^ 2 := by
   rw [hdiff_sq]
   have h1 : 0 ≤ jL z ^ 2 - 1 := by nlinarith only [hcz_ge_1]
   have h2 : jL z ^ 2 - 1 ≤ M ^ 2 - 1 := by nlinarith only [hcz_ge_1, hzM]
   have h3 : 0 ≤ Dmin ^ 2 - 1 := by nlinarith only [hDmin_ge_1]
   have h4 : Dmin ^ 2 - 1 ≤ M ^ 2 - 1 := by nlinarith only [hDmin_ge_1, hDmin_le_M]
   calc (jL z ^ 2 - 1) * (Dmin ^ 2 - 1)
       ≤ (M ^ 2 - 1) * (Dmin ^ 2 - 1) := mul_le_mul_of_nonneg_right h2 h3
     _ ≤ (M ^ 2 - 1) * (M ^ 2 - 1) := mul_le_mul_of_nonneg_left h4 hM2_nn
     _ = (M ^ 2 - 1) ^ 2 := (sq _).symm
  have hdiff_le : jL p - jL z * Dmin ≤ M ^ 2 - 1 :=
   (sq_le_sq₀ hdiff_nn hM2_nn).1 hsq_le
  have hprod_le : jL z * Dmin ≤ M ^ 2 :=
   (mul_le_mul hzM hDmin_le_M (by linarith only [hDmin_ge_1]) (by linarith only [hM1])).trans_eq (sq M).symm
  linarith only [hdiff_le, hprod_le]
lemma jW {w : List (Fin 3)} {z x : Z}
  (hz : z ∈ T0) (hx : x ∈ T0) (heq : jr w z = x) :
  ∃ w₀ ∈ jn, ∀ u ∈ ball (0 : Z) 1, jr w u = jr w₀ u := by
 have hp : jr w 0 ∈ ball (0 : Z) 1 := jv w (mem_ball_self one_pos)
 have hdelta : 1 + 2 * qR (jr w 0) x = jL z := by
  rw [← heq, jy w (mem_ball_self one_pos) hz.1];dsimp [qR, jL];simp only [zero_sub,normSq_neg,normSq_zero,sub_zero,one_mul];have hz1 : 1 - W z ≠ 0 := (sub_pos.2 (qm hz.1)).ne';field_simp [hz1];ring
 have hcosh_x : jL x ≤ jP := jU hx;have hcosh_z : jL z ≤ jP := jU hz;have hd_le : 1 + 2 * qR (jr w 0) x ≤ jP := hdelta ▸ hcosh_z
 have hp_le : jL (jr w 0) ≤ 2 * jP ^ 2 - 1 :=
  jV hp hx.1 jR hcosh_x hd_le
 have hΦ_le : Φ (jr w 0) 0 + Φ (jr w 0) 1 + Φ (jr w 0) 2 ≤ 25 := by
  have h1 : (Φ (jr w 0) 0 + Φ (jr w 0) 1 + Φ (jr w 0) 2) / 3 = jL (jr w 0) :=
   (jO hp).symm
  linarith [jS]
 exact jK w hΦ_le
def jX (K : ℕ) : Finset Z3 :=
 ((Finset.Icc (-(K : ℤ)) (K : ℤ)) ×ˢ (Finset.Icc (-(K : ℤ)) (K : ℤ))).image
  fun p => ⟨p.1, p.2⟩
def jY (K : ℕ) : Finset V3 :=
 ((jX K) ×ˢ ((jX K) ×ˢ (jX K))).image
  fun t => ⟨t.1, t.2.1, t.2.2⟩
lemma jZ {x : Z3} {B : X} (K : ℕ)
  (hK : (3 * max B 0 + 8) / 2 ≤ (K : X))
  (hx0 : 0 < x.t0) (hxB : x.t0 ≤ 3 * max B 0)
  (hxc : (-8 : X) ≤ x.pj ∧ x.pj ≤ 8) :
  x ∈ jX K := by
 have hrt : (1 : X) ≤ Y 3 := qe.le
 have ha : (2 : X) * x.a = x.t0 + x.pj := by simp only [Z3.t0,Z3.pj,add_add_sub_cancel];ring
 have hb : (2 : X) * x.b * Y 3 = x.t0 - x.pj := by simp only [Z3.t0,Z3.pj,add_sub_sub_cancel];ring
 have ha_abs : |(x.a : X)| ≤ (K : X) := by rw [abs_le];constructor <;> linarith [hx0, hxB, hxc.1, hxc.2, ha, hK]
 have hb_abs : |(x.b : X)| ≤ (K : X) := by
  have hbmul : |(x.b : X)| * Y 3 ≤ (K : X) := by
   have h1 : |(2 : X) * x.b * Y 3| ≤ 3 * max B 0 + 8 := by rw [hb, abs_le];constructor <;> linarith [hx0, hxB, hxc.1, hxc.2]
   have h3p : (0 : X) < Y 3 := qd;rw [abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos h3p] at h1;linarith
  have hK0 : 0 ≤ (K : X) := Nat.cast_nonneg K;nlinarith only [hrt, abs_nonneg (x.b : X), hbmul, hK0]
 have ha_int : -(K : ℤ) ≤ x.a ∧ x.a ≤ (K : ℤ) := by rw [abs_le] at ha_abs;exact ⟨by exact_mod_cast ha_abs.1, by exact_mod_cast ha_abs.2⟩
 have hb_int : -(K : ℤ) ≤ x.b ∧ x.b ≤ (K : ℤ) := by rw [abs_le] at hb_abs;exact ⟨by exact_mod_cast hb_abs.1, by exact_mod_cast hb_abs.2⟩
 dsimp [jX];rw [Finset.mem_image]
 refine ⟨(x.a, x.b), Finset.mem_product.2 ⟨Finset.mem_Icc.2 ha_int, Finset.mem_Icc.2 hb_int⟩, ?_⟩
 cases x;rfl
lemma j1 (B : X) :
  ∃ F : Finset (List (Fin 3)), ∀ w : List (Fin 3),
   jL (jr w 0) ≤ B → ∃ w₀ ∈ F, ∀ z ∈ ball (0 : Z) 1, jr w z = jr w₀ z := by
 classical
 let K : ℕ := Nat.ceil ((3 * max B 0 + 8) / 2) + 1
 have hK : (3 * max B 0 + 8) / 2 ≤ (K : X) :=
  (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
 let pick : V3 → List (Fin 3) := fun v =>
  if h : ∃ w : List (Fin 3), (pX w).pP = v then h.choose else []
 refine ⟨(jY K).image pick, fun w hw => ?_⟩
 have hp : jr w 0 ∈ ball (0 : Z) 1 := jv w (mem_ball_self one_pos)
 have hΦ_sum : Φ (jr w 0) 0 + Φ (jr w 0) 1 + Φ (jr w 0) 2 ≤ 3 * max B 0 := by
  have h1 : (Φ (jr w 0) 0 + Φ (jr w 0) 1 + Φ (jr w 0) 2) / 3 = jL (jr w 0) :=
   (jO hp).symm
  linarith [le_max_left B 0]
 have hv_mem : ∀ r : Fin 3, ((pX w).pP.get r) ∈ jX K := by
  intro r
  have hpos : 0 < ((pX w).pP.get r).t0 := by rw [← jA w r];exact jC hp r
  have hle : ((pX w).pP.get r).t0 ≤ 3 * max B 0 := by
   have h0 : 0 < Φ (jr w 0) 0 := jC hp 0;have h1 : 0 < Φ (jr w 0) 1 := jC hp 1;have h2 : 0 < Φ (jr w 0) 2 := jC hp 2;rw [← jA w r]
   fin_cases r <;> dsimp <;> linarith
  have hc := jE (pX w).pP (p3 w)
  have hcr : (-8 : X) ≤ ((pX w).pP.get r).pj ∧
    ((pX w).pP.get r).pj ≤ 8 := by
   have hsq : ((pX w).pP.get r).pj ^ 2 ≤ 64 := by
    fin_cases r
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2
   exact abs_le.1 (by nlinarith only [sq_abs ((pX w).pP.get r).pj, hsq])
  exact jZ K hK hpos hle hcr
 have hbox : (pX w).pP ∈ jY K := by
  dsimp [jY];rw [Finset.mem_image]
  refine ⟨((pX w).pP.v0, ((pX w).pP.v1, (pX w).pP.v2)), ?_, ?_⟩
  · exact Finset.mem_product.2 ⟨hv_mem 0, Finset.mem_product.2 ⟨hv_mem 1, hv_mem 2⟩⟩
  · cases (pX w).pP;rfl
 refine ⟨pick (pX w).pP, Finset.mem_image_of_mem pick hbox, ?_⟩
 have hex : ∃ w' : List (Fin 3), (pX w').pP = (pX w).pP := ⟨w, rfl⟩
 have hpick : (pX (pick (pX w).pP)).pP = (pX w).pP := by dsimp [pick];rw [dif_pos hex];exact hex.choose_spec
 exact jJ hpick.symm
lemma j2 (z : Z) (hz : z ∈ ball (0 : Z) 1) :
  ∃ w : List (Fin 3), jr w z ∈ T0 := by
 let B : X := 2 * (jL z) ^ 2 - 1;obtain ⟨F, hF⟩ := j1 B;let S : Finset (List (Fin 3)) := F.filter fun w => W (jr w z) ≤ W z
 have h0_bound : jL (jr [] 0) ≤ B := by
  have hz1 : 1 ≤ jL z := jM hz
  have h0 : jL (jr [] 0) = 1 := by simp only [jL,jr,map_zero,add_zero,sub_zero,ne_eq,one_ne_zero,not_false_eq_true,div_self]
  rw [h0];nlinarith only [hz1]
 have hS_ne : S.Nonempty := by
  obtain ⟨w0, hw0, heq⟩ := hF [] h0_bound
  refine ⟨w0, Finset.mem_filter.2 ⟨hw0, ?_⟩⟩
  rw [← heq z hz];simp only [jr,Std.le_refl]
 obtain ⟨w_min, hw_min, hmin⟩ := S.exists_min_image (fun w => W (jr w z)) hS_ne;have hw_min_F : w_min ∈ F := (Finset.mem_filter.1 hw_min).1;have hw_min_le : W (jr w_min z) ≤ W z := (Finset.mem_filter.1 hw_min).2
 refine ⟨w_min, jv w_min hz, fun i => ?_⟩
 by_contra hlt
 push Not at hlt;have hmem := jv w_min hz
 have hlt_ns : W (qL i (jr w_min z)) < W (jr w_min z) := by
  by_contra hge
  push Not at hge;exact absurd ((qT hmem).1 hge) hlt.not_ge
 let w' := i :: w_min
 have hw'_ns : W (jr w' z) < W (jr w_min z) := by simpa [w', jr] using hlt_ns
 have hw'_le : W (jr w' z) ≤ W z := hw'_ns.le.trans hw_min_le;have hw'_mem := jv w' hz;have hcosh_w' : jL (jr w' z) ≤ jL z := jN hw'_mem hz hw'_le
 have hdelta_w' : 1 + 2 * qR (jr w' 0) (jr w' z) = jL z := by
  rw [jy w' (mem_ball_self one_pos) hz];dsimp [qR, jL];simp only [zero_sub,normSq_neg,normSq_zero,sub_zero,one_mul];have hz1 : 1 - W z ≠ 0 := (sub_pos.2 (qm hz)).ne';field_simp [hz1];ring
 have hcosh_w'0 : jL (jr w' 0) ≤ B :=
  jV (jv w' (mem_ball_self one_pos)) hw'_mem
   (jM hz) hcosh_w' (hdelta_w'.le)
 obtain ⟨w0, hw0, heq⟩ := hF w' hcosh_w'0
 have hw0_S : w0 ∈ S := Finset.mem_filter.2 ⟨hw0, by rw [← heq z hz];exact hw'_le⟩
 have hle_min := hmin w0 hw0_S;rw [← heq z hz] at hle_min;linarith
lemma j3 {r : X} (hr0 : 0 ≤ r) (hr1 : r < 1) :
  ∃ F : Finset (List (Fin 3)), ∀ (w : List (Fin 3)) (x : Z),
   x ∈ T0 → ‖jr w x‖ ≤ r → ∃ w₀ ∈ F, ∀ z ∈ ball (0 : Z) 1, jr w z = jr w₀ z := by
 let M : X := max ((1 + r ^ 2) / (1 - r ^ 2)) jP;have hM1 : 1 ≤ M := jR.trans (le_max_right _ _);obtain ⟨F, hF⟩ := j1 (2 * M ^ 2 - 1)
 refine ⟨F, fun w x hx hwr => ?_⟩
 have hy : jr w x ∈ ball (0 : Z) 1 := jv w hx.1
 have hy_ns : W (jr w x) ≤ r ^ 2 := by
  rw [← Complex.sq_norm]
  exact sq_le_sq' (by linarith [norm_nonneg (jr w x), hr0]) hwr
 have hy_cosh : jL (jr w x) ≤ M := by
  have h1r : 0 < 1 - r ^ 2 := by nlinarith only [hr0, hr1]
  have hy1 : 0 < 1 - W (jr w x) := sub_pos.2 (qm hy)
  have hcle : jL (jr w x) ≤ (1 + r ^ 2) / (1 - r ^ 2) := by dsimp [jL];rw [div_le_div_iff₀ hy1 h1r];nlinarith only [hy_ns]
  exact hcle.trans (le_max_left _ _)
 have hdelta : 1 + 2 * qR (jr w 0) (jr w x) ≤ M := by
  rw [jy w (mem_ball_self one_pos) hx.1]
  have h1 : 1 + 2 * qR 0 x = jL x := by
   dsimp [qR, jL];simp only [zero_sub,normSq_neg,normSq_zero,sub_zero,one_mul];have hx1 : 1 - W x ≠ 0 := (sub_pos.2 (qm hx.1)).ne';field_simp [hx1];ring
  rw [h1];exact (jU hx).trans (le_max_right _ _)
 have h0_le : jL (jr w 0) ≤ 2 * M ^ 2 - 1 :=
  jV (jv w (mem_ball_self one_pos)) hy hM1 hy_cosh hdelta
 exact hF w h0_le
def j4 : Fin 3 → Z
 | 0 => 1
 | 1 => ω ^ 2
 | 2 => ω
def j5 (k : Fin 3) : Z := (σ : Z) * j4 k
lemma j6 (k : Fin 3) : W (j4 k) = 1 := by
 fin_cases k
 · simp only [j4,map_one]
 · simp only [j4,← Complex.sq_norm,norm_pow,qk,one_pow]
 · simp only [j4,← Complex.sq_norm,qk,one_pow]
lemma j7 (k : Fin 3) : j5 k ∈ ball (0 : Z) 1 := by
 rw [mem_ball, dist_zero_right, j5, norm_mul, Complex.norm_of_nonneg qn.le]
 have hnv : ‖j4 k‖ = 1 := by
  have : W (j4 k) = ‖j4 k‖ ^ 2 := (Complex.sq_norm _).symm;rw [j6] at this;nlinarith only [this, norm_nonneg (j4 k)]
 rw [hnv, mul_one];exact qp
lemma j8 (i k : Fin 3) (hik : i ≠ k) : qX i (j4 k) = j4 k := by
 fin_cases i <;> fin_cases k <;> try contradiction
 · simp only [qX,j4,qY];linear_combination -qi
 · simp only [qX,j4,ql];linear_combination -qi
 · simp only [qX,j4,map_one,mul_one];linear_combination -qi
 · simp only [qX,j4,ql];linear_combination -qj - qi
 · simp only [qX,j4,map_one,mul_one];linear_combination -qi
 · simp only [qX,j4,qY];linear_combination -qj - qi
lemma j9 (i k : Fin 3) :
  W (j5 k - qH i) =
   σ ^ 2 + tR ^ 2 - 2 * σ * tR * (j4 k * T (qy i)).re := by
 have hns : W (j5 k) = σ ^ 2 := by simp only [j5,normSq_mul,normSq_ofReal,j6,mul_one,sq]
 have hre : (j5 k * T (qH i)).re =
   σ * tR * (j4 k * T (qy i)).re := by
  rw [j5, qH, map_mul, conj_ofReal]
  simp only [mul_re, mul_im, conj_re, conj_im,
   ofReal_re, ofReal_im]
  ring
 have h0 : W (j5 k - qH i) =
   W (j5 k) + W (qH i) - 2 * (j5 k * T (qH i)).re := by
  simp only [normSq_apply, sub_re, sub_im, mul_re,
   conj_re, conj_im];ring
 rw [h0, hns, qI, hre];ring
lemma ka {i k : Fin 3} (hik : i ≠ k) :
  (j4 k * T (qy i)).re = 1 / 2 := by
 have h3 : Y 3 ^ 2 = 3 := qc
 fin_cases i <;> fin_cases k <;> try contradiction
 all_goals
  simp only [j4,ω,sq,qy,map_neg,map_one,mul_neg,mul_one,neg_re,mul_re,neg_sub,one_div,map_mul,one_mul,conj_re,conj_im,neg_mul,neg_neg,mul_im,sub_neg_eq_add,neg_add_rev]
  try nlinarith only [h3]
lemma kb {i k : Fin 3} (hik : i ≠ k) :
  W (j5 k - qH i) = R2 := by
 rw [j9, ka hik]
 have hst : σ * tR = σ ^ 2 + 1 := by dsimp [tR];field_simp [qn.ne']
 dsimp [R2];nlinarith only [hst]
lemma kc {i : Fin 3} {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  qL i z = z ↔ W (z - qH i) = R2 := by
 have hden := qM (i := i) hz
 have hconj : W (T z - T (qH i)) =
   W (z - qH i) := by rw [← map_sub, normSq_conj]
 have hr_sub : qL i z - qH i =
   (R2 : Z) / (T z - T (qH i)) := by
  have hr0 : qL i z - qH i =
    (qH i * T z - 1 - qH i * (T z - T (qH i))) /
     (T z - T (qH i)) := by
   dsimp [qL];field_simp [hden]
  have hnum : qH i * T z - 1 - qH i * (T z - T (qH i)) =
    (R2 : Z) := by
   have hcs : qH i * T (qH i) = (tR ^ 2 : Z) := by
    have := qI i;rw [← ofReal_inj] at this;simpa [mul_conj] using this
   dsimp [R2];push_cast;linear_combination hcs
  rw [hr0, hnum]
 constructor
 ·
  intro h;have hmul := congr_arg (fun w => w * (T z - T (qH i))) hr_sub;rw [h, div_mul_cancel₀ _ hden] at hmul
  have hns : (z - qH i) * T (z - qH i) = (R2 : Z) := by simpa [map_sub] using hmul
  rw [mul_conj] at hns;exact_mod_cast hns
 ·
  intro h
  have hmul : (z - qH i) * (T z - T (qH i)) = (R2 : Z) := by rw [← map_sub, mul_conj, h]
  have heq : qL i z - qH i = z - qH i := by rw [hr_sub, div_eq_iff hden, hmul]
  linear_combination heq
lemma kd {i k : Fin 3} (hik : i ≠ k) : qL i (j5 k) = j5 k :=
 (kc (j7 k)).2 (kb hik)
lemma ke {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
  {x : Z} (hx : x ∈ T0)
  (hi : W (x - qH i) = R2) (hj : W (x - qH j) = R2) :
  x = j5 k := by
 have h1 : W (x - qH i) = W x + tR ^ 2 - 2 * tR * (x * T (qy i)).re := by
  have hre : (x * T (qH i)).re = tR * (x * T (qy i)).re := by
   rw [qH, map_mul, conj_ofReal]
   simp only [mul_re, mul_im, conj_re, conj_im,
    ofReal_re, ofReal_im];ring
  have h0 : W (x - qH i) =
    W x + W (qH i) - 2 * (x * T (qH i)).re := by
   simp only [normSq_apply, sub_re, sub_im, mul_re,
    conj_re, conj_im];ring
  rw [h0, qI, hre];ring
 have h2 : W (x - qH j) = W x + tR ^ 2 - 2 * tR * (x * T (qy j)).re := by
  have hre : (x * T (qH j)).re = tR * (x * T (qy j)).re := by
   rw [qH, map_mul, conj_ofReal]
   simp only [mul_re, mul_im, conj_re, conj_im,
    ofReal_re, ofReal_im];ring
  have h0 : W (x - qH j) =
    W x + W (qH j) - 2 * (x * T (qH j)).re := by
   simp only [normSq_apply, sub_re, sub_im, mul_re,
    conj_re, conj_im];ring
  rw [h0, qI, hre];ring
 have hre_eq : (x * T (qy i)).re = (x * T (qy j)).re := by
  have : tR * (x * T (qy i)).re = tR * (x * T (qy j)).re := by linarith [hi, hj, h1, h2]
  exact mul_left_cancel₀ qq.ne' this
 have h3 : Y 3 ^ 2 = 3 := qc;have h3p : (0 : X) < Y 3 := qd
 have hx_dir0 : (x * T (qy 0)).re = -x.re := by simp only [Fin.isValue,mul_re,conj_re,qB,mul_neg,mul_one,conj_im,qC,neg_zero,mul_zero,sub_zero]
 have hx_dir1 : (x * T (qy 1)).re = x.re / 2 + x.im * (Y 3 / 2) := by simp only [mul_re,conj_re,conj_im,qD,qE];ring
 have hx_dir2 : (x * T (qy 2)).re = x.re / 2 - x.im * (Y 3 / 2) := by simp only [mul_re,conj_re,conj_im,qF,qG];ring
 have h_dir : ∃ r : X, x = (r : Z) * j4 k ∧ 0 ≤ r := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  ·
   change (x * T (qy 0)).re = (x * T (qy 1)).re at hre_eq;rw [hx_dir0, hx_dir1] at hre_eq
   have him : x.im = -x.re * Y 3 := by linear_combination (-2 * Y 3 / 3) * hre_eq - (x.im / 3) * h3
   have hxre_le : x.re ≤ 0 := by
    have this := hi;change W (x - qH 0) = R2 at this
    have h1' : W (x - qH 0) =
      W x + tR ^ 2 - 2 * tR * (x * T (qy 0)).re := h1
    rw [h1', hx_dir0] at this;have hnsx0 : 0 ≤ W x := normSq_nonneg x;dsimp [R2] at this;nlinarith only [this, qq, hnsx0]
   refine ⟨-2 * x.re, ?_, by linarith⟩
   apply Complex.ext
   · simp only [neg_mul,ofReal_neg,ofReal_mul,ofReal_ofNat,j4,ω,neg_re,mul_re,re_ofNat,ofReal_re,im_ofNat,ofReal_im,mul_zero,sub_zero,mul_im,zero_mul,add_zero];ring
   · simp only [neg_mul,ofReal_neg,ofReal_mul,ofReal_ofNat,j4,ω,neg_im,mul_im,mul_re,re_ofNat,ofReal_re,im_ofNat,ofReal_im,mul_zero,sub_zero,zero_mul,add_zero];linarith
  ·
   change (x * T (qy 0)).re = (x * T (qy 2)).re at hre_eq;rw [hx_dir0, hx_dir2] at hre_eq
   have him : x.im = x.re * Y 3 := by linear_combination (2 * Y 3 / 3) * hre_eq - (x.im / 3) * h3
   have hxre_le : x.re ≤ 0 := by
    have this := hi;change W (x - qH 0) = R2 at this
    have h1' : W (x - qH 0) =
      W x + tR ^ 2 - 2 * tR * (x * T (qy 0)).re := h1
    rw [h1', hx_dir0] at this;have hnsx0 : 0 ≤ W x := normSq_nonneg x;dsimp [R2] at this;nlinarith only [this, qq, hnsx0]
   refine ⟨-2 * x.re, ?_, by linarith⟩
   apply Complex.ext
   · simp only [neg_mul,ofReal_neg,ofReal_mul,ofReal_ofNat,j4,ω,sq,neg_re,mul_re,re_ofNat,ofReal_re,im_ofNat,ofReal_im,mul_zero,sub_zero,mul_im,zero_mul,add_zero];nlinarith only [h3, hxre_le]
   · simp only [neg_mul,ofReal_neg,ofReal_mul,ofReal_ofNat,j4,ω,sq,neg_im,mul_im,mul_re,re_ofNat,ofReal_re,im_ofNat,ofReal_im,mul_zero,sub_zero,zero_mul,add_zero];linarith
  ·
   change (x * T (qy 1)).re = (x * T (qy 0)).re at hre_eq;rw [hx_dir1, hx_dir0] at hre_eq
   have him : x.im = -x.re * Y 3 := by linear_combination (2 * Y 3 / 3) * hre_eq - (x.im / 3) * h3
   have hxre_le : x.re ≤ 0 := by
    have this := hj;change W (x - qH 0) = R2 at this
    have h2' : W (x - qH 0) =
      W x + tR ^ 2 - 2 * tR * (x * T (qy 0)).re := h2
    rw [h2', hx_dir0] at this;have hnsx0 : 0 ≤ W x := normSq_nonneg x;dsimp [R2] at this;nlinarith only [this, qq, hnsx0]
   refine ⟨-2 * x.re, ?_, by linarith⟩
   apply Complex.ext
   · simp only [neg_mul,ofReal_neg,ofReal_mul,ofReal_ofNat,j4,ω,neg_re,mul_re,re_ofNat,ofReal_re,im_ofNat,ofReal_im,mul_zero,sub_zero,mul_im,zero_mul,add_zero];ring
   · simp only [neg_mul,ofReal_neg,ofReal_mul,ofReal_ofNat,j4,ω,neg_im,mul_im,mul_re,re_ofNat,ofReal_re,im_ofNat,ofReal_im,mul_zero,sub_zero,zero_mul,add_zero];linarith
  ·
   change (x * T (qy 1)).re = (x * T (qy 2)).re at hre_eq;rw [hx_dir1, hx_dir2] at hre_eq
   have him : x.im = 0 := by nlinarith only [h3p, hre_eq]
   have hxre_nn : 0 ≤ x.re := by
    have this := hi;change W (x - qH 1) = R2 at this
    have h1' : W (x - qH 1) =
      W x + tR ^ 2 - 2 * tR * (x * T (qy 1)).re := h1
    rw [h1', hx_dir1, him] at this;have hnsx0 : 0 ≤ W x := normSq_nonneg x;dsimp [R2] at this;nlinarith only [this, qq, hnsx0]
   refine ⟨x.re, ?_, hxre_nn⟩
   apply Complex.ext <;> simp only [j4,mul_one,ofReal_re,him,ofReal_im]
  ·
   change (x * T (qy 2)).re = (x * T (qy 0)).re at hre_eq;rw [hx_dir2, hx_dir0] at hre_eq
   have him : x.im = x.re * Y 3 := by linear_combination (-2 * Y 3 / 3) * hre_eq - (x.im / 3) * h3
   have hxre_le : x.re ≤ 0 := by
    have this := hj;change W (x - qH 0) = R2 at this
    have h2' : W (x - qH 0) =
      W x + tR ^ 2 - 2 * tR * (x * T (qy 0)).re := h2
    rw [h2', hx_dir0] at this;have hnsx0 : 0 ≤ W x := normSq_nonneg x;dsimp [R2] at this;nlinarith only [this, qq, hnsx0]
   refine ⟨-2 * x.re, ?_, by linarith⟩
   apply Complex.ext
   · simp only [neg_mul,ofReal_neg,ofReal_mul,ofReal_ofNat,j4,ω,sq,neg_re,mul_re,re_ofNat,ofReal_re,im_ofNat,ofReal_im,mul_zero,sub_zero,mul_im,zero_mul,add_zero];nlinarith only [h3, hxre_le]
   · simp only [neg_mul,ofReal_neg,ofReal_mul,ofReal_ofNat,j4,ω,sq,neg_im,mul_im,mul_re,re_ofNat,ofReal_re,im_ofNat,ofReal_im,mul_zero,sub_zero,zero_mul,add_zero];linarith
  ·
   change (x * T (qy 2)).re = (x * T (qy 1)).re at hre_eq;rw [hx_dir2, hx_dir1] at hre_eq
   have him : x.im = 0 := by nlinarith only [h3p, hre_eq]
   have hxre_nn : 0 ≤ x.re := by
    have this := hi;change W (x - qH 2) = R2 at this
    have h1' : W (x - qH 2) =
      W x + tR ^ 2 - 2 * tR * (x * T (qy 2)).re := h1
    rw [h1', hx_dir2, him] at this;have hnsx0 : 0 ≤ W x := normSq_nonneg x;dsimp [R2] at this;nlinarith only [this, qq, hnsx0]
   refine ⟨x.re, ?_, hxre_nn⟩
   apply Complex.ext <;> simp only [j4,mul_one,ofReal_re,him,ofReal_im]
 obtain ⟨r, rfl, hr0⟩ := h_dir
 have hns : W ((r : Z) * j4 k) = r ^ 2 := by simp only [normSq_mul,normSq_ofReal,j6,mul_one,sq]
 have hre_k : ((r : Z) * j4 k * T (qy i)).re = r / 2 := by
  have hmul : ((r : Z) * j4 k * T (qy i)).re =
    r * (j4 k * T (qy i)).re := by
   simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,conj_re,mul_im,add_zero,conj_im,mul_neg,sub_neg_eq_add];ring
  rw [hmul, ka hik];ring
 have hquad : r ^ 2 - tR * r + 1 = 0 := by
  have h0 : W ((r : Z) * j4 k - qH i) = R2 := hi
  have h0' : W ((r : Z) * j4 k - qH i) =
    W ((r : Z) * j4 k) + tR ^ 2 -
     2 * tR * ((r : Z) * j4 k * T (qy i)).re := by
   have hre : (((r : Z) * j4 k) * T (qH i)).re =
     tR * ((r : Z) * j4 k * T (qy i)).re := by
    rw [qH, map_mul, conj_ofReal]
    simp only [mul_re, mul_im, conj_re, conj_im,
     ofReal_re, ofReal_im];ring
   have hsub : W ((r : Z) * j4 k - qH i) =
     W ((r : Z) * j4 k) + W (qH i) -
      2 * (((r : Z) * j4 k) * T (qH i)).re := by
    simp only [normSq_apply, sub_re, sub_im, mul_re,
     conj_re, conj_im];ring
   rw [hsub, qI, hre];ring
  rw [h0', hns, hre_k] at h0;dsimp [R2] at h0;linarith
 have hfac : (r - σ) * (r - 1 / σ) = 0 := by
  have : (r - σ) * (r - 1 / σ) = r ^ 2 - tR * r + 1 := by dsimp [tR];field_simp [qn.ne'];ring
  linarith
 have hr1 : r < 1 := by
  have hx1 := qm hx.1;rw [hns] at hx1;nlinarith only [hx1, hr0]
 have hr_inv : r - 1 / σ ≠ 0 := by
  have : 1 < 1 / σ := by rw [lt_div_iff₀ qn, one_mul];exact qp
  linarith
 have hrσ : r = σ := sub_eq_zero.1 ((mul_eq_zero.1 hfac).resolve_right hr_inv);rw [hrσ];rfl
def kf (w : List (Fin 3)) : Bool :=
 let N := pY w;let rowAllNonpos (r : V3) := r.v0.pB && r.v1.pB && r.v2.pB;let rowAllLtZero (r : V3) := r.v0.l0 && r.v1.l0 && r.v2.l0;let rowZeroAt (r : V3) (k : Fin 3) := (r.get k) == Z3.zero
 if w == [] then true
 else if w.length == 1 then true
 else
  ([0, 1, 2] : List (Fin 3)).any (fun r => rowAllLtZero (N.row r)) ||
  ([(0, 1, 2), (0, 2, 1), (1, 2, 0)] : List (Fin 3 × Fin 3 × Fin 3)).any fun (i, j, k) =>
   w.all (fun a => a == i || a == j) &&
   (([0, 1, 2] : List (Fin 3)).any (fun r =>
    rowAllNonpos (N.row r) && ((N.row r).get i).l0 &&
     ((N.row r).get j).l0 && rowZeroAt (N.row r) k) ||
   (rowAllNonpos (N.row i) && ((N.row i).get i).l0 &&
    rowAllNonpos (N.row j) && ((N.row j).get j).l0))
lemma kg : jn.all kf = true := by decide
lemma kh : (jn.map (fun w => (pX w).pP)).Nodup = true := by rw [jp];decide
lemma ki {x : Z} (hx : x ∈ T0) (r : Fin 3) : q5 x r ≤ 0 := by
 dsimp [q5];have h1 : 0 ≤ W (x - qH r) - R2 := sub_nonneg.2 (hx.2 r);have hden : 0 < R2 * (1 - W x) := mul_pos qu (sub_pos.2 (qm hx.1))
 exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
lemma kj {x : Z} (hx : x ∈ T0) : q5 x 0 + q5 x 1 + q5 x 2 < 0 := by
 rw [q8 hx.1];have hden : 0 < R2 * (1 - W x) := mul_pos qu (sub_pos.2 (qm hx.1))
 have hnum : -9 * (1 + W x) < 0 := by linarith [normSq_nonneg x]
 exact div_neg_of_neg_of_pos hnum hden
lemma kk {w₀ : List (Fin 3)} (hw₀ : w₀ ∈ jn)
  {x : Z} (hx : x ∈ T0) (hwx : jr w₀ x ∈ T0) :
  jr w₀ x = x ∧
   (w₀ = [] ∨
    (∃ i : Fin 3, w₀ = [i] ∧ W (x - qH i) = R2) ∨
    (∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ x = j5 k ∧ ∀ a ∈ w₀, a = i ∨ a = j)) := by
 have hvalid : kf w₀ = true := List.all_eq_true.1 kg w₀ hw₀
 by_cases hnil : w₀ = []
 · subst hnil;exact ⟨rfl, Or.inl rfl⟩
 ·
  by_cases hlen1 : w₀.length = 1
  ·
   rcases w₀ with _ | ⟨i, _ | ⟨b, t⟩⟩
   · contradiction
   ·
    have hip_le : q5 (qL i x) i ≤ 0 := ki hwx i;rw [pb hx.1] at hip_le;have hx_le := ki hx i
    have hip0 : q5 x i = 0 := by linarith
    have hns : W (x - qH i) = R2 := by
     dsimp [q5] at hip0
     have hden : R2 * (1 - W x) ≠ 0 :=
      (mul_pos qu (sub_pos.2 (qm hx.1))).ne'
     have := (div_eq_zero_iff.1 hip0).resolve_right hden;linarith
    have hfix : qL i x = x := (kc hx.1).2 hns;exact ⟨hfix, Or.inr (Or.inl ⟨i, rfl, hns⟩)⟩
   · simp only [List.length_cons,Nat.add_eq_right,Nat.add_eq_zero_iff,List.length_eq_zero_iff,one_ne_zero,and_false] at hlen1
  ·
   have hlen1_false : (w₀.length == 1) = false := beq_false_of_ne hlen1;have hnil_false : (w₀ == []) = false := beq_false_of_ne hnil;unfold kf at hvalid;rw [hnil_false, hlen1_false] at hvalid;simp only [Bool.false_eq_true,↓reduceIte,Bool.or_eq_true] at hvalid
   rcases hvalid with hneg | hpair
   ·
    exfalso;rw [List.any_eq_true] at hneg;obtain ⟨r, _, hr⟩ := hneg;simp only [Bool.and_eq_true,Z3.pF] at hr;obtain ⟨⟨hc0, hc1⟩, hc2⟩ := hr;have hrow := jB w₀ hx.1 r;have hip_hwx : q5 (jr w₀ x) r ≤ 0 := ki hwx r;have h0 := ki hx 0;have h1 := ki hx 1;have h2 := ki hx 2;have hsum := kj hx;have hn0 : ((pY w₀).get r 0).t0 < 0 := hc0;have hn1 : ((pY w₀).get r 1).t0 < 0 := hc1;have hn2 : ((pY w₀).get r 2).t0 < 0 := hc2
    have hgt : 0 < ((pY w₀).get r 0).t0 * q5 x 0 + ((pY w₀).get r 1).t0 * q5 x 1 +
      ((pY w₀).get r 2).t0 * q5 x 2 := by
     have p0 : 0 ≤ ((pY w₀).get r 0).t0 * q5 x 0 := mul_nonneg_of_nonpos_of_nonpos hn0.le h0;have p1 : 0 ≤ ((pY w₀).get r 1).t0 * q5 x 1 := mul_nonneg_of_nonpos_of_nonpos hn1.le h1;have p2 : 0 ≤ ((pY w₀).get r 2).t0 * q5 x 2 := mul_nonneg_of_nonpos_of_nonpos hn2.le h2
     rcases lt_or_ge (q5 x 0) 0 with hx0 | hx0
     · linarith only [mul_pos_of_neg_of_neg hn0 hx0, p1, p2]
     ·
      rcases lt_or_ge (q5 x 1) 0 with hx1 | hx1
      · linarith only [p0, mul_pos_of_neg_of_neg hn1 hx1, p2]
      ·
       have hx2 : q5 x 2 < 0 := by linarith only [hsum, hx0, hx1]
       linarith only [p0, p1, mul_pos_of_neg_of_neg hn2 hx2]
    linarith
   ·
    rw [List.any_eq_true] at hpair;obtain ⟨⟨i, j, k⟩, hmem, hcond⟩ := hpair;simp only [Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hcond;obtain ⟨hletters, hsep⟩ := hcond
    have hij : i ≠ j ∧ i ≠ k ∧ j ≠ k := by
     simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hmem
     rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
    have hip_ij : q5 x i = 0 ∧ q5 x j = 0 := by
     rcases hsep with hr | hij_sep
     ·
      rw [List.any_eq_true] at hr;obtain ⟨r, _, hr⟩ := hr;simp only [Bool.and_eq_true,Z3.pE,Z3.pF,beq_iff_eq] at hr;obtain ⟨⟨⟨⟨⟨hn0, hn1⟩, hn2⟩, hni⟩, hnj⟩, _⟩ := hr;have hrow := jB w₀ hx.1 r;have hip_hwx : q5 (jr w₀ x) r ≤ 0 := ki hwx r;have h0 := ki hx 0;have h1 := ki hx 1;have h2 := ki hx 2
      have hn_all : ∀ c : Fin 3, ((pY w₀).get r c).t0 ≤ 0 := fun c => by
       fin_cases c <;> assumption
      have hi0 : 0 ≤ ((pY w₀).get r i).t0 * q5 x i :=
       mul_nonneg_of_nonpos_of_nonpos (hn_all i) (ki hx i)
      have hj0 : 0 ≤ ((pY w₀).get r j).t0 * q5 x j :=
       mul_nonneg_of_nonpos_of_nonpos (hn_all j) (ki hx j)
      have hk0 : 0 ≤ ((pY w₀).get r k).t0 * q5 x k :=
       mul_nonneg_of_nonpos_of_nonpos (hn_all k) (ki hx k)
      have hsum_eq : ((pY w₀).get r 0).t0 * q5 x 0 + ((pY w₀).get r 1).t0 * q5 x 1 +
        ((pY w₀).get r 2).t0 * q5 x 2 =
        ((pY w₀).get r i).t0 * q5 x i + ((pY w₀).get r j).t0 * q5 x j +
        ((pY w₀).get r k).t0 * q5 x k := by
       fin_cases i <;> fin_cases j <;> fin_cases k <;>
        first | exact absurd hij.1 (by decide) | exact absurd hij.2.1 (by decide) |
         exact absurd hij.2.2 (by decide) | (dsimp;all_goals ring)
      have hip_i_eq : ((pY w₀).get r i).t0 * q5 x i = 0 := by linarith
      have hip_j_eq : ((pY w₀).get r j).t0 * q5 x j = 0 := by linarith
      exact ⟨(mul_eq_zero.1 hip_i_eq).resolve_left hni.ne,
         (mul_eq_zero.1 hip_j_eq).resolve_left hnj.ne⟩
     ·
      simp only [Z3.pE,Z3.pF,and_assoc] at hij_sep;obtain ⟨hi0, hi1, hi2, hii, hj0, hj1, hj2, hjj⟩ := hij_sep
      have hdiag0 : ∀ r : Fin 3, ((pY w₀).row r).v0.t0 ≤ 0 →
        ((pY w₀).row r).v1.t0 ≤ 0 → ((pY w₀).row r).v2.t0 ≤ 0 →
        (((pY w₀).row r).get r).t0 < 0 → q5 x r = 0 := by
       intro r hr0 hr1 hr2 hrr;have hrow := jB w₀ hx.1 r;have hip_hwx : q5 (jr w₀ x) r ≤ 0 := ki hwx r;have h0 := ki hx 0;have h1 := ki hx 1;have h2 := ki hx 2
       have hle0 : ((pY w₀).get r r).t0 * q5 x r = 0 := by
        have hg0 : ((pY w₀).get r 0).t0 ≤ 0 := hr0;have hg1 : ((pY w₀).get r 1).t0 ≤ 0 := hr1;have hg2 : ((pY w₀).get r 2).t0 ≤ 0 := hr2;have hp0 : 0 ≤ ((pY w₀).get r 0).t0 * q5 x 0 := mul_nonneg_of_nonpos_of_nonpos hg0 h0;have hp1 : 0 ≤ ((pY w₀).get r 1).t0 * q5 x 1 := mul_nonneg_of_nonpos_of_nonpos hg1 h1;have hp2 : 0 ≤ ((pY w₀).get r 2).t0 * q5 x 2 := mul_nonneg_of_nonpos_of_nonpos hg2 h2
        fin_cases r <;> dsimp at * <;> linarith
       exact (mul_eq_zero.1 hle0).resolve_left hrr.ne
      exact ⟨hdiag0 i hi0 hi1 hi2 hii, hdiag0 j hj0 hj1 hj2 hjj⟩
    have hden : R2 * (1 - W x) ≠ 0 :=
     (mul_pos qu (sub_pos.2 (qm hx.1))).ne'
    have hnsi : W (x - qH i) = R2 := by
     have := hip_ij.1;dsimp [q5] at this;linarith [(div_eq_zero_iff.1 this).resolve_right hden]
    have hnsj : W (x - qH j) = R2 := by
     have := hip_ij.2;dsimp [q5] at this;linarith [(div_eq_zero_iff.1 this).resolve_right hden]
    have hxv : x = j5 k := ke hij.1 hij.2.1 hij.2.2 hx hnsi hnsj
    have hfix_w : ∀ w : List (Fin 3), (∀ a ∈ w, a = i ∨ a = j) → jr w (j5 k) = j5 k := by
     intro w hw
     induction w with
     | nil => rfl
     | cons a w ih =>
      simp only [jr];rw [ih (fun b hb => hw b (List.mem_cons_of_mem a hb))]
      rcases hw a List.mem_cons_self with rfl | rfl
      · exact kd hij.2.1
      · exact kd hij.2.2
    refine ⟨by rw [hxv];exact hfix_w w₀ hletters, Or.inr (Or.inr ⟨i, j, k, hij.1, hij.2.1, hij.2.2, hxv, hletters⟩)⟩
def kl (i j a : Fin 3) (st : Bool × Fin 6) : Bool × Fin 6 :=
 if a == i then (!st.1, st.2)
 else if a == j then (!st.1, if st.1 then st.2 - 1 else st.2 + 1)
 else st
def km (i j : Fin 3) : List (Fin 3) → Bool × Fin 6
 | [] => (false, 0)
 | a :: w => kl i j a (km i j w)
def kn (i j : Fin 3) (st : Bool × Fin 6) : List (Fin 3) :=
 let rot := List.flatten (List.replicate st.2.val [i, j])
 if st.1 then i :: rot else rot
def ko : List (Bool × Fin 6) :=
 ([false, true] : List Bool).flatMap fun s =>
  ([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun r => (s, r)
lemma kp :
  ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)).all
   (fun (i, j) => pX (List.flatten (List.replicate 6 [i, j])) == M3.id) = true := by
 decide
lemma kq :
  ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)).all
   (fun (i, j) => (ko.map (fun st => (pX (kn i j st)).pP)).Nodup) = true := by
 decide
lemma kr {i j : Fin 3} (hij : i < j) {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  jr (List.flatten (List.replicate 6 [i, j])) z = z := by
 have hmem : (i, j) ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)) := by fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | decide
 have hchk := List.all_eq_true.1 kp (i, j) hmem;simp only [beq_iff_eq] at hchk
 have happ : (pX (List.flatten (List.replicate 6 [i, j]))).pP = (pX []).pP := by rw [hchk];rfl
 exact jJ happ z hz
lemma ks {i j : Fin 3} (hij : i < j) (w : List (Fin 3))
  (hw : ∀ a ∈ w, a = i ∨ a = j) {z : Z} (hz : z ∈ ball (0 : Z) 1) :
  jr w z = jr (kn i j (km i j w)) z := by
 induction w with
 | nil => rfl
 | cons a w ih =>
  have hw' : ∀ b ∈ w, b = i ∨ b = j := fun b hb => hw b (List.mem_cons_of_mem a hb);have ihz := ih hw';change qL a (jr w z) = _;rw [ihz]
  have hpow6 : ∀ z' ∈ ball (0 : Z) 1,
    (fun x => qL i (qL j x))^[6] z' = z' := by
   intro z' hz';simpa [jr, List.replicate, List.flatten] using kr hij hz'
  have hiter : ∀ k : ℕ, ∀ z' ∈ ball (0 : Z) 1,
    jr (List.flatten (List.replicate k [i, j])) z' = (fun x => qL i (qL j x))^[k] z' := by
   intro k
   induction k with
   | zero => intro z' _;rfl
   | succ k ihk =>
    intro z' hz';rw [List.replicate_succ, List.flatten_cons, jt, ihk z' hz'];simp only [jr,Function.iterate_succ_apply']
  change _ = jr (kn i j (kl i j a (km i j w))) z
  rcases heval : km i j w with ⟨s, r⟩
  rcases hw a List.mem_cons_self with hai | haj
  ·
   rw [hai];simp only [kl,beq_self_eq_true,↓reduceIte]
   cases s
   · simp only [kn,Bool.false_eq_true,↓reduceIte,Bool.not_false];rfl
   ·
    simp only [kn,Bool.not_true,Bool.false_eq_true,↓reduceIte];exact qO (jv _ hz)
  ·
   rw [haj];have hij_ne : j ≠ i := hij.ne';simp only [kl,beq_iff_eq,hij_ne,↓reduceIte]
   cases s
   ·
    simp only [kn,Bool.not_false,Bool.false_eq_true,↓reduceIte];have hr_val : (r + 1).val = (r.val + 1) % 6 := rfl
    have hrot_lhs : qL j (jr (List.flatten (List.replicate r.val [i, j])) z) =
      qL i ((fun x => qL i (qL j x))^[r.val + 1] z) := by
     rw [hiter r.val z hz, Function.iterate_succ_apply']
     have hmem_it : (fun x => qL i (qL j x))^[r.val] z ∈ ball (0 : Z) 1 := by rw [← hiter r.val z hz];exact jv _ hz
     rw [qO (qN hmem_it)]
    have hrot_rhs : jr (i :: List.flatten (List.replicate (r + 1).val [i, j])) z =
      qL i ((fun x => qL i (qL j x))^[(r + 1).val] z) := by
     simp only [jr];rw [hiter _ z hz]
    change qL j (jr (List.flatten (List.replicate r.val [i, j])) z) =
     jr (i :: List.flatten (List.replicate (r + 1).val [i, j])) z
    rw [hrot_lhs, hrot_rhs, hr_val]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 r.isLt) with hlt5 | heq5
    · rw [Nat.mod_eq_of_lt (by omega)]
    ·
     have hr5 : r.val = 5 := by omega
     rw [hr5, show (5 + 1) % 6 = 0 by rfl, Function.iterate_zero_apply,
      show 5 + 1 = 6 by rfl, hpow6 z hz]
   ·
    simp only [kn,Bool.not_true,Bool.false_eq_true,↓reduceIte]
    have hrot_lhs : qL j (qL i (jr (List.flatten (List.replicate r.val [i, j])) z)) =
      qL j (qL i ((fun x => qL i (qL j x))^[r.val] z)) := by
     rw [hiter r.val z hz]
    have hrot_rhs : jr (List.flatten (List.replicate (r - 1).val [i, j])) z =
      (fun x => qL i (qL j x))^[(r - 1).val] z := hiter _ z hz
    change qL j (qL i (jr (List.flatten (List.replicate r.val [i, j])) z)) =
     jr (List.flatten (List.replicate (r - 1).val [i, j])) z
    rw [hrot_lhs, hrot_rhs]
    by_cases hr0 : r.val = 0
    ·
     have hr_sub : (r - 1).val = 5 := by
      have : r = 0 := Fin.ext hr0;subst this;decide
     rw [hr0, hr_sub, Function.iterate_zero_apply];have h6 := hpow6 z hz
     rw [show (6 : ℕ) = 1 + 5 by rfl, Function.iterate_add_apply,
      Function.iterate_one] at h6
     have h5mem : (fun x => qL i (qL j x))^[5] z ∈ ball (0 : Z) 1 := by rw [← hiter 5 z hz];exact jv _ hz
     have := congr_arg (fun w => qL j (qL i w)) h6;rw [qO (qN h5mem), qO h5mem] at this;exact this.symm
    ·
     have hr_pos : 0 < r.val := Nat.pos_of_ne_zero hr0
     have hr_sub : (r - 1).val = r.val - 1 := by omega
     rw [hr_sub]
     have hm1 : (fun x => qL i (qL j x))^[r.val - 1] z ∈ ball (0 : Z) 1 := by rw [← hiter (r.val - 1) z hz];exact jv _ hz
     have hstep : (fun x => qL i (qL j x))^[r.val] z =
       qL i (qL j ((fun x => qL i (qL j x))^[r.val - 1] z)) := by
      nth_rw 1 [show r.val = (r.val - 1) + 1 by omega]
      rw [Function.iterate_succ_apply']
     nth_rw 1 [hstep];rw [qO (qN hm1), qO hm1]
lemma kt {i j : Fin 3} (w : List (Fin 3)) (hw : ∀ a ∈ w, a = i ∨ a = j) (ζ : Z) :
  js w ζ =
   (if (km i j w).1 then qX i else id)
    ((fun x => qX i (qX j x))^[(km i j w).2.val] ζ) := by
 induction w with
 | nil => simp only [js,km,Fin.isValue,Bool.false_eq_true,↓reduceIte,Fin.coe_ofNat_eq_mod,Nat.zero_mod,iterate_zero,id_eq]
 | cons a w ih =>
  have hw' : ∀ b ∈ w, b = i ∨ b = j := fun b hb => hw b (List.mem_cons_of_mem a hb);have ihz := ih hw';change qX a (js w ζ) = _;rw [ihz]
  have hpow3 : ∀ x : Z, (fun y => qX i (qX j y))^[3] x = x := by intro x;simpa [Function.iterate_succ_apply'] using q2 i j x
  have hpow6 : ∀ x : Z, (fun y => qX i (qX j y))^[6] x = x := by intro x;rw [show (6 : ℕ) = 3 + 3 by rfl, Function.iterate_add_apply, hpow3, hpow3]
  change _ =
   (if (kl i j a (km i j w)).1 then qX i else id)
    ((fun x => qX i (qX j x))^[(kl i j a (km i j w)).2.val] ζ)
  rcases heval : km i j w with ⟨s, r⟩
  rcases hw a List.mem_cons_self with hai | haj
  ·
   rw [hai];simp only [kl,beq_self_eq_true,↓reduceIte]
   cases s
   · simp only [Bool.false_eq_true,↓reduceIte,id_eq,Bool.not_false]
   · simp only [↓reduceIte,q0,Bool.not_true,Bool.false_eq_true,id_eq]
  ·
   rw [haj]
   by_cases hij : j = i
   ·
    subst hij;simp only [kl,beq_self_eq_true,↓reduceIte]
    cases s
    · simp only [Bool.false_eq_true,↓reduceIte,id_eq,Bool.not_false]
    · simp only [↓reduceIte,q0,Bool.not_true,Bool.false_eq_true,id_eq]
   ·
    simp only [kl,beq_iff_eq,hij,↓reduceIte]
    cases s
    ·
     simp only [Bool.not_false,↓reduceIte];have hr_val : (r + 1).val = (r.val + 1) % 6 := rfl
     change qX j ((fun x => qX i (qX j x))^[r.val] ζ) =
      qX i ((fun x => qX i (qX j x))^[(r + 1).val] ζ)
     rw [hr_val]
     have hlhs : qX j ((fun x => qX i (qX j x))^[r.val] ζ) =
       qX i ((fun x => qX i (qX j x))^[r.val + 1] ζ) := by
      rw [Function.iterate_succ_apply', q0]
     rw [hlhs]
     rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 r.isLt) with hlt5 | heq5
     · rw [Nat.mod_eq_of_lt (by omega)]
     ·
      have hr5 : r.val = 5 := by omega
      rw [hr5, show (5 + 1) % 6 = 0 by rfl, Function.iterate_zero_apply,
       show 5 + 1 = 6 by rfl, hpow6]
    ·
     simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,id_eq]
     change qX j (qX i ((fun x => qX i (qX j x))^[r.val] ζ)) =
      (fun x => qX i (qX j x))^[(r - 1).val] ζ
     by_cases hr0 : r.val = 0
     ·
      have hr_sub : (r - 1).val = 5 := by
       have : r = 0 := Fin.ext hr0;subst this;decide
      rw [hr0, hr_sub, Function.iterate_zero_apply];have h6 := hpow6 ζ
      rw [show (6 : ℕ) = 1 + 5 by rfl, Function.iterate_add_apply,
       Function.iterate_one] at h6
      have := congr_arg (fun w => qX j (qX i w)) h6;rw [q0, q0] at this;exact this.symm
     ·
      have hr_pos : 0 < r.val := Nat.pos_of_ne_zero hr0
      have hr_sub : (r - 1).val = r.val - 1 := by omega
      rw [hr_sub]
      have hstep : (fun x => qX i (qX j x))^[r.val] ζ =
        qX i (qX j ((fun x => qX i (qX j x))^[r.val - 1] ζ)) := by
       nth_rw 1 [show r.val = (r.val - 1) + 1 by omega]
       rw [Function.iterate_succ_apply']
      nth_rw 1 [hstep];rw [q0, q0]
lemma ku {i j : Fin 3} (u : List (Fin 3))
  (hu : ∀ a ∈ u, a = i ∨ a = j) (hid : ∀ z ∈ ball (0 : Z) 1, jr u z = z) :
  ∀ ζ : Z, js u ζ = ζ := by
 by_cases hij : i = j
 ·
  subst hij;have hu_i : ∀ a ∈ u, a = i := fun a ha => (hu a ha).elim id id
  have hev_single : ∀ (w : List (Fin 3)), (∀ a ∈ w, a = i) →
    (w.length % 2 = 0 → (∀ z ∈ ball (0 : Z) 1, jr w z = z) ∧ ∀ ζ, js w ζ = ζ) ∧
    (w.length % 2 = 1 → (∀ z ∈ ball (0 : Z) 1, jr w z = qL i z) ∧ ∀ ζ, js w ζ = qX i ζ) := by
   intro w hw
   induction w with
   | nil => simp only [List.length_nil,Nat.zero_mod,mem_ball,dist_zero_right,jr,implies_true,js,and_self,zero_ne_one,IsEmpty.forall_iff]
   | cons a w ih =>
    have ha : a = i := hw a List.mem_cons_self;subst ha;have ihw := ih (fun b hb => hw b (List.mem_cons_of_mem a hb))
    rcases Nat.mod_two_eq_zero_or_one w.length with hw0 | hw1
    ·
     have h_even := ihw.1 hw0
     have hw_len : (a :: w).length % 2 = 1 := by simp only [List.length_cons];omega
     refine ⟨fun h => absurd h (by omega), fun _ => ⟨fun z hz => ?_, fun ζ => ?_⟩⟩
     · simp only [jr];rw [h_even.1 z hz]
     · simp only [js];rw [h_even.2 ζ]
    ·
     have h_odd := ihw.2 hw1
     have hw_len : (a :: w).length % 2 = 0 := by simp only [List.length_cons];omega
     refine ⟨fun _ => ⟨fun z hz => ?_, fun ζ => ?_⟩, fun h => absurd h (by omega)⟩
     · simp only [jr];rw [h_odd.1 z hz, qO hz]
     · simp only [js];rw [h_odd.2 ζ, q0]
  have hrec := hev_single u hu_i
  rcases Nat.mod_two_eq_zero_or_one u.length with h0 | h1
  · exact (hrec.1 h0).2
  ·
   exfalso
   have h0 : qL i 0 = 0 := by rw [← (hrec.2 h1).1 0 (mem_ball_self one_pos), hid 0 (mem_ball_self one_pos)]
   have hR : W (0 - qH i) = R2 := (kc (mem_ball_self one_pos)).1 h0;simp only [zero_sub,normSq_neg,qI] at hR;dsimp [R2] at hR;linarith
 ·
  have hswap : ∃ i' j' : Fin 3, i' < j' ∧ ∀ a ∈ u, a = i' ∨ a = j' := by
   rcases lt_trichotomy i j with h | h | h
   · exact ⟨i, j, h, hu⟩
   · exact absurd h hij
   · exact ⟨j, i, h, fun a ha => (hu a ha).symm⟩
  obtain ⟨i', j', hij', hu'⟩ := hswap;have heq_op := ks hij' u hu' (mem_ball_self one_pos);rw [hid 0 (mem_ball_self one_pos)] at heq_op
  have hmem : (i', j') ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)) := by fin_cases i' <;> fin_cases j' <;> first | exact absurd hij' (by decide) | decide
  have hnodup := List.all_eq_true.1 kq (i', j') hmem;simp only [decide_eq_true_eq] at hnodup
  have h_apply : (pX (kn i' j' (km i' j' u))).pP = (pX (kn i' j' (false, 0))).pP := by
   have h0 : jr (kn i' j' (km i' j' u)) 0 = jr (kn i' j' (false, 0)) 0 := by simpa [kn, jr] using heq_op.symm
   have hΦ : ∀ r : Fin 3, ((pX (kn i' j' (km i' j' u))).pP.get r).t0 =
     ((pX (kn i' j' (false, 0))).pP.get r).t0 := fun r => by
    rw [← jA, ← jA, h0]
   have hg : ∀ r : Fin 3, (pX (kn i' j' (km i' j' u))).pP.get r =
     (pX (kn i' j' (false, 0))).pP.get r := fun r => Z3.toReal_inj (hΦ r)
   rcases hL : (pX (kn i' j' (km i' j' u))).pP with ⟨a0, a1, a2⟩
   rcases hR : (pX (kn i' j' (false, 0))).pP with ⟨b0, b1, b2⟩
   have h0' := hg 0;have h1' := hg 1;have h2' := hg 2;rw [hL, hR] at h0' h1' h2';simp only [V3.get] at h0' h1' h2';rw [h0', h1', h2']
  have hmem_all : ∀ st : Bool × Fin 6, st ∈ ko := by intro ⟨s, r⟩;fin_cases s <;> fin_cases r <;> decide
  have hst : km i' j' u = (false, 0) := by
   have hnd_all : ko.Nodup := by decide
   rw [List.nodup_map_iff_inj_on hnd_all] at hnodup;exact hnodup _ (hmem_all _) _ (hmem_all _) h_apply
  intro ζ;rw [kt u hu' ζ, hst];simp only [Bool.false_eq_true,↓reduceIte,Fin.isValue,Fin.coe_ofNat_eq_mod,Nat.zero_mod,iterate_zero,id_eq]
def kv (i : Fin 3) : Z := ((tR - qv : X) : Z) * qy i
lemma kw : 0 < tR - qv := by
 have hlt : qv ^ 2 < tR ^ 2 := by rw [qx];dsimp [R2];linarith
 nlinarith only [hlt, qq, qw]
lemma kx : tR - qv < 1 := by
 have hprod : (tR - qv) * (tR + qv) = 1 := by
  have : (tR - qv) * (tR + qv) = tR ^ 2 - qv ^ 2 := by ring
  rw [this, qx];dsimp [R2];ring
 have hgt1 : 1 < tR + qv := by
  have htr1 : 1 < tR ^ 2 := by rw [qr];nlinarith only [qd]
  nlinarith only [htr1, qq, qw]
 nlinarith only [hprod, hgt1, kw]
lemma ky (i : Fin 3) {t : X} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
  (t : Z) * kv i ∈ T0 := by
 have h3 : Y 3 ^ 2 = 3 := qc
 have h01 : t * (tR - qv) < 1 := by
  have := mul_le_mul_of_nonneg_left kx.le ht0;nlinarith only [this, ht1, kx]
 have h00 : 0 ≤ t * (tR - qv) := mul_nonneg ht0 kw.le
 refine ⟨?_, fun j => ?_⟩
 ·
  rw [mem_ball, dist_zero_right, kv, ← mul_assoc, ← ofReal_mul, norm_mul,
   Complex.norm_of_nonneg h00, qz, mul_one]
  exact h01
 ·
  have hns : W ((t : Z) * kv i) = (t * (tR - qv)) ^ 2 := by
   rw [kv, ← mul_assoc, ← ofReal_mul, normSq_mul, normSq_ofReal,
    qA, mul_one, ← sq]
  have hre : ((t : Z) * kv i * T (qH j)).re =
    t * (tR - qv) * tR * (qy i * T (qy j)).re := by
   rw [kv, qH, ← mul_assoc, ← ofReal_mul, map_mul, conj_ofReal]
   simp only [mul_re, mul_im, conj_re, conj_im,
    ofReal_re, ofReal_im];ring
  have hsub : W ((t : Z) * kv i - qH j) =
    W ((t : Z) * kv i) + tR ^ 2 - 2 * ((t : Z) * kv i * T (qH j)).re := by
   simp only [normSq_apply, sub_re, sub_im, mul_re,
    conj_re, conj_im]
   have hc := qI j;simp only [normSq_apply] at hc;linarith
  rw [hsub, hns, hre]
  by_cases hij : j = i
  ·
   subst hij
   have hdir : (qy j * T (qy j)).re = 1 := by
    have := qA j;rw [← ofReal_inj] at this;rw [← mul_conj] at this;have hre' := congr_arg Complex.re this;simpa using hre'
   rw [hdir]
   have hsq : (tR - t * (tR - qv)) ^ 2 = (t * (tR - qv)) ^ 2 + tR ^ 2 - 2 * (t * (tR - qv) * tR * 1) := by ring
   rw [← hsq, ← qx]
   have hle : qv ≤ tR - t * (tR - qv) := by nlinarith only [ht1, kw]
   exact sq_le_sq' (by linarith [qw]) hle
  ·
   have hdir : (qy i * T (qy j)).re = -1 / 2 := by
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals
     simp only [qy,ω,sq,map_neg,map_mul,mul_neg,neg_mul,one_mul,neg_neg,mul_re,conj_re,conj_im,map_one,mul_one,mul_im,sub_neg_eq_add]
     try nlinarith only [h3]
   rw [hdir];dsimp [R2];nlinarith only [mul_nonneg h00 qq.le, sq_nonneg (t * (tR - qv))]
lemma kz (i : Fin 3) : qL i (kv i) = kv i := by
 have hm : kv i ∈ T0 := by simpa using ky i zero_le_one le_rfl
 apply (kc hm.1).2
 have hsub : kv i - qH i = (-qv : Z) * qy i := by dsimp [kv, qH];push_cast;ring
 rw [hsub, normSq_mul, normSq_neg, normSq_ofReal, qA, mul_one, ← sq, qx]
lemma kA : IsCompact T0 := by
 have hsub : T0 ⊆ closedBall (0 : Z) σ := fun x hx => by
  rw [mem_closedBall, dist_zero_right];exact jT hx
 have hcl : IsClosed T0 := by
  have hball : closedBall (0 : Z) σ ⊆ ball (0 : Z) 1 := by
   intro x hx;rw [mem_closedBall, dist_zero_right] at hx;rw [mem_ball, dist_zero_right];exact hx.trans_lt qp
  have heq : T0 = closedBall (0 : Z) σ ∩ ⋂ i : Fin 3, { z : Z | R2 ≤ W (z - qH i) } := by
   ext x;simp only [T0,mem_inter_iff,mem_iInter,mem_ofPred_eq];constructor
   · intro hx;exact ⟨by rw [mem_closedBall, dist_zero_right];exact jT hx, hx.2⟩
   · intro ⟨hx1, hx2⟩;exact ⟨hball hx1, hx2⟩
  rw [heq]
  refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
  exact isClosed_le continuous_const (continuous_normSq.comp (continuous_id.sub continuous_const))
 exact (isCompact_closedBall (0 : Z) σ).of_isClosed_subset hcl hsub
lemma kB (i : Fin 3) : ContinuousOn (qL i) (ball (0 : Z) 1) := by
 intro z hz
 refine ContinuousAt.continuousWithinAt ?_
 refine ContinuousAt.div ?_ ?_ (qM (i := i) hz)
 · exact (continuous_const.mul continuous_conj).sub continuous_const |>.continuousAt
 · exact (continuous_conj.sub continuous_const).continuousAt
lemma kC (w : List (Fin 3)) : ContinuousOn (jr w) (ball (0 : Z) 1) := by
 induction w with
 | nil => exact continuousOn_id
 | cons i w ih =>
  exact (kB i).comp ih (fun z hz => jv w hz)
def kD (v : List (Fin 3)) (k : ℕ) (τ : X) : Z :=
 match v[k]? with
 | none => 0
 | some a =>
  if τ ≤ 1 / 2 then jr (v.take k) (((2 * τ : X) : Z) * kv a)
  else jr (v.take (k + 1)) (((2 - 2 * τ : X) : Z) * kv a)
def kE (v : List (Fin 3)) (t : X) : Z :=
 if _hv : v.length = 0 then 0
 else
  let m := v.length;let k := min (Nat.floor (t * m)) (m - 1);let τ := t * m - k
  kD v k τ
lemma kF (v : List (Fin 3)) {k : ℕ} (hk : k < v.length) :
  kD v k 0 = jr (v.take k) 0 := by
 dsimp [kD];rw [getElem?_pos v k hk];simp only [one_div,inv_nonneg,Nat.ofNat_nonneg,↓reduceIte,mul_zero,ofReal_zero,zero_mul]
lemma kG (v : List (Fin 3)) {k : ℕ} (hk : k < v.length) :
  kD v k 1 = jr (v.take (k + 1)) 0 := by
 dsimp [kD];rw [getElem?_pos v k hk];norm_num
lemma kH (v : List (Fin 3)) {k : ℕ} (hk : k < v.length) :
  ContinuousOn (kD v k) (Icc 0 1) := by
 unfold kD;rw [getElem?_pos v k hk]
 have hc1 : ContinuousOn (fun τ : X => jr (v.take k) (((2 * τ : X) : Z) * kv v[k])) (Icc 0 (1 / 2)) := by
  refine (kC (v.take k)).comp ?_ ?_
  · exact ((continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const).continuousOn
  ·
   intro τ hτ
   exact (ky v[k] (by linarith [hτ.1]) (by linarith [hτ.2])).1
 have hc2 : ContinuousOn (fun τ : X => jr (v.take (k + 1)) (((2 - 2 * τ : X) : Z) * kv v[k])) (Icc (1 / 2) 1) := by
  refine (kC (v.take (k + 1))).comp ?_ ?_
  · exact ((continuous_ofReal.comp (continuous_const.sub (continuous_const.mul continuous_id))).mul continuous_const).continuousOn
  ·
   intro τ hτ
   exact (ky v[k] (by linarith [hτ.2]) (by linarith [hτ.1])).1
 have heq : jr (v.take k) (((2 * (1 / 2 : X) : X) : Z) * kv v[k]) =
   jr (v.take (k + 1)) (((2 - 2 * (1 / 2 : X) : X) : Z) * kv v[k]) := by
  norm_num;rw [List.take_succ_eq_append_getElem hk, jt];simp only [jr,kz]
 have hpiece : ContinuousOn (fun τ => if τ ≤ (1 / 2 : X) then
    jr (v.take k) (((2 * τ : X) : Z) * kv v[k])
   else jr (v.take (k + 1)) (((2 - 2 * τ : X) : Z) * kv v[k])) (Icc 0 1) := by
  have hcov : Icc (0 : X) 1 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 1 := by
   ext x;simp only [mem_Icc,mem_union];constructor
   ·
    rintro ⟨hx0, hx1⟩
    rcases le_total x (1 / 2) with h1 | h1
    · exact Or.inl ⟨hx0, h1⟩
    · exact Or.inr ⟨h1, hx1⟩
   · rintro (⟨hx0, hx1⟩ | ⟨hx0, hx1⟩) <;> exact ⟨by linarith, by linarith⟩
  rw [hcov]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
  · refine hc1.congr fun τ hτ => if_pos hτ.2
  ·
   refine hc2.congr fun τ hτ => ?_
   rcases eq_or_lt_of_le hτ.1 with rfl | hlt
   · rw [if_pos le_rfl];exact heq
   · rw [if_neg (not_le.2 hlt)]
 exact hpiece
lemma kI (v : List (Fin 3)) (k : ℕ) {τ : X} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
  kD v k τ ∈ ball (0 : Z) 1 := by
 dsimp [kD]
 cases h : v[k]? with
 | none => exact mem_ball_self one_pos
 | some a =>
  split_ifs with h12
  · exact jv _ (ky a (by linarith) (by linarith)).1
  · exact jv _ (ky a (by linarith) (by linarith)).1
lemma kJ (v : List (Fin 3)) {t : X} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
  kE v t ∈ ball (0 : Z) 1 := by
 dsimp [kE]
 split_ifs with hv
 · exact mem_ball_self one_pos
 ·
  have hm : 0 < v.length := Nat.pos_of_ne_zero hv;set k := min (Nat.floor (t * v.length)) (v.length - 1);have hk_le_fl : k ≤ Nat.floor (t * v.length) := min_le_left _ _
  have htau0 : 0 ≤ t * v.length - k := by
   have h1 : (k : X) ≤ Nat.floor (t * v.length) := by exact_mod_cast hk_le_fl
   have h2 : (Nat.floor (t * v.length) : X) ≤ t * v.length := Nat.floor_le (mul_nonneg ht0 (Nat.cast_nonneg _));linarith
  have htau1 : t * v.length - k ≤ 1 := by
   rcases le_total (Nat.floor (t * v.length)) (v.length - 1) with hle | hgt
   ·
    have hk_eq : k = Nat.floor (t * v.length) := min_eq_left hle;rw [hk_eq];have := Nat.lt_floor_add_one (t * v.length);linarith
   ·
    have hk_eq : k = v.length - 1 := min_eq_right hgt;rw [hk_eq]
    have htm : t * v.length ≤ v.length := by nlinarith only [ht1, (show (0 : X) ≤ v.length by positivity)]
    have hk_cast : ((v.length - 1 : ℕ) : X) = (v.length : X) - 1 := by rw [Nat.cast_sub hm];simp only [Nat.succ_eq_add_one,zero_add,Nat.cast_one]
    linarith
  exact kI v k htau0 htau1
lemma kK (v : List (Fin 3)) : ContinuousOn (kE v) (Icc 0 1) := by
 by_cases hv : v.length = 0
 ·
  refine (continuousOn_const (c := (0 : Z))).congr fun t _ => ?_
  simp only [kE,hv,↓reduceDIte]
 ·
  have hm : 0 < v.length := Nat.pos_of_ne_zero hv
  have hpiece : ∀ k < v.length,
    ContinuousOn (fun t : X => kD v k (t * v.length - k)) (Icc ((k : X) / v.length) (((k + 1 : ℕ) : X) / v.length)) := by
   intro k hk
   refine (kH v hk).comp ?_ ?_
   · exact ((continuous_id.mul continuous_const).sub continuous_const).continuousOn
   ·
    intro t ht;have hm0 : (0 : X) < v.length := Nat.cast_pos.2 hm
    rw [mem_Icc] at ht ⊢
    constructor
    ·
     have : (k : X) ≤ t * v.length := (div_le_iff₀ hm0).1 ht.1;linarith
    ·
     have : t * v.length ≤ k + 1 := by
      have h1 := (le_div_iff₀ hm0).1 ht.2;push_cast at h1;linarith
     linarith
  have hmatch : ∀ k < v.length, ∀ t ∈ Icc ((k : X) / v.length) (((k + 1 : ℕ) : X) / v.length),
    kE v t = kD v k (t * v.length - k) := by
   intro k hk t ht;have hm0 : (0 : X) < v.length := Nat.cast_pos.2 hm;have hkt0 : (k : X) ≤ t * v.length := (div_le_iff₀ hm0).1 ht.1
   have hkt1 : t * v.length ≤ k + 1 := by
    have h1 := (le_div_iff₀ hm0).1 ht.2;push_cast at h1;linarith
   unfold kE;rw [dif_neg hv]
   rcases eq_or_lt_of_le hkt1 with htop | hlt
   ·
    have hfl : Nat.floor (t * v.length) = k + 1 := by
     rw [htop];exact_mod_cast Nat.floor_natCast (k + 1)
    by_cases hlast : k + 1 = v.length
    ·
     have hmin : min (Nat.floor (t * v.length)) (v.length - 1) = k := by rw [hfl];omega
     simp only [hmin]
    ·
     have hmin : min (Nat.floor (t * v.length)) (v.length - 1) = k + 1 := by rw [hfl];omega
     have hk1_lt : k + 1 < v.length := by omega
     simp only [hmin];rw [htop];have hs0 : kD v (k + 1) 0 = jr (v.take (k + 1)) 0 := kF v hk1_lt;have hs1 : kD v k 1 = jr (v.take (k + 1)) 0 := kG v hk
     rw [show (k : X) + 1 - ((k + 1 : ℕ) : X) = 0 by push_cast;ring, hs0,
      show (k : X) + 1 - (k : X) = 1 by ring, hs1]
   ·
    have hnn : (0 : X) ≤ t * v.length :=
     mul_nonneg (le_trans (by positivity) ht.1) (Nat.cast_nonneg _)
    have hfl : Nat.floor (t * v.length) = k :=
     (Nat.floor_eq_iff hnn).2 ⟨hkt0, hlt⟩
    have hmin : min (Nat.floor (t * v.length)) (v.length - 1) = k := by rw [hfl];exact min_eq_left (by omega)
    simp only [hmin]
  have hunion : ∀ n : ℕ, n ≤ v.length → n ≠ 0 →
    ContinuousOn (kE v) (Icc 0 ((n : X) / v.length)) := by
   intro n hn hn0
   induction n with
   | zero => exact absurd rfl hn0
   | succ n ih =>
    by_cases hn_zero : n = 0
    ·
     subst hn_zero
     convert (hpiece 0 hm).congr (fun t ht => hmatch 0 hm t ht) using 2;simp only [CharP.cast_eq_zero,zero_div]
    ·
     have ih_n := ih (by omega) hn_zero
     have hcov : Icc (0 : X) (((n + 1 : ℕ) : X) / v.length) =
       Icc 0 ((n : X) / v.length) ∪ Icc ((n : X) / v.length) (((n + 1 : ℕ) : X) / v.length) := by
      ext t;simp only [mem_Icc,mem_union];have hm0 : (0 : X) < v.length := Nat.cast_pos.2 hm
      have h0n : (0 : X) ≤ (n : X) / v.length := by positivity
      have hnn1 : (n : X) / v.length ≤ ((n + 1 : ℕ) : X) / v.length := by rw [div_le_div_iff_of_pos_right hm0];exact_mod_cast Nat.le_succ n
      constructor
      ·
       rintro ⟨ht0, htn1⟩
       rcases le_total t ((n : X) / v.length) with hle | hge
       · exact Or.inl ⟨ht0, hle⟩
       · exact Or.inr ⟨hge, htn1⟩
      ·
       rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
       · exact ⟨h1, h2.trans hnn1⟩
       · exact ⟨h0n.trans h1, h2⟩
     rw [hcov]
     refine ContinuousOn.union_of_isClosed ih_n ?_ isClosed_Icc isClosed_Icc
     exact (hpiece n (by omega)).congr fun t ht => hmatch n (by omega) t ht
  have hfull := hunion v.length le_rfl hv;have hm0 : ((v.length : X) / v.length) = 1 := div_self (Nat.cast_ne_zero.2 hv);simpa [hm0] using hfull
lemma kL (v : List (Fin 3)) : kE v 0 = 0 := by
 dsimp [kE]
 split_ifs with hv
 · rfl
 ·
  simp only [zero_mul,Nat.floor_zero,Nat.zero_min,CharP.cast_eq_zero,sub_zero];rw [kF v (Nat.pos_of_ne_zero hv)];rfl
lemma kM (v : List (Fin 3)) : kE v 1 = jr v 0 := by
 dsimp [kE]
 split_ifs with hv
 ·
  have : v = [] := List.length_eq_zero_iff.1 hv;subst this;rfl
 ·
  have hm : 0 < v.length := Nat.pos_of_ne_zero hv
  have hfl : Nat.floor ((1 : X) * v.length) = v.length := by rw [one_mul];exact_mod_cast Nat.floor_natCast v.length
  have hmin : min (Nat.floor ((1 : X) * v.length)) (v.length - 1) = v.length - 1 := by rw [hfl];exact min_eq_right (Nat.sub_le _ _)
  rw [hmin]
  have htau : (1 : X) * v.length - ((v.length - 1 : ℕ) : X) = 1 := by rw [Nat.cast_sub hm];ring
  rw [htau, kG v (Nat.sub_lt hm one_pos)];have htk : v.length - 1 + 1 = v.length := Nat.sub_add_cancel hm;rw [htk, List.take_length]
def kN (E : (ℕ × ℕ) → (ℕ × ℕ) → Z → Z) : ℕ → ℕ → ℕ → Z → Z
 | _, 0, _, ζ => ζ
 | a, k + 1, b, ζ => E (a, b) (a + 1, b) (kN E (a + 1) k b ζ)
def kO (E : (ℕ × ℕ) → (ℕ × ℕ) → Z → Z) : ℕ → ℕ → ℕ → Z → Z
 | _, _, 0, ζ => ζ
 | a, b, k + 1, ζ => E (a, b) (a, b + 1) (kO E a (b + 1) k ζ)
open Classical in
noncomputable def kP (w₁ w₂ : List (Fin 3)) : List (Fin 3) :=
 if h : ∃ w₀ ∈ jn, ∀ z ∈ ball (0 : Z) 1, jr (w₁ ++ w₂.reverse) z = jr w₀ z
 then h.choose else []
lemma kQ {w₁ w₂ w₀ : List (Fin 3)} (hw₀ : w₀ ∈ jn)
  (heq : ∀ z ∈ ball (0 : Z) 1, jr (w₁ ++ w₂.reverse) z = jr w₀ z) :
  kP w₁ w₂ = w₀ := by
 have hex : ∃ w' ∈ jn, ∀ z ∈ ball (0 : Z) 1, jr (w₁ ++ w₂.reverse) z = jr w' z := ⟨w₀, hw₀, heq⟩;dsimp [kP];rw [dif_pos hex];have hch_mem := hex.choose_spec.1;have hch_eq := hex.choose_spec.2
 have h_apply : (pX hex.choose).pP = (pX w₀).pP := by
  have h0 : jr hex.choose 0 = jr w₀ 0 := by rw [← hch_eq 0 (mem_ball_self one_pos), heq 0 (mem_ball_self one_pos)]
  have hΦ : ∀ r : Fin 3, ((pX hex.choose).pP.get r).t0 = ((pX w₀).pP.get r).t0 := fun r => by
   rw [← jA, ← jA, h0]
  have hg : ∀ r : Fin 3, (pX hex.choose).pP.get r = (pX w₀).pP.get r := fun r =>
   Z3.toReal_inj (hΦ r)
  rcases hL : (pX hex.choose).pP with ⟨a0, a1, a2⟩
  rcases hR : (pX w₀).pP with ⟨b0, b1, b2⟩
  have h0' := hg 0;have h1' := hg 1;have h2' := hg 2;rw [hL, hR] at h0' h1' h2';simp only [V3.get] at h0' h1' h2';rw [h0', h1', h2']
 have hnodup : (jn.map (fun w => (pX w).pP)).Nodup := by simpa using kh
 rw [List.nodup_map_iff_inj_on (by decide : jn.Nodup)] at hnodup
 exact hnodup hex.choose hch_mem w₀ hw₀ h_apply
lemma kR {w₁ w₂ : List (Fin 3)} {z_star : Z}
  (hz : z_star ∈ ball (0 : Z) 1) (hw1 : jr w₁ z_star ∈ T0) (hw2 : jr w₂ z_star ∈ T0) :
  jr w₁ z_star = jr w₂ z_star ∧
  (∀ u ∈ ball (0 : Z) 1, jr (w₁ ++ w₂.reverse) u = jr (kP w₁ w₂) u) ∧
  ((kP w₁ w₂ = []) ∨
   (∃ i : Fin 3, kP w₁ w₂ = [i] ∧ W (jr w₂ z_star - qH i) = R2) ∨
   (∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ jr w₂ z_star = j5 k ∧
    ∀ a ∈ kP w₁ w₂, a = i ∨ a = j)) := by
 have hcomp : jr (w₁ ++ w₂.reverse) (jr w₂ z_star) = jr w₁ z_star := by rw [jt, jw w₂ hz]
 obtain ⟨w₀, hw₀, heq⟩ := jW hw2 hw1 hcomp;have h_edge_eq : kP w₁ w₂ = w₀ := kQ hw₀ heq
 have hwx : jr w₀ (jr w₂ z_star) ∈ T0 := by rw [← heq _ hw2.1, hcomp];exact hw1
 obtain ⟨hfix, hcls⟩ := kk hw₀ hw2 hwx
 refine ⟨?_, ?_, ?_⟩
 · rw [← hcomp, heq _ hw2.1, hfix]
 · rw [h_edge_eq];exact heq
 · rw [h_edge_eq];exact hcls
lemma kS {α : Type*} (gridW : α → List (Fin 3))
  (u_list : List (α × α)) {z_star x_star : Z}
  (hz : z_star ∈ ball (0 : Z) 1) (hx_star : x_star ∈ T0)
  (hmem : ∀ e ∈ u_list, jr (gridW e.1) z_star = x_star ∧ jr (gridW e.2) z_star = x_star)
  (hid : ∀ u ∈ ball (0 : Z) 1, jr (u_list.flatMap fun e => kP (gridW e.1) (gridW e.2)) u = u) :
  ∀ ζ : Z, js (u_list.flatMap fun e => kP (gridW e.1) (gridW e.2)) ζ = ζ := by
 have hx_pair : ∃ i j : Fin 3, ∀ (w₁ w₂ : List (Fin 3)),
   jr w₁ z_star = x_star → jr w₂ z_star = x_star →
   ∀ a ∈ kP w₁ w₂, a = i ∨ a = j := by
  have hvert_inj : ∀ k₁ k₂ : Fin 3, j5 k₁ = j5 k₂ → k₁ = k₂ := by
   intro k₁ k₂ h
   have h' : j4 k₁ = j4 k₂ :=
    mul_left_cancel₀ (ofReal_ne_zero.2 qn.ne') h
   have h3 : Y 3 ^ 2 = 3 := qc;have h3p : (0 : X) < Y 3 := qd
   fin_cases k₁ <;> fin_cases k₂ <;> try rfl
   all_goals
    exfalso;have hre := congr_arg Complex.re h';have him := congr_arg Complex.im h';simp only [j4,ω,sq,mul_re,mul_im,one_re,one_im] at hre him;nlinarith only [hre, him, h3, h3p]
  have hvert_diag : ∀ k : Fin 3, W (j5 k - qH k) ≠ R2 := by
   intro k h;have h3 : Y 3 ^ 2 = 3 := qc
   have hre : (j4 k * T (qy k)).re = -1 := by
    fin_cases k
    · simp only [j4,qy,map_neg,map_one,mul_neg,mul_one,neg_re,one_re]
    ·
     simp only [j4,ω,sq,qy,map_neg,map_mul,mul_neg,neg_re,mul_re,conj_re,conj_im,neg_mul,neg_neg,mul_im,neg_sub];nlinarith only [h3]
    ·
     simp only [j4,ω,qy,map_neg,mul_neg,neg_re,mul_re,conj_re,conj_im,sub_neg_eq_add,neg_add_rev];nlinarith only [h3]
   rw [j9, hre] at h;dsimp [R2] at h;nlinarith only [h, qn, qq]
  by_cases h0 : ∃ k : Fin 3, x_star = j5 k
  ·
   obtain ⟨k, rfl⟩ := h0
   have hex_pair : ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    fin_cases k
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
   obtain ⟨i, j, hij, hik, hjk⟩ := hex_pair
   refine ⟨i, j, fun w₁ w₂ hw1 hw2 a ha => ?_⟩
   obtain ⟨_, _, hcls⟩ := kR hz (hw1 ▸ hx_star) (hw2 ▸ hx_star);rw [hw2] at hcls
   rcases hcls with heq | ⟨i', hi', hns⟩ | ⟨i', j', k', _, _, _, hvk, hlet⟩
   · rw [heq] at ha;simp only [List.not_mem_nil] at ha
   ·
    rw [hi', List.mem_singleton] at ha;subst ha
    have ha_ne_k : a ≠ k := fun h => by subst h;exact hvert_diag a hns
    omega
   ·
    have hkk' := hvert_inj k k' hvk;subst hkk'
    rcases hlet a ha with rfl | rfl <;> omega
  ·
   by_cases h1 : ∃ i : Fin 3, W (x_star - qH i) = R2
   ·
    obtain ⟨i, hi⟩ := h1
    refine ⟨i, i, fun w₁ w₂ hw1 hw2 a ha => ?_⟩
    obtain ⟨_, _, hcls⟩ := kR hz (hw1 ▸ hx_star) (hw2 ▸ hx_star);rw [hw2] at hcls
    rcases hcls with heq | ⟨i', hi', hns⟩ | ⟨_, _, k', _, _, _, hvk, _⟩
    · rw [heq] at ha;simp only [List.not_mem_nil] at ha
    ·
     rw [hi', List.mem_singleton] at ha;subst ha
     by_cases hai : a = i
     · exact Or.inl hai
     ·
      exfalso
      have hexk : ∃ k : Fin 3, a ≠ k ∧ i ≠ k := by fin_cases a <;> fin_cases i <;> first | contradiction | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ | exact ⟨2, by decide, by decide⟩
      obtain ⟨k, hak, hik⟩ := hexk;exact h0 ⟨k, ke hai hak hik hx_star hns hi⟩
    · exact absurd hvk (fun h => h0 ⟨k', h⟩)
   ·
    refine ⟨0, 0, fun w₁ w₂ hw1 hw2 a ha => ?_⟩
    obtain ⟨_, _, hcls⟩ := kR hz (hw1 ▸ hx_star) (hw2 ▸ hx_star);rw [hw2] at hcls
    rcases hcls with heq | ⟨i', _, hns⟩ | ⟨_, _, k', _, _, _, hvk, _⟩
    · rw [heq] at ha;simp only [List.not_mem_nil] at ha
    · exact absurd ⟨i', hns⟩ h1
    · exact absurd hvk (fun h => h0 ⟨k', h⟩)
 obtain ⟨i, j, hij⟩ := hx_pair
 refine @ku i j _ (fun a ha => ?_) hid
 rw [List.mem_flatMap] at ha;obtain ⟨e, he, hae⟩ := ha;exact hij _ _ (hmem e he).1 (hmem e he).2 a hae
lemma kT (x : Fin 3) : [x] ∈ jn := by fin_cases x <;> decide
def kU (m N K b : ℕ) : ℕ :=
 if b = N then m
 else if b % (2 * K) ≤ K then b / (2 * K)
 else b / (2 * K) + 1
lemma kV {m N K : ℕ} (hN : 0 < N) : kU m N K 0 = 0 := by simp only [kU,hN.ne,↓reduceIte,Nat.zero_mod,zero_le,Nat.zero_div]
lemma kW (m N K : ℕ) : kU m N K N = m := by simp only [kU,↓reduceIte]
lemma kX {m N K : ℕ} (hK2 : 2 ≤ K) (hN : N = 2 * m * K)
  {b : ℕ} (hb : b < N) :
  kU m N K (b + 1) = kU m N K b ∨
   (kU m N K (b + 1) = kU m N K b + 1 ∧ kU m N K b < m) := by
 have h2K_pos : 0 < 2 * K := by omega
 obtain ⟨k, hk_def⟩ : ∃ k : ℕ, k = b / (2 * K) := ⟨_, rfl⟩;obtain ⟨rem, hrem_def⟩ : ∃ rem : ℕ, rem = b % (2 * K) := ⟨_, rfl⟩
 have hdiv : b = 2 * K * k + rem := by rw [hk_def, hrem_def];exact (Nat.div_add_mod b (2 * K)).symm
 have hrem_lt : rem < 2 * K := by rw [hrem_def];exact Nat.mod_lt b h2K_pos
 have hk_lt : k < m := by
  have hb' : b < 2 * m * K := hN ▸ hb
  have : 2 * K * k < 2 * K * m := by nlinarith only [hb', hdiv]
  exact Nat.lt_of_mul_lt_mul_left this
 have hbN : b ≠ N := hb.ne
 by_cases hrem_lt_K : rem < K
 ·
  left
  have hb1_lt : b + 1 < N := by
   rw [hN];have : 2 * K * (k + 1) ≤ 2 * K * m := Nat.mul_le_mul_left _ hk_lt;nlinarith only [this, hdiv, hrem_lt_K]
  have hb1_rem : (b + 1) % (2 * K) = rem + 1 := by
   rw [hdiv, add_assoc, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
   exact Nat.mod_eq_of_lt (by omega)
  have hb1_div : (b + 1) / (2 * K) = k := by rw [hdiv, add_assoc, Nat.mul_add_div h2K_pos, Nat.div_eq_of_lt (by omega), add_zero]
  dsimp [kU]
  rw [if_neg hb1_lt.ne, if_pos (by rw [hb1_rem];omega), hb1_div, ← hk_def,
   if_neg hbN, if_pos (by rw [← hrem_def];omega : b % (2 * K) ≤ K)]
 ·
  by_cases hrem_eq_K : rem = K
  ·
   right
   have hrem1_lt : K + 1 < 2 * K := by omega
   have hb1_lt : b + 1 < N := by
    rw [hN];have : 2 * K * (k + 1) ≤ 2 * K * m := Nat.mul_le_mul_left _ hk_lt;nlinarith only [this, hdiv, hrem_eq_K, hK2]
   have hb1_rem : (b + 1) % (2 * K) = K + 1 := by
    rw [hdiv, hrem_eq_K, add_assoc, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod];exact Nat.mod_eq_of_lt hrem1_lt
   have hb1_div : (b + 1) / (2 * K) = k := by rw [hdiv, hrem_eq_K, add_assoc, Nat.mul_add_div h2K_pos, Nat.div_eq_of_lt hrem1_lt, add_zero]
   dsimp [kU]
   rw [if_neg hb1_lt.ne, if_neg (by rw [hb1_rem];omega), hb1_div, ← hk_def,
    if_neg hbN, if_pos (by rw [← hrem_def, hrem_eq_K])]
   exact ⟨rfl, hk_lt⟩
  ·
   left
   have hrem_gt : K < rem := by omega
   by_cases hrem_top : rem + 1 < 2 * K
   ·
    have hb1_lt : b + 1 < N := by
     rw [hN];have : 2 * K * (k + 1) ≤ 2 * K * m := Nat.mul_le_mul_left _ hk_lt;nlinarith only [this, hdiv, hrem_top]
    have hb1_rem : (b + 1) % (2 * K) = rem + 1 := by
     rw [hdiv, add_assoc, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod];exact Nat.mod_eq_of_lt hrem_top
    have hb1_div : (b + 1) / (2 * K) = k := by rw [hdiv, add_assoc, Nat.mul_add_div h2K_pos, Nat.div_eq_of_lt hrem_top, add_zero]
    dsimp [kU]
    rw [if_neg hb1_lt.ne, if_neg (by rw [hb1_rem];omega), hb1_div, ← hk_def,
     if_neg hbN, if_neg (by rw [← hrem_def];omega)]
   ·
    have hrem_eq : rem + 1 = 2 * K := by omega
    have hb1_eq : b + 1 = 2 * K * (k + 1) := by linarith
    have hright_b : kU m N K b = k + 1 := by dsimp [kU];rw [if_neg hbN, if_neg (by rw [← hrem_def];omega), ← hk_def]
    rw [hright_b];dsimp [kU]
    by_cases hk1 : k + 1 = m
    ·
     have hb1N : b + 1 = N := by rw [hb1_eq, hk1, hN];ring
     rw [if_pos hb1N, hk1]
    ·
     have hb1N : b + 1 ≠ N := by
      intro h;have : 2 * K * (k + 1) = 2 * K * m := by rw [← hb1_eq, h, hN];ring
      exact hk1 (Nat.eq_of_mul_eq_mul_left h2K_pos this)
     have hb1_rem : (b + 1) % (2 * K) = 0 := by rw [hb1_eq];exact Nat.mul_mod_right _ _
     have hb1_div : (b + 1) / (2 * K) = k + 1 := by rw [hb1_eq];exact Nat.mul_div_right _ h2K_pos
     rw [if_neg hb1N, if_pos (by rw [hb1_rem];omega), hb1_div]
lemma kY (v : List (Fin 3)) (hv0 : v.length ≠ 0) {N K : ℕ}
  (hK2 : 2 ≤ K) (hN : N = 2 * v.length * K) {b : ℕ} (hb : b < N) :
  jr (v.take (kU v.length N K b)).reverse (kE v ((b : X) / N)) ∈ T0 := by
 have hm : 0 < v.length := Nat.pos_of_ne_zero hv0
 have h2K_pos : 0 < 2 * K := by omega
 obtain ⟨k, hk_def⟩ : ∃ k : ℕ, k = b / (2 * K) := ⟨_, rfl⟩;obtain ⟨rem, hrem_def⟩ : ∃ rem : ℕ, rem = b % (2 * K) := ⟨_, rfl⟩
 have hdiv : b = 2 * K * k + rem := by rw [hk_def, hrem_def];exact (Nat.div_add_mod b (2 * K)).symm
 have hrem_lt : rem < 2 * K := by rw [hrem_def];exact Nat.mod_lt b h2K_pos
 have hk_lt : k < v.length := by
  have hb' : b < 2 * v.length * K := hN ▸ hb
  have : 2 * K * k < 2 * K * v.length := by nlinarith only [hb', hdiv]
  exact Nat.lt_of_mul_lt_mul_left this
 have htm : ((b : X) / N) * v.length = (b : X) / (2 * K) := by
  rw [hN];push_cast;have hm0 : (v.length : X) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hK0 : (K : X) ≠ 0 := by positivity
  field_simp [hm0, hK0]
 have hfl : Nat.floor (((b : X) / N) * v.length) = k := by
  rw [htm, Nat.floor_eq_iff (by positivity)]
  have h2K0 : (0 : X) < 2 * K := by positivity
  constructor
  · rw [le_div_iff₀ h2K0];exact_mod_cast (by nlinarith only [hdiv] : k * (2 * K) ≤ b)
  · rw [div_lt_iff₀ h2K0];exact_mod_cast (by nlinarith only [hdiv, hrem_lt] : b < (k + 1) * (2 * K))
 have hmin : min (Nat.floor (((b : X) / N) * v.length)) (v.length - 1) = k := by rw [hfl];exact min_eq_left (by omega)
 have hγ_eq : kE v ((b : X) / N) = kD v k (((b : X) / N) * v.length - k) := by dsimp [kE];rw [if_neg hv0, hmin]
 rw [hγ_eq]
 have htau_eq : ((b : X) / N) * v.length - k = (rem : X) / (2 * K) := by
  rw [htm, hdiv];push_cast
  have h2K0 : (2 : X) * K ≠ 0 := by positivity
  field_simp [h2K0];ring
 rw [htau_eq];dsimp [kD];rw [getElem?_pos v k hk_lt];dsimp
 have h2K0 : (0 : X) < 2 * K := by positivity
 have htau0 : 0 ≤ (rem : X) / (2 * K) := by positivity
 have htau1 : (rem : X) / (2 * K) ≤ 1 := by rw [div_le_one h2K0];exact_mod_cast hrem_lt.le
 by_cases hremK : rem ≤ K
 ·
  have hhalf : (rem : X) / (2 * K) ≤ 1 / 2 := by rw [div_le_div_iff₀ h2K0 two_pos];exact_mod_cast (by nlinarith only [hremK] : rem * 2 ≤ 1 * (2 * K))
  have hri : kU v.length N K b = k := by dsimp [kU];rw [if_neg hb.ne, if_pos (by rw [← hrem_def];exact hremK), ← hk_def]
  rw [if_pos hhalf, hri];let s : Z := ((2 * ((rem : X) / (2 * K)) : X) : Z) * kv v[k]
  have hseg : s ∈ T0 := ky v[k] (t := 2 * ((rem : X) / (2 * K))) (by linarith) (by linarith)
  change jr (v.take k).reverse (jr (v.take k) s) ∈ T0;rw [jw _ hseg.1];exact hseg
 ·
  have hhalf : ¬ ((rem : X) / (2 * K) ≤ 1 / 2) := by rw [not_le, div_lt_div_iff₀ two_pos h2K0];exact_mod_cast (by nlinarith only [hremK] : 1 * (2 * K) < rem * 2)
  have hri : kU v.length N K b = k + 1 := by dsimp [kU];rw [if_neg hb.ne, if_neg (by rw [← hrem_def];exact hremK), ← hk_def]
  rw [if_neg hhalf, hri];let s : Z := ((2 - 2 * ((rem : X) / (2 * K)) : X) : Z) * kv v[k]
  have hseg : s ∈ T0 := ky v[k] (t := 2 - 2 * ((rem : X) / (2 * K))) (by linarith) (by linarith)
  change jr (v.take (k + 1)).reverse (jr (v.take (k + 1)) s) ∈ T0;rw [jw _ hseg.1];exact hseg
lemma kZ (v : List (Fin 3)) (hv0 : v.length ≠ 0)
  (hv : ∀ z ∈ ball (0 : Z) 1, jr v z = z) :
  ∃ (N K : ℕ) (rightIdx : ℕ → ℕ) (gridWord : ℕ → ℕ → List (Fin 3)),
   0 < N ∧ 2 ≤ K ∧ N = 2 * v.length * K ∧
   rightIdx 0 = 0 ∧ rightIdx N = v.length ∧
   (∀ b < N, rightIdx (b + 1) = rightIdx b ∨
    (rightIdx (b + 1) = rightIdx b + 1 ∧ rightIdx b < v.length)) ∧
   (∀ a ≤ N, gridWord a 0 = []) ∧
   (∀ b ≤ N, gridWord 0 b = []) ∧
   (∀ a ≤ N, a ≠ 0 → gridWord a N = v.reverse) ∧
   (∀ b < N, b ≠ 0 → gridWord N b = (v.take (rightIdx b)).reverse) ∧
   (∀ a b, a < N → b < N →
    ∃ z_star ∈ ball (0 : Z) 1,
     jr (gridWord a b) z_star ∈ T0 ∧
     jr (gridWord (a + 1) b) z_star ∈ T0 ∧
     jr (gridWord (a + 1) (b + 1)) z_star ∈ T0 ∧
     jr (gridWord a (b + 1)) z_star ∈ T0) := by
 classical
 have hm : 0 < v.length := Nat.pos_of_ne_zero hv0;obtain ⟨m, hm_eq⟩ : ∃ m : ℕ, m = v.length := ⟨_, rfl⟩;let Kdom : Set (X × X) := Icc 0 1 ×ˢ Icc 0 1;have hKdom : IsCompact Kdom := isCompact_Icc.prod isCompact_Icc;let H : X × X → Z := fun p => (p.1 : Z) * kE v p.2
 have hH_cont : ContinuousOn H Kdom := by
  have h1 : ContinuousOn (fun p : X × X => (p.1 : Z)) Kdom :=
   (continuous_ofReal.comp continuous_fst).continuousOn
  have h2 : ContinuousOn (fun p : X × X => kE v p.2) Kdom :=
   (kK v).comp continuous_snd.continuousOn (fun _ hp => hp.2)
  exact h1.mul h2
 have hH_ball : ∀ p ∈ Kdom, H p ∈ ball (0 : Z) 1 := fun p hp => by
  have hγ := kJ v hp.2.1 hp.2.2
  rw [mem_ball, dist_zero_right] at hγ ⊢
  dsimp [H];rw [norm_mul, Complex.norm_of_nonneg hp.1.1];exact (mul_le_of_le_one_left (norm_nonneg _) hp.1.2).trans_lt hγ
 obtain ⟨p_max, hp_max_mem, hp_max⟩ := hKdom.exists_isMaxOn (⟨(0, 0), by simp only [Icc_prod_Icc,mem_Icc,Std.le_refl,Prod.mk_le_mk,zero_le_one,and_self,Kdom]⟩)
  (continuous_norm.comp_continuousOn hH_cont)
 obtain ⟨r, hr_eq⟩ : ∃ r : X, r = ‖H p_max‖ := ⟨_, rfl⟩
 have hr0 : 0 ≤ r := by rw [hr_eq];exact norm_nonneg _
 have hr1 : r < 1 := by
  rw [hr_eq];have := hH_ball p_max hp_max_mem;simpa [mem_ball, dist_zero_right] using this
 have hH_le_r : ∀ p ∈ Kdom, ‖H p‖ ≤ r := fun p hp => by rw [hr_eq];exact hp_max hp
 obtain ⟨F, hF⟩ := j3 hr0 hr1;obtain ⟨F_sym, hF_sym_eq⟩ : ∃ F_sym : Finset (List (Fin 3)), F_sym = F.image List.reverse := ⟨_, rfl⟩
 have htile_closed : ∀ g : List (Fin 3), IsClosed { z : Z | z ∈ ball (0 : Z) 1 ∧ jr g z ∈ T0 } := by
  intro g
  have heq : { z : Z | z ∈ ball (0 : Z) 1 ∧ jr g z ∈ T0 } = jr g.reverse '' T0 := by
   ext z;constructor
   ·
    rintro ⟨hz, hgz⟩;exact ⟨jr g z, hgz, jw g hz⟩
   ·
    rintro ⟨x, hx, rfl⟩
    refine ⟨jv g.reverse hx.1, ?_⟩
    have hc : jr g (jr g.reverse x) = x := by simpa [List.reverse_reverse] using jw g.reverse hx.1
    rw [hc];exact hx
  rw [heq]
  exact (kA.image_of_continuousOn
   ((kC g.reverse).mono (fun _ hx => hx.1))).isClosed
 let badUnion : X × X → Set Z := fun p =>
  ⋃ g ∈ (F_sym.filter fun g => ¬ (jr g (H p) ∈ T0)), { z : Z | z ∈ ball (0 : Z) 1 ∧ jr g z ∈ T0 }
 have hbad_closed : ∀ p : X × X, IsClosed (badUnion p) := fun p =>
  isClosed_biUnion_finset fun g _ => htile_closed g
 have hH_not_bad : ∀ p : X × X, H p ∉ badUnion p := by
  intro p hmem;simp only [badUnion,mem_iUnion,Finset.mem_filter,exists_prop] at hmem;obtain ⟨g, ⟨_, hnot⟩, _, hg⟩ := hmem;exact hnot hg
 have hloc : ∀ p ∈ Kdom, ∃ δ : X, 0 < δ ∧
   ∀ q ∈ Kdom, dist q p < δ → H q ∉ badUnion p := by
  intro p hp;have hopen : IsOpen ((badUnion p)ᶜ) := (hbad_closed p).isOpen_compl;obtain ⟨ε, hε, hball⟩ := isOpen_iff.1 hopen (H p) (hH_not_bad p);obtain ⟨δ, hδ, hcont⟩ := Metric.continuousOn_iff.1 hH_cont p hp ε hε;exact ⟨δ, hδ, fun q hq hqp => hball (hcont q hq hqp)⟩
 choose δ_fn hδ_pos hδ_prop using hloc
 let U_ball : X × X → Set (X × X) := fun p =>
  if hp : p ∈ Kdom then ball p (δ_fn p hp / 2) else ∅
 have hU_cov : Kdom ⊆ ⋃ p ∈ Kdom, U_ball p := fun p hp =>
  mem_biUnion hp (by simp only [hp,↓reduceDIte,mem_ball,dist_self,div_pos (hδ_pos p hp) two_pos,U_ball])
 obtain ⟨S_cov_set, hS_sub_set, hS_fin, hS_cov_set⟩ := hKdom.elim_finite_subcover_image
  (fun p _ => by by_cases hp : p ∈ Kdom <;> simp only [hp,↓reduceDIte,isOpen_ball,U_ball,isOpen_empty])
  hU_cov
 obtain ⟨S_cov, hS_cov_eq⟩ : ∃ S_cov : Finset (X × X), S_cov = hS_fin.toFinset := ⟨_, rfl⟩;have hS_sub : ↑S_cov ⊆ Kdom := fun p hp => hS_sub_set (hS_fin.mem_toFinset.1 (hS_cov_eq ▸ hp))
 have hS_cov : Kdom ⊆ ⋃ p ∈ S_cov, U_ball p := fun p hp => by
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.1 (hS_cov_set hp);exact mem_iUnion₂.2 ⟨q, hS_cov_eq ▸ hS_fin.mem_toFinset.2 hq, hpq⟩
 have hS_ne : S_cov.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have h0 : (0, 0) ∈ Kdom := by simp only [Icc_prod_Icc,mem_Icc,Std.le_refl,Prod.mk_le_mk,zero_le_one,and_self,Kdom]
  have := hS_cov h0;simp only [h,Finset.notMem_empty,iUnion_of_empty,iUnion_empty,mem_empty_iff_false] at this
 obtain ⟨δ, hδ_eq⟩ : ∃ δ : X, δ = S_cov.inf' hS_ne fun p => if hp : p ∈ Kdom then δ_fn p hp / 2 else 1 := ⟨_, rfl⟩
 have hδ_min_pos : 0 < δ := by
  rw [hδ_eq, Finset.lt_inf'_iff];intro p hp;have hpK := hS_sub hp;simp only [hpK,↓reduceDIte];exact div_pos (hδ_pos p hpK) two_pos
 obtain ⟨Knat, hKnat⟩ := exists_nat_gt (1 / δ);obtain ⟨K, hK_eq⟩ : ∃ K : ℕ, K = max 2 Knat := ⟨_, rfl⟩
 have hK2 : 2 ≤ K := by rw [hK_eq];exact le_max_left 2 Knat
 have hKδ : (1 : X) / K < δ := by
  have hKpos : (0 : X) < K := by positivity
  have hgt : 1 / δ < (K : X) := hKnat.trans_le (by rw [hK_eq];exact_mod_cast le_max_right 2 Knat)
  exact (div_lt_iff₀ hKpos).2 ((div_lt_iff₀ hδ_min_pos).1 hgt |>.trans_eq (mul_comm _ _))
 obtain ⟨N, hN_eq⟩ : ∃ N : ℕ, N = 2 * m * K := ⟨_, rfl⟩;have hm' : 0 < m := hm_eq ▸ hm
 have hK_pos : 0 < K := by omega
 have hN_pos : 0 < N := by rw [hN_eq];positivity
 have hNδ : (1 : X) / N < δ := by
  have hKN : K ≤ N := by
   rw [hN_eq];have : 1 ≤ 2 * m := by rw [hm_eq];omega
   nlinarith only [this]
  have hKpos : (0 : X) < K := by positivity
  have hNpos : (0 : X) < N := by positivity
  have h1 : (1 : X) / N ≤ 1 / K := one_div_le_one_div_of_le hKpos (by exact_mod_cast hKN)
  exact h1.trans_lt hKδ
 let rightIdx : ℕ → ℕ := kU v.length N K
 let gridWord : ℕ → ℕ → List (Fin 3) := fun a b =>
  if ha : a ≤ N then
   if hb : b ≤ N then
    if a = 0 then []
    else if b = 0 then []
    else if b = N then v.reverse
    else if a = N then (v.take (rightIdx b)).reverse
    else (j2 (H ((a : X) / N, (b : X) / N))
     (hH_ball _ ⟨⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      div_le_one_of_le₀ (by exact_mod_cast ha) (Nat.cast_nonneg _)⟩,
      ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      div_le_one_of_le₀ (by exact_mod_cast hb) (Nat.cast_nonneg _)⟩⟩)).choose
   else []
  else []
 have hgrid_mem : ∀ a b, a ≤ N → b ≤ N →
   jr (gridWord a b) (H ((a : X) / N, (b : X) / N)) ∈ T0 := by
  intro a b ha hb;dsimp [gridWord];rw [dif_pos ha, dif_pos hb]
  by_cases ha0 : a = 0
  · simp only [ha0,↓reduceIte,CharP.cast_eq_zero,zero_div,ofReal_zero,zero_mul,jr,qW qV,H]
  ·
   by_cases hb0 : b = 0
   · simp only [ha0,↓reduceIte,hb0,CharP.cast_eq_zero,zero_div,ofReal_div,ofReal_natCast,kL,mul_zero,jr,qW qV,H]
   ·
    by_cases hbN : b = N
    ·
     have hN0 : (N : X) ≠ 0 := Nat.cast_ne_zero.2 hN_pos.ne';simp only [ha0,hbN,hN_pos.ne',↓reduceIte,div_self hN0,H,kM];rw [hv 0 (mem_ball_self one_pos), mul_zero]
     have hrev0 : jr v.reverse 0 = 0 := by
      have := jw v (mem_ball_self one_pos);rwa [hv 0 (mem_ball_self one_pos)] at this
     rw [hrev0];exact qW qV
    ·
     by_cases haN : a = N
     ·
      have hN0 : (N : X) ≠ 0 := Nat.cast_ne_zero.2 hN_pos.ne';simp only [hb0,hbN,haN,hN_pos.ne',↓reduceIte,div_self hN0,ofReal_one,one_mul,H];exact kY v hv0 hK2 (hm_eq ▸ hN_eq) (Nat.lt_of_le_of_ne hb hbN)
     ·
      simp only [ha0,hb0,hbN,haN,↓reduceIte]
      exact (j2 (H ((a : X) / N, (b : X) / N))
       (hH_ball _ ⟨⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
        div_le_one_of_le₀ (by exact_mod_cast ha) (Nat.cast_nonneg _)⟩,
        ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
        div_le_one_of_le₀ (by exact_mod_cast hb) (Nat.cast_nonneg _)⟩⟩)).choose_spec
 have hcell_common : ∀ a b, a < N → b < N →
   ∃ z_star ∈ ball (0 : Z) 1,
    jr (gridWord a b) z_star ∈ T0 ∧
    jr (gridWord (a + 1) b) z_star ∈ T0 ∧
    jr (gridWord (a + 1) (b + 1)) z_star ∈ T0 ∧
    jr (gridWord a (b + 1)) z_star ∈ T0 := by
  intro a b ha hb
  have hK0 : ((a : X) / N, (b : X) / N) ∈ Kdom :=
   ⟨⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    div_le_one_of_le₀ (by exact_mod_cast ha.le) (Nat.cast_nonneg _)⟩,
    ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    div_le_one_of_le₀ (by exact_mod_cast hb.le) (Nat.cast_nonneg _)⟩⟩
  have hcov0 := hS_cov hK0;simp only [mem_iUnion,exists_prop] at hcov0;obtain ⟨p₀, hp₀, hp₀_ball⟩ := hcov0;have hp₀K := hS_sub hp₀;simp only [U_ball,hp₀K,↓reduceDIte,mem_ball] at hp₀_ball
  have hδp₀ : δ ≤ δ_fn p₀ hp₀K / 2 := by
   have := Finset.inf'_le (fun p => if hp : p ∈ Kdom then δ_fn p hp / 2 else 1) hp₀;rw [← hδ_eq] at this;simpa [hp₀K] using this
  have hcorner : ∀ a' b' (ha' : a' ≤ N) (hb' : b' ≤ N)
    (had : a' = a ∨ a' = a + 1) (hbd : b' = b ∨ b' = b + 1),
    jr (gridWord a' b') (H p₀) ∈ T0 := by
   intro a' b' ha' hb' had hbd;let q : X × X := ((a' : X) / N, (b' : X) / N)
   have hqK : q ∈ Kdom :=
    ⟨⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
     div_le_one_of_le₀ (by exact_mod_cast ha') (Nat.cast_nonneg _)⟩,
     ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
     div_le_one_of_le₀ (by exact_mod_cast hb') (Nat.cast_nonneg _)⟩⟩
   have hd_q0 : dist q ((a : X) / N, (b : X) / N) ≤ 1 / N := by
    rw [Prod.dist_eq, max_le_iff];have hNpos : (0 : X) < N := Nat.cast_pos.2 hN_pos;constructor
    ·
     rcases had with rfl | rfl
     · simp only [dist_self,one_div,inv_nonneg,Nat.cast_nonneg,q]
     ·
      rw [Real.dist_eq, show ((a + 1 : ℕ) : X) / N - (a : X) / N = 1 / N by push_cast;ring,
       abs_of_pos (one_div_pos.2 hNpos)]
    ·
     rcases hbd with rfl | rfl
     · simp only [dist_self,one_div,inv_nonneg,Nat.cast_nonneg,q]
     ·
      rw [Real.dist_eq, show ((b + 1 : ℕ) : X) / N - (b : X) / N = 1 / N by push_cast;ring,
       abs_of_pos (one_div_pos.2 hNpos)]
   have hd_qp : dist q p₀ < δ_fn p₀ hp₀K :=
    (dist_triangle q _ p₀).trans_lt (by linarith [hd_q0, hNδ, hδp₀, hp₀_ball])
   have hnotbad := hδ_prop p₀ hp₀K q hqK hd_qp;have hgm := hgrid_mem a' b' ha' hb';obtain ⟨g', hg'F, hg'eq⟩ := hF (gridWord a' b').reverse (jr (gridWord a' b') (H q)) hgm
    (by rw [jw _ (hH_ball q hqK)];exact hH_le_r q hqK)
   have hg_mem : jr g'.reverse (H p₀) ∈ T0 := by
    by_contra hnot
    apply hnotbad
    simp only [badUnion,mem_iUnion,Finset.mem_filter,exists_prop,mem_ofPred_eq]
    refine ⟨g'.reverse, ⟨hF_sym_eq ▸ Finset.mem_image_of_mem _ hg'F, hnot⟩, hH_ball q hqK, ?_⟩
    have hq_eq : jr g'.reverse (H q) = jr (gridWord a' b') (H q) := by
     have h1 : H q = jr g' (jr (gridWord a' b') (H q)) := by rw [← hg'eq _ hgm.1, jw _ (hH_ball q hqK)]
     calc jr g'.reverse (H q)
         = jr g'.reverse (jr g' (jr (gridWord a' b') (H q))) := by nth_rw 1 [h1]
       _ = jr (gridWord a' b') (H q) := jw g' hgm.1
    rw [hq_eq];exact hgm
   have hp_eq : jr (gridWord a' b') (H p₀) = jr g'.reverse (H p₀) := by
    have h1 : H p₀ = jr g' (jr (gridWord a' b') (H p₀)) := by rw [← hg'eq _ (jv _ (hH_ball p₀ hp₀K)), jw _ (hH_ball p₀ hp₀K)]
    calc jr (gridWord a' b') (H p₀)
        = jr g'.reverse (jr g' (jr (gridWord a' b') (H p₀))) :=
          (jw g' (jv _ (hH_ball p₀ hp₀K))).symm
      _ = jr g'.reverse (H p₀) := by rw [← h1]
   rw [hp_eq];exact hg_mem
  refine ⟨H p₀, hH_ball p₀ hp₀K, ?_, ?_, ?_, ?_⟩
  · exact hcorner a b ha.le hb.le (Or.inl rfl) (Or.inl rfl)
  · exact hcorner (a + 1) b ha hb.le (Or.inr rfl) (Or.inl rfl)
  · exact hcorner (a + 1) (b + 1) ha hb (Or.inr rfl) (Or.inr rfl)
  · exact hcorner a (b + 1) ha.le hb (Or.inl rfl) (Or.inr rfl)
 refine ⟨N, K, rightIdx, gridWord, hN_pos, hK2, hm_eq ▸ hN_eq,
  kV hN_pos, kW v.length N K,
  fun b hb => kX hK2 (hm_eq ▸ hN_eq) hb, ?_, ?_, ?_, ?_, hcell_common⟩
 · intro a ha;dsimp [gridWord];split_ifs;all_goals rfl
 · intro b hb;dsimp [gridWord];split_ifs;all_goals rfl
 · intro a ha ha0;dsimp [gridWord];rw [dif_pos ha, dif_pos le_rfl, if_neg ha0, if_neg hN_pos.ne', if_pos rfl]
 · intro b hb hb0;dsimp [gridWord];rw [dif_pos le_rfl, dif_pos hb.le, if_neg hN_pos.ne', if_neg hb0, if_neg hb.ne, if_pos rfl]
lemma k0 (v : List (Fin 3))
  (hv : ∀ z ∈ ball (0 : Z) 1, jr v z = z) :
  ∀ ζ : Z, js v ζ = ζ := by
 by_cases hv0 : v.length = 0
 ·
  have : v = [] := List.length_eq_zero_iff.1 hv0;subst this;intro ζ;rfl
 obtain ⟨N, K, rightIdx, gridWord, hN_pos, hK2, hN_eq, hrightIdx_zero, hrightIdx_N,
  hrightIdx_step, hgw_bot, hgw_left, hgw_top, hgw_right, hcell_common⟩ :=
  kZ v hv0 hv
 let E : (ℕ × ℕ) → (ℕ × ℕ) → Z → Z := fun p q =>
  js (kP (gridWord p.1 p.2) (gridWord q.1 q.2))
 have hE_square : ∀ a b, a < N → b < N → ∀ ζ : Z,
   E (a, b) (a + 1, b) (E (a + 1, b) (a + 1, b + 1) ζ) =
    E (a, b) (a, b + 1) (E (a, b + 1) (a + 1, b + 1) ζ) := by
  intro a b ha hb ζ;obtain ⟨z_star, hz, hw00, hw10, hw11, hw01⟩ := hcell_common a b ha hb;let x_star := jr (gridWord a b) z_star;have hx00 : jr (gridWord a b) z_star = x_star := rfl
  have hx10 : jr (gridWord (a + 1) b) z_star = x_star :=
   (kR hz hw10 hw00).1
  have hx11 : jr (gridWord (a + 1) (b + 1)) z_star = x_star :=
   (kR hz hw11 hw10).1.trans hx10
  have hx01 : jr (gridWord a (b + 1)) z_star = x_star :=
   (kR hz hw01 hw00).1
  have hinv01_00 : ∀ y : Z, E (a, b + 1) (a, b) (E (a, b) (a, b + 1) y) = y := by
   intro y;let el := [((a, b + 1), (a, b)), ((a, b), (a, b + 1))]
   have hev : ∀ u ∈ ball (0 : Z) 1,
     jr (el.flatMap fun e => kP (gridWord e.1.1 e.1.2) (gridWord e.2.1 e.2.2)) u = u := by
    intro u hu;simp only [el,List.flatMap_cons,List.flatMap_nil,List.append_nil,jt];have h1 := (kR hz hw01 hw00).2.1;have h2 := (kR hz hw00 hw01).2.1
    rw [← h2 _ hu, jt,
     ← h1 _ (jv _ (jv _ hu)), jt,
     jw _ (jv _ hu)]
    have hrev : jr (gridWord a (b + 1)) (jr (gridWord a (b + 1)).reverse u) = u := by simpa [List.reverse_reverse] using jw (gridWord a (b + 1)).reverse hu
    rw [hrev]
   have hres := kS (fun p : ℕ × ℕ => gridWord p.1 p.2) el hz hw00 (by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨hx01, hx00⟩
    · rcases List.mem_singleton.1 he with rfl;exact ⟨hx00, hx01⟩) hev y
   simpa [el, E, ju] using hres
  have hinv11_01 : ∀ y : Z, E (a + 1, b + 1) (a, b + 1) (E (a, b + 1) (a + 1, b + 1) y) = y := by
   intro y;let el := [((a + 1, b + 1), (a, b + 1)), ((a, b + 1), (a + 1, b + 1))]
   have hev : ∀ u ∈ ball (0 : Z) 1,
     jr (el.flatMap fun e => kP (gridWord e.1.1 e.1.2) (gridWord e.2.1 e.2.2)) u = u := by
    intro u hu;simp only [el,List.flatMap_cons,List.flatMap_nil,List.append_nil,jt];have h1 := (kR hz hw11 hw01).2.1;have h2 := (kR hz hw01 hw11).2.1
    rw [← h2 _ hu, jt,
     ← h1 _ (jv _ (jv _ hu)), jt,
     jw _ (jv _ hu)]
    simpa [List.reverse_reverse] using jw (gridWord (a + 1) (b + 1)).reverse hu
   have hres := kS (fun p : ℕ × ℕ => gridWord p.1 p.2) el hz hw00 (by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨hx11, hx01⟩
    · rcases List.mem_singleton.1 he with rfl;exact ⟨hx01, hx11⟩) hev y
   simpa [el, E, ju] using hres
  let sq_el := [((a, b), (a + 1, b)), ((a + 1, b), (a + 1, b + 1)),
         ((a + 1, b + 1), (a, b + 1)), ((a, b + 1), (a, b))]
  have hsq_ev𝔻 : ∀ u ∈ ball (0 : Z) 1,
    jr (sq_el.flatMap fun e => kP (gridWord e.1.1 e.1.2) (gridWord e.2.1 e.2.2)) u = u := by
   intro u hu;simp only [sq_el,List.flatMap_cons,List.flatMap_nil,List.append_nil,jt];have h1 := (kR hz hw00 hw10).2.1;have h2 := (kR hz hw10 hw11).2.1;have h3 := (kR hz hw11 hw01).2.1;have h4 := (kR hz hw01 hw00).2.1
   rw [← h4 _ hu, jt,
    ← h3 _ (jv _ (jv _ hu)), jt,
    jw _ (jv _ hu),
    ← h2 _ (jv _ (jv _ hu)), jt,
    jw _ (jv _ hu),
    ← h1 _ (jv _ (jv _ hu)), jt,
    jw _ (jv _ hu)]
   simpa [List.reverse_reverse] using jw (gridWord a b).reverse hu
  have hsq := kS (fun p : ℕ × ℕ => gridWord p.1 p.2) sq_el hz hw00 (by
   intro e he
   rcases List.mem_cons.1 he with rfl | he;exact ⟨hx00, hx10⟩
   rcases List.mem_cons.1 he with rfl | he;exact ⟨hx10, hx11⟩
   rcases List.mem_cons.1 he with rfl | he;exact ⟨hx11, hx01⟩
   rcases List.mem_singleton.1 he with rfl;exact ⟨hx01, hx00⟩) hsq_ev𝔻
   (E (a, b) (a, b + 1) (E (a, b + 1) (a + 1, b + 1) ζ))
  simp only [sq_el,List.flatMap_cons,List.flatMap_nil,List.append_nil,ju] at hsq
  change E (a, b) (a + 1, b) (E (a + 1, b) (a + 1, b + 1)
   (E (a + 1, b + 1) (a, b + 1) (E (a, b + 1) (a, b)
    (E (a, b) (a, b + 1) (E (a, b + 1) (a + 1, b + 1) ζ))))) =
   E (a, b) (a, b + 1) (E (a, b + 1) (a + 1, b + 1) ζ) at hsq
  rw [hinv01_00, hinv11_01] at hsq;exact hsq
 have hrc_one_col : ∀ n₁ a b, a + n₁ ≤ N → b < N → ∀ ζ : Z,
   kN E a n₁ b (kO E (a + n₁) b 1 ζ) =
    kO E a b 1 (kN E a n₁ (b + 1) ζ) := by
  intro n₁
  induction n₁ with
  | zero => intro a b _ _ ζ;simp only [kN,kO,add_zero]
  | succ k ih =>
   intro a b han hb ζ;simp only [kN,kO]
   have ha_lt : a < N := by omega
   have ih_step := ih (a + 1) b (by omega) hb ζ
   simp only [kO] at ih_step
   rw [show a + (k + 1) = a + 1 + k by omega]
   rw [ih_step, ← hE_square a b ha_lt hb]
 have hrc_comm : ∀ n₂ n₁ a b, a + n₁ ≤ N → b + n₂ ≤ N → ∀ ζ : Z,
   kN E a n₁ b (kO E (a + n₁) b n₂ ζ) =
    kO E a b n₂ (kN E a n₁ (b + n₂) ζ) := by
  intro n₂
  induction n₂ with
  | zero => intro n₁ a b _ _ ζ;simp only [kO,add_zero]
  | succ l ih =>
   intro n₁ a b han hbn ζ
   have hblt : b < N := by omega
   have h1 := ih n₁ a (b + 1) han (by omega) ζ
   have h2 := hrc_one_col n₁ a b han hblt (kO E (a + n₁) (b + 1) l ζ)
   simp only [kO] at h2 ⊢
   rw [h2, h1, show b + 1 + l = b + (l + 1) by omega]
 have h_edge_self : ∀ w : List (Fin 3), kP w w = [] := fun w =>
  kQ (by decide : [] ∈ jn) fun z hz => by
   rw [jt];change jr w (jr w.reverse z) = z;simpa [List.reverse_reverse] using jw w.reverse hz
 have h_bottom : ∀ ζ : Z, kN E 0 N 0 ζ = ζ := by
  intro ζ
  have haux : ∀ n a, a + n ≤ N → kN E a n 0 ζ = ζ := by
   intro n
   induction n with
   | zero => intro a _;rfl
   | succ k ih =>
    intro a han;simp only [kN,ih (a + 1) (by omega)]
    have hwa : gridWord a 0 = [] := hgw_bot a (by linarith)
    have hwa1 : gridWord (a + 1) 0 = [] := hgw_bot (a + 1) (by linarith)
    simp only [E,hwa,hwa1,h_edge_self,js]
  exact haux N 0 (by omega)
 have h_left : ∀ ζ : Z, kO E 0 0 N ζ = ζ := by
  intro ζ
  have haux : ∀ n b, b + n ≤ N → kO E 0 b n ζ = ζ := by
   intro n
   induction n with
   | zero => intro b _;rfl
   | succ k ih =>
    intro b hbn;simp only [kO,ih (b + 1) (by omega)]
    have hwb : gridWord 0 b = [] := hgw_left b (by linarith)
    have hwb1 : gridWord 0 (b + 1) = [] := hgw_left (b + 1) (by linarith)
    simp only [E,hwb,hwb1,h_edge_self,js]
  exact haux N 0 (by omega)
 have h_top : ∀ ζ : Z, kN E 0 N N ζ = ζ := by
  intro ζ
  have haux : ∀ n a, a + n ≤ N → kN E a n N ζ = ζ := by
   intro n
   induction n with
   | zero => intro a _ ;rfl
   | succ k ih =>
    intro a han;simp only [kN,ih (a + 1) (by omega)]
    have hwa : gridWord a N = (if a = 0 then [] else v.reverse) := by
     by_cases ha0 : a = 0
     · simp only [ha0,hgw_left N le_rfl,↓reduceIte]
     · simp only [hgw_top a (by linarith) ha0,ha0,↓reduceIte]
    have hwa1 : gridWord (a + 1) N = v.reverse :=
     hgw_top (a + 1) (by linarith) (Nat.succ_ne_zero a)
    have hev_id : ∀ z ∈ ball (0 : Z) 1, jr (gridWord a N ++ (gridWord (a + 1) N).reverse) z = z := by
     intro z hz;rw [hwa, hwa1]
     split_ifs
     · simp only [List.nil_append,List.reverse_reverse,hv z hz]
     ·
      simp only [jt,List.reverse_reverse];exact jw v hz
    have hed : kP (gridWord a N) (gridWord (a + 1) N) = [] :=
     kQ (by decide : [] ∈ jn) hev_id
    simp only [E,hed,js]
  exact haux N 0 (by omega)
 have h_right : ∀ ζ : Z, kO E N 0 N ζ = js v ζ := by
  have haux : ∀ n b, b + n = N → ∀ ζ : Z, kO E N b n ζ = js (v.drop (rightIdx b)) ζ := by
   intro n
   induction n with
   | zero =>
    intro b hb ζ
    have hbN : b = N := by omega
    subst hbN;rw [hrightIdx_N, List.drop_length];rfl
   | succ k ih =>
    intro b hb ζ
    have hblt : b < N := by omega
    simp only [kO,ih (b + 1) (by omega) ζ]
    have hwb : gridWord N b = (if b = 0 then [] else (v.take (rightIdx b)).reverse) := by
     by_cases hb0 : b = 0
     · simp only [hb0,hgw_bot N le_rfl,↓reduceIte]
     · simp only [hgw_right b hblt hb0,hb0,↓reduceIte]
    have hwb_ev𝔻 : ∀ u ∈ ball (0 : Z) 1, jr (gridWord N b) u = jr (v.take (rightIdx b)).reverse u := by
     intro u hu;rw [hwb];split_ifs with hb0
     · rw [hb0, hrightIdx_zero];rfl
     · rfl
    have hwb1_ev𝔻 : ∀ u ∈ ball (0 : Z) 1,
      jr (gridWord N (b + 1)).reverse u = jr (v.take (rightIdx (b + 1))) u := by
     intro u hu
     by_cases hb1N : b + 1 = N
     · rw [hb1N, hgw_top N le_rfl hN_pos.ne', hrightIdx_N, List.reverse_reverse, List.take_length]
     · rw [hgw_right (b + 1) (by omega) (Nat.succ_ne_zero b), List.reverse_reverse]
    rcases hrightIdx_step b hblt with hsame | ⟨hsucc, hrlt⟩
    ·
     have hev : ∀ u ∈ ball (0 : Z) 1,
       jr (gridWord N b ++ (gridWord N (b + 1)).reverse) u = jr [] u := by
      intro u hu
      rw [jt, hwb1_ev𝔻 u hu, hwb_ev𝔻 _ (jv _ hu), hsame,
       jw _ hu];rfl
     have hed : kP (gridWord N b) (gridWord N (b + 1)) = [] :=
      kQ (by decide : [] ∈ jn) hev
     simp only [E,hed,js,hsame]
    ·
     have hev : ∀ u ∈ ball (0 : Z) 1,
       jr (gridWord N b ++ (gridWord N (b + 1)).reverse) u = jr [v[rightIdx b]] u := by
      intro u hu
      rw [jt, hwb1_ev𝔻 u hu, hwb_ev𝔻 _ (jv _ hu), hsucc,
       List.take_succ_eq_append_getElem hrlt, jt,
       jw _ (jv _ hu)]
     have hed : kP (gridWord N b) (gridWord N (b + 1)) = [v[rightIdx b]] :=
      kQ (kT v[rightIdx b]) hev
     simp only [E,hed,js]
     rw [hsucc, ← show js (v[rightIdx b] :: v.drop (rightIdx b + 1)) ζ =
       qX v[rightIdx b] (js (v.drop (rightIdx b + 1)) ζ) from rfl,
      List.cons_getElem_drop_succ]
  intro ζ;have := haux N 0 (zero_add N) ζ;rwa [hrightIdx_zero, List.drop_zero] at this
 intro ζ;have hmain := hrc_comm N N 0 0 (zero_add N).le (zero_add N).le ζ;simp only [zero_add] at hmain;rw [h_bottom, h_left, h_top, h_right] at hmain;exact hmain
lemma k1 {w₁ w₂ : List (Fin 3)} {z : Z} (hz : z ∈ ball (0 : Z) 1)
  (hw1 : jr w₁ z ∈ T0) (hw2 : jr w₂ z ∈ T0) :
  jr w₁ z = jr w₂ z ∧
  ∃ w₀ ∈ jn,
   (∀ u ∈ ball (0 : Z) 1, jr (w₁ ++ w₂.reverse) u = jr w₀ u) ∧
   (∀ ζ : Z, js (w₁ ++ w₂.reverse) ζ = js w₀ ζ) ∧
   (w₀ = [] ∨
    (∃ i : Fin 3, w₀ = [i] ∧ W (jr w₂ z - qH i) = R2) ∨
    (∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ jr w₂ z = j5 k ∧ ∀ a ∈ w₀, a = i ∨ a = j)) := by
 have hcomp : jr (w₁ ++ w₂.reverse) (jr w₂ z) = jr w₁ z := by rw [jt, jw w₂ hz]
 obtain ⟨w₀, hw₀, heq⟩ := jW hw2 hw1 hcomp
 have hwx : jr w₀ (jr w₂ z) ∈ T0 := by rw [← heq _ hw2.1, hcomp];exact hw1
 obtain ⟨hfix, hcls⟩ := kk hw₀ hw2 hwx
 refine ⟨?_, w₀, hw₀, heq, ?_, hcls⟩
 · rw [← hcomp, heq _ hw2.1, hfix]
 ·
  intro ζ
  have hid : ∀ u ∈ ball (0 : Z) 1, jr ((w₁ ++ w₂.reverse) ++ w₀.reverse) u = u := by
   intro u hu;rw [jt, heq _ (jv _ hu)];simpa [List.reverse_reverse] using jw w₀.reverse hu
  have hc := k0 ((w₁ ++ w₂.reverse) ++ w₀.reverse) hid (js w₀ ζ);rw [ju, jx w₀ ζ] at hc;exact hc
end
end BlochAG
section
open _root_.Complex hiding sqrt Gamma sin cos
open Real Metric Set Filter Topology Function intervalIntegral MeasureTheory
namespace BlochAG
noncomputable section
lemma k2 : (0 : X) < 1 / 2 := by norm_num
lemma k3 : (0 : X) < 1 / 3 := by norm_num
lemma k4 : (0 : X) < 2 / 3 := by norm_num
lemma k5 : (0 : X) < 4 / 3 := by norm_num
lemma k6 : (0 : X) < 1 / 4 := by norm_num
lemma k7 : (0 : X) < 3 / 4 := by norm_num
lemma k8 : (0 : X) < 1 / 6 := by norm_num
lemma k9 : (0 : X) < 1 / 8 := by norm_num
lemma xc : (0 : X) < 3 / 8 := by norm_num
lemma xd : (0 : X) < 5 / 8 := by norm_num
lemma xe : (0 : X) < 7 / 8 := by norm_num
lemma xf : (0 : X) < 1 / 12 := by norm_num
lemma xg : (0 : X) < 5 / 12 := by norm_num
lemma xh : (0 : X) < 7 / 12 := by norm_num
lemma xi : (0 : X) < 11 / 12 := by norm_num
lemma xj : (0 : X) < 1 / 24 := by norm_num
lemma xk : (0 : X) < 13 / 24 := by norm_num
lemma xl : (0 : X) < 23 / 24 := by norm_num
lemma xm : (0 : X) < 25 / 24 := by norm_num
lemma xn : (0 : X) < 2 / 3 - 5 / 12 := by norm_num
lemma xo : (0 : X) < 2 / 3 - 1 / 12 - 5 / 12 := by norm_num
lemma xp : (0 : X) < 2 / 3 - 1 / 12 := by norm_num
lemma xq : (0 : X) ≤ 1 / 12 := by norm_num
lemma xr : (1 / 12 : X) < 1 := by norm_num
lemma xs : (0 : X) < 4 / 3 - 3 / 4 := by norm_num
lemma xt : (0 : X) < 4 / 3 - 5 / 12 - 3 / 4 := by norm_num
lemma xu : (0 : X) < 4 / 3 - 5 / 12 := by norm_num
lemma xv : (0 : X) ≤ 5 / 12 := by norm_num
lemma xw : (5 / 12 : X) < 1 := by norm_num
lemma xx : (0 : X) < 4 / 3 - 2 / 3 := by norm_num
lemma xy : (0 : X) < 4 / 3 - 1 / 3 - 2 / 3 := by norm_num
lemma xz : (0 : X) < 4 / 3 - 1 / 3 := by norm_num
lemma xA : (0 : X) ≤ 1 / 3 := by norm_num
lemma xB {x : X} (h : 0 < x) : Gamma x ≠ 0 := (gP h).ne'
lemma xC {x : X} (h : 0 < x) : (Gamma x : Z) ≠ 0 := ofReal_ne_zero.2 (xB h)
def xD (a b c : X) (s : Z) (t : X) : Z :=
 (t : Z) ^ ((b : Z) - 1) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1) *
  (1 - s * (t : Z)) ^ ((-a : Z))
def xE (a b c : X) (s : Z) : Z :=
 ((Gamma c / (Gamma b * Gamma (c - b)) : X) : Z) *
  ∫ t in (0 : X)..1, xD a b c s t
lemma xF {s : Z} (hs : ¬ (1 ≤ s.re ∧ s.im = 0))
  {t : X} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
  1 - s * (t : Z) ∈ slitPlane := by
 rw [mem_slitPlane_iff]
 by_cases him : (1 - s * (t : Z)).im = 0
 ·
  left
  have hsim : s.im * t = 0 := by
   have h0 := him
   simp only [sub_im, one_im, mul_im, ofReal_re, ofReal_im, mul_zero,
    zero_sub, neg_eq_zero] at h0
   linarith
  rcases mul_eq_zero.mp hsim with hsi | ht_zero
  ·
   have hsre : s.re < 1 := by
    by_contra hge
    push Not at hge;exact hs ⟨hge, hsi⟩
   simp only [sub_re,one_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
   by_cases h0 : 0 ≤ s.re <;> nlinarith only [h0, hsre, ht0, ht1]
  ·
   subst ht_zero;simp only [ofReal_zero,mul_zero,sub_zero,one_re,zero_lt_one]
 · right;exact him
lemma xG {s : Z} (hs : ‖s‖ ≤ 1)
  {t : X} (ht0 : 0 ≤ t) (ht1 : t < 1) :
  0 < (1 - s * (t : Z)).re := by
 have hsre : s.re ≤ 1 := le_trans (re_le_norm s) hs;simp only [sub_re,one_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero];nlinarith only [hsre, ht0, ht1]
lemma xH {K : Set Z} (hKc : IsCompact K)
  (hK : ∀ s ∈ K, ¬ (1 ≤ s.re ∧ s.im = 0)) :
  ∃ δ : X, 0 < δ ∧ ∀ s ∈ K, ∀ t ∈ Icc (0 : X) 1, δ ≤ ‖1 - s * (t : Z)‖ := by
 by_cases hne : K.Nonempty
 ·
  have hcomp : IsCompact (K ×ˢ Icc (0 : X) 1) := hKc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : Z × X => ‖1 - p.1 * (p.2 : Z)‖) (K ×ˢ Icc 0 1) :=
   ((continuous_const.sub (continuous_fst.mul (continuous_ofReal.comp continuous_snd))).norm).continuousOn
  obtain ⟨⟨s₀, t₀⟩, hp₀, hmin⟩ := hcomp.exists_isMinOn (hne.prod ⟨0, le_rfl, zero_le_one⟩) hcont
  have hne0 : 1 - s₀ * (t₀ : Z) ≠ 0 :=
   slitPlane_ne_zero (xF (hK s₀ hp₀.1) hp₀.2.1 hp₀.2.2)
  refine ⟨‖1 - s₀ * (t₀ : Z)‖, norm_pos_iff.mpr hne0, fun s hs t ht => ?_⟩
  exact hmin (show (s, t) ∈ K ×ˢ Icc 0 1 from ⟨hs, ht⟩)
 · exact ⟨1, one_pos, fun s hs => absurd ⟨s, hs⟩ hne⟩
lemma xI {b c : X} (hb : 0 < b) (hcb : 0 < c - b) :
  IntervalIntegrable (fun t : X => ‖(t : Z) ^ ((b : Z) - 1) *
   (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1)‖) volume 0 1 := by
 have h1 := Complex.betaIntegral_convergent (u := (b : Z)) (v := ((c - b : X) : Z))
  (by simpa using hb) (by simpa using hcb)
 simpa [sub_sub] using h1.norm
lemma xJ {a b c : X} (hb : 0 < b) (hcb : 0 < c - b)
  {s : Z} (hs : ¬ (1 ≤ s.re ∧ s.im = 0)) :
  IntervalIntegrable (xD a b c s) volume 0 1 := by
 have hcont : ContinuousOn (fun t : X => (1 - s * (t : Z)) ^ ((-a : Z))) (uIcc 0 1) := by
  rw [uIcc_of_le zero_le_one];intro t ht
  refine (ContinuousAt.cpow (continuous_const.sub (continuous_const.mul continuous_ofReal)).continuousAt continuousAt_const ?_).continuousWithinAt
  exact xF hs ht.1 ht.2
 have hbeta := Complex.betaIntegral_convergent (u := (b : Z)) (v := ((c - b : X) : Z))
  (by simpa using hb) (by simpa using hcb)
 have hbeta' : IntervalIntegrable (fun x : X =>
   (x : Z) ^ ((b : Z) - 1) * (1 - (x : Z)) ^ ((c : Z) - (b : Z) - 1)) volume 0 1 := by
  simpa [sub_sub] using hbeta
 exact hbeta'.mul_continuousOn hcont
lemma xK {a b c : X} (hb : 0 < b) (hcab : 0 < c - a - b) :
  IntervalIntegrable (xD a b c 1) volume 0 1 := by
 have hbeta := Complex.betaIntegral_convergent (u := (b : Z)) (v := ((c - a - b : X) : Z))
  (by simpa using hb) (by simpa using hcab)
 have heq : (fun x : X => (x : Z) ^ ((b : Z) - 1) * (1 - (x : Z)) ^ (((c - a - b : X) : Z) - 1)) =ᵐ[volume.restrict (Ioc 0 1)]
   xD a b c 1 := by
  have hne1 : ∀ᵐ t : X ∂volume, t ≠ 1 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne1] with t ht ht1_ne
  have ht1 : 0 < 1 - t := sub_pos.2 (lt_of_le_of_ne ht.2 ht1_ne)
  have ht1c : (1 : Z) - (t : Z) = ((1 - t : X) : Z) := by push_cast;rfl
  have hne : ((1 - t : X) : Z) ≠ 0 := ofReal_ne_zero.2 ht1.ne';simp only [xD,one_mul,ht1c,mul_assoc];congr 1;rw [← cpow_add _ _ hne];congr 1;push_cast;ring
 have h1 : IntegrableOn (xD a b c 1) (Ioc 0 1) volume :=
  Integrable.congr hbeta.1 heq
 rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one];exact h1
lemma xL {a b c : X} (hb : 0 < b) (hcb : 0 < c - b) (hc : 0 < c) :
  xE a b c 0 = 1 := by
 dsimp [xE]
 have heq : (∫ t in (0 : X)..1, xD a b c 0 t) =
   betaIntegral (b : Z) ((c : Z) - (b : Z)) := by
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [xD,sub_sub,zero_mul,sub_zero,one_cpow,mul_one]
 rw [heq];have hbg := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (b : Z)) (t := (c : Z) - (b : Z))
  (by simpa using hb) (by simpa using hcb)
 have hbc : (b : Z) + ((c : Z) - (b : Z)) = (c : Z) := by ring
 rw [hbc, show (c : Z) - (b : Z) = ((c - b : X) : Z) by push_cast;rfl,
  Gamma_ofReal, Gamma_ofReal, Gamma_ofReal] at hbg
 have hGbC : (Gamma b : Z) ≠ 0 := ofReal_ne_zero.2 (gP hb).ne';have hGcbC : (Gamma (c - b) : Z) ≠ 0 := ofReal_ne_zero.2 (gP hcb).ne';have hGcC : (Gamma c : Z) ≠ 0 := ofReal_ne_zero.2 (gP hc).ne';push_cast;field_simp [hGcC, hGbC, hGcbC]
 rw [show ((c - b : X) : Z) = (c : Z) - (b : Z) by push_cast;rfl] at hbg
 linear_combination -hbg
lemma xM {a b c : X} (hb : 0 < b) (hcb : 0 < c - b) (hcab : 0 < c - a - b)
  (hca : 0 < c - a) :
  xE a b c 1 =
   ((Gamma c * Gamma (c - a - b) /
    (Gamma (c - a) * Gamma (c - b)) : X) : Z) := by
 dsimp [xE]
 have heq : (∫ t in (0 : X)..1, xD a b c 1 t) =
   betaIntegral (b : Z) ((c : Z) - (a : Z) - (b : Z)) := by
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ t ∂volume, t ≠ (1 : X) := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
  filter_upwards [hne] with t htne ht
  rw [uIoc_of_le zero_le_one] at ht;have ht1 : 0 < 1 - t := sub_pos.2 (lt_of_le_of_ne ht.2 htne)
  have ht1c : (1 : Z) - (t : Z) = ((1 - t : X) : Z) := by push_cast;rfl
  have hne' : ((1 - t : X) : Z) ≠ 0 := ofReal_ne_zero.2 ht1.ne';simp only [xD,one_mul,ht1c,mul_assoc];congr 1;rw [← cpow_add _ _ hne'];congr 1;ring
 rw [heq];have hbg := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (b : Z)) (t := (c : Z) - (a : Z) - (b : Z))
  (by simpa using hb) (by simpa using hcab)
 have hba : (b : Z) + ((c : Z) - (a : Z) - (b : Z)) = ((c - a : X) : Z) := by push_cast;ring
 rw [hba, show (c : Z) - (a : Z) - (b : Z) = ((c - a - b : X) : Z) by push_cast;rfl,
  Gamma_ofReal, Gamma_ofReal, Gamma_ofReal] at hbg
 have hGb : (Gamma b : Z) ≠ 0 := ofReal_ne_zero.2 (gP hb).ne';have hGcb : (Gamma (c - b) : Z) ≠ 0 := ofReal_ne_zero.2 (gP hcb).ne';have hGca : (Gamma (c - a) : Z) ≠ 0 := ofReal_ne_zero.2 (gP hca).ne';push_cast;field_simp [hGb, hGcb, hGca]
 rw [show ((c - a - b : X) : Z) = (c : Z) - (a : Z) - (b : Z) by push_cast;rfl] at hbg
 linear_combination -(Gamma c : Z) * hbg
def xN : Set Z := { s : Z | ¬ (1 ≤ s.re ∧ s.im = 0) }
lemma xO : IsOpen xN := by
 have heq : xN = (fun s : Z => 1 - s) ⁻¹' slitPlane := by
  ext s
  simp only [xN, Set.mem_ofPred, mem_preimage, mem_slitPlane_iff, sub_re, one_re,
   sub_im, one_im, zero_sub, sub_pos, not_and]
  constructor <;> intro h
  ·
   by_cases hre : 1 ≤ s.re
   · exact Or.inr (neg_ne_zero.mpr (h hre))
   · exact Or.inl (lt_of_not_ge hre)
  ·
   intro hre
   rcases h with hlt | hne
   · linarith
   · exact fun him => hne (by simp only [him,neg_zero])
 rw [heq];exact Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)
lemma xP : ball (0 : Z) 1 ⊆ xN := by
 intro s hs h;rw [mem_ball, dist_zero_right] at hs;have := le_trans h.1 (re_le_norm s);linarith
lemma xQ {a b c : X} (hb : 0 < b) (hcb : 0 < c - b)
  (hcab : 0 < c - a - b) {s : Z} (hs : ‖s‖ ≤ 1) :
  IntervalIntegrable (xD a b c s) volume 0 1 := by
 by_cases hs1 : s = 1
 · subst hs1;exact xK hb hcab
 ·
  refine xJ hb hcb fun ⟨hre, him⟩ => hs1 ?_
  have hre1 : s.re ≤ 1 := le_trans (re_le_norm s) hs;exact Complex.ext (le_antisymm hre1 hre) him
lemma xR {a b c : X} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 < b) (hcb : 0 < c - b)
  (hcab : 0 < c - a - b) (hc : 0 < c) {s : Z} (hs : ‖s‖ ≤ 1) :
  0 < (xE a b c s).re := by
 have hint : IntervalIntegrable (xD a b c s) volume 0 1 :=
  xQ hb hcb hcab hs
 have hpre_pos : 0 < Gamma c / (Gamma b * Gamma (c - b)) :=
  div_pos (gP hc) (mul_pos (gP hb) (gP hcb))
 dsimp [xE];rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
 refine mul_pos hpre_pos ?_
 have hre_int : (∫ t in (0 : X)..1, xD a b c s t).re =
   ∫ t in (0 : X)..1, (xD a b c s t).re :=
  (reCLM.intervalIntegral_comp_comm hint).symm
 rw [hre_int, integral_of_le zero_le_one];rw [integral_Ioc_eq_integral_Ioo]
 have hre_pos_on : ∀ t ∈ Ioo (0 : X) 1, 0 < (xD a b c s t).re := by
  intro t ht;have ht0 : 0 < t := ht.1;have ht1 : 0 < 1 - t := sub_pos.2 ht.2
  have h1t : (1 : Z) - (t : Z) = ((1 - t : X) : Z) := by push_cast;rfl
  have hw_re : 0 < (1 - s * (t : Z)).re := xG hs ht0.le ht.2
  have hw_ne : 1 - s * (t : Z) ≠ 0 := by intro h;rw [h, zero_re] at hw_re;linarith
  have harg : |Complex.arg (1 - s * (t : Z))| < π / 2 :=
   abs_arg_lt_pi_div_two_iff.2 (Or.inl hw_re)
  have hcp : ((1 - s * (t : Z)) ^ (-a : Z)).re =
    ‖1 - s * (t : Z)‖ ^ (-a) * cos (-a * Complex.arg (1 - s * (t : Z))) := by
   rw [cpow_def_of_ne_zero hw_ne, exp_re]
   simp only [mul_re, mul_im, log_re, log_im, ofReal_re,
    ofReal_im, neg_re, neg_im, neg_zero, mul_zero, sub_zero]
   rw [rpow_def_of_pos (norm_pos_iff.2 hw_ne)];ring_nf
  have hcos : 0 < cos (-a * Complex.arg (1 - s * (t : Z))) := by
   refine Real.cos_pos_of_mem_Ioo ?_
   have hbd : |(-a) * Complex.arg (1 - s * (t : Z))| < π / 2 := by
    rw [abs_mul, abs_neg, abs_of_nonneg ha0]
    rcases eq_or_lt_of_le ha0 with rfl | ha_pos
    · simp only [zero_mul,pi_pos,div_pos_iff_of_pos_left,Nat.ofNat_pos]
    ·
     calc a * |Complex.arg (1 - s * (t : Z))|
          < 1 * (π / 2) := mul_lt_mul' ha1.le harg (abs_nonneg _) one_pos
        _ = π / 2 := one_mul _
   exact abs_lt.1 hbd
  have hcp_pos : 0 < ((1 - s * (t : Z)) ^ (-a : Z)).re := by
   rw [hcp];exact mul_pos (rpow_pos_of_pos (norm_pos_iff.2 hw_ne) _) hcos
  have hbase : (t : Z) ^ ((b : Z) - 1) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1) =
    ((t ^ (b - 1) * (1 - t) ^ (c - b - 1) : X) : Z) := by
   rw [h1t, show (b : Z) - 1 = ((b - 1 : X) : Z) by push_cast;rfl,
    show (c : Z) - (b : Z) - 1 = ((c - b - 1 : X) : Z) by push_cast;rfl,
    ← ofReal_cpow ht0.le, ← ofReal_cpow ht1.le, ofReal_mul]
  have hbase_pos : 0 < t ^ (b - 1) * (1 - t) ^ (c - b - 1) :=
   mul_pos (rpow_pos_of_pos ht0 _) (rpow_pos_of_pos ht1 _)
  dsimp [xD];rw [hbase, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero];exact mul_pos hbase_pos hcp_pos
 have hint_re : IntegrableOn (fun t : X => (xD a b c s t).re) (Ioo 0 1) volume :=
  (reCLM.integrable_comp hint.1).mono_measure
   (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
 rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae ?_ hint_re]
 ·
  have hsup : Ioo (0 : X) 1 ⊆ Function.support (fun t : X => (xD a b c s t).re) :=
   fun t ht => (hre_pos_on t ht).ne'
  have hpos : (0 : ENNReal) < volume (Ioo (0 : X) 1) := by simp only [volume_Ioo,sub_zero,ENNReal.ofReal_one,zero_lt_one]
  exact lt_of_lt_of_le hpos (measure_mono (subset_inter hsup Subset.rfl))
 ·
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (hre_pos_on t ht).le
lemma xS {a b c : X} {s : Z} (hs : s ∈ xN)
  {t : X} (ht0 : 0 < t) (ht1 : t < 1) :
  HasDerivAt (fun w : Z => xD a b c w t)
   (a * xD (a + 1) (b + 1) (c + 1) s t) s := by
 have hslit : 1 - s * (t : Z) ∈ slitPlane :=
  xF hs ht0.le ht1.le
 have h1 : HasDerivAt (fun w : Z => 1 - w * (t : Z)) (-(t : Z)) s := by simpa using ((hasDerivAt_id s).mul_const (t : Z)).const_sub 1
 have hcp : HasDerivAt (fun w : Z => (1 - w * (t : Z)) ^ (-a : Z))
   ((-a : Z) * (1 - s * (t : Z)) ^ ((-a : Z) - 1) * -(t : Z)) s := by
  refine (h1.cpow (hasDerivAt_const s (-a : Z)) hslit).congr_deriv ?_
  simp only [neg_mul,mul_neg,neg_neg,mul_zero,add_zero]
 have hmul : HasDerivAt (fun w : Z => xD a b c w t)
   ((t : Z) ^ ((b : Z) - 1) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1) *
    ((-a : Z) * (1 - s * (t : Z)) ^ ((-a : Z) - 1) * -(t : Z))) s :=
  hcp.const_mul _
 refine hmul.congr_deriv ?_
 have ht_ne : (t : Z) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
 have htp : (t : Z) ^ (((b + 1 : X) : Z) - 1) = (t : Z) ^ ((b : Z) - 1) * (t : Z) := by
  have heq : (((b + 1 : X) : Z) - 1) = ((b : Z) - 1) + 1 := by push_cast;ring
  rw [heq, cpow_add _ _ ht_ne, cpow_one]
 dsimp [xD]
 rw [htp, show ((c + 1 : X) : Z) - ((b + 1 : X) : Z) - 1 = (c : Z) - (b : Z) - 1 by push_cast;ring,
  show (-(a + 1 : X) : Z) = (-a : Z) - 1 by push_cast;ring]
 ring
lemma xT {a b c : X} (hb : 0 < b) (hcb : 0 < c - b) (hc : 0 < c)
  {s : Z} (hs : s ∈ xN) :
  HasDerivAt (xE a b c) ((a * b / c : X) * xE (a + 1) (b + 1) (c + 1) s) s := by
 obtain ⟨r, hr_pos, hr_sub⟩ := isOpen_iff.1 xO s hs;have hcomp : IsCompact (closedBall s (r / 2)) := isCompact_closedBall s (r / 2)
 have hcb_sub : closedBall s (r / 2) ⊆ xN :=
  (closedBall_subset_ball (half_lt_self hr_pos)).trans hr_sub
 obtain ⟨δ, hδ_pos, hδ⟩ := xH hcomp (fun w hw => hcb_sub hw);let F : Z → X → Z := fun w t => xD a b c w t;let F' : Z → X → Z := fun w t => (a : Z) * xD (a + 1) (b + 1) (c + 1) w t;let M0 : X := max (δ ^ (-a - 1)) ((1 + (‖s‖ + r / 2)) ^ (-a - 1));let M : X := |a| * M0;let bound : X → X := fun t => M * ‖(t : Z) ^ ((b : Z) - 1) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1)‖
 have hF_meas : ∀ᶠ w in 𝓝 s, AEStronglyMeasurable (F w) (volume.restrict (uIoc 0 1)) := by
  rw [uIoc_of_le zero_le_one]
  filter_upwards [ball_mem_nhds s (half_pos hr_pos)] with w hw
  exact (xJ (a := a) (b := b) (c := c) hb hcb
   (hr_sub (ball_subset_ball (half_le_self hr_pos.le) hw))).1.1
 have hF_int : IntervalIntegrable (F s) volume 0 1 := xJ hb hcb hs
 have hF'_int : IntervalIntegrable (F' s) volume 0 1 := by
  refine (xJ (a := a + 1) (b := b + 1) (c := c + 1)
   (by linarith) (by linarith) hs).const_mul (a : Z)
 have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (uIoc 0 1)) := by rw [uIoc_of_le zero_le_one];exact hF'_int.1.1
 have h_bound : ∀ᵐ t ∂volume, t ∈ uIoc (0 : X) 1 → ∀ w ∈ closedBall s (r / 2), ‖F' w t‖ ≤ bound t := by
  have hne0 : ∀ᵐ t : X ∂volume, t ≠ 0 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
  have hne1 : ∀ᵐ t : X ∂volume, t ≠ 1 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
  filter_upwards [hne0, hne1] with t ht0_ne ht1_ne ht w hw
  rw [uIoc_of_le zero_le_one] at ht;have ht0 : 0 < t := lt_of_le_of_ne ht.1.le (Ne.symm ht0_ne);have ht1 : t < 1 := lt_of_le_of_ne ht.2 ht1_ne;have hnw : δ ≤ ‖1 - w * (t : Z)‖ := hδ w hw t ⟨ht0.le, ht1.le⟩
  have hw_ne : 1 - w * (t : Z) ≠ 0 := by intro h0;rw [h0, norm_zero] at hnw;linarith
  have hle1 : ‖1 - w * (t : Z)‖ ≤ 1 + (‖s‖ + r / 2) := by
   have hw_le : ‖w‖ ≤ ‖s‖ + r / 2 := by
    rw [mem_closedBall, dist_eq_norm] at hw
    calc ‖w‖ = ‖(w - s) + s‖ := by ring_nf
      _ ≤ ‖w - s‖ + ‖s‖ := norm_add_le _ _
      _ ≤ r / 2 + ‖s‖ := add_le_add hw le_rfl
      _ = ‖s‖ + r / 2 := add_comm _ _
   calc ‖1 - w * (t : Z)‖ ≤ ‖(1 : Z)‖ + ‖w * (t : Z)‖ := norm_sub_le _ _
     _ = 1 + ‖w‖ * |t| := by simp only [norm_one,Complex.norm_mul,norm_real,norm_eq_abs]
     _ ≤ 1 + (‖s‖ + r / 2) * 1 := by gcongr;rw [abs_of_pos ht0];exact ht1.le
     _ = 1 + (‖s‖ + r / 2) := by ring
  have hcp_norm : ‖(1 - w * (t : Z)) ^ (-(a + 1 : X) : Z)‖ ≤ M0 := by
   have hre : ‖(1 - w * (t : Z)) ^ (-(a + 1 : X) : Z)‖ = ‖1 - w * (t : Z)‖ ^ (-a - 1) := by
    rw [cpow_def_of_ne_zero hw_ne, Complex.norm_exp, rpow_def_of_pos (norm_pos_iff.2 hw_ne)]
    simp only [mul_re, log_re, log_im, neg_re, neg_im,
     ofReal_re, ofReal_im, neg_zero]
    congr 1;ring
   rw [hre]
   by_cases hsign : -a - 1 ≤ 0
   · exact (Real.rpow_le_rpow_of_nonpos hδ_pos hnw hsign).trans (le_max_left _ _)
   ·
    push Not at hsign;exact (rpow_le_rpow (norm_nonneg _) hle1 hsign.le).trans (le_max_right _ _)
  have htp : (t : Z) ^ (((b + 1 : X) : Z) - 1) = (t : Z) ^ ((b : Z) - 1) * (t : Z) := by
   have ht_ne : (t : Z) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
   rw [show (((b + 1 : X) : Z) - 1) = ((b : Z) - 1) + 1 by push_cast;ring,
    cpow_add _ _ ht_ne, cpow_one]
  have ht_le : ‖(t : Z)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg ht0.le];exact ht1.le
  dsimp [F', xD, bound, M]
  rw [show ((c + 1 : X) : Z) - ((b + 1 : X) : Z) - 1 = (c : Z) - (b : Z) - 1 by push_cast;ring,
   htp, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hprod_norm : ‖(t : Z) ^ ((b : Z) - 1) * (t : Z) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1) *
     (1 - w * (t : Z)) ^ (-(a + 1 : X) : Z)‖ =
    ‖(t : Z) ^ ((b : Z) - 1) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1)‖ *
     ‖(t : Z)‖ * ‖(1 - w * (t : Z)) ^ (-(a + 1 : X) : Z)‖ := by
   rw [show (t : Z) ^ ((b : Z) - 1) * (t : Z) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1) *
      (1 - w * (t : Z)) ^ (-(a + 1 : X) : Z) =
     ((t : Z) ^ ((b : Z) - 1) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1)) * (t : Z) *
      (1 - w * (t : Z)) ^ (-(a + 1 : X) : Z) by ring, norm_mul, norm_mul]
  calc |a| * ‖(t : Z) ^ ((b : Z) - 1) * (t : Z) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1) *
        (1 - w * (t : Z)) ^ (-(a + 1 : X) : Z)‖
      = |a| * (‖(t : Z) ^ ((b : Z) - 1) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1)‖ *
          ‖(t : Z)‖ * ‖(1 - w * (t : Z)) ^ (-(a + 1 : X) : Z)‖) := by rw [hprod_norm]
    _ ≤ |a| * (‖(t : Z) ^ ((b : Z) - 1) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1)‖ * 1 * M0) := by gcongr
    _ = |a| * M0 * ‖(t : Z) ^ ((b : Z) - 1) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1)‖ := by ring
 have h_bound_int : IntervalIntegrable bound volume 0 1 :=
  (xI hb hcb).const_mul M
 have h_diff : ∀ᵐ t ∂volume, t ∈ uIoc (0 : X) 1 → ∀ w ∈ closedBall s (r / 2),
   HasDerivAt (fun x => F x t) (F' w t) w := by
  have hne0 : ∀ᵐ t : X ∂volume, t ≠ 0 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
  have hne1 : ∀ᵐ t : X ∂volume, t ≠ 1 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
  filter_upwards [hne0, hne1] with t ht0_ne ht1_ne ht w hw
  rw [uIoc_of_le zero_le_one] at ht;exact xS (hcb_sub hw) (lt_of_le_of_ne ht.1.le (Ne.symm ht0_ne))
   (lt_of_le_of_ne ht.2 ht1_ne)
 have h_int_deriv := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
  (closedBall_mem_nhds s (half_pos hr_pos)) hF_meas hF_int hF'_meas
  h_bound h_bound_int h_diff).2
 have hconst := h_int_deriv.const_mul
  ((Gamma c / (Gamma b * Gamma (c - b)) : X) : Z)
 refine hconst.congr_deriv ?_
 have h_pull : (∫ t in (0 : X)..1, F' s t) =
   (a : Z) * ∫ t in (0 : X)..1, xD (a + 1) (b + 1) (c + 1) s t :=
  intervalIntegral.integral_const_mul (a : Z) _
 dsimp [xE];rw [h_pull];have hGb : Gamma b ≠ 0 := (gP hb).ne';have hGc : Gamma c ≠ 0 := (gP hc).ne';have hGcb : Gamma (c - b) ≠ 0 := (gP hcb).ne';have hGbc : Gamma (b + 1) = b * Gamma b := Real.Gamma_add_one hb.ne';have hGcc : Gamma (c + 1) = c * Gamma c := Real.Gamma_add_one hc.ne'
 have heqc : ((c + 1 : X) - (b + 1 : X)) = c - b := by ring
 rw [heqc, hGbc, hGcc];push_cast;have hGbC : (Gamma b : Z) ≠ 0 := ofReal_ne_zero.2 hGb;have hGcC : (Gamma c : Z) ≠ 0 := ofReal_ne_zero.2 hGc;have hGcbC : (Gamma (c - b) : Z) ≠ 0 := ofReal_ne_zero.2 hGcb;have hbC : (b : Z) ≠ 0 := ofReal_ne_zero.2 hb.ne';have hcC : (c : Z) ≠ 0 := ofReal_ne_zero.2 hc.ne';field_simp [hGbC, hGcC, hGcbC, hbC, hcC]
lemma xU {a b c : X} (hb : 0 < b) (hcb : 0 < c - b) (hc : 0 < c)
  {s : Z} (hs : s ∈ xN) :
  HasDerivAt (deriv (xE a b c))
   (((a * b / c) * ((a + 1) * (b + 1) / (c + 1)) : X) *
    xE (a + 2) (b + 2) (c + 2) s) s := by
 have h1 : ∀ᶠ w in 𝓝 s, deriv (xE a b c) w =
   ((a * b / c : X) : Z) * xE (a + 1) (b + 1) (c + 1) w := by
  filter_upwards [xO.mem_nhds hs] with w hw
  exact (xT hb hcb hc hw).deriv
 have h2 := (xT (a := a + 1) (b := b + 1) (c := c + 1)
  (by linarith) (by linarith) (by linarith) hs).const_mul ((a * b / c : X) : Z)
 refine (h2.congr_of_eventuallyEq h1).congr_deriv ?_
 push_cast;ring_nf
lemma xV {a b c : X} (hb : 0 < b) (hcb : 0 < c - b) (hc : 0 < c)
  {s : Z} (hs : s ∈ xN) :
  s * (1 - s) * deriv (deriv (xE a b c)) s +
   ((c : Z) - ((a + b + 1 : X) : Z) * s) * deriv (xE a b c) s -
   ((a * b : X) : Z) * xE a b c s = 0 := by
 rw [(xT hb hcb hc hs).deriv, (xU hb hcb hc hs).deriv]
 have hpre : Gamma c / (Gamma b * Gamma (c - b)) ≠ 0 := by
  have := gP hc;have := gP hb;have := gP hcb;positivity
 have hGbc : Gamma (b + 1) = b * Gamma b := Real.Gamma_add_one hb.ne';have hGcc : Gamma (c + 1) = c * Gamma c := Real.Gamma_add_one hc.ne'
 have hGbc2 : Gamma (b + 2) = (b + 1) * b * Gamma b := by rw [show b + 2 = (b + 1) + 1 by ring, Real.Gamma_add_one (by linarith), hGbc];ring
 have hGcc2 : Gamma (c + 2) = (c + 1) * c * Gamma c := by rw [show c + 2 = (c + 1) + 1 by ring, Real.Gamma_add_one (by linarith), hGcc];ring
 have hGbC : (Gamma b : Z) ≠ 0 := ofReal_ne_zero.2 (gP hb).ne';have hGcC : (Gamma c : Z) ≠ 0 := ofReal_ne_zero.2 (gP hc).ne';have hGcbC : (Gamma (c - b) : Z) ≠ 0 := ofReal_ne_zero.2 (gP hcb).ne';have hbC : (b : Z) ≠ 0 := ofReal_ne_zero.2 hb.ne';have hcC : (c : Z) ≠ 0 := ofReal_ne_zero.2 hc.ne'
 have hb1C : ((b + 1 : X) : Z) ≠ 0 := ofReal_ne_zero.2 (by linarith)
 have hc1C : ((c + 1 : X) : Z) ≠ 0 := ofReal_ne_zero.2 (by linarith)
 have hint0 := xJ (a := a) (b := b) (c := c) hb hcb hs;have hint1 := xJ (a := a + 1) (b := b + 1) (c := c + 1)
  (by linarith) (by linarith) hs
 have hint2 := xJ (a := a + 2) (b := b + 2) (c := c + 2)
  (by linarith) (by linarith) hs
 let P : X → Z := fun t =>
  (t : Z) ^ (b : Z) * (1 - (t : Z)) ^ ((c : Z) - (b : Z)) * (1 - s * (t : Z)) ^ (-(a + 1 : X) : Z)
 let P' : X → Z := fun t =>
  (t : Z) ^ ((b : Z) - 1) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1) *
   (1 - s * (t : Z)) ^ (-(a + 2 : X) : Z) *
   ((b : Z) * (1 - (t : Z)) * (1 - s * (t : Z)) -
    ((c : Z) - (b : Z)) * (t : Z) * (1 - s * (t : Z)) +
    ((a + 1 : X) : Z) * s * (t : Z) * (1 - (t : Z)))
 have hP_deriv : ∀ t ∈ Ioo (0 : X) 1, HasDerivAt P (P' t) t := by
  intro t ht;have ht0 : (0 : X) < t := ht.1;have ht1 : (0 : X) < 1 - t := sub_pos.2 ht.2;have htc : (t : Z) ∈ slitPlane := Complex.ofReal_mem_slitPlane.2 ht0
  have h1tc : (1 - (t : Z)) ∈ slitPlane := by
   rw [show (1 : Z) - (t : Z) = ((1 - t : X) : Z) by push_cast;rfl]
   exact Complex.ofReal_mem_slitPlane.2 ht1
  have hstc : 1 - s * (t : Z) ∈ slitPlane :=
   xF hs ht0.le ht.2.le
  have d1 : HasDerivAt (fun x : X => (x : Z) ^ (b : Z)) ((b : Z) * (t : Z) ^ ((b : Z) - 1)) t := by
   have := (Complex.hasStrictDerivAt_cpow_const (c := (b : Z)) htc).hasDerivAt.comp_ofReal;simpa using this
  have d2 : HasDerivAt (fun x : X => (1 - (x : Z)) ^ ((c : Z) - (b : Z)))
    (((c : Z) - (b : Z)) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1) * (-1)) t := by
   have hsub : HasDerivAt (fun x : X => 1 - (x : Z)) (-1) t :=
    ((hasDerivAt_id (t : Z)).const_sub 1).comp_ofReal
   exact ((Complex.hasStrictDerivAt_cpow_const (c := (c : Z) - (b : Z)) h1tc).hasDerivAt).comp t hsub
  have d3 : HasDerivAt (fun x : X => (1 - s * (x : Z)) ^ (-(a + 1 : X) : Z))
    ((-(a + 1 : X) : Z) * (1 - s * (t : Z)) ^ ((-(a + 1 : X) : Z) - 1) * (-s)) t := by
   have hsub : HasDerivAt (fun x : X => 1 - s * (x : Z)) (-s) t := by simpa using (((hasDerivAt_id (t : Z)).const_mul s).const_sub 1).comp_ofReal
   exact ((Complex.hasStrictDerivAt_cpow_const (c := (-(a + 1 : X) : Z)) hstc).hasDerivAt).comp t hsub
  have d123 := ((d1.mul d2).mul d3)
  refine d123.congr_deriv ?_
  have ht_ne : (t : Z) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
  have h1t_ne : (1 : Z) - (t : Z) ≠ 0 := ofReal_ne_zero.2 ht1.ne' |>.symm |> fun _ => by
   rw [show (1 : Z) - (t : Z) = ((1 - t : X) : Z) by push_cast;rfl]
   exact ofReal_ne_zero.2 ht1.ne'
  have hst_ne : 1 - s * (t : Z) ≠ 0 := slitPlane_ne_zero hstc
  have htb : (t : Z) ^ (b : Z) = (t : Z) ^ ((b : Z) - 1) * (t : Z) := by
   conv_lhs => rw [show (b : Z) = ((b : Z) - 1) + 1 by ring]
   rw [cpow_add _ _ ht_ne, cpow_one]
  have htcb : (1 - (t : Z)) ^ ((c : Z) - (b : Z)) =
    (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1) * (1 - (t : Z)) := by
   conv_lhs => rw [show (c : Z) - (b : Z) = ((c : Z) - (b : Z) - 1) + 1 by ring]
   rw [cpow_add _ _ h1t_ne, cpow_one]
  have hta1 : (1 - s * (t : Z)) ^ (-(a + 1 : X) : Z) =
    (1 - s * (t : Z)) ^ (-(a + 2 : X) : Z) * (1 - s * (t : Z)) := by
   conv_lhs => rw [show (-(a + 1 : X) : Z) = (-(a + 2 : X) : Z) + 1 by push_cast;ring]
   rw [cpow_add _ _ hst_ne, cpow_one]
  have hta2 : (1 - s * (t : Z)) ^ ((-(a + 1 : X) : Z) - 1) =
    (1 - s * (t : Z)) ^ (-(a + 2 : X) : Z) := by
   congr 1;push_cast;ring
  dsimp [P'];rw [htb, htcb, hta1, hta2];ring
 have hP'_eq : EqOn (fun t : X =>
   s * (1 - s) * ((a * (a + 1) : X) : Z) * xD (a + 2) (b + 2) (c + 2) s t +
   ((c : Z) - ((a + b + 1 : X) : Z) * s) * (a : Z) * xD (a + 1) (b + 1) (c + 1) s t -
   ((a * b : X) : Z) * xD a b c s t) (fun t => -(a : Z) * P' t) (Ioo 0 1) := by
  intro t ht;have ht0 : (0 : X) < t := ht.1;have ht1 : (0 : X) < 1 - t := sub_pos.2 ht.2;have htc_ne : (t : Z) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
  have hst_ne : 1 - s * (t : Z) ≠ 0 :=
   slitPlane_ne_zero (xF hs ht0.le ht.2.le)
  have ht1c : (t : Z) ^ (((b + 1 : X) : Z) - 1) = (t : Z) ^ ((b : Z) - 1) * (t : Z) := by
   rw [show (((b + 1 : X) : Z) - 1) = ((b : Z) - 1) + 1 by push_cast;ring,
    cpow_add _ _ htc_ne, cpow_one]
  have ht2c : (t : Z) ^ (((b + 2 : X) : Z) - 1) = (t : Z) ^ ((b : Z) - 1) * (t : Z) ^ 2 := by
   rw [show (((b + 2 : X) : Z) - 1) = ((b : Z) - 1) + 2 by push_cast;ring,
    cpow_add _ _ htc_ne, Complex.cpow_two]
  have ha0c : (1 - s * (t : Z)) ^ (-a : Z) =
    (1 - s * (t : Z)) ^ (-(a + 2 : X) : Z) * (1 - s * (t : Z)) ^ 2 := by
   conv_lhs => rw [show (-a : Z) = (-(a + 2 : X) : Z) + 2 by push_cast;ring]
   rw [cpow_add _ _ hst_ne, Complex.cpow_two]
  have ha1c : (1 - s * (t : Z)) ^ (-(a + 1 : X) : Z) =
    (1 - s * (t : Z)) ^ (-(a + 2 : X) : Z) * (1 - s * (t : Z)) := by
   conv_lhs => rw [show (-(a + 1 : X) : Z) = (-(a + 2 : X) : Z) + 1 by push_cast;ring]
   rw [cpow_add _ _ hst_ne, cpow_one]
  dsimp [xD, P']
  rw [show ((c + 1 : X) : Z) - ((b + 1 : X) : Z) - 1 = (c : Z) - (b : Z) - 1 by push_cast;ring,
   show ((c + 2 : X) : Z) - ((b + 2 : X) : Z) - 1 = (c : Z) - (b : Z) - 1 by push_cast;ring,
   ht1c, ht2c, ha0c, ha1c]
  push_cast;ring
 by_cases ha0 : a = 0
 ·
  subst ha0
  have h0 : xE 0 b c s = 1 := by
   dsimp [xE]
   have heq : (∫ t in (0 : X)..1, xD 0 b c s t) =
     betaIntegral (b : Z) ((c - b : X) : Z) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne0 : ∀ᵐ t : X ∂volume, t ≠ 0 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
    have hne1 : ∀ᵐ t : X ∂volume, t ≠ 1 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
    filter_upwards [hne0, hne1] with t ht0 ht1 ht
    rw [uIoc_of_le zero_le_one] at ht
    have hw_ne : 1 - s * (t : Z) ≠ 0 :=
     slitPlane_ne_zero (xF hs ht.1.le ht.2)
    simp only [xD,sub_sub,ofReal_zero,neg_zero,cpow_zero,mul_one,ofReal_sub]
   rw [heq];have hbg := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (b : Z)) (t := (c : Z) - (b : Z))
    (by simpa using hb) (by simpa using hcb)
   have hbc : (b : Z) + ((c : Z) - (b : Z)) = (c : Z) := by ring
   rw [hbc, show (c : Z) - (b : Z) = ((c - b : X) : Z) by push_cast;rfl,
    Gamma_ofReal, Gamma_ofReal, Gamma_ofReal] at hbg
   have hGbC : (Gamma b : Z) ≠ 0 := ofReal_ne_zero.2 (gP hb).ne';have hGcbC : (Gamma (c - b) : Z) ≠ 0 := ofReal_ne_zero.2 (gP hcb).ne';have hGcC : (Gamma c : Z) ≠ 0 := ofReal_ne_zero.2 (gP hc).ne';push_cast;field_simp [hGcC, hGbC, hGcbC]
   rw [show ((c - b : X) : Z) = (c : Z) - (b : Z) by push_cast;rfl] at hbg
   linear_combination -hbg
  simp only [zero_mul,zero_div,zero_add,one_mul,ofReal_zero,mul_zero,ofReal_add,ofReal_one,add_zero,h0,mul_one,sub_self]
 have haC : (a : Z) ≠ 0 := ofReal_ne_zero.2 ha0
 let Q : X → Z := fun t =>
  s * (1 - s) * ((a * (a + 1) : X) : Z) * xD (a + 2) (b + 2) (c + 2) s t +
  ((c : Z) - ((a + b + 1 : X) : Z) * s) * (a : Z) * xD (a + 1) (b + 1) (c + 1) s t -
  ((a * b : X) : Z) * xD a b c s t
 have hQ_int : IntervalIntegrable Q volume 0 1 :=
  ((hint2.const_mul _).add (hint1.const_mul _)).sub (hint0.const_mul _)
 have h_int_zero : (∫ t in (0 : X)..1, P' t) = 0 := by
  have hP'_eq' : (fun t => -(a : Z)⁻¹ * Q t) =ᵐ[volume.restrict (Ioc 0 1)] P' := by
   have hne1 : ∀ᵐ t : X ∂volume, t ≠ 1 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
   filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne1] with t ht ht1
   have ht_oo : t ∈ Ioo (0 : X) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩;have hq : Q t = -(a : Z) * P' t := hP'_eq ht_oo;rw [hq];field_simp [haC]
  have hP'_int : IntervalIntegrable P' volume 0 1 := by
   rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one];exact Integrable.congr (hQ_int.const_mul (-(a : Z)⁻¹)).1 hP'_eq'
  let G : X → Z := fun x => ∫ t in (1 / 2 : X)..x, P' t
  have hG_cont : ContinuousOn G (Icc 0 1) := by
   have hc := intervalIntegral.continuousOn_primitive_interval' hP'_int
    (by norm_num : (1 / 2 : X) ∈ uIcc 0 1)
   simpa [G, uIcc_of_le zero_le_one] using hc
  have h_ftc : ∀ ε ∈ Ioo (0 : X) (1 / 2), ∫ t in ε..(1 - ε), P' t = P (1 - ε) - P ε := by
   intro ε hε
   have hle : ε ≤ 1 - ε := by linarith [hε.2]
   have hsub : uIcc ε (1 - ε) ⊆ Ioo 0 1 := by
    rw [uIcc_of_le hle];intro t ht
    exact ⟨lt_of_lt_of_le hε.1 ht.1, lt_of_le_of_lt ht.2 (by linarith [hε.1])⟩
   have hint_ε : IntervalIntegrable P' volume ε (1 - ε) :=
    hP'_int.mono_set (by rw [uIcc_of_le zero_le_one];exact hsub.trans Ioo_subset_Icc_self)
   exact integral_eq_sub_of_hasDerivAt
    (fun t ht => hP_deriv t (hsub ht)) hint_ε
  have h_lhs : Tendsto (fun ε : X => ∫ t in ε..(1 - ε), P' t) (𝓝[>] 0)
    (𝓝 (∫ t in (0 : X)..1, P' t)) := by
   have heq_ε : ∀ᶠ ε in 𝓝[>] (0 : X), ∫ t in ε..(1 - ε), P' t = G (1 - ε) - G ε := by
    filter_upwards [Ioo_mem_nhdsGT k2] with ε hε
    have hi1 : IntervalIntegrable P' volume ε (1 / 2) :=
     hP'_int.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le (by linarith [hε.2] : ε ≤ 1 / 2)];intro x hx;exact ⟨le_trans hε.1.le hx.1, le_trans hx.2 (by norm_num)⟩)
    have hi2 : IntervalIntegrable P' volume (1 / 2) (1 - ε) :=
     hP'_int.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le (by linarith [hε.2] : 1 / 2 ≤ 1 - ε)];intro x hx;exact ⟨le_trans (by norm_num) hx.1, le_trans hx.2 (by linarith [hε.1])⟩)
    dsimp [G]
    rw [← integral_add_adjacent_intervals hi1 hi2,
     integral_symm (1 / 2) ε]
    ring
   have hG1 : Tendsto (fun ε : X => G (1 - ε)) (𝓝[>] 0) (𝓝 (G 1)) := by
    have ht1 : Tendsto (fun ε : X => 1 - ε) (𝓝[>] 0) (𝓝[Icc 0 1] 1) := by
     rw [tendsto_nhdsWithin_iff]
     have hlim : Tendsto (fun ε : X => 1 - ε) (𝓝 0) (𝓝 1) := by
      simpa only [sub_zero] using
       ((tendsto_const_nhds.sub tendsto_id) : Tendsto (fun ε : X => 1 - ε) (𝓝 0) (𝓝 (1 - 0)))
     refine ⟨hlim.mono_left nhdsWithin_le_nhds, ?_⟩
     filter_upwards [Ioo_mem_nhdsGT k2] with ε hε
     exact ⟨by linarith [hε.2], by linarith [hε.1]⟩
    exact (hG_cont 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp ht1
   have hG0 : Tendsto G (𝓝[>] 0) (𝓝 (G 0)) := by
    have ht0 : Tendsto (id : X → X) (𝓝[>] 0) (𝓝[Icc 0 1] 0) := by
     rw [tendsto_nhdsWithin_iff]
     refine ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
     filter_upwards [Ioo_mem_nhdsGT k2] with ε hε
     exact ⟨hε.1.le, le_trans hε.2.le (half_le_self zero_le_one)⟩
    exact (hG_cont 0 ⟨le_rfl, zero_le_one⟩).tendsto.comp ht0
   have hdiff := hG1.sub hG0
   have hG_eq : G 1 - G 0 = ∫ t in (0 : X)..1, P' t := by
    have hi1 : IntervalIntegrable P' volume 0 (1 / 2) :=
     hP'_int.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le k2.le];exact Icc_subset_Icc_right (half_le_self zero_le_one))
    have hi2 : IntervalIntegrable P' volume (1 / 2) 1 :=
     hP'_int.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le (half_le_self zero_le_one)];exact Icc_subset_Icc_left k2.le)
    dsimp [G]
    rw [← integral_add_adjacent_intervals hi1 hi2,
     integral_symm (1 / 2) 0]
    ring
   rw [hG_eq] at hdiff;exact hdiff.congr' (heq_ε.mono fun ε h => h.symm)
  have h_rhs : Tendsto (fun ε : X => P (1 - ε) - P ε) (𝓝[>] 0) (𝓝 0) := by
   have hP0 : Tendsto P (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : X => (ε : Z) ^ (b : Z)) (𝓝[>] 0) (𝓝 0) := by
     have hr : Tendsto (fun ε : X => ε ^ b) (𝓝[>] 0) (𝓝 0) :=
      (Real.continuousAt_rpow_const 0 b (Or.inr hb.le)).tendsto.mono_left nhdsWithin_le_nhds |>.trans (by simp only [Real.zero_rpow hb.ne',Std.le_refl])
     have hc_eq : ∀ᶠ (ε : X) in 𝓝[>] 0, (ε : Z) ^ (b : Z) = ((ε ^ b : X) : Z) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (ofReal_cpow hε.le b).symm
     exact (continuous_ofReal.continuousAt.tendsto.comp hr).congr' (hc_eq.mono fun _ h => h.symm)
    have h2 : Tendsto (fun ε : X => (1 - (ε : Z)) ^ ((c : Z) - (b : Z))) (𝓝[>] 0) (𝓝 1) := by
     have hc2 : ContinuousAt (fun ε : X => (1 - (ε : Z)) ^ ((c : Z) - (b : Z))) 0 :=
      ContinuousAt.cpow (continuous_const.sub continuous_ofReal).continuousAt continuousAt_const (by simp only [ofReal_zero,sub_zero,one_mem_slitPlane])
     simpa using hc2.tendsto.mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun ε : X => (1 - s * (ε : Z)) ^ (-(a + 1 : X) : Z)) (𝓝[>] 0) (𝓝 1) := by
     have hc3 : ContinuousAt (fun ε : X => (1 - s * (ε : Z)) ^ (-(a + 1 : X) : Z)) 0 :=
      ContinuousAt.cpow (continuous_const.sub (continuous_const.mul continuous_ofReal)).continuousAt continuousAt_const (by simp only [ofReal_zero,mul_zero,sub_zero,one_mem_slitPlane])
     simpa using hc3.tendsto.mono_left nhdsWithin_le_nhds
    simpa [P] using (h1.mul h2).mul h3
   have hP1 : Tendsto (fun ε : X => P (1 - ε)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : X => ((1 - ε : X) : Z) ^ (b : Z)) (𝓝[>] 0) (𝓝 1) := by
     have hc1 : ContinuousAt (fun ε : X => ((1 - ε : X) : Z) ^ (b : Z)) 0 :=
      ContinuousAt.cpow (continuous_ofReal.comp (continuous_const.sub continuous_id)).continuousAt continuousAt_const (by simp only [sub_zero,ofReal_one,one_mem_slitPlane])
     simpa using hc1.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ε : X => (1 - ((1 - ε : X) : Z)) ^ ((c : Z) - (b : Z))) (𝓝[>] 0) (𝓝 0) := by
     have hr : Tendsto (fun ε : X => ε ^ (c - b)) (𝓝[>] 0) (𝓝 0) :=
      (Real.continuousAt_rpow_const 0 (c - b) (Or.inr hcb.le)).tendsto.mono_left nhdsWithin_le_nhds |>.trans (by simp only [Real.zero_rpow hcb.ne',Std.le_refl])
     have hc_eq : ∀ᶠ (ε : X) in 𝓝[>] 0,
       (1 - ((1 - ε : X) : Z)) ^ ((c : Z) - (b : Z)) = ((ε ^ (c - b) : X) : Z) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [show (1 : Z) - ((1 - ε : X) : Z) = (ε : Z) by push_cast;ring,
       show (c : Z) - (b : Z) = ((c - b : X) : Z) by push_cast;rfl]
      exact (ofReal_cpow hε.le _).symm
     exact (continuous_ofReal.continuousAt.tendsto.comp hr).congr' (hc_eq.mono fun _ h => h.symm)
    have h3 : Tendsto (fun ε : X => (1 - s * ((1 - ε : X) : Z)) ^ (-(a + 1 : X) : Z)) (𝓝[>] 0)
      (𝓝 ((1 - s) ^ (-(a + 1 : X) : Z))) := by
     have hslit1 : 1 - s ∈ slitPlane := by simpa using xF hs zero_le_one le_rfl
     have hc3 : ContinuousAt (fun ε : X => (1 - s * ((1 - ε : X) : Z)) ^ (-(a + 1 : X) : Z)) 0 :=
      ContinuousAt.cpow (continuous_const.sub (continuous_const.mul (continuous_ofReal.comp (continuous_const.sub continuous_id)))).continuousAt continuousAt_const (by simpa using hslit1)
     simpa using hc3.tendsto.mono_left nhdsWithin_le_nhds
    simpa [P] using (h1.mul h2).mul h3
   simpa using hP1.sub hP0
  have h_lhs' : Tendsto (fun ε : X => P (1 - ε) - P ε) (𝓝[>] 0) (𝓝 (∫ t in (0 : X)..1, P' t)) :=
   h_lhs.congr' (by filter_upwards [Ioo_mem_nhdsGT k2] with ε hε;exact h_ftc ε hε)
  exact tendsto_nhds_unique h_lhs' h_rhs
 have h_int_Q : (∫ t in (0 : X)..1, Q t) = 0 := by
  have heq_Q : (∫ t in (0 : X)..1, Q t) = -(a : Z) * ∫ t in (0 : X)..1, P' t := by
   rw [← intervalIntegral.integral_const_mul]
   refine intervalIntegral.integral_congr_ae ?_
   have hne1 : ∀ᵐ t : X ∂volume, t ≠ 1 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
   filter_upwards [hne1] with t ht1 ht
   rw [uIoc_of_le zero_le_one] at ht;exact hP'_eq ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
  rw [heq_Q, h_int_zero, mul_zero]
 have hQ_split : (∫ t in (0 : X)..1, Q t) =
   s * (1 - s) * ((a * (a + 1) : X) : Z) * (∫ t in (0 : X)..1, xD (a + 2) (b + 2) (c + 2) s t) +
   ((c : Z) - ((a + b + 1 : X) : Z) * s) * (a : Z) * (∫ t in (0 : X)..1, xD (a + 1) (b + 1) (c + 1) s t) -
   ((a * b : X) : Z) * (∫ t in (0 : X)..1, xD a b c s t) := by
  dsimp [Q]
  rw [intervalIntegral.integral_sub ((hint2.const_mul _).add (hint1.const_mul _)) (hint0.const_mul _),
   intervalIntegral.integral_add (hint2.const_mul _) (hint1.const_mul _),
   intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
   intervalIntegral.integral_const_mul]
 rw [hQ_split] at h_int_Q
 have hF1_eq : ((a * b / c : X) : Z) * xE (a + 1) (b + 1) (c + 1) s =
   ((Gamma c / (Gamma b * Gamma (c - b)) : X) : Z) *
    ((a : Z) * ∫ t in (0 : X)..1, xD (a + 1) (b + 1) (c + 1) s t) := by
  dsimp [xE]
  rw [show ((c + 1 : X) - (b + 1 : X)) = c - b by ring, hGbc, hGcc]
  push_cast;field_simp [hGbC, hGcC, hGcbC, hbC, hcC]
 have hF2_eq : (((a * b / c) * ((a + 1) * (b + 1) / (c + 1)) : X) : Z) * xE (a + 2) (b + 2) (c + 2) s =
   ((Gamma c / (Gamma b * Gamma (c - b)) : X) : Z) *
    (((a * (a + 1) : X) : Z) * ∫ t in (0 : X)..1, xD (a + 2) (b + 2) (c + 2) s t) := by
  dsimp [xE]
  rw [show ((c + 2 : X) - (b + 2 : X)) = c - b by ring, hGbc2, hGcc2]
  push_cast at hb1C hc1C ⊢
  field_simp [hGbC, hGcC, hGcbC, hbC, hcC, hb1C, hc1C]
 rw [hF1_eq, hF2_eq];dsimp [xE];linear_combination ((Gamma c / (Gamma b * Gamma (c - b)) : X) : Z) * h_int_Q
lemma xW (f : X → Z) :
  ∫ x in Ioo (0 : X) 1, f x = ∫ t in Ioo (0 : X) 1, (2 * t) • f (t ^ 2) := by
 have hs : MeasurableSet (Ioo (0 : X) 1) := measurableSet_Ioo
 have hinj : InjOn (fun t : X => t ^ 2) (Ioo 0 1) := fun a ha b hb h => by
  nlinarith only [ha.1, hb.1, h]
 have himg : (fun t : X => t ^ 2) '' Ioo (0 : X) 1 = Ioo 0 1 := by
  ext x;constructor
  ·
   rintro ⟨t, ht, rfl⟩
   exact ⟨sq_pos_of_pos ht.1, by nlinarith only [ht.1, ht.2]⟩
  ·
   intro hx
   refine ⟨Y x, ⟨sqrt_pos.2 hx.1, ?_⟩, sq_sqrt hx.1.le⟩
   rw [Real.sqrt_lt' one_pos];simpa using hx.2
 have hderiv : ∀ t ∈ Ioo (0 : X) 1, HasDerivWithinAt (fun x : X => x ^ 2) (2 * t) (Ioo 0 1) t :=
  fun t _ => ((hasDerivAt_pow 2 t).congr_deriv (by ring)).hasDerivWithinAt
 have hch := integral_image_eq_integral_abs_deriv_smul hs hderiv hinj f;rw [himg] at hch;rw [hch]
 refine setIntegral_congr_fun hs fun t ht => ?_
 rw [abs_of_pos (by linarith [ht.1])]
lemma xX (f : X → Z) :
  ∫ t in Ioo (0 : X) 1, f t =
   ∫ y in Ioo (0 : X) 1, (2 / (1 + y) ^ 2) • f ((1 - y) / (1 + y)) := by
 let φ : X → X := fun y => (1 - y) / (1 + y);have hs : MeasurableSet (Ioo (0 : X) 1) := measurableSet_Ioo
 have hinj : InjOn φ (Ioo 0 1) := fun a ha b hb h => by
  dsimp [φ] at h
  have ha1 : 1 + a ≠ 0 := by linarith [ha.1]
  have hb1 : 1 + b ≠ 0 := by linarith [hb.1]
  rw [div_eq_div_iff ha1 hb1] at h;linarith
 have himg : φ '' Ioo (0 : X) 1 = Ioo 0 1 := by
  ext x;constructor
  ·
   rintro ⟨y, hy, rfl⟩
   have hy1 : 0 < 1 + y := by linarith [hy.1]
   exact ⟨div_pos (sub_pos.2 hy.2) hy1, (div_lt_one hy1).2 (by linarith [hy.1])⟩
  ·
   intro hx
   have hx1 : 0 < 1 + x := by linarith [hx.1]
   refine ⟨(1 - x) / (1 + x), ⟨div_pos (sub_pos.2 hx.2) hx1, (div_lt_one hx1).2 (by linarith [hx.1])⟩, ?_⟩
   dsimp [φ];field_simp [hx1.ne'];ring
 have hderiv : ∀ y ∈ Ioo (0 : X) 1, HasDerivWithinAt φ (-2 / (1 + y) ^ 2) (Ioo 0 1) y := by
  intro y hy
  have h1 : HasDerivAt (fun x : X => 1 - x) (-1) y :=
   (hasDerivAt_id y).const_sub (1 : X)
  have h2 : HasDerivAt (fun x : X => 1 + x) 1 y :=
   (hasDerivAt_id y).const_add (1 : X)
  have hdiv : HasDerivAt (fun x : X => (1 - x) / (1 + x))
    (((-1) * (1 + y) - (1 - y) * 1) / (1 + y) ^ 2) y :=
   h1.div h2 (by linarith [hy.1])
  have hd : HasDerivAt (fun x : X => (1 - x) / (1 + x)) (-2 / (1 + y) ^ 2) y := by convert hdiv using 1;field_simp [show 1 + y ≠ 0 by linarith [hy.1]];ring
  simpa only [φ] using hd.hasDerivWithinAt
 have hch := integral_image_eq_integral_abs_deriv_smul hs hderiv hinj f;rw [himg] at hch;rw [hch]
 refine setIntegral_congr_fun hs fun y hy => ?_
 have hy1 : 0 < (1 + y) ^ 2 := sq_pos_of_pos (by linarith [hy.1])
 rw [show |-2 / (1 + y) ^ 2| = 2 / (1 + y) ^ 2 by
  rw [abs_div, abs_neg, abs_of_pos two_pos, abs_of_pos hy1]]
lemma xY :
  ∫ t in (0 : X)..1, xD (5 / 12) (3 / 4) (4 / 3) (-1) t =
   (1 / 2 : Z) * betaIntegral (3 / 8 : Z) (7 / 12 : Z) := by
 have hint : IntervalIntegrable (xD (5 / 12) (3 / 4) (4 / 3) (-1)) volume 0 1 :=
  xJ (by norm_num) (by norm_num) (by norm_num [xN])
 have hbeta := Complex.betaIntegral_convergent (u := (3 / 8 : Z)) (v := (7 / 12 : Z))
  (by norm_num) (by norm_num)
 rw [integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
 have hb_eq : betaIntegral (3 / 8 : Z) (7 / 12 : Z) =
   ∫ x in Ioo (0 : X) 1, (x : Z) ^ ((3 / 8 : Z) - 1) * (1 - (x : Z)) ^ ((7 / 12 : Z) - 1) := by
  dsimp [betaIntegral];rw [integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
 rw [hb_eq]
 conv_rhs => rw [xW]
 rw [← MeasureTheory.integral_const_mul]
 refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
 have ht0 : 0 < t := ht.1;have ht1 : 0 < 1 - t := sub_pos.2 ht.2
 have ht2 : 0 < 1 + t := by linarith [ht0]
 have htsq : 0 < t ^ 2 := sq_pos_of_pos ht0
 have h1tsq : 0 < 1 - t ^ 2 := by nlinarith only [ht0, ht.2]
 have hsplit : (1 - t ^ 2) = (1 - t) * (1 + t) := by ring
 have hc1 : ((1 - (t ^ 2 : X) : X) : Z) = 1 - ((t ^ 2 : X) : Z) := by push_cast;rfl
 have hc2 : ((1 - t : X) : Z) = 1 - (t : Z) := by push_cast;rfl
 have hc3 : ((1 + t : X) : Z) = 1 - (-1 : Z) * (t : Z) := by push_cast;ring
 rw [real_smul];dsimp [xD]
 rw [show (3 / 8 : Z) - 1 = ((-5 / 8 : X) : Z) by push_cast;ring,
  show (7 / 12 : Z) - 1 = ((-5 / 12 : X) : Z) by push_cast;ring,
  show ((3 / 4 : X) : Z) - 1 = ((-1 / 4 : X) : Z) by push_cast;ring,
  show ((4 / 3 : X) : Z) - ((3 / 4 : X) : Z) - 1 = ((-5 / 12 : X) : Z) by push_cast;ring,
  show (-(5 / 12 : X) : Z) = ((-5 / 12 : X) : Z) by push_cast;ring]
 rw [← hc1, ← hc2, ← hc3]
 rw [← ofReal_cpow htsq.le, ← ofReal_cpow h1tsq.le,
  ← ofReal_cpow ht0.le, ← ofReal_cpow ht1.le, ← ofReal_cpow ht2.le]
 push_cast
 have hr1 : (t ^ 2) ^ (-5 / 8 : X) * t = t ^ (-1 / 4 : X) := by
  rw [← rpow_natCast t 2, ← rpow_mul ht0.le];push_cast
  conv_lhs => rhs;rw [← rpow_one t]
  rw [← rpow_add ht0];norm_num
 have hr2 : (1 - t ^ 2) ^ (-5 / 12 : X) = (1 - t) ^ (-5 / 12 : X) * (1 + t) ^ (-5 / 12 : X) := by rw [hsplit, mul_rpow ht1.le ht2.le]
 have hreal : (1 / 2 : X) * ((2 * t) * ((t ^ 2) ^ (-5 / 8 : X) * (1 - t ^ 2) ^ (-5 / 12 : X))) =
   t ^ (-1 / 4 : X) * (1 - t) ^ (-5 / 12 : X) * (1 + t) ^ (-5 / 12 : X) := by
  calc (1 / 2 : X) * ((2 * t) * ((t ^ 2) ^ (-5 / 8 : X) * (1 - t ^ 2) ^ (-5 / 12 : X)))
      = ((t ^ 2) ^ (-5 / 8 : X) * t) * (1 - t ^ 2) ^ (-5 / 12 : X) := by ring
    _ = t ^ (-1 / 4 : X) * ((1 - t) ^ (-5 / 12 : X) * (1 + t) ^ (-5 / 12 : X)) := by rw [hr1, hr2]
    _ = _ := by ring
 have hC := congr_arg (fun r : X => (r : Z)) hreal.symm;simpa [ofReal_mul, ofReal_div] using hC
lemma xZ {a b : X} (_hb : 0 < b) (_hpos : 0 < (a - 2 * b + 1) / 2) :
  ∫ t in (0 : X)..1, xD a b (1 + a - b) (-1) t =
   (((2 : X) ^ (-2 * b) : X) : Z) *
    betaIntegral (((a - 2 * b + 1) / 2 : X) : Z) (b : Z) := by
 rw [integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
 have hb_eq : betaIntegral (((a - 2 * b + 1) / 2 : X) : Z) (b : Z) =
   ∫ x in Ioo (0 : X) 1, (x : Z) ^ ((((a - 2 * b + 1) / 2 : X) : Z) - 1) *
    (1 - (x : Z)) ^ ((b : Z) - 1) := by
  dsimp [betaIntegral];rw [integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
 rw [hb_eq]
 conv_lhs => rw [xX]
 conv_rhs => rw [xW]
 rw [← MeasureTheory.integral_const_mul]
 refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
 have hy0 : 0 < y := hy.1;have hy1 : 0 < 1 - y := sub_pos.2 hy.2
 have hy2 : 0 < 1 + y := by linarith [hy0]
 have hy2c : (1 : Z) + (y : Z) ≠ 0 := by exact_mod_cast hy2.ne'
 have hysq : 0 < y ^ 2 := sq_pos_of_pos hy0
 have h1ysq : 0 < 1 - y ^ 2 := by nlinarith only [hy0, hy.2]
 have hφ0 : 0 < (1 - y) / (1 + y) := div_pos hy1 hy2
 have hφ1 : 0 < 1 - (1 - y) / (1 + y) := by
  rw [show 1 - (1 - y) / (1 + y) = (2 * y) / (1 + y) by field_simp [hy2.ne'];ring]
  positivity
 have hφ2 : 0 < 1 + (1 - y) / (1 + y) := by
  rw [show 1 + (1 - y) / (1 + y) = 2 / (1 + y) by field_simp [hy2.ne'];ring]
  positivity
 rw [real_smul, real_smul];dsimp [xD]
 have hc_a : ((1 + a - b : X) : Z) - (b : Z) - 1 = ((a - 2 * b : X) : Z) := by push_cast;ring
 have hc_b : ((b : Z) - 1) = ((b - 1 : X) : Z) := by push_cast;rfl
 have hc_ab : (((a - 2 * b + 1) / 2 : X) : Z) - 1 = (((a - 2 * b - 1) / 2 : X) : Z) := by push_cast;ring
 have hc_1φ : 1 - (((1 - y) / (1 + y) : X) : Z) = (((2 * y) / (1 + y) : X) : Z) := by push_cast;field_simp [hy2c];ring
 have hc_pφ : 1 - (-1 : Z) * (((1 - y) / (1 + y) : X) : Z) = ((2 / (1 + y) : X) : Z) := by push_cast;field_simp [hy2c];ring
 have hc_ysq : 1 - ((y ^ 2 : X) : Z) = ((1 - y ^ 2 : X) : Z) := by push_cast;rfl
 rw [hc_a, hc_b, hc_ab, hc_1φ, hc_pφ, hc_ysq, show (-a : Z) = ((-a : X) : Z) by push_cast;rfl]
 have hφ1' : 0 < 2 * y / (1 + y) := by positivity
 have hφ2' : 0 < 2 / (1 + y) := by positivity
 rw [← ofReal_cpow hφ0.le, ← ofReal_cpow hφ1'.le, ← ofReal_cpow hφ2'.le,
  ← ofReal_cpow hysq.le, ← ofReal_cpow h1ysq.le]
 have hr1 : ((1 - y) / (1 + y)) ^ (b - 1) = (1 - y) ^ (b - 1) / (1 + y) ^ (b - 1) :=
  div_rpow hy1.le hy2.le _
 have hr2 : ((2 * y) / (1 + y)) ^ (a - 2 * b) =
   ((2 : X) ^ (a - 2 * b) * y ^ (a - 2 * b)) / (1 + y) ^ (a - 2 * b) := by
  rw [div_rpow (by positivity) hy2.le, mul_rpow two_pos.le hy0.le]
 have hr3 : (2 / (1 + y)) ^ (-a) = (2 : X) ^ (-a) / (1 + y) ^ (-a) :=
  div_rpow two_pos.le hy2.le _
 have hr4 : (y ^ 2) ^ ((a - 2 * b - 1) / 2) * y = y ^ (a - 2 * b) := by
  rw [← rpow_natCast y 2, ← rpow_mul hy0.le];push_cast
  conv_lhs => rhs;rw [← rpow_one y]
  rw [← rpow_add hy0];congr 1;ring
 have hr5 : (1 - y ^ 2) ^ (b - 1) = (1 - y) ^ (b - 1) * (1 + y) ^ (b - 1) := by rw [show 1 - y ^ 2 = (1 - y) * (1 + y) by ring, mul_rpow hy1.le hy2.le]
 have h2pow : (2 : X) * (2 : X) ^ (a - 2 * b) * (2 : X) ^ (-a) = (2 : X) ^ (-2 * b) * 2 := by
  have h2_1 : (2 : X) ^ (a - 2 * b) * (2 : X) ^ (-a) = (2 : X) ^ (-2 * b) := by
   rw [← rpow_add two_pos];congr 1;ring
  linarith
 have hreal : (2 / (1 + y) ^ 2) *
   (((1 - y) / (1 + y)) ^ (b - 1) * ((2 * y) / (1 + y)) ^ (a - 2 * b) * (2 / (1 + y)) ^ (-a)) =
   (2 : X) ^ (-2 * b) * ((2 * y) * ((y ^ 2) ^ ((a - 2 * b - 1) / 2) * (1 - y ^ 2) ^ (b - 1))) := by
  rw [hr1, hr2, hr3, hr5];set A := (1 + y) ^ (b - 1);set B := (1 + y) ^ (a - 2 * b);set C := (1 + y) ^ (-a);have hA : A ≠ 0 := (rpow_pos_of_pos hy2 _).ne';have hB : B ≠ 0 := (rpow_pos_of_pos hy2 _).ne';have hC : C ≠ 0 := (rpow_pos_of_pos hy2 _).ne';have hy2sq : (1 + y) ^ 2 ≠ 0 := (sq_pos_of_pos hy2).ne'
  have hprod_den : (1 + y) ^ 2 * A * B * C = A⁻¹ := by
   dsimp [A, B, C]
   rw [← rpow_two (1 + y), ← rpow_add hy2, ← rpow_add hy2, ← rpow_add hy2,
    show (2 : X) + (b - 1) + (a - 2 * b) + -a = -(b - 1) by ring, rpow_neg hy2.le]
  have hmul_den : ((1 + y) ^ 2 * A * B * C) * A = 1 := by rw [hprod_den, inv_mul_cancel₀ hA]
  have hLHS : (2 / (1 + y) ^ 2) * ((1 - y) ^ (b - 1) / A * (2 ^ (a - 2 * b) * y ^ (a - 2 * b) / B) * (2 ^ (-a) / C)) =
    (2 * (2 : X) ^ (a - 2 * b) * (2 : X) ^ (-a)) * ((1 - y) ^ (b - 1) * y ^ (a - 2 * b)) *
     ((1 + y) ^ 2 * A * B * C)⁻¹ := by
   field_simp [hy2sq, hA, hB, hC]
  rw [hLHS, hprod_den, inv_inv, h2pow, ← hr4];ring
 have hC := congr_arg (fun r : X => (r : Z)) hreal;simpa [ofReal_mul, ofReal_div] using hC
lemma x0 {a b : X} (ha : 0 < a) (hb : 0 < b) :
  betaIntegral (a : Z) (b : Z) =
   ((Gamma a * Gamma b / Gamma (a + b) : X) : Z) := by
 have hbg := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : Z)) (t := (b : Z))
  (by exact_mod_cast ha) (by exact_mod_cast hb)
 have gC : (Gamma (a + b) : Z) ≠ 0 :=
  ofReal_ne_zero.2 (gP (by linarith)).ne'
 rw [show (a : Z) + (b : Z) = ((a + b : X) : Z) by push_cast;rfl,
  Gamma_ofReal, Gamma_ofReal, Gamma_ofReal] at hbg
 rw [ofReal_div, ofReal_mul, eq_div_iff gC, mul_comm, ← hbg]
lemma x1 :
  xE (5 / 12) (3 / 4) (4 / 3) (-1) =
   (((1 / 2 * Gamma (4 / 3) * Gamma (3 / 8) /
    (Gamma (3 / 4) * Gamma (23 / 24))) : X) : Z) := by
 dsimp [xE];rw [xY];have hbeta_eq := x0 (a := 3 / 8) (b := 7 / 12) xc xh
 rw [show (3 / 8 + 7 / 12 : X) = 23 / 24 by ring] at hbeta_eq
 rw [show (3 / 8 : Z) = ((3 / 8 : X) : Z) by push_cast;rfl,
  show (7 / 12 : Z) = ((7 / 12 : X) : Z) by push_cast;rfl, hbeta_eq,
  show (1 / 2 : Z) = ((1 / 2 : X) : Z) by push_cast;rfl,
  ← ofReal_mul, ← ofReal_mul]
 congr 1
 rw [show (4 / 3 - 3 / 4 : X) = 7 / 12 by ring]
 have g34 : Gamma (3 / 4) ≠ 0 := xB k7;have g712 : Gamma (7 / 12) ≠ 0 := xB xh;have g23r : Gamma (23 / 24) ≠ 0 := xB xl;field_simp [g34, g712, g23r]
lemma x2 :
  xE (1 / 12) (5 / 12) (2 / 3) (-1) =
   ((((2 : X) ^ (-5 / 6 : X) * Gamma (2 / 3) * Gamma (1 / 8) /
    (Gamma (1 / 4) * Gamma (13 / 24))) : X) : Z) := by
 dsimp [xE]
 have hk := xZ (a := 1 / 12) (b := 5 / 12) xg (by norm_num)
 rw [show (1 + (1 / 12 : X) - 5 / 12) = 2 / 3 by ring,
  show ((1 / 12 - 2 * (5 / 12) + 1) / 2 : X) = 1 / 8 by ring,
  show (-2 * (5 / 12 : X)) = -5 / 6 by ring] at hk
 rw [hk];have hbeta_eq := x0 (a := 1 / 8) (b := 5 / 12) k9 xg
 rw [show (1 / 8 + 5 / 12 : X) = 13 / 24 by ring] at hbeta_eq
 rw [hbeta_eq, ← ofReal_mul, ← ofReal_mul];congr 1
 rw [show (2 / 3 - 5 / 12 : X) = 1 / 4 by ring]
 have g5 : Gamma (5 / 12) ≠ 0 := xB xg;have g1 : Gamma (1 / 4) ≠ 0 := xB k6;have g13r : Gamma (13 / 24) ≠ 0 := xB xk;field_simp [g5, g1, g13r]
lemma x3 :
  6 * deriv (xE (1 / 12) (5 / 12) (2 / 3)) (-1) -
   (1 / 4) * xE (1 / 12) (5 / 12) (2 / 3) (-1) =
   (((-(1 / 4) * (2 : X) ^ (-5 / 6 : X) * Gamma (2 / 3) * Gamma (5 / 8) /
    (Gamma (1 / 4) * Gamma (25 / 24))) : X) : Z) := by
 have hm1 : (-1 : Z) ∈ xN := by simp only [xN,not_and,mem_ofPred_eq,neg_re,one_re,le_neg_self_iff,neg_im,one_im,neg_zero,not_true_eq_false,imp_false,not_le,zero_lt_one]
 have hd := (xT (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
  xg xn k4 hm1).deriv
 rw [hd]
 have hG5 : Gamma (17 / 12) = (5 / 12) * Gamma (5 / 12) := by rw [show (17 / 12 : X) = 5 / 12 + 1 by ring, Real.Gamma_add_one (by positivity)]
 have hG2 : Gamma (5 / 3) = (2 / 3) * Gamma (2 / 3) := by rw [show (5 / 3 : X) = 2 / 3 + 1 by ring, Real.Gamma_add_one (by positivity)]
 have hint1 := xJ (a := 13 / 12) (b := 17 / 12) (c := 5 / 3)
  (by norm_num) (by norm_num) hm1
 have hint0 := xJ (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
  (by norm_num) (by norm_num) hm1
 have hcomb_int :
   (1 / 2 : Z) * (∫ t in (0 : X)..1, xD (13 / 12) (17 / 12) (5 / 3) (-1) t) -
    (1 / 4 : Z) * (∫ t in (0 : X)..1, xD (1 / 12) (5 / 12) (2 / 3) (-1) t) =
   -(1 / 4 : Z) * ∫ t in (0 : X)..1, xD (13 / 12) (5 / 12) (5 / 3) (-1) t := by
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
   ← intervalIntegral.integral_const_mul,
   ← intervalIntegral.integral_sub (hint1.const_mul _) (hint0.const_mul _)]
  refine intervalIntegral.integral_congr_ae ?_
  have hne0 : ∀ᵐ t : X ∂volume, t ≠ 0 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
  have hne1 : ∀ᵐ t : X ∂volume, t ≠ 1 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
  filter_upwards [hne0, hne1] with t ht0 ht1 ht
  rw [uIoc_of_le zero_le_one] at ht;have ht_pos : 0 < t := lt_of_le_of_ne ht.1.le (Ne.symm ht0);have h1t_pos : 0 < 1 - t := sub_pos.2 (lt_of_le_of_ne ht.2 ht1);have htc_ne : (t : Z) ≠ 0 := ofReal_ne_zero.2 ht_pos.ne'
  have h1tc_ne : (1 : Z) - (t : Z) ≠ 0 := by
   rw [show (1 : Z) - (t : Z) = ((1 - t : X) : Z) by push_cast;rfl]
   exact ofReal_ne_zero.2 h1t_pos.ne'
  have hpt_ne : (1 : Z) - (-1 : Z) * (t : Z) ≠ 0 := by
   rw [show (1 : Z) - (-1 : Z) * (t : Z) = ((1 + t : X) : Z) by push_cast;ring]
   exact ofReal_ne_zero.2 (by linarith)
  have htp : (t : Z) ^ (((17 / 12 : X) : Z) - 1) = (t : Z) ^ (((5 / 12 : X) : Z) - 1) * (t : Z) := by
   rw [show (((17 / 12 : X) : Z) - 1) = (((5 / 12 : X) : Z) - 1) + 1 by push_cast;ring,
    cpow_add _ _ htc_ne, cpow_one]
  have h1tp : (1 - (t : Z)) ^ (((5 / 3 : X) : Z) - ((5 / 12 : X) : Z) - 1) =
    (1 - (t : Z)) ^ (((2 / 3 : X) : Z) - ((5 / 12 : X) : Z) - 1) * (1 - (t : Z)) := by
   rw [show (((5 / 3 : X) : Z) - ((5 / 12 : X) : Z) - 1) =
     (((2 / 3 : X) : Z) - ((5 / 12 : X) : Z) - 1) + 1 by push_cast;ring,
    cpow_add _ _ h1tc_ne, cpow_one]
  have hptp : (1 - (-1 : Z) * (t : Z)) ^ (-(1 / 12 : X) : Z) =
    (1 - (-1 : Z) * (t : Z)) ^ (-(13 / 12 : X) : Z) * (1 - (-1 : Z) * (t : Z)) := by
   rw [show (-(1 / 12 : X) : Z) = (-(13 / 12 : X) : Z) + 1 by push_cast;ring,
    cpow_add _ _ hpt_ne, cpow_one]
  dsimp [xD]
  rw [show (((5 / 3 : X) : Z) - ((17 / 12 : X) : Z) - 1) =
    (((2 / 3 : X) : Z) - ((5 / 12 : X) : Z) - 1) by push_cast;ring,
   htp, h1tp, hptp]
  ring
 have hk := xZ (a := 13 / 12) (b := 5 / 12) xg (by norm_num)
 rw [show (1 + (13 / 12 : X) - 5 / 12) = 5 / 3 by ring,
  show ((13 / 12 - 2 * (5 / 12) + 1) / 2 : X) = 5 / 8 by ring,
  show (-2 * (5 / 12 : X)) = -5 / 6 by ring] at hk
 have hbeta_eq := x0 (a := 5 / 8) (b := 5 / 12) xd xg
 rw [show (5 / 8 + 5 / 12 : X) = 25 / 24 by ring] at hbeta_eq
 dsimp [xE]
 rw [show (1 / 12 + 1 : X) = 13 / 12 by ring, show (5 / 12 + 1 : X) = 17 / 12 by ring,
  show (2 / 3 + 1 : X) = 5 / 3 by ring,
  show (5 / 3 - 17 / 12 : X) = 1 / 4 by ring,
  show (2 / 3 - 5 / 12 : X) = 1 / 4 by ring, hG5, hG2]
 have g5C : (Gamma (5 / 12) : Z) ≠ 0 := xC xg;have g1C : (Gamma (1 / 4) : Z) ≠ 0 := xC k6;have g2C : (Gamma (2 / 3) : Z) ≠ 0 := xC k4
 have hsplit_lhs :
   6 * (((1 / 12 * (5 / 12) / (2 / 3) : X) : Z) *
    ((((2 / 3 * Gamma (2 / 3)) / (5 / 12 * Gamma (5 / 12) * Gamma (1 / 4)) : X) : Z) *
     ∫ t in (0 : X)..1, xD (13 / 12) (17 / 12) (5 / 3) (-1) t)) -
   1 / 4 * (((Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (1 / 4)) : X) : Z) *
    ∫ t in (0 : X)..1, xD (1 / 12) (5 / 12) (2 / 3) (-1) t) =
   ((Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (1 / 4)) : X) : Z) *
    ((1 / 2 : Z) * (∫ t in (0 : X)..1, xD (13 / 12) (17 / 12) (5 / 3) (-1) t) -
     (1 / 4 : Z) * (∫ t in (0 : X)..1, xD (1 / 12) (5 / 12) (2 / 3) (-1) t)) := by
  push_cast;field_simp [g5C, g1C, g2C];ring
 rw [hsplit_lhs, hcomb_int, hk, hbeta_eq]
 rw [show -(1 / 4 : Z) = ((-(1 / 4) : X) : Z) by push_cast;ring,
  ← ofReal_mul, ← ofReal_mul, ← ofReal_mul]
 congr 1;have h5 : Gamma (5 / 12) ≠ 0 := xB xg;have g5 : Gamma (5 / 12) ≠ 0 := h5;have g1 : Gamma (1 / 4) ≠ 0 := xB k6;have g25 : Gamma (25 / 24) ≠ 0 := xB xm;field_simp [g5, g1, g25]
lemma x4 :
  2 * sin (π / 8) * sin (π / 24) / sin (π / 12) =
   (1 + Y (1 + Y 3) ^ 2 -
    Y (1 + Y 3) * Y (3 * (1 + Y 3) / 2)) := by
 have h3 : Y 3 ^ 2 = 3 := qc
 have h13 : 0 < 1 + Y 3 := by positivity
 have h13_sq : Y (1 + Y 3) ^ 2 = 1 + Y 3 := sq_sqrt h13.le
 have hrad_sq : Y (3 * (1 + Y 3) / 2) ^ 2 = 3 * (1 + Y 3) / 2 :=
  sq_sqrt (by positivity)
 have h2sin : 2 * sin (π / 8) * sin (π / 24) =
   cos (π / 12) - cos (π / 6) := by
  have hsub := Real.cos_sub (π / 8) (π / 24);have hadd := Real.cos_add (π / 8) (π / 24)
  rw [show π / 8 - π / 24 = π / 12 by ring] at hsub
  rw [show π / 8 + π / 24 = π / 6 by ring] at hadd
  linarith
 have hs12_pos : 0 < sin (π / 12) :=
  sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
 have hsin_prod : 2 * sin (π / 12) * cos (π / 12) = 1 / 2 := by
  have := Real.sin_two_mul (π / 12)
  rw [show 2 * (π / 12) = π / 6 by ring, Real.sin_pi_div_six] at this
  linarith
 have hs12_sq : sin (π / 12) ^ 2 = (2 - Y 3) / 4 := by
  have := Real.cos_two_mul (π / 12)
  rw [show 2 * (π / 12) = π / 6 by ring, cos_pi_div_six,
   Real.cos_sq' (π / 12)] at this
  linarith
 have hrad_s12 : Y (1 + Y 3) * Y (3 * (1 + Y 3) / 2) *
   sin (π / 12) = Y 3 / 2 := by
  have hlhs_pos : 0 < Y (1 + Y 3) * Y (3 * (1 + Y 3) / 2) *
    sin (π / 12) := by positivity
  have hsq : (Y (1 + Y 3) * Y (3 * (1 + Y 3) / 2) *
    sin (π / 12)) ^ 2 = (Y 3 / 2) ^ 2 := by
   rw [mul_pow, mul_pow, h13_sq, hrad_sq, hs12_sq];ring_nf
   rw [show Y 3 ^ 3 = Y 3 * Y 3 ^ 2 by ring, h3];ring
  exact (sq_eq_sq₀ hlhs_pos.le (by positivity)).1 hsq
 rw [h2sin, cos_pi_div_six, h13_sq, div_eq_iff hs12_pos.ne']
 have h4 : (1 + (1 + Y 3)) * sin (π / 12) ^ 2 = 1 / 4 := by rw [hs12_sq];ring_nf;rw [h3];ring
 have hcs : cos (π / 12) * sin (π / 12) = 1 / 4 := by linarith [hsin_prod]
 have hres : (cos (π / 12) - Y 3 / 2) * sin (π / 12) =
   (2 + Y 3 - Y (1 + Y 3) * Y (3 * (1 + Y 3) / 2)) *
    sin (π / 12) * sin (π / 12) := by
  have hsq : sin (π / 12) * sin (π / 12) = sin (π / 12) ^ 2 := (sq _).symm;rw [mul_assoc, hsq];linear_combination hcs - h4 + sin (π / 12) * hrad_s12
 have hres' := mul_right_cancel₀ hs12_pos.ne' hres;linarith [hres']
lemma x5 :
  (Gamma (2 / 3) * Gamma (11 / 12) /
    (Gamma (4 / 3) * Gamma (1 / 4) * Y (1 + Y 3))) *
   (1 / 2 * Gamma (4 / 3) * Gamma (3 / 8) /
    (Gamma (3 / 4) * Gamma (23 / 24))) /
   ((2 : X) ^ (-5 / 6 : X) * Gamma (2 / 3) * Gamma (1 / 8) /
    (Gamma (1 / 4) * Gamma (13 / 24))) =
  (1 / Y (1 + Y 3) + Y (1 + Y 3)) -
   Y (3 * (1 + Y 3) / 2) := by
 have hpi : 0 < π := pi_pos;have hspi : Y π ≠ 0 := (sqrt_pos.2 hpi).ne'
 have hs12 : sin (π / 12) ≠ 0 :=
  (sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)).ne'
 have hs8 : sin (π / 8) ≠ 0 :=
  (sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)).ne'
 have hs24 : sin (π / 24) ≠ 0 :=
  (sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)).ne'
 have href8 : Gamma (1 / 8) * Gamma (7 / 8) = π / sin (π / 8) := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 8)
  rw [show (1 : X) - 1 / 8 = 7 / 8 by ring, show π * (1 / 8) = π / 8 by ring] at h
  exact h
 have hdup8 : Gamma (3 / 8) * Gamma (7 / 8) =
   Gamma (3 / 4) * (2 : X) ^ (1 / 4 : X) * Y π := by
  have h := Real.Gamma_mul_Gamma_add_half (3 / 8)
  rw [show (3 / 8 : X) + 1 / 2 = 7 / 8 by ring, show 2 * (3 / 8 : X) = 3 / 4 by ring,
   show (1 : X) - 3 / 4 = 1 / 4 by ring] at h
  exact h
 have href24 : Gamma (1 / 24) * Gamma (23 / 24) = π / sin (π / 24) := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 24)
  rw [show (1 : X) - 1 / 24 = 23 / 24 by ring, show π * (1 / 24) = π / 24 by ring] at h
  exact h
 have hdup24 : Gamma (1 / 24) * Gamma (13 / 24) =
   Gamma (1 / 12) * (2 : X) ^ (11 / 12 : X) * Y π := by
  have h := Real.Gamma_mul_Gamma_add_half (1 / 24)
  rw [show (1 / 24 : X) + 1 / 2 = 13 / 24 by ring, show 2 * (1 / 24 : X) = 1 / 12 by ring,
   show (1 : X) - 1 / 12 = 11 / 12 by ring] at h
  exact h
 have href12 : Gamma (1 / 12) * Gamma (11 / 12) = π / sin (π / 12) := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 12)
  rw [show (1 : X) - 1 / 12 = 11 / 12 by ring, show π * (1 / 12) = π / 12 by ring] at h
  exact h
 have h2pow : (2 : X) ^ (5 / 6 : X) * (2 : X) ^ (1 / 4 : X) * (2 : X) ^ (11 / 12 : X) = 4 := by
  have h0 : (0 : X) < 2 := two_pos
  rw [← rpow_add h0, ← rpow_add h0,
   show (5 / 6 : X) + 1 / 4 + 11 / 12 = 2 by ring, rpow_two];norm_num
 have g23 : Gamma (2 / 3) ≠ 0 := xB k4;have g43 : Gamma (4 / 3) ≠ 0 := xB k5;have g14 : Gamma (1 / 4) ≠ 0 := xB k6;have g34 : Gamma (3 / 4) ≠ 0 := xB k7;have g18 : Gamma (1 / 8) ≠ 0 := xB k9;have g78 : Gamma (7 / 8) ≠ 0 := xB xe;have g124 : Gamma (1 / 24) ≠ 0 := xB xj;have g2324 : Gamma (23 / 24) ≠ 0 := xB xl
 have hsr : Y (1 + Y 3) ≠ 0 := by positivity
 have hr1 : Gamma (3 / 8) / (Gamma (3 / 4) * Gamma (1 / 8)) =
   (2 : X) ^ (1 / 4 : X) * sin (π / 8) / Y π := by
  field_simp [g34, g18, hspi];apply mul_right_cancel₀ g78
  calc Gamma (3 / 8) * Y π * Gamma (7 / 8)
      = (Gamma (3 / 8) * Gamma (7 / 8)) * Y π := by ring
    _ = Gamma (3 / 4) * (2 : X) ^ (1 / 4 : X) * (Y π ^ 2) := by rw [hdup8];ring
    _ = Gamma (3 / 4) * (2 : X) ^ (1 / 4 : X) * π := by rw [sq_sqrt hpi.le]
    _ = Gamma (3 / 4) * (2 : X) ^ (1 / 4 : X) *
        (sin (π / 8) * (Gamma (1 / 8) * Gamma (7 / 8))) := by
        rw [href8, mul_div_cancel₀ _ hs8]
    _ = Gamma (3 / 4) * Gamma (1 / 8) * (2 : X) ^ (1 / 4 : X) * sin (π / 8) * Gamma (7 / 8) := by ring
 have hr2 : Gamma (13 / 24) / Gamma (23 / 24) =
   Gamma (1 / 12) * (2 : X) ^ (11 / 12 : X) * sin (π / 24) / Y π := by
  field_simp [g2324, hspi];apply mul_right_cancel₀ g124
  calc Gamma (13 / 24) * Y π * Gamma (1 / 24)
      = (Gamma (1 / 24) * Gamma (13 / 24)) * Y π := by ring
    _ = Gamma (1 / 12) * (2 : X) ^ (11 / 12 : X) * (Y π ^ 2) := by rw [hdup24];ring
    _ = Gamma (1 / 12) * (2 : X) ^ (11 / 12 : X) * π := by rw [sq_sqrt hpi.le]
    _ = Gamma (1 / 12) * (2 : X) ^ (11 / 12 : X) *
        (sin (π / 24) * (Gamma (1 / 24) * Gamma (23 / 24))) := by
        rw [href24, mul_div_cancel₀ _ hs24]
    _ = Gamma (23 / 24) * Gamma (1 / 12) * (2 : X) ^ (11 / 12 : X) * sin (π / 24) * Gamma (1 / 24) := by ring
 have hlhs_simp :
   (Gamma (2 / 3) * Gamma (11 / 12) /
     (Gamma (4 / 3) * Gamma (1 / 4) * Y (1 + Y 3))) *
    (1 / 2 * Gamma (4 / 3) * Gamma (3 / 8) /
     (Gamma (3 / 4) * Gamma (23 / 24))) /
    ((2 : X) ^ (-5 / 6 : X) * Gamma (2 / 3) * Gamma (1 / 8) /
     (Gamma (1 / 4) * Gamma (13 / 24))) =
   1 / Y (1 + Y 3) * (1 / 2) * (2 : X) ^ (5 / 6 : X) *
    Gamma (11 / 12) * (Gamma (3 / 8) / (Gamma (3 / 4) * Gamma (1 / 8))) *
    (Gamma (13 / 24) / Gamma (23 / 24)) := by
  have h2n : (2 : X) ^ (-5 / 6 : X) ≠ 0 := (rpow_pos_of_pos two_pos _).ne'
  have hp : (2 : X) ^ (5 / 6 : X) * (2 : X) ^ (-5 / 6 : X) = 1 := by rw [← rpow_add two_pos, show (5 / 6 : X) + (-5 / 6) = 0 by ring, rpow_zero]
  field_simp [g23, g43, g14, g34, g18, g2324, hsr, h2n]
  rw [show -(5 / 6 : X) = -5 / 6 by ring, mul_comm ((2 : X) ^ (-5 / 6 : X)), hp]
 rw [hlhs_simp, hr1, hr2]
 have hlhs2 :
   1 / Y (1 + Y 3) * (1 / 2) * (2 : X) ^ (5 / 6 : X) * Gamma (11 / 12) *
    ((2 : X) ^ (1 / 4 : X) * sin (π / 8) / Y π) *
    (Gamma (1 / 12) * (2 : X) ^ (11 / 12 : X) * sin (π / 24) / Y π) =
   (1 / Y (1 + Y 3)) *
    ((2 : X) ^ (5 / 6 : X) * (2 : X) ^ (1 / 4 : X) * (2 : X) ^ (11 / 12 : X)) / 2 *
    (Gamma (1 / 12) * Gamma (11 / 12)) / (Y π ^ 2) *
    (sin (π / 8) * sin (π / 24)) := by ring
 rw [hlhs2, h2pow, href12, sq_sqrt hpi.le]
 have hlhs3 :
   (1 / Y (1 + Y 3)) * 4 / 2 * (π / sin (π / 12)) / π *
    (sin (π / 8) * sin (π / 24)) =
   (2 * sin (π / 8) * sin (π / 24) / sin (π / 12)) /
    Y (1 + Y 3) := by
  field_simp [hpi.ne', hs12, hsr];norm_num
 rw [hlhs3, x4]
 have h13_sq : Y (1 + Y 3) ^ 2 = 1 + Y 3 :=
  sq_sqrt (by positivity)
 field_simp [hsr]
lemma x6 :
  (-(1 / 4) * (2 : X) ^ (-5 / 6 : X) * Gamma (2 / 3) * Gamma (5 / 8) /
    (Gamma (1 / 4) * Gamma (25 / 24))) *
   ((2 : X) ^ (-5 / 6 : X) * Gamma (2 / 3) * Gamma (1 / 8) /
    (Gamma (1 / 4) * Gamma (13 / 24))) =
  -(Gamma (2 / 3) * Gamma (11 / 12) /
    (Gamma (4 / 3) * Gamma (1 / 4) * Y (1 + Y 3))) *
   (2 : X) ^ (-5 / 6 : X) / Y (3 * (1 + Y 3) / 2) := by
 have hpi : 0 < π := pi_pos;have hspi : Y π ≠ 0 := (sqrt_pos.2 hpi).ne'
 have hs12_pos : 0 < sin (π / 12) :=
  sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
 have hG25 : Gamma (25 / 24) = (1 / 24) * Gamma (1 / 24) := by rw [show (25 / 24 : X) = 1 / 24 + 1 by ring, Real.Gamma_add_one (by positivity)]
 have hG43 : Gamma (4 / 3) = (1 / 3) * Gamma (1 / 3) := by rw [show (4 / 3 : X) = 1 / 3 + 1 by ring, Real.Gamma_add_one (by positivity)]
 have hdup8 : Gamma (1 / 8) * Gamma (5 / 8) =
   Gamma (1 / 4) * (2 : X) ^ (3 / 4 : X) * Y π := by
  have h := Real.Gamma_mul_Gamma_add_half (1 / 8)
  rw [show (1 / 8 : X) + 1 / 2 = 5 / 8 by ring, show 2 * (1 / 8 : X) = 1 / 4 by ring,
   show (1 : X) - 1 / 4 = 3 / 4 by ring] at h
  exact h
 have hdup24 : Gamma (1 / 24) * Gamma (13 / 24) =
   Gamma (1 / 12) * (2 : X) ^ (11 / 12 : X) * Y π := by
  have h := Real.Gamma_mul_Gamma_add_half (1 / 24)
  rw [show (1 / 24 : X) + 1 / 2 = 13 / 24 by ring, show 2 * (1 / 24 : X) = 1 / 12 by ring,
   show (1 : X) - 1 / 12 = 11 / 12 by ring] at h
  exact h
 have href12 : Gamma (1 / 12) * Gamma (11 / 12) = π / sin (π / 12) := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 12)
  rw [show (1 : X) - 1 / 12 = 11 / 12 by ring, show π * (1 / 12) = π / 12 by ring] at h
  exact h
 have href3 : Gamma (1 / 3) * Gamma (2 / 3) = π / sin (π / 3) := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : X) - 1 / 3 = 2 / 3 by ring, show π * (1 / 3) = π / 3 by ring] at h
  exact h
 have h2pow : (2 : X) ^ (-5 / 6 : X) * (2 : X) ^ (-5 / 6 : X) * (2 : X) ^ (3 / 4 : X) /
   (2 : X) ^ (11 / 12 : X) = (1 / 2) * (2 : X) ^ (-5 / 6 : X) := by
  have h0 : (0 : X) < 2 := two_pos
  rw [div_eq_mul_inv, ← rpow_neg h0.le, ← rpow_add h0, ← rpow_add h0,
   ← rpow_add h0]
  have hsum : (-5 / 6 : X) + (-5 / 6) + 3 / 4 + -(11 / 12) = -1 + (-5 / 6) := by ring
  rw [hsum, rpow_add h0, rpow_neg h0.le, rpow_one];ring
 have hrad_sin : Y (3 * (1 + Y 3) / 2) * sin (π / 12) =
   sin (π / 3) / Y (1 + Y 3) := by
  have h3 : Y 3 ^ 2 = 3 := qc
  have hs12_sq : sin (π / 12) ^ 2 = (2 - Y 3) / 4 := by
   have := Real.cos_two_mul (π / 12)
   rw [show 2 * (π / 12) = π / 6 by ring, cos_pi_div_six,
    Real.cos_sq' (π / 12)] at this
   linarith
  have hpos_l : 0 < Y (3 * (1 + Y 3) / 2) * sin (π / 12) := by positivity
  have hpos_r : 0 < sin (π / 3) / Y (1 + Y 3) := by rw [sin_pi_div_three];positivity
  have hsq : (Y (3 * (1 + Y 3) / 2) * sin (π / 12)) ^ 2 =
    (sin (π / 3) / Y (1 + Y 3)) ^ 2 := by
   rw [mul_pow, div_pow, sq_sqrt (by positivity), hs12_sq, Real.sq_sin_pi_div_three,
    sq_sqrt (by positivity)]
   field_simp [show (1 + Y 3) ≠ 0 by positivity]
   nlinarith only [h3]
  exact (sq_eq_sq₀ hpos_l.le hpos_r.le).1 hsq
 have g14 : Gamma (1 / 4) ≠ 0 := xB k6;have g13 : Gamma (1 / 3) ≠ 0 := xB k3;have g23 : Gamma (2 / 3) ≠ 0 := xB k4;have g112 : Gamma (1 / 12) ≠ 0 := xB xf;have h211 : (2 : X) ^ (11 / 12 : X) ≠ 0 := (rpow_pos_of_pos two_pos _).ne'
 have hsr : Y (1 + Y 3) ≠ 0 := by positivity
 have hrad : Y (3 * (1 + Y 3) / 2) ≠ 0 := by positivity
 have hs3 : sin (π / 3) ≠ 0 := by rw [sin_pi_div_three];positivity
 rw [hG25, hG43]
 have h1_eq : Gamma (2 / 3) = π / (sin (π / 3) * Gamma (1 / 3)) := by
  field_simp [hs3, g13]
  calc Gamma (2 / 3) * sin (π / 3) * Gamma (1 / 3)
      = sin (π / 3) * (Gamma (1 / 3) * Gamma (2 / 3)) := by ring
    _ = π := by rw [href3, mul_div_cancel₀ _ hs3]
 have h2_eq : (Gamma (1 / 12))⁻¹ = sin (π / 12) * Gamma (11 / 12) / π := by
  field_simp [hpi.ne', g112]
  symm
  calc Gamma (1 / 12) * sin (π / 12) * Gamma (11 / 12)
      = (Gamma (1 / 12) * Gamma (11 / 12)) * sin (π / 12) := by ring
    _ = π := by rw [href12, div_mul_cancel₀ _ hs12_pos.ne']
 calc (-(1 / 4) * (2 : X) ^ (-5 / 6 : X) * Gamma (2 / 3) * Gamma (5 / 8) /
         (Gamma (1 / 4) * (1 / 24 * Gamma (1 / 24)))) *
       ((2 : X) ^ (-5 / 6 : X) * Gamma (2 / 3) * Gamma (1 / 8) /
         (Gamma (1 / 4) * Gamma (13 / 24)))
     = -6 * ((2 : X) ^ (-5 / 6 : X) * (2 : X) ^ (-5 / 6 : X)) * Gamma (2 / 3) ^ 2 *
         (Gamma (1 / 8) * Gamma (5 / 8)) /
         (Gamma (1 / 4) ^ 2 * (Gamma (1 / 24) * Gamma (13 / 24))) := by ring
   _ = -6 * ((2 : X) ^ (-5 / 6 : X) * (2 : X) ^ (-5 / 6 : X) * (2 : X) ^ (3 / 4 : X) /
         (2 : X) ^ (11 / 12 : X)) * Gamma (2 / 3) ^ 2 /
         (Gamma (1 / 4) * Gamma (1 / 12)) := by
       rw [hdup8, hdup24];field_simp [g14, g112, hspi, h211]
   _ = -3 * (2 : X) ^ (-5 / 6 : X) * Gamma (2 / 3) ^ 2 /
         (Gamma (1 / 4) * Gamma (1 / 12)) := by rw [h2pow];ring
   _ = -3 * (2 : X) ^ (-5 / 6 : X) *
         (Gamma (2 / 3) * (π / (sin (π / 3) * Gamma (1 / 3)))) *
         (sin (π / 12) * Gamma (11 / 12) / π) / Gamma (1 / 4) := by
       have hsq : Gamma (2 / 3) ^ 2 =
           Gamma (2 / 3) * (π / (sin (π / 3) * Gamma (1 / 3))) := by
         rw [sq];congr 1
       rw [hsq, div_eq_mul_inv, mul_inv, h2_eq]
       ring
   _ = -(Gamma (2 / 3) * Gamma (11 / 12) /
         ((1 / 3 * Gamma (1 / 3)) * Gamma (1 / 4) * Y (1 + Y 3))) *
         (2 : X) ^ (-5 / 6 : X) / Y (3 * (1 + Y 3) / 2) := by
       field_simp [hpi.ne', hs3, hs12_pos.ne', g13, g14, hsr, hrad]
       rw [show (sin (π / 12) * Y (1 + Y 3) *
           Y (3 * (1 + Y 3) / 2)) =
           (Y (3 * (1 + Y 3) / 2) * sin (π / 12)) *
             Y (1 + Y 3) by ring, hrad_sin]
       field_simp [hsr]
def x7 : Z := ⟨-1 / 2, Y 3 / 2⟩
lemma x8 : x7 ^ 2 + x7 + 1 = 0 := by
 apply Complex.ext
 · simp only [x7,sq,add_re,mul_re,one_re,zero_re];nlinarith only [qc]
 · simp only [x7,sq,add_im,mul_im,one_im,add_zero,zero_im];ring
lemma x9 : x7 ^ 3 = 1 := by linear_combination (x7 - 1) * x8
lemma za : T x7 = x7 ^ 2 := by
 apply Complex.ext
 · simp only [x7,conj_re,sq,mul_re];nlinarith only [qc]
 · simp only [x7,conj_im,sq,mul_im];ring
lemma zb : T (x7 ^ 2) = x7 := by rw [map_pow, za];linear_combination x7 * (x7 - 1) * x8
def zc : X :=
 Gamma (2 / 3) * Gamma (11 / 12) /
  (Gamma (4 / 3) * Gamma (1 / 4) * Y (1 + Y 3))
def zd : X :=
 Gamma (1 / 3) * Gamma (11 / 12) /
  (Gamma (1 / 4) * Y (1 + Y 3))
lemma ze : 0 < zc := by
 dsimp [zc];have g23 := gP k4;have g1112 := gP xi;have g43 := gP k5;have g14 := gP k6;positivity
lemma zf : 0 < zd := by
 dsimp [zd];have g13 := gP k3;have g1112 := gP xi;have g14 := gP k6;positivity
def zg : X := 1 / Y (1 + Y 3)
def zh : X := zg + 1 / zg
def zi : X := Y (zh ^ 2 - 1)
lemma zj : zh = 1 / Y (1 + Y 3) + Y (1 + Y 3) := by simp only [zh,zg,one_div,div_inv_eq_mul,one_mul]
lemma zk : zi = Y (3 * (1 + Y 3) / 2) := by
 dsimp [zi];congr 1
 have h13 : 0 < 1 + Y 3 := by positivity
 have hsq : Y (1 + Y 3) ^ 2 = 1 + Y 3 := sq_sqrt h13.le;have h3 : Y 3 ^ 2 = 3 := qc
 have hne1 : Y (1 + Y 3) ≠ 0 := by positivity
 have hne2 : Y 3 - 1 ≠ 0 := by nlinarith only [h3, qd]
 rw [zj]
 have hσ2 : (1 / Y (1 + Y 3)) ^ 2 = (Y 3 - 1) / 2 := by rw [div_pow, one_pow, hsq];field_simp;nlinarith only [h3]
 have h1σ2 : Y (1 + Y 3) ^ 2 = 1 + Y 3 := hsq
 calc (1 / Y (1 + Y 3) + Y (1 + Y 3)) ^ 2 - 1
     = (1 / Y (1 + Y 3)) ^ 2 + Y (1 + Y 3) ^ 2 + 1 := by field_simp [hne1];ring
   _ = (Y 3 - 1) / 2 + (1 + Y 3) + 1 := by rw [hσ2, h1σ2]
   _ = 3 * (1 + Y 3) / 2 := by ring
lemma zl : 0 < zi := by rw [zk];positivity
lemma zm : zh ^ 2 - zi ^ 2 = 1 := by
 dsimp [zi]
 have hpos : 0 < zh ^ 2 - 1 := by
  have : zi ^ 2 = 3 * (1 + Y 3) / 2 := by rw [zk, sq_sqrt (by positivity)]
  have h1 : zh ^ 2 - 1 = (1 / Y (1 + Y 3) + Y (1 + Y 3)) ^ 2 - 1 := by rw [zj]
  have h3 : Y 3 ^ 2 = 3 := qc
  have h13 : Y (1 + Y 3) ^ 2 = 1 + Y 3 := sq_sqrt (by positivity)
  have hne : Y (1 + Y 3) ≠ 0 := by positivity
  have h4 : (1 / Y (1 + Y 3) + Y (1 + Y 3)) ^ 2 - 1 =
    3 * (1 + Y 3) / 2 := by
   field_simp [hne];rw [h13];nlinarith only [h3]
  rw [h1, h4];positivity
 rw [sq_sqrt hpos.le];ring
def zn (u : Z) : Z := u * xE (5 / 12) (3 / 4) (4 / 3) (u ^ 3)
def zo (u : Z) : Z := xE (1 / 12) (5 / 12) (2 / 3) (u ^ 3)
def zp (u : Z) : Z := (zc : Z) * zn u / zo u
def zq (u : Z) : Z := u * xE (1 / 3) (2 / 3) (4 / 3) (u ^ 3)
def zr (u : Z) : Z := (zc : Z) * zq u
def zs : Z := -x7 ^ 2
lemma zt : zs ^ 3 = -1 := by
 dsimp [zs];calc (-x7 ^ 2) ^ 3 = -(x7 ^ 3) ^ 2 := by ring
   _ = -1 := by rw [x9];ring
lemma zu : T zs = -x7 := by dsimp [zs];rw [map_neg, zb]
lemma zv : zs * (-x7) = 1 := by
 dsimp [zs];calc (-x7 ^ 2) * (-x7) = x7 ^ 3 := by ring
   _ = 1 := x9
lemma zw : zs ≠ 0 := by intro h;have := zv;rw [h, zero_mul] at this;norm_num at this
lemma zx : 1 / T zs = zs := by
 rw [zu, div_eq_iff (by intro h;have := zv;rw [h, mul_zero] at this;norm_num at this)]
 exact zv.symm
def zy : Set Z := { u : Z | 0 < u.im ∧ 0 < (u * (-x7 ^ 2)).im }
lemma zz {u : Z} (hu : u ∈ zy) : u ≠ 0 := by intro h;have := hu.1;rw [h, zero_im] at this;exact lt_irrefl _ this
lemma zA : IsOpen zy := by
 have h1 : IsOpen { u : Z | 0 < u.im } := isOpen_lt continuous_const Complex.continuous_im
 have h2 : IsOpen { u : Z | 0 < (u * (-x7 ^ 2)).im } :=
  isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_id.mul continuous_const))
 exact h1.inter h2
lemma zB : Convex X zy := by
 intro x hx y hy a b ha hb hab
 have hsm : ∀ r : X, ∀ z : Z, (r • z).im = r * z.im := fun r z => by
  simp only [real_smul,mul_im,ofReal_re,ofReal_im,zero_mul,add_zero]
 have hsm2 : ∀ r : X, ∀ z : Z, ((r • z) * (-x7 ^ 2)).im = r * (z * (-x7 ^ 2)).im := fun r z => by
  rw [real_smul, mul_assoc, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
 refine ⟨?_, ?_⟩
 ·
  rw [add_im, hsm, hsm]
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  ·
   have hb1 : b = 1 := by linarith
   subst hb1;simpa using hy.1
  · exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx.1) (mul_nonneg hb hy.1.le)
 ·
  rw [add_mul, add_im, hsm2, hsm2]
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  ·
   have hb1 : b = 1 := by linarith
   subst hb1;simpa using hy.2
  · exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx.2) (mul_nonneg hb hy.2.le)
lemma zC {h : Z → Z} (hh : ∀ u ∈ zy, HasDerivAt h 0 u)
  {u v : Z} (hu : u ∈ zy) (hv : v ∈ zy) : h u = h v := by
 let γ : X → Z := fun t => ((1 - t : X) : Z) * u + (t : Z) * v
 have hγ_mem : ∀ t ∈ Icc (0 : X) 1, γ t ∈ zy := by
  intro t ht
  simpa [γ, real_smul] using zB hu hv (sub_nonneg.2 ht.2) ht.1 (by ring)
 have hderiv : ∀ t ∈ uIcc (0 : X) 1, HasDerivAt (fun s => h (γ s)) 0 t := by
  intro t ht;rw [uIcc_of_le zero_le_one] at ht
  have hγd : HasDerivAt γ (v - u) t := by
   have d1 : HasDerivAt (fun s : X => ((1 - s : X) : Z) * u) ((-1 : Z) * u) t := by simpa using (((hasDerivAt_id t).const_sub (1 : X)).ofReal_comp).mul_const u
   have d2 : HasDerivAt (fun s : X => (s : Z) * v) ((1 : Z) * v) t := by simpa using ((hasDerivAt_id t).ofReal_comp).mul_const v
   exact (d1.add d2).congr_deriv (by ring)
  have hcomp : HasDerivAt (h ∘ γ) ((v - u) • (0 : Z)) t := (hh (γ t) (hγ_mem t ht)).scomp t hγd;rw [smul_zero] at hcomp;exact hcomp
 have hint : ∫ _ in (0 : X)..1, (0 : Z) = h (γ 1) - h (γ 0) :=
  integral_eq_sub_of_hasDerivAt hderiv continuousOn_const.intervalIntegrable
 simp only [intervalIntegral.integral_zero, γ, sub_zero, sub_self, ofReal_zero, zero_mul,
  ofReal_one, one_mul, zero_add, add_zero] at hint
 exact (sub_eq_zero.1 hint.symm).symm
lemma zD {h : Z → Z} (hh : ∀ u ∈ ball (0 : Z) 1, HasDerivAt h 0 u)
  {u v : Z} (hu : u ∈ ball (0 : Z) 1) (hv : v ∈ ball (0 : Z) 1) : h u = h v := by
 let γ : X → Z := fun t => ((1 - t : X) : Z) * u + (t : Z) * v
 have hγ_mem : ∀ t ∈ Icc (0 : X) 1, γ t ∈ ball (0 : Z) 1 := by
  intro t ht
  simpa [γ, real_smul] using (convex_ball (0 : Z) 1) hu hv (sub_nonneg.2 ht.2) ht.1 (by ring)
 have hderiv : ∀ t ∈ uIcc (0 : X) 1, HasDerivAt (fun s => h (γ s)) 0 t := by
  intro t ht;rw [uIcc_of_le zero_le_one] at ht
  have hγd : HasDerivAt γ (v - u) t := by
   have d1 : HasDerivAt (fun s : X => ((1 - s : X) : Z) * u) ((-1 : Z) * u) t := by simpa using (((hasDerivAt_id t).const_sub (1 : X)).ofReal_comp).mul_const u
   have d2 : HasDerivAt (fun s : X => (s : Z) * v) ((1 : Z) * v) t := by simpa using ((hasDerivAt_id t).ofReal_comp).mul_const v
   exact (d1.add d2).congr_deriv (by ring)
  have hcomp : HasDerivAt (h ∘ γ) ((v - u) • (0 : Z)) t := (hh (γ t) (hγ_mem t ht)).scomp t hγd;rw [smul_zero] at hcomp;exact hcomp
 have hint : ∫ _ in (0 : X)..1, (0 : Z) = h (γ 1) - h (γ 0) :=
  integral_eq_sub_of_hasDerivAt hderiv continuousOn_const.intervalIntegrable
 simp only [intervalIntegral.integral_zero, γ, sub_zero, sub_self, ofReal_zero, zero_mul,
  ofReal_one, one_mul, zero_add, add_zero] at hint
 exact (sub_eq_zero.1 hint.symm).symm
lemma zE : ‖zs‖ = 1 := by
 have h3 : Y 3 ^ 2 = 3 := qc
 have hωn : ‖x7‖ = 1 := by
  have hns : W x7 = 1 := by rw [normSq_apply];dsimp [x7];nlinarith only [h3]
  have : ‖x7‖ ^ 2 = 1 := by rw [Complex.sq_norm, hns]
  nlinarith only [this, norm_nonneg x7]
 dsimp [zs];rw [norm_neg, norm_pow, hωn, one_pow]
lemma zF : zs ∈ zy := by
 constructor
 ·
  change (-x7 ^ 2).im > 0
  have h1 : (-x7 ^ 2).im = Y 3 / 2 := by simp only [x7,sq,neg_im,mul_im];ring
  rw [h1];positivity
 ·
  have hmul : zs * (-x7 ^ 2) = x7 := by
   dsimp [zs];calc (-x7 ^ 2) * (-x7 ^ 2) = x7 ^ 3 * x7 := by ring
     _ = x7 := by rw [x9, one_mul]
  rw [hmul];change x7.im > 0;simp only [x7,gt_iff_lt,sqrt_pos,Nat.ofNat_pos,div_pos_iff_of_pos_left]
lemma zG : (1 / 2 : Z) * zs ∈ ball (0 : Z) 1 ∩ zy := by
 refine ⟨?_, ?_⟩
 · rw [mem_ball, dist_zero_right, norm_mul, zE, mul_one];norm_num
 ·
  constructor
  ·
   simp only [mul_im, show (1 / 2 : Z).re = 1 / 2 by norm_num,
    show (1 / 2 : Z).im = 0 by norm_num, zero_mul, add_zero]
   exact mul_pos k2 zF.1
  ·
   rw [show (1 / 2 : Z) * zs * (-x7 ^ 2) = (1 / 2 : Z) * (zs * (-x7 ^ 2)) by ring]
   simp only [mul_im, show (1 / 2 : Z).re = 1 / 2 by norm_num,
    show (1 / 2 : Z).im = 0 by norm_num, zero_mul, add_zero]
   exact mul_pos k2 zF.2
lemma zH (u : Z) : 1 / T u = u / (W u : Z) := by
 by_cases hu : u = 0
 · subst hu;simp only [map_zero,div_zero,ofReal_zero]
 ·
  have hns : (W u : Z) ≠ 0 :=
   ofReal_ne_zero.2 (normSq_pos.2 hu).ne'
  have hconj : T u ≠ 0 := fun h => hu (by simpa using congr_arg (T) h)
  rw [div_eq_div_iff hconj hns, mul_conj, one_mul]
lemma zI {u : Z} (hu : u ∈ zy) : 1 / T u ∈ zy := by
 have hu_ne : u ≠ 0 := zz hu;have hns : 0 < W u := normSq_pos.2 hu_ne;rw [zH, div_eq_mul_inv, mul_comm, ← Complex.ofReal_inv];constructor
 ·
  rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero];exact mul_pos (inv_pos.2 hns) hu.1
 ·
  rw [mul_assoc, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero];exact mul_pos (inv_pos.2 hns) hu.2
lemma zJ {u : Z} (hu : u ∈ zy) : 0 < (u * (-x7)).re := by
 have h3 : Y 3 ^ 2 = 3 := qc;have h3p : 0 < Y 3 := qd
 have him2 : (u * (-x7 ^ 2)).im = (1 / 2) * u.im + (Y 3 / 2) * u.re := by
  have hre : (-x7 ^ 2).re = 1 / 2 := by simp only [x7,sq,neg_re,mul_re];linear_combination (1 / 4 : X) * h3
  have him : (-x7 ^ 2).im = Y 3 / 2 := by simp only [x7,sq,neg_im,mul_im];ring
  rw [mul_im, hre, him];ring
 have hre1 : (u * (-x7)).re = (1 / 2) * u.re + (Y 3 / 2) * u.im := by
  have hre : (-x7).re = 1 / 2 := by simp only [x7,neg_re,one_div];norm_num
  have him : (-x7).im = -Y 3 / 2 := by simp only [x7,neg_im];ring
  rw [mul_re, hre, him];ring
 have hpos : 0 < 2 * Y 3 * (u * (-x7)).re := by
  have h1 := hu.1;have h2 := hu.2;rw [him2] at h2
  calc 2 * Y 3 * (u * (-x7)).re
      = Y 3 * u.re + Y 3 ^ 2 * u.im := by rw [hre1];ring
    _ = 2 * ((1 / 2) * u.im + (Y 3 / 2) * u.re) + 2 * u.im := by rw [h3];ring
    _ > 0 := by linarith
 exact pos_of_mul_pos_right hpos (by positivity)
lemma zK {u : Z} (hu : u ∈ zy) : u ^ 3 ∈ xN := by
 intro ⟨hre, him⟩;have h3 : Y 3 ^ 2 = 3 := qc;have h3p : 0 < Y 3 := qd
 have him2 : (u * (-x7 ^ 2)).im = (1 / 2) * u.im + (Y 3 / 2) * u.re := by
  have hre' : (-x7 ^ 2).re = 1 / 2 := by simp only [x7,sq,neg_re,mul_re];linear_combination (1 / 4 : X) * h3
  have him' : (-x7 ^ 2).im = Y 3 / 2 := by simp only [x7,sq,neg_im,mul_im];ring
  rw [mul_im, hre', him'];ring
 have hu3_re : (u ^ 3).re = u.re ^ 3 - 3 * u.re * u.im ^ 2 := by simp only [pow_three,mul_re,mul_im];ring
 have hu3_im : (u ^ 3).im = u.im * (3 * u.re ^ 2 - u.im ^ 2) := by simp only [pow_three,mul_re,mul_im];ring
 rw [hu3_im] at him
 rcases mul_eq_zero.mp him with hy0 | hsq
 · linarith [hu.1]
 ·
  have hfac : (u.im - Y 3 * u.re) * (u.im + Y 3 * u.re) = 0 := by linear_combination -hsq - u.re ^ 2 * h3
  have hsum_pos : 0 < u.im + Y 3 * u.re := by
   have := hu.2;rw [him2] at this;linarith
  have hy_eq : u.im = Y 3 * u.re := by
   rcases mul_eq_zero.mp hfac with h0 | h0
   · linarith
   · linarith
  have hx_pos : 0 < u.re := by
   have := hu.1;rw [hy_eq] at this;exact pos_of_mul_pos_right this h3p.le
  rw [hu3_re, hy_eq] at hre
  have : u.re ^ 3 - 3 * u.re * (Y 3 * u.re) ^ 2 = -8 * u.re ^ 3 := by linear_combination -3 * u.re ^ 3 * h3
  linarith only [pow_pos hx_pos 3, hre, this]
lemma zL {u : Z} (hu : u ∈ ball (0 : Z) 1) : u ^ 3 ∈ xN := by
 refine xP ?_
 rw [mem_ball, dist_zero_right] at hu ⊢
 rw [norm_pow];exact pow_lt_one₀ (norm_nonneg u) hu (Nat.succ_ne_zero 2)
lemma zM {u : Z} (hu : u ^ 3 ∈ xN) :
  1 - u ^ 3 ∈ slitPlane := by
 simpa using xF hu zero_le_one le_rfl
lemma zN {z : Z} (hz : z ∈ slitPlane) (r : X) :
  T (z ^ (r : Z)) = (T z) ^ (r : Z) := by
 have hz_ne : z ≠ 0 := slitPlane_ne_zero hz
 have hzc_ne : T z ≠ 0 := fun h => hz_ne (by simpa using congr_arg (T) h)
 have harg : z.arg ≠ π := by
  intro hpi;rw [Complex.arg_eq_pi_iff] at hpi
  rcases mem_slitPlane_iff.1 hz with hr | hi
  · linarith [hpi.1]
  · exact hi hpi.2
 rw [cpow_def_of_ne_zero hz_ne, cpow_def_of_ne_zero hzc_ne,
  ← Complex.exp_conj, map_mul, conj_ofReal, Complex.log_conj z harg]
lemma zO {a b c : X} (hb : 0 < b) (hcb : 0 < c - b) (hc : 0 < c)
  {u : Z} (hu : u ^ 3 ∈ xN) :
  HasDerivAt (fun x : Z => xE a b c (x ^ 3))
   (3 * u ^ 2 * ((a * b / c : X) * xE (a + 1) (b + 1) (c + 1) (u ^ 3))) u := by
 have h1 := xT (a := a) hb hcb hc hu
 have h2 : HasDerivAt (fun x : Z => x ^ 3) (3 * u ^ 2) u := by simpa using hasDerivAt_pow 3 u
 refine (h1.comp u h2).congr_deriv ?_
 ring
lemma zP {a b c : X} (hb : 0 < b) (hcb : 0 < c - b) (hc : 0 < c)
  {u : Z} (hu : u ^ 3 ∈ xN) :
  HasDerivAt (deriv (fun x : Z => xE a b c (x ^ 3)))
   (6 * u * ((a * b / c : X) * xE (a + 1) (b + 1) (c + 1) (u ^ 3)) +
    9 * u ^ 4 * (((a * b / c) * ((a + 1) * (b + 1) / (c + 1)) : X) *
     xE (a + 2) (b + 2) (c + 2) (u ^ 3))) u := by
 have hopen : IsOpen { x : Z | x ^ 3 ∈ xN } :=
  xO.preimage (continuous_pow 3)
 have hev : ∀ᶠ x in 𝓝 u, deriv (fun z => xE a b c (z ^ 3)) x =
   3 * x ^ 2 * ((a * b / c : X) * xE (a + 1) (b + 1) (c + 1) (x ^ 3)) := by
  filter_upwards [hopen.mem_nhds hu] with x hx
  exact (zO hb hcb hc hx).deriv
 have d1 : HasDerivAt (fun x : Z => 3 * x ^ 2) (6 * u) u := by simpa using ((hasDerivAt_pow 2 u).const_mul (3 : Z)).congr_deriv (by ring)
 have d2 := (zO (a := a + 1) (b := b + 1) (c := c + 1)
  (by linarith) (by linarith) (by linarith) hu).const_mul ((a * b / c : X) : Z)
 rw [show a + 1 + 1 = a + 2 by ring, show b + 1 + 1 = b + 2 by ring,
  show c + 1 + 1 = c + 2 by ring] at d2
 refine ((d1.mul d2).congr_of_eventuallyEq hev).congr_deriv ?_
 push_cast;ring
lemma zQ {u : Z} (hu : u ^ 3 ∈ xN) :
  HasDerivAt zn
   (xE (5 / 12) (3 / 4) (4 / 3) (u ^ 3) +
    3 * u ^ 3 * (((5 / 12) * (3 / 4) / (4 / 3) : X) *
     xE (17 / 12) (7 / 4) (7 / 3) (u ^ 3))) u := by
 have dF := zO (a := 5 / 12) (b := 3 / 4) (c := 4 / 3)
  k7 xs k5 hu
 have hid : HasDerivAt zn
   (1 * xE (5 / 12) (3 / 4) (4 / 3) (u ^ 3) +
    u * (3 * u ^ 2 * ((5 / 12 * (3 / 4) / (4 / 3) : X) *
     xE (5 / 12 + 1) (3 / 4 + 1) (4 / 3 + 1) (u ^ 3)))) u :=
  (hasDerivAt_id u).mul dF
 rw [show (5 / 12 + 1 : X) = 17 / 12 by ring, show (3 / 4 + 1 : X) = 7 / 4 by ring,
  show (4 / 3 + 1 : X) = 7 / 3 by ring] at hid
 exact hid.congr_deriv (by ring)
lemma zR {u : Z} (hu : u ^ 3 ∈ xN) :
  HasDerivAt (deriv zn)
   (12 * u ^ 2 * (((5 / 12) * (3 / 4) / (4 / 3) : X) *
     xE (17 / 12) (7 / 4) (7 / 3) (u ^ 3)) +
    9 * u ^ 5 * ((((5 / 12) * (3 / 4) / (4 / 3)) * ((17 / 12) * (7 / 4) / (7 / 3)) : X) *
     xE (29 / 12) (11 / 4) (10 / 3) (u ^ 3))) u := by
 have hopen : IsOpen { x : Z | x ^ 3 ∈ xN } :=
  xO.preimage (continuous_pow 3)
 have hev : ∀ᶠ x in 𝓝 u, deriv zn x =
   xE (5 / 12) (3 / 4) (4 / 3) (x ^ 3) +
    3 * x ^ 3 * (((5 / 12) * (3 / 4) / (4 / 3) : X) *
     xE (17 / 12) (7 / 4) (7 / 3) (x ^ 3)) := by
  filter_upwards [hopen.mem_nhds hu] with x hx
  exact (zQ hx).deriv
 have d1 := zO (a := 5 / 12) (b := 3 / 4) (c := 4 / 3)
  k7 xs k5 hu
 have d2p : HasDerivAt (fun x : Z => 3 * x ^ 3) (9 * u ^ 2) u := by simpa using ((hasDerivAt_pow 3 u).const_mul (3 : Z)).congr_deriv (by ring)
 have d2f := (zO (a := 17 / 12) (b := 7 / 4) (c := 7 / 3)
  (by norm_num) (by norm_num) (by norm_num) hu).const_mul (((5 / 12) * (3 / 4) / (4 / 3) : X) : Z)
 refine ((d1.add (d2p.mul d2f)).congr_of_eventuallyEq hev).congr_deriv ?_
 rw [show (5 / 12 + 1 : X) = 17 / 12 by ring, show (3 / 4 + 1 : X) = 7 / 4 by ring,
  show (4 / 3 + 1 : X) = 7 / 3 by ring, show (17 / 12 + 1 : X) = 29 / 12 by ring,
  show (7 / 4 + 1 : X) = 11 / 4 by ring, show (7 / 3 + 1 : X) = 10 / 3 by ring]
 push_cast;ring
lemma zS {u : Z} (hu : u ^ 3 ∈ xN) :
  (1 - u ^ 3) * deriv (deriv zn) u - (5 / 2 : Z) * u ^ 2 * deriv zn u -
   (5 / 16 : Z) * u * zn u = 0 := by
 rw [(zQ hu).deriv, (zR hu).deriv];have hode := xV (a := 5 / 12) (b := 3 / 4) (c := 4 / 3)
  k7 xs k5 hu
 rw [(xT (a := 5 / 12) (b := 3 / 4) (c := 4 / 3)
   k7 xs k5 hu).deriv,
  (xU (a := 5 / 12) (b := 3 / 4) (c := 4 / 3)
   k7 xs k5 hu).deriv] at hode
 rw [show (5 / 12 + 1 : X) = 17 / 12 by ring, show (3 / 4 + 1 : X) = 7 / 4 by ring,
  show (4 / 3 + 1 : X) = 7 / 3 by ring, show (5 / 12 + 2 : X) = 29 / 12 by ring,
  show (3 / 4 + 2 : X) = 11 / 4 by ring, show (4 / 3 + 2 : X) = 10 / 3 by ring] at hode
 dsimp [zn]
 push_cast at hode ⊢
 linear_combination (9 * u ^ 2) * hode
lemma zT {u : Z} (hu : u ^ 3 ∈ xN) :
  HasDerivAt zo
   (3 * u ^ 2 * (((1 / 12) * (5 / 12) / (2 / 3) : X) *
    xE (13 / 12) (17 / 12) (5 / 3) (u ^ 3))) u := by
 change HasDerivAt (fun x => xE (1 / 12) (5 / 12) (2 / 3) (x ^ 3)) _ u
 convert zO (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
  xg xn k4 hu using 2;norm_num
lemma zU {u : Z} (hu : u ^ 3 ∈ xN) :
  HasDerivAt (deriv zo)
   (6 * u * (((1 / 12) * (5 / 12) / (2 / 3) : X) *
     xE (13 / 12) (17 / 12) (5 / 3) (u ^ 3)) +
    9 * u ^ 4 * ((((1 / 12) * (5 / 12) / (2 / 3)) * ((13 / 12) * (17 / 12) / (5 / 3)) : X) *
     xE (25 / 12) (29 / 12) (8 / 3) (u ^ 3))) u := by
 change HasDerivAt (deriv (fun x => xE (1 / 12) (5 / 12) (2 / 3) (x ^ 3))) _ u
 convert zP (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
  xg xn k4 hu using 2 <;> norm_num
lemma zV {u : Z} (hu : u ^ 3 ∈ xN) :
  (1 - u ^ 3) * deriv (deriv zo) u - (5 / 2 : Z) * u ^ 2 * deriv zo u -
   (5 / 16 : Z) * u * zo u = 0 := by
 rw [(zT hu).deriv, (zU hu).deriv];have hode := xV (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
  xg xn k4 hu
 rw [(xT (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
   xg xn k4 hu).deriv,
  (xU (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
   xg xn k4 hu).deriv] at hode
 rw [show (1 / 12 + 1 : X) = 13 / 12 by ring, show (5 / 12 + 1 : X) = 17 / 12 by ring,
  show (2 / 3 + 1 : X) = 5 / 3 by ring, show (1 / 12 + 2 : X) = 25 / 12 by ring,
  show (5 / 12 + 2 : X) = 29 / 12 by ring, show (2 / 3 + 2 : X) = 8 / 3 by ring] at hode
 dsimp [zo]
 push_cast at hode ⊢
 linear_combination (9 * u) * hode
lemma zW {u : Z} (hu : u ^ 3 ∈ xN) :
  HasDerivAt zq
   (xE (1 / 3) (2 / 3) (4 / 3) (u ^ 3) +
    3 * u ^ 3 * (((1 / 3) * (2 / 3) / (4 / 3) : X) *
     xE (4 / 3) (5 / 3) (7 / 3) (u ^ 3))) u := by
 have dF := zO (a := 1 / 3) (b := 2 / 3) (c := 4 / 3)
  k4 xx k5 hu
 have hid : HasDerivAt zq
   (1 * xE (1 / 3) (2 / 3) (4 / 3) (u ^ 3) +
    u * (3 * u ^ 2 * ((1 / 3 * (2 / 3) / (4 / 3) : X) *
     xE (1 / 3 + 1) (2 / 3 + 1) (4 / 3 + 1) (u ^ 3)))) u :=
  (hasDerivAt_id u).mul dF
 rw [show (1 / 3 + 1 : X) = 4 / 3 by ring, show (2 / 3 + 1 : X) = 5 / 3 by ring,
  show (4 / 3 + 1 : X) = 7 / 3 by ring] at hid
 exact hid.congr_deriv (by ring)
lemma zX {u : Z} (hu : u ^ 3 ∈ xN) :
  HasDerivAt (deriv zq)
   (12 * u ^ 2 * (((1 / 3) * (2 / 3) / (4 / 3) : X) *
     xE (4 / 3) (5 / 3) (7 / 3) (u ^ 3)) +
    9 * u ^ 5 * ((((1 / 3) * (2 / 3) / (4 / 3)) * ((4 / 3) * (5 / 3) / (7 / 3)) : X) *
     xE (7 / 3) (8 / 3) (10 / 3) (u ^ 3))) u := by
 have hopen : IsOpen { x : Z | x ^ 3 ∈ xN } :=
  xO.preimage (continuous_pow 3)
 have hev : ∀ᶠ x in 𝓝 u, deriv zq x =
   xE (1 / 3) (2 / 3) (4 / 3) (x ^ 3) +
    3 * x ^ 3 * (((1 / 3) * (2 / 3) / (4 / 3) : X) *
     xE (4 / 3) (5 / 3) (7 / 3) (x ^ 3)) := by
  filter_upwards [hopen.mem_nhds hu] with x hx
  exact (zW hx).deriv
 have d1 := zO (a := 1 / 3) (b := 2 / 3) (c := 4 / 3)
  k4 xx k5 hu
 have d2p : HasDerivAt (fun x : Z => 3 * x ^ 3) (9 * u ^ 2) u := by simpa using ((hasDerivAt_pow 3 u).const_mul (3 : Z)).congr_deriv (by ring)
 have d2f := (zO (a := 4 / 3) (b := 5 / 3) (c := 7 / 3)
  (by norm_num) (by norm_num) (by norm_num) hu).const_mul (((1 / 3) * (2 / 3) / (4 / 3) : X) : Z)
 refine ((d1.add (d2p.mul d2f)).congr_of_eventuallyEq hev).congr_deriv ?_
 rw [show (1 / 3 + 1 : X) = 4 / 3 by ring, show (2 / 3 + 1 : X) = 5 / 3 by ring,
  show (4 / 3 + 1 : X) = 7 / 3 by ring, show (5 / 3 + 1 : X) = 8 / 3 by ring,
  show (7 / 3 + 1 : X) = 10 / 3 by ring]
 push_cast;ring
lemma zY {u : Z} (hu : u ^ 3 ∈ xN) :
  (1 - u ^ 3) * deriv (deriv zq) u - 2 * u ^ 2 * deriv zq u = 0 := by
 rw [(zW hu).deriv, (zX hu).deriv];have hode := xV (a := 1 / 3) (b := 2 / 3) (c := 4 / 3)
  k4 xx k5 hu
 rw [(xT (a := 1 / 3) (b := 2 / 3) (c := 4 / 3)
   k4 xx k5 hu).deriv,
  (xU (a := 1 / 3) (b := 2 / 3) (c := 4 / 3)
   k4 xx k5 hu).deriv] at hode
 rw [show (1 / 3 + 1 : X) = 4 / 3 by ring, show (2 / 3 + 1 : X) = 5 / 3 by ring,
  show (4 / 3 + 1 : X) = 7 / 3 by ring, show (1 / 3 + 2 : X) = 7 / 3 by ring,
  show (2 / 3 + 2 : X) = 8 / 3 by ring, show (4 / 3 + 2 : X) = 10 / 3 by ring] at hode
 push_cast at hode ⊢
 linear_combination (9 * u ^ 2) * hode
lemma zZ {f : Z → Z} {f' u : Z} (hu : u ≠ 0)
  (hf : HasDerivAt f f' (1 / T u)) :
  HasDerivAt (fun x : Z => T (f (1 / T x)))
   (-(T f') / u ^ 2) u := by
 rw [hasDerivAt_iff_isLittleO_nhds_zero] at hf ⊢
 let φ : Z → Z := fun h => 1 / T (u + h) - 1 / T u
 have hφ0 : Tendsto φ (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt (fun h : Z => 1 / T (u + h)) 0 :=
   (continuousAt_const.div (Complex.continuous_conj.continuousAt.comp (continuousAt_const.add continuousAt_id))
    (by simp only [add_zero,ne_eq,map_eq_zero,hu,not_false_eq_true]))
  have hc' : Tendsto (fun h : Z => 1 / T (u + h) - 1 / T u)
    (𝓝 0) (𝓝 (1 / T (u + 0) - 1 / T u)) :=
   hc.tendsto.sub tendsto_const_nhds
  simpa [φ] using hc'
 have hcomp := hf.comp_tendsto hφ0;have hconj_o : (fun h : Z => T (f (1 / T u + φ h) - f (1 / T u) - φ h * f')) =o[𝓝 0]
   (fun h => φ h) := by
  rw [Asymptotics.isLittleO_iff] at hcomp ⊢
  intro c hc
  filter_upwards [hcomp hc] with h hh
  dsimp only [Function.comp_def,smul_eq_mul] at hh;simpa only [norm_conj] using hh
 have hφ_bigO : φ =O[𝓝 (0 : Z)] (fun h : Z => h) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 / ‖u‖ ^ 2, ?_⟩
  have hball : ∀ᶠ h in 𝓝 (0 : Z), ‖h‖ ≤ ‖u‖ / 2 := by
   filter_upwards [ball_mem_nhds 0 (half_pos (norm_pos_iff.2 hu))] with h hh
   rw [mem_ball, dist_zero_right] at hh;exact hh.le
  filter_upwards [hball] with h hh
  have hu_h : u + h ≠ 0 := by
   intro h0;have heq : u = -h := eq_neg_of_add_eq_zero_left h0
   have : ‖u‖ = ‖h‖ := by rw [heq, norm_neg]
   linarith [norm_pos_iff.2 hu]
  have hstar : T (φ h) = -h / (u * (u + h)) := by
   dsimp [φ];simp only [map_sub,map_div₀,map_one,starRingEnd_self_apply];rw [div_sub_div _ _ hu_h hu];ring
  have hnorm_eq : ‖φ h‖ = ‖-h / (u * (u + h))‖ := by rw [← hstar, norm_conj]
  rw [hnorm_eq, norm_div, norm_neg, norm_mul]
  have hbd : ‖u‖ / 2 ≤ ‖u + h‖ := by
   have := norm_sub_le (u + h) h;simp only [add_sub_cancel_right] at this;linarith
  have hmul_pos : 0 < ‖u‖ * ‖u + h‖ := mul_pos (norm_pos_iff.2 hu) (by linarith [norm_pos_iff.2 hu])
  rw [div_le_iff₀ hmul_pos]
  calc ‖h‖ = (2 / ‖u‖ ^ 2 * ‖h‖) * (‖u‖ * (‖u‖ / 2)) := by
        have : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
        field_simp [this]
    _ ≤ (2 / ‖u‖ ^ 2 * ‖h‖) * (‖u‖ * ‖u + h‖) := by gcongr
 have hmain := hconj_o.trans_isBigO hφ_bigO;have hquad : (fun h : Z => T (φ h * f') - h * (-(T f') / u ^ 2)) =o[𝓝 0]
   (fun h : Z => h) := by
  have heq : ∀ᶠ h in 𝓝 (0 : Z),
    T (φ h * f') - h * (-(T f') / u ^ 2) =
     (T f' / (u ^ 2 * (u + h))) * (h * h) := by
   have hball : ∀ᶠ h in 𝓝 (0 : Z), u + h ≠ 0 := by
    filter_upwards [ball_mem_nhds 0 (half_pos (norm_pos_iff.2 hu))] with h hh
    intro h0;rw [mem_ball, dist_zero_right] at hh;have heq : u = -h := eq_neg_of_add_eq_zero_left h0
    have : ‖u‖ = ‖h‖ := by rw [heq, norm_neg]
    linarith [norm_pos_iff.2 hu]
   filter_upwards [hball] with h hu_h
   dsimp [φ];simp only [map_mul,map_sub,map_div₀,map_one,starRingEnd_self_apply];field_simp [hu, hu_h];ring
  have ho : (fun h : Z => (T f' / (u ^ 2 * (u + h))) * (h * h)) =o[𝓝 0] (fun h : Z => h) := by
   have h1 : (fun h : Z => T f' / (u ^ 2 * (u + h))) =O[𝓝 0] (fun _ : Z => (1 : Z)) := by
    refine Tendsto.isBigO_one (c := T f' / (u ^ 2 * (u + 0))) Z ?_
    exact (continuousAt_const.div ((continuousAt_const).mul (continuousAt_const.add continuousAt_id))
     (mul_ne_zero (pow_ne_zero 2 hu) (by simp only [Pi.add_apply,id_eq,add_zero,ne_eq,hu,not_false_eq_true]))).tendsto
   have h2 : (fun h : Z => h * h) =o[𝓝 0] (fun h : Z => h) := by
    rw [Asymptotics.isLittleO_iff];intro c hc
    filter_upwards [ball_mem_nhds 0 hc] with h hh
    rw [mem_ball, dist_zero_right] at hh;rw [norm_mul];gcongr
   exact (h1.mul_isLittleO h2).congr_right (fun h => one_mul h)
  exact ho.congr' (heq.mono fun _ h => h.symm) EventuallyEq.rfl
 refine (hmain.add hquad).congr' ?_ EventuallyEq.rfl
 filter_upwards with h
 have hplus : 1 / T (u + h) = 1 / T u + φ h := by dsimp [φ];ring
 rw [hplus, map_sub, map_sub];ring
lemma z0 {f : Z → Z}
  (hf1 : ∀ v ∈ zy, DifferentiableAt Z f v)
  (hf2 : ∀ v ∈ zy, DifferentiableAt Z (deriv f) v)
  (hode : ∀ v ∈ zy, (1 - v ^ 3) * deriv (deriv f) v - (5 / 2 : Z) * v ^ 2 * deriv f v -
   (5 / 16 : Z) * v * f v = 0) :
  ∀ u ∈ zy,
   let w : Z → Z := fun x => (x * (-x7)) ^ (-1 / 4 : Z) * T (f (1 / T x))
   DifferentiableAt Z w u ∧ DifferentiableAt Z (deriv w) u ∧
    (1 - u ^ 3) * deriv (deriv w) u - (5 / 2 : Z) * u ^ 2 * deriv w u -
     (5 / 16 : Z) * u * w u = 0 := by
 intro u hu;let Ψ : Z → Z := fun x => T (f (1 / T x));let α : Z → Z := fun x => (x * (-x7)) ^ (-1 / 4 : Z);let w : Z → Z := fun x => α x * Ψ x
 have hΨd : ∀ x ∈ zy, HasDerivAt Ψ (-(T (deriv f (1 / T x))) / x ^ 2) x := fun x hx =>
  zZ (zz hx) ((hf1 _ (zI hx)).hasDerivAt)
 have hΨd2 : ∀ x ∈ zy, HasDerivAt (deriv Ψ)
   (2 / x ^ 3 * T (deriv f (1 / T x)) +
    1 / x ^ 4 * T (deriv (deriv f) (1 / T x))) x := by
  intro x hx;have hx0 : x ≠ 0 := zz hx
  have hev : ∀ᶠ z in 𝓝 x, deriv Ψ z =
    -(T (deriv f (1 / T z))) / z ^ 2 := by
   filter_upwards [zA.mem_nhds hx] with z hz
   exact (hΨd z hz).deriv
  have df' := zZ hx0 ((hf2 _ (zI hx)).hasDerivAt);have dneg : HasDerivAt (fun z : Z => -(T (deriv f (1 / T z))))
    (-(-(T (deriv (deriv f) (1 / T x))) / x ^ 2)) x := df'.neg
  have dpow : HasDerivAt (fun z : Z => z ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  refine ((dneg.div dpow (pow_ne_zero 2 hx0)).congr_of_eventuallyEq hev).congr_deriv ?_
  field_simp [hx0];ring
 have hα_slit : ∀ x ∈ zy, x * (-x7) ∈ slitPlane := fun x hx =>
  mem_slitPlane_iff.2 (Or.inl (zJ hx))
 have hαd : ∀ x ∈ zy, HasDerivAt α (-(1 / 4 : Z) * α x / x) x := by
  intro x hx;have hx0 : x ≠ 0 := zz hx
  have hω0 : (-x7) ≠ 0 := by intro h;have := zv;rw [h, mul_zero] at this;norm_num at this
  have dmul : HasDerivAt (fun z : Z => z * (-x7)) (-x7) x := by simpa using (hasDerivAt_id x).mul_const (-x7)
  have dcp := (dmul.cpow (hasDerivAt_const x (-1 / 4 : Z)) (hα_slit x hx))
  refine dcp.congr_deriv ?_
  have hmul0 : x * (-x7) ≠ 0 := mul_ne_zero hx0 hω0
  have hsub : (-1 / 4 : Z) - 1 = (-1 / 4 : Z) + (-1 : Z) := by ring
  simp only [mul_zero,add_zero]
  rw [show (-1 / 4 : Z) * (x * (-x7)) ^ ((-1 / 4 : Z) - 1) * (-x7) =
    -(1 / 4 : Z) * ((x * (-x7)) ^ ((-1 / 4 : Z) - 1) * (x * (-x7))) / x by
     field_simp [hx0],
   hsub, cpow_add _ _ hmul0, Complex.cpow_neg_one, inv_mul_cancel_right₀ hmul0]
 have hαd2 : ∀ x ∈ zy, HasDerivAt (deriv α) ((5 / 16 : Z) * α x / x ^ 2) x := by
  intro x hx;have hx0 : x ≠ 0 := zz hx
  have hev : ∀ᶠ z in 𝓝 x, deriv α z = -(1 / 4 : Z) * α z / z := by
   filter_upwards [zA.mem_nhds hx] with z hz
   exact (hαd z hz).deriv
  have hd := (((hαd x hx).const_mul (-(1 / 4 : Z))).div (hasDerivAt_id x) hx0).congr_of_eventuallyEq hev
  refine hd.congr_deriv ?_
  simp only [id_eq];field_simp [hx0];ring
 have hwd : ∀ x ∈ zy, HasDerivAt w (deriv α x * Ψ x + α x * deriv Ψ x) x := fun x hx =>
  ((hαd x hx).congr_deriv (hαd x hx).deriv.symm).mul
   ((hΨd x hx).congr_deriv (hΨd x hx).deriv.symm)
 have hwd2 : HasDerivAt (deriv w)
   (deriv (deriv α) u * Ψ u + 2 * deriv α u * deriv Ψ u + α u * deriv (deriv Ψ) u) u := by
  have hev : ∀ᶠ x in 𝓝 u, deriv w x = deriv α x * Ψ x + α x * deriv Ψ x := by
   filter_upwards [zA.mem_nhds hu] with x hx
   exact (hwd x hx).deriv
  have da1 := (hαd2 u hu).congr_deriv (hαd2 u hu).deriv.symm;have da0 := (hαd u hu).congr_deriv (hαd u hu).deriv.symm;have dp1 := (hΨd2 u hu).congr_deriv (hΨd2 u hu).deriv.symm;have dp0 := (hΨd u hu).congr_deriv (hΨd u hu).deriv.symm
  exact ((da1.mul dp0 |>.add (da0.mul dp1)).congr_of_eventuallyEq hev).congr_deriv (by ring)
 refine ⟨(hwd u hu).differentiableAt, hwd2.differentiableAt, ?_⟩
 rw [(hwd u hu).deriv, hwd2.deriv, (hαd u hu).deriv, (hαd2 u hu).deriv,
  (hΨd u hu).deriv, (hΨd2 u hu).deriv]
 have hu0 : u ≠ 0 := zz hu;have hode_v := congr_arg (T) (hode (1 / T u) (zI hu));simp only [map_zero,map_sub,map_mul,map_pow,map_one,map_div₀,map_ofNat,starRingEnd_self_apply] at hode_v
 have halg : (1 - u ^ 3) * ((5 / 16 : Z) * α u / u ^ 2 * Ψ u +
   2 * (-(1 / 4 : Z) * α u / u) * (-(T (deriv f (1 / T u))) / u ^ 2) +
   α u * (2 / u ^ 3 * T (deriv f (1 / T u)) +
    1 / u ^ 4 * T (deriv (deriv f) (1 / T u)))) -
   (5 / 2 : Z) * u ^ 2 * (-(1 / 4 : Z) * α u / u * Ψ u +
    α u * (-(T (deriv f (1 / T u))) / u ^ 2)) -
   (5 / 16 : Z) * u * w u =
   -(α u / u) * ((1 - (1 / u) ^ 3) * T (deriv (deriv f) (1 / T u)) -
    (5 / 2 : Z) * (1 / u) ^ 2 * T (deriv f (1 / T u)) -
    (5 / 16 : Z) * (1 / u) * Ψ u) := by
  dsimp [w, Ψ];field_simp [hu0];ring
 rw [halg, hode_v, mul_zero]
lemma z1 :
  ∀ u ∈ ball (0 : Z) 1 ∪ zy,
   (1 - u ^ 3) ^ (5 / 6 : Z) * (deriv zn u * zo u - zn u * deriv zo u) = 1 := by
 have hdiff : ∀ u, u ^ 3 ∈ xN →
   HasDerivAt (fun x => (1 - x ^ 3) ^ (5 / 6 : Z) * (deriv zn x * zo x - zn x * deriv zo x)) 0 u := by
  intro u hu;have hslit : 1 - u ^ 3 ∈ slitPlane := zM hu;have hne : 1 - u ^ 3 ≠ 0 := slitPlane_ne_zero hslit;have dp : HasDerivAt (fun x : Z => (1 - x ^ 3) ^ (5 / 6 : Z))
    ((5 / 6 : Z) * (1 - u ^ 3) ^ ((5 / 6 : Z) - 1) * -(3 * u ^ 2)) u := by
   simpa using ((hasDerivAt_pow 3 u).const_sub 1).cpow (hasDerivAt_const u (5 / 6 : Z)) hslit
  have dy1 := (zQ hu).congr_deriv (zQ hu).deriv.symm;have dy1' := (zR hu).congr_deriv (zR hu).deriv.symm;have dy2 := (zT hu).congr_deriv (zT hu).deriv.symm;have dy2' := (zU hu).congr_deriv (zU hu).deriv.symm;have dw : HasDerivAt (fun x => deriv zn x * zo x - zn x * deriv zo x)
    (deriv (deriv zn) u * zo u - zn u * deriv (deriv zo) u) u :=
   ((dy1'.mul dy2).sub (dy1.mul dy2')).congr_deriv (by ring)
  refine (dp.mul dw).congr_deriv ?_
  have hode1 := zS hu;have hode2 := zV hu
  have hcp : (1 - u ^ 3) ^ (5 / 6 : Z) = (1 - u ^ 3) ^ ((5 / 6 : Z) - 1) * (1 - u ^ 3) := by
   conv_lhs => rw [show (5 / 6 : Z) = ((5 / 6 : Z) - 1) + 1 by ring]
   rw [cpow_add _ _ hne, cpow_one]
  rw [hcp]
  have hW_ode : (1 - u ^ 3) * (deriv (deriv zn) u * zo u - zn u * deriv (deriv zo) u) =
    (5 / 2 : Z) * u ^ 2 * (deriv zn u * zo u - zn u * deriv zo u) := by
   linear_combination zo u * hode1 - zn u * hode2
  calc (5 / 6 : Z) * (1 - u ^ 3) ^ ((5 / 6 : Z) - 1) * -(3 * u ^ 2) *
          (deriv zn u * zo u - zn u * deriv zo u) +
        (1 - u ^ 3) ^ ((5 / 6 : Z) - 1) * (1 - u ^ 3) *
          (deriv (deriv zn) u * zo u - zn u * deriv (deriv zo) u)
      = (1 - u ^ 3) ^ ((5 / 6 : Z) - 1) *
          ((1 - u ^ 3) * (deriv (deriv zn) u * zo u - zn u * deriv (deriv zo) u) -
            (5 / 2 : Z) * u ^ 2 * (deriv zn u * zo u - zn u * deriv zo u)) := by ring
    _ = 0 := by rw [hW_ode, sub_self, mul_zero]
 have hball : ∀ u ∈ ball (0 : Z) 1,
   (1 - u ^ 3) ^ (5 / 6 : Z) * (deriv zn u * zo u - zn u * deriv zo u) = 1 := by
  intro u hu
  rw [zD (fun x hx => hdiff x (zL hx))
   hu (mem_ball_self one_pos)]
  have h0 : (0 : Z) ^ 3 ∈ xN := zL (mem_ball_self one_pos)
  have hy1_0 : zn 0 = 0 := by simp only [zn,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_mul]
  have hy2_0 : zo 0 = 1 := by
   simpa [zo] using xL (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
    xg xn k4
  have hdy1_0 : deriv zn 0 = 1 := by
   rw [(zQ h0).deriv];simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,xL (a := 5 / 12) (b := 3 / 4) (c := 4 / 3) k7 xs k5,mul_zero,ofReal_div,ofReal_mul,ofReal_ofNat,zero_mul,add_zero]
  simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,sub_zero,one_cpow,hdy1_0,hy2_0,mul_one,hy1_0,zero_mul]
 intro u hu
 rcases hu with hu | hu
 · exact hball u hu
 ·
  rw [zC (fun x hx => hdiff x (zK hx))
   hu zG.2]
  exact hball ((1 / 2 : Z) * zs) zG.1
lemma z2 {w : Z → Z}
  (hw1 : ∀ u ∈ zy, DifferentiableAt Z w u)
  (hw2 : ∀ u ∈ zy, DifferentiableAt Z (deriv w) u)
  (hode : ∀ u ∈ zy, (1 - u ^ 3) * deriv (deriv w) u - (5 / 2 : Z) * u ^ 2 * deriv w u -
   (5 / 16 : Z) * u * w u = 0)
  {A B : Z}
  (hA : (deriv w zs * zo zs - w zs * deriv zo zs) * (2 : Z) ^ (5 / 6 : Z) = A)
  (hB : (deriv zn zs * w zs - zn zs * deriv w zs) * (2 : Z) ^ (5 / 6 : Z) = B) :
  ∀ u ∈ zy, w u = A * zn u + B * zo u := by
 have hconst : ∀ f₁ f₂ : Z → Z,
   (∀ u ∈ zy, DifferentiableAt Z f₁ u ∧ DifferentiableAt Z (deriv f₁) u ∧
    (1 - u ^ 3) * deriv (deriv f₁) u - (5 / 2 : Z) * u ^ 2 * deriv f₁ u -
     (5 / 16 : Z) * u * f₁ u = 0) →
   (∀ u ∈ zy, DifferentiableAt Z f₂ u ∧ DifferentiableAt Z (deriv f₂) u ∧
    (1 - u ^ 3) * deriv (deriv f₂) u - (5 / 2 : Z) * u ^ 2 * deriv f₂ u -
     (5 / 16 : Z) * u * f₂ u = 0) →
   ∀ u ∈ zy,
    (deriv f₁ u * f₂ u - f₁ u * deriv f₂ u) * (1 - u ^ 3) ^ (5 / 6 : Z) =
     (deriv f₁ zs * f₂ zs - f₁ zs * deriv f₂ zs) * (1 - zs ^ 3) ^ (5 / 6 : Z) := by
  intro f₁ f₂ h1 h2 u hu
  refine zC
   (h := fun x => (deriv f₁ x * f₂ x - f₁ x * deriv f₂ x) * (1 - x ^ 3) ^ (5 / 6 : Z))
   (fun x hx => ?_) hu zF
  have hslit : 1 - x ^ 3 ∈ slitPlane := zM (zK hx);have hne : 1 - x ^ 3 ≠ 0 := slitPlane_ne_zero hslit;obtain ⟨d1, d1', o1⟩ := h1 x hx;obtain ⟨d2, d2', o2⟩ := h2 x hx;have dw : HasDerivAt (fun x => deriv f₁ x * f₂ x - f₁ x * deriv f₂ x)
    (deriv (deriv f₁) x * f₂ x - f₁ x * deriv (deriv f₂) x) x := by
   refine ((d1'.hasDerivAt.mul d2.hasDerivAt).sub (d1.hasDerivAt.mul d2'.hasDerivAt)).congr_deriv ?_
   ring
  have dp : HasDerivAt (fun z : Z => (1 - z ^ 3) ^ (5 / 6 : Z))
    ((5 / 6 : Z) * (1 - x ^ 3) ^ ((5 / 6 : Z) - 1) * -(3 * x ^ 2)) x := by
   simpa using ((hasDerivAt_pow 3 x).const_sub 1).cpow (hasDerivAt_const x (5 / 6 : Z)) hslit
  refine (dw.mul dp).congr_deriv ?_
  have hcp : (1 - x ^ 3) ^ (5 / 6 : Z) = (1 - x ^ 3) ^ ((5 / 6 : Z) - 1) * (1 - x ^ 3) := by
   conv_lhs => rw [show (5 / 6 : Z) = ((5 / 6 : Z) - 1) + 1 by ring]
   rw [cpow_add _ _ hne, cpow_one]
  rw [hcp]
  have hW_ode : (1 - x ^ 3) * (deriv (deriv f₁) x * f₂ x - f₁ x * deriv (deriv f₂) x) =
    (5 / 2 : Z) * x ^ 2 * (deriv f₁ x * f₂ x - f₁ x * deriv f₂ x) := by
   linear_combination f₂ x * o1 - f₁ x * o2
  calc (deriv (deriv f₁) x * f₂ x - f₁ x * deriv (deriv f₂) x) *
          ((1 - x ^ 3) ^ ((5 / 6 : Z) - 1) * (1 - x ^ 3)) +
        (deriv f₁ x * f₂ x - f₁ x * deriv f₂ x) *
          ((5 / 6 : Z) * (1 - x ^ 3) ^ ((5 / 6 : Z) - 1) * -(3 * x ^ 2))
      = (1 - x ^ 3) ^ ((5 / 6 : Z) - 1) *
          ((1 - x ^ 3) * (deriv (deriv f₁) x * f₂ x - f₁ x * deriv (deriv f₂) x) -
            (5 / 2 : Z) * x ^ 2 * (deriv f₁ x * f₂ x - f₁ x * deriv f₂ x)) := by ring
    _ = 0 := by rw [hW_ode, sub_self, mul_zero]
 have hy1_spec : ∀ u ∈ zy, DifferentiableAt Z zn u ∧ DifferentiableAt Z (deriv zn) u ∧
   (1 - u ^ 3) * deriv (deriv zn) u - (5 / 2 : Z) * u ^ 2 * deriv zn u - (5 / 16 : Z) * u * zn u = 0 :=
  fun u hu => let hc := zK hu;
   ⟨(zQ hc).differentiableAt,(zR hc).differentiableAt,zS hc⟩
 have hy2_spec : ∀ u ∈ zy, DifferentiableAt Z zo u ∧ DifferentiableAt Z (deriv zo) u ∧
   (1 - u ^ 3) * deriv (deriv zo) u - (5 / 2 : Z) * u ^ 2 * deriv zo u - (5 / 16 : Z) * u * zo u = 0 :=
  fun u hu => let hc := zK hu;
   ⟨(zT hc).differentiableAt,(zU hc).differentiableAt,zV hc⟩
 have hw_spec : ∀ u ∈ zy, DifferentiableAt Z w u ∧ DifferentiableAt Z (deriv w) u ∧
   (1 - u ^ 3) * deriv (deriv w) u - (5 / 2 : Z) * u ^ 2 * deriv w u - (5 / 16 : Z) * u * w u = 0 :=
  fun u hu => ⟨hw1 u hu, hw2 u hu, hode u hu⟩
 intro u hu;have h1 := hconst w zo hw_spec hy2_spec u hu;have h2 := hconst zn w hy1_spec hw_spec u hu
 have h1u0 : (1 - zs ^ 3 : Z) = 2 := by rw [zt];ring
 rw [h1u0] at h1 h2;rw [hA] at h1;rw [hB] at h2;have hwron := z1 u (Or.inr hu)
 calc w u = ((1 - u ^ 3) ^ (5 / 6 : Z) * (deriv zn u * zo u - zn u * deriv zo u)) * w u := by
       rw [hwron, one_mul]
   _ = ((deriv w u * zo u - w u * deriv zo u) * (1 - u ^ 3) ^ (5 / 6 : Z)) * zn u +
         ((deriv zn u * w u - zn u * deriv w u) * (1 - u ^ 3) ^ (5 / 6 : Z)) * zo u := by ring
   _ = A * zn u + B * zo u := by rw [h1, h2]
lemma z3 {u : Z} (hu : u ∈ closedBall (0 : Z) 1) : zo u ≠ 0 := by
 have hnorm : ‖u ^ 3‖ ≤ 1 := by
  rw [mem_closedBall, dist_zero_right] at hu;rw [norm_pow];exact pow_le_one₀ (norm_nonneg u) hu
 have hpos := xR (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
  xq xr xg xn xo k4 hnorm
 intro h0;dsimp [zo] at h0;rw [h0, zero_re] at hpos;linarith
lemma z4 {u : Z} (hu : u ∈ zy) (hy2u : zo u ≠ 0) (hy2v : zo (1 / T u) ≠ 0) :
  zp (1 / T u) =
   ((zh : Z) * zs * T (zp u) - 1) /
    (T (zp u) - (zh : Z) * T zs) := by
 let w₁ : Z → Z := fun x => (x * (-x7)) ^ (-1 / 4 : Z) * T (zn (1 / T x));let w₂ : Z → Z := fun x => (x * (-x7)) ^ (-1 / 4 : Z) * T (zo (1 / T x));have hw1_spec := z0
  (fun v hv => (zQ (zK hv)).differentiableAt)
  (fun v hv => (zR (zK hv)).differentiableAt)
  (fun v hv => zS (zK hv))
 have hw2_spec := z0
  (fun v hv => (zT (zK hv)).differentiableAt)
  (fun v hv => (zU (zK hv)).differentiableAt)
  (fun v hv => zV (zK hv))
 have hu₀_cube : zs ^ 3 = -1 := zt;let F1 := xE (5 / 12) (3 / 4) (4 / 3) (-1);let F2 := xE (1 / 12) (5 / 12) (2 / 3) (-1);let F2d := deriv (xE (1 / 12) (5 / 12) (2 / 3)) (-1)
 have hF1v : F1 = (((1 / 2 * Gamma (4 / 3) * Gamma (3 / 8) /
   (Gamma (3 / 4) * Gamma (23 / 24))) : X) : Z) := x1
 have hF2v : F2 = ((((2 : X) ^ (-5 / 6 : X) * Gamma (2 / 3) * Gamma (1 / 8) /
   (Gamma (1 / 4) * Gamma (13 / 24))) : X) : Z) := x2
 have hF2comb : 6 * F2d - (1 / 4 : Z) * F2 =
   (((-(1 / 4) * (2 : X) ^ (-5 / 6 : X) * Gamma (2 / 3) * Gamma (5 / 8) /
    (Gamma (1 / 4) * Gamma (25 / 24))) : X) : Z) := by
  simpa [F2d, F2] using x3
 have hF1_real : T F1 = F1 := by rw [hF1v, conj_ofReal]
 have hF2_real : T F2 = F2 := by rw [hF2v, conj_ofReal]
 have hF2d_real : T F2d = F2d := by
  have hcomb_real : T (6 * F2d - (1 / 4 : Z) * F2) = 6 * F2d - (1 / 4 : Z) * F2 := by rw [hF2comb, conj_ofReal]
  simp only [map_sub,map_mul,map_div₀,map_one,map_ofNat,hF2_real] at hcomb_real
  have : 6 * (T F2d - F2d) = 0 := by linear_combination hcomb_real
  exact sub_eq_zero.1 (mul_eq_zero.1 this |>.resolve_left (by norm_num))
 have hy1_u0 : zn zs = zs * F1 := by simp only [zn,hu₀_cube,F1]
 have hy2_u0 : zo zs = F2 := by simp only [zo,one_div,hu₀_cube,F2]
 have hdy2_u0 : deriv zo zs = 3 * zs ^ 2 * F2d := by
  rw [(zT (zK zF)).deriv]
  have hd := (xT (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
   xg xn k4 (s := zs ^ 3)
   (zK zF)).deriv
  rw [show (1 / 12 + 1 : X) = 13 / 12 by ring, show (5 / 12 + 1 : X) = 17 / 12 by ring,
   show (2 / 3 + 1 : X) = 5 / 3 by ring, hu₀_cube] at hd
  rw [hu₀_cube];exact congr_arg (fun z : Z => 3 * zs ^ 2 * z) hd.symm
 have hy2u0_ne : zo zs ≠ 0 := by
  rw [hy2_u0, hF2v, ofReal_ne_zero];have g23 := gP k4;have g18 := gP k9;have g14 := gP k6;have g1324 := gP xk;have h2p := rpow_pos_of_pos two_pos (-5 / 6);positivity
 have h256 : (2 : Z) ^ (5 / 6 : Z) = (((2 : X) ^ (5 / 6 : X) : X) : Z) := by
  rw [show (2 : Z) = ((2 : X) : Z) by push_cast;rfl,
   show (5 / 6 : Z) = ((5 / 6 : X) : Z) by push_cast;rfl,
   ← ofReal_cpow two_pos.le]
 have hwron0 : deriv zn zs * F2 - zs * F1 * (3 * zs ^ 2 * F2d) = (((2 : X) ^ (-5 / 6 : X) : X) : Z) := by
  have hw := z1 zs (Or.inr zF)
  rw [hu₀_cube, show (1 - (-1 : Z)) = 2 by ring, h256, hy1_u0, hy2_u0, hdy2_u0] at hw
  have h2n : (((2 : X) ^ (5 / 6 : X) : X) : Z) ≠ 0 :=
   ofReal_ne_zero.2 (rpow_pos_of_pos two_pos _).ne'
  have hpow : (((2 : X) ^ (5 / 6 : X) : X) : Z) * (((2 : X) ^ (-5 / 6 : X) : X) : Z) = 1 := by
   rw [← ofReal_mul, ← rpow_add two_pos,
    show (5 / 6 : X) + (-5 / 6) = 0 by ring, rpow_zero];push_cast;ring
  apply mul_left_cancel₀ h2n
  rw [hw, hpow]
 have hdy1_F2 : deriv zn zs * F2 = (((2 : X) ^ (-5 / 6 : X) : X) : Z) - 3 * F1 * F2d := by
  have h1 : zs * F1 * (3 * zs ^ 2 * F2d) = -3 * F1 * F2d := by
   calc zs * F1 * (3 * zs ^ 2 * F2d) = 3 * zs ^ 3 * F1 * F2d := by ring
     _ = -3 * F1 * F2d := by rw [hu₀_cube];ring
  rw [h1] at hwron0;linear_combination hwron0
 have hdy1_real : T (deriv zn zs) = deriv zn zs := by
  have h2 : T (deriv zn zs * F2) = deriv zn zs * F2 := by rw [hdy1_F2];simp only [map_sub,map_mul,map_ofNat,conj_ofReal,hF1_real,hF2d_real]
  rw [map_mul, hF2_real] at h2
  have hF2ne : F2 ≠ 0 := by rw [← hy2_u0];exact hy2u0_ne
  exact mul_right_cancel₀ hF2ne (by linear_combination h2)
 have hgt1 : (zc : Z) * F1 = ((zh - zi : X) : Z) * F2 := by
  have hF2ne : F2 ≠ 0 := by rw [← hy2_u0];exact hy2u0_ne
  have hg := congr_arg (fun r : X => (r : Z)) x5
  dsimp [zc] at hg ⊢
  rw [ofReal_div, ofReal_mul, ← hF1v, ← hF2v] at hg
  have hsub : (1 / Y (1 + Y 3) + Y (1 + Y 3)) -
    Y (3 * (1 + Y 3) / 2) = zh - zi := by
   rw [zj, zk]
  rw [hsub] at hg;rw [div_eq_iff hF2ne] at hg;exact hg
 have hgt2 : (6 * F2d - (1 / 4 : Z) * F2) * F2 =
   -(((zc * (2 : X) ^ (-5 / 6 : X) / zi : X) : Z)) := by
  rw [hF2comb, hF2v, ← ofReal_mul];have hg := congr_arg (fun r : X => (r : Z)) x6;rw [hg];dsimp [zc];rw [← zk];push_cast;ring
 have hF1_comb : F1 * (6 * F2d - (1 / 4 : Z) * F2) =
   -((zh / zi - 1 : X) : Z) * (((2 : X) ^ (-5 / 6 : X) : X) : Z) := by
  have hF2ne : F2 ≠ 0 := by rw [← hy2_u0];exact hy2u0_ne
  have hC1ne : (zc : Z) ≠ 0 := ofReal_ne_zero.2 ze.ne';have hradne : (zi : Z) ≠ 0 := ofReal_ne_zero.2 zl.ne';apply mul_left_cancel₀ (mul_ne_zero hC1ne hF2ne)
  calc (zc : Z) * F2 * (F1 * (6 * F2d - (1 / 4 : Z) * F2))
      = ((zc : Z) * F1) * ((6 * F2d - (1 / 4 : Z) * F2) * F2) := by ring
    _ = (((zh - zi : X) : Z) * F2) * (-(((zc * (2 : X) ^ (-5 / 6 : X) / zi : X) : Z))) := by rw [hgt1, hgt2]
    _ = (zc : Z) * F2 * (-((zh / zi - 1 : X) : Z) * (((2 : X) ^ (-5 / 6 : X) : X) : Z)) := by push_cast;field_simp [hradne]
 have hw_deriv : ∀ (f : Z → Z),
   (∀ v ∈ zy, DifferentiableAt Z f v) →
   let w : Z → Z := fun x => (x * (-x7)) ^ (-1 / 4 : Z) * T (f (1 / T x))
   w zs = T (f zs) ∧
    deriv w zs = -(T (deriv f zs)) / zs ^ 2 -
     (1 / 4 : Z) / zs * T (f zs) := by
  intro f hf w
  have hslit : zs * (-x7) ∈ slitPlane :=
   mem_slitPlane_iff.2 (Or.inl (zJ zF))
  have dα : HasDerivAt (fun x : Z => (x * (-x7)) ^ (-1 / 4 : Z))
    (-(1 / 4 : Z) / zs) zs := by
   have dm : HasDerivAt (fun x : Z => x * (-x7)) (-x7) zs := by simpa using (hasDerivAt_id zs).mul_const (-x7)
   refine (dm.cpow (hasDerivAt_const zs (-1 / 4 : Z)) hslit).congr_deriv ?_
   rw [zv, one_cpow]
   have hdiv : (-x7) = 1 / zs := by rw [eq_div_iff zw];linear_combination zv
   rw [hdiv];ring
  have hfu0 := (hf zs zF).hasDerivAt;rw [← zx] at hfu0;have dΨ := zZ zw hfu0;have dw := dα.mul dΨ;rw [zv, one_cpow, zx] at dw;change HasDerivAt w _ zs at dw
  refine ⟨?_, ?_⟩
  · dsimp [w];rw [zv, one_cpow, one_mul, zx]
  · rw [dw.deriv];ring
 obtain ⟨hw1_val, hw1_der⟩ := hw_deriv zn (fun v hv => (zQ (zK hv)).differentiableAt);obtain ⟨hw2_val, hw2_der⟩ := hw_deriv zo (fun v hv => (zT (zK hv)).differentiableAt);dsimp only at hw1_val hw1_der hw2_val hw2_der
 have hu0_inv : T zs = zs⁻¹ := by rw [zu];exact eq_inv_of_mul_eq_one_left (by rw [mul_comm];exact zv)
 have hpow256_mul : (((2 : X) ^ (-5 / 6 : X) : X) : Z) * (2 : Z) ^ (5 / 6 : Z) = 1 := by
  rw [h256, ← ofReal_mul, ← rpow_add two_pos,
   show (-5 / 6 : X) + 5 / 6 = 0 by ring, rpow_zero];push_cast;ring
 have hrad_ne : (zi : Z) ≠ 0 := ofReal_ne_zero.2 zl.ne';have hC1_ne : (zc : Z) ≠ 0 := ofReal_ne_zero.2 ze.ne'
 have hF2_ne : F2 ≠ 0 := by rw [← hy2_u0];exact hy2u0_ne
 let A₁ : Z := -(zh : Z) / ((zi : Z) * zs ^ 2);let B₁ : Z := 1 / ((zc : Z) * (zi : Z) * zs);let A₂ : Z := -(zc : Z) / ((zi : Z) * zs);let B₂ : Z := (zh : Z) / (zi : Z)
 have hw1_u0 : w₁ zs = zs⁻¹ * F1 := by dsimp [w₁];rw [hw1_val, hy1_u0, map_mul, hF1_real, hu0_inv]
 have hw1_d0 : deriv w₁ zs = -zs⁻¹ * zs⁻¹ * (deriv zn zs + (1 / 4 : Z) * F1) := by dsimp [w₁];rw [hw1_der, hy1_u0, map_mul, hF1_real, hdy1_real, hu0_inv];ring
 have hw2_u0 : w₂ zs = F2 := by dsimp [w₂];rw [hw2_val, hy2_u0, hF2_real]
 have hw2_d0 : deriv w₂ zs = zs⁻¹ * (3 * F2d - (1 / 4 : Z) * F2) := by
  dsimp [w₂];rw [hw2_der, hy2_u0, hdy2_u0, hF2_real];simp only [map_mul,map_pow,map_ofNat,hF2d_real,hu0_inv];field_simp [zw];rw [show zs ^ 3 = -1 from hu₀_cube];ring
 have hA1 : (deriv w₁ zs * zo zs - w₁ zs * deriv zo zs) * (2 : Z) ^ (5 / 6 : Z) = A₁ := by
  rw [hw1_d0, hy2_u0, hw1_u0, hdy2_u0]
  have hcalc : (-zs⁻¹ * zs⁻¹ * (deriv zn zs + (1 / 4 : Z) * F1) * F2 -
    zs⁻¹ * F1 * (3 * zs ^ 2 * F2d)) =
    (zs ^ 2)⁻¹ * (-(((2 : X) ^ (-5 / 6 : X) : X) : Z) + F1 * (6 * F2d - (1 / 4 : Z) * F2)) := by
   have h_num : -(deriv zn zs * F2) - (1 / 4 : Z) * F1 * F2 - 3 * zs ^ 3 * F1 * F2d =
     -(((2 : X) ^ (-5 / 6 : X) : X) : Z) + F1 * (6 * F2d - (1 / 4 : Z) * F2) := by
    rw [hu₀_cube, hdy1_F2];ring
   calc (-zs⁻¹ * zs⁻¹ * (deriv zn zs + (1 / 4 : Z) * F1) * F2 -
         zs⁻¹ * F1 * (3 * zs ^ 2 * F2d))
       = (zs ^ 2)⁻¹ * (-(deriv zn zs * F2) - (1 / 4 : Z) * F1 * F2 - 3 * zs ^ 3 * F1 * F2d) := by field_simp [zw];ring
     _ = (zs ^ 2)⁻¹ * (-(((2 : X) ^ (-5 / 6 : X) : X) : Z) + F1 * (6 * F2d - (1 / 4 : Z) * F2)) := by rw [h_num]
  rw [hcalc, hF1_comb]
  calc (zs ^ 2)⁻¹ * (-(((2 : X) ^ (-5 / 6 : X) : X) : Z) +
          -((zh / zi - 1 : X) : Z) * (((2 : X) ^ (-5 / 6 : X) : X) : Z)) * (2 : Z) ^ (5 / 6 : Z)
      = (zs ^ 2)⁻¹ * (-(zh : Z) / (zi : Z)) *
          ((((2 : X) ^ (-5 / 6 : X) : X) : Z) * (2 : Z) ^ (5 / 6 : Z)) := by push_cast;field_simp [hrad_ne];ring
    _ = A₁ := by rw [hpow256_mul, mul_one];dsimp [A₁];ring
 have hB1 : (deriv zn zs * w₁ zs - zn zs * deriv w₁ zs) * (2 : Z) ^ (5 / 6 : Z) = B₁ := by
  rw [hw1_u0, hy1_u0, hw1_d0]
  have hcalc : (deriv zn zs * (zs⁻¹ * F1) - zs * F1 * (-zs⁻¹ * zs⁻¹ * (deriv zn zs + (1 / 4 : Z) * F1))) *
    F2 = zs⁻¹ * F1 * (2 * (deriv zn zs * F2) + (1 / 4 : Z) * F1 * F2) := by
   field_simp [zw];ring
  rw [hdy1_F2] at hcalc
  have hcomb2 : 2 * ((((2 : X) ^ (-5 / 6 : X) : X) : Z) - 3 * F1 * F2d) + (1 / 4 : Z) * F1 * F2 =
    ((1 + zh / zi : X) : Z) * (((2 : X) ^ (-5 / 6 : X) : X) : Z) := by
   calc 2 * ((((2 : X) ^ (-5 / 6 : X) : X) : Z) - 3 * F1 * F2d) + (1 / 4 : Z) * F1 * F2
       = 2 * (((2 : X) ^ (-5 / 6 : X) : X) : Z) - F1 * (6 * F2d - (1 / 4 : Z) * F2) := by ring
     _ = 2 * (((2 : X) ^ (-5 / 6 : X) : X) : Z) -
           (-((zh / zi - 1 : X) : Z) * (((2 : X) ^ (-5 / 6 : X) : X) : Z)) := by rw [hF1_comb]
     _ = ((1 + zh / zi : X) : Z) * (((2 : X) ^ (-5 / 6 : X) : X) : Z) := by push_cast;ring
  rw [hcomb2] at hcalc
  have hdiff_sq : ((zh - zi : X) : Z) * ((1 + zh / zi : X) : Z) = 1 / (zi : Z) := by
   have hs : (zh : Z) ^ 2 - (zi : Z) ^ 2 = 1 := by exact_mod_cast zm
   push_cast;rw [eq_div_iff hrad_ne];field_simp [hrad_ne];linear_combination hs
  have hF1_eq : F1 = ((zc : Z)⁻¹ * ((zh - zi : X) : Z)) * F2 := by
   apply mul_left_cancel₀ hC1_ne
   calc (zc : Z) * F1 = ((zh - zi : X) : Z) * F2 := hgt1
     _ = (zc : Z) * (((zc : Z)⁻¹ * ((zh - zi : X) : Z)) * F2) := by field_simp [hC1_ne]
  apply mul_right_cancel₀ hF2_ne
  calc (deriv zn zs * (zs⁻¹ * F1) - zs * F1 * (-zs⁻¹ * zs⁻¹ * (deriv zn zs + (1 / 4 : Z) * F1))) *
          (2 : Z) ^ (5 / 6 : Z) * F2
      = ((deriv zn zs * (zs⁻¹ * F1) - zs * F1 * (-zs⁻¹ * zs⁻¹ * (deriv zn zs + (1 / 4 : Z) * F1))) * F2) *
          (2 : Z) ^ (5 / 6 : Z) := by ring
    _ = zs⁻¹ * (((zc : Z)⁻¹ * ((zh - zi : X) : Z)) * F2) *
          (((1 + zh / zi : X) : Z) * (((2 : X) ^ (-5 / 6 : X) : X) : Z)) * (2 : Z) ^ (5 / 6 : Z) := by
        rw [hcalc, hF1_eq]
    _ = zs⁻¹ * (zc : Z)⁻¹ * (((zh - zi : X) : Z) * ((1 + zh / zi : X) : Z)) *
          ((((2 : X) ^ (-5 / 6 : X) : X) : Z) * (2 : Z) ^ (5 / 6 : Z)) * F2 := by ring
    _ = B₁ * F2 := by rw [hdiff_sq, hpow256_mul, mul_one];dsimp [B₁];field_simp [zw, hC1_ne, hrad_ne]
 have hA2 : (deriv w₂ zs * zo zs - w₂ zs * deriv zo zs) * (2 : Z) ^ (5 / 6 : Z) = A₂ := by
  rw [hw2_d0, hy2_u0, hw2_u0, hdy2_u0]
  have hcalc : zs⁻¹ * (3 * F2d - (1 / 4 : Z) * F2) * F2 - F2 * (3 * zs ^ 2 * F2d) =
    zs⁻¹ * ((6 * F2d - (1 / 4 : Z) * F2) * F2) := by
   field_simp [zw];rw [show zs ^ 3 = -1 from hu₀_cube];ring
  rw [hcalc, hgt2];push_cast
  calc zs⁻¹ * -((zc : Z) * (((2 : X) ^ (-5 / 6 : X) : X) : Z) / (zi : Z)) * (2 : Z) ^ (5 / 6 : Z)
      = (-(zc : Z) / ((zi : Z) * zs)) * ((((2 : X) ^ (-5 / 6 : X) : X) : Z) * (2 : Z) ^ (5 / 6 : Z)) := by field_simp [zw, hrad_ne]
    _ = A₂ := by rw [hpow256_mul, mul_one]
 have hB2 : (deriv zn zs * w₂ zs - zn zs * deriv w₂ zs) * (2 : Z) ^ (5 / 6 : Z) = B₂ := by
  rw [hw2_u0, hy1_u0, hw2_d0, hdy1_F2]
  have hcalc : (((2 : X) ^ (-5 / 6 : X) : X) : Z) - 3 * F1 * F2d -
    zs * F1 * (zs⁻¹ * (3 * F2d - (1 / 4 : Z) * F2)) =
    (((2 : X) ^ (-5 / 6 : X) : X) : Z) - F1 * (6 * F2d - (1 / 4 : Z) * F2) := by
   field_simp [zw];ring
  rw [hcalc, hF1_comb]
  calc ((((2 : X) ^ (-5 / 6 : X) : X) : Z) -
          -((zh / zi - 1 : X) : Z) * (((2 : X) ^ (-5 / 6 : X) : X) : Z)) * (2 : Z) ^ (5 / 6 : Z)
      = ((zh : Z) / (zi : Z)) * ((((2 : X) ^ (-5 / 6 : X) : X) : Z) * (2 : Z) ^ (5 / 6 : Z)) := by push_cast;field_simp [hrad_ne];ring
    _ = B₂ := by rw [hpow256_mul, mul_one]
 have hw1_lin := z2 (fun x hx => (hw1_spec x hx).1)
  (fun x hx => (hw1_spec x hx).2.1) (fun x hx => (hw1_spec x hx).2.2) hA1 hB1 u hu
 have hw2_lin := z2 (fun x hx => (hw2_spec x hx).1)
  (fun x hx => (hw2_spec x hx).2.1) (fun x hx => (hw2_spec x hx).2.2) hA2 hB2 u hu
 have hα_ne : (u * (-x7)) ^ (-1 / 4 : Z) ≠ 0 :=
  Complex.cpow_ne_zero_iff.2 (Or.inl (slitPlane_ne_zero
   (mem_slitPlane_iff.2 (Or.inl (zJ hu)))))
 have hα_ne' : (-(u * x7)) ^ (-1 / 4 : Z) ≠ 0 := by simpa [mul_neg] using hα_ne
 have hy2v_conj : T (zo (1 / T u)) ≠ 0 :=
  fun h => hy2v (by simpa using congr_arg (T) h)
 have hstar_ratio : T (zp (1 / T u)) = (zc : Z) * w₁ u / w₂ u := by
  have hw2_ne : w₂ u ≠ 0 := by dsimp [w₂];exact mul_ne_zero hα_ne hy2v_conj
  dsimp [zp, w₁, w₂];simp only [map_div₀,map_mul,conj_ofReal];field_simp [hw2_ne, hα_ne, hα_ne', hy2v_conj]
  rw [mul_div_cancel_right₀ _ (by simpa using hα_ne')]
 have hstar_rhs : T (zp (1 / T u)) =
   ((zh : Z) * T zs * zp u - 1) / (zp u - (zh : Z) * zs) := by
  rw [hstar_ratio];dsimp [w₁, w₂];rw [hw1_lin, hw2_lin]
  have hw2_ne : A₂ * zn u + B₂ * zo u ≠ 0 := by rw [← hw2_lin];exact mul_ne_zero hα_ne hy2v_conj
  have hw2_ne' : -(zc : Z) / ((zi : Z) * zs) * zn u + (zh : Z) / (zi : Z) * zo u ≠ 0 := by simpa [A₂, B₂] using hw2_ne
  have hden_ne : zp u - (zh : Z) * zs ≠ 0 := by
   intro h0
   have hzq : (zc : Z) * zn u = (zh : Z) * zs * zo u := by dsimp [zp] at h0;rw [sub_eq_zero, div_eq_iff hy2u] at h0;exact h0
   apply hw2_ne
   dsimp [A₂, B₂]
   rw [show A₂ * zn u + B₂ * zo u = -((zc : Z) * zn u) / ((zi : Z) * zs) +
     (zh : Z) / (zi : Z) * zo u by ring, hzq]
   field_simp [hrad_ne, zw];ring
  have hden2 : -(zc : Z) * zn u + (zh : Z) * zs * zo u ≠ 0 := by intro h;apply hden_ne;dsimp [zp];rw [sub_eq_zero, div_eq_iff hy2u];linear_combination -h
  dsimp [zp, A₁, B₁, A₂, B₂];rw [hu0_inv];field_simp [hw2_ne', hy2u, hden_ne, hden2, hrad_ne, hC1_ne, zw];rw [← neg_div_neg_eq];congr 1 <;> ring
 have hres := congr_arg (T) hstar_rhs;simp only [starRingEnd_self_apply,map_div₀,map_sub,map_mul,map_one,conj_ofReal] at hres;exact hres
lemma z5 :
  ∀ u ∈ ball (0 : Z) 1 ∪ zy,
   HasDerivAt zq ((1 - u ^ 3) ^ (-2 / 3 : Z)) u := by
 have hconst_ode : ∀ u, u ^ 3 ∈ xN →
   HasDerivAt (fun x : Z => (1 - x ^ 3) ^ (2 / 3 : Z) * deriv zq x) 0 u := by
  intro u hu;have hslit : 1 - u ^ 3 ∈ slitPlane := zM hu;have hne : 1 - u ^ 3 ≠ 0 := slitPlane_ne_zero hslit;have dp : HasDerivAt (fun x : Z => (1 - x ^ 3) ^ (2 / 3 : Z))
    ((2 / 3 : Z) * (1 - u ^ 3) ^ ((2 / 3 : Z) - 1) * -(3 * u ^ 2)) u := by
   simpa using ((hasDerivAt_pow 3 u).const_sub 1).cpow (hasDerivAt_const u (2 / 3 : Z)) hslit
  have dg' := (zX hu).congr_deriv (zX hu).deriv.symm
  refine (dp.mul dg').congr_deriv ?_
  have hcp : (1 - u ^ 3) ^ (2 / 3 : Z) = (1 - u ^ 3) ^ ((2 / 3 : Z) - 1) * (1 - u ^ 3) := by
   conv_lhs => rw [show (2 / 3 : Z) = ((2 / 3 : Z) - 1) + 1 by ring]
   rw [cpow_add _ _ hne, cpow_one]
  rw [hcp];have hode := zY hu
  calc (2 / 3 : Z) * (1 - u ^ 3) ^ ((2 / 3 : Z) - 1) * -(3 * u ^ 2) * deriv zq u +
        (1 - u ^ 3) ^ ((2 / 3 : Z) - 1) * (1 - u ^ 3) * deriv (deriv zq) u
      = (1 - u ^ 3) ^ ((2 / 3 : Z) - 1) *
          ((1 - u ^ 3) * deriv (deriv zq) u - 2 * u ^ 2 * deriv zq u) := by ring
    _ = 0 := by rw [hode, mul_zero]
 have heq_one : ∀ u ∈ ball (0 : Z) 1 ∪ zy, (1 - u ^ 3) ^ (2 / 3 : Z) * deriv zq u = 1 := by
  have hball : ∀ u ∈ ball (0 : Z) 1, (1 - u ^ 3) ^ (2 / 3 : Z) * deriv zq u = 1 := by
   intro u hu
   rw [zD (fun x hx => hconst_ode x (zL hx))
    hu (mem_ball_self one_pos)]
   have h0 := zL (mem_ball_self one_pos);rw [(zW h0).deriv]
   simp only [zero_pow (Nat.succ_ne_zero 2), mul_zero, zero_mul, add_zero,
    sub_zero, one_cpow, one_mul]
   exact xL (a := 1 / 3) (b := 2 / 3) (c := 4 / 3)
    k4 xx k5
  intro u hu
  rcases hu with hu | hu
  · exact hball u hu
  ·
   rw [zC (fun x hx => hconst_ode x (zK hx))
    hu zG.2]
   exact hball ((1 / 2 : Z) * zs) zG.1
 intro u hu
 have hslit_one : u ^ 3 ∈ xN := by
  rcases hu with hu | hu
  · exact zL hu
  · exact zK hu
 have hne : 1 - u ^ 3 ≠ 0 := slitPlane_ne_zero (zM hslit_one)
 have hval : deriv zq u = (1 - u ^ 3) ^ (-2 / 3 : Z) := by
  have heq := heq_one u hu
  have hcp : (1 - u ^ 3) ^ (2 / 3 : Z) * (1 - u ^ 3) ^ (-2 / 3 : Z) = 1 := by rw [← cpow_add _ _ hne, show (2 / 3 : Z) + (-2 / 3 : Z) = 0 by ring, cpow_zero]
  have hnz : (1 - u ^ 3) ^ (2 / 3 : Z) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hne);apply mul_left_cancel₀ hnz
  rw [heq, hcp]
 exact (zW hslit_one).congr_deriv (by rw [← hval, (zW hslit_one).deriv])
lemma z6 :
  zq 1 = ((Gamma (4 / 3) * Gamma (1 / 3) / Gamma (2 / 3) : X) : Z) := by
 dsimp [zq];rw [one_pow, one_mul]
 convert xM (a := 1 / 3) (b := 2 / 3) (c := 4 / 3)
  k4 xx xy (by norm_num) using 2;norm_num
lemma z7 : zr 1 = (zd : Z) := by
 dsimp [zr, zc, zd];rw [z6, ← ofReal_mul];congr 1;have g43 : Gamma (4 / 3) ≠ 0 := xB k5;have g23 : Gamma (2 / 3) ≠ 0 := xB k4;have g14 : Gamma (1 / 4) ≠ 0 := xB k6
 have hsr : Y (1 + Y 3) ≠ 0 := by positivity
 field_simp [g43, g23, g14, hsr]
lemma z8 : zq zs = (1 / 2 : Z) * zq 1 * zs := by
 have hcont_pos : ContinuousOn (fun t : X => (1 + t ^ 3) ^ (-2 / 3 : X)) (Icc 0 1) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt
   (ContinuousAt.rpow (continuous_const.add (continuous_pow 3)).continuousAt continuousAt_const (Or.inl ?_))
  have : 0 ≤ t := ht.1;positivity
 have hint_pos : IntervalIntegrable (fun t : X => (1 + t ^ 3) ^ (-2 / 3 : X)) volume 0 1 :=
  hcont_pos.intervalIntegrable_of_Icc zero_le_one
 have hpath : zq zs = zs * ((∫ t in (0 : X)..1, (1 + t ^ 3) ^ (-2 / 3 : X) : X) : Z) := by
  have hd : ∀ t ∈ uIcc (0 : X) 1,
    HasDerivAt (fun s : X => zq ((s : Z) * zs)) (zs * (((1 + t ^ 3) ^ (-2 / 3 : X) : X) : Z)) t := by
   intro t ht;rw [uIcc_of_le zero_le_one] at ht
   have hmem : (t : Z) * zs ∈ ball (0 : Z) 1 ∪ zy := by
    by_cases ht1 : t < 1
    ·
     left;rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1, zE, mul_one];exact ht1
    ·
     right
     have ht_pos : 0 < t := by linarith [not_lt.1 ht1]
     constructor
     ·
      rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero];exact mul_pos ht_pos zF.1
     ·
      rw [mul_assoc, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero];exact mul_pos ht_pos zF.2
   have dg := z5 ((t : Z) * zs) hmem
   have dlin : HasDerivAt (fun s : X => (s : Z) * zs) zs t := by simpa using (hasDerivAt_id t).ofReal_comp.mul_const zs
   refine (dg.comp t dlin).congr_deriv ?_
   have h13 : 1 - ((t : Z) * zs) ^ 3 = ((1 + t ^ 3 : X) : Z) := by rw [mul_pow, zt];push_cast;ring
   have ht13 : 0 ≤ 1 + t ^ 3 := by have ht0 := ht.1;positivity
   rw [h13, show (-2 / 3 : Z) = ((-2 / 3 : X) : Z) by push_cast;rfl,
    ← ofReal_cpow ht13, mul_comm]
  have hintC : IntervalIntegrable (fun t : X => zs * (((1 + t ^ 3) ^ (-2 / 3 : X) : X) : Z)) volume 0 1 :=
   ((continuous_ofReal.comp_continuousOn hcont_pos).const_mul zs).intervalIntegrable_of_Icc zero_le_one
  have hftc := integral_eq_sub_of_hasDerivAt hd hintC
  have hg0 : zq ((0 : Z) * zs) = 0 := by simp only [zq,zero_mul,one_div,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
  simp only [ofReal_zero,ofReal_one,one_mul,hg0,sub_zero] at hftc;rw [← hftc, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
 have hbeta_eq : ∫ t in (0 : X)..1, (1 + t ^ 3) ^ (-2 / 3 : X) =
   1 / 2 * (Gamma (4 / 3) * Gamma (1 / 3) / Gamma (2 / 3)) := by
  have hsub1 : ∫ t in (0 : X)..1, (1 + t ^ 3) ^ (-2 / 3 : X) =
    (1 / 3) * ∫ x in Ioo (0 : X) (1 / 2), x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X) := by
   let φ : X → X := fun t => t ^ 3 / (1 + t ^ 3);have hs : MeasurableSet (Ioo (0 : X) 1) := measurableSet_Ioo
   have hinj : InjOn φ (Ioo (0 : X) 1) := by
    intro x hx y hy hxy
    have hx1 : 0 < 1 + x ^ 3 := by positivity [hx.1]
    have hy1 : 0 < 1 + y ^ 3 := by positivity [hy.1]
    have h1 : x ^ 3 * (1 + y ^ 3) = y ^ 3 * (1 + x ^ 3) := by dsimp [φ] at hxy;rw [div_eq_div_iff hx1.ne' hy1.ne'] at hxy;exact hxy
    have h2 : x ^ 3 = y ^ 3 := by linarith
    have hfac : (x - y) * (x ^ 2 + x * y + y ^ 2) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp hfac with h0 | h0
    · linarith
    · exfalso;nlinarith only [h0, hx.1, hy.1]
   have himg : φ '' Ioo (0 : X) 1 = Ioo 0 (1 / 2) := by
    ext x;constructor
    ·
     rintro ⟨t, ht, rfl⟩;have ht0 := ht.1;have ht1 := ht.2
     have hden : 0 < 1 + t ^ 3 := by positivity
     refine ⟨div_pos (pow_pos ht0 3) hden, ?_⟩
     rw [div_lt_div_iff₀ hden two_pos];have ht3 : t ^ 3 < 1 := pow_lt_one₀ ht0.le ht1 (Nat.succ_ne_zero 2);linarith
    ·
     intro hx;have hx0 := hx.1
     have hx1 : 0 < 1 - x := by linarith [hx.2]
     let t := (x / (1 - x)) ^ (1 / 3 : X)
     refine ⟨t, ⟨rpow_pos_of_pos (div_pos hx0 hx1) _, ?_⟩, ?_⟩
     ·
      rw [Real.rpow_lt_one_iff' (div_nonneg hx0.le hx1.le) k3];rw [div_lt_one hx1];linarith [hx.2]
     ·
      have ht3 : t ^ 3 = x / (1 - x) := by
       dsimp [t];rw [← rpow_natCast, ← rpow_mul (div_pos hx0 hx1).le];norm_num
      have h1p : 1 + x / (1 - x) = 1 / (1 - x) := by field_simp [hx1.ne'];ring
      dsimp [φ];rw [ht3, h1p, div_div_div_cancel_right₀ hx1.ne', div_one]
   have hderiv : ∀ t ∈ Ioo (0 : X) 1,
     HasDerivWithinAt φ (3 * t ^ 2 / (1 + t ^ 3) ^ 2) (Ioo 0 1) t := by
    intro t ht
    have d1 : HasDerivAt (fun s : X => s ^ 3) (3 * t ^ 2) t := by simpa using hasDerivAt_pow 3 t
    have d2 : HasDerivAt (fun s : X => 1 + s ^ 3) (3 * t ^ 2) t := d1.const_add 1
    have hden : 1 + t ^ 3 ≠ 0 := (by positivity [ht.1] : 0 < 1 + t ^ 3).ne'
    have hd := d1.div d2 hden
    have hd' : HasDerivAt φ (3 * t ^ 2 / (1 + t ^ 3) ^ 2) t :=
     hd.congr_deriv (by ring)
    exact hd'.hasDerivWithinAt
   have hch := integral_image_eq_integral_abs_deriv_smul hs hderiv hinj
    (fun x : X => x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X))
   rw [himg] at hch
   rw [integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, hch,
    ← MeasureTheory.integral_const_mul]
   refine setIntegral_congr_fun hs fun t ht => ?_
   have ht0 := ht.1
   have hden : 0 < 1 + t ^ 3 := by positivity
   have habs : |3 * t ^ 2 / (1 + t ^ 3) ^ 2| = 3 * t ^ 2 / (1 + t ^ 3) ^ 2 :=
    abs_of_pos (by positivity)
   rw [habs, smul_eq_mul]
   have h1φ : 1 - φ t = 1 / (1 + t ^ 3) := by dsimp [φ];field_simp [hden.ne'];ring
   rw [h1φ];dsimp [φ]
   have ht3r : (t ^ 3) ^ (-2 / 3 : X) = t ^ (-2 : X) := by rw [← rpow_natCast t 3, ← rpow_mul ht0.le];norm_num
   rw [div_rpow (pow_nonneg ht0.le 3) hden.le,
    show (1 / (1 + t ^ 3)) = (1 + t ^ 3)⁻¹ by rw [one_div], Real.inv_rpow hden.le,
    show ((1 + t ^ 3) ^ (-2 / 3 : X))⁻¹ = (1 + t ^ 3) ^ (2 / 3 : X) by
     rw [← rpow_neg hden.le];norm_num, ht3r]
   have hpow2 : t ^ (-2 : X) * t ^ 2 = 1 := by
    rw [← rpow_natCast t 2, ← rpow_add ht0, show (-2 : X) + (2 : ℕ) = 0 by ring,
     rpow_zero]
   have hpowd : (1 + t ^ 3) ^ (-2 / 3 : X) * (1 + t ^ 3) ^ (2 : X) = (1 + t ^ 3) ^ (4 / 3 : X) := by rw [← rpow_add hden];congr 1;ring
   have hd4_ne : (1 + t ^ 3) ^ (4 / 3 : X) ≠ 0 := (rpow_pos_of_pos hden _).ne';have hdm23_ne : (1 + t ^ 3) ^ (-2 / 3 : X) ≠ 0 := (rpow_pos_of_pos hden _).ne'
   calc (1 + t ^ 3) ^ (-2 / 3 : X)
       = (t ^ (-2 : X) * t ^ 2) * ((1 + t ^ 3) ^ (2 / 3 : X) / (1 + t ^ 3) ^ (4 / 3 : X)) := by
           rw [hpow2, one_mul, eq_div_iff hd4_ne, ← rpow_add hden]
           congr 1;ring
     _ = (t ^ (-2 : X) * t ^ 2) * ((1 + t ^ 3) ^ (2 / 3 : X) / ((1 + t ^ 3) ^ (-2 / 3 : X) * (1 + t ^ 3) ^ (2 : X))) := by rw [hpowd]
     _ = (1 / 3 : X) * ((3 * t ^ 2 / (1 + t ^ 3) ^ 2) *
           ((t ^ (-2 : X) / (1 + t ^ 3) ^ (-2 / 3 : X)) * (1 + t ^ 3) ^ (2 / 3 : X))) := by
           rw [rpow_two];field_simp [hdm23_ne, hden.ne']
  have hsymm : ∫ x in Ioo (1 / 2 : X) 1, x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X) =
    ∫ x in Ioo (0 : X) (1 / 2), x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X) := by
   let ψ : X → X := fun x => 1 - x;have hs : MeasurableSet (Ioo (0 : X) (1 / 2)) := measurableSet_Ioo
   have hinj : InjOn ψ (Ioo (0 : X) (1 / 2)) := fun x _ y _ h => by dsimp [ψ] at h;linarith
   have himg : ψ '' Ioo (0 : X) (1 / 2) = Ioo (1 / 2) 1 := by
    ext x;constructor
    · rintro ⟨y, hy, rfl⟩;exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    · intro hx;exact ⟨1 - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, by dsimp [ψ];ring⟩
   have hderiv : ∀ x ∈ Ioo (0 : X) (1 / 2), HasDerivWithinAt ψ (-1) (Ioo 0 (1 / 2)) x := by intro x _;simpa using ((hasDerivAt_id x).const_sub (1 : X)).hasDerivWithinAt
   have hch := integral_image_eq_integral_abs_deriv_smul hs hderiv hinj
    (fun x : X => x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X))
   rw [himg] at hch;rw [hch]
   refine setIntegral_congr_fun hs fun x _ => ?_
   simp only [abs_neg,abs_one,sub_sub_cancel,mul_comm,smul_eq_mul,one_mul,ψ]
  have hbetaC := Complex.betaIntegral_convergent (u := (1 / 3 : Z)) (v := (1 / 3 : Z)) (by simp only [Complex.div_ofNat_re,one_re];exact k3) (by simp only [Complex.div_ofNat_re,one_re];exact k3)
  have hreal_int : IntervalIntegrable (fun x : X => x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X)) volume 0 1 := by
   have hC_eq : (fun x : X => ((x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X) : X) : Z)) =ᵐ[volume.restrict (Ioc 0 1)]
     (fun x : X => (x : Z) ^ ((1 / 3 : Z) - 1) * (1 - (x : Z)) ^ ((1 / 3 : Z) - 1)) := by
    have hne1 : ∀ᵐ x : X ∂volume, x ≠ 1 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne1] with x hx _
    have hx0 := hx.1.le
    have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
    rw [show (1 / 3 : Z) - 1 = ((-2 / 3 : X) : Z) by push_cast;ring,
     show (1 : Z) - (x : Z) = ((1 - x : X) : Z) by push_cast;rfl,
     ← ofReal_cpow hx0, ← ofReal_cpow hx1, ofReal_mul]
   have hint1 := (reCLM.integrable_comp hbetaC.1);rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
   refine Integrable.congr hint1 ?_
   filter_upwards [hC_eq] with x hx
   have := congr_arg Complex.re hx;simpa using this.symm
  have hsplit : ∫ x in (0 : X)..1, x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X) =
    2 * ∫ x in Ioo (0 : X) (1 / 2), x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X) := by
   have hi1 : IntervalIntegrable (fun x : X => x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X)) volume 0 (1 / 2) :=
    hreal_int.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le k2.le];exact Icc_subset_Icc_right (half_le_self zero_le_one))
   have hi2 : IntervalIntegrable (fun x : X => x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X)) volume (1 / 2) 1 :=
    hreal_int.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le (half_le_self zero_le_one)];exact Icc_subset_Icc_left k2.le)
   rw [← integral_add_adjacent_intervals hi1 hi2,
    integral_of_le k2.le,
    integral_of_le (half_le_self zero_le_one),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, hsymm, two_mul]
  have hbeta_val : ∫ x in (0 : X)..1, x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X) =
    Gamma (1 / 3) * Gamma (1 / 3) / Gamma (2 / 3) := by
   have hC_int : (∫ x in (0 : X)..1, ((x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X) : X) : Z)) =
     betaIntegral (1 / 3 : Z) (1 / 3 : Z) := by
    dsimp [betaIntegral]
    refine intervalIntegral.integral_congr_ae ?_
    have hne0 : ∀ᵐ x : X ∂volume, x ≠ 0 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
    have hne1 : ∀ᵐ x : X ∂volume, x ≠ 1 := by rw [ae_iff];simp only [ne_eq,Decidable.not_not,ofPred_eq_eq_singleton,measure_singleton]
    filter_upwards [hne0, hne1] with x _ _ hx
    rw [uIoc_of_le zero_le_one] at hx
    rw [show (1 / 3 : Z) - 1 = ((-2 / 3 : X) : Z) by push_cast;ring,
     show (1 : Z) - (x : Z) = ((1 - x : X) : Z) by push_cast;rfl,
     ← ofReal_cpow hx.1.le, ← ofReal_cpow (by linarith [hx.2] : 0 ≤ 1 - x),
     ofReal_mul]
   rw [intervalIntegral.integral_ofReal] at hC_int;have hbv := x0 (a := 1 / 3) (b := 1 / 3) k3 k3
   rw [show (1 / 3 + 1 / 3 : X) = 2 / 3 by ring] at hbv
   rw [show (1 / 3 : Z) = ((1 / 3 : X) : Z) by push_cast;rfl] at hC_int
   exact_mod_cast (congr_arg Complex.re (hC_int.trans hbv))
  have hG43 : Gamma (4 / 3) = (1 / 3) * Gamma (1 / 3) := by rw [show (4 / 3 : X) = 1 / 3 + 1 by ring, Real.Gamma_add_one (by positivity)]
  have hhalf : ∫ x in Ioo (0 : X) (1 / 2), x ^ (-2 / 3 : X) * (1 - x) ^ (-2 / 3 : X) =
    1 / 2 * (Gamma (1 / 3) * Gamma (1 / 3) / Gamma (2 / 3)) := by
   linarith [hsplit, hbeta_val]
  rw [hsub1, hhalf, hG43];ring
 rw [hpath, hbeta_eq, z6];push_cast;ring
lemma z9 {u : Z} (hu : u ∈ zy) :
  zr (1 / T u) = -(zd : Z) * x7 ^ 2 - x7 * T (zr u) := by
 let H : Z → Z := fun x => zq x + x7 * T (zq (1 / T x))
 have hH_const : H u = H zs := by
  refine zC (fun x hx => ?_) hu zF
  have hx0 : x ≠ 0 := zz hx;have dg_x := z5 x (Or.inr hx);have dg_v := z5 (1 / T x) (Or.inr (zI hx));have dstar := (zZ hx0 dg_v).const_mul x7
  refine (dg_x.add dstar).congr_deriv ?_
  have hslit_v : 1 - (1 / T x) ^ 3 ∈ slitPlane :=
   zM (zK (zI hx))
  have hslit_x : 1 - x ^ 3 ∈ slitPlane :=
   zM (zK hx)
  have hconj : T ((1 - (1 / T x) ^ 3) ^ (-2 / 3 : Z)) =
    (1 - 1 / x ^ 3) ^ (-2 / 3 : Z) := by
   rw [show (-2 / 3 : Z) = ((-2 / 3 : X) : Z) by push_cast;rfl,
    zN hslit_v]
   simp only [map_sub,map_one,map_pow,map_div₀,starRingEnd_self_apply];rw [one_div_pow]
  have hratio_eq : (1 - 1 / x ^ 3) ^ (-2 / 3 : Z) =
    (1 - x ^ 3) ^ (-2 / 3 : Z) * (x * (-x7)) ^ 2 := by
   let ratio : Z → Z := fun z =>
    (1 - 1 / z ^ 3) ^ (-2 / 3 : Z) / ((1 - z ^ 3) ^ (-2 / 3 : Z) * (z * (-x7)) ^ 2)
   have hrcube : ∀ z ∈ zy, ratio z ^ 3 = 1 := by
    intro z hz;have hz0 : z ≠ 0 := zz hz
    have hs1 : 1 - 1 / z ^ 3 ≠ 0 := by
     have := slitPlane_ne_zero (zM (zK (zI hz)));intro h0;apply this;have h0' := congr_arg (T) h0;simp only [map_sub,map_one,map_div₀,map_pow,map_zero] at h0';simpa using h0'
    have hs2 : 1 - z ^ 3 ≠ 0 := slitPlane_ne_zero (zM (zK hz))
    have hcp1 : ((1 - 1 / z ^ 3) ^ (-2 / 3 : Z)) ^ 3 = (1 - 1 / z ^ 3) ^ (-2 : Z) := by rw [← Complex.cpow_nat_mul];congr 1;ring
    have hcp2 : ((1 - z ^ 3) ^ (-2 / 3 : Z)) ^ 3 = (1 - z ^ 3) ^ (-2 : Z) := by rw [← Complex.cpow_nat_mul];congr 1;ring
    dsimp [ratio];rw [div_pow, mul_pow, hcp1, hcp2]
    have hnegw3 : (-x7) ^ 3 = -1 := by calc (-x7) ^ 3 = -(x7 ^ 3) := by ring
      _ = -1 := by rw [x9]
    have hz6 : ((z * (-x7)) ^ 2) ^ 3 = z ^ 6 := by
     calc ((z * (-x7)) ^ 2) ^ 3 = z ^ 6 * ((-x7) ^ 3) ^ 2 := by ring
       _ = z ^ 6 := by rw [hnegw3];ring
    have h13 : 1 - 1 / z ^ 3 = -(1 - z ^ 3) / z ^ 3 := by field_simp [pow_ne_zero 3 hz0];ring
    have hmul : (1 - 1 / z ^ 3) ^ (-2 : Z) = z ^ 6 / (1 - z ^ 3) ^ 2 := by
     rw [cpow_neg, Complex.cpow_two, h13, div_pow, neg_sq];field_simp [pow_ne_zero 3 hz0, hs2]
    rw [hmul, cpow_neg, Complex.cpow_two, hz6];field_simp [pow_ne_zero 3 hz0, hs2]
   have hrc1 : ratio x = ratio zs := by
    refine zC (fun z hz => ?_) hx zF
    have hz0 : z ≠ 0 := zz hz
    have hsz1 : 1 - 1 / z ^ 3 ∈ slitPlane := by
     have hs := zM (zK (zI hz))
     have hbar : 1 - 1 / z ^ 3 = T (1 - (1 / T z) ^ 3) := by simp only [one_div,inv_pow,map_sub,map_one,map_inv₀,map_pow,RingHomCompTriple.comp_apply,RingHom.id_apply]
     rw [hbar, mem_slitPlane_iff]
     rcases mem_slitPlane_iff.1 hs with hr | hi
     · exact Or.inl (by rw [conj_re];exact hr)
     · exact Or.inr (by rw [conj_im];exact neg_ne_zero.2 hi)
    have hsz2 : 1 - z ^ 3 ∈ slitPlane := zM (zK hz)
    have hd1 : DifferentiableAt Z (fun w : Z => (1 - 1 / w ^ 3) ^ (-2 / 3 : Z)) z := by
     have di : HasDerivAt (fun w : Z => 1 - 1 / w ^ 3) (3 / z ^ 4) z := by
      have d1_div : HasDerivAt (fun w : Z => 1 / w ^ 3) (-(3 * z ^ 2) / (z ^ 3) ^ 2) z := by
       have d0 := (hasDerivAt_pow 3 z).inv (pow_ne_zero 3 hz0)
       refine (d0.congr_of_eventuallyEq (Eventually.of_forall fun w : Z => one_div (w ^ 3))).congr_deriv ?_
       ring
      refine d1_div.const_sub 1 |>.congr_deriv ?_
      field_simp [hz0]
     exact (di.cpow (hasDerivAt_const z (-2 / 3 : Z)) hsz1).differentiableAt
    have hd2 : DifferentiableAt Z (fun w : Z => (1 - w ^ 3) ^ (-2 / 3 : Z) * (w * (-x7)) ^ 2) z := by
     have dcp := (((hasDerivAt_pow 3 z).const_sub 1).cpow (hasDerivAt_const z (-2 / 3 : Z)) hsz2).differentiableAt;exact dcp.mul (((hasDerivAt_id z).mul_const (-x7)).pow 2).differentiableAt
    have hden0 : (1 - z ^ 3) ^ (-2 / 3 : Z) * (z * (-x7)) ^ 2 ≠ 0 := by
     have h1 : (1 - z ^ 3) ^ (-2 / 3 : Z) ≠ 0 :=
      Complex.cpow_ne_zero_iff.2 (Or.inl (slitPlane_ne_zero hsz2))
     have h2 : (-x7) ≠ 0 := by intro h;have := zv;rw [h, mul_zero] at this;norm_num at this
     exact mul_ne_zero h1 (pow_ne_zero 2 (mul_ne_zero hz0 h2))
    have hr_diff : DifferentiableAt Z ratio z := hd1.div hd2 hden0
    have hcube_d : ∀ᶠ w in 𝓝 z, ratio w ^ 3 = 1 := by
     filter_upwards [zA.mem_nhds hz] with w hw
     exact hrcube w hw
    have hd0 : HasDerivAt (fun w => ratio w ^ 3) 0 z :=
     (hasDerivAt_const z (1 : Z)).congr_of_eventuallyEq hcube_d
    have hd_lhs : HasDerivAt (fun w => ratio w ^ 3) (3 * ratio z ^ 2 * deriv ratio z) z :=
     (hasDerivAt_pow 3 (ratio z)).comp z hr_diff.hasDerivAt
    have heq0 : 3 * ratio z ^ 2 * deriv ratio z = 0 := hd_lhs.unique hd0
    have hrz0 : ratio z ≠ 0 := by intro h0;have := hrcube z hz;rw [h0, zero_pow (by norm_num)] at this;norm_num at this
    have hdr : deriv ratio z = 0 := by
     rcases mul_eq_zero.mp heq0 with h | h
     ·
      exfalso;rcases mul_eq_zero.mp h with h3 | h2
      · norm_num at h3
      · exact hrz0 (sq_eq_zero_iff.1 h2)
     · exact h
    rw [← hdr];exact hr_diff.hasDerivAt
   have hru0 : ratio zs = 1 := by
    dsimp [ratio]
    rw [zt, zv, one_pow, mul_one, show (1 : Z) / (-1 : Z) = -1 by norm_num,
     show (1 : Z) - (-1 : Z) = 2 by norm_num,
     div_self (Complex.cpow_ne_zero_iff.2 (Or.inl (by norm_num)))]
   rw [hru0] at hrc1
   have hden0 : (1 - x ^ 3) ^ (-2 / 3 : Z) * (x * (-x7)) ^ 2 ≠ 0 := by
    have h1 : (1 - x ^ 3) ^ (-2 / 3 : Z) ≠ 0 :=
     Complex.cpow_ne_zero_iff.2 (Or.inl (slitPlane_ne_zero hslit_x))
    have h2 : (-x7) ≠ 0 := by intro h;have := zv;rw [h, mul_zero] at this;norm_num at this
    exact mul_ne_zero h1 (pow_ne_zero 2 (mul_ne_zero hx0 h2))
   exact (div_eq_one_iff_eq hden0).1 hrc1
  rw [hconj, hratio_eq]
  have hmul : x7 * (-(x * (-x7)) ^ 2 / x ^ 2) = -1 := by
   calc x7 * (-(x * (-x7)) ^ 2 / x ^ 2) = -(x7 ^ 3) * (x ^ 2 / x ^ 2) := by ring
     _ = -1 * 1 := by rw [x9, div_self (pow_ne_zero 2 hx0)]
     _ = -1 := by ring
  rw [show x7 * (-((1 - x ^ 3) ^ (-2 / 3 : Z) * (x * (-x7)) ^ 2) / x ^ 2) =
    (1 - x ^ 3) ^ (-2 / 3 : Z) * (x7 * (-(x * (-x7)) ^ 2 / x ^ 2)) by ring, hmul]
  ring
 have hHu0 : H zs = -zq 1 * x7 ^ 2 := by
  dsimp [H];rw [zx, z8, map_mul, map_mul, zu]
  have hg1_real : T (zq 1) = zq 1 := by rw [z6, conj_ofReal]
  rw [show T (1 / 2 : Z) = 1 / 2 by simp only [map_div₀,map_one,map_ofNat], hg1_real]
  dsimp [zs];ring
 rw [hHu0] at hH_const;have hstar := congr_arg (T) hH_const;simp only [H,map_add,map_mul,map_neg,map_pow,za,starRingEnd_self_apply] at hstar
 have hg1_real : T (zq 1) = zq 1 := by rw [z6, conj_ofReal]
 rw [hg1_real] at hstar;have hω3 : x7 ^ 3 = 1 := x9
 rw [show ((x7 ^ 2) ^ 2 : Z) = x7 * x7 ^ 3 by ring, hω3, mul_one] at hstar
 have hg₀_eq : zq (1 / T u) = -zq 1 * x7 ^ 2 - x7 * T (zq u) := by
  have hmul := congr_arg (fun z => x7 * z) hstar;linear_combination hmul - zq (1 / T u) * hω3
 have hcAG_eq : (zc : Z) * zq 1 = (zd : Z) := by simpa [zr] using z7
 dsimp [zr];rw [hg₀_eq, map_mul, conj_ofReal];linear_combination -(x7 ^ 2) * hcAG_eq
end
end BlochAG
namespace BlochAG
noncomputable section
lemma Qa : x7 = ω := rfl
lemma Qb : zh = tR := rfl
lemma Qc (u : Z) : zo (ω * u) = zo u := by
 dsimp [zo];rw [mul_pow, ← Qa, x9, one_mul]
lemma Qd (u : Z) : zn (ω * u) = ω * zn u := by
 dsimp [zn];rw [mul_pow, ← Qa, x9, one_mul, mul_assoc]
lemma Qe (u : Z) : zp (ω * u) = ω * zp u := by
 dsimp [zp];rw [Qd, Qc];ring
lemma Qf (u : Z) : zq (ω * u) = ω * zq u := by
 dsimp [zq];rw [mul_pow, ← Qa, x9, one_mul, mul_assoc]
lemma Qg (u : Z) : zr (ω * u) = ω * zr u := by
 dsimp [zr];rw [Qf];ring
lemma Qh {p q : X} (hp : 0 < p) (hq : 0 < q) :
  IntegrableOn (fun t : X => t ^ (p - 1) * (1 - t) ^ (q - 1)) (Ioo (0 : X) 1) := by
 have hib := xI (b := p) (c := p + q) hp (by linarith)
 rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hib
 refine (hib.mono_set Ioo_subset_Ioc_self).congr_fun (fun t ht => ?_) measurableSet_Ioo
 have ht0 : 0 < t := ht.1;have ht1 : 0 < 1 - t := sub_pos.2 ht.2
 have h1tc : (1 : Z) - (t : Z) = ((1 - t : X) : Z) := by push_cast;rfl
 have hp1 : (t : Z) ^ ((p : Z) - 1) = ((t ^ (p - 1) : X) : Z) := by rw [show (p : Z) - 1 = ((p - 1 : X) : Z) by push_cast;ring, ← ofReal_cpow ht0.le]
 have hq1 : (1 - (t : Z)) ^ (((p + q : X) : Z) - (p : Z) - 1) = (((1 - t) ^ (q - 1) : X) : Z) := by
  rw [h1tc, show ((p + q : X) : Z) - (p : Z) - 1 = ((q - 1 : X) : Z) by push_cast;ring,
   ← ofReal_cpow ht1.le]
 dsimp only
 rw [hp1, hq1, ← ofReal_mul, Complex.norm_of_nonneg (by positivity)]
lemma Qi {w : Z} (hw : w ≠ 0) (a : X) :
  ‖w ^ (-a : Z)‖ = ‖w‖ ^ (-a) := by
 rw [cpow_def_of_ne_zero hw, Complex.norm_exp, rpow_def_of_pos (norm_pos_iff.2 hw)];simp only [mul_neg,neg_re,mul_re,log_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
lemma Qj {a b c : X}
  (ha : 0 ≤ a) (hb : 0 < b) (hcab : 0 < c - a - b) :
  ContinuousOn (xE a b c) (closedBall (0 : Z) 1) := by
 have hcb : 0 < c - b := by linarith
 unfold xE
 refine continuousOn_const.mul ?_
 have heq : (fun s : Z => ∫ t in (0 : X)..1, xD a b c s t) =
   (fun s : Z => ∫ t in Ioo (0 : X) 1, xD a b c s t) := by
  funext s
  rw [integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
 rw [heq];let bound : X → X := fun t => t ^ (b - 1) * (1 - t) ^ (c - a - b - 1)
 have hbound_int : IntegrableOn bound (Ioo (0 : X) 1) := by simpa [bound, sub_sub] using Qh hb hcab
 refine MeasureTheory.continuousOn_of_dominated
  (F := fun s t => xD a b c s t) (bound := bound) ?_ ?_ hbound_int ?_
 ·
  intro s hs;have hslit := xQ hb hcb hcab (mem_closedBall_zero_iff.1 hs);exact hslit.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
 ·
  intro s hs;have hs1 : ‖s‖ ≤ 1 := mem_closedBall_zero_iff.1 hs
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 < t := ht.1;have ht1 : 0 < 1 - t := sub_pos.2 ht.2;have hw_re : 0 < (1 - s * (t : Z)).re := xG hs1 ht0.le ht.2
  have hw_ne : 1 - s * (t : Z) ≠ 0 := by intro h;rw [h, zero_re] at hw_re;linarith
  have hw_ge : 1 - t ≤ ‖1 - s * (t : Z)‖ := by
   have htri := norm_sub_norm_le (1 : Z) (s * (t : Z))
   have hst : ‖s * (t : Z)‖ ≤ t := by
    rw [norm_mul, Complex.norm_of_nonneg ht0.le];exact mul_le_of_le_one_left ht0.le hs1
   simp only [norm_one] at htri;linarith
  have hcp_norm : ‖(1 - s * (t : Z)) ^ (-a : Z)‖ = ‖1 - s * (t : Z)‖ ^ (-a) :=
   Qi hw_ne a
  have hpow_le : ‖1 - s * (t : Z)‖ ^ (-a) ≤ (1 - t) ^ (-a) := by
   rw [rpow_neg (norm_nonneg _), rpow_neg ht1.le];exact inv_anti₀ (rpow_pos_of_pos ht1 _) (rpow_le_rpow ht1.le hw_ge ha)
  have ht_norm : ‖(t : Z) ^ ((b : Z) - 1)‖ = t ^ (b - 1) := by
   rw [show (b : Z) - 1 = ((b - 1 : X) : Z) by push_cast;ring, ← ofReal_cpow ht0.le,
    Complex.norm_of_nonneg (by positivity)]
  have h1t_norm : ‖(1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1)‖ = (1 - t) ^ (c - b - 1) := by
   have h1tc : (1 : Z) - (t : Z) = ((1 - t : X) : Z) := by push_cast;rfl
   rw [h1tc, show (c : Z) - (b : Z) - 1 = ((c - b - 1 : X) : Z) by push_cast;ring,
    ← ofReal_cpow ht1.le, Complex.norm_of_nonneg (by positivity)]
  dsimp [xD, bound];rw [norm_mul, norm_mul, ht_norm, h1t_norm, hcp_norm]
  calc t ^ (b - 1) * (1 - t) ^ (c - b - 1) * ‖1 - s * (t : Z)‖ ^ (-a)
      ≤ t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - t) ^ (-a) :=
        mul_le_mul_of_nonneg_left hpow_le (mul_nonneg (rpow_nonneg ht0.le _) (rpow_nonneg ht1.le _))
    _ = t ^ (b - 1) * ((1 - t) ^ (c - b - 1) * (1 - t) ^ (-a)) := by ring
    _ = t ^ (b - 1) * (1 - t) ^ (c - a - b - 1) := by rw [← rpow_add ht1];congr 2;ring
 ·
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 < t := ht.1;intro s hs;have hs1 : ‖s‖ ≤ 1 := mem_closedBall_zero_iff.1 hs;have hw_re : 0 < (1 - s * (t : Z)).re := xG hs1 ht0.le ht.2;have hslit : 1 - s * (t : Z) ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl hw_re)
  refine ContinuousAt.continuousWithinAt ?_
  dsimp [xD]
  refine continuousAt_const.mul (ContinuousAt.cpow ?_ continuousAt_const hslit)
  exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
lemma Qk : ContinuousOn zn (closedBall (0 : Z) 1) := by
 have hcomp : ContinuousOn (fun u : Z => xE (5 / 12) (3 / 4) (4 / 3) (u ^ 3))
   (closedBall (0 : Z) 1) :=
  (Qj xv k7 xt).comp
   (continuous_pow 3).continuousOn fun u hu => by
    rw [mem_closedBall, dist_zero_right] at hu ⊢
    rw [norm_pow];exact pow_le_one₀ (norm_nonneg u) hu
 exact continuousOn_id.mul hcomp
lemma Ql : ContinuousOn zo (closedBall (0 : Z) 1) :=
 (Qj xq xg xo).comp
  (continuous_pow 3).continuousOn fun u hu => by
   rw [mem_closedBall, dist_zero_right] at hu ⊢
   rw [norm_pow];exact pow_le_one₀ (norm_nonneg u) hu
lemma Qm : ContinuousOn zp (closedBall (0 : Z) 1) :=
 (continuousOn_const.mul Qk).div Ql
  fun _ hu => z3 hu
lemma Qn : ContinuousOn zq (closedBall (0 : Z) 1) := by
 have hcomp : ContinuousOn (fun u : Z => xE (1 / 3) (2 / 3) (4 / 3) (u ^ 3))
   (closedBall (0 : Z) 1) :=
  (Qj xA k4 xy).comp
   (continuous_pow 3).continuousOn fun u hu => by
    rw [mem_closedBall, dist_zero_right] at hu ⊢
    rw [norm_pow];exact pow_le_one₀ (norm_nonneg u) hu
 exact continuousOn_id.mul hcomp
lemma Qo : ContinuousOn zr (closedBall (0 : Z) 1) :=
 continuousOn_const.mul Qn
lemma Qp {u : Z} (hu : u ∈ ball (0 : Z) 1 ∪ zy) (hy2 : zo u ≠ 0) :
  HasDerivAt zp ((zc : Z) * (1 - u ^ 3) ^ (-5 / 6 : Z) / zo u ^ 2) u := by
 have hslit_one : u ^ 3 ∈ xN := by
  rcases hu with h | h
  · exact zL h
  · exact zK h
 have dy1 := (zQ hslit_one).congr_deriv (zQ hslit_one).deriv.symm;have dy2 := (zT hslit_one).congr_deriv (zT hslit_one).deriv.symm;have hdiv := ((dy1.const_mul (zc : Z)).div dy2 hy2)
 refine hdiv.congr_deriv ?_
 have hwron := z1 u hu;have hslit_p : 1 - u ^ 3 ∈ slitPlane := zM hslit_one;have hne : 1 - u ^ 3 ≠ 0 := slitPlane_ne_zero hslit_p
 have hcp : (1 - u ^ 3) ^ (-5 / 6 : Z) = ((1 - u ^ 3) ^ (5 / 6 : Z))⁻¹ := by
  rw [show (-5 / 6 : Z) = -(5 / 6 : Z) by ring]
  exact cpow_neg (1 - u ^ 3) (5 / 6 : Z)
 have hderiv_wron : deriv zn u * zo u - zn u * deriv zo u = (1 - u ^ 3) ^ (-5 / 6 : Z) := by
  rw [hcp];exact eq_inv_of_mul_eq_one_right hwron
 calc ((zc : Z) * deriv zn u * zo u - (zc : Z) * zn u * deriv zo u) / zo u ^ 2
     = (zc : Z) * (deriv zn u * zo u - zn u * deriv zo u) / zo u ^ 2 := by ring
   _ = (zc : Z) * (1 - u ^ 3) ^ (-5 / 6 : Z) / zo u ^ 2 := by rw [hderiv_wron]
lemma Qq {u : Z} (hu : u ∈ ball (0 : Z) 1 ∪ zy) (hy2 : zo u ≠ 0) :
  deriv zp u ≠ 0 := by
 rw [(Qp hu hy2).deriv]
 have hslit_one : u ^ 3 ∈ xN := by
  rcases hu with h | h
  · exact zL h
  · exact zK h
 have hne1 : 1 - u ^ 3 ≠ 0 := slitPlane_ne_zero (zM hslit_one);have hcp_ne : (1 - u ^ 3) ^ (-5 / 6 : Z) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hne1);have hC1_ne : (zc : Z) ≠ 0 := ofReal_ne_zero.2 ze.ne';exact div_ne_zero (mul_ne_zero hC1_ne hcp_ne) (pow_ne_zero 2 hy2)
lemma Qr : zp 0 = 0 := by simp only [zp,zn,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_mul,mul_zero,zero_div]
lemma Qs : deriv zp 0 = (zc : Z) := by
 have hy2_0 : zo 0 = 1 := by
  simpa [zo] using xL (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
   xg xn k4
 rw [(Qp (Or.inl (mem_ball_self one_pos)) (by rw [hy2_0];norm_num)).deriv, hy2_0]
 simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,sub_zero,one_cpow,mul_one,one_pow,div_one]
lemma Qt : zp 1 = (σ : Z) := by
 dsimp [zp, zn, zo];rw [one_pow, one_mul];have hF1 := xM (a := 5 / 12) (b := 3 / 4) (c := 4 / 3)
  k7 xs xt xu
 have hF2 := xM (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
  xg xn xo xp
 rw [hF1, hF2];dsimp [zc, σ];rw [← ofReal_mul, ← ofReal_div];congr 1;have h43 : Gamma (4 / 3) ≠ 0 := xB k5;have h23 : Gamma (2 / 3) ≠ 0 := xB k4;have h14 : Gamma (1 / 4) ≠ 0 := xB k6;have h1112 : Gamma (11 / 12) ≠ 0 := xB xi;have h712 : Gamma (7 / 12) ≠ 0 := xB xh;have h16 : Gamma (1 / 6) ≠ 0 := xB k8
 have hsr : Y (1 + Y 3) ≠ 0 := by positivity
 rw [show (4 / 3 - 5 / 12 - 3 / 4 : X) = 1 / 6 by ring,
  show (4 / 3 - 5 / 12 : X) = 11 / 12 by ring,
  show (4 / 3 - 3 / 4 : X) = 7 / 12 by ring,
  show (2 / 3 - 1 / 12 - 5 / 12 : X) = 1 / 6 by ring,
  show (2 / 3 - 1 / 12 : X) = 7 / 12 by ring,
  show (2 / 3 - 5 / 12 : X) = 1 / 4 by ring]
 field_simp [h43, h23, h14, h1112, h712, h16, hsr]
lemma Qu :
  zp 1 = j5 0 ∧ zp (ω ^ 2) = j5 1 ∧ zp ω = j5 2 := by
 have h0 : zp 1 = j5 0 := by rw [Qt];simp only [j5,j4,mul_one]
 have h2 : zp ω = j5 2 := by rw [show ω = ω * 1 by ring, Qe, Qt];simp only [j5,j4];ring
 have h1 : zp (ω ^ 2) = j5 1 := by rw [show ω ^ 2 = ω * ω by ring, Qe, h2, j5, j5, j4, j4];ring
 exact ⟨h0, h1, h2⟩
lemma Qv :
  (xE (1 / 12) (5 / 12) (2 / 3) 1).re ≤ 3 / 2 := by
 have hint1 : IntervalIntegrable (xD (1 / 12) (5 / 12) (2 / 3) 1) volume 0 1 :=
  xQ xg xn xo norm_one.le
 have hint0 : IntervalIntegrable (xD (1 / 12) (5 / 12) (2 / 3) 0) volume 0 1 :=
  xQ xg xn xo (norm_zero.trans_le zero_le_one)
 have hF0 : xE (1 / 12) (5 / 12) (2 / 3) 0 = 1 :=
  xL xg xn k4
 have hpre_pos : 0 < Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (1 / 4)) := by
  have g1 := gP k4;have g2 := gP xg;have g3 := gP k6;positivity
 have hre_eq : ∀ s : Z, ‖s‖ ≤ 1 → s = 0 ∨ s = 1 →
   (xE (1 / 12) (5 / 12) (2 / 3) s).re =
    (Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (1 / 4))) *
     ∫ t in Ioo (0 : X) 1, t ^ (-7 / 12 : X) * (1 - t) ^ (if s = 1 then (-5 / 6 : X) else (-3 / 4 : X)) := by
  intro s hs h01;have hint := xQ (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
   xg xn xo hs
  dsimp [xE]
  rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
   show (2 / 3 - 5 / 12 : X) = 1 / 4 by ring]
  congr 1
  have hre_int : (∫ t in (0 : X)..1, xD (1 / 12) (5 / 12) (2 / 3) s t).re =
    ∫ t in (0 : X)..1, (xD (1 / 12) (5 / 12) (2 / 3) s t).re :=
   (reCLM.intervalIntegral_comp_comm hint).symm
  rw [hre_int, integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := ht.1;have ht1 : 0 < 1 - t := sub_pos.2 ht.2
  have h1t : (1 : Z) - (t : Z) = ((1 - t : X) : Z) := by push_cast;rfl
  have ht_pow : (t : Z) ^ (((5 / 12 : X) : Z) - 1) = ((t ^ (-7 / 12 : X) : X) : Z) := by
   rw [show (((5 / 12 : X) : Z) - 1) = ((-7 / 12 : X) : Z) by push_cast;ring,
    ← ofReal_cpow ht0.le]
  have h1t_pow : (1 - (t : Z)) ^ (((2 / 3 : X) : Z) - ((5 / 12 : X) : Z) - 1) =
    (((1 - t) ^ (-3 / 4 : X) : X) : Z) := by
   rw [h1t, show (((2 / 3 : X) : Z) - ((5 / 12 : X) : Z) - 1) = ((-3 / 4 : X) : Z) by push_cast;ring,
    ← ofReal_cpow ht1.le]
  dsimp [xD]
  rcases h01 with rfl | rfl
  ·
   simp only [zero_mul,sub_zero,one_cpow,mul_one,if_neg zero_ne_one];rw [ht_pow, h1t_pow, ← ofReal_mul, ofReal_re]
  ·
   simp only [one_mul,↓reduceIte]
   have hc_pow : (1 - (t : Z)) ^ (-((1 / 12 : X) : Z)) = (((1 - t) ^ (-1 / 12 : X) : X) : Z) := by
    rw [h1t, show -((1 / 12 : X) : Z) = ((-1 / 12 : X) : Z) by push_cast;ring,
     ← ofReal_cpow ht1.le]
   rw [ht_pow, h1t_pow, hc_pow, ← ofReal_mul, ← ofReal_mul, ofReal_re, mul_assoc,
    ← rpow_add ht1, show (-3 / 4 : X) + (-1 / 12 : X) = -5 / 6 by ring]
 have hI1 := hre_eq 1 norm_one.le (Or.inr rfl);have hI0 := hre_eq 0 (norm_zero.trans_le zero_le_one) (Or.inl rfl);rw [if_pos rfl] at hI1;rw [if_neg zero_ne_one, hF0, one_re] at hI0
 have hdiff_le : ∫ t in Ioo (0 : X) 1, t ^ (-7 / 12 : X) * (1 - t) ^ (-5 / 6 : X) ≤
   (3 / 2 : X) * ∫ t in Ioo (0 : X) 1, t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X) := by
  have hi1 : IntegrableOn (fun t : X => t ^ (-7 / 12 : X) * (1 - t) ^ (-5 / 6 : X)) (Ioo 0 1) := by
   rw [show (-7 / 12 : X) = 5 / 12 - 1 by ring, show (-5 / 6 : X) = 1 / 6 - 1 by ring]
   exact Qh (p := 5 / 12) (q := 1 / 6) xg k8
  have hi0 : IntegrableOn (fun t : X => t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X)) (Ioo 0 1) := by
   rw [show (-7 / 12 : X) = 5 / 12 - 1 by ring, show (-3 / 4 : X) = 1 / 4 - 1 by ring]
   exact Qh (p := 5 / 12) (q := 1 / 4) xg k6
  have hsub : (∫ t in Ioo (0 : X) 1, t ^ (-7 / 12 : X) * (1 - t) ^ (-5 / 6 : X)) -
    (3 / 2 : X) * ∫ t in Ioo (0 : X) 1, t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X) =
    ∫ u in Ioo (0 : X) 1, (1 - u) ^ (-7 / 12 : X) * (u ^ (-5 / 6 : X) - (3 / 2 : X) * u ^ (-3 / 4 : X)) := by
   have hmul : (3 / 2 : X) * ∫ t in Ioo (0 : X) 1, t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X) =
     ∫ t in Ioo (0 : X) 1, (3 / 2 : X) * (t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X)) :=
    (MeasureTheory.integral_const_mul _ _).symm
   rw [hmul, ← MeasureTheory.integral_sub hi1 (hi0.const_mul _)];let ψ : X → X := fun u => 1 - u
   have hinj : InjOn ψ (Ioo (0 : X) 1) := fun x _ y _ h => by dsimp [ψ] at h;linarith
   have himg : ψ '' Ioo (0 : X) 1 = Ioo 0 1 := by
    ext x;constructor
    · rintro ⟨y, hy, rfl⟩;exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    · intro hx;exact ⟨1 - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, by dsimp [ψ];ring⟩
   have hd : ∀ u ∈ Ioo (0 : X) 1, HasDerivWithinAt ψ (-1) (Ioo 0 1) u := fun u _ =>
    ((hasDerivAt_id u).const_sub 1).hasDerivWithinAt
   have hch := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj
    (fun t : X => t ^ (-7 / 12 : X) * (1 - t) ^ (-5 / 6 : X) -
     (3 / 2 : X) * (t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X)))
   rw [himg] at hch;rw [hch]
   refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
   simp only [ψ,abs_neg,abs_one,one_smul,sub_sub_cancel];ring
  let uc : X := (2 / 3 : X) ^ (12 : ℕ)
  have huc0 : 0 < uc := by positivity
  have huc1 : uc < 1 := by dsimp [uc];norm_num
  have h1uc : 0 < 1 - uc := by linarith
  let C : X := (1 - uc) ^ (-7 / 12 : X);have hC0 : 0 < C := rpow_pos_of_pos h1uc _;have hdom_int : IntegrableOn
    (fun u : X => C * (u ^ (-5 / 6 : X) - (3 / 2 : X) * u ^ (-3 / 4 : X))) (Ioo 0 1) := by
   have ha56 : IntegrableOn (fun u : X => u ^ (-5 / 6 : X)) (Ioo 0 1) := by
    have := intervalIntegrable_rpow' (a := (0 : X)) (b := 1) (r := (-5 / 6 : X)) (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this;exact this.mono_set Ioo_subset_Ioc_self
   have ha34 : IntegrableOn (fun u : X => u ^ (-3 / 4 : X)) (Ioo 0 1) := by
    have := intervalIntegrable_rpow' (a := (0 : X)) (b := 1) (r := (-3 / 4 : X)) (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this;exact this.mono_set Ioo_subset_Ioc_self
   exact (ha56.sub (ha34.const_mul _)).const_mul _
  have hpt : ∀ u ∈ Ioo (0 : X) 1,
    (1 - u) ^ (-7 / 12 : X) * (u ^ (-5 / 6 : X) - (3 / 2 : X) * u ^ (-3 / 4 : X)) ≤
     C * (u ^ (-5 / 6 : X) - (3 / 2 : X) * u ^ (-3 / 4 : X)) := by
   intro u hu;have hu0 : 0 < u := hu.1;have h1u : 0 < 1 - u := sub_pos.2 hu.2
   have hfac : u ^ (-5 / 6 : X) - (3 / 2 : X) * u ^ (-3 / 4 : X) =
     u ^ (-5 / 6 : X) * (1 - (3 / 2 : X) * u ^ (1 / 12 : X)) := by
    rw [mul_sub, mul_one, ← mul_assoc, mul_comm (u ^ (-5 / 6 : X)) (3 / 2 : X), mul_assoc,
     ← rpow_add hu0, show (-5 / 6 : X) + 1 / 12 = -3 / 4 by norm_num]
   have hupos : 0 < u ^ (-5 / 6 : X) := rpow_pos_of_pos hu0 _
   have hpow12 : (uc) ^ (1 / 12 : X) = 2 / 3 := by dsimp [uc];rw [← rpow_natCast, ← rpow_mul (by norm_num)];norm_num
   rcases le_total u uc with hle | hge
   ·
    have hle12 : u ^ (1 / 12 : X) ≤ 2 / 3 := by rw [← hpow12];exact rpow_le_rpow hu0.le hle xf.le
    have hdiff_nn : 0 ≤ u ^ (-5 / 6 : X) - (3 / 2 : X) * u ^ (-3 / 4 : X) := by rw [hfac];exact mul_nonneg hupos.le (by linarith only [hle12])
    have h1u_ge : 1 - uc ≤ 1 - u := by linarith only [hle]
    have hC_ge : (1 - u) ^ (-7 / 12 : X) ≤ C := by
     dsimp [C];rw [show (-7 / 12 : X) = -(7 / 12) by ring, rpow_neg h1u.le, rpow_neg h1uc.le]
     exact inv_anti₀ (rpow_pos_of_pos h1uc _) (rpow_le_rpow h1uc.le h1u_ge xh.le)
    exact mul_le_mul_of_nonneg_right hC_ge hdiff_nn
   ·
    have hge12 : 2 / 3 ≤ u ^ (1 / 12 : X) := by rw [← hpow12];exact rpow_le_rpow huc0.le hge xf.le
    have hdiff_np : u ^ (-5 / 6 : X) - (3 / 2 : X) * u ^ (-3 / 4 : X) ≤ 0 := by rw [hfac];exact mul_nonpos_of_nonneg_of_nonpos hupos.le (by linarith only [hge12])
    have h1u_le : 1 - u ≤ 1 - uc := by linarith only [hge]
    have hC_le : C ≤ (1 - u) ^ (-7 / 12 : X) := by
     dsimp [C];rw [show (-7 / 12 : X) = -(7 / 12) by ring, rpow_neg h1u.le, rpow_neg h1uc.le]
     exact inv_anti₀ (rpow_pos_of_pos h1u _) (rpow_le_rpow h1u.le h1u_le xh.le)
    nlinarith only [hdiff_np, hC_le]
  have hleft_int : IntegrableOn
    (fun u : X => (1 - u) ^ (-7 / 12 : X) * (u ^ (-5 / 6 : X) - (3 / 2 : X) * u ^ (-3 / 4 : X))) (Ioo 0 1) := by
   have ha1 : IntegrableOn (fun u : X => u ^ (-5 / 6 : X) * (1 - u) ^ (-7 / 12 : X)) (Ioo 0 1) := by
    rw [show (-5 / 6 : X) = 1 / 6 - 1 by ring, show (-7 / 12 : X) = 5 / 12 - 1 by ring]
    exact Qh (p := 1 / 6) (q := 5 / 12) k8 xg
   have ha2 : IntegrableOn (fun u : X => u ^ (-3 / 4 : X) * (1 - u) ^ (-7 / 12 : X)) (Ioo 0 1) := by
    rw [show (-3 / 4 : X) = 1 / 4 - 1 by ring, show (-7 / 12 : X) = 5 / 12 - 1 by ring]
    exact Qh (p := 1 / 4) (q := 5 / 12) k6 xg
   refine (ha1.sub (ha2.const_mul (3 / 2 : X))).congr_fun (fun u _ => by simp only [Pi.sub_apply];ring) measurableSet_Ioo
  have hzero : ∫ u in Ioo (0 : X) 1, C * (u ^ (-5 / 6 : X) - (3 / 2 : X) * u ^ (-3 / 4 : X)) = 0 := by
   rw [MeasureTheory.integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← integral_of_le zero_le_one]
   have hi56 : IntervalIntegrable (fun u : X => u ^ (-5 / 6 : X)) volume 0 1 :=
    intervalIntegrable_rpow' (by norm_num)
   have hi34 : IntervalIntegrable (fun u : X => u ^ (-3 / 4 : X)) volume 0 1 :=
    intervalIntegrable_rpow' (by norm_num)
   rw [intervalIntegral.integral_sub hi56 (hi34.const_mul _),
    intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num)), integral_rpow (Or.inl (by norm_num))]
   norm_num
  have hmono := setIntegral_mono_on hleft_int hdom_int measurableSet_Ioo hpt
  have hneg : ∫ u in Ioo (0 : X) 1, (1 - u) ^ (-7 / 12 : X) * (u ^ (-5 / 6 : X) - (3 / 2 : X) * u ^ (-3 / 4 : X)) ≤ 0 :=
   hmono.trans hzero.le
  linarith only [hsub, hneg]
 rw [hI1]
 calc (Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (1 / 4))) *
       ∫ t in Ioo (0 : X) 1, t ^ (-7 / 12 : X) * (1 - t) ^ (-5 / 6 : X)
     ≤ (Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (1 / 4))) *
       ((3 / 2 : X) * ∫ t in Ioo (0 : X) 1, t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X)) :=
       mul_le_mul_of_nonneg_left hdiff_le hpre_pos.le
   _ = 3 / 2 * ((Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (1 / 4))) *
       ∫ t in Ioo (0 : X) 1, t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X)) := by ring
   _ = 3 / 2 := by rw [← hI0, mul_one]
lemma Qw {a b c : X} (ha : 0 ≤ a) (hb : 0 < b) (hcab : 0 < c - a - b)
  {s : Z} (hs : ‖s‖ ≤ 1) :
  ‖xE a b c s‖ ≤ (xE a b c 1).re := by
 have hcb : 0 < c - b := by linarith
 have hpre_pos : 0 < Gamma c / (Gamma b * Gamma (c - b)) := by
  have g1 := gP (by linarith : 0 < c)
  have g2 := gP hb;have g3 := gP hcb;positivity
 have hint_s := xQ hb hcb hcab hs;have hint_1 := xQ hb hcb hcab norm_one.le;dsimp [xE]
 rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
  norm_mul, Complex.norm_of_nonneg hpre_pos.le]
 refine mul_le_mul_of_nonneg_left ?_ hpre_pos.le
 have hre_int : (∫ t in (0 : X)..1, xD a b c 1 t).re =
   ∫ t in (0 : X)..1, (xD a b c 1 t).re :=
  (reCLM.intervalIntegral_comp_comm hint_1).symm
 rw [hre_int, integral_of_le zero_le_one, integral_of_le zero_le_one]
 calc ‖∫ t in Ioc (0 : X) 1, xD a b c s t‖
     ≤ ∫ t in Ioc (0 : X) 1, ‖xD a b c s t‖ :=
       MeasureTheory.norm_integral_le_integral_norm _
   _ = ∫ t in Ioo (0 : X) 1, ‖xD a b c s t‖ :=
       integral_Ioc_eq_integral_Ioo
   _ ≤ ∫ t in Ioo (0 : X) 1, (xD a b c 1 t).re := by
       refine setIntegral_mono_on
         (hint_s.1.norm.mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl))
         ((reCLM.integrable_comp hint_1.1).mono_measure
           (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl))
         measurableSet_Ioo fun t ht => ?_
       have ht0 : 0 < t := ht.1
       have ht1 : 0 < 1 - t := sub_pos.2 ht.2
       have hw_re : 0 < (1 - s * (t : Z)).re := xG hs ht0.le ht.2
       have hw_ne : 1 - s * (t : Z) ≠ 0 := by intro h;rw [h, zero_re] at hw_re;linarith
       have hw_ge : 1 - t ≤ ‖1 - s * (t : Z)‖ := by
         have htri := norm_sub_norm_le (1 : Z) (s * (t : Z))
         have hst : ‖s * (t : Z)‖ ≤ t := by rw [norm_mul, Complex.norm_of_nonneg ht0.le];exact mul_le_of_le_one_left ht0.le hs
         simp only [norm_one] at htri;linarith
       have hcp_norm : ‖(1 - s * (t : Z)) ^ (-a : Z)‖ = ‖1 - s * (t : Z)‖ ^ (-a) :=
         Qi hw_ne a
       have hpow_le : ‖1 - s * (t : Z)‖ ^ (-a) ≤ (1 - t) ^ (-a) := by
         rw [rpow_neg (norm_nonneg _), rpow_neg ht1.le]
         exact inv_anti₀ (rpow_pos_of_pos ht1 _) (rpow_le_rpow ht1.le hw_ge ha)
       have h1t : (1 : Z) - (t : Z) = ((1 - t : X) : Z) := by push_cast;rfl
       have hbase : (t : Z) ^ ((b : Z) - 1) * (1 - (t : Z)) ^ ((c : Z) - (b : Z) - 1) =
           ((t ^ (b - 1) * (1 - t) ^ (c - b - 1) : X) : Z) := by
         rw [h1t, show (b : Z) - 1 = ((b - 1 : X) : Z) by push_cast;ring,
           show (c : Z) - (b : Z) - 1 = ((c - b - 1 : X) : Z) by push_cast;ring,
           ← ofReal_cpow ht0.le, ← ofReal_cpow ht1.le, ofReal_mul]
       have hbase_nn : 0 ≤ t ^ (b - 1) * (1 - t) ^ (c - b - 1) := by positivity
       dsimp [xD]
       rw [norm_mul, hbase, Complex.norm_of_nonneg hbase_nn, hcp_norm]
       have h_rhs : (((t ^ (b - 1) * (1 - t) ^ (c - b - 1) : X) : Z) *
             (1 - 1 * (t : Z)) ^ (-a : Z)).re =
           (t ^ (b - 1) * (1 - t) ^ (c - b - 1)) * (1 - t) ^ (-a) := by
         rw [one_mul, h1t, show (-a : Z) = ((-a : X) : Z) by push_cast;rfl,
           ← ofReal_cpow ht1.le, ← ofReal_mul, ofReal_re]
       rw [h_rhs]
       exact mul_le_mul_of_nonneg_left hpow_le hbase_nn
   _ = ∫ t in Ioc (0 : X) 1, (xD a b c 1 t).re :=
       integral_Ioc_eq_integral_Ioo.symm
lemma Qx {u : Z} (hu : u ∈ closedBall (0 : Z) 1) : ‖zp u‖ < 1 := by
 have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
 have hu3 : ‖u ^ 3‖ ≤ 1 := by rw [norm_pow];exact pow_le_one₀ (norm_nonneg u) hu1
 have hy1_bound : ‖zn u‖ ≤ (xE (5 / 12) (3 / 4) (4 / 3) 1).re := by
  have hE_le := Qw (a := 5 / 12) (b := 3 / 4) (c := 4 / 3)
   xv k7 xt hu3
  calc ‖zn u‖ = ‖u‖ * ‖xE (5 / 12) (3 / 4) (4 / 3) (u ^ 3)‖ := by dsimp [zn];rw [norm_mul]
    _ ≤ 1 * (xE (5 / 12) (3 / 4) (4 / 3) 1).re :=
        mul_le_mul hu1 hE_le (norm_nonneg _) zero_le_one
    _ = (xE (5 / 12) (3 / 4) (4 / 3) 1).re := one_mul _
 have hC1_F1_eq : zc * (xE (5 / 12) (3 / 4) (4 / 3) 1).re =
   σ * (xE (1 / 12) (5 / 12) (2 / 3) 1).re := by
  have h1 := xM (a := 5 / 12) (b := 3 / 4) (c := 4 / 3)
   k7 xs xt xu
  have h2 := xM (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
   xg xn xo xp
  rw [h1, h2, ofReal_re, ofReal_re];dsimp [zc, σ];have h43 : Gamma (4 / 3) ≠ 0 := xB k5;have h23 : Gamma (2 / 3) ≠ 0 := xB k4;have h14 : Gamma (1 / 4) ≠ 0 := xB k6;have h1112 : Gamma (11 / 12) ≠ 0 := xB xi;have h712 : Gamma (7 / 12) ≠ 0 := xB xh;have h16 : Gamma (1 / 6) ≠ 0 := xB k8
  have hsr : Y (1 + Y 3) ≠ 0 := by positivity
  rw [show (4 / 3 - 5 / 12 - 3 / 4 : X) = 1 / 6 by ring,
   show (4 / 3 - 5 / 12 : X) = 11 / 12 by ring,
   show (4 / 3 - 3 / 4 : X) = 7 / 12 by ring,
   show (2 / 3 - 1 / 12 - 5 / 12 : X) = 1 / 6 by ring,
   show (2 / 3 - 1 / 12 : X) = 7 / 12 by ring,
   show (2 / 3 - 5 / 12 : X) = 1 / 4 by ring]
  field_simp [h43, h23, h14, h1112, h712, h16, hsr]
 have hnum_le : ‖(zc : Z) * zn u‖ ≤ σ * (3 / 2) := by
  rw [norm_mul, Complex.norm_of_nonneg ze.le]
  calc zc * ‖zn u‖ ≤ zc * (xE (5 / 12) (3 / 4) (4 / 3) 1).re :=
        mul_le_mul_of_nonneg_left hy1_bound ze.le
    _ = σ * (xE (1 / 12) (5 / 12) (2 / 3) 1).re := hC1_F1_eq
    _ ≤ σ * (3 / 2) := mul_le_mul_of_nonneg_left Qv qn.le
 have hy2_lb : (16 / 17 : X) * (99 / 100) ≤ (zo u).re := by
  have hint := xQ (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
   xg xn xo hu3
  have hint0 := xQ (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
   xg xn xo (norm_zero.trans_le zero_le_one)
  have hF0 : xE (1 / 12) (5 / 12) (2 / 3) 0 = 1 :=
   xL xg xn k4
  have hpre_pos : 0 < Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (2 / 3 - 5 / 12)) := by
   have g1 := gP k4;have g2 := gP xg;have g3 := gP xn;positivity
  have hre_0 : (Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (2 / 3 - 5 / 12))) *
    ∫ t in Ioo (0 : X) 1, (xD (1 / 12) (5 / 12) (2 / 3) 0 t).re = 1 := by
   have h0 := congr_arg Complex.re hF0;dsimp [xE] at h0
   have hre_int0 : (∫ t in (0 : X)..1, xD (1 / 12) (5 / 12) (2 / 3) 0 t).re =
     ∫ t in (0 : X)..1, (xD (1 / 12) (5 / 12) (2 / 3) 0 t).re :=
    (reCLM.intervalIntegral_comp_comm hint0).symm
   rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    hre_int0, integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h0
   simpa using h0
  have h2_12 : (16 / 17 : X) ≤ (2 : X) ^ (-1 / 12 : X) := by
   have hpow : (16 / 17 : X) ^ (12 : ℕ) ≤ 2⁻¹ := by norm_num
   have h12 : ((16 / 17 : X) ^ (12 : ℕ)) ^ (1 / 12 : X) ≤ (2⁻¹ : X) ^ (1 / 12 : X) :=
    rpow_le_rpow (by positivity) hpow (by norm_num)
   rw [← rpow_natCast, ← rpow_mul (by norm_num), show ((12 : ℕ) : X) * (1 / 12) = 1 by norm_num,
    rpow_one, ← Real.rpow_neg_one, ← rpow_mul (by norm_num),
    show (-1 : X) * (1 / 12) = -1 / 12 by norm_num] at h12
   exact h12
  have hcos_lb : ∀ θ : X, |θ| ≤ π / 24 → (99 / 100 : X) ≤ cos θ := by
   intro θ hθ
   have hpi : π < 32 / 10 := by linarith [pi_lt_d2]
   have hsin : |sin (θ / 2)| ≤ |θ / 2| := abs_sin_le_abs
   have hsq : sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 := by
    rw [← sq_abs (sin (θ / 2)), ← sq_abs (θ / 2)]
    exact sq_le_sq' (by linarith [abs_nonneg (sin (θ / 2))]) hsin
   have hcos2 : cos θ = 1 - 2 * sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring, Real.cos_sq'] at this
    linarith
   have hth_sq : (θ / 2) ^ 2 ≤ (32 / 10 / 48) ^ 2 := by
    rw [← sq_abs (θ / 2)]
    have hbd : |θ / 2| ≤ 32 / 10 / 48 := by rw [abs_div, abs_of_pos (two_pos : (0 : X) < 2)];linarith
    exact sq_le_sq' (by linarith [abs_nonneg (θ / 2)]) hbd
   nlinarith only [hth_sq, hcos2, hsq]
  have hpt : ∀ t ∈ Ioo (0 : X) 1,
    ((16 / 17 : X) * (99 / 100)) * (xD (1 / 12) (5 / 12) (2 / 3) 0 t).re ≤
     (xD (1 / 12) (5 / 12) (2 / 3) (u ^ 3) t).re := by
   intro t ht;have ht0 : 0 < t := ht.1;have ht1 : 0 < 1 - t := sub_pos.2 ht.2
   have h1t : (1 : Z) - (t : Z) = ((1 - t : X) : Z) := by push_cast;rfl
   have hw_re : 0 < (1 - u ^ 3 * (t : Z)).re := xG hu3 ht0.le ht.2
   have hw_ne : 1 - u ^ 3 * (t : Z) ≠ 0 := by intro h;rw [h, zero_re] at hw_re;linarith
   have hw_le : ‖1 - u ^ 3 * (t : Z)‖ ≤ 2 := by
    calc ‖1 - u ^ 3 * (t : Z)‖ ≤ ‖(1 : Z)‖ + ‖u ^ 3 * (t : Z)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 * 1 := by
          rw [norm_one, norm_mul, Complex.norm_of_nonneg ht0.le]
          exact add_le_add le_rfl (mul_le_mul hu3 ht.2.le ht0.le zero_le_one)
      _ = 2 := by ring
   have hw_rpow : (16 / 17 : X) ≤ ‖1 - u ^ 3 * (t : Z)‖ ^ (-1 / 12 : X) := by
    refine h2_12.trans ?_
    rw [show (-1 / 12 : X) = -(1 / 12) by ring, rpow_neg two_pos.le,
     rpow_neg (norm_nonneg _)]
    exact inv_anti₀ (rpow_pos_of_pos (norm_pos_iff.2 hw_ne) _)
     (rpow_le_rpow (norm_nonneg _) hw_le xf.le)
   have harg : |Complex.arg (1 - u ^ 3 * (t : Z))| < π / 2 :=
    abs_arg_lt_pi_div_two_iff.2 (Or.inl hw_re)
   have hcos_ge : (99 / 100 : X) ≤ cos (-(1 / 12 : X) * Complex.arg (1 - u ^ 3 * (t : Z))) := by
    refine hcos_lb _ ?_
    rw [abs_mul, abs_neg, abs_of_nonneg xf.le];linarith
   have hcp_re : ((1 - u ^ 3 * (t : Z)) ^ (-((1 / 12 : X) : Z))).re =
     ‖1 - u ^ 3 * (t : Z)‖ ^ (-1 / 12 : X) *
      cos (-(1 / 12 : X) * Complex.arg (1 - u ^ 3 * (t : Z))) := by
    rw [cpow_def_of_ne_zero hw_ne, exp_re,
     show (-((1 / 12 : X) : Z)) = ((-1 / 12 : X) : Z) by push_cast;ring]
    simp only [mul_re, mul_im, log_re, log_im,
     ofReal_re, ofReal_im, mul_zero, sub_zero]
    rw [rpow_def_of_pos (norm_pos_iff.2 hw_ne)];ring_nf
   have hcp_lb : (16 / 17 : X) * (99 / 100) ≤ ((1 - u ^ 3 * (t : Z)) ^ (-((1 / 12 : X) : Z))).re := by
    rw [hcp_re]
    exact mul_le_mul hw_rpow hcos_ge (by norm_num) (rpow_nonneg (norm_nonneg _) _)
   have hbase : (t : Z) ^ (((5 / 12 : X) : Z) - 1) * (1 - (t : Z)) ^ (((2 / 3 : X) : Z) - ((5 / 12 : X) : Z) - 1) =
     ((t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X) : X) : Z) := by
    rw [h1t, show (((5 / 12 : X) : Z) - 1) = ((-7 / 12 : X) : Z) by push_cast;ring,
     show (((2 / 3 : X) : Z) - ((5 / 12 : X) : Z) - 1) = ((-3 / 4 : X) : Z) by push_cast;ring,
     ← ofReal_cpow ht0.le, ← ofReal_cpow ht1.le, ofReal_mul]
   have hbase_nn : 0 ≤ t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X) := by positivity
   have h0_val : (xD (1 / 12) (5 / 12) (2 / 3) 0 t).re =
     t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X) := by
    dsimp [xD];rw [zero_mul, sub_zero, one_cpow, mul_one, hbase, ofReal_re]
   have hu_val : (xD (1 / 12) (5 / 12) (2 / 3) (u ^ 3) t).re =
     (t ^ (-7 / 12 : X) * (1 - t) ^ (-3 / 4 : X)) *
      ((1 - u ^ 3 * (t : Z)) ^ (-((1 / 12 : X) : Z))).re := by
    dsimp [xD];rw [hbase, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
   rw [h0_val, hu_val];nlinarith only [hbase_nn, hcp_lb]
  have h_int_mono := setIntegral_mono_on
   ((reCLM.integrable_comp hint0.1).mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl) |>.const_mul _)
   ((reCLM.integrable_comp hint.1).mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl))
   measurableSet_Ioo hpt
  rw [MeasureTheory.integral_const_mul] at h_int_mono
  have hy2_eq : (zo u).re = (Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (2 / 3 - 5 / 12))) *
    ∫ t in Ioo (0 : X) 1, (xD (1 / 12) (5 / 12) (2 / 3) (u ^ 3) t).re := by
   dsimp [zo, xE]
   have hre_int : (∫ t in (0 : X)..1, xD (1 / 12) (5 / 12) (2 / 3) (u ^ 3) t).re =
     ∫ t in (0 : X)..1, (xD (1 / 12) (5 / 12) (2 / 3) (u ^ 3) t).re :=
    (reCLM.intervalIntegral_comp_comm hint).symm
   rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    hre_int, integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [hy2_eq]
  calc (16 / 17 : X) * (99 / 100) = ((16 / 17 : X) * (99 / 100)) * 1 := (mul_one _).symm
    _ = ((16 / 17 : X) * (99 / 100)) *
        ((Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (2 / 3 - 5 / 12))) *
          ∫ t in Ioo (0 : X) 1, (xD (1 / 12) (5 / 12) (2 / 3) 0 t).re) := by rw [hre_0]
    _ = (Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (2 / 3 - 5 / 12))) *
        (((16 / 17 : X) * (99 / 100)) *
          ∫ t in Ioo (0 : X) 1, (xD (1 / 12) (5 / 12) (2 / 3) 0 t).re) := by ring
    _ ≤ (Gamma (2 / 3) / (Gamma (5 / 12) * Gamma (2 / 3 - 5 / 12))) *
        ∫ t in Ioo (0 : X) 1, (xD (1 / 12) (5 / 12) (2 / 3) (u ^ 3) t).re :=
        mul_le_mul_of_nonneg_left h_int_mono hpre_pos.le
 have hden_ge : (16 / 17 : X) * (99 / 100) ≤ ‖zo u‖ :=
  hy2_lb.trans (re_le_norm (zo u))
 have hgap : σ * (3 / 2 : X) < (16 / 17 : X) * (99 / 100) := by
  have hrt3 : 17 / 10 < Y 3 := qf
  have hσ_sq : σ ^ 2 < 10 / 27 := by
   rw [qo];have h3 : Y 3 ^ 2 = 3 := qc
   have h1 : (Y 3 - 1) / 2 = 1 / (1 + Y 3) := by
    have hpos : (0 : X) < 1 + Y 3 := by positivity
    field_simp [hpos.ne'];linear_combination h3
   rw [h1, div_lt_div_iff₀ (by positivity) (by norm_num)]
   linarith
  have hsq_lt : (σ * (3 / 2 : X)) ^ 2 < ((16 / 17 : X) * (99 / 100)) ^ 2 := by nlinarith only [hσ_sq]
  nlinarith only [qn, hsq_lt]
 dsimp [zp];rw [norm_div]
 exact (div_lt_one (by positivity)).2 (lt_of_le_of_lt hnum_le (lt_of_lt_of_le hgap hden_ge))
lemma Qy {u : Z} (hu : u ∈ zy) (hy2u : zo u ≠ 0) (hy2v : zo (1 / T u) ≠ 0) :
  zp (1 / T u) = qL 1 (zp u) := by
 rw [z4 hu hy2u hy2v];dsimp [qL, qH, qy];rw [Qb, ← Qa];simp only [zs,mul_neg,neg_mul,map_neg,map_pow,sub_neg_eq_add,map_mul,conj_ofReal]
lemma Qz {u : Z} (hu : u ∈ zy) :
  zr (1 / T u) = (zd : Z) * qX 1 (zr u / (zd : Z)) := by
 rw [z9 hu];dsimp [qX];rw [← Qa];have hcAG_ne : (zd : Z) ≠ 0 := ofReal_ne_zero.2 zf.ne';simp only [map_div₀,conj_ofReal];field_simp [hcAG_ne]
lemma QA (z : Z) :
  qL 0 (ω * z) = ω * qL 1 z ∧ qL 2 (ω ^ 2 * z) = ω ^ 2 * qL 1 z := by
 have hc0 : qH 0 = ω * qH 1 := by
  dsimp [qH, qy]
  rw [show (tR : Z) * -1 = -((tR : Z) * ω ^ 3) by rw [qj];ring];ring
 have hc2 : qH 2 = ω ^ 2 * qH 1 := by
  dsimp [qH, qy]
  rw [show (tR : Z) * -ω = -((tR : Z) * ω * ω ^ 3) by rw [qj];ring];ring
 constructor
 ·
  dsimp [qL];rw [hc0, map_mul, ql]
  have hnum : ω * qH 1 * (ω ^ 2 * T z) - 1 =
    ω ^ 3 * (qH 1 * T z - 1) := by
   linear_combination qj
  have hden : ω ^ 2 * T z - T (ω * qH 1) =
    ω ^ 2 * (T z - T (qH 1)) := by
   rw [map_mul, ql];ring
  rw [hnum, hden]
  by_cases hd : T z - T (qH 1) = 0
  · simp only [Fin.isValue,hd,mul_zero,div_zero]
  ·
   have hne2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 (by intro h;have := qk;rw [h, norm_zero] at this;exact one_ne_zero this.symm)
   field_simp [hd, hne2]
 ·
  dsimp [qL];rw [hc2, map_mul, qY]
  have hnum : ω ^ 2 * qH 1 * (ω * T z) - 1 =
    ω ^ 3 * (qH 1 * T z - 1) := by
   linear_combination qj
  have hden : ω * T z - T (ω ^ 2 * qH 1) =
    ω * (T z - T (qH 1)) := by
   rw [map_mul, qY];ring
  rw [hnum, hden]
  by_cases hd : T z - T (qH 1) = 0
  · simp only [Fin.isValue,hd,mul_zero,div_zero]
  ·
   have hne : ω ≠ 0 := by intro h;have := qk;rw [h, norm_zero] at this;exact one_ne_zero this.symm
   field_simp [hd, hne]
lemma QB (w : Z) :
  qX 0 (ω * w) = ω * qX 1 w ∧ qX 2 (ω ^ 2 * w) = ω ^ 2 * qX 1 w := by
 constructor
 · dsimp [qX];rw [map_mul, ql];linear_combination qj
 · dsimp [qX];rw [map_mul, qY];linear_combination ω * qj
lemma QC :
  ω * qH 1 = qH 0 ∧ ω * qH 0 = qH 2 ∧ ω * qH 2 = qH 1 := by
 dsimp [qH, qy]
 refine ⟨?_, by ring, by ring⟩
 calc ω * ((tR : Z) * -ω ^ 2) = -(tR : Z) * ω ^ 3 := by ring
   _ = (tR : Z) * -1 := by rw [qj];ring
lemma QD {z : Z} : ω * z ∈ T0 ↔ z ∈ T0 := by
 have hω_normSq : W ω = 1 := by rw [← Complex.sq_norm, qk];exact one_pow 2
 have hball : ω * z ∈ ball (0 : Z) 1 ↔ z ∈ ball (0 : Z) 1 := by simp only [mem_ball,dist_zero_right,norm_mul,qk,one_mul]
 have hc := QC
 have hns : ∀ i j : Fin 3, ω * qH i = qH j →
   W (ω * z - qH j) = W (z - qH i) := fun i j hij => by
  rw [← hij, ← mul_sub, normSq_mul, hω_normSq, one_mul]
 constructor
 ·
  rintro ⟨hz, hT⟩
  refine ⟨hball.1 hz, fun i => ?_⟩
  fin_cases i <;> dsimp
  · rw [← hns 0 2 hc.2.1];exact hT 2
  · rw [← hns 1 0 hc.1];exact hT 0
  · rw [← hns 2 1 hc.2.2];exact hT 1
 ·
  rintro ⟨hz, hT⟩
  refine ⟨hball.2 hz, fun i => ?_⟩
  fin_cases i <;> dsimp
  · rw [hns 1 0 hc.1];exact hT 1
  · rw [hns 2 1 hc.2.2];exact hT 2
  · rw [hns 0 2 hc.2.1];exact hT 0
lemma QE {z : Z} : ω * z ∈ qU ↔ z ∈ qU := by
 have hω_normSq : W ω = 1 := by rw [← Complex.sq_norm, qk];exact one_pow 2
 have hball : ω * z ∈ ball (0 : Z) 1 ↔ z ∈ ball (0 : Z) 1 := by simp only [mem_ball,dist_zero_right,norm_mul,qk,one_mul]
 have hc := QC
 have hns : ∀ i j : Fin 3, ω * qH i = qH j →
   W (ω * z - qH j) = W (z - qH i) := fun i j hij => by
  rw [← hij, ← mul_sub, normSq_mul, hω_normSq, one_mul]
 constructor
 ·
  rintro ⟨hz, hT⟩
  refine ⟨hball.1 hz, fun i => ?_⟩
  fin_cases i <;> dsimp
  · rw [← hns 0 2 hc.2.1];exact hT 2
  · rw [← hns 1 0 hc.1];exact hT 0
  · rw [← hns 2 1 hc.2.2];exact hT 1
 ·
  rintro ⟨hz, hT⟩
  refine ⟨hball.2 hz, fun i => ?_⟩
  fin_cases i <;> dsimp
  · rw [hns 1 0 hc.1];exact hT 1
  · rw [hns 2 1 hc.2.2];exact hT 2
  · rw [hns 0 2 hc.2.1];exact hT 0
lemma QF :
  T (qH 0) = qH 0 ∧
  T (qH 1) = qH 2 ∧
  T (qH 2) = qH 1 := by
 dsimp [qH, qy];simp only [mul_neg,mul_one,map_neg,conj_ofReal,map_mul,qY,ql,and_self]
def QG (θ : X) : Z := Complex.exp ((θ : Z) * I)
lemma QH (θ : X) : ‖QG θ‖ = 1 := by dsimp [QG];exact Complex.norm_exp_ofReal_mul_I θ
lemma QI (θ : X) : QG θ ∈ closedBall (0 : Z) 1 := by rw [mem_closedBall, dist_zero_right, QH]
lemma QJ (θ : X) : 1 / T (QG θ) = QG θ := by
 have hmul : T (QG θ) * QG θ = 1 := by simp only [conj_mul',QH,ofReal_one,one_pow]
 rw [div_eq_iff (by intro h;rw [h, zero_mul] at hmul;norm_num at hmul), mul_comm]
 exact hmul.symm
lemma QK : QG 0 = 1 := by simp only [QG,ofReal_zero,zero_mul,Complex.exp_zero]
lemma QL : QG (2 * π / 3) = ω := by
 dsimp [QG];rw [Complex.exp_mul_I]
 have hcos : cos (2 * π / 3) = -1 / 2 := by
  rw [show 2 * π / 3 = 2 * (π / 3) by ring, Real.cos_two_mul, cos_pi_div_three]
  ring
 have hsin : sin (2 * π / 3) = Y 3 / 2 := by
  rw [show 2 * π / 3 = 2 * (π / 3) by ring, Real.sin_two_mul,
   sin_pi_div_three, cos_pi_div_three]
  ring
 rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin];apply Complex.ext
 · simp only [ofReal_div,ofReal_neg,ofReal_one,ofReal_ofNat,add_re,div_ofNat_re,neg_re,one_re,mul_re,ofReal_re,I_re,mul_zero,div_ofNat_im,ofReal_im,zero_div,I_im,mul_one,sub_self,add_zero,ω]
 · simp only [ofReal_div,ofReal_neg,ofReal_one,ofReal_ofNat,add_im,div_ofNat_im,neg_im,one_im,neg_zero,zero_div,mul_im,div_ofNat_re,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,add_zero,zero_add,ω]
lemma QM (θ₁ θ₂ : X) : QG (θ₁ + θ₂) = QG θ₁ * QG θ₂ := by dsimp [QG];rw [ofReal_add, add_mul, Complex.exp_add]
lemma QN {θ : X} (hθ0 : 0 < θ) (hθ1 : θ < 2 * π / 3) : QG θ ∈ zy := by
 dsimp [zy, QG];rw [Complex.exp_mul_I]
 have him1 : (Complex.cos (θ : Z) + Complex.sin (θ : Z) * I).im = sin θ := by
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [add_im, mul_im, ofReal_re, ofReal_im,
   I_re, I_im, mul_one, mul_zero, add_zero, zero_add]
 have him2 : ((Complex.cos (θ : Z) + Complex.sin (θ : Z) * I) * (-x7 ^ 2)).im =
   sin (θ + π / 3) := by
  have hnw : -x7 ^ 2 = (⟨1 / 2, Y 3 / 2⟩ : Z) := by
   have h3 : Y 3 ^ 2 = 3 := qc;apply Complex.ext <;> simp only [x7,sq,neg_re,mul_re,neg_sub,one_div,neg_im,mul_im,neg_add_rev] <;> try nlinarith only [h3]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hnw, Real.sin_add, cos_pi_div_three,
   sin_pi_div_three]
  simp only [add_re, add_im, mul_re, mul_im,
   ofReal_re, ofReal_im, I_re, I_im]
  ring
 rw [him1, him2]
 exact ⟨sin_pos_of_pos_of_lt_pi hθ0 (by linarith [pi_pos]),
  sin_pos_of_pos_of_lt_pi (by linarith [pi_pos]) (by linarith)⟩
lemma QO {θ : X} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 2 * π / 3) :
  W (zp (QG θ) - qH 1) = R2 := by
 rcases eq_or_lt_of_le hθ0 with rfl | hθ0'
 · rw [QK, Qu.1];exact kb (by decide)
 ·
  rcases eq_or_lt_of_le hθ1 with rfl | hθ1'
  · rw [QL, Qu.2.2];exact kb (by decide)
  ·
   have huU : QG θ ∈ zy := QN hθ0' hθ1';have hy2u : zo (QG θ) ≠ 0 := z3 (QI θ)
   have hfix : zp (QG θ) = qL 1 (zp (QG θ)) := by
    have h := Qy huU hy2u (by rw [QJ];exact hy2u)
    rwa [QJ] at h
   have hz_ball : zp (QG θ) ∈ ball (0 : Z) 1 := by rw [mem_ball, dist_zero_right];exact Qx (QI θ)
   exact (kc hz_ball).1 hfix.symm
noncomputable def QP (z : Z) : Z := ((tR : Z) - z * T (qy 1)) / (qv : Z)
lemma QQ {z : Z} (hz : W (z - qH 1) = R2) :
  W (QP z) = 1 := by
 have hc : qH 1 = (tR : Z) * qy 1 := rfl
 have hd1 : qy 1 * T (qy 1) = 1 := by simp only [Fin.isValue,mul_conj',qz,ofReal_one,one_pow]
 have hsub : (tR : Z) - z * T (qy 1) = -(z - qH 1) * T (qy 1) := by
  calc (tR : Z) - z * T (qy 1)
      = (tR : Z) * (qy 1 * T (qy 1)) - z * T (qy 1) := by rw [hd1, mul_one]
    _ = -(z - qH 1) * T (qy 1) := by rw [hc];ring
 dsimp [QP]
 rw [hsub, normSq_div, normSq_mul, normSq_neg, hz, normSq_conj,
  qA, mul_one, normSq_ofReal, ← sq, qx, div_self qu.ne']
lemma QR {z : Z} (hz : ‖z‖ < 1) : 0 < (QP z).re := by
 dsimp [QP];rw [div_ofReal_re]
 refine div_pos ?_ qw
 have hre_le : (z * T (qy 1)).re ≤ ‖z‖ := by
  calc (z * T (qy 1)).re ≤ ‖z * T (qy 1)‖ := re_le_norm _
    _ = ‖z‖ * ‖T (qy 1)‖ := norm_mul _ _
    _ = ‖z‖ * 1 := by rw [norm_conj, qz]
    _ = ‖z‖ := mul_one _
 have htR1 : 1 < tR := qs;simp only [sub_re,ofReal_re];linarith
lemma QS : (QP (j5 0)).re = (tR - σ / 2) / qv ∧
  (QP (j5 0)).im = σ * Y 3 / (2 * qv) := by
 dsimp [QP, j5, j4];rw [div_ofReal_re, div_ofReal_im]
 simp only [sub_re, sub_im, mul_re, mul_im,
  ofReal_re, ofReal_im, conj_re, conj_im,
  qD, qE, mul_one, zero_mul, sub_zero, add_zero, zero_sub]
 constructor <;> ring
lemma QT : (QP (j5 2)).re = (tR - σ / 2) / qv ∧
  (QP (j5 2)).im = -(σ * Y 3 / (2 * qv)) := by
 have h3 : Y 3 ^ 2 = 3 := qc;dsimp [QP, j5, j4];rw [div_ofReal_re, div_ofReal_im]
 simp only [sub_re, sub_im, mul_re, mul_im,
  ofReal_re, ofReal_im, conj_re, conj_im,
  qD, qE, ω, zero_mul, sub_zero, add_zero]
 constructor
 ·
  rw [show (tR - (σ * (-1 / 2) * (1 / 2) - σ * (Y 3 / 2) * -(Y 3 / 2))) / qv =
    (tR + σ / 4 - σ * (Y 3 ^ 2) / 4) / qv by ring, h3]
  ring
 · ring
lemma QU (z : Z) :
  (z * T (qH 0 - qH 1)).re =
   tR * (-(3 / 2) * (tR - qv * (QP z).re) - Y 3 / 2 * qv * (QP z).im) ∧
  (z * T (qH 2 - qH 1)).re =
   tR * (-(3 / 2) * (tR - qv * (QP z).re) + Y 3 / 2 * qv * (QP z).im) := by
 have h3 : Y 3 ^ 2 = 3 := qc
 have hz_eq : z = qy 1 * ((tR : Z) - (qv : Z) * QP z) := by
  dsimp [QP]
  have hd1 : qy 1 * T (qy 1) = 1 := by simp only [Fin.isValue,mul_conj',qz,ofReal_one,one_pow]
  rw [mul_div_cancel₀ _ (ofReal_ne_zero.2 qw.ne')]
  calc z = (qy 1 * T (qy 1)) * z := by rw [hd1, one_mul]
    _ = qy 1 * ((tR : Z) - ((tR : Z) - z * T (qy 1))) := by ring
 have hdir0 : qy 1 * T (qy 0 - qy 1) = ⟨-3 / 2, -Y 3 / 2⟩ := by
  apply Complex.ext
  ·
   simp only [Fin.isValue,map_sub,mul_re,qD,one_div,sub_re,conj_re,qB,qE,sub_im,conj_im,qC,neg_zero,sub_neg_eq_add,zero_add];nlinarith only [h3]
  · simp only [Fin.isValue,map_sub,mul_im,qD,one_div,sub_im,conj_im,qC,neg_zero,qE,sub_neg_eq_add,zero_add,sub_re,conj_re,qB];ring
 have hdir2 : qy 1 * T (qy 2 - qy 1) = ⟨-3 / 2, Y 3 / 2⟩ := by
  apply Complex.ext
  ·
   simp only [Fin.isValue,map_sub,mul_re,qD,one_div,sub_re,conj_re,qF,sub_self,mul_zero,qE,sub_im,conj_im,qG,sub_neg_eq_add,zero_sub];nlinarith only [h3]
  · simp only [Fin.isValue,map_sub,mul_im,qD,one_div,sub_im,conj_im,qG,qE,sub_neg_eq_add,sub_re,conj_re,qF,sub_self,mul_zero,add_zero];ring
 constructor
 ·
  nth_rw 1 [hz_eq]
  rw [qH, qH, ← mul_sub, map_mul, conj_ofReal,
   show qy 1 * ((tR : Z) - (qv : Z) * QP z) * ((tR : Z) * T (qy 0 - qy 1)) =
    (tR : Z) * ((tR : Z) - (qv : Z) * QP z) * (qy 1 * T (qy 0 - qy 1)) by ring,
   hdir0]
  simp only [mul_re, mul_im, sub_re, sub_im,
   ofReal_re, ofReal_im];ring
 ·
  nth_rw 1 [hz_eq]
  rw [qH, qH, ← mul_sub, map_mul, conj_ofReal,
   show qy 1 * ((tR : Z) - (qv : Z) * QP z) * ((tR : Z) * T (qy 2 - qy 1)) =
    (tR : Z) * ((tR : Z) - (qv : Z) * QP z) * (qy 1 * T (qy 2 - qy 1)) by ring,
   hdir2]
  simp only [mul_re, mul_im, sub_re, sub_im,
   ofReal_re, ofReal_im];ring
lemma QV (z : Z) (i : Fin 3) :
  W (z - qH i) - W (z - qH 1) =
   -2 * (z * T (qH i - qH 1)).re := by
 have hci : W (qH i) = W (qH 1) := by simp only [qI,Fin.isValue]
 simp only [normSq_apply, sub_re, sub_im, mul_re,
  conj_re, conj_im, map_sub] at hci ⊢
 nlinarith only [hci]
lemma QW {z : Z} (hz1 : W (z - qH 1) = R2)
  (hre : 0 < (QP z).re) (him : |(QP z).im| ≤ σ * Y 3 / (2 * qv)) :
  R2 ≤ W (z - qH 0) ∧ R2 ≤ W (z - qH 2) := by
 have h3 : Y 3 ^ 2 = 3 := qc;have h3p : (0 : X) < Y 3 := qd;let a := (QP z).re;let b := (QP z).im;let a0 := (tR - σ / 2) / qv;let b0 := σ * Y 3 / (2 * qv)
 have hsq : a ^ 2 + b ^ 2 = 1 := by
  have := QQ hz1;rwa [normSq_apply, ← sq, ← sq] at this
 have hsq0 : a0 ^ 2 + b0 ^ 2 = 1 := by
  have := QQ (kb (i := 1) (k := 0) (by decide))
  rw [normSq_apply, ← sq, ← sq, QS.1, QS.2] at this;exact this
 have ha0_pos : 0 < a0 := by
  dsimp [a0];refine div_pos ?_ qw;have ht1 : 1 < tR := qs;linarith only [qp, ht1]
 have ha_ge : a0 ≤ a := by
  have hb_sq : b ^ 2 ≤ b0 ^ 2 := by rw [← sq_abs b];exact sq_le_sq' (by linarith only [abs_nonneg b, him]) him
  have : a0 ^ 2 ≤ a ^ 2 := by linarith only [hsq, hsq0, hb_sq]
  exact le_of_not_gt fun hlt => by nlinarith only [this, mul_pos (show 0 < a + a0 by linarith only [hre, ha0_pos]) (sub_pos.2 hlt)]
 have ha0_b0 : Y 3 * a0 - 3 * b0 > 0 := by
  have hdiff : Y 3 * a0 - 3 * b0 = Y 3 * (tR - 2 * σ) / qv := by dsimp [a0, b0];ring
  rw [hdiff]
  refine div_pos (mul_pos h3p ?_) qw
  have hsig : tR - 2 * σ = (1 - σ ^ 2) / σ := by dsimp [tR];field_simp [qn.ne'];ring
  rw [hsig];exact div_pos (by nlinarith only [qn, qp]) qn
 have hineq : 3 * a + Y 3 * |b| ≤ 3 * a0 + Y 3 * b0 := by
  have hident : (a + a0) * ((3 * a0 + Y 3 * b0) - (3 * a + Y 3 * |b|)) =
    (b0 - |b|) * (Y 3 * (a + a0) - 3 * (b0 + |b|)) := by
   have hbb : |b| ^ 2 = b ^ 2 := sq_abs b;nlinarith only [hsq, hsq0, hbb, h3]
  have hfac2 : 0 ≤ Y 3 * (a + a0) - 3 * (b0 + |b|) := by
   have hrt_le : Y 3 * a0 ≤ Y 3 * a := mul_le_mul_of_nonneg_left ha_ge h3p.le;linarith only [hrt_le, him, ha0_b0]
  have hprod_nn : 0 ≤ (b0 - |b|) * (Y 3 * (a + a0) - 3 * (b0 + |b|)) :=
   mul_nonneg (by linarith only [him]) hfac2
  rw [← hident] at hprod_nn;nlinarith only [hre, ha0_pos, hprod_nn]
 have hst : σ * tR = σ ^ 2 + 1 := by dsimp [tR];field_simp [qn.ne']
 have hrad_c : 3 * qv * a0 + Y 3 * qv * b0 = 3 * tR := by
  dsimp [a0, b0];field_simp [qw.ne'];rw [h3];ring
 have hkey_abs : Y 3 * qv * |b| ≤ 3 * (tR - qv * a) := by
  have hm : qv * (3 * a + Y 3 * |b|) ≤ qv * (3 * a0 + Y 3 * b0) :=
   mul_le_mul_of_nonneg_left hineq qw.le
  linarith [hrad_c]
 obtain ⟨hre0, hre2⟩ := QU z;have hb_pos := le_abs_self b;have hb_neg := neg_le_abs b
 have h0_le : (z * T (qH 0 - qH 1)).re ≤ 0 := by
  rw [hre0];exact mul_nonpos_of_nonneg_of_nonpos qq.le
   (by linarith [hkey_abs, mul_le_mul_of_nonneg_left hb_neg (mul_nonneg h3p.le qw.le)])
 have h2_le : (z * T (qH 2 - qH 1)).re ≤ 0 := by
  rw [hre2];exact mul_nonpos_of_nonneg_of_nonpos qq.le
   (by linarith [hkey_abs, mul_le_mul_of_nonneg_left hb_pos (mul_nonneg h3p.le qw.le)])
 exact ⟨by linarith [QV z 0, hz1, h0_le], by linarith [QV z 2, hz1, h2_le]⟩
lemma QX :
  InjOn (fun θ : X => (QP (zp (QG θ))).im) (Icc 0 (2 * π / 3)) := by
 let s : X → X := fun θ => (QP (zp (QG θ))).im
 have hs_cont : ContinuousOn s (Icc 0 (2 * π / 3)) := by
  have hu : Continuous (QG : X → Z) := (continuous_ofReal.mul continuous_const).cexp
  have hz : ContinuousOn (fun θ : X => zp (QG θ)) (Icc 0 (2 * π / 3)) :=
   Qm.comp hu.continuousOn fun θ _ => QI θ
  have hw : Continuous (QP : Z → Z) :=
   (continuous_const.sub (continuous_id.mul continuous_const)).div_const _
  exact Complex.continuous_im.comp_continuousOn (hw.continuousOn.comp hz fun _ _ => mem_univ _)
 have hs_deriv : ∀ θ ∈ Ioo 0 (2 * π / 3),
   ∃ s' : X, HasDerivAt s s' θ ∧ s' ≠ 0 := by
  intro θ hθ;have huU : QG θ ∈ zy := QN hθ.1 hθ.2;have hy2 : zo (QG θ) ≠ 0 := z3 (QI θ)
  have hzd : HasDerivAt zp (deriv zp (QG θ)) (QG θ) := by
   have := Qp (Or.inr huU) hy2;exact this.congr_deriv this.deriv.symm
  have hud : HasDerivAt QG (I * QG θ) θ := by
   have hl : HasDerivAt (fun t : X => (t : Z) * I) (1 * I) θ :=
    (Complex.ofRealCLM.hasDerivAt).mul_const I
   refine hl.cexp.congr_deriv ?_
   simp only [mul_comm,mul_one,QG]
  have hcomp : HasDerivAt (fun t : X => zp (QG t)) (I * QG θ * deriv zp (QG θ)) θ :=
   (hzd.scomp θ hud).congr_deriv (by ring)
  have hw_deriv : HasDerivAt (fun t : X => QP (zp (QG t)))
    (-(I * QG θ * deriv zp (QG θ) * T (qy 1)) / (qv : Z)) θ := by
   have hsub := ((hasDerivAt_const θ (tR : Z)).sub (hcomp.mul_const (T (qy 1)))).div_const (qv : Z)
   refine hsub.congr_deriv ?_
   simp only [Fin.isValue,zero_sub]
  let w' : Z := -(I * QG θ * deriv zp (QG θ) * T (qy 1)) / (qv : Z)
  have hw'_ne : w' ≠ 0 := by
   have h1 : I ≠ 0 := I_ne_zero;have h2 : QG θ ≠ 0 := Complex.exp_ne_zero _;have h3 : deriv zp (QG θ) ≠ 0 := Qq (Or.inr huU) hy2
   have h4 : T (qy 1) ≠ 0 := by intro h;have := qz 1;rw [← norm_conj, h, norm_zero] at this;exact one_ne_zero this.symm
   have h5 : (qv : Z) ≠ 0 := ofReal_ne_zero.2 qw.ne';exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4)) h5
  have hre_d : HasDerivAt (fun t : X => (QP (zp (QG t))).re) w'.re θ :=
   reCLM.hasFDerivAt.comp_hasDerivAt θ hw_deriv
  have him_d : HasDerivAt s w'.im θ :=
   imCLM.hasFDerivAt.comp_hasDerivAt θ hw_deriv
  have hconst_sq : ∀ᶠ t in 𝓝 θ,
    (QP (zp (QG t))).re ^ 2 + (QP (zp (QG t))).im ^ 2 = 1 := by
   filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
   have := QQ (QO ht.1.le ht.2.le);rwa [normSq_apply, ← sq, ← sq] at this
  have hd0 : HasDerivAt (fun t : X => (QP (zp (QG t))).re ^ 2 + (QP (zp (QG t))).im ^ 2) 0 θ :=
   (hasDerivAt_const θ (1 : X)).congr_of_eventuallyEq hconst_sq
  have hsum_d : HasDerivAt (fun t : X => (QP (zp (QG t))).re ^ 2 + (QP (zp (QG t))).im ^ 2)
    (2 * (QP (zp (QG θ))).re * w'.re + 2 * (QP (zp (QG θ))).im * w'.im) θ := by
   have hre2 : HasDerivAt (fun t : X => (QP (zp (QG t))).re ^ 2)
     (2 * (QP (zp (QG θ))).re * w'.re) θ :=
    (hre_d.pow 2).congr_deriv (by norm_num)
   have him2 : HasDerivAt (fun t : X => (QP (zp (QG t))).im ^ 2)
     (2 * (QP (zp (QG θ))).im * w'.im) θ :=
    (him_d.pow 2).congr_deriv (by dsimp [s];norm_num)
   exact hre2.add him2
  have hrel : 2 * (QP (zp (QG θ))).re * w'.re + 2 * (QP (zp (QG θ))).im * w'.im = 0 :=
   hsum_d.unique hd0
  have him_ne : w'.im ≠ 0 := by
   intro him0;rw [him0, mul_zero, add_zero] at hrel;have hre_pos := QR (Qx (QI θ))
   have hre0 : w'.re = 0 := by
    rcases mul_eq_zero.1 hrel with h2 | hre0
    · exfalso;linarith
    · exact hre0
   exact hw'_ne (Complex.ext hre0 him0)
  exact ⟨w'.im, him_d, him_ne⟩
 intro θ₁ hθ₁ θ₂ hθ₂ heq
 rcases lt_trichotomy θ₁ θ₂ with hlt | rfl | hgt
 ·
  exfalso;obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_zero hlt (hs_cont.mono (Icc_subset_Icc hθ₁.1 hθ₂.2)) heq;obtain ⟨s', hs', hs'0⟩ := hs_deriv ξ ⟨lt_of_le_of_lt hθ₁.1 hξ.1, lt_of_lt_of_le hξ.2 hθ₂.2⟩;exact hs'0 (hs'.deriv.symm.trans hξd)
 · rfl
 ·
  exfalso;obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_zero hgt (hs_cont.mono (Icc_subset_Icc hθ₂.1 hθ₁.2)) heq.symm;obtain ⟨s', hs', hs'0⟩ := hs_deriv ξ ⟨lt_of_le_of_lt hθ₂.1 hξ.1, lt_of_lt_of_le hξ.2 hθ₁.2⟩;exact hs'0 (hs'.deriv.symm.trans hξd)
lemma QY {θ : X} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 2 * π / 3) :
  zp (QG θ) ∈ T0 \ qU := by
 let s : X → X := fun t => (QP (zp (QG t))).im
 have hs_cont : ContinuousOn s (Icc 0 (2 * π / 3)) := by
  have hu : Continuous (QG : X → Z) := (continuous_ofReal.mul continuous_const).cexp
  have hz : ContinuousOn (fun t : X => zp (QG t)) (Icc 0 (2 * π / 3)) :=
   Qm.comp hu.continuousOn fun t _ => QI t
  have hw : Continuous (QP : Z → Z) :=
   (continuous_const.sub (continuous_id.mul continuous_const)).div_const _
  exact Complex.continuous_im.comp_continuousOn (hw.continuousOn.comp hz fun _ _ => mem_univ _)
 have hs0 : s 0 = σ * Y 3 / (2 * qv) := by dsimp [s];rw [QK, Qu.1];exact QS.2
 have hs1 : s (2 * π / 3) = -(σ * Y 3 / (2 * qv)) := by dsimp [s];rw [QL, Qu.2.2];exact QT.2
 have hs_le_0 : s θ ≤ s 0 := by
  by_contra hgt
  rw [not_le] at hgt
  have hmem : s 0 ∈ Icc (s (2 * π / 3)) (s θ) := by
   have hb0 : 0 < σ * Y 3 / (2 * qv) := by positivity [qn, qw]
   rw [hs0, hs1];constructor <;> linarith [hb0]
  obtain ⟨t, ht, hst⟩ := intermediate_value_Icc' hθ1 (hs_cont.mono (Icc_subset_Icc hθ0 le_rfl)) hmem
  have h0_eq : 0 = t := QX ⟨le_rfl, by positivity [pi_pos]⟩
   ⟨hθ0.trans ht.1,ht.2⟩ hst.symm
  have hθ_eq : θ = 0 := by linarith [h0_eq, ht.1, hθ0]
  rw [hθ_eq] at hgt;linarith
 have hs_ge_1 : s (2 * π / 3) ≤ s θ := by
  by_contra hlt
  rw [not_le] at hlt
  have hmem : s (2 * π / 3) ∈ Icc (s θ) (s 0) := by
   have hb0 : 0 < σ * Y 3 / (2 * qv) := by positivity [qn, qw]
   rw [hs0, hs1];constructor <;> linarith [hb0]
  obtain ⟨t, ht, hst⟩ := intermediate_value_Icc' hθ0 (hs_cont.mono (Icc_subset_Icc le_rfl hθ1)) hmem;have h1_eq : 2 * π / 3 = t := QX
   ⟨by positivity [pi_pos],le_rfl⟩ ⟨ht.1,ht.2.trans hθ1⟩ hst.symm
  have hθ_eq : θ = 2 * π / 3 := by linarith [h1_eq, ht.2, hθ1]
  rw [hθ_eq] at hlt;linarith
 have habs : |s θ| ≤ σ * Y 3 / (2 * qv) := abs_le.2 ⟨by linarith [hs1], by linarith [hs0]⟩
 have hns1 : W (zp (QG θ) - qH 1) = R2 := QO hθ0 hθ1;have hre_pos := QR (Qx (QI θ));obtain ⟨h0, h2⟩ := QW hns1 hre_pos habs
 have hball : zp (QG θ) ∈ ball (0 : Z) 1 := by rw [mem_ball, dist_zero_right];exact Qx (QI θ)
 refine ⟨⟨hball, fun i => ?_⟩, fun hint => ?_⟩
 ·
  fin_cases i <;> dsimp
  · exact h0
  · exact hns1.ge
  · exact h2
 · exact (hint.2 1).ne hns1.symm
lemma QZ :
  zp '' sphere (0 : Z) 1 ⊆ T0 \ qU := by
 rintro _ ⟨u, hu, rfl⟩;rw [mem_sphere_zero_iff_norm] at hu
 have hu0 : u ≠ 0 := by intro h;rw [h, norm_zero] at hu;exact one_ne_zero hu.symm
 let θ : X := if 0 ≤ Complex.arg u then Complex.arg u else Complex.arg u + 2 * π
 have hθ0 : 0 ≤ θ := by
  dsimp [θ];split_ifs with h
  · exact h
  · linarith [neg_pi_lt_arg u]
 have hθ2π : θ < 2 * π := by
  dsimp [θ];split_ifs with h
  · linarith [arg_le_pi u, pi_pos]
  · linarith
 have hu_eq : u = QG θ := by
  have hbase := norm_mul_exp_arg_mul_I u;rw [hu] at hbase;simp only [ofReal_one,one_mul] at hbase;dsimp [θ, QG];split_ifs
  · exact hbase.symm
  ·
   rw [ofReal_add, add_mul, Complex.exp_add]
   have h2pi : Complex.exp (((2 * π : X) : Z) * I) = 1 := by push_cast;rw [exp_two_pi_mul_I]
   rw [h2pi, mul_one];exact hbase.symm
 rw [hu_eq]
 rcases le_total θ (2 * π / 3) with h1 | h1
 · exact QY hθ0 h1
 ·
  rcases le_total θ (4 * π / 3) with h2 | h2
  ·
   have hsub : θ = 2 * π / 3 + (θ - 2 * π / 3) := by ring
   rw [hsub, QM, QL, Qe]
   have hm := QY (θ := θ - 2 * π / 3) (by linarith) (by linarith)
   exact ⟨QD.2 hm.1, fun h => hm.2 (QE.1 h)⟩
  ·
   have hsub : θ = 2 * π / 3 + (2 * π / 3 + (θ - 4 * π / 3)) := by ring
   rw [hsub, QM, QM, QL, Qe, Qe]
   have hm := QY (θ := θ - 4 * π / 3) (by linarith) (by linarith)
   exact ⟨QD.2 (QD.2 hm.1),
    fun h => hm.2 (QE.1 (QE.1 h))⟩
lemma Q0 :
  0 < Y 3 * ((tR - σ / 2) / qv) - 3 * (σ * Y 3 / (2 * qv)) - (Y 3 - Y 2) := by
 have h3 : Y 3 ^ 2 = 3 := qc;have h3p : (0 : X) < Y 3 := qd
 have hts : tR - 2 * σ = (1 - σ ^ 2) / σ := by dsimp [tR];field_simp [qn.ne'];ring
 have ha0_b0 : Y 3 * ((tR - σ / 2) / qv) - 3 * (σ * Y 3 / (2 * qv)) =
   Y 3 * (1 - σ ^ 2) / (σ * qv) := by
  calc Y 3 * ((tR - σ / 2) / qv) - 3 * (σ * Y 3 / (2 * qv))
      = Y 3 * (tR - 2 * σ) / qv := by ring
    _ = Y 3 * ((1 - σ ^ 2) / σ) / qv := by rw [hts]
    _ = Y 3 * (1 - σ ^ 2) / (σ * qv) := by ring
 have hsub_val : (Y 3 * ((tR - σ / 2) / qv) - 3 * (σ * Y 3 / (2 * qv))) ^ 2 =
   3 * (1 - σ ^ 2) ^ 2 / (σ ^ 2 * R2) := by
  rw [ha0_b0, div_pow, mul_pow, h3, mul_pow, qx]
 have hσ2 : σ ^ 2 * R2 = 3 / 2 := by rw [qo, qt];field_simp;nlinarith only [h3]
 have h1s2 : (1 - σ ^ 2) ^ 2 = (6 - 3 * Y 3) / 2 := by
  rw [qo]
  have hexp : (1 - (Y 3 - 1) / 2) ^ 2 = (9 - 6 * Y 3 + Y 3 ^ 2) / 4 := by ring
  rw [hexp, h3];ring
 have hsq_eq : (Y 3 * ((tR - σ / 2) / qv) - 3 * (σ * Y 3 / (2 * qv))) ^ 2 = 6 - 3 * Y 3 := by rw [hsub_val, hσ2, h1s2];ring
 have hrt3_bd : (173 / 100 : X) < Y 3 ∧ Y 3 < 174 / 100 :=
  ⟨by rw [lt_sqrt (by norm_num)];norm_num,by rw [Real.sqrt_lt' (by norm_num)];norm_num⟩
 have hrt2_bd : (141 / 100 : X) < Y 2 := by rw [lt_sqrt (by norm_num)];norm_num
 have hgap_sq : (Y 3 - Y 2) ^ 2 <
   (Y 3 * ((tR - σ / 2) / qv) - 3 * (σ * Y 3 / (2 * qv))) ^ 2 := by
  rw [hsq_eq]
  have h1 : Y 3 - Y 2 < 33 / 100 := by linarith only [hrt3_bd.2, hrt2_bd]
  have hnn : 0 ≤ Y 3 - Y 2 := sub_nonneg.2 (sqrt_le_sqrt (by norm_num))
  nlinarith only [hrt3_bd.2, h1, hnn]
 have hpos_lhs : 0 < Y 3 * ((tR - σ / 2) / qv) - 3 * (σ * Y 3 / (2 * qv)) := by
  rw [ha0_b0]
  exact div_pos (mul_pos h3p (by nlinarith only [qn, qp])) (mul_pos qn qw)
 nlinarith only [hgap_sq, hpos_lhs]
lemma Q1 {x : Z} (hx : x ∈ T0) (hx1 : W (x - qH 1) = R2) :
  ∃ θ ∈ Icc 0 (2 * π / 3), zp (QG θ) = x := by
 have h3 : Y 3 ^ 2 = 3 := qc;have h3p : (0 : X) < Y 3 := qd;obtain ⟨a, ha_def⟩ : ∃ a : X, a = (QP x).re := ⟨_, rfl⟩;obtain ⟨b, hb_def⟩ : ∃ b : X, b = (QP x).im := ⟨_, rfl⟩;obtain ⟨a0, ha0_def⟩ : ∃ a0 : X, a0 = (tR - σ / 2) / qv := ⟨_, rfl⟩;obtain ⟨b0, hb0_def⟩ : ∃ b0 : X, b0 = σ * Y 3 / (2 * qv) := ⟨_, rfl⟩
 have hsq : a ^ 2 + b ^ 2 = 1 := by
  have := QQ hx1;rwa [normSq_apply, ← sq, ← sq, ← ha_def, ← hb_def] at this
 have hsq0 : a0 ^ 2 + b0 ^ 2 = 1 := by
  have := QQ (kb (i := 1) (k := 0) (by decide))
  rw [normSq_apply, ← sq, ← sq, QS.1, QS.2, ← ha0_def, ← hb0_def] at this;exact this
 have hx_ball : ‖x‖ < 1 := by rw [← mem_ball_zero_iff];exact hx.1
 have ha_pos : 0 < a := by rw [ha_def];exact QR hx_ball
 have ha_ge_min : (tR - σ) / qv ≤ a := by
  rw [ha_def];dsimp [QP];rw [div_ofReal_re]
  refine div_le_div_of_nonneg_right ?_ qw.le
  have hre_le : (x * T (qy 1)).re ≤ σ := by
   calc (x * T (qy 1)).re ≤ ‖x * T (qy 1)‖ := re_le_norm _
     _ = ‖x‖ * ‖T (qy 1)‖ := norm_mul _ _
     _ = ‖x‖ * 1 := by rw [norm_conj, qz]
     _ ≤ σ := by rw [mul_one];exact jT hx
  simp only [sub_re,ofReal_re];linarith
 have hmin_sq : ((tR - σ) / qv) ^ 2 = 2 / 3 := by
  have hts : tR - σ = 1 / σ := by dsimp [tR];ring
  rw [hts, div_pow, div_pow, one_pow, qo, qx, qt]
  have h13 : (0 : X) < 1 + Y 3 := by positivity
  have h3m1 : (0 : X) < Y 3 - 1 := by nlinarith only [h3, qd]
  field_simp [h13.ne', h3m1.ne'];nlinarith only [h3]
 have hmin_pos : 0 < (tR - σ) / qv := by
  have hts : tR - σ = 1 / σ := by dsimp [tR];ring
  rw [hts];exact div_pos (one_div_pos.2 qn) qw
 have ha_sq_ge : 2 / 3 ≤ a ^ 2 := by rw [← hmin_sq];exact sq_le_sq' (by linarith) ha_ge_min
 have hb_sq_le : b ^ 2 ≤ 1 / 3 := by linarith
 have habs_le_rt : |b| ≤ 1 / Y 3 := by
  have hrt_sq : (1 / Y 3) ^ 2 = 1 / 3 := by rw [div_pow, one_pow, h3]
  have hsq_le : |b| ^ 2 ≤ (1 / Y 3) ^ 2 := by rw [sq_abs, hrt_sq];exact hb_sq_le
  exact (abs_le_of_sq_le_sq' hsq_le (by positivity)).2
 have hrad_c : 3 * qv * a0 + Y 3 * qv * b0 = 3 * tR := by
  rw [ha0_def, hb0_def]
  rw [show 3 * qv * ((tR - σ / 2) / qv) + Y 3 * qv * (σ * Y 3 / (2 * qv)) =
    3 * tR - 3 / 2 * σ + σ * Y 3 ^ 2 / 2 by field_simp [qw.ne'], h3];ring
 have hre0_le : (x * T (qH 0 - qH 1)).re ≤ 0 := by linarith [QV x 0, hx.2 0, hx1]
 have hre2_le : (x * T (qH 2 - qH 1)).re ≤ 0 := by linarith [QV x 2, hx.2 2, hx1]
 obtain ⟨hre0, hre2⟩ := QU x
 have h3ab : 3 * a + Y 3 * |b| ≤ 3 * a0 + Y 3 * b0 := by
  rw [← ha_def, ← hb_def] at hre0 hre2
  have h1 : Y 3 * qv * (-b) ≤ 3 * (tR - qv * a) := by
   rw [hre0] at hre0_le;have := nonpos_of_mul_nonpos_right hre0_le qq;linarith
  have h2 : Y 3 * qv * b ≤ 3 * (tR - qv * a) := by
   rw [hre2] at hre2_le;have := nonpos_of_mul_nonpos_right hre2_le qq;linarith
  have hm : Y 3 * qv * |b| ≤ 3 * (tR - qv * a) := by
   rcases le_total 0 b with hb | hb
   · rwa [abs_of_nonneg hb]
   · rwa [abs_of_nonpos hb]
  have hmul_rad : qv * (3 * a + Y 3 * |b|) ≤ qv * (3 * a0 + Y 3 * b0) := by linarith [hrad_c]
  exact le_of_mul_le_mul_left hmul_rad qw
 have ha0_pos : 0 < a0 := by
  rw [ha0_def];refine div_pos ?_ qw;have ht1 : 1 < tR := qs;linarith [qp]
 have hb_le_b0 : |b| ≤ b0 := by
  by_contra hgt
  rw [not_le] at hgt
  have hb0_nn : 0 ≤ b0 := by
   have : 0 ≤ σ * Y 3 / (2 * qv) := by positivity [qn, qw]
   exact hb0_def ▸ this
  have hb_sq_gt : b0 ^ 2 < b ^ 2 := by rw [← sq_abs b];exact sq_lt_sq' (by linarith) hgt
  have ha_sq_lt : a ^ 2 < a0 ^ 2 := by linarith [hsq, hsq0, hb_sq_gt]
  have ha_lt_a0 : a < a0 := by
   by_contra hle
   rw [not_lt] at hle
   have : a0 ^ 2 ≤ a ^ 2 := sq_le_sq' (by linarith [ha0_pos]) hle
   linarith
  have hident : (a + a0) * ((3 * a + Y 3 * |b|) - (3 * a0 + Y 3 * b0)) =
    (|b| - b0) * (Y 3 * (a + a0) - 3 * (|b| + b0)) := by
   have hdiff_sq : a ^ 2 - a0 ^ 2 = -((|b| - b0) * (|b| + b0)) := by
    have h1 : a ^ 2 + |b| ^ 2 = a0 ^ 2 + b0 ^ 2 := by rw [sq_abs b, hsq, hsq0]
    linear_combination h1
   linear_combination 3 * hdiff_sq
  have hnum_gt : 0 < Y 3 * a0 - 3 * b0 - (Y 3 - Y 2) := by rw [ha0_def, hb0_def];exact Q0
  have hmin_part : Y 3 * a - 3 * |b| ≥ -(Y 3 - Y 2) := by
   have ha_r2 : Y (2 / 3) ≤ a := by rw [← Real.sqrt_sq ha_pos.le];exact sqrt_le_sqrt ha_sq_ge
   have hrt3_a : Y 2 ≤ Y 3 * a := by
    have hmul : Y 3 * Y (2 / 3) = Y 2 := by rw [← sqrt_mul (by norm_num)];norm_num
    calc Y 2 = Y 3 * Y (2 / 3) := hmul.symm
      _ ≤ Y 3 * a := mul_le_mul_of_nonneg_left ha_r2 h3p.le
   have h3b_le : 3 * |b| ≤ Y 3 := by
    calc 3 * |b| ≤ 3 * (1 / Y 3) := by linarith only [habs_le_rt]
      _ = Y 3 := by field_simp [h3p.ne'];exact h3.symm
   linarith only [hrt3_a, h3b_le]
  have hfac_pos : 0 < Y 3 * (a + a0) - 3 * (|b| + b0) := by
   have : Y 3 * (a + a0) - 3 * (|b| + b0) =
     (Y 3 * a0 - 3 * b0) + (Y 3 * a - 3 * |b|) := by ring
   linarith only [this, hnum_gt, hmin_part]
  have hprod_pos : 0 < (a + a0) * ((3 * a + Y 3 * |b|) - (3 * a0 + Y 3 * b0)) := by rw [hident];exact mul_pos (sub_pos.2 hgt) hfac_pos
  nlinarith only [ha_pos, ha0_pos, h3ab, hprod_pos]
 let s : X → X := fun t => (QP (zp (QG t))).im
 have hs_cont : ContinuousOn s (Icc 0 (2 * π / 3)) := by
  have hu : Continuous (QG : X → Z) := (continuous_ofReal.mul continuous_const).cexp
  have hz : ContinuousOn (fun t : X => zp (QG t)) (Icc 0 (2 * π / 3)) :=
   Qm.comp hu.continuousOn fun t _ => QI t
  have hw : Continuous (QP : Z → Z) :=
   (continuous_const.sub (continuous_id.mul continuous_const)).div_const _
  exact Complex.continuous_im.comp_continuousOn (hw.continuousOn.comp hz fun _ _ => mem_univ _)
 have hs0 : s 0 = b0 := by dsimp [s];rw [hb0_def, QK, Qu.1];exact QS.2
 have hs1 : s (2 * π / 3) = -b0 := by dsimp [s];rw [hb0_def, QL, Qu.2.2];exact QT.2
 have hb_mem : b ∈ Icc (s (2 * π / 3)) (s 0) := by rw [hs0, hs1];exact abs_le.1 hb_le_b0
 obtain ⟨θ, hθ, hθ_eq⟩ := intermediate_value_Icc' (by positivity [pi_pos]) hs_cont hb_mem
 refine ⟨θ, hθ, ?_⟩
 have hwa : QP (zp (QG θ)) = QP x := by
  have hns_θ : W (QP (zp (QG θ))) = 1 :=
   QQ (QO hθ.1 hθ.2)
  have hre_θ : 0 < (QP (zp (QG θ))).re :=
   QR (Qx (QI θ))
  have hre_sq : (QP (zp (QG θ))).re ^ 2 = a ^ 2 := by
   have h1 : (QP (zp (QG θ))).re ^ 2 + (QP (zp (QG θ))).im ^ 2 = 1 := by rwa [normSq_apply, ← sq, ← sq] at hns_θ
   change s θ = b at hθ_eq;dsimp [s] at hθ_eq;rw [hθ_eq] at h1;linarith only [hsq, h1]
  have hre_eq : (QP (zp (QG θ))).re = a := by rw [← Real.sqrt_sq hre_θ.le, ← Real.sqrt_sq ha_pos.le, hre_sq]
  exact Complex.ext (hre_eq.trans ha_def) (hθ_eq.trans hb_def)
 dsimp [QP] at hwa;have h1 := congr_arg (fun z => (tR : Z) - (qv : Z) * z) hwa
 have hmul : (tR : Z) - (qv : Z) * (((tR : Z) - zp (QG θ) * T (qy 1)) / (qv : Z)) =
   zp (QG θ) * T (qy 1) := by field_simp [qw.ne'];ring
 have hmul2 : (tR : Z) - (qv : Z) * (((tR : Z) - x * T (qy 1)) / (qv : Z)) =
   x * T (qy 1) := by field_simp [qw.ne'];ring
 rw [hmul, hmul2] at h1
 have hd1_ne : T (qy 1) ≠ 0 := by intro h;have := qz 1;rw [← norm_conj, h, norm_zero] at this;exact one_ne_zero this.symm
 exact mul_right_cancel₀ hd1_ne h1
lemma Q2 {x : Z} (hx : x ∈ qU) {t : X} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
  (t : Z) * x ∈ qU := by
 rcases eq_or_lt_of_le ht1 with rfl | ht1'
 · simpa using hx
 refine ⟨?_, fun i => ?_⟩
 ·
  rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_of_nonneg ht0]
  have hx1 : ‖x‖ < 1 := by rw [← mem_ball_zero_iff];exact hx.1
  exact (mul_le_of_le_one_left (norm_nonneg _) ht1'.le).trans_lt hx1
 ·
  have hnsx : W x < 1 := qm hx.1;have hxi : R2 < W (x - qH i) := hx.2 i
  have hre_id : W (x - qH i) =
    W x + tR ^ 2 - 2 * (x * T (qH i)).re := by
   rw [← qI i]
   simp only [normSq_apply, sub_re, sub_im, mul_re,
    conj_re, conj_im];ring
  have hre_bd : 2 * (x * T (qH i)).re < W x + 1 := by dsimp [R2] at hxi;linarith
  have hre_t : W ((t : Z) * x - qH i) =
    t ^ 2 * W x + tR ^ 2 - 2 * t * (x * T (qH i)).re := by
   have hc := qI i
   simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im,
    ofReal_re, ofReal_im, conj_re, conj_im, zero_mul, sub_zero, add_zero] at hc ⊢
   nlinarith only [hc]
  have hgap : 0 < (1 - t) * (1 - t * W x) := by
   have h1 : 0 < 1 - t := sub_pos.2 ht1'
   have h2 : 0 < 1 - t * W x := by nlinarith only [normSq_nonneg x, hnsx, ht0, ht1']
   exact mul_pos h1 h2
  dsimp [R2];rw [hre_t];nlinarith only [hre_bd, hgap, ht0]
lemma Q3 : IsPreconnected qU := by
 refine (IsPathConnected.isConnected ⟨0, qV, fun x hx => ?_⟩).isPreconnected
 refine ⟨⟨⟨fun t => (t : Z) * x, (continuous_ofReal.comp continuous_subtype_val).mul continuous_const⟩,
  by simp only [Icc.coe_zero,ofReal_zero,zero_mul], by simp only [Icc.coe_one,ofReal_one,one_mul]⟩, fun t => Q2 hx t.2.1 t.2.2⟩
lemma Q4 : IsPreconnected T0ᶜ := by
 have h2_mem : (2 : Z) ∈ T0ᶜ := fun h => by
  have := jT h;simp only [Complex.norm_ofNat] at this;linarith [qp]
 refine (IsPathConnected.isConnected ⟨2, h2_mem, fun x hx => ?_⟩).isPreconnected
 have h_ray_path : ∀ y : Z, 1 ≤ ‖y‖ → JoinedIn T0ᶜ y (2 : Z) := by
  intro y hy;let θ : X := Complex.arg y;let y2 : Z := (2 : Z) * QG θ;have hy_eq : y = ((‖y‖ : X) : Z) * QG θ := (norm_mul_exp_arg_mul_I y).symm
  let p1 : Path y y2 :=
   ⟨⟨fun t => ((((1 - (t : X)) * ‖y‖ + (t : X) * 2 : X)) : Z) * QG θ,(continuous_ofReal.comp (((continuous_const.sub continuous_subtype_val).mul continuous_const).add (continuous_subtype_val.mul continuous_const))).mul continuous_const⟩,
    by dsimp;simp only [sub_zero,one_mul,zero_mul,add_zero];exact hy_eq.symm, by dsimp;simp only [sub_self,zero_mul,one_mul,zero_add,ofReal_ofNat,y2]⟩
  have hp1 : ∀ t : unitInterval, p1 t ∈ T0ᶜ := fun t ht => by
   have hnorm : 1 ≤ ‖p1 t‖ := by
    dsimp [p1]
    rw [norm_mul, QH, mul_one, Complex.norm_of_nonneg (by nlinarith only [t.2.1, t.2.2, hy])]
    nlinarith only [t.2.1, t.2.2, hy]
   have := jT ht;linarith [qp]
  have hp2_mem : ∀ z : Z, ‖z‖ = 2 → z ∈ T0ᶜ := fun z hz hT => by
   have := jT hT;linarith [qp]
  let p2 : Path y2 (2 : Z) :=
   ⟨⟨fun t => (2 : Z) * QG ((1 - (t : X)) * θ),continuous_const.mul (Complex.continuous_exp.comp ((continuous_ofReal.comp ((continuous_const.sub continuous_subtype_val).mul continuous_const)).mul continuous_const))⟩,
    by dsimp;simp only [sub_zero,one_mul,y2], by dsimp;simp only [QG,sub_self,zero_mul,ofReal_zero,Complex.exp_zero,mul_one]⟩
  have hp2 : ∀ t : unitInterval, p2 t ∈ T0ᶜ := fun t =>
   hp2_mem _ (by dsimp [p2];rw [norm_mul, QH, mul_one];exact Complex.norm_ofNat 2)
  exact JoinedIn.trans ⟨p1, hp1⟩ ⟨p2, hp2⟩
 by_cases hnorm : 1 ≤ ‖x‖
 · exact (h_ray_path x hnorm).symm
 ·
  rw [not_le] at hnorm
  have hball : x ∈ ball (0 : Z) 1 := by rwa [mem_ball_zero_iff]
  have hnot : ¬ ∀ i : Fin 3, R2 ≤ W (x - qH i) := fun hi => hx ⟨hball, hi⟩;push Not at hnot;obtain ⟨i, hi⟩ := hnot
  let p0 : Path (qH i) x :=
   ⟨⟨fun t => (1 - (t : X) : Z) * qH i + (t : X) * x,((continuous_const.sub (continuous_ofReal.comp continuous_subtype_val)).mul continuous_const).add ((continuous_ofReal.comp continuous_subtype_val).mul continuous_const)⟩,
    by dsimp;simp only [sub_zero,one_mul,zero_mul,add_zero], by dsimp;simp only [sub_self,zero_mul,one_mul,zero_add]⟩
  have hp0 : ∀ t : unitInterval, p0 t ∈ T0ᶜ := fun t hT => by
   have hsub : p0 t - qH i = (t : Z) * (x - qH i) := by dsimp [p0];ring
   have hns : W (p0 t - qH i) = (t : X) ^ 2 * W (x - qH i) := by rw [hsub, normSq_mul, normSq_ofReal, sq]
   have ht_le : (t : X) ^ 2 ≤ 1 := by nlinarith only [t.2.1, t.2.2]
   have hlt : W (p0 t - qH i) < R2 := by
    rw [hns];exact (mul_le_of_le_one_left (normSq_nonneg _) ht_le).trans_lt hi
   exact absurd (hT.2 i) (not_le.2 hlt)
  have hci_norm : 1 ≤ ‖qH i‖ := by
   rw [qJ];exact qs.le
  exact JoinedIn.trans (h_ray_path (qH i) hci_norm).symm ⟨p0, hp0⟩
lemma Q5 : IsOpen qU := by
 have heq : qU = ball (0 : Z) 1 ∩ ⋂ i : Fin 3, { z : Z | R2 < W (z - qH i) } := by ext z;simp only [qU,mem_ball,dist_zero_right,mem_ofPred_eq,mem_inter_iff,mem_iInter]
 rw [heq]
 refine isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
 exact isOpen_lt continuous_const (continuous_normSq.comp (continuous_id.sub continuous_const))
lemma Q6 : DifferentiableOn Z zo (ball (0 : Z) 1 ∪ zy) := by
 intro u hu
 have hslit : u ^ 3 ∈ xN := by
  rcases hu with h | h
  · exact zL h
  · exact zK h
 exact (zT hslit).differentiableAt.differentiableWithinAt
lemma Q7 {u : Z} (hu : u ∈ ball (0 : Z) 1 ∪ zy) (hy2 : zo u ≠ 0) :
  AnalyticAt Z zp u := by
 have hU_open : IsOpen (ball (0 : Z) 1 ∪ zy) := isOpen_ball.union zA
 have hy2_cont : ContinuousAt zo u :=
  (Q6 u hu).continuousWithinAt.continuousAt (hU_open.mem_nhds hu)
 have hne_nhds : ∀ᶠ v in 𝓝 u, zo v ≠ 0 := hy2_cont.eventually_ne hy2
 have hdiff_nhds : ∀ᶠ v in 𝓝 u, DifferentiableAt Z zp v := by
  filter_upwards [hU_open.mem_nhds hu, hne_nhds] with v hv hvy2
  exact (Qp hv hvy2).differentiableAt
 obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hdiff_nhds;exact (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).2
  (fun v hv => (hball hv).differentiableWithinAt) u (mem_ball_self hr)
lemma Q8 : AnalyticOnNhd Z zp (ball (0 : Z) 1) :=
 fun _ hu => Q7 (Or.inl hu) (z3 (ball_subset_closedBall hu))
lemma Q9 {V : Set Z} (hVo : IsOpen V) (hV : V ⊆ ball (0 : Z) 1) :
  IsOpen (zp '' V) := by
 rw [isOpen_iff_mem_nhds];rintro _ ⟨u, huV, rfl⟩;have ha : AnalyticAt Z zp u := Q8 u (hV huV)
 have hne : deriv zp u ≠ 0 :=
  Qq (Or.inl (hV huV)) (z3 (ball_subset_closedBall (hV huV)))
 have hmap : Filter.map zp (𝓝 u) = 𝓝 (zp u) := ha.hasStrictDerivAt.map_nhds_eq hne;rw [← hmap, Filter.mem_map];exact mem_of_superset (hVo.mem_nhds huV) (subset_preimage_image zp V)
lemma Ka : zp '' ball (0 : Z) 1 = qU := by
 let U := zp '' ball (0 : Z) 1;have hUo : IsOpen U := Q9 isOpen_ball Subset.rfl
 have hKc : IsClosed (zp '' closedBall (0 : Z) 1) :=
  ((isCompact_closedBall (0 : Z) 1).image_of_continuousOn Qm).isClosed
 let V := (zp '' closedBall (0 : Z) 1)ᶜ;have hVo : IsOpen V := hKc.isOpen_compl
 have hUV : U ∩ V = ∅ := by
  ext x;simp only [mem_inter_iff,mem_compl_iff,mem_empty_iff_false,iff_false,not_and,not_not,U,V];rintro ⟨u, hu, rfl⟩;exact ⟨u, ball_subset_closedBall hu, rfl⟩
 have hcb_split : zp '' closedBall (0 : Z) 1 = U ∪ zp '' sphere (0 : Z) 1 := by rw [← ball_union_sphere, image_union]
 have hcompl_sub : T0ᶜ ⊆ U ∪ V := by
  intro x hx
  by_cases hmem : x ∈ zp '' closedBall (0 : Z) 1
  ·
   rw [hcb_split] at hmem
   rcases hmem with hxU | hxS
   · exact Or.inl hxU
   · exact absurd (QZ hxS).1 hx
  · exact Or.inr hmem
 have hT0c_sub : T0ᶜ ⊆ U ∨ T0ᶜ ⊆ V :=
  isPreconnected_iff_subset_of_disjoint.1 Q4 U V hUo hVo hcompl_sub
   (by rw [hUV, inter_empty])
 have hU_sub_T0 : U ⊆ T0 := by
  rcases hT0c_sub with h1 | h2
  ·
   exfalso
   have h2_mem : (2 : Z) ∈ T0ᶜ := fun h => by
    have := jT h;simp only [Complex.norm_ofNat] at this;linarith [qp]
   rcases h1 h2_mem with ⟨u, hu, hu2⟩
   have hlt : ‖zp u‖ < 1 := Qx (ball_subset_closedBall hu);rw [hu2] at hlt;norm_num at hlt
  ·
   intro x hxU
   by_contra hxT0
   have hxV := h2 hxT0;exact eq_empty_iff_forall_notMem.1 hUV x ⟨hxU, hxV⟩
 have hU_sub_int : U ⊆ qU := by
  intro x hxU
  refine ⟨(hU_sub_T0 hxU).1, fun i => ?_⟩
  rcases lt_or_eq_of_le ((hU_sub_T0 hxU).2 i) with hlt | heq
  · exact hlt
  ·
   exfalso;obtain ⟨ε, hε, hε_sub⟩ := isOpen_iff.1 hUo x hxU
   have hsub : x - qH i ≠ 0 := by intro h0;rw [h0, normSq_zero] at heq;linarith [qu]
   have hnorm_pos : 0 < ‖x - qH i‖ := norm_pos_iff.2 hsub;let t : X := min (ε / 2 / ‖x - qH i‖) (1 / 2);have ht0 : 0 < t := lt_min (div_pos (half_pos hε) hnorm_pos) k2;have ht1 : t < 1 := (min_le_right _ _).trans_lt (half_lt_self zero_lt_one);let y : Z := x - (t : Z) * (x - qH i)
   have hy_ball : y ∈ ball x ε := by
    rw [mem_ball, dist_eq_norm, show y - x = -((t : Z) * (x - qH i)) by dsimp [y];ring,
     norm_neg, norm_mul, Complex.norm_of_nonneg ht0.le]
    have hle : t * ‖x - qH i‖ ≤ ε / 2 := by
     calc t * ‖x - qH i‖ ≤ (ε / 2 / ‖x - qH i‖) * ‖x - qH i‖ :=
           mul_le_mul_of_nonneg_right (min_le_left _ _) hnorm_pos.le
       _ = ε / 2 := div_mul_cancel₀ _ hnorm_pos.ne'
    linarith
   have hyT0 : y ∈ T0 := hU_sub_T0 (hε_sub hy_ball)
   have hy_sub : y - qH i = ((1 - t : X) : Z) * (x - qH i) := by dsimp [y];push_cast;ring
   have hy_ns : W (y - qH i) = (1 - t) ^ 2 * R2 := by rw [hy_sub, normSq_mul, normSq_ofReal, ← sq, ← heq]
   have h1t_sq : (1 - t) ^ 2 < 1 := by nlinarith only [ht0, ht1]
   have hlt_R2 : W (y - qH i) < R2 := by rw [hy_ns];nlinarith only [h1t_sq, qu]
   exact (hyT0.2 i).not_gt hlt_R2
 have hint_sub_U : qU ⊆ U := by
  have hint_cov : qU ⊆ U ∪ V := by
   intro x hx
   by_cases hmem : x ∈ zp '' closedBall (0 : Z) 1
   ·
    rw [hcb_split] at hmem
    rcases hmem with hxU | hxS
    · exact Or.inl hxU
    · exact absurd hx (QZ hxS).2
   · exact Or.inr hmem
  rcases isPreconnected_iff_subset_of_disjoint.1 Q3 U V hUo hVo hint_cov
    (by rw [hUV, inter_empty]) with h1 | h2
  · exact h1
  ·
   exfalso;have h0U : (0 : Z) ∈ U := ⟨0, mem_ball_self one_pos, Qr⟩;have h0V : (0 : Z) ∈ V := h2 qV;exact eq_empty_iff_forall_notMem.1 hUV 0 ⟨h0U, h0V⟩
 exact Subset.antisymm hU_sub_int hint_sub_U
lemma Kb {u : Z} (hu : u ∈ closedBall (0 : Z) 1) : zp u = 0 ↔ u = 0 := by
 constructor
 ·
  intro hz;have hy2 : zo u ≠ 0 := z3 hu;have hC1 : (zc : Z) ≠ 0 := ofReal_ne_zero.2 ze.ne'
  have hy1 : zn u = 0 := by
   dsimp [zp] at hz
   rcases mul_eq_zero.1 ((div_eq_zero_iff.1 hz).resolve_right hy2) with h | h
   · exact absurd h hC1
   · exact h
  dsimp [zn] at hy1
  rcases mul_eq_zero.1 hy1 with rfl | hF
  · rfl
  ·
   exfalso
   have hu3 : ‖u ^ 3‖ ≤ 1 := by rw [norm_pow];exact pow_le_one₀ (norm_nonneg u) (mem_closedBall_zero_iff.1 hu)
   have hpos := xR (a := 5 / 12) (b := 3 / 4) (c := 4 / 3)
    xv xw k7 xs xt k5 hu3
   rw [hF, zero_re] at hpos;linarith
 · rintro rfl;exact Qr
lemma Kc : InjOn zp (ball (0 : Z) 1) := by
 let U_uniq : Set Z :=
  ⋃ (V : Set Z) (_ : IsOpen V) (_ : V ⊆ ball (0 : Z) 1) (_ : InjOn zp V),
   (zp '' V) ∩ (zp '' (closedBall (0 : Z) 1 \ V))ᶜ
 let U_multi : Set Z :=
  ⋃ (V₁ : Set Z) (_ : IsOpen V₁) (_ : V₁ ⊆ ball (0 : Z) 1)
   (V₂ : Set Z) (_ : IsOpen V₂) (_ : V₂ ⊆ ball (0 : Z) 1) (_ : Disjoint V₁ V₂),
   (zp '' V₁) ∩ (zp '' V₂)
 have hU_uniq_open : IsOpen U_uniq := by
  refine isOpen_iUnion fun V => isOpen_iUnion fun hVo => isOpen_iUnion fun hVsub =>
   isOpen_iUnion fun _ => ?_
  refine (Q9 hVo hVsub).inter ?_
  have hKc : IsCompact (closedBall (0 : Z) 1 \ V) :=
   (isCompact_closedBall (0 : Z) 1).diff hVo
  exact (hKc.image_of_continuousOn
   (Qm.mono sdiff_subset)).isClosed.isOpen_compl
 have hU_multi_open : IsOpen U_multi := by
  refine isOpen_iUnion fun V₁ => isOpen_iUnion fun hV1o => isOpen_iUnion fun hV1sub =>
   isOpen_iUnion fun V₂ => isOpen_iUnion fun hV2o => isOpen_iUnion fun hV2sub =>
   isOpen_iUnion fun _ => ?_
  exact (Q9 hV1o hV1sub).inter (Q9 hV2o hV2sub)
 have hdisj : U_uniq ∩ U_multi = ∅ := by
  ext x;simp only [mem_inter_iff,mem_empty_iff_false,iff_false,not_and];intro hx1 hx2;simp only [U_uniq,mem_iUnion,exists_prop] at hx1;simp only [U_multi,mem_iUnion,exists_prop] at hx2;obtain ⟨V, _, hVsub, hVinj, ⟨u, huV, rfl⟩, hxnot⟩ := hx1;obtain ⟨V₁, _, hV1sub, V₂, _, hV2sub, hV12, ⟨u₁, hu₁V₁, hu1eq⟩, ⟨u₂, hu₂V₂, hu2eq⟩⟩ := hx2
  have hu₁V : u₁ ∈ V := by
   by_contra h
   exact hxnot ⟨u₁, ⟨ball_subset_closedBall (hV1sub hu₁V₁), h⟩, hu1eq⟩
  have hu₂V : u₂ ∈ V := by
   by_contra h
   exact hxnot ⟨u₂, ⟨ball_subset_closedBall (hV2sub hu₂V₂), h⟩, hu2eq⟩
  have hu12 : u₁ = u₂ := hVinj hu₁V hu₂V (hu1eq.trans hu2eq.symm);exact disjoint_left.1 hV12 hu₁V₁ (hu12 ▸ hu₂V₂)
 have hcov : qU ⊆ U_uniq ∪ U_multi := by
  intro x hx
  have hxU : x ∈ zp '' ball (0 : Z) 1 := by rwa [Ka]
  obtain ⟨u, hu, rfl⟩ := hxU
  by_cases huniq : ∀ v ∈ ball (0 : Z) 1, zp v = zp u → v = u
  ·
   refine Or.inl ?_
   have ha : AnalyticAt Z zp u := Q8 u hu
   have hne : deriv zp u ≠ 0 :=
    Qq (Or.inl hu) (z3 (ball_subset_closedBall hu))
   have hli := ha.hasStrictDerivAt.eventually_left_inverse hne;obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hli.and (isOpen_ball.mem_nhds hu))
   refine mem_iUnion.2 ⟨ball u r, mem_iUnion.2 ⟨isOpen_ball, mem_iUnion.2
    ⟨fun v hv => (hball hv).2,mem_iUnion.2 ⟨?_,?_⟩⟩⟩⟩
   ·
    intro v₁ hv₁ v₂ hv₂ heq;have h1 := (hball hv₁).1;have h2 := (hball hv₂).1;rw [← h1, ← h2, heq]
   ·
    refine ⟨⟨u, mem_ball_self hr, rfl⟩, ?_⟩
    rintro ⟨v, ⟨hv_cb, hv_nV⟩, hveq⟩
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.1 hv_cb) with hv_ball | hv_sph
    · exact hv_nV ((huniq v (mem_ball_zero_iff.2 hv_ball) hveq) ▸ mem_ball_self hr)
    ·
     have hsph : zp v ∈ zp '' sphere (0 : Z) 1 := ⟨v, mem_sphere_zero_iff_norm.2 hv_sph, rfl⟩;exact (QZ hsph).2 (hveq ▸ hx)
  ·
   push Not at huniq;obtain ⟨v, hv, hveq, hvne⟩ := huniq;obtain ⟨V₁, V₂, hV1o, hV2o, huV₁, hvV₂, hdisjV⟩ := t2_separation hvne.symm
   refine Or.inr (mem_iUnion.2 ⟨V₁ ∩ ball 0 1, mem_iUnion.2 ⟨hV1o.inter isOpen_ball,
    mem_iUnion.2 ⟨inter_subset_right, mem_iUnion.2 ⟨V₂ ∩ ball 0 1,
    mem_iUnion.2 ⟨hV2o.inter isOpen_ball, mem_iUnion.2 ⟨inter_subset_right,
    mem_iUnion.2 ⟨hdisjV.mono inter_subset_left inter_subset_left, ?_⟩⟩⟩⟩⟩⟩⟩)
   exact ⟨⟨u, ⟨huV₁, hu⟩, rfl⟩, ⟨v, ⟨hvV₂, hv⟩, hveq⟩⟩
 have h0_uniq : (0 : Z) ∈ U_uniq := by
  rcases hcov qV with h | h
  · exact h
  ·
   exfalso;simp only [U_multi,mem_iUnion,exists_prop] at h;obtain ⟨V₁, _, hV1sub, V₂, _, hV2sub, hV12, ⟨u₁, hu₁V₁, hu1eq⟩, ⟨u₂, hu₂V₂, hu2eq⟩⟩ := h;have h1 : u₁ = 0 := (Kb (ball_subset_closedBall (hV1sub hu₁V₁))).1 hu1eq;have h2 : u₂ = 0 := (Kb (ball_subset_closedBall (hV2sub hu₂V₂))).1 hu2eq;exact disjoint_left.1 hV12 hu₁V₁ (h1 ▸ h2 ▸ hu₂V₂)
 have hint_uniq : qU ⊆ U_uniq := by
  rcases isPreconnected_iff_subset_of_disjoint.1 Q3 U_uniq U_multi
    hU_uniq_open hU_multi_open hcov (by rw [hdisj, inter_empty]) with h1 | h2
  · exact h1
  · exact absurd (h2 qV) (fun h => eq_empty_iff_forall_notMem.1 hdisj 0 ⟨h0_uniq, h⟩)
 intro u₁ hu₁ u₂ hu₂ heq
 have hx : zp u₁ ∈ qU := by rw [← Ka];exact ⟨u₁, hu₁, rfl⟩
 have hxu := hint_uniq hx;simp only [U_uniq,mem_iUnion,exists_prop] at hxu;obtain ⟨V, _, _, hVinj, ⟨v₁, hv₁, hv1eq⟩, hxnot⟩ := hxu
 have hu₁V : u₁ ∈ V := by
  by_contra h;exact hxnot ⟨u₁, ⟨ball_subset_closedBall hu₁, h⟩, rfl⟩
 have hu₂V : u₂ ∈ V := by
  by_contra h;exact hxnot ⟨u₂, ⟨ball_subset_closedBall hu₂, h⟩, heq.symm⟩
 exact hVinj hu₁V hu₂V heq
lemma Kd {θ : X} (hθ0 : 0 < θ) (hθ1 : θ < 2 * π / 3) :
  W (zp (QG θ) - qH 1) = R2 ∧
  R2 < W (zp (QG θ) - qH 0) ∧
  R2 < W (zp (QG θ) - qH 2) := by
 have hmem := QY hθ0.le hθ1.le
 have h1 : W (zp (QG θ) - qH 1) = R2 :=
  QO hθ0.le hθ1.le
 have hne0 : zp (QG θ) ≠ j5 0 := by
  intro h
  have h0 := QX ⟨le_rfl, by positivity [pi_pos]⟩ ⟨hθ0.le, hθ1.le⟩
   (by dsimp only;rw [QK, Qu.1, h])
  linarith
 have hne2 : zp (QG θ) ≠ j5 2 := by
  intro h
  have h2 := QX ⟨by positivity [pi_pos], le_rfl⟩ ⟨hθ0.le, hθ1.le⟩
   (by dsimp only;rw [QL, Qu.2.2, h])
  linarith
 refine ⟨h1, ?_, ?_⟩
 ·
  rcases lt_or_eq_of_le (hmem.1.2 0) with hlt | heq
  · exact hlt
  · exact absurd (ke (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide) hmem.1 heq.symm h1) hne2
 ·
  rcases lt_or_eq_of_le (hmem.1.2 2) with hlt | heq
  · exact hlt
  · exact absurd (ke (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide) hmem.1 h1 heq.symm) hne0
lemma Ke : InjOn zp (sphere (0 : Z) 1) := by
 let S₁ : Set Z := QG '' Ioo 0 (2 * π / 3);let S₂ : Set Z := (fun u => ω * u) '' S₁;let S₀ : Set Z := (fun u => ω ^ 2 * u) '' S₁
 have hθ_rep : ∀ u ∈ sphere (0 : Z) 1,
   u = 1 ∨ u = ω ∨ u = ω ^ 2 ∨ u ∈ S₁ ∨ u ∈ S₂ ∨ u ∈ S₀ := by
  intro u hu;rw [mem_sphere_zero_iff_norm] at hu;let θ : X := if 0 ≤ Complex.arg u then Complex.arg u else Complex.arg u + 2 * π
  have hθ0 : 0 ≤ θ := by
   dsimp [θ];split_ifs with h
   · exact h
   · linarith [neg_pi_lt_arg u]
  have hθ2π : θ < 2 * π := by
   dsimp [θ];split_ifs with h
   · linarith [arg_le_pi u, pi_pos]
   · linarith
  have hu_eq : u = QG θ := by
   have hbase := norm_mul_exp_arg_mul_I u;rw [hu] at hbase;simp only [ofReal_one,one_mul] at hbase;dsimp [θ, QG];split_ifs
   · exact hbase.symm
   ·
    rw [ofReal_add, add_mul, Complex.exp_add]
    have h2pi : Complex.exp (((2 * π : X) : Z) * I) = 1 := by push_cast;rw [exp_two_pi_mul_I]
    rw [h2pi, mul_one];exact hbase.symm
  rw [hu_eq]
  rcases eq_or_lt_of_le hθ0 with h0_eq | h0'
  · rw [← h0_eq];exact Or.inl QK
  ·
   rcases lt_trichotomy θ (2 * π / 3) with h1 | h1 | h1
   · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨θ, ⟨h0', h1⟩, rfl⟩)))
   · rw [h1];exact Or.inr (Or.inl QL)
   ·
    rcases lt_trichotomy θ (4 * π / 3) with h2 | h2 | h2
    ·
     refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨QG (θ - 2 * π / 3),
      ⟨θ - 2 * π / 3,⟨by linarith,by linarith⟩,rfl⟩,?_⟩))))
     dsimp only;rw [← QL, ← QM];ring_nf
    ·
     refine Or.inr (Or.inr (Or.inl ?_))
     rw [h2, show 4 * π / 3 = 2 * π / 3 + 2 * π / 3 by ring,
      QM, QL];ring
    ·
     refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨QG (θ - 4 * π / 3),
      ⟨θ - 4 * π / 3,⟨by linarith,by linarith⟩,rfl⟩,?_⟩))))
     dsimp only;rw [sq, mul_assoc, ← QL, ← QM, ← QM];ring_nf
 have hω_ns : W ω = 1 := by rw [← Complex.sq_norm, qk];exact one_pow 2
 have h_open1 : ∀ u ∈ S₁,
   W (zp u - qH 1) = R2 ∧
   R2 < W (zp u - qH 0) ∧
   R2 < W (zp u - qH 2) := by
  rintro _ ⟨θ, hθ, rfl⟩;exact Kd hθ.1 hθ.2
 have h_open2 : ∀ u ∈ S₂,
   W (zp u - qH 0) = R2 ∧
   R2 < W (zp u - qH 1) ∧
   R2 < W (zp u - qH 2) := by
  rintro _ ⟨u, hu, rfl⟩;dsimp only;have hm := h_open1 u hu;rw [Qe];have hc := QC
  have h0 : W (ω * zp u - qH 0) = W (zp u - qH 1) := by rw [← hc.1, ← mul_sub, normSq_mul, hω_ns, one_mul]
  have h1 : W (ω * zp u - qH 1) = W (zp u - qH 2) := by rw [← hc.2.2, ← mul_sub, normSq_mul, hω_ns, one_mul]
  have h2 : W (ω * zp u - qH 2) = W (zp u - qH 0) := by rw [← hc.2.1, ← mul_sub, normSq_mul, hω_ns, one_mul]
  rw [h0, h1, h2];exact ⟨hm.1, hm.2.2, hm.2.1⟩
 have h_open0 : ∀ u ∈ S₀,
   W (zp u - qH 2) = R2 ∧
   R2 < W (zp u - qH 0) ∧
   R2 < W (zp u - qH 1) := by
  rintro _ ⟨u, hu, rfl⟩;dsimp only;have hm := h_open2 (ω * u) ⟨u, hu, rfl⟩
  rw [show ω ^ 2 * u = ω * (ω * u) by ring, Qe]
  have hc := QC
  have h0 : W (ω * zp (ω * u) - qH 0) = W (zp (ω * u) - qH 1) := by rw [← hc.1, ← mul_sub, normSq_mul, hω_ns, one_mul]
  have h1 : W (ω * zp (ω * u) - qH 1) = W (zp (ω * u) - qH 2) := by rw [← hc.2.2, ← mul_sub, normSq_mul, hω_ns, one_mul]
  have h2 : W (ω * zp (ω * u) - qH 2) = W (zp (ω * u) - qH 0) := by rw [← hc.2.1, ← mul_sub, normSq_mul, hω_ns, one_mul]
  rw [h0, h1, h2];exact ⟨hm.1, hm.2.1, hm.2.2⟩
 have hS1_inj : InjOn zp S₁ := by
  rintro _ ⟨θ₁, hθ₁, rfl⟩ _ ⟨θ₂, hθ₂, rfl⟩ heq
  have hθ := QX ⟨hθ₁.1.le, hθ₁.2.le⟩ ⟨hθ₂.1.le, hθ₂.2.le⟩ (by dsimp only;rw [heq])
  rw [hθ]
 have hω_ne : ω ≠ 0 := by intro h;have := qk;rw [h, norm_zero] at this;exact one_ne_zero this.symm
 have hS2_inj : InjOn zp S₂ := by
  rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ heq
  dsimp only at heq ⊢
  rw [Qe, Qe] at heq;rw [hS1_inj hu₁ hu₂ (mul_left_cancel₀ hω_ne heq)]
 have hS0_inj : InjOn zp S₀ := by
  rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ heq
  dsimp only at heq ⊢
  rw [show ω ^ 2 * u₁ = ω * (ω * u₁) by ring, show ω ^ 2 * u₂ = ω * (ω * u₂) by ring,
   Qe, Qe, Qe, Qe] at heq
  rw [hS1_inj hu₁ hu₂ (mul_left_cancel₀ hω_ne (mul_left_cancel₀ hω_ne heq))]
 let sideCode : Z → ℕ := fun z =>
  (if W (z - qH 0) = R2 then 1 else 0) +
  (if W (z - qH 1) = R2 then 2 else 0) +
  (if W (z - qH 2) = R2 then 4 else 0)
 have hdiag_gt : ∀ k : Fin 3, R2 < W (j5 k - qH k) := by
  intro k;have h3 : Y 3 ^ 2 = 3 := qc
  have hre : (j4 k * T (qy k)).re = -1 := by
   fin_cases k
   · simp only [j4,qy,map_neg,map_one,mul_neg,mul_one,neg_re,one_re]
   · simp only [j4,ω,sq,qy,map_neg,map_mul,mul_neg,neg_re,mul_re,conj_re,conj_im,neg_mul,neg_neg,mul_im,neg_sub];nlinarith only [h3]
   · simp only [j4,ω,qy,map_neg,mul_neg,neg_re,mul_re,conj_re,conj_im,sub_neg_eq_add,neg_add_rev];nlinarith only [h3]
  rw [j9, hre];dsimp [R2];nlinarith only [qn, qq]
 have hcode_v0 : sideCode (j5 0) = 6 := by simp only [Fin.isValue,(hdiag_gt 0).ne',↓reduceIte,kb (i := 1) (k := 0) (by decide),zero_add,kb (i := 2) (k := 0) (by decide),Nat.reduceAdd,sideCode]
 have hcode_v1 : sideCode (j5 1) = 5 := by simp only [Fin.isValue,kb (i := 0) (k := 1) (by decide),↓reduceIte,(hdiag_gt 1).ne',add_zero,kb (i := 2) (k := 1) (by decide),Nat.reduceAdd,sideCode]
 have hcode_v2 : sideCode (j5 2) = 3 := by simp only [Fin.isValue,kb (i := 0) (k := 2) (by decide),↓reduceIte,kb (i := 1) (k := 2) (by decide),Nat.reduceAdd,(hdiag_gt 2).ne',add_zero,sideCode]
 have hcode_s1 : ∀ u ∈ S₁, sideCode (zp u) = 2 := fun u hu => by
  obtain ⟨h1, h0, h2⟩ := h_open1 u hu;simp only [Fin.isValue,h0.ne',↓reduceIte,h1,zero_add,h2.ne',add_zero,sideCode]
 have hcode_s2 : ∀ u ∈ S₂, sideCode (zp u) = 1 := fun u hu => by
  obtain ⟨h0, h1, h2⟩ := h_open2 u hu;simp only [Fin.isValue,h0,↓reduceIte,h1.ne',add_zero,h2.ne',sideCode]
 have hcode_s0 : ∀ u ∈ S₀, sideCode (zp u) = 4 := fun u hu => by
  obtain ⟨h2, h0, h1⟩ := h_open0 u hu;simp only [Fin.isValue,h0.ne',↓reduceIte,h1.ne',add_zero,h2,zero_add,sideCode]
 have htag : ∀ u ∈ sphere (0 : Z) 1,
   (u = 1 ∧ sideCode (zp u) = 6) ∨
   (u = ω ∧ sideCode (zp u) = 3) ∨
   (u = ω ^ 2 ∧ sideCode (zp u) = 5) ∨
   (u ∈ S₁ ∧ sideCode (zp u) = 2) ∨
   (u ∈ S₂ ∧ sideCode (zp u) = 1) ∨
   (u ∈ S₀ ∧ sideCode (zp u) = 4) := fun u hu => by
  rcases hθ_rep u hu with rfl | rfl | rfl | h1 | h2 | h0
  · exact Or.inl ⟨rfl, by rw [Qu.1, hcode_v0]⟩
  · exact Or.inr (Or.inl ⟨rfl, by rw [Qu.2.2, hcode_v2]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, by rw [Qu.2.1, hcode_v1]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, hcode_s1 u h1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, hcode_s2 u h2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, hcode_s0 u h0⟩))))
 intro u hu v hv heq;have hce : sideCode (zp u) = sideCode (zp v) := congrArg sideCode heq
 rcases htag u hu with ⟨rfl, hcu⟩ | ⟨rfl, hcu⟩ | ⟨rfl, hcu⟩ | ⟨hu1, hcu⟩ | ⟨hu2, hcu⟩ | ⟨hu0, hcu⟩ <;>
 rcases htag v hv with ⟨rfl, hcv⟩ | ⟨rfl, hcv⟩ | ⟨rfl, hcv⟩ | ⟨hv1, hcv⟩ | ⟨hv2, hcv⟩ | ⟨hv0, hcv⟩
 all_goals first | rfl | exact hS1_inj hu1 hv1 heq | exact hS2_inj hu2 hv2 heq |
  exact hS0_inj hu0 hv0 heq | (exfalso;linarith [hce, hcu, hcv])
lemma Kf : BijOn zp (closedBall (0 : Z) 1) T0 := by
 have hmaps : MapsTo zp (closedBall (0 : Z) 1) T0 := by
  intro u hu
  rcases lt_or_eq_of_le (mem_closedBall_zero_iff.1 hu) with hu_b | hu_s
  ·
   have : zp u ∈ zp '' ball (0 : Z) 1 := ⟨u, mem_ball_zero_iff.2 hu_b, rfl⟩;rw [Ka] at this;exact qW this
  · exact (QZ ⟨u, mem_sphere_zero_iff_norm.2 hu_s, rfl⟩).1
 have hinj : InjOn zp (closedBall (0 : Z) 1) := by
  intro u₁ hu₁ u₂ hu₂ heq
  rcases lt_or_eq_of_le (mem_closedBall_zero_iff.1 hu₁) with h1 | h1 <;>
  rcases lt_or_eq_of_le (mem_closedBall_zero_iff.1 hu₂) with h2 | h2
  · exact Kc (mem_ball_zero_iff.2 h1) (mem_ball_zero_iff.2 h2) heq
  ·
   exfalso
   have hx1 : zp u₁ ∈ qU := by rw [← Ka];exact ⟨u₁, mem_ball_zero_iff.2 h1, rfl⟩
   have hx2 : zp u₂ ∈ T0 \ qU := QZ ⟨u₂, mem_sphere_zero_iff_norm.2 h2, rfl⟩;exact hx2.2 (heq ▸ hx1)
  ·
   exfalso;have hx1 : zp u₁ ∈ T0 \ qU := QZ ⟨u₁, mem_sphere_zero_iff_norm.2 h1, rfl⟩
   have hx2 : zp u₂ ∈ qU := by rw [← Ka];exact ⟨u₂, mem_ball_zero_iff.2 h2, rfl⟩
   exact hx1.2 (heq.symm ▸ hx2)
  · exact Ke (mem_sphere_zero_iff_norm.2 h1) (mem_sphere_zero_iff_norm.2 h2) heq
 have hsurj : SurjOn zp (closedBall (0 : Z) 1) T0 := by
  intro x hx
  by_cases hx_int : x ∈ qU
  ·
   rw [← Ka] at hx_int;obtain ⟨u, hu, rfl⟩ := hx_int;exact ⟨u, ball_subset_closedBall hu, rfl⟩
  ·
   have hnot : ¬ ∀ i : Fin 3, R2 < W (x - qH i) := fun h => hx_int ⟨hx.1, h⟩;push Not at hnot;obtain ⟨i, hi⟩ := hnot;have hxi : W (x - qH i) = R2 := le_antisymm hi (hx.2 i)
   fin_cases i
   ·
    have hx1 : ω ^ 2 * x ∈ T0 := by rw [sq, mul_assoc];exact QD.2 (QD.2 hx)
    have hx1_side : W (ω ^ 2 * x - qH 1) = R2 := by
     have hc : ω ^ 2 * qH 0 = qH 1 := by rw [sq, mul_assoc, QC.2.1, QC.2.2]
     rw [← hc, ← mul_sub, normSq_mul, ← Complex.sq_norm, norm_pow,
      qk, one_pow, one_pow, one_mul]
     exact hxi
    obtain ⟨θ, hθ, hθeq⟩ := Q1 hx1 hx1_side
    refine ⟨ω * QG θ, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_mul, qk, one_mul, QH]
    ·
     rw [Qe, hθeq]
     calc ω * (ω ^ 2 * x) = ω ^ 3 * x := by ring
       _ = x := by rw [qj, one_mul]
   ·
    obtain ⟨θ, hθ, hθeq⟩ := Q1 hx hxi;exact ⟨QG θ, QI θ, hθeq⟩
   ·
    have hx1 : ω * x ∈ T0 := QD.2 hx
    have hx1_side : W (ω * x - qH 1) = R2 := by
     rw [← QC.2.2, ← mul_sub, normSq_mul, ← Complex.sq_norm, qk, one_pow, one_mul];exact hxi
    obtain ⟨θ, hθ, hθeq⟩ := Q1 hx1 hx1_side
    refine ⟨ω ^ 2 * QG θ, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_mul, norm_pow, qk, one_pow, one_mul, QH]
    ·
     rw [show ω ^ 2 * QG θ = ω * (ω * QG θ) by ring, Qe, Qe, hθeq]
     calc ω * (ω * (ω * x)) = ω ^ 3 * x := by ring
       _ = x := by rw [qj, one_mul]
 exact ⟨hmaps, hinj, hsurj⟩
noncomputable def Kg : Z → Z := Function.invFunOn zp (closedBall (0 : Z) 1)
lemma Kh {x : Z} (hx : x ∈ T0) : Kg x ∈ closedBall (0 : Z) 1 := by
 have hx' : x ∈ zp '' closedBall (0 : Z) 1 := Kf.surjOn hx;exact (Function.invFunOn_pos hx').1
lemma Ki {x : Z} (hx : x ∈ T0) : zp (Kg x) = x := by
 have hx' : x ∈ zp '' closedBall (0 : Z) 1 := Kf.surjOn hx;exact (Function.invFunOn_pos hx').2
lemma Kj {u : Z} (hu : u ∈ closedBall (0 : Z) 1) : Kg (zp u) = u :=
 Kf.injOn (Kh (Kf.mapsTo hu)) hu
  (Ki (Kf.mapsTo hu))
lemma Kk {x : Z} (hx : x ∈ qU) : Kg x ∈ ball (0 : Z) 1 := by
 rcases lt_or_eq_of_le (mem_closedBall_zero_iff.1 (Kh (qW hx))) with h | h
 · exact mem_ball_zero_iff.2 h
 ·
  exfalso
  have hs : x ∈ zp '' sphere (0 : Z) 1 :=
   ⟨Kg x,mem_sphere_zero_iff_norm.2 h,Ki (qW hx)⟩
  exact (QZ hs).2 hx
lemma Kl : ContinuousOn Kg T0 := by
 rw [continuousOn_iff_isClosed];intro t ht;let K := t ∩ closedBall (0 : Z) 1;have hKc : IsCompact K := (isCompact_closedBall (0 : Z) 1).inter_left ht
 have himg_closed : IsClosed (zp '' K) :=
  (hKc.image_of_continuousOn (Qm.mono inter_subset_right)).isClosed
 refine ⟨zp '' K, himg_closed, ?_⟩
 ext x;simp only [mem_inter_iff,mem_preimage];constructor
 ·
  rintro ⟨hxt, hxT⟩;exact ⟨⟨Kg x, ⟨hxt, Kh hxT⟩, Ki hxT⟩, hxT⟩
 ·
  rintro ⟨⟨u, ⟨hut, hu_cb⟩, rfl⟩, hxT⟩
  exact ⟨by rwa [Kj hu_cb], hxT⟩
lemma Km : DifferentiableOn Z Kg qU := by
 intro x hx;have hu : Kg x ∈ ball (0 : Z) 1 := Kk hx;have ha : AnalyticAt Z zp (Kg x) := Q8 (Kg x) hu
 have hne : deriv zp (Kg x) ≠ 0 :=
  Qq (Or.inl hu) (z3 (ball_subset_closedBall hu))
 have hli := ha.hasStrictDerivAt.eventually_left_inverse hne
 have hloc : ∀ᶠ y in 𝓝 x, Kg y = ha.hasStrictDerivAt.localInverse zp (deriv zp (Kg x)) (Kg x) hne y := by
  have hcont : ContinuousAt Kg x :=
   Kl.continuousAt (mem_of_superset (Q5.mem_nhds hx) qW)
  have htend : ∀ᶠ y in 𝓝 x, Kg y ∈ { u | ha.hasStrictDerivAt.localInverse zp (deriv zp (Kg x)) (Kg x) hne (zp u) = u } :=
   hcont.eventually hli
  filter_upwards [Q5.mem_nhds hx, htend] with y hy hyeq
  calc Kg y = ha.hasStrictDerivAt.localInverse zp (deriv zp (Kg x)) (Kg x) hne (zp (Kg y)) := hyeq.symm
    _ = ha.hasStrictDerivAt.localInverse zp (deriv zp (Kg x)) (Kg x) hne y := by rw [Ki (qW hy)]
 have hloc_d := (ha.hasStrictDerivAt.to_localInverse hne).hasDerivAt;rw [Ki (qW hx)] at hloc_d;exact (hloc_d.congr_of_eventuallyEq hloc).differentiableAt.differentiableWithinAt
noncomputable def Kn : Z → Z := zr ∘ Kg
lemma Ko : ContinuousOn Kn T0 :=
 Qo.comp Kl fun _ hx => Kh hx
lemma Kp : DifferentiableOn Z Kn qU := by
 intro x hx;have hu : Kg x ∈ ball (0 : Z) 1 := Kk hx
 have dg : DifferentiableAt Z zr (Kg x) := by
  have dg0 := (z5 (Kg x) (Or.inl hu)).const_mul (zc : Z);exact dg0.differentiableAt
 exact (dg.comp x ((Km x hx).differentiableAt
  (Q5.mem_nhds hx))).differentiableWithinAt
lemma Kq : deriv Kn 0 = 1 := by
 have hz0 : Kg 0 = 0 := by
  calc Kg 0 = Kg (zp 0) := by rw [Qr]
    _ = 0 := Kj (mem_closedBall_self zero_le_one)
 have hdz_inv : HasDerivAt Kg (zc : Z)⁻¹ 0 := by
  have hd_z : HasDerivAt zp (zc : Z) 0 := by
   have ha := Q8 0 (mem_ball_self one_pos);rw [← Qs];exact ha.hasStrictDerivAt.hasDerivAt
  have hdz' := (Km 0 qV).differentiableAt
   (Q5.mem_nhds qV) |>.hasDerivAt
  have hdz'_z : HasDerivAt Kg (deriv Kg 0) (zp 0) := by rwa [Qr]
  have hcomp : HasDerivAt (Kg ∘ zp) (deriv Kg 0 * (zc : Z)) 0 :=
   hdz'_z.comp 0 hd_z
  have heq : ∀ᶠ u in 𝓝 (0 : Z), (Kg ∘ zp) u = u := by
   filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with u hu
   exact Kj (ball_subset_closedBall hu)
  have hid := (hasDerivAt_id (0 : Z)).congr_of_eventuallyEq heq;have hmul := hid.unique hcomp;have hC1 : (zc : Z) ≠ 0 := ofReal_ne_zero.2 ze.ne';have hinv : deriv Kg 0 = (zc : Z)⁻¹ := eq_inv_of_mul_eq_one_left hmul.symm;rwa [← hinv]
 have dg0 : HasDerivAt zr (zc : Z) 0 := by
  change HasDerivAt (fun y => (zc : Z) * zq y) (zc : Z) 0;have hdg := (z5 0 (Or.inl (mem_ball_self one_pos))).const_mul (zc : Z);simpa [one_cpow] using hdg
 rw [← hz0] at dg0
 have df0 : HasDerivAt Kn ((zc : Z) * (zc : Z)⁻¹) 0 := by dsimp [Kn];exact dg0.comp 0 hdz_inv
 have hC1 : (zc : Z) ≠ 0 := ofReal_ne_zero.2 ze.ne';rw [df0.deriv, mul_inv_cancel₀ hC1]
lemma Kr {x : Z} (hx : x ∈ T0) : Kn (ω * x) = ω * Kn x := by
 have hu : Kg x ∈ closedBall (0 : Z) 1 := Kh hx
 have hωu : ω * Kg x ∈ closedBall (0 : Z) 1 := by
  rw [mem_closedBall, dist_zero_right, norm_mul, qk, one_mul];exact mem_closedBall_zero_iff.1 hu
 have hzinv : Kg (ω * x) = ω * Kg x := by
  have hmap : zp (ω * Kg x) = ω * x := by rw [Qe, Ki hx]
  rw [← hmap, Kj hωu]
 dsimp [Kn];rw [hzinv, Qg]
lemma Ks {x : Z} (hx : x ∈ T0) (hx1 : W (x - qH 1) = R2)
  (hx0 : R2 < W (x - qH 0)) (hx2 : R2 < W (x - qH 2)) :
  ∃ G : Z → Z, AnalyticAt Z G x ∧
   (∀ᶠ y in 𝓝 x, y ∈ T0 → Kn y = G y) ∧
   (∀ᶠ y in 𝓝 x, y ∈ ball (0 : Z) 1 → qL 1 y ∈ T0 →
    (zd : Z) * qX 1 (Kn (qL 1 y) / (zd : Z)) = G y) := by
 obtain ⟨θ, hθ, hθeq⟩ := Q1 hx hx1
 have hθ0 : 0 < θ := by
  rcases eq_or_lt_of_le hθ.1 with rfl | h
  ·
   exfalso;rw [QK, Qu.1] at hθeq
   have hside := kb (i := 2) (k := 0) (by decide)
   rw [hθeq] at hside;linarith [hx2]
  · exact h
 have hθ1 : θ < 2 * π / 3 := by
  rcases eq_or_lt_of_le hθ.2 with rfl | h
  ·
   exfalso;rw [QL, Qu.2.2] at hθeq
   have hside := kb (i := 0) (k := 2) (by decide)
   rw [hθeq] at hside;linarith [hx0]
  · exact h
 let u := QG θ;have hu_eq : zp u = x := hθeq;have hu_cb : u ∈ closedBall (0 : Z) 1 := QI θ
 have hu_zinv : Kg x = u := by rw [← hu_eq, Kj hu_cb]
 have huU : u ∈ zy := QN hθ0 hθ1;have hy2u : zo u ≠ 0 := z3 hu_cb;have ha : AnalyticAt Z zp u := Q7 (Or.inr huU) hy2u;have hne : deriv zp u ≠ 0 := Qq (Or.inr huU) hy2u;let ψ := ha.hasStrictDerivAt.localInverse zp (deriv zp u) u hne
 have hψa : AnalyticAt Z ψ x := by rw [← hu_eq];exact ha.analyticAt_localInverse hne
 have hψx : ψ x = u := by rw [← hu_eq];exact HasStrictFDerivAt.localInverse_apply_image ..
 have hg_a : AnalyticAt Z zr u := by
  have hdiff_nhds : ∀ᶠ v in 𝓝 u, DifferentiableAt Z zr v := by
   filter_upwards [zA.mem_nhds huU] with v hv
   exact ((z5 v (Or.inr hv)).const_mul (zc : Z)).differentiableAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hdiff_nhds;exact (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).2
   (fun v hv => (hball hv).differentiableWithinAt) u (mem_ball_self hr)
 let G : Z → Z := zr ∘ ψ
 have hGa : AnalyticAt Z G x := AnalyticAt.comp (by rwa [hψx]) hψa
 refine ⟨G, hGa, ?_, ?_⟩
 ·
  have hli := ha.hasStrictDerivAt.eventually_left_inverse hne;have hcont : ContinuousWithinAt Kg T0 x := Kl x hx
  have hnhds_u : ∀ᶠ y in 𝓝[T0] x, ψ (zp (Kg y)) = Kg y :=
   hcont.eventually (by rw [hu_zinv];exact hli)
  rw [eventually_nhdsWithin_iff] at hnhds_u
  filter_upwards [hnhds_u] with y hy hyT
  have hψy : ψ y = Kg y := by nth_rw 1 [← Ki hyT];exact hy hyT
  dsimp [Kn, G];rw [hψy]
 ·
  have hli := ha.hasStrictDerivAt.eventually_left_inverse hne;have hri := ha.hasStrictDerivAt.eventually_right_inverse hne;rw [hu_eq] at hri;have hψ_cont : ContinuousAt ψ x := hψa.continuousAt
  have hψ_U1 : ∀ᶠ y in 𝓝 x, ψ y ∈ zy := hψ_cont.eventually (by rw [hψx];exact zA.mem_nhds huU)
  have hinv_star_cont : ContinuousAt (fun v : Z => 1 / T v) u :=
   continuousAt_const.div continuous_conj.continuousAt (by
    intro h0;have := QH θ;rw [← norm_conj, h0, norm_zero] at this;exact one_ne_zero this.symm)
  have hinv_star_u : 1 / T u = u := QJ θ
  have hy2_ne_nhds : ∀ᶠ v in 𝓝 u, zo v ≠ 0 := by
   have : ContinuousAt zo u := (Q6 u (Or.inr huU)).continuousWithinAt.continuousAt
    ((isOpen_ball.union zA).mem_nhds (Or.inr huU))
   exact this.eventually_ne hy2u
  have hy2_ψ : ∀ᶠ y in 𝓝 x, zo (ψ y) ≠ 0 := hψ_cont.eventually (by rwa [hψx])
  have hy2_inv_ψ : ∀ᶠ y in 𝓝 x, zo (1 / T (ψ y)) ≠ 0 := by
   have hc : ContinuousAt (fun y => 1 / T (ψ y)) x :=
    (by rw [hψx];exact hinv_star_cont : ContinuousAt (fun v : Z => 1 / T v) (ψ x)).comp hψ_cont
   exact hc.eventually (by dsimp only;rw [hψx, hinv_star_u];exact hy2_ne_nhds)
  have hli_inv : ∀ᶠ y in 𝓝 x, ψ (zp (1 / T (ψ y))) = 1 / T (ψ y) := by
   have hc : ContinuousAt (fun y => 1 / T (ψ y)) x :=
    (by rw [hψx];exact hinv_star_cont : ContinuousAt (fun v : Z => 1 / T v) (ψ x)).comp hψ_cont
   exact hc.eventually (by dsimp only;rw [hψx, hinv_star_u];exact hli)
  have hr_cont : ContinuousWithinAt (fun y => Kg (qL 1 y)) (qL 1 ⁻¹' T0) x := by
   have hr1_cont : ContinuousAt (qL 1) x :=
    (kB 1).continuousAt (isOpen_ball.mem_nhds hx.1)
   have hx_r : qL 1 x = x := (kc hx.1).2 hx1
   refine ContinuousWithinAt.comp (f := qL 1) (g := Kg) (s := qL 1 ⁻¹' T0) (t := T0)
    (by rw [hx_r];exact Kl x hx) hr1_cont.continuousWithinAt (fun _ hy => hy)
  have hli_zr : ∀ᶠ y in 𝓝[qL 1 ⁻¹' T0] x, ψ (zp (Kg (qL 1 y))) = Kg (qL 1 y) := by
   have hx_r : qL 1 x = x := (kc hx.1).2 hx1
   have hlim : Tendsto (fun y => Kg (qL 1 y)) (𝓝[qL 1 ⁻¹' T0] x) (𝓝 u) := by
    change Tendsto (fun y => Kg (qL 1 y)) (𝓝[qL 1 ⁻¹' T0] x) (𝓝 (Kg (qL 1 x))) at hr_cont;rw [hx_r, hu_zinv] at hr_cont;exact hr_cont
   exact hlim.eventually hli
  rw [eventually_nhdsWithin_iff] at hli_zr
  filter_upwards [hri, hψ_U1, hy2_ψ, hy2_inv_ψ, hli_inv, hli_zr] with
   y hy_ri hy_U1 hy2_1 hy2_2 hy_li1 hy_lizr _hy_ball hy_rT
  have hzmap_inv : zp (1 / T (ψ y)) = qL 1 y := by rw [Qy hy_U1 hy2_1 hy2_2, hy_ri]
  have hzinv_eq : Kg (qL 1 y) = 1 / T (ψ y) := by
   calc Kg (qL 1 y) = ψ (zp (Kg (qL 1 y))) := (hy_lizr hy_rT).symm
     _ = ψ (qL 1 y) := by rw [Ki hy_rT]
     _ = ψ (zp (1 / T (ψ y))) := by rw [hzmap_inv]
     _ = 1 / T (ψ y) := hy_li1
  have hf0_r : Kn (qL 1 y) = (zd : Z) * qX 1 (G y / (zd : Z)) := by
   dsimp [Kn, G];rw [hzinv_eq, Qz hy_U1]
  have hcAG : (zd : Z) ≠ 0 := ofReal_ne_zero.2 zf.ne'
  rw [hf0_r, show (zd : Z) * qX 1 (G y / (zd : Z)) / (zd : Z) = qX 1 (G y / (zd : Z)) by
   field_simp [hcAG], q0]
  field_simp [hcAG]
lemma Kt (i : Fin 3) {x : Z} (hx : x ∈ T0) (hxi : W (x - qH i) = R2)
  (hx_other : ∀ j ≠ i, R2 < W (x - qH j)) :
  ∃ G : Z → Z, AnalyticAt Z G x ∧
   (∀ᶠ y in 𝓝 x, y ∈ T0 → Kn y = G y) ∧
   (∀ᶠ y in 𝓝 x, y ∈ ball (0 : Z) 1 → qL i y ∈ T0 →
    (zd : Z) * qX i (Kn (qL i y) / (zd : Z)) = G y) := by
 have hω_ns : W ω = 1 := by rw [← Complex.sq_norm, qk];exact one_pow 2
 have hω_ne : ω ≠ 0 := by intro h;have := qk;rw [h, norm_zero] at this;exact one_ne_zero this.symm
 have hcAG_ne : (zd : Z) ≠ 0 := ofReal_ne_zero.2 zf.ne'
 fin_cases i <;> dsimp
 ·
  have hx1 : ω ^ 2 * x ∈ T0 := by rw [sq, mul_assoc];exact QD.2 (QD.2 hx)
  have hc01 : ω ^ 2 * qH 0 = qH 1 := by rw [sq, mul_assoc, QC.2.1, QC.2.2]
  have hc10 : ω ^ 2 * qH 1 = qH 2 := by rw [sq, mul_assoc, QC.1, QC.2.1]
  have hc20 : ω ^ 2 * qH 2 = qH 0 := by rw [sq, mul_assoc, QC.2.2, QC.1]
  have hs1 : W (ω ^ 2 * x - qH 1) = R2 := by rw [← hc01, ← mul_sub, normSq_mul, ← Complex.sq_norm, norm_pow, qk, one_pow, one_pow, one_mul];exact hxi
  have hs0 : R2 < W (ω ^ 2 * x - qH 0) := by
   rw [← hc20, ← mul_sub, normSq_mul, ← Complex.sq_norm, norm_pow, qk, one_pow, one_pow, one_mul]
   exact hx_other 2 (by decide)
  have hs2 : R2 < W (ω ^ 2 * x - qH 2) := by
   rw [← hc10, ← mul_sub, normSq_mul, ← Complex.sq_norm, norm_pow, qk, one_pow, one_pow, one_mul]
   exact hx_other 1 (by decide)
  obtain ⟨G1, hG1a, hG1_T0, hG1_r⟩ := Ks hx1 hs1 hs0 hs2
  refine ⟨fun y => ω * G1 (ω ^ 2 * y), ?_, ?_, ?_⟩
  · exact analyticAt_const.mul (hG1a.comp ((analyticAt_const.mul analyticAt_id)))
  ·
   have hc : ContinuousAt (fun y : Z => ω ^ 2 * y) x := continuousAt_const.mul continuousAt_id
   filter_upwards [hc.eventually hG1_T0] with y hy hyT
   have hy1 : ω ^ 2 * y ∈ T0 := by rw [sq, mul_assoc];exact QD.2 (QD.2 hyT)
   have hf_rot : Kn (ω ^ 2 * y) = ω ^ 2 * Kn y := by rw [sq, mul_assoc, Kr (QD.2 hyT), Kr hyT];ring
   rw [← hy hy1, hf_rot]
   calc Kn y = ω ^ 3 * Kn y := by rw [qj, one_mul]
     _ = ω * (ω ^ 2 * Kn y) := by ring
  ·
   have hc : ContinuousAt (fun y : Z => ω ^ 2 * y) x := continuousAt_const.mul continuousAt_id
   filter_upwards [hc.eventually hG1_r] with y hy hy_ball hyrT
   have hy1_ball : ω ^ 2 * y ∈ ball (0 : Z) 1 := by rw [mem_ball_zero_iff, norm_mul, norm_pow, qk, one_pow, one_mul];exact mem_ball_zero_iff.1 hy_ball
   have hr_rot : qL 1 (ω ^ 2 * y) = ω ^ 2 * qL 0 y := by
    have hr01 : qL 0 (ω * (ω ^ 2 * y)) = ω * qL 1 (ω ^ 2 * y) := (QA _).1
    have h3y : ω * (ω ^ 2 * y) = y := by calc ω * (ω ^ 2 * y) = ω ^ 3 * y := by ring
      _ = y := by rw [qj, one_mul]
    rw [h3y] at hr01
    calc qL 1 (ω ^ 2 * y) = ω ^ 2 * (ω * qL 1 (ω ^ 2 * y)) := by
          calc qL 1 (ω ^ 2 * y) = ω ^ 3 * qL 1 (ω ^ 2 * y) := by rw [qj, one_mul]
            _ = _ := by ring
      _ = ω ^ 2 * qL 0 y := by rw [hr01]
   have hyr1T : qL 1 (ω ^ 2 * y) ∈ T0 := by rw [hr_rot, sq, mul_assoc];exact QD.2 (QD.2 hyrT)
   have hG1 := hy hy1_ball hyr1T
   have hf_rot : Kn (qL 1 (ω ^ 2 * y)) = ω ^ 2 * Kn (qL 0 y) := by rw [hr_rot, sq, mul_assoc, Kr (QD.2 hyrT), Kr hyrT];ring
   have hρ_rot : qX 0 (Kn (qL 0 y) / (zd : Z)) =
     ω * qX 1 (ω ^ 2 * (Kn (qL 0 y) / (zd : Z))) := by
    have h1 := (QB (ω ^ 2 * (Kn (qL 0 y) / (zd : Z)))).1
    have h3 : ω * (ω ^ 2 * (Kn (qL 0 y) / (zd : Z))) = Kn (qL 0 y) / (zd : Z) := by
     calc _ = ω ^ 3 * (Kn (qL 0 y) / (zd : Z)) := by ring
       _ = _ := by rw [qj, one_mul]
    rwa [h3] at h1
   change (zd : Z) * qX 0 (Kn (qL 0 y) / (zd : Z)) = ω * G1 (ω ^ 2 * y)
   rw [hρ_rot, show ω ^ 2 * (Kn (qL 0 y) / (zd : Z)) = Kn (qL 1 (ω ^ 2 * y)) / (zd : Z) by
    rw [hf_rot];ring]
   rw [show (zd : Z) * (ω * qX 1 (Kn (qL 1 (ω ^ 2 * y)) / (zd : Z))) =
     ω * ((zd : Z) * qX 1 (Kn (qL 1 (ω ^ 2 * y)) / (zd : Z))) by ring, hG1]
 · exact Ks hx hxi (hx_other 0 (by decide)) (hx_other 2 (by decide))
 ·
  have hx1 : ω * x ∈ T0 := QD.2 hx
  have hs1 : W (ω * x - qH 1) = R2 := by rw [← QC.2.2, ← mul_sub, normSq_mul, hω_ns, one_mul];exact hxi
  have hs0 : R2 < W (ω * x - qH 0) := by rw [← QC.1, ← mul_sub, normSq_mul, hω_ns, one_mul];exact hx_other 1 (by decide)
  have hs2 : R2 < W (ω * x - qH 2) := by rw [← QC.2.1, ← mul_sub, normSq_mul, hω_ns, one_mul];exact hx_other 0 (by decide)
  obtain ⟨G1, hG1a, hG1_T0, hG1_r⟩ := Ks hx1 hs1 hs0 hs2
  refine ⟨fun y => ω ^ 2 * G1 (ω * y), ?_, ?_, ?_⟩
  · exact analyticAt_const.mul (hG1a.comp ((analyticAt_const.mul analyticAt_id)))
  ·
   have hc : ContinuousAt (fun y : Z => ω * y) x := continuousAt_const.mul continuousAt_id
   filter_upwards [hc.eventually hG1_T0] with y hy hyT
   have hy1 : ω * y ∈ T0 := QD.2 hyT;rw [← hy hy1, Kr hyT]
   calc Kn y = ω ^ 3 * Kn y := by rw [qj, one_mul]
     _ = ω ^ 2 * (ω * Kn y) := by ring
  ·
   have hc : ContinuousAt (fun y : Z => ω * y) x := continuousAt_const.mul continuousAt_id
   filter_upwards [hc.eventually hG1_r] with y hy hy_ball hyrT
   have hy1_ball : ω * y ∈ ball (0 : Z) 1 := by rw [mem_ball_zero_iff, norm_mul, qk, one_mul];exact mem_ball_zero_iff.1 hy_ball
   have hr_rot : qL 1 (ω * y) = ω * qL 2 y := by
    have hr21 : qL 2 (ω ^ 2 * (ω * y)) = ω ^ 2 * qL 1 (ω * y) := (QA _).2
    have h3y : ω ^ 2 * (ω * y) = y := by calc _ = ω ^ 3 * y := by ring
      _ = y := by rw [qj, one_mul]
    rw [h3y] at hr21
    calc qL 1 (ω * y) = ω * (ω ^ 2 * qL 1 (ω * y)) := by
          calc qL 1 (ω * y) = ω ^ 3 * qL 1 (ω * y) := by rw [qj, one_mul]
            _ = _ := by ring
      _ = ω * qL 2 y := by rw [hr21]
   have hyr1T : qL 1 (ω * y) ∈ T0 := by rw [hr_rot];exact QD.2 hyrT
   have hG1 := hy hy1_ball hyr1T
   have hf_rot : Kn (qL 1 (ω * y)) = ω * Kn (qL 2 y) := by rw [hr_rot, Kr hyrT]
   have hρ_rot : qX 2 (Kn (qL 2 y) / (zd : Z)) =
     ω ^ 2 * qX 1 (ω * (Kn (qL 2 y) / (zd : Z))) := by
    have h2 := (QB (ω * (Kn (qL 2 y) / (zd : Z)))).2
    have h3 : ω ^ 2 * (ω * (Kn (qL 2 y) / (zd : Z))) = Kn (qL 2 y) / (zd : Z) := by
     calc _ = ω ^ 3 * (Kn (qL 2 y) / (zd : Z)) := by ring
       _ = _ := by rw [qj, one_mul]
    rwa [h3] at h2
   change (zd : Z) * qX 2 (Kn (qL 2 y) / (zd : Z)) = ω ^ 2 * G1 (ω * y)
   rw [hρ_rot, show ω * (Kn (qL 2 y) / (zd : Z)) = Kn (qL 1 (ω * y)) / (zd : Z) by
    rw [hf_rot];ring]
   rw [show (zd : Z) * (ω ^ 2 * qX 1 (Kn (qL 1 (ω * y)) / (zd : Z))) =
     ω ^ 2 * ((zd : Z) * qX 1 (Kn (qL 1 (ω * y)) / (zd : Z))) by ring, hG1]
lemma Ku {u : Z} (hu : u ∈ closedBall (0 : Z) 1) :
  ‖zr u‖ ≤ zd ∧ (‖zr u‖ = zd ↔ u = 1 ∨ u = ω ∨ u = ω ^ 2) := by
 have hu1 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
 have hu3 : ‖u ^ 3‖ ≤ 1 := by rw [norm_pow];exact pow_le_one₀ (norm_nonneg u) hu1
 have hpre_pos : 0 < Gamma (4 / 3) / (Gamma (2 / 3) * Gamma (4 / 3 - 2 / 3)) := by
  have g1 := gP k5;have g2 := gP k4;have g3 := gP xx;positivity
 have hint_u := xQ (a := 1 / 3) (b := 2 / 3) (c := 4 / 3)
  k4 xx xy hu3
 have hint_1 := xQ (a := 1 / 3) (b := 2 / 3) (c := 4 / 3)
  k4 xx xy norm_one.le
 have hg1 : zq 1 = (xE (1 / 3) (2 / 3) (4 / 3) 1).re := by
  have hE := xM (a := 1 / 3) (b := 2 / 3) (c := 4 / 3)
   k4 xx xy xz
  dsimp [zq];rw [one_pow, one_mul, hE, ofReal_re]
 have hcAG_eq : zd = zc * (xE (1 / 3) (2 / 3) (4 / 3) 1).re := by
  have h1 : (zr 1).re = (zd : Z).re := congr_arg Complex.re z7;dsimp [zr] at h1;simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] at h1
  have hgre : (zq 1).re = (xE (1 / 3) (2 / 3) (4 / 3) 1).re := by
   have := congr_arg Complex.re hg1;simpa using this
  rw [hgre] at h1;exact h1.symm
 have hnorm_eq : ∀ t ∈ Ioo (0 : X) 1,
   ‖xD (1 / 3) (2 / 3) (4 / 3) (u ^ 3) t‖ =
    (t ^ (-1 / 3 : X) * (1 - t) ^ (-1 / 3 : X)) * ‖1 - u ^ 3 * (t : Z)‖ ^ (-1 / 3 : X) := by
  intro t ht;have ht0 : 0 < t := ht.1;have ht1 : 0 < 1 - t := sub_pos.2 ht.2;have hw_re : 0 < (1 - u ^ 3 * (t : Z)).re := xG hu3 ht0.le ht.2
  have hw_ne : 1 - u ^ 3 * (t : Z) ≠ 0 := by intro h;rw [h, zero_re] at hw_re;linarith
  have h1t : (1 : Z) - (t : Z) = ((1 - t : X) : Z) := by push_cast;rfl
  have hbase : (t : Z) ^ (((2 / 3 : X) : Z) - 1) * (1 - (t : Z)) ^ (((4 / 3 : X) : Z) - ((2 / 3 : X) : Z) - 1) =
    ((t ^ (-1 / 3 : X) * (1 - t) ^ (-1 / 3 : X) : X) : Z) := by
   rw [h1t, show (((2 / 3 : X) : Z) - 1) = ((-1 / 3 : X) : Z) by push_cast;ring,
    show (((4 / 3 : X) : Z) - ((2 / 3 : X) : Z) - 1) = ((-1 / 3 : X) : Z) by push_cast;ring,
    ← ofReal_cpow ht0.le, ← ofReal_cpow ht1.le, ofReal_mul]
  have hbase_nn : 0 ≤ t ^ (-1 / 3 : X) * (1 - t) ^ (-1 / 3 : X) := by positivity
  dsimp [xD]
  rw [norm_mul, hbase, Complex.norm_of_nonneg hbase_nn,
   show (-((1 / 3 : X) : Z)) = (-(1 / 3 : X) : Z) by push_cast;rfl,
   Qi hw_ne (1 / 3)]
  norm_num
 have hrhs_eq : ∀ t ∈ Ioo (0 : X) 1,
   (xD (1 / 3) (2 / 3) (4 / 3) 1 t).re =
    (t ^ (-1 / 3 : X) * (1 - t) ^ (-1 / 3 : X)) * (1 - t) ^ (-1 / 3 : X) := by
  intro t ht;have ht0 : 0 < t := ht.1;have ht1 : 0 < 1 - t := sub_pos.2 ht.2
  have h1t : (1 : Z) - (t : Z) = ((1 - t : X) : Z) := by push_cast;rfl
  have hbase : (t : Z) ^ (((2 / 3 : X) : Z) - 1) * (1 - (t : Z)) ^ (((4 / 3 : X) : Z) - ((2 / 3 : X) : Z) - 1) =
    ((t ^ (-1 / 3 : X) * (1 - t) ^ (-1 / 3 : X) : X) : Z) := by
   rw [h1t, show (((2 / 3 : X) : Z) - 1) = ((-1 / 3 : X) : Z) by push_cast;ring,
    show (((4 / 3 : X) : Z) - ((2 / 3 : X) : Z) - 1) = ((-1 / 3 : X) : Z) by push_cast;ring,
    ← ofReal_cpow ht0.le, ← ofReal_cpow ht1.le, ofReal_mul]
  dsimp [xD]
  rw [one_mul, hbase, show (-((1 / 3 : X) : Z)) = ((-1 / 3 : X) : Z) by push_cast;ring,
   h1t, ← ofReal_cpow ht1.le, ← ofReal_mul, ofReal_re]
 have hpt : ∀ t ∈ Ioo (0 : X) 1,
   ‖xD (1 / 3) (2 / 3) (4 / 3) (u ^ 3) t‖ ≤
    (xD (1 / 3) (2 / 3) (4 / 3) 1 t).re := by
  intro t ht;have ht0 : 0 < t := ht.1;have ht1 : 0 < 1 - t := sub_pos.2 ht.2
  have hw_ge : 1 - t ≤ ‖1 - u ^ 3 * (t : Z)‖ := by
   have htri := norm_sub_norm_le (1 : Z) (u ^ 3 * (t : Z))
   have hst : ‖u ^ 3 * (t : Z)‖ ≤ t := by rw [norm_mul, Complex.norm_of_nonneg ht0.le];exact mul_le_of_le_one_left ht0.le hu3
   simp only [norm_one] at htri;linarith
  have hpow_le : ‖1 - u ^ 3 * (t : Z)‖ ^ (-1 / 3 : X) ≤ (1 - t) ^ (-1 / 3 : X) := by
   rw [show (-1 / 3 : X) = -(1 / 3) by ring, rpow_neg (norm_nonneg _), rpow_neg ht1.le]
   exact inv_anti₀ (rpow_pos_of_pos ht1 _) (rpow_le_rpow ht1.le hw_ge k3.le)
  rw [hnorm_eq t ht, hrhs_eq t ht]
  exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
 have hE_le : ‖xE (1 / 3) (2 / 3) (4 / 3) (u ^ 3)‖ ≤
   (xE (1 / 3) (2 / 3) (4 / 3) 1).re :=
  Qw xA k4 xy hu3
 have hle : ‖zr u‖ ≤ zd := by
  dsimp [zr, zq];rw [norm_mul, norm_mul, Complex.norm_of_nonneg ze.le, hcAG_eq]
  refine mul_le_mul_of_nonneg_left ?_ ze.le
  calc ‖u‖ * ‖xE (1 / 3) (2 / 3) (4 / 3) (u ^ 3)‖
      ≤ 1 * (xE (1 / 3) (2 / 3) (4 / 3) 1).re :=
        mul_le_mul hu1 hE_le (norm_nonneg _) zero_le_one
    _ = _ := one_mul _
 refine ⟨hle, ?_⟩
 constructor
 ·
  intro heq
  have hE_pos : 0 < (xE (1 / 3) (2 / 3) (4 / 3) 1).re := by
   have hE := xM (a := 1 / 3) (b := 2 / 3) (c := 4 / 3)
    k4 xx xy xz
   rw [hE, ofReal_re];have g1 := gP k5;have g2 := gP xy;have g3 := gP xz;have g4 := gP xx;positivity
  have hu_one : ‖u‖ = 1 := by
   by_contra hne
   have hlt : ‖u‖ < 1 := lt_of_le_of_ne hu1 hne
   have hlt' : ‖zr u‖ < zd := by
    dsimp [zr, zq];rw [norm_mul, norm_mul, Complex.norm_of_nonneg ze.le, hcAG_eq]
    refine mul_lt_mul_of_pos_left ?_ ze
    calc ‖u‖ * ‖xE (1 / 3) (2 / 3) (4 / 3) (u ^ 3)‖
        ≤ ‖u‖ * (xE (1 / 3) (2 / 3) (4 / 3) 1).re :=
          mul_le_mul_of_nonneg_left hE_le (norm_nonneg _)
      _ < 1 * (xE (1 / 3) (2 / 3) (4 / 3) 1).re :=
          mul_lt_mul_of_pos_right hlt hE_pos
      _ = _ := one_mul _
   linarith
  have hu3_one : u ^ 3 = 1 := by
   by_contra hu3_ne
   have hmid_lt : ‖xD (1 / 3) (2 / 3) (4 / 3) (u ^ 3) (1 / 2)‖ <
     (xD (1 / 3) (2 / 3) (4 / 3) 1 (1 / 2)).re := by
    have hre_lt : (u ^ 3).re < 1 := by
     have hns : W (u ^ 3) = 1 := by rw [← Complex.sq_norm, norm_pow, hu_one, one_pow, one_pow]
     have hle1 : (u ^ 3).re ≤ 1 := by
      calc (u ^ 3).re ≤ ‖u ^ 3‖ := re_le_norm _
        _ = 1 := by rw [norm_pow, hu_one, one_pow]
     rcases lt_or_eq_of_le hle1 with h | h
     · exact h
     ·
      exfalso;apply hu3_ne
      rw [normSq_apply, h] at hns
      exact Complex.ext (by simpa using h) (by simp only [one_im];nlinarith only [hns])
    have hgt : (1 / 2 : X) < ‖1 - u ^ 3 * ((1 / 2 : X) : Z)‖ := by
     have hsq : (1 / 2 : X) ^ 2 < ‖1 - u ^ 3 * ((1 / 2 : X) : Z)‖ ^ 2 := by
      rw [Complex.sq_norm]
      have hns : W (u ^ 3) = 1 := by rw [← Complex.sq_norm, norm_pow, hu_one, one_pow, one_pow]
      simp only [normSq_apply, sub_re, sub_im, mul_re,
       mul_im, one_re, one_im, ofReal_re, ofReal_im,
       mul_zero, sub_zero] at hns ⊢
      nlinarith only [hns, hre_lt]
     nlinarith only [hsq, norm_nonneg (1 - u ^ 3 * ((1 / 2 : X) : Z))]
    have hpow_lt : ‖1 - u ^ 3 * ((1 / 2 : X) : Z)‖ ^ (-1 / 3 : X) <
      (1 - (1 / 2 : X)) ^ (-1 / 3 : X) := by
     rw [show (-1 / 3 : X) = -(1 / 3) by ring, rpow_neg (norm_nonneg _), rpow_neg (by norm_num)]
     exact inv_strictAnti₀ (by positivity) (Real.rpow_lt_rpow (by norm_num) (by linarith) (by norm_num))
    rw [hnorm_eq (1 / 2) ⟨by norm_num, by norm_num⟩, hrhs_eq (1 / 2) ⟨by norm_num, by norm_num⟩]
    exact mul_lt_mul_of_pos_left hpow_lt (by positivity)
   let diff : X → X := fun t =>
    (xD (1 / 3) (2 / 3) (4 / 3) 1 t).re -
     ‖xD (1 / 3) (2 / 3) (4 / 3) (u ^ 3) t‖
   have hdiff_cont : ContinuousOn diff (Icc (1 / 4 : X) (3 / 4)) := by
    let g_r : X → X := fun t => (t ^ (-1 / 3 : X) * (1 - t) ^ (-1 / 3 : X)) * (1 - t) ^ (-1 / 3 : X)
    let g_u : X → X := fun t =>
     (t ^ (-1 / 3 : X) * (1 - t) ^ (-1 / 3 : X)) * ‖1 - u ^ 3 * (t : Z)‖ ^ (-1 / 3 : X)
    have hg_eq : EqOn diff (fun t => g_r t - g_u t) (Icc (1 / 4 : X) (3 / 4)) := fun t ht => by
     have ht01 : t ∈ Ioo (0 : X) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
     dsimp [diff, g_r, g_u];rw [hrhs_eq t ht01, hnorm_eq t ht01]
    refine ContinuousOn.congr ?_ hg_eq
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht1 : 1 - t ≠ 0 := by linarith [ht.2]
    have hwu : ‖1 - u ^ 3 * (t : Z)‖ ≠ 0 := by
     have hpos := xG (t := t) hu3 (by linarith [ht.1]) (by linarith [ht.2])
     intro h0;rw [norm_eq_zero] at h0;rw [h0, zero_re] at hpos;linarith
    have c1 : ContinuousAt (fun t : X => t ^ (-1 / 3 : X)) t :=
     continuousAt_id.rpow continuousAt_const (Or.inl ht0)
    have c2 : ContinuousAt (fun t : X => (1 - t) ^ (-1 / 3 : X)) t :=
     (continuousAt_const.sub continuousAt_id).rpow continuousAt_const (Or.inl ht1)
    have c3 : ContinuousAt (fun t : X => ‖1 - u ^ 3 * (t : Z)‖ ^ (-1 / 3 : X)) t :=
     (continuous_const.sub (continuous_const.mul continuous_ofReal)).norm.continuousAt.rpow
      continuousAt_const (Or.inl hwu)
    exact (((c1.mul c2).mul c2).sub ((c1.mul c2).mul c3)).continuousWithinAt
   have hpos_sub : 0 < ∫ t in (1 / 4 : X)..(3 / 4), diff t :=
    intervalIntegral.integral_pos (by norm_num) hdiff_cont
     (fun t ht => sub_nonneg.2 (hpt t ⟨by linarith [ht.1], by linarith [ht.2]⟩))
     ⟨1 / 2,⟨by norm_num,by norm_num⟩,sub_pos.2 hmid_lt⟩
   have hint_1_re : IntervalIntegrable (fun t => (xD (1 / 3) (2 / 3) (4 / 3) 1 t).re) volume 0 1 :=
    ⟨reCLM.integrable_comp hint_1.1,reCLM.integrable_comp hint_1.2⟩
   have h_int_full : IntervalIntegrable diff volume 0 1 := hint_1_re.sub hint_u.norm
   have hmono := intervalIntegral.integral_mono_interval (by norm_num : (0 : X) ≤ 1 / 4)
    (by norm_num : (1 / 4 : X) ≤ 3 / 4) (by norm_num : (3 / 4 : X) ≤ 1)
    (by
     rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
     filter_upwards with t ht
     rcases eq_or_lt_of_le ht.2 with rfl | ht1
     ·
      dsimp [diff, xD]
      have hz : (0 : Z) ^ ((4 / 3 : Z) - 2 / 3 - 1) = 0 := zero_cpow (by norm_num)
      simp only [ofReal_div,ofReal_ofNat,one_cpow,sub_self,one_mul,mul_one,one_div,ofReal_inv,ne_eq,neg_eq_zero,inv_eq_zero,OfNat.ofNat_ne_zero,not_false_eq_true,zero_cpow,mul_zero,zero_re,Complex.norm_mul,zero_sub,Left.nonneg_neg_iff,ge_iff_le];rw [hz];simp only [norm_zero,zero_mul,Std.le_refl]
     · exact sub_nonneg.2 (hpt t ⟨ht.1, ht1⟩))
    h_int_full
   have hfull_eq : ∫ t in (0 : X)..1, diff t =
     (∫ t in Ioo (0 : X) 1, (xD (1 / 3) (2 / 3) (4 / 3) 1 t).re) -
     (∫ t in Ioo (0 : X) 1, ‖xD (1 / 3) (2 / 3) (4 / 3) (u ^ 3) t‖) := by
    rw [intervalIntegral.integral_sub hint_1_re hint_u.norm,
     integral_of_le zero_le_one, integral_of_le zero_le_one,
     integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
   have hE_lt : ‖xE (1 / 3) (2 / 3) (4 / 3) (u ^ 3)‖ <
     (xE (1 / 3) (2 / 3) (4 / 3) 1).re := by
    dsimp [xE]
    rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
     norm_mul, Complex.norm_of_nonneg hpre_pos.le]
    refine mul_lt_mul_of_pos_left ?_ hpre_pos
    have hre1 : (∫ t in (0 : X)..1, xD (1 / 3) (2 / 3) (4 / 3) 1 t).re =
      ∫ t in (0 : X)..1, (xD (1 / 3) (2 / 3) (4 / 3) 1 t).re :=
     (reCLM.intervalIntegral_comp_comm hint_1).symm
    rw [hre1, integral_of_le zero_le_one, integral_of_le zero_le_one]
    calc ‖∫ t in Ioc (0 : X) 1, xD (1 / 3) (2 / 3) (4 / 3) (u ^ 3) t‖
        ≤ ∫ t in Ioc (0 : X) 1, ‖xD (1 / 3) (2 / 3) (4 / 3) (u ^ 3) t‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ t in Ioo (0 : X) 1, ‖xD (1 / 3) (2 / 3) (4 / 3) (u ^ 3) t‖ :=
          integral_Ioc_eq_integral_Ioo
      _ < ∫ t in Ioo (0 : X) 1, (xD (1 / 3) (2 / 3) (4 / 3) 1 t).re := by linarith
      _ = ∫ t in Ioc (0 : X) 1, (xD (1 / 3) (2 / 3) (4 / 3) 1 t).re :=
          integral_Ioc_eq_integral_Ioo.symm
   have hlt_cAG : ‖zr u‖ < zd := by
    dsimp [zr, zq];rw [norm_mul, norm_mul, Complex.norm_of_nonneg ze.le, hcAG_eq, hu_one, one_mul];exact mul_lt_mul_of_pos_left hE_lt ze
   linarith
  have hfac : (u - 1) * (u - ω) * (u - ω ^ 2) = 0 := by
   have hid : (u - 1) * (u - ω) * (u - ω ^ 2) =
     (u - 1) * (u ^ 2 - (ω + ω ^ 2) * u + ω ^ 3) := by ring
   rw [hid, qj, show ω + ω ^ 2 = -1 by linear_combination qi]
   linear_combination sub_eq_zero.2 hu3_one
  rcases mul_eq_zero.1 hfac with h12 | h3
  ·
   rcases mul_eq_zero.1 h12 with h1 | h2
   · exact Or.inl (sub_eq_zero.1 h1)
   · exact Or.inr (Or.inl (sub_eq_zero.1 h2))
  · exact Or.inr (Or.inr (sub_eq_zero.1 h3))
 ·
  rintro (rfl | rfl | rfl)
  · rw [z7, Complex.norm_of_nonneg zf.le]
  ·
   rw [show ω = ω * 1 by ring, Qg, norm_mul, qk, one_mul, z7,
    Complex.norm_of_nonneg zf.le]
  ·
   rw [show ω ^ 2 = ω * (ω * 1) by ring, Qg, Qg, norm_mul, norm_mul,
    qk, one_mul, one_mul, z7, Complex.norm_of_nonneg zf.le]
def Kv (w : Z) : Prop :=
 ∃ m n : ℤ, w = 1 + (m : Z) * (ω - 1) + (n : Z) * (ω ^ 2 - 1)
lemma Kw {w : Z} (hw : Kv w) (hnorm : ‖w‖ ≤ 1) :
  w = 1 ∨ w = ω ∨ w = ω ^ 2 := by
 obtain ⟨m, n, rfl⟩ := hw;have h3 : Y 3 ^ 2 = 3 := qc
 have hns : W (1 + (m : Z) * (ω - 1) + (n : Z) * (ω ^ 2 - 1)) ≤ 1 := by rw [← Complex.sq_norm];nlinarith only [norm_nonneg (1 + (m : Z) * (ω - 1) + (n : Z) * (ω ^ 2 - 1)), hnorm]
 have hre : (1 + (m : Z) * (ω - 1) + (n : Z) * (ω ^ 2 - 1)).re = 1 - 3 / 2 * ((m : X) + n) := by
  simp only [add_re, one_re, mul_re, intCast_re, intCast_im,
   sub_re, sub_im, qg, qh, zero_mul, sub_zero]
  have hω2re : (ω ^ 2).re = -1 / 2 := by simp only [ω,sq,mul_re];linear_combination (-1 / 4 : X) * h3
  rw [hω2re];ring
 have him : (1 + (m : Z) * (ω - 1) + (n : Z) * (ω ^ 2 - 1)).im = Y 3 * ((m : X) - n) / 2 := by
  simp only [add_im, one_im, mul_im, intCast_re, intCast_im,
   sub_re, sub_im, qg, qh, zero_mul, add_zero]
  have hω2im : (ω ^ 2).im = -Y 3 / 2 := by simp only [ω,sq,mul_im];ring
  rw [hω2im];ring
 have h4 : 3 * (2 * m + n - 1) ^ 2 + (3 * n - 1) ^ 2 ≤ 4 := by
  have hr : (4 : X) * W (1 + (m : Z) * (ω - 1) + (n : Z) * (ω ^ 2 - 1)) ≤ 4 := by linarith only [hns]
  rw [normSq_apply, hre, him] at hr
  have hr' : (3 * (2 * (m : X) + n - 1) ^ 2 + (3 * (n : X) - 1) ^ 2) ≤ 4 := by nlinarith only [h3, hr]
  exact_mod_cast hr'
 have hsq_n : (3 * n - 1) ^ 2 ≤ 2 ^ 2 := by nlinarith only [sq_nonneg (2 * m + n - 1), h4]
 have hn_bd : -2 ≤ 3 * n - 1 ∧ 3 * n - 1 ≤ 2 := abs_le_of_sq_le_sq' hsq_n (by norm_num)
 have hm_bd : (2 * m + n - 1) ^ 2 ≤ 1 := by nlinarith only [sq_nonneg (3 * n - 1), h4]
 have hn01 : n = 0 ∨ n = 1 := by omega
 rcases hn01 with rfl | rfl
 ·
  have hsq_m : (2 * m - 1) ^ 2 ≤ 1 ^ 2 := by nlinarith only [hm_bd]
  have hm_abs : -1 ≤ 2 * m - 1 ∧ 2 * m - 1 ≤ 1 := abs_le_of_sq_le_sq' hsq_m (by norm_num)
  have hm01 : m = 0 ∨ m = 1 := by omega
  rcases hm01 with rfl | rfl
  · left;simp only [Int.cast_zero,zero_mul,add_zero]
  · right;left;simp only [Int.cast_one,one_mul,add_sub_cancel,Int.cast_zero,zero_mul,add_zero]
 ·
  have hm_abs : -0 ≤ 2 * m ∧ 2 * m ≤ 0 := abs_le_of_sq_le_sq' (by nlinarith only [h4] : (2 * m) ^ 2 ≤ 0 ^ 2) le_rfl
  have hm0 : m = 0 := by omega
  subst hm0;right;right;simp only [Int.cast_zero,zero_mul,add_zero,Int.cast_one,one_mul,add_sub_cancel]
lemma Kx {u : Z} (hu : u ∈ closedBall (0 : Z) 1) :
  Kv (zr u / (zd : Z)) ↔ u = 1 ∨ u = ω ∨ u = ω ^ 2 := by
 constructor
 ·
  intro hw
  have hnorm : ‖zr u / (zd : Z)‖ ≤ 1 := by
   rw [norm_div, Complex.norm_of_nonneg zf.le, div_le_one zf];exact (Ku hu).1
  rcases Kw hw hnorm with heq | heq | heq
  ·
   have hnorm1 : ‖zr u‖ = zd := by
    have h := congr_arg (fun z : Z => ‖z‖ * zd) heq
    rw [norm_div, Complex.norm_of_nonneg zf.le, div_mul_cancel₀ _ zf.ne',
     norm_one, one_mul] at h
    exact h
   exact (Ku hu).2.1 hnorm1
  ·
   have hnorm1 : ‖zr u‖ = zd := by
    have h := congr_arg (fun z : Z => ‖z‖ * zd) heq
    rw [norm_div, Complex.norm_of_nonneg zf.le, div_mul_cancel₀ _ zf.ne',
     qk, one_mul] at h
    exact h
   exact (Ku hu).2.1 hnorm1
  ·
   have hnorm1 : ‖zr u‖ = zd := by
    have h := congr_arg (fun z : Z => ‖z‖ * zd) heq
    rw [norm_div, Complex.norm_of_nonneg zf.le, div_mul_cancel₀ _ zf.ne',
     norm_pow, qk, one_pow, one_mul] at h
    exact h
   exact (Ku hu).2.1 hnorm1
 ·
  rintro (rfl | rfl | rfl)
  ·
   rw [z7, div_self (ofReal_ne_zero.2 zf.ne')]
   exact ⟨0, 0, by simp only [Int.cast_zero,zero_mul,add_zero]⟩
  ·
   rw [show ω = ω * 1 by ring, Qg, z7, mul_div_cancel_right₀ _
    (ofReal_ne_zero.2 zf.ne')]
   exact ⟨1, 0, by simp only [Int.cast_one,one_mul,add_sub_cancel,Int.cast_zero,zero_mul,add_zero]⟩
  ·
   rw [show ω ^ 2 = ω * (ω * 1) by ring, Qg, Qg, z7,
    show ω * (ω * (zd : Z)) / (zd : Z) = ω ^ 2 by
     field_simp [ofReal_ne_zero.2 zf.ne']]
   exact ⟨0, 1, by simp only [Int.cast_zero,zero_mul,add_zero,Int.cast_one,one_mul,add_sub_cancel]⟩
lemma Ky {x : Z} (hx : x ∈ T0) :
  Kv (Kn x / (zd : Z)) ↔ ∃ k : Fin 3, x = j5 k := by
 dsimp [Kn];rw [Kx (Kh hx)];constructor
 ·
  rintro (h | h | h)
  · exact ⟨0, by rw [← Ki hx, h, Qu.1]⟩
  · exact ⟨2, by rw [← Ki hx, h, Qu.2.2]⟩
  · exact ⟨1, by rw [← Ki hx, h, Qu.2.1]⟩
 ·
  rintro ⟨k, rfl⟩
  fin_cases k <;> dsimp
  · left;rw [← Qu.1, Kj (by simp only [mem_closedBall,dist_zero_right,norm_one,Std.le_refl])]
  · right;right;rw [← Qu.2.1, Kj (by rw [mem_closedBall, dist_zero_right, norm_pow, qk, one_pow])]
  · right;left;rw [← Qu.2.2, Kj (by rw [mem_closedBall, dist_zero_right, qk])]
lemma Kz (i : Fin 3) {w : Z} (hw : Kv w) :
  Kv (qX i w) := by
 obtain ⟨m, n, rfl⟩ := hw;have hc : T ω = ω ^ 2 := ql;have hc2 : T (ω ^ 2) = ω := qY;have hid : ω ^ 2 + ω + 1 = 0 := qi
 fin_cases i
 ·
  refine ⟨1 - n, 1 - m, ?_⟩
  simp only [qX,map_add,map_one,map_mul,map_sub,map_intCast,hc,hc2];push_cast;linear_combination -hid
 ·
  refine ⟨m + n, -n, ?_⟩
  simp only [qX,map_add,map_one,map_mul,map_sub,map_intCast,hc,hc2];push_cast;linear_combination -hid - (m : Z) * qj
 ·
  refine ⟨-m, m + n, ?_⟩
  simp only [qX,map_add,map_one,map_mul,map_sub,map_intCast,hc,hc2];push_cast;linear_combination -hid - (m : Z) * qZ - (n : Z) * qj
lemma KA (w : List (Fin 3)) {ζ : Z} (hζ : Kv ζ) :
  Kv (js w ζ) := by
 induction w with
 | nil => exact hζ
 | cons a w ih => exact Kz a ih
end
end BlochAG
namespace BlochAG
noncomputable section
lemma KB (k : Fin 3) : Kn (j5 k) / (zd : Z) = j4 k := by
 have hcAG : (zd : Z) ≠ 0 := ofReal_ne_zero.2 zf.ne';dsimp [Kn]
 fin_cases k <;> dsimp
 · rw [← Qu.1, Kj (by simp only [mem_closedBall,dist_zero_right,norm_one,Std.le_refl]), z7, div_self hcAG];rfl
 ·
  rw [← Qu.2.1, Kj (by rw [mem_closedBall, dist_zero_right, norm_pow, qk, one_pow]),
   show ω ^ 2 = ω * (ω * 1) by ring, Qg, Qg, z7]
  simp only [j4];field_simp [hcAG]
 ·
  rw [← Qu.2.2, Kj (by rw [mem_closedBall, dist_zero_right, qk]),
   show ω = ω * 1 by ring, Qg, z7]
  simp only [j4];field_simp [hcAG]
lemma KC (i : Fin 3) {x : Z} (hx : x ∈ T0) (hxi : W (x - qH i) = R2) :
  qX i (Kn x / (zd : Z)) = Kn x / (zd : Z) := by
 have hcAG : (zd : Z) ≠ 0 := ofReal_ne_zero.2 zf.ne'
 have hside1 : ∀ y ∈ T0, W (y - qH 1) = R2 →
   qX 1 (Kn y / (zd : Z)) = Kn y / (zd : Z) := by
  intro y hy hy1;obtain ⟨θ, hθ, hθeq⟩ := Q1 hy hy1
  rcases eq_or_lt_of_le hθ.1 with rfl | h0'
  ·
   rw [QK, Qu.1] at hθeq;rw [← hθeq, KB 0]
   exact j8 1 0 (by decide)
  ·
   rcases eq_or_lt_of_le hθ.2 with rfl | h1'
   ·
    rw [QL, Qu.2.2] at hθeq;rw [← hθeq, KB 2]
    exact j8 1 2 (by decide)
   ·
    have huU : QG θ ∈ zy := QN h0' h1'
    have hzinv : Kg y = QG θ := by rw [← hθeq, Kj (QI θ)]
    have hgf : Kn y = zr (QG θ) := by dsimp [Kn];rw [hzinv]
    have hg := Qz huU;rw [QJ] at hg;have hg' := congr_arg (fun z : Z => z / (zd : Z)) hg;rw [mul_div_cancel_left₀ _ hcAG] at hg';rw [hgf];exact hg'.symm
 have hω_ns : W ω = 1 := by rw [← Complex.sq_norm, qk];exact one_pow 2
 fin_cases i <;> dsimp
 ·
  have hx1 : ω ^ 2 * x ∈ T0 := by rw [sq, mul_assoc];exact QD.2 (QD.2 hx)
  have hc01 : ω ^ 2 * qH 0 = qH 1 := by rw [sq, mul_assoc, QC.2.1, QC.2.2]
  have hs1 : W (ω ^ 2 * x - qH 1) = R2 := by rw [← hc01, ← mul_sub, normSq_mul, ← Complex.sq_norm, norm_pow, qk, one_pow, one_pow, one_mul];exact hxi
  have h1 := hside1 (ω ^ 2 * x) hx1 hs1
  have hf_rot : Kn (ω ^ 2 * x) = ω ^ 2 * Kn x := by rw [sq, mul_assoc, Kr (QD.2 hx), Kr hx];ring
  rw [hf_rot, mul_div_assoc] at h1;have hρ := (QB (ω ^ 2 * (Kn x / (zd : Z)))).1
  have h3 : ω * (ω ^ 2 * (Kn x / (zd : Z))) = Kn x / (zd : Z) := by
   calc _ = ω ^ 3 * (Kn x / (zd : Z)) := by ring
     _ = _ := by rw [qj, one_mul]
  rw [h3] at hρ;rw [hρ, h1];exact h3
 · exact hside1 x hx hxi
 ·
  have hx1 : ω * x ∈ T0 := QD.2 hx
  have hs1 : W (ω * x - qH 1) = R2 := by rw [← QC.2.2, ← mul_sub, normSq_mul, hω_ns, one_mul];exact hxi
  have h1 := hside1 (ω * x) hx1 hs1;have hf_rot : Kn (ω * x) = ω * Kn x := Kr hx;rw [hf_rot, mul_div_assoc] at h1;have hρ := (QB (ω * (Kn x / (zd : Z)))).2
  have h3 : ω ^ 2 * (ω * (Kn x / (zd : Z))) = Kn x / (zd : Z) := by
   calc _ = ω ^ 3 * (Kn x / (zd : Z)) := by ring
     _ = _ := by rw [qj, one_mul]
  rw [h3] at hρ;rw [hρ, h1];exact h3
noncomputable def KD (z : Z) : List (Fin 3) :=
 @dite _ (z ∈ ball (0 : Z) 1) (Classical.propDecidable _)
  (fun hz => Classical.choose (j2 z hz)) (fun _ => [])
lemma KE {z : Z} (hz : z ∈ ball (0 : Z) 1) : jr (KD z) z ∈ T0 := by
 dsimp [KD];rw [dif_pos hz];exact Classical.choose_spec (j2 z hz)
noncomputable def KF (z : Z) : Z :=
 (zd : Z) * js (KD z).reverse (Kn (jr (KD z) z) / (zd : Z))
lemma KG {i j k : Fin 3} (hik : i ≠ k) (hjk : j ≠ k) :
  ∀ w₀ : List (Fin 3), (∀ a ∈ w₀, a = i ∨ a = j) → js w₀ (j4 k) = j4 k := by
 intro w₀ hlet
 induction w₀ with
 | nil => rfl
 | cons a w ih =>
  simp only [js];rw [ih (fun b hb => hlet b (List.mem_cons_of_mem a hb))]
  rcases hlet a List.mem_cons_self with ha | ha <;> rw [ha]
  · exact j8 i k hik
  · exact j8 j k hjk
lemma KH {w : List (Fin 3)} {z : Z} (hz : z ∈ ball (0 : Z) 1) (hw : jr w z ∈ T0) :
  KF z = (zd : Z) * js w.reverse (Kn (jr w z) / (zd : Z)) := by
 dsimp [KF];congr 1;have htw := KE hz;obtain ⟨hx_eq, w₀, _, _, hc_eq, hcls⟩ := k1 hz htw hw;let x := jr w z
 have hfix : js w₀ (Kn x / (zd : Z)) = Kn x / (zd : Z) := by
  rcases hcls with rfl | ⟨i, rfl, hside⟩ | ⟨i, j, k, _, hik, hjk, hxv, hlet⟩
  · rfl
  · exact KC i hw hside
  ·
   change jr w z = j5 k at hxv
   have hfvert : Kn x / (zd : Z) = j4 k := by dsimp [x];rw [hxv];exact KB k
   rw [hfvert];exact KG hik hjk w₀ hlet
 have hstep2 := hc_eq (Kn x / (zd : Z));rw [hfix, ju] at hstep2;have hfin := congr_arg (js (KD z).reverse) hstep2;rw [jx] at hfin;rw [hx_eq];exact hfin.symm
lemma KI (w : List (Fin 3)) : Continuous (js w) := by
 induction w with
 | nil => exact continuous_id
 | cons a w ih =>
  have hρ : Continuous (qX a) := by
   fin_cases a <;> dsimp [qX]
   · exact continuous_const.sub continuous_conj
   · exact continuous_const.sub (continuous_const.mul continuous_conj)
   · exact continuous_const.sub (continuous_const.mul continuous_conj)
  exact hρ.comp ih
lemma KJ : ContinuousOn KF (ball (0 : Z) 1) := by
 rw [continuousOn_iff_continuous_domRestrict];rw [continuous_iff_continuousAt];intro ⟨z, hz⟩
 have hball_nhds : ∃ r : X, 0 ≤ r ∧ r < 1 ∧ closedBall (0 : Z) r ∈ 𝓝 z := by
  let r : X := (‖z‖ + 1) / 2
  have hr0 : 0 ≤ r := by dsimp [r];positivity
  have hz1 : ‖z‖ < 1 := by rwa [mem_ball_zero_iff] at hz
  have hr1 : r < 1 := by dsimp [r];linarith
  have hzr : ‖z‖ < r := by dsimp [r];linarith
  have hnhds : closedBall (0 : Z) r ∈ 𝓝 z := by
   refine mem_of_superset (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hzr)) ball_subset_closedBall
  exact ⟨r, hr0, hr1, hnhds⟩
 obtain ⟨r, hr0, hr1, hnhds⟩ := hball_nhds;obtain ⟨F, hF⟩ := j3 hr0 hr1;let P : List (Fin 3) → Set Z := fun w => closedBall (0 : Z) r ∩ jr w '' T0
 have hP_closed : ∀ w : List (Fin 3), IsClosed (P w) := fun w => by
  refine isClosed_closedBall.inter ?_
  exact (kA.image_of_continuousOn
   ((kC w).mono fun _ hx => hx.1)).isClosed
 have hP_cont : ∀ w : List (Fin 3), ContinuousOn KF (P w) := fun w => by
  have heq : EqOn KF (fun u => (zd : Z) * js w (Kn (jr w.reverse u) / (zd : Z))) (P w) := by
   intro u hu
   have hu_ball : u ∈ ball (0 : Z) 1 := by rw [mem_ball_zero_iff];exact (mem_closedBall_zero_iff.1 hu.1).trans_lt hr1
   obtain ⟨x, hxT, rfl⟩ := hu.2;have hwx : jr w.reverse (jr w x) = x := jw w hxT.1
   rw [KH hu_ball (by rw [hwx];exact hxT), List.reverse_reverse]
  refine ContinuousOn.congr ?_ heq
  have hsub : P w ⊆ ball (0 : Z) 1 := fun u hu => by
   rw [mem_ball_zero_iff];exact (mem_closedBall_zero_iff.1 hu.1).trans_lt hr1
  refine continuousOn_const.mul ((KI w).continuousOn.comp ?_ fun _ _ => mem_univ _)
  refine (Ko.comp ((kC w.reverse).mono hsub) ?_).div_const _
  rintro u hu;obtain ⟨x, hxT, rfl⟩ := hu.2;rw [jw w hxT.1];exact hxT
 have hU_cont : ContinuousOn KF (⋃ w ∈ F, P w) := by
  clear hF
  induction F using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty,iUnion_of_empty,iUnion_empty,continuousOn_empty]
  | @insert w F' _ ih =>
   rw [Finset.set_biUnion_insert];exact (hP_cont w).union_of_isClosed ih (hP_closed w)
    (isClosed_biUnion_finset fun w' _ => hP_closed w')
 have hcb_sub : closedBall (0 : Z) r ⊆ ⋃ w ∈ F, P w := by
  intro u hu
  have hu_ball : u ∈ ball (0 : Z) 1 := by rw [mem_ball_zero_iff];exact (mem_closedBall_zero_iff.1 hu).trans_lt hr1
  have htw := KE hu_ball
  have hnorm_rev : ‖jr (KD u).reverse (jr (KD u) u)‖ ≤ r := by
   rw [jw (KD u) hu_ball];exact mem_closedBall_zero_iff.1 hu
  obtain ⟨w₀, hw₀, hw₀_eq⟩ := hF (KD u).reverse (jr (KD u) u) htw hnorm_rev
  refine mem_iUnion₂.2 ⟨w₀, hw₀, hu, jr (KD u) u, htw, ?_⟩
  rw [← hw₀_eq _ htw.1, jw (KD u) hu_ball]
 have hcb_cont : ContinuousOn KF (closedBall (0 : Z) r) := hU_cont.mono hcb_sub;have hAt : ContinuousAt KF z := hcb_cont.continuousAt hnhds;exact hAt.comp continuousAt_subtype_val
def KK (i : Fin 3) (w : Z) : Z :=
 (qH i * w - 1) / (w - T (qH i))
lemma KL (i : Fin 3) (z : Z) : qL i z = KK i (T z) := rfl
lemma KM {i : Fin 3} {w : Z} (hw : w ∈ ball (0 : Z) 1) :
  w - T (qH i) ≠ 0 := by
 intro h;have h1 : w = T (qH i) := sub_eq_zero.1 h;rw [mem_ball_zero_iff, h1, norm_conj, qJ] at hw;have ht1 : 1 < tR := qs;linarith
lemma KN {i : Fin 3} {w : Z} (hw : w - T (qH i) ≠ 0) :
  HasDerivAt (KK i) (-(R2 : Z) / (w - T (qH i)) ^ 2) w := by
 have hnum : HasDerivAt (fun x : Z => qH i * x - 1) (qH i) w := by simpa using ((hasDerivAt_id w).const_mul (qH i)).sub_const 1
 have hden : HasDerivAt (fun x : Z => x - T (qH i)) 1 w :=
  (hasDerivAt_id w).sub_const _
 refine (hnum.div hden hw).congr_deriv ?_
 have hc2 : qH i * T (qH i) = (tR ^ 2 : Z) := by rw [mul_conj, Complex.normSq_eq_norm_sq, qJ];push_cast;ring
 have hR2 : (R2 : Z) = (tR ^ 2 : Z) - 1 := by dsimp [R2];push_cast;ring
 rw [hR2]
 calc (qH i * (w - T (qH i)) - (qH i * w - 1) * 1) / (w - T (qH i)) ^ 2
     = (1 - qH i * T (qH i)) / (w - T (qH i)) ^ 2 := by ring
   _ = -((tR ^ 2 : Z) - 1) / (w - T (qH i)) ^ 2 := by rw [hc2];ring
lemma KO (w : List (Fin 3)) :
  (w.length % 2 = 0 → DifferentiableOn Z (jr w) (ball (0 : Z) 1)) ∧
  (w.length % 2 = 1 → DifferentiableOn Z (T ∘ jr w) (ball (0 : Z) 1)) := by
 induction w with
 | nil => exact ⟨fun _ => differentiableOn_id, fun h => by simp only [List.length_nil,Nat.zero_mod,zero_ne_one] at h⟩
 | cons a w ih =>
  rcases Nat.mod_two_eq_zero_or_one w.length with hw0 | hw1
  ·
   have ih0 := ih.1 hw0;constructor
   · intro h;simp only [List.length_cons] at h;omega
   ·
    intro _ z hz;have hwa : DifferentiableAt Z (jr w) z := (ih0 z hz).differentiableAt (isOpen_ball.mem_nhds hz);have hmem : jr w z ∈ ball (0 : Z) 1 := jv w hz
    have hd_conj : T (jr w z) - T (qH a) ≠ 0 := by
     refine KM ?_;simpa [mem_ball_zero_iff] using hmem
    have hr_diff : DifferentiableAt Z (KK a) (T (jr w z)) :=
     (KN hd_conj).differentiableAt
    have hcc : DifferentiableAt Z (T ∘ KK a ∘ T) (jr w z) := by
     have h := hr_diff.conj_conj;rwa [starRingEnd_self_apply] at h
    have heq : (T ∘ jr (a :: w)) = (T ∘ KK a ∘ T) ∘ jr w := rfl;rw [heq];exact (hcc.comp z hwa).differentiableWithinAt
  ·
   have ih1 := ih.2 hw1;constructor
   ·
    intro _ z hz
    have hwa : DifferentiableAt Z (T ∘ jr w) z :=
     (ih1 z hz).differentiableAt (isOpen_ball.mem_nhds hz)
    have hmem : jr w z ∈ ball (0 : Z) 1 := jv w hz
    have hd_conj : T (jr w z) - T (qH a) ≠ 0 := by
     refine KM ?_;simpa [mem_ball_zero_iff] using hmem
    have hr_diff : DifferentiableAt Z (KK a) (T (jr w z)) :=
     (KN hd_conj).differentiableAt
    have heq : jr (a :: w) = KK a ∘ (T ∘ jr w) := rfl;rw [heq];exact (hr_diff.comp z hwa).differentiableWithinAt
   · intro h;simp only [List.length_cons] at h;omega
def KP : Fin 3 → Z
 | 0 => -1
 | 1 => -ω
 | 2 => -ω ^ 2
def KQ : Fin 3 → Z
 | 0 => -1
 | 1 => -ω ^ 2
 | 2 => -ω
lemma KR (a : Fin 3) (ζ : Z) : qX a ζ = KP a * T ζ + KQ a := by fin_cases a <;> simp only [qX,KP,neg_mul,one_mul,KQ] <;> ring
lemma KS (a : Fin 3) : KP a ^ 3 = -1 := by
 fin_cases a
 · dsimp [KP];ring
 ·
  dsimp [KP];calc (-ω) ^ 3 = -(ω ^ 3) := by ring
     _ = -1 := by rw [qj]
 ·
  dsimp [KP];calc (-ω ^ 2) ^ 3 = -(ω ^ 3) ^ 2 := by ring
     _ = -1 := by rw [qj];ring
lemma KT (w : List (Fin 3)) :
  (w.length % 2 = 0 → ∃ A B : Z, A ^ 3 = 1 ∧ ∀ ζ : Z, js w ζ = A * ζ + B) ∧
  (w.length % 2 = 1 → ∃ A B : Z, A ^ 3 = -1 ∧ ∀ ζ : Z, js w ζ = A * T ζ + B) := by
 induction w with
 | nil => exact ⟨fun _ => ⟨1, 0, one_pow 3, fun ζ => by simp only [js,one_mul,add_zero]⟩, fun h => by simp only [List.length_nil,Nat.zero_mod,zero_ne_one] at h⟩
 | cons a w ih =>
  rcases Nat.mod_two_eq_zero_or_one w.length with hw0 | hw1
  ·
   obtain ⟨A, B, hA, hform⟩ := ih.1 hw0;constructor
   · intro h;simp only [List.length_cons] at h;omega
   ·
    intro _
    refine ⟨KP a * T A, KP a * T B + KQ a, ?_, fun ζ => ?_⟩
    · rw [mul_pow, ← map_pow, hA, map_one, mul_one, KS]
    · simp only [js,KR,hform,map_add,map_mul];ring
  ·
   obtain ⟨A, B, hA, hform⟩ := ih.2 hw1;constructor
   ·
    intro _
    refine ⟨KP a * T A, KP a * T B + KQ a, ?_, fun ζ => ?_⟩
    · rw [mul_pow, ← map_pow, hA, map_neg, map_one, KS];ring
    · simp only [js,KR,hform,map_add,map_mul,starRingEnd_self_apply];ring
   · intro h;simp only [List.length_cons] at h;omega
lemma KU {z : Z} (hz : z ∈ ball (0 : Z) 1)
  (hnot : ∀ k : Fin 3, jr (KD z) z ≠ j5 k) :
  DifferentiableAt Z KF z := by
 let w := KD z;let x := jr w z;have hxT0 : x ∈ T0 := KE hz
 have hG_exists : ∃ G : Z → Z, AnalyticAt Z G x ∧
   (∀ᶠ y in 𝓝 x, y ∈ T0 → Kn y = G y) ∧
   (∀ᶠ z' in 𝓝 z, KF z' = (zd : Z) * js w.reverse (G (jr w z') / (zd : Z))) := by
  by_cases hx_int : x ∈ qU
  ·
   refine ⟨Kn, ?_, Eventually.of_forall fun _ _ => rfl, ?_⟩
   · exact (Complex.analyticOnNhd_iff_differentiableOn Q5).2 Kp x hx_int
   ·
    have hcont : ContinuousAt (jr w) z := (kC w).continuousAt (isOpen_ball.mem_nhds hz);have hnhds : ∀ᶠ z' in 𝓝 z, jr w z' ∈ qU := hcont.eventually (Q5.mem_nhds hx_int)
    filter_upwards [isOpen_ball.mem_nhds hz, hnhds] with z' hz' hx'
    exact KH hz' (qW hx')
  ·
   have hnot_int : ¬ ∀ i : Fin 3, R2 < W (x - qH i) := fun h => hx_int ⟨hxT0.1, h⟩;push Not at hnot_int;obtain ⟨i, hi⟩ := hnot_int;have hxi : W (x - qH i) = R2 := le_antisymm hi (hxT0.2 i)
   have hx_other : ∀ j ≠ i, R2 < W (x - qH j) := by
    intro j hji
    rcases lt_or_eq_of_le (hxT0.2 j) with hlt | heq
    · exact hlt
    ·
     exfalso
     rcases (by fin_cases i <;> fin_cases j <;> first | exact absurd rfl hji | decide :
      ∃ k : Fin 3, i ≠ k ∧ j ≠ k) with ⟨k, hik, hjk⟩
     exact hnot k (ke hji.symm hik hjk hxT0 hxi heq.symm)
   obtain ⟨G, hGa, hGT0, hGr⟩ := Kt i hxT0 hxi hx_other
   refine ⟨G, hGa, hGT0, ?_⟩
   have hcont : ContinuousAt (jr w) z := (kC w).continuousAt (isOpen_ball.mem_nhds hz)
   have hothers : ∀ᶠ y in 𝓝 x, ∀ j ≠ i, R2 < W (y - qH j) := by
    have hopen_o : IsOpen { y : Z | ∀ j ≠ i, R2 < W (y - qH j) } := by
     have : { y : Z | ∀ j ≠ i, R2 < W (y - qH j) } =
       ⋂ j ∈ ({0, 1, 2} : Finset (Fin 3)).filter (· ≠ i), { y : Z | R2 < W (y - qH j) } := by
      ext y;simp only [mem_ofPred_eq,mem_iInter,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton];constructor
      · intro h j hj;exact h j hj.2
      · intro h j hj;exact h j ⟨by fin_cases j <;> simp only [Fin.zero_eta,Fin.isValue,zero_ne_one,Fin.reduceEq,or_self,or_false,Fin.mk_one,one_ne_zero,or_true,Fin.reduceFinMk], hj⟩
     rw [this]
     exact isOpen_biInter_finset fun j _ =>
      isOpen_lt continuous_const (continuous_normSq.comp (continuous_id.sub continuous_const))
    exact hopen_o.mem_nhds hx_other
   have hball_y : ∀ᶠ y in 𝓝 x, y ∈ ball (0 : Z) 1 := isOpen_ball.mem_nhds hxT0.1;have hr_cont : ContinuousAt (qL i) x := (kB i).continuousAt (isOpen_ball.mem_nhds hxT0.1);have hxr : qL i x = x := (kc hxT0.1).2 hxi
   have hr_others : ∀ᶠ y in 𝓝 x, ∀ j ≠ i, R2 < W (qL i y - qH j) := by
    have hopen_o : IsOpen { y : Z | ∀ j ≠ i, R2 < W (y - qH j) } := by
     have : { y : Z | ∀ j ≠ i, R2 < W (y - qH j) } =
       ⋂ j ∈ ({0, 1, 2} : Finset (Fin 3)).filter (· ≠ i), { y : Z | R2 < W (y - qH j) } := by
      ext y;simp only [mem_ofPred_eq,mem_iInter,Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton];constructor
      · intro h j hj;exact h j hj.2
      · intro h j hj;exact h j ⟨by fin_cases j <;> simp only [Fin.zero_eta,Fin.isValue,zero_ne_one,Fin.reduceEq,or_self,or_false,Fin.mk_one,one_ne_zero,or_true,Fin.reduceFinMk], hj⟩
     rw [this]
     exact isOpen_biInter_finset fun j _ =>
      isOpen_lt continuous_const (continuous_normSq.comp (continuous_id.sub continuous_const))
    exact hr_cont.eventually (by rw [hxr];exact hopen_o.mem_nhds hx_other)
   have hmain_y : ∀ᶠ y in 𝓝 x,
     (y ∈ T0 ∧ Kn y = G y) ∨
     (y ∈ ball (0 : Z) 1 ∧ qL i y ∈ T0 ∧ (zd : Z) * qX i (Kn (qL i y) / (zd : Z)) = G y) := by
    filter_upwards [hball_y, hothers, hr_others, hGT0, hGr] with y hyb hyo hyro hyT hyr
    by_cases hyi : R2 ≤ W (y - qH i)
    ·
     have hyT0 : y ∈ T0 := ⟨hyb, fun j => by by_cases hj : j = i;subst hj;exact hyi;exact (hyo j hj).le⟩
     exact Or.inl ⟨hyT0, hyT hyT0⟩
    ·
     rw [not_le] at hyi;have hry_ball : qL i y ∈ ball (0 : Z) 1 := qN hyb
     have hsub_id : qL i y - qH i = (R2 : Z) / (T y - T (qH i)) := by
      dsimp [qL]
      have hc2 : qH i * T (qH i) = (tR ^ 2 : Z) := by rw [mul_conj, Complex.normSq_eq_norm_sq, qJ];push_cast;ring
      have hden := qM (i := i) hyb;field_simp [hden]
      rw [show qH i * T y - 1 - qH i * (T y - T (qH i)) =
        qH i * T (qH i) - 1 by ring, hc2]
      dsimp [R2];push_cast;ring
     have hry_ns : W (qL i y - qH i) = R2 ^ 2 / W (y - qH i) := by rw [hsub_id, normSq_div, normSq_ofReal, ← sq, ← map_sub, normSq_conj]
     have hden_pos : 0 < W (y - qH i) := by
      by_contra h0
      have hle0 : W (y - qH i) ≤ 0 := not_lt.1 h0;have heq0 : y = qH i := sub_eq_zero.1 (normSq_eq_zero.1 (le_antisymm hle0 (normSq_nonneg _)));have hyn : ‖y‖ < 1 := mem_ball_zero_iff.1 hyb;rw [heq0, qJ] at hyn;nlinarith only [qs, hyn]
     have hry_i : R2 ≤ W (qL i y - qH i) := by rw [hry_ns, le_div_iff₀ hden_pos];nlinarith only [hyi, qu]
     have hry_T0 : qL i y ∈ T0 := ⟨hry_ball, fun j => by by_cases hj : j = i;subst hj;exact hry_i;exact (hyro j hj).le⟩
     exact Or.inr ⟨hyb, hry_T0, hyr hyb hry_T0⟩
   filter_upwards [isOpen_ball.mem_nhds hz, hcont.eventually hmain_y] with z' hz' hy
   rcases hy with ⟨hyT0, hyG⟩ | ⟨_, hryT0, hyrG⟩
   · rw [KH hz' hyT0, hyG]
   ·
    have hw1 : jr (i :: w) z' ∈ T0 := hryT0;rw [KH hz' hw1];have hcAG : (zd : Z) ≠ 0 := ofReal_ne_zero.2 zf.ne'
    have hevc : js (i :: w).reverse (Kn (jr (i :: w) z') / (zd : Z)) =
      js w.reverse (qX i (Kn (qL i (jr w z')) / (zd : Z))) := by
     rw [List.reverse_cons, ju];rfl
    rw [hevc]
    have hG_div : qX i (Kn (qL i (jr w z')) / (zd : Z)) = G (jr w z') / (zd : Z) := by rw [← hyrG];field_simp [hcAG]
    rw [hG_div]
 obtain ⟨G, hGa, _, hf_eq⟩ := hG_exists;have hw_rev_len : w.reverse.length = w.length := List.length_reverse (as := w)
 have hDiff_comp : DifferentiableAt Z (fun z' => (zd : Z) * js w.reverse (G (jr w z') / (zd : Z))) z := by
  rcases Nat.mod_two_eq_zero_or_one w.length with hw0 | hw1
  ·
   have hw_rev0 : w.reverse.length % 2 = 0 := by rw [hw_rev_len];exact hw0
   obtain ⟨A, B, _, hA⟩ := (KT w.reverse).1 hw_rev0;have hG_diff : DifferentiableAt Z G (jr w z) := hGa.differentiableAt
   have hev_diff : DifferentiableAt Z (jr w) z :=
    ((KO w).1 hw0 z hz).differentiableAt (isOpen_ball.mem_nhds hz)
   have heq_f : (fun z' => (zd : Z) * js w.reverse (G (jr w z') / (zd : Z))) =
     (fun z' => (zd : Z) * (A * (G (jr w z') / (zd : Z)) + B)) := by
    funext z';rw [hA]
   rw [heq_f];exact (((((hG_diff.comp z hev_diff).div_const _).const_mul A).add_const B).const_mul _)
  ·
   have hw_rev1 : w.reverse.length % 2 = 1 := by rw [hw_rev_len];exact hw1
   obtain ⟨A, B, _, hA⟩ := (KT w.reverse).2 hw_rev1;have hcAG : (zd : Z) ≠ 0 := ofReal_ne_zero.2 zf.ne'
   have hG_conj : DifferentiableAt Z (T ∘ G ∘ T) (T x) :=
    hGa.differentiableAt.conj_conj
   have hev_conj : DifferentiableAt Z (T ∘ jr w) z :=
    ((KO w).2 hw1 z hz).differentiableAt (isOpen_ball.mem_nhds hz)
   have heq_f : (fun z' => (zd : Z) * js w.reverse (G (jr w z') / (zd : Z))) =
     (fun z' => (zd : Z) * (A * ((T ∘ G ∘ T) ((T ∘ jr w) z') / (zd : Z)) + B)) := by
    funext z'
    rw [hA, map_div₀, conj_ofReal];dsimp only [Function.comp_apply];rw [starRingEnd_self_apply]
   rw [heq_f];exact ((((((hG_conj.comp z hev_conj).div_const _).const_mul A).add_const B).const_mul _))
 exact hDiff_comp.congr_of_eventuallyEq hf_eq
lemma KV : DifferentiableOn Z KF (ball (0 : Z) 1) := by
 intro z hz
 by_cases hnot : ∀ k : Fin 3, jr (KD z) z ≠ j5 k
 · exact (KU hz hnot).differentiableWithinAt
 ·
  push Not at hnot;obtain ⟨k, hk⟩ := hnot;let w := KD z
  have hcont_at : ContinuousAt KF z :=
   KJ.continuousAt (isOpen_ball.mem_nhds hz)
  have hpunct : ∀ᶠ z' in 𝓝[≠] z, DifferentiableAt Z KF z' := by
   have hz_lt : ‖z‖ < 1 := mem_ball_zero_iff.1 hz;let r : X := (‖z‖ + 1) / 2
   have hr0 : 0 ≤ r := by dsimp [r];positivity
   have hr1 : r < 1 := by dsimp [r];linarith
   have hcb_nhds : closedBall (0 : Z) r ∈ 𝓝 z :=
    mem_of_superset (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by dsimp [r];linarith))) ball_subset_closedBall
   obtain ⟨F, hF⟩ := j3 hr0 hr1;let badPts : Finset Z := F.biUnion fun w' => Finset.univ.image fun j : Fin 3 => jr w' (j5 j);let S_fin : Set Z := ↑badPts \ {z};have hS_closed : IsClosed S_fin := (badPts.finite_toSet.subset sdiff_subset).isClosed;have hz_not_S : z ∉ S_fin := fun h => h.2 rfl
   have h_avoid : ∀ᶠ z' in 𝓝[≠] z, z' ∈ ball (0 : Z) 1 ∧ z' ∈ closedBall (0 : Z) r ∧ z' ∉ badPts := by
    have h1 : ∀ᶠ z' in 𝓝[≠] z, z' ∈ ball (0 : Z) 1 := nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz);have h2 : ∀ᶠ z' in 𝓝[≠] z, z' ∈ closedBall (0 : Z) r := nhdsWithin_le_nhds hcb_nhds
    have h3 : ∀ᶠ z' in 𝓝[≠] z, z' ∉ badPts := by
     have ho : S_finᶜ ∈ 𝓝 z := hS_closed.isOpen_compl.mem_nhds hz_not_S
     filter_upwards [nhdsWithin_le_nhds ho, self_mem_nhdsWithin] with z' hzS hzne hzb
     exact hzS ⟨hzb, hzne⟩
    exact h1.and (h2.and h3)
   filter_upwards [h_avoid] with z' ⟨hz'b, hz'cb, hz'nb⟩
   refine KU hz'b (fun j hj => ?_)
   apply hz'nb
   have htw := KE hz'b
   have hnorm_rev : ‖jr (KD z').reverse (jr (KD z') z')‖ ≤ r := by
    rw [jw (KD z') hz'b];exact mem_closedBall_zero_iff.1 hz'cb
   obtain ⟨w₀, hw₀, hw₀_eq⟩ := hF (KD z').reverse (jr (KD z') z') htw hnorm_rev
   refine Finset.mem_biUnion.2 ⟨w₀, hw₀, ?_⟩
   refine Finset.mem_image.2 ⟨j, Finset.mem_univ j, ?_⟩
   rw [← hj, ← hw₀_eq _ htw.1, jw (KD z') hz'b]
  exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hpunct hcont_at).differentiableAt.differentiableWithinAt
lemma KW : deriv KF 0 = 1 := by
 have hcAG : (zd : Z) ≠ 0 := ofReal_ne_zero.2 zf.ne'
 have heq : ∀ᶠ z in 𝓝 (0 : Z), KF z = Kn z := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos),
   (Q5.mem_nhds qV)] with z hzb hzi
  have h1 := KH (w := []) hzb (qW hzi);simpa [jr, js, mul_div_cancel₀ _ hcAG] using h1
 have h0 := (Kp 0 qV).differentiableAt
  (Q5.mem_nhds qV) |>.hasDerivAt
 rw [Kq] at h0;exact (h0.congr_of_eventuallyEq heq).deriv
lemma KX {i j k : Fin 3} (hij : i < j) (hik : i ≠ k) (hjk : j ≠ k) :
  (deriv (fun u => qL i (qL j u)) (j5 k)) ^ 3 = -1 := by
 have hd_val : ∀ (a b c : Fin 3), a ≠ c → b ≠ c →
   HasDerivAt (fun u => qL a (qL b u))
    ((R2 : Z) ^ 2 / (T (j5 c - qH a) * (j5 c - qH b)) ^ 2) (j5 c) := by
  intro a b c hac hbc;let g : Z → Z := T ∘ KK b ∘ T;have hvc : j5 c ∈ ball (0 : Z) 1 := j7 c
  have hden_b : T (j5 c) - T (qH b) ≠ 0 :=
   KM (by simpa [mem_ball_zero_iff] using hvc)
  have hdb := (KN hden_b).conj_conj
  have hg_d : HasDerivAt g (-(R2 : Z) / (j5 c - qH b) ^ 2) (j5 c) := by
   have hss : T (T (j5 c)) = j5 c := starRingEnd_self_apply _
   have hsc : T (-(R2 : Z) / (T (j5 c) - T (qH b)) ^ 2) =
     -(R2 : Z) / (j5 c - qH b) ^ 2 := by
    simp only [map_div₀,map_neg,conj_ofReal,map_pow,map_sub,starRingEnd_self_apply]
   rw [hss, hsc] at hdb;exact hdb
  have hg_at : g (j5 c) = T (j5 c) := by dsimp [g];rw [← KL, kd hbc]
  have hden_a : g (j5 c) - T (qH a) ≠ 0 := by rw [hg_at];exact KM (by simpa [mem_ball_zero_iff] using hvc)
  have hda := KN (i := a) hden_a;have hda' : HasDerivAt (KK a) (-(R2 : Z) / (T (j5 c) - T (qH a)) ^ 2)
    (g (j5 c)) := by
   convert hda using 2
   rw [hg_at]
  refine ((hda'.comp (j5 c) hg_d).congr_deriv ?_)
  rw [← map_sub, div_mul_div_comm, neg_mul_neg, ← mul_pow];ring
 have h_inv_val : ∀ (a b c : Fin 3), a ≠ c → b ≠ c →
   deriv (fun u => qL a (qL b u)) (j5 c) *
    deriv (fun u => qL b (qL a u)) (j5 c) = 1 := by
  intro a b c hac hbc;have hd1 := hd_val a b c hac hbc;have hd2 := hd_val b a c hbc hac
  have hr_at : qL b (qL a (j5 c)) = j5 c := by rw [kd hac, kd hbc]
  have hd1' : HasDerivAt (fun u => qL a (qL b u))
    (deriv (fun u => qL a (qL b u)) (j5 c)) (qL b (qL a (j5 c))) := by
   rw [hr_at];exact hd1.congr_deriv hd1.deriv.symm
  have hd2' : HasDerivAt (fun u => qL b (qL a u))
    (deriv (fun u => qL b (qL a u)) (j5 c)) (j5 c) :=
   hd2.congr_deriv hd2.deriv.symm
  have hcomp : HasDerivAt ((fun u => qL a (qL b u)) ∘ (fun u => qL b (qL a u)))
    (deriv (fun u => qL a (qL b u)) (j5 c) *
     deriv (fun u => qL b (qL a u)) (j5 c)) (j5 c) :=
   hd1'.comp (j5 c) hd2'
  have hid_ev : ∀ᶠ u in 𝓝 (j5 c), ((fun u => qL a (qL b u)) ∘ (fun u => qL b (qL a u))) u = id u := by
   filter_upwards [isOpen_ball.mem_nhds (j7 c)] with u hu
   dsimp [Function.comp_apply, id];rw [qO (qN hu), qO hu]
  exact hcomp.unique ((hasDerivAt_id (j5 c)).congr_of_eventuallyEq hid_ev)
 have h120 : (deriv (fun u => qL 1 (qL 2 u)) (j5 0)) ^ 3 = -1 := by
  rw [(hd_val 1 2 0 (by decide) (by decide)).deriv]
  have hc12 : T (j5 0 - qH 1) = j5 0 - qH 2 := by simp only [map_sub,j5,j4,mul_one,conj_ofReal,QF]
  have hns : W (j5 0 - qH 1) = R2 := kb (by decide)
  have hmul_bar : (j5 0 - qH 1) * T (j5 0 - qH 1) = (R2 : Z) := by rw [mul_conj, hns]
  have hsimp : (R2 : Z) ^ 2 / (T (j5 0 - qH 1) * (j5 0 - qH 2)) ^ 2 =
    ((j5 0 - qH 1) / (j5 0 - qH 2)) ^ 2 := by
   rw [hc12, ← hmul_bar, hc12]
   have hne : j5 0 - qH 2 ≠ 0 := by
    intro h0;have := kb (i := 2) (k := 0) (by decide)
    rw [h0, normSq_zero] at this;linarith [qu]
   field_simp [hne]
  rw [hsimp];let ζ : Z := ⟨Y 3 / 2, 1 / 2⟩
  have hζ3 : ζ ^ 3 = I := by
   have h3 : Y 3 ^ 2 = 3 := qc;apply Complex.ext
   ·
    simp only [one_div,pow_succ,pow_zero,one_mul,mul_re,mul_im,I_re,ζ];ring_nf
    rw [show Y 3 ^ 3 = Y 3 * Y 3 ^ 2 by ring, h3];ring
   ·
    simp only [one_div,pow_succ,pow_zero,one_mul,mul_im,mul_re,I_im,ζ];ring_nf;rw [h3];norm_num
  have hζ6 : ζ ^ 6 = -1 := by rw [show (6 : ℕ) = 3 * 2 by rfl, pow_mul, hζ3];simp only [I_sq]
  have h3 : Y 3 ^ 2 = 3 := qc
  have hw_sq : ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) ^ 2 = ζ := by
   have hsub : j5 0 - qH 1 = (-(qv : Z) * qy 1) * ⟨(tR - σ / 2) / qv, σ * Y 3 / (2 * qv)⟩ := by
    have hw0 : QP (j5 0) = ⟨(tR - σ / 2) / qv, σ * Y 3 / (2 * qv)⟩ :=
     Complex.ext QS.1 QS.2
    have hz_eq : j5 0 = qH 1 - (qv : Z) * qy 1 * QP (j5 0) := by
     dsimp [QP, qH]
     have hd1 : qy 1 * T (qy 1) = 1 := by simp only [Fin.isValue,mul_conj',qz,ofReal_one,one_pow]
     rw [mul_assoc (qv : Z), mul_comm (qy 1) _, ← mul_assoc,
      mul_div_cancel₀ _ (ofReal_ne_zero.2 qw.ne')]
     linear_combination -j5 0 * hd1
    rw [hz_eq, hw0];ring
   have hden_ne : -(qv : Z) * qy 1 ≠ 0 := by
    refine mul_ne_zero (neg_ne_zero.2 (ofReal_ne_zero.2 qw.ne')) ?_
    intro h;have := qz 1;rw [h, norm_zero] at this;exact one_ne_zero this.symm
   rw [hsub, mul_div_cancel_left₀ _ hden_ne]
   have hst : σ * tR = σ ^ 2 + 1 := by dsimp [tR];field_simp [qn.ne']
   apply Complex.ext
   ·
    simp only [sq,mul_re,ζ]
    rw [show ((tR - σ / 2) / qv * ((tR - σ / 2) / qv) -
      σ * Y 3 / (2 * qv) * (σ * Y 3 / (2 * qv))) =
      (tR ^ 2 - σ * tR - σ ^ 2 / 2) / R2 by
     rw [← qx];field_simp [qw.ne'];nlinarith only [h3]]
    rw [qr, hst, qo, qt]
    have h13 : (0 : X) < 1 + Y 3 := by positivity
    field_simp [h13.ne'];nlinarith only [h3]
   ·
    simp only [sq,mul_im,ζ]
    rw [show ((tR - σ / 2) / qv * (σ * Y 3 / (2 * qv)) +
      σ * Y 3 / (2 * qv) * ((tR - σ / 2) / qv)) =
      (σ * tR - σ ^ 2 / 2) * Y 3 / R2 by
     rw [← qx];field_simp [qw.ne'];ring]
    rw [hst, qo, qt]
    have h13 : (0 : X) < 1 + Y 3 := by positivity
    field_simp [h13.ne'];nlinarith only [h3]
  have hratio : (j5 0 - qH 1) / (j5 0 - qH 2) = ω * ζ := by
   have hden_ne : j5 0 - qH 2 ≠ 0 := by
    intro h0;have := kb (i := 2) (k := 0) (by decide)
    rw [h0, normSq_zero] at this;linarith [qu]
   have hden_c : -(qv : Z) * qy 1 ≠ 0 := by
    refine mul_ne_zero (neg_ne_zero.2 (ofReal_ne_zero.2 qw.ne')) ?_
    intro h;have := qz 1;rw [h, norm_zero] at this;exact one_ne_zero this.symm
   have hconj_w : (j5 0 - qH 2) / (-(qv : Z) * qy 2) =
     T ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) := by
    rw [map_div₀, map_mul, map_neg, conj_ofReal, hc12]
    have hd : T (qy 1) = qy 2 := by simp only [qy,map_neg,qY]
    rw [hd]
   have hratio_w : ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) /
     ((j5 0 - qH 2) / (-(qv : Z) * qy 2)) =
     ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) ^ 2 := by
    have hns1 : W ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) = 1 := by
     rw [normSq_div, normSq_mul, normSq_neg, normSq_ofReal,
      qA, mul_one, ← sq, qx, kb (by decide), div_self qu.ne']
    have hmul1 : ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) *
      T ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) = 1 := by
     rw [mul_conj, hns1, ofReal_one]
    have hne_s : T ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) ≠ 0 := by intro h;rw [h, mul_zero] at hmul1;norm_num at hmul1
    rw [hconj_w, div_eq_iff hne_s]
    calc (j5 0 - qH 1) / (-(qv : Z) * qy 1)
        = ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) * 1 := (mul_one _).symm
      _ = ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) *
          (((j5 0 - qH 1) / (-(qv : Z) * qy 1)) *
            T ((j5 0 - qH 1) / (-(qv : Z) * qy 1))) := by rw [hmul1]
      _ = ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) ^ 2 *
          T ((j5 0 - qH 1) / (-(qv : Z) * qy 1)) := by ring
   rw [hw_sq] at hratio_w
   have hdir_div : qy 1 / qy 2 = ω := by dsimp [qy];field_simp [show ω ≠ 0 from fun h => by have := qk;rw [h, norm_zero] at this;exact one_ne_zero this.symm]
   have hd1_ne : qy 1 ≠ 0 := fun h => by have := qz 1;rw [h, norm_zero] at this;exact one_ne_zero this.symm
   have hd2_ne : qy 2 ≠ 0 := fun h => by have := qz 2;rw [h, norm_zero] at this;exact one_ne_zero this.symm
   have hrad_ne : (qv : Z) ≠ 0 := ofReal_ne_zero.2 qw.ne'
   have hdiv : (j5 0 - qH 1) / (j5 0 - qH 2) =
     (qy 1 / qy 2) * (((j5 0 - qH 1) / (-(qv : Z) * qy 1)) /
      ((j5 0 - qH 2) / (-(qv : Z) * qy 2))) := by
    field_simp [hden_ne, hd1_ne, hd2_ne, hrad_ne]
   rw [hdiv, hdir_div, hratio_w]
  rw [hratio, ← pow_mul, show 2 * 3 = 6 by rfl, mul_pow,
   show ω ^ 6 = (ω ^ 3) ^ 2 by ring, qj, one_pow, one_mul, hζ6]
 have hrot_eq : ∀ (a' b' c' a b c : Fin 3),
   a' ≠ c' → b' ≠ c' → a ≠ c → b ≠ c →
   ω * qH a = qH a' → ω * qH b = qH b' → ω * j5 c = j5 c' →
   deriv (fun u => qL a' (qL b' u)) (j5 c') =
    deriv (fun u => qL a (qL b u)) (j5 c) := by
  intro a' b' c' a b c ha' hb' ha hb hca hcb hvc;rw [(hd_val a' b' c' ha' hb').deriv, (hd_val a b c ha hb).deriv];congr 1;rw [← hvc, ← hca, ← hcb, ← mul_sub, ← mul_sub, map_mul]
  have hω_mul : T ω * ω = 1 := by simp only [conj_mul',qk,ofReal_one,one_pow]
  rw [show (T ω * T (j5 c - qH a)) * (ω * (j5 c - qH b)) =
    (T ω * ω) * (T (j5 c - qH a) * (j5 c - qH b)) by ring,
   hω_mul, one_mul]
 have hvc02 : ω * j5 0 = j5 2 := by simp only [j5,j4,mul_one];ring
 have hvc21 : ω * j5 2 = j5 1 := by simp only [j5,j4];ring
 have h012 : deriv (fun u => qL 0 (qL 1 u)) (j5 2) =
   deriv (fun u => qL 1 (qL 2 u)) (j5 0) :=
  hrot_eq 0 1 2 1 2 0 (by decide) (by decide) (by decide) (by decide)
   QC.1 QC.2.2 hvc02
 have h201 : deriv (fun u => qL 2 (qL 0 u)) (j5 1) =
   deriv (fun u => qL 0 (qL 1 u)) (j5 2) :=
  hrot_eq 2 0 1 0 1 2 (by decide) (by decide) (by decide) (by decide)
   QC.2.1 QC.1 hvc21
 fin_cases i <;> fin_cases j <;> fin_cases k <;> dsimp at * <;> try contradiction
 · rw [h012];exact h120
 ·
  have hinv := h_inv_val 0 2 1 (by decide) (by decide)
  rw [h201, h012] at hinv;have hpow := congr_arg (fun z : Z => z ^ 3) hinv;rw [mul_pow, h120, one_pow] at hpow;linear_combination -hpow
 · exact h120
lemma KY {w : List (Fin 3)} {z : Z} {i j k : Fin 3}
  (hz : z ∈ ball (0 : Z) 1) (hij : i < j) (hik : i ≠ k) (hjk : j ≠ k)
  (hx : jr w z = j5 k) :
  (deriv (jr (w.reverse ++ [i, j] ++ w)) z) ^ 3 = -1 := by
 let rot : Z → Z := fun u => qL i (qL j u)
 have h_eq : ∀ u : Z, jr (w.reverse ++ [i, j] ++ w) u = jr w.reverse (rot (jr w u)) := by
  intro u;rw [List.append_assoc, jt, jt];rfl
 have h_rot_diff : DifferentiableAt Z rot (j5 k) := by
  have heq : rot = KK i ∘ (T ∘ KK j ∘ T) := rfl;rw [heq];have hvc : j5 k ∈ ball (0 : Z) 1 := j7 k
  have hden_j : T (j5 k) - T (qH j) ≠ 0 :=
   KM (by simpa [mem_ball_zero_iff] using hvc)
  have hdj := (KN hden_j).differentiableAt.conj_conj;rw [starRingEnd_self_apply] at hdj
  have hgj : (T ∘ KK j ∘ T) (j5 k) = T (j5 k) := by
   change T (qL j (j5 k)) = T (j5 k);rw [kd hjk]
  have hden_i : (T ∘ KK j ∘ T) (j5 k) - T (qH i) ≠ 0 := by rw [hgj];exact KM (by simpa [mem_ball_zero_iff] using hvc)
  have hdi := (KN hden_i).differentiableAt;exact hdi.comp (j5 k) hdj
 have h_rot_at : rot (j5 k) = j5 k := by dsimp [rot];rw [kd hjk, kd hik]
 have hcube : (deriv rot (j5 k)) ^ 3 = -1 := KX hij hik hjk
 rcases Nat.mod_two_eq_zero_or_one w.length with hw0 | hw1
 ·
  have hw_rev0 : w.reverse.length % 2 = 0 := by rw [List.length_reverse];exact hw0
  have hd_w : DifferentiableAt Z (jr w) z :=
   ((KO w).1 hw0 z hz).differentiableAt (isOpen_ball.mem_nhds hz)
  have hd_rev : DifferentiableAt Z (jr w.reverse) (j5 k) :=
   ((KO w.reverse).1 hw_rev0 (j5 k) (j7 k)).differentiableAt
    (isOpen_ball.mem_nhds (j7 k))
  have h_inv_d : deriv (jr w.reverse) (j5 k) * deriv (jr w) z = 1 := by
   have hd_rev' : HasDerivAt (jr w.reverse) (deriv (jr w.reverse) (j5 k)) (jr w z) := by rw [hx];exact hd_rev.hasDerivAt
   have hcomp := hd_rev'.comp z hd_w.hasDerivAt
   have hid_ev : ∀ᶠ u in 𝓝 z, (jr w.reverse ∘ jr w) u = u := by
    filter_upwards [isOpen_ball.mem_nhds hz] with u hu
    exact jw w hu
   exact hcomp.unique ((hasDerivAt_id z).congr_of_eventuallyEq hid_ev)
  have h_full_d : HasDerivAt (jr (w.reverse ++ [i, j] ++ w))
    (deriv (jr w.reverse) (j5 k) * deriv rot (j5 k) * deriv (jr w) z) z := by
   have hrot' : HasDerivAt rot (deriv rot (j5 k)) (jr w z) := by rw [hx];exact h_rot_diff.hasDerivAt
   have h1 : HasDerivAt (fun u => rot (jr w u)) (deriv rot (j5 k) * deriv (jr w) z) z :=
    hrot'.comp z hd_w.hasDerivAt
   have hd_rev'' : HasDerivAt (jr w.reverse) (deriv (jr w.reverse) (j5 k)) (rot (jr w z)) := by rw [hx, h_rot_at];exact hd_rev.hasDerivAt
   have h2 := hd_rev''.comp z h1
   refine h2.congr_of_eventuallyEq (Eventually.of_forall fun u => h_eq u) |>.congr_deriv (by ring)
  have h_deriv_eq : deriv (jr (w.reverse ++ [i, j] ++ w)) z = deriv rot (j5 k) := by
   rw [h_full_d.deriv]
   calc deriv (jr w.reverse) (j5 k) * deriv rot (j5 k) * deriv (jr w) z
       = (deriv (jr w.reverse) (j5 k) * deriv (jr w) z) * deriv rot (j5 k) := by ring
     _ = 1 * deriv rot (j5 k) := by rw [h_inv_d]
     _ = deriv rot (j5 k) := one_mul _
  rw [h_deriv_eq];exact hcube
 ·
  have hw_rev1 : w.reverse.length % 2 = 1 := by rw [List.length_reverse];exact hw1
  let L : Z → Z := T ∘ jr w;let R : Z → Z := jr w.reverse ∘ T;let M : Z → Z := T ∘ rot ∘ T
  have hd_L : DifferentiableAt Z L z :=
   ((KO w).2 hw1 z hz).differentiableAt (isOpen_ball.mem_nhds hz)
  have h_rev_hol : DifferentiableAt Z (T ∘ jr w.reverse) (j5 k) :=
   ((KO w.reverse).2 hw_rev1 (j5 k) (j7 k)).differentiableAt
    (isOpen_ball.mem_nhds (j7 k))
  have hd_R : DifferentiableAt Z R (T (j5 k)) := by
   have hc := h_rev_hol.conj_conj
   have heqR : (T ∘ (T ∘ jr w.reverse) ∘ T) = R := by funext u;simp only [comp_apply,RingHomCompTriple.comp_apply,RingHom.id_apply,R]
   rwa [heqR] at hc
  have hM_d : HasDerivAt M (T (deriv rot (j5 k))) (T (j5 k)) :=
   h_rot_diff.hasDerivAt.conj_conj
  have hL_at : L z = T (j5 k) := by dsimp [L];rw [hx]
  have hM_at : M (T (j5 k)) = T (j5 k) := by dsimp [M];rw [starRingEnd_self_apply, h_rot_at]
  have h_inv_d : deriv R (T (j5 k)) * deriv L z = 1 := by
   have hd_R' : HasDerivAt R (deriv R (T (j5 k))) (L z) := by rw [hL_at];exact hd_R.hasDerivAt
   have hcomp := hd_R'.comp z hd_L.hasDerivAt
   have hid_ev : ∀ᶠ u in 𝓝 z, (R ∘ L) u = u := by
    filter_upwards [isOpen_ball.mem_nhds hz] with u hu
    dsimp [R, L];rw [starRingEnd_self_apply, jw w hu]
   exact hcomp.unique ((hasDerivAt_id z).congr_of_eventuallyEq hid_ev)
  have h_eq_RML : ∀ u : Z, jr (w.reverse ++ [i, j] ++ w) u = R (M (L u)) := fun u => by
   rw [h_eq u];dsimp [R, M, L];simp only [RingHomCompTriple.comp_apply,RingHom.id_apply]
  have h_full_d : HasDerivAt (jr (w.reverse ++ [i, j] ++ w))
    (deriv R (T (j5 k)) * T (deriv rot (j5 k)) * deriv L z) z := by
   have hM_d' : HasDerivAt M (T (deriv rot (j5 k))) (L z) := by rw [hL_at];exact hM_d
   have h1 : HasDerivAt (fun u => M (L u))
     (T (deriv rot (j5 k)) * deriv L z) z :=
    hM_d'.comp z hd_L.hasDerivAt
   have hd_R'' : HasDerivAt R (deriv R (T (j5 k))) (M (L z)) := by rw [hL_at, hM_at];exact hd_R.hasDerivAt
   have h2 := hd_R''.comp z h1
   refine h2.congr_of_eventuallyEq (Eventually.of_forall fun u => h_eq_RML u) |>.congr_deriv (by ring)
  have h_deriv_eq : deriv (jr (w.reverse ++ [i, j] ++ w)) z = T (deriv rot (j5 k)) := by
   rw [h_full_d.deriv]
   calc deriv R (T (j5 k)) * T (deriv rot (j5 k)) * deriv L z
       = (deriv R (T (j5 k)) * deriv L z) * T (deriv rot (j5 k)) := by ring
     _ = 1 * T (deriv rot (j5 k)) := by rw [h_inv_d]
     _ = T (deriv rot (j5 k)) := one_mul _
  rw [h_deriv_eq, ← map_pow, hcube];simp only [map_neg,map_one]
lemma KZ {z : Z} (hz : z ∈ ball (0 : Z) 1)
  (hlat : ∃ m n : ℤ, KF z = (zd : Z) *
   (1 + (m : Z) * ((⟨-1 / 2, Y 3 / 2⟩ : Z) - 1) +
    (n : Z) * ((⟨-1 / 2, Y 3 / 2⟩ : Z) ^ 2 - 1))) :
  deriv KF z = 0 := by
 have hcAG : (zd : Z) ≠ 0 := ofReal_ne_zero.2 zf.ne';let w := KD z;let x := jr w z;have hxT0 : x ∈ T0 := KE hz
 have hf_lat : Kv (KF z / (zd : Z)) := by
  obtain ⟨m, n, hm⟩ := hlat;rw [hm, mul_div_cancel_left₀ _ hcAG];exact ⟨m, n, rfl⟩
 have hf0_lat : Kv (Kn x / (zd : Z)) := by
  have htw : KF z / (zd : Z) = js w.reverse (Kn x / (zd : Z)) := by dsimp [KF, w, x];rw [mul_div_cancel_left₀ _ hcAG]
  have hback := congr_arg (js w) htw
  have hcan : js w (js w.reverse (Kn x / (zd : Z))) = Kn x / (zd : Z) := by simpa [List.reverse_reverse] using jx w.reverse (Kn x / (zd : Z))
  rw [hcan] at hback;rw [← hback];exact KA w hf_lat
 obtain ⟨k, hk⟩ := (Ky hxT0).1 hf0_lat
 obtain ⟨i, j, hij, hik, hjk⟩ : ∃ i j : Fin 3, i < j ∧ i ≠ k ∧ j ≠ k := by
  fin_cases k
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩
 let wrot := w.reverse ++ [i, j] ++ w;let h : Z → Z := jr wrot
 have hwrot_even : wrot.length % 2 = 0 := by dsimp [wrot];simp only [List.append_assoc,List.cons_append,List.nil_append,List.length_append,List.length_reverse,List.length_cons];omega
 have h_diff : DifferentiableAt Z h z :=
  ((KO wrot).1 hwrot_even z hz).differentiableAt (isOpen_ball.mem_nhds hz)
 have h_at : h z = z := by
  dsimp [h, wrot];rw [List.append_assoc, jt, jt];change jr w.reverse (qL i (qL j x)) = z;rw [hk, kd hjk, kd hik, ← hk];exact jw w hz
 have h_cube : (deriv h z) ^ 3 = -1 := KY hz hij hik hjk hk;obtain ⟨A, B, hA3, hA_form⟩ := (KT wrot).1 hwrot_even
 have h_fAG_rot : ∀ u ∈ ball (0 : Z) 1, KF (h u) = A * KF u + (zd : Z) * B := by
  intro u hu;let wu := KD u;have hy : jr wu u ∈ T0 := KE hu
  have hwrot_rev : wrot.reverse = w.reverse ++ [j, i] ++ w := by
   dsimp [wrot];simp only [List.append_assoc,List.cons_append,List.nil_append,List.reverse_append,List.reverse_cons,List.reverse_reverse]
  have h_inv_u : jr (wu ++ wrot.reverse) (h u) = jr wu u := by
   rw [jt];dsimp [h];rw [jw wrot hu]
  have hmem_T0 : jr (wu ++ wrot.reverse) (h u) ∈ T0 := by rw [h_inv_u];exact hy
  have hhu_ball : h u ∈ ball (0 : Z) 1 := jv wrot hu
  rw [KH hhu_ball hmem_T0, h_inv_u, List.reverse_append, List.reverse_reverse,
   ju, hA_form]
  have hfu : KF u / (zd : Z) = js wu.reverse (Kn (jr wu u) / (zd : Z)) := by dsimp [KF, wu];rw [mul_div_cancel_left₀ _ hcAG]
  rw [← hfu];field_simp [hcAG]
 have hdf_z : DifferentiableAt Z KF z :=
  (KV z hz).differentiableAt (isOpen_ball.mem_nhds hz)
 have h_lhs : HasDerivAt (fun u => KF (h u)) (deriv KF z * deriv h z) z := by
  have hdf_hz : HasDerivAt KF (deriv KF z) (h z) := by rw [h_at];exact hdf_z.hasDerivAt
  exact hdf_hz.comp z h_diff.hasDerivAt
 have h_rhs : HasDerivAt (fun u => A * KF u + (zd : Z) * B) (A * deriv KF z) z :=
  (hdf_z.hasDerivAt.const_mul A).add_const _
 have h_eq_d : deriv KF z * deriv h z = A * deriv KF z :=
  h_lhs.unique (h_rhs.congr_of_eventuallyEq (by
   filter_upwards [isOpen_ball.mem_nhds hz] with u hu;exact h_fAG_rot u hu))
 have h_fac : (deriv h z - A) * deriv KF z = 0 := by linear_combination h_eq_d
 rcases mul_eq_zero.1 h_fac with hne | h0
 ·
  exfalso;have h_eqA : deriv h z = A := sub_eq_zero.1 hne;have h_c := congr_arg (fun c : Z => c ^ 3) h_eqA;rw [h_cube, hA3] at h_c;norm_num at h_c
 · exact h0
def H1_prop : Prop :=
 ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) ∧ deriv f 0 = 1 ∧
  ∀ z ∈ ball (0 : ℂ) 1,
   (∃ m n : ℤ, f z = ((Real.Gamma (1 / 3) * Real.Gamma (11 / 12) / (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3)) : ℝ) : ℂ) *
    (1 + (m : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 1) +
     (n : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 - 1))) →
   deriv f z = 0
theorem H1_proof : H1_prop := by
 refine ⟨KF, KV, KW, fun z hz hlat => ?_⟩
 exact KZ hz hlat
end
end BlochAG
end

section
private lemma rect_hex_cover (U V : ℝ) :
    ∃ m n : ℤ,
      (9 / 4 : ℝ) * (U - (m + n : ℤ)) ^ 2 + (3 / 4 : ℝ) * (V - (m - n : ℤ)) ^ 2 ≤ 1 := by
  let a0 : ℤ := ⌊U⌋
  let b0 : ℤ := ⌊V⌋
  have ht0 : 0 ≤ U - a0 := sub_nonneg.2 (Int.floor_le U)
  have ht1 : U - a0 ≤ 1 := by linarith [Int.lt_floor_add_one U]
  have hs0 : 0 ≤ V - b0 := sub_nonneg.2 (Int.floor_le V)
  have hs1 : V - b0 ≤ 1 := by linarith [Int.lt_floor_add_one V]
  let t := U - a0
  let s := V - b0
  have heven : (9 / 4 : ℝ) * t ^ 2 + (3 / 4 : ℝ) * s ^ 2 ≤ 1 ∨
      (9 / 4 : ℝ) * (1 - t) ^ 2 + (3 / 4 : ℝ) * (1 - s) ^ 2 ≤ 1 := by
    rcases le_total t (1 / 3) with h | h
    · exact Or.inl (by nlinarith)
    · rcases le_total (2 / 3) t with h2 | h2
      · exact Or.inr (by nlinarith)
      · by_cases hd : (9 / 4 : ℝ) * t ^ 2 + (3 / 4 : ℝ) * s ^ 2 ≤ 1
        · exact Or.inl hd
        · exact Or.inr (by nlinarith)
  have hodd : (9 / 4 : ℝ) * t ^ 2 + (3 / 4 : ℝ) * (1 - s) ^ 2 ≤ 1 ∨
      (9 / 4 : ℝ) * (1 - t) ^ 2 + (3 / 4 : ℝ) * s ^ 2 ≤ 1 := by
    rcases le_total t (1 / 3) with h | h
    · exact Or.inl (by nlinarith)
    · rcases le_total (2 / 3) t with h2 | h2
      · exact Or.inr (by nlinarith)
      · by_cases hd : (9 / 4 : ℝ) * t ^ 2 + (3 / 4 : ℝ) * (1 - s) ^ 2 ≤ 1
        · exact Or.inl hd
        · exact Or.inr (by nlinarith)
  rcases Int.even_or_odd (a0 - b0) with ⟨k, hk⟩ | ⟨k, hk⟩
  · rcases heven with hd | hd
    · refine ⟨b0 + k, k, ?_⟩
      have ha : (b0 + k + k : ℤ) = a0 := by omega
      have hb : (b0 + k - k : ℤ) = b0 := by omega
      rw [ha, hb]; exact hd
    · refine ⟨b0 + k + 1, k, ?_⟩
      have ha : ((b0 + k + 1 + k : ℤ) : ℝ) = (a0 : ℝ) + 1 := by
        exact_mod_cast (by omega : b0 + k + 1 + k = a0 + 1)
      have hb : ((b0 + k + 1 - k : ℤ) : ℝ) = (b0 : ℝ) + 1 := by
        exact_mod_cast (by omega : b0 + k + 1 - k = b0 + 1)
      rw [ha, hb]
      have et : U - ((a0 : ℝ) + 1) = -(1 - t) := by dsimp [t]; ring
      have es : V - ((b0 : ℝ) + 1) = -(1 - s) := by dsimp [s]; ring
      rw [et, es]; nlinarith
  · rcases hodd with hd | hd
    · refine ⟨b0 + k + 1, k, ?_⟩
      have ha : (b0 + k + 1 + k : ℤ) = a0 := by omega
      have hb : ((b0 + k + 1 - k : ℤ) : ℝ) = (b0 : ℝ) + 1 := by
        exact_mod_cast (by omega : b0 + k + 1 - k = b0 + 1)
      rw [ha, hb]
      have es : V - ((b0 : ℝ) + 1) = -(1 - s) := by dsimp [s]; ring
      rw [es]; nlinarith
    · refine ⟨b0 + k + 1, k + 1, ?_⟩
      have ha : ((b0 + k + 1 + (k + 1) : ℤ) : ℝ) = (a0 : ℝ) + 1 := by
        exact_mod_cast (by omega : b0 + k + 1 + (k + 1) = a0 + 1)
      have hb : (b0 + k + 1 - (k + 1) : ℤ) = b0 := by omega
      rw [ha, hb]
      have et : U - ((a0 : ℝ) + 1) = -(1 - t) := by dsimp [t]; ring
      rw [et]; nlinarith

private lemma eisenstein_ball_hit {c : ℝ} (hc : 0 < c) (x : ℂ) {r : ℝ} (hr : c < r) :
    ∃ m n : ℤ,
      ((c : ℂ) * (1 + (m : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 1) +
        (n : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 - 1))) ∈ ball x r := by
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  let U : ℝ := (1 - x.re / c) * (2 / 3)
  let V : ℝ := (x.im / c) * (2 / Real.sqrt 3)
  obtain ⟨m, n, hmn⟩ := rect_hex_cover U V
  refine ⟨m, n, ?_⟩
  rw [mem_ball, Complex.dist_eq_re_im]
  refine lt_of_le_of_lt ?_ hr
  rw [Real.sqrt_le_iff]
  refine ⟨hc.le, ?_⟩
  let w : ℂ := (c : ℂ) * (1 + (m : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 1) +
    (n : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 - 1))
  have hc0 : c ≠ 0 := hc.ne'
  have hs0 : Real.sqrt 3 ≠ 0 := hs3.ne'
  have hw_re : w.re - x.re = c * (3 / 2) * (U - (m + n : ℤ)) := by
    dsimp [w, U]
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Int.cast_add]
    field_simp [hc0]
    rw [hsq3]; ring
  have hw_im : w.im - x.im = -c * (Real.sqrt 3 / 2) * (V - (m - n : ℤ)) := by
    dsimp [w, V]
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Int.cast_sub]
    field_simp [hc0, hs0]
    rw [hsq3]; ring
  change (w.re - x.re) ^ 2 + (w.im - x.im) ^ 2 ≤ c ^ 2
  rw [hw_re, hw_im]
  have hsq : (c * (3 / 2) * (U - (m + n : ℤ))) ^ 2 +
      (-c * (Real.sqrt 3 / 2) * (V - (m - n : ℤ))) ^ 2 =
      c ^ 2 * ((9 / 4) * (U - (m + n : ℤ)) ^ 2 + (3 / 4) * (V - (m - n : ℤ)) ^ 2) := by
    linear_combination (c ^ 2 * (V - (m - n : ℤ)) ^ 2 / 4) * hsq3
  rw [hsq]
  nlinarith [sq_nonneg c]

private lemma univalent_deriv_ne_zero {f : ℂ → ℂ} {S : Set ℂ}
    (hSo : IsOpen S) (hf : DifferentiableOn ℂ f S) (hinj : InjOn f S)
    {z0 : ℂ} (hz0 : z0 ∈ S) : deriv f z0 ≠ 0 := by
  intro hd0
  have hSnhds : S ∈ 𝓝 z0 := hSo.mem_nhds hz0
  have han : AnalyticAt ℂ (fun u => f (z0 + u) - f z0) 0 := by
    have hf0 : AnalyticAt ℂ f (z0 + 0) := hf.analyticAt (by simpa using hSnhds)
    exact (hf0.comp (analyticAt_const.add analyticAt_id)).sub analyticAt_const
  by_cases htop : analyticOrderAt (fun u => f (z0 + u) - f z0) 0 = ⊤
  · obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
      ((analyticOrderAt_eq_top.1 htop).and
        ((continuous_const.add continuous_id).tendsto' 0 z0 (add_zero z0) hSnhds))
    have hu : ((r / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) r := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    obtain ⟨hfeq, hmem⟩ := hball hu
    have hmem' : z0 + ((r / 2 : ℝ) : ℂ) ∈ S := by simpa using hmem
    have hinj_eq : z0 + ((r / 2 : ℝ) : ℂ) = z0 + 0 := by
      simpa using hinj hmem' hz0 (sub_eq_zero.1 hfeq)
    have hne : ((r / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
    exact hne (add_left_cancel hinj_eq)
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 htop
    have hk2 : 2 ≤ k := by
      have hge : (2 : ℕ∞) ≤ analyticOrderAt (fun u => f (z0 + u) - f z0) 0 := by
        exact_mod_cast (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 2) han).2 (by
          intro j hj
          interval_cases j
          · simp
          · simp [iteratedDeriv_one, deriv_sub_const, deriv_comp_const_add, hd0])
      rw [← hk] at hge
      exact_mod_cast hge
    obtain ⟨g, hga, hg0, hfg⟩ := (han.analyticOrderAt_eq_natCast (n := k)).1 hk.symm
    have hk0 : k ≠ 0 := by omega
    let ψ : ℂ → ℂ := fun u => Complex.exp (Complex.log (g u / g 0) / (k : ℂ))
    have hψ0 : ψ 0 = 1 := by simp [ψ, div_self hg0]
    have hslit0 : g 0 / g 0 ∈ Complex.slitPlane := by
      rw [div_self hg0]; exact Complex.one_mem_slitPlane
    obtain ⟨pg, hpg⟩ := hga
    have hψ_strict : HasStrictDerivAt ψ _ 0 :=
      (((hpg.hasStrictDerivAt.div_const (g 0)).clog hslit0).div_const (k : ℂ)).cexp
    let Φ : ℂ → ℂ := fun u => u * ψ u
    have hΦ0 : Φ 0 = 0 := by simp [Φ]
    have hΦ_strict : HasStrictDerivAt Φ 1 0 :=
      ((hasStrictDerivAt_id (0 : ℂ)).mul hψ_strict).congr_deriv (by simp [hψ0])
    have hslit_ev : ∀ᶠ u in 𝓝 (0 : ℂ), g u / g 0 ∈ Complex.slitPlane :=
      (hpg.continuousAt.div_const (g 0)).eventually (Complex.isOpen_slitPlane.mem_nhds hslit0)
    have hpow_ev : ∀ᶠ u in 𝓝 (0 : ℂ), f (z0 + u) - f z0 = g 0 * (Φ u) ^ k := by
      filter_upwards [hfg, hslit_ev] with u hu hsl
      have hne_q : g u / g 0 ≠ 0 := Complex.slitPlane_ne_zero hsl
      have hψk : (ψ u) ^ k = g u / g 0 := by
        dsimp [ψ]
        rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hk0), Complex.exp_log hne_q]
      dsimp [Φ]
      simp only [sub_zero, smul_eq_mul] at hu
      rw [hu, mul_pow, hψk]
      field_simp [hg0]
    have hU_ev : ∀ᶠ u in 𝓝 (0 : ℂ), z0 + u ∈ S :=
      (continuous_const.add continuous_id).tendsto' 0 z0 (add_zero z0) hSnhds
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hpow_ev.and hU_ev)
    have himg : Φ '' ball (0 : ℂ) ε ∈ 𝓝 (0 : ℂ) := by
      have hmap := hΦ_strict.map_nhds_eq one_ne_zero
      rw [hΦ0] at hmap
      rw [← hmap]
      exact Filter.image_mem_map (ball_mem_nhds (0 : ℂ) hε)
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 himg
    let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (k : ℂ))
    have hξ : IsPrimitiveRoot ξ k := Complex.isPrimitiveRoot_exp k hk0
    have hξ_norm : ‖ξ‖ = 1 := hξ.norm'_eq_one hk0
    let w : ℂ := ((δ / 2 : ℝ) : ℂ)
    have hw0 : w ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
    have hw_norm : ‖w‖ < δ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
    obtain ⟨u1, hu1, hΦ1⟩ := hsub (show w ∈ ball (0 : ℂ) δ by simpa [mem_ball_zero_iff] using hw_norm)
    obtain ⟨u2, hu2, hΦ2⟩ := hsub (show ξ * w ∈ ball (0 : ℂ) δ by
      rw [mem_ball_zero_iff, norm_mul, hξ_norm, one_mul]; exact hw_norm)
    obtain ⟨hf1, hs1⟩ := hball (mem_ball.1 hu1)
    obtain ⟨hf2, hs2⟩ := hball (mem_ball.1 hu2)
    have hfeq : f (z0 + u1) = f (z0 + u2) := by
      have hd12 : f (z0 + u1) - f z0 = f (z0 + u2) - f z0 := by
        rw [hf1, hf2, hΦ1, hΦ2, mul_pow, hξ.pow_eq_one, one_mul]
      linear_combination hd12
    have hu12 : u1 = u2 := add_left_cancel (hinj hs1 hs2 hfeq)
    have hξ1 : ξ * w = 1 * w := by rw [one_mul, ← hΦ2, ← hu12, hΦ1]
    exact hξ.ne_one hk2 (mul_right_cancel₀ hw0 hξ1)

private lemma bloch_upper_from_ag (hag : BlochAG.H1_prop) : type_of% @Bloch.blochConstant_upper_bound := by
  obtain ⟨f, hf, hf0, hcrit⟩ := hag
  set c : ℝ := Real.Gamma (1 / 3) * Real.Gamma (11 / 12) /
      (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3))
  have hc : 0 < c := by
    have hg1 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
    have hg2 : 0 < Real.Gamma (11 / 12) := Real.Gamma_pos_of_pos (by norm_num)
    have hg3 : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
    have hs : 0 < Real.sqrt (1 + Real.sqrt 3) := Real.sqrt_pos.2 (by positivity)
    positivity
  unfold Bloch.blochConstant
  refine csSup_le ⟨0, fun g _ _ => ⟨∅, isOpen_empty, empty_subset _, 0, by simp⟩⟩ ?_
  intro r hr
  by_contra hlt
  obtain ⟨S, hSo, hS1, x, himg, hinj⟩ := hr f hf hf0
  obtain ⟨m, n, hmem⟩ := eisenstein_ball_hit hc x (not_le.1 hlt)
  rw [← himg] at hmem
  obtain ⟨z, hzS, hfz⟩ := hmem
  exact univalent_deriv_ne_zero hSo (hf.mono hS1) hinj hzS
    (hcrit z (hS1 hzS) ⟨m, n, hfz⟩)
end

theorem OMA.solution : type_of% @Bloch.blochConstant_upper_bound :=
  bloch_upper_from_ag BlochAG.H1_proof
