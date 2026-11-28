import FormalConjectures.ErdosProblems.«305»
import Mathlib

/-!
The denominator bound of Liu and Sawhney, arXiv:2404.07113.
The moderate-fraction and scale estimates come from the Erdős 294
formalization in PR #11974. It uses @steveDOTdigital's reductions and
estimates (#5730, #6217, #6261, #6598 and #6840), @mattdorman's
near-frequency proof (#8765), and @ppleskov's far-frequency proof (#11598).
The final argument represents any a/b by two dilated blocks at the small
scale. Small numerators use a fixed finite collection of disjoint blocks.
-/

section

namespace OMA.R_Erdos294_erdos_294_R1

open Filter Real Finset

/-- Lemma 4.1, using divisibility by the lcm of the prime powers up to the
smoothness cutoff. The denominators lie between N/16 and N. -/
def H1 : Prop := ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ d a : ℕ, 0 < d → d ∣ Nat.lcmUpto (⌊c * (N : ℝ) / ((Real.log N)^3 * (Real.log (Real.log N))^4)⌋₊) →
    d ≤ 3*a → a ≤ d →
    ∃ B : Finset ℕ, (∀ b ∈ B, N ≤ 16*b ∧ b ≤ N) ∧
      ∑ b ∈ B, (1 : ℚ)/b = (a : ℚ)/d

/-- A choice of the smaller interval scale. Its lcm exceeds four times the
large scale, divides the large-scale lcm, and its dilates stay strictly
below the second block throughout the proposed denominator range. -/
def H2 : Prop := ∀ c : ℝ, 0 < c → ∀ N₀ : ℕ, ∃ K : ℝ, ∀ᶠ N : ℕ in atTop,
    ∃ L : ℕ, N₀ ≤ L ∧ 32 ≤ L ∧ 4*N ≤ Nat.lcmUpto (⌊c * (L : ℝ) / ((Real.log L)^3 * (Real.log (Real.log L))^4)⌋₊) ∧
      Nat.lcmUpto (⌊c * (L : ℝ) / ((Real.log L)^3 * (Real.log (Real.log L))^4)⌋₊) ∣ Nat.lcmUpto (⌊c * (N : ℝ) / ((Real.log N)^3 * (Real.log (Real.log N))^4)⌋₊) ∧
      32*(L : ℝ)*|(N : ℝ) / (Real.log N * (Real.log (Real.log N))^3 * (Real.log (Real.log (Real.log N)))^K)| ≤ N

end OMA.R_Erdos294_erdos_294_R1

end

section

/-!
A finite Fourier extraction for the smooth-denominator representation in
Liu and Sawhney, arXiv:2404.07113, Section 4. Work modulo four times the
common denominator. The total possible sum is below the modulus, so a
congruence gives equality without a separate concentration inequality.
-/

open Finset Filter

namespace OMA.R_Erdos294_erdos_294_R1_H1_R1

/-- If no subset has the prescribed sum, the indicated Fourier coefficient
of the Bernoulli product vanishes. The parameter can even be complex. -/
theorem zero_of_no_subset {M : ℕ} [NeZero M] (A : Finset ℕ)
    (w : ℕ → ZMod M) (p : ℂ) (t : ZMod M) (no : ∀ B ⊆ A, (∑ n ∈ B,w n) ≠ t) :
    (∑ h : ZMod M, ZMod.stdAddChar ((-t)*h) *
      ∏ n ∈ A, (1-p+p*ZMod.stdAddChar (w n*h))) = 0 := by
  classical
  induction A using Finset.induction_on generalizing t with
  | empty =>
    have ht : -t ≠ 0 := neg_ne_zero.mpr (fun ht => no ∅ (by simp) (by simp [ht]))
    simpa only [prod_empty,mul_one,AddChar.mulShift_apply] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M ht))
  | @insert i A hi ih =>
    have h₀ := ih t (fun B hB => no B (hB.trans (subset_insert _ _)))
    have h₁ := ih (t-w i) (fun B hB eq => by
      apply no (insert i B) (insert_subset_insert _ hB)
      rw [sum_insert (fun h => hi (hB h)), eq]
      abel)
    let F (h : ZMod M) : ℂ := ∏ n ∈ A, (1-p+p*ZMod.stdAddChar (w n*h))
    calc
      _ = ∑ h : ZMod M, ((1-p)*(ZMod.stdAddChar ((-t)*h)*F h) +
          p*(ZMod.stdAddChar ((-(t-w i))*h)*F h)) := by
        apply sum_congr rfl
        intro h _
        rw [prod_insert hi,show (-(t-w i))*h = (-t)*h + w i*h by ring,
          AddChar.map_add_eq_mul]
        dsimp only [F]
        ring
      _ = _ := by rw [sum_add_distrib,←mul_sum,←mul_sum]; dsimp only [F]; rw [h₀,h₁];ring

/-- The central frequencies for an interval of Bernoulli reciprocals.
The choice of p centers the weighted sum at the requested numerator. -/
def H1 : Prop := ∀ᶠ N : ℕ in atTop, ∀ (Q : ℕ) [NeZero Q] (A : Finset ℕ),
  (∀ n ∈ A, 0<n ∧ N ≤ 16*n ∧ n ≤ N ∧ n ∣ Q) →
  3*Q ≤ 2*(∑ n ∈ A,Q/n) → (∑ n ∈ A,Q/n) ≤ 3*Q → ∀ t : ℕ, Q ≤ 3*t → t ≤ Q →
  let V := ∑ n ∈ A, Q/n
  let p : ℂ := (t:ℂ)/(V:ℂ)
  let S := Finset.univ.filter (fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5 ≤ N^3)
  let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t : ZMod (4*Q)))*h) *
    ∏ n ∈ A, (1-p+p*ZMod.stdAddChar (((Q/n : ℕ) : ZMod (4*Q))*h))
  1 ≤ (∑ h ∈ S, F h).re

/-- The arithmetic input is a set of smooth denominators with sufficient
mass and a bound for the complementary Fourier frequencies. -/
def H2 : Prop := ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop,
  let Q := Nat.lcmUpto ⌊c*(N:ℝ)/((Real.log N)^3*(Real.log (Real.log N))^4)⌋₊
  letI : NeZero Q := ⟨Nat.lcmUpto_ne_zero _⟩
  ∃ A : Finset ℕ, (∀ n ∈ A, 0<n ∧ N ≤ 16*n ∧ n ≤ N ∧ n ∣ Q) ∧
    3*Q ≤ 2*(∑ n ∈ A,Q/n) ∧ (∑ n ∈ A,Q/n) ≤ 3*Q ∧ ∀ t : ℕ, Q ≤ 3*t → t ≤ Q →
    let V := ∑ n ∈ A, Q/n
    let p : ℂ := (t:ℂ)/(V:ℂ)
    let S := Finset.univ.filter (fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5 ≤ N^3)
    let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t : ZMod (4*Q)))*h) *
      ∏ n ∈ A, (1-p+p*ZMod.stdAddChar (((Q/n : ℕ) : ZMod (4*Q))*h))
    ‖∑ h ∈ Sᶜ, F h‖ < 1

theorem main : H1 → H2 → OMA.R_Erdos294_erdos_294_R1.H1 := by
  classical
  rintro central ⟨c,hc,minor⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.1 (central.and minor)
  refine ⟨c,hc,N₀,?_⟩
  intro N hN d a hd hdiv ha₁ ha₂
  let Q := Nat.lcmUpto ⌊c*(N:ℝ)/((Real.log N)^3*(Real.log (Real.log N))^4)⌋₊
  have hQ : 0<Q := Nat.lcmUpto_pos _
  letI : NeZero Q := ⟨hQ.ne'⟩
  change d ∣ Q at hdiv
  obtain ⟨hcN,hmN⟩ := hN₀ N hN
  obtain ⟨A,hA,hmass,hcap,hminor⟩ := hmN
  let t := a*(Q/d)
  have htmax : t ≤ Q := calc
    _ ≤ d*(Q/d) := Nat.mul_le_mul_right _ ha₂
    _ = _ := Nat.mul_div_cancel' hdiv
  have htmin : Q ≤ 3*t := calc
    _ = d*(Q/d) := (Nat.mul_div_cancel' hdiv).symm
    _ ≤ (3*a)*(Q/d) := Nat.mul_le_mul_right _ ha₁
    _ = _ := by dsimp [t];ring
  let V := ∑ n ∈ A, Q/n
  let p : ℂ := (t:ℂ)/(V:ℂ)
  let S := Finset.univ.filter (fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5 ≤ N^3)
  let w (n : ℕ) : ZMod (4*Q) := (Q/n:ℕ)
  let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t : ZMod (4*Q)))*h) *
    ∏ n ∈ A, (1-p+p*ZMod.stdAddChar (w n*h))
  have hlow : 1 ≤ (∑ h ∈ S, F h).re := hcN Q A hA hmass hcap t htmin htmax
  have hhigh : ‖∑ h ∈ Sᶜ, F h‖ < 1 := hminor t htmin htmax
  have hnon : (∑ h, F h) ≠ 0 := by
    intro heq
    have hs := congrArg Complex.re ((Finset.sum_add_sum_compl S F).trans heq)
    rw [Complex.add_re,Complex.zero_re] at hs
    have hab := abs_le.mp (Complex.abs_re_le_norm (∑ h ∈ Sᶜ,F h))
    linarith
  obtain ⟨B,hB,hmod⟩ : ∃ B ⊆ A, (∑ n ∈ B,w n) = (t : ZMod (4*Q)) := by
    by_contra! no
    exact hnon (zero_of_no_subset A w p (t : ZMod (4*Q)) no)
  have hcast : ((∑ n ∈ B,Q/n : ℕ) : ZMod (4*Q)) = (t : ZMod (4*Q)) := by
    push_cast
    exact hmod
  have hsumle : (∑ n ∈ B,Q/n) ≤ 3*Q := (Finset.sum_le_sum_of_subset_of_nonneg hB
    (fun _ _ _ => Nat.zero_le _)).trans hcap
  have hsum := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hsum
  refine ⟨B,fun n hn => ⟨(hA n (hB hn)).2.1,(hA n (hB hn)).2.2.1⟩,?_⟩
  have hscale : (Q:ℚ)*(∑ n ∈ B,(1:ℚ)/n) = (t:ℚ) := by
    rw [← hsum, Nat.cast_sum, Finset.mul_sum]
    apply sum_congr rfl
    intro n hn
    obtain ⟨hnpos,_,_,hnQ⟩ := hA n (hB hn)
    have hm : ((Q/n:ℕ):ℚ)*n = Q := by exact_mod_cast Nat.div_mul_cancel hnQ
    rw [mul_one_div]
    exact (div_eq_iff (by exact_mod_cast hnpos.ne')).mpr hm.symm
  have ht : (t:ℚ)*d = (a:ℚ)*Q := by
    have hm : ((Q/d:ℕ):ℚ)*d = Q := by exact_mod_cast Nat.div_mul_cancel hdiv
    dsimp only [t]
    push_cast
    rw [mul_assoc,hm]
  apply (eq_div_iff (by exact_mod_cast hd.ne')).mpr
  apply mul_left_cancel₀ (by exact_mod_cast hQ.ne' : (Q:ℚ)≠0)
  rw [← mul_assoc,hscale,ht,mul_comm]

end OMA.R_Erdos294_erdos_294_R1_H1_R1

end

section

/-!
Use the full pool of admissible divisors. A Bernoulli factor with parameter
between 1/9 and 2/3 has norm at most exp(-(8/27) times the squared
distance of its phase to the nearest integer). This removes the target t
from the estimate. Between N^(3/5) and N/16 there is no modular wrap,
and the reciprocal mass gives a Gaussian bound. Only the more distant
frequencies enter the arithmetic hypothesis.
-/

open Finset Filter
namespace OMA.R_Erdos294_erdos_294_R1_H1_R1_H2_R1

/-- The full smooth pool on the interval has sufficient reciprocal mass. -/
def H1 : Prop := ∀ c : ℝ, 0<c → ∀ᶠ N : ℕ in atTop,
  let Q := Nat.lcmUpto ⌊c*(N:ℝ)/((Real.log N)^3*(Real.log (Real.log N))^4)⌋₊
  let A := (Icc 1 N).filter fun n => N ≤ 16*n ∧ n ∣ Q
  3*Q ≤ 2*(∑ n ∈ A,Q/n) ∧ (∑ n ∈ A,Q/n) ≤ 3*Q

/-- Far frequencies, expressed solely by distances to integer multiples of 4n. -/
def H2 : Prop := ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop,
  let Q := Nat.lcmUpto ⌊c*(N:ℝ)/((Real.log N)^3*(Real.log (Real.log N))^4)⌋₊
  letI : NeZero Q := ⟨Nat.lcmUpto_ne_zero _⟩
  let A := (Icc 1 N).filter fun n => N ≤ 16*n ∧ n ∣ Q
  let far := univ.filter fun h : ZMod (4*Q) => N < 16*h.valMinAbs.natAbs
  (∑ h ∈ far, Real.exp (-(8/27:ℝ)*∑ n ∈ A,
    let x := (h.valMinAbs:ℝ)/(4*n)
    (x - round x)^2)) < 1/2

lemma cos_loss (x : ℝ) : 8*(x-round x)^2 ≤ 1-Real.cos (2*Real.pi*x) := by
  let r := x-(round x:ℝ)
  have hr : |r| ≤ 1/2 := abs_sub_round x
  have hsin' := Real.mul_le_sin (x:=Real.pi*|r|) (by positivity)
    (by nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_left hr Real.pi_pos.le])
  have he : 2/Real.pi*(Real.pi*|r|)=2*|r| := by field_simp
  rw [he] at hsin'
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2*|r|) hsin' 2
  rw [mul_pow,sq_abs] at hs
  have hp : Real.cos (2*Real.pi*x)=Real.cos (2*(Real.pi*|r|)) := by
    have hper : Real.cos (2*Real.pi*r)=Real.cos (2*Real.pi*x) := by
      dsimp [r]
      rw [show 2*Real.pi*(x-(round x:ℝ))=2*Real.pi*x-(round x:ℝ)*(2*Real.pi) by ring,
        Real.cos_sub_int_mul_two_pi]
    rw [← hper]
    rcases le_or_gt 0 r with h|h
    · rw [abs_of_nonneg h]; congr 1; ring
    · rw [abs_of_neg h,show 2*(Real.pi*(-r))= -(2*Real.pi*r) by ring,Real.cos_neg]
  rw [hp, Real.cos_two_mul]
  change 8*r^2 ≤ _
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi*|r|)]

lemma factor_decay (p x : ℝ) (hp : 1/9 ≤ p) (hq : p ≤ 2/3) :
    ‖1-(p:ℂ)+(p:ℂ)*Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)‖ ≤
      Real.exp (-(8/27:ℝ)*(x-round x)^2) := by
  let z := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  have hz : ‖z‖=1 := by simp [z,Complex.norm_exp]
  have hre : z.re=Real.cos (2*Real.pi*x) := by simp [z,Complex.exp_re]
  have hcircle : z.re*z.re+z.im*z.im=1 := by rw [← Complex.normSq_apply,← Complex.sq_norm,hz]; norm_num
  have heq : ‖1-(p:ℂ)+(p:ℂ)*z‖^2=1-2*p*(1-p)*(1-z.re) := by
    simp [Complex.sq_norm, Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
    nlinarith only [congrArg (fun y:ℝ => p^2*y) hcircle]
  have hcoeff : 1/27 ≤ p*(1-p) := calc
    (1/27:ℝ) = (1/9)*(1/3) := by norm_num
    _ ≤ _ := mul_le_mul hp (by linarith) (by norm_num) (by linarith)
  have hcos := cos_loss x
  rw [← hre] at hcos
  have hpos : 0 ≤ 1-z.re := by nlinarith [sq_nonneg (x-(round x:ℝ))]
  have hmult := mul_le_mul_of_nonneg_right hcoeff hpos
  change ‖1-(p:ℂ)+(p:ℂ)*z‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  rw [heq,pow_two,← Real.exp_add]
  have h := Real.add_one_le_exp ((-(8/27:ℝ)*(x-round x)^2)+(-(8/27:ℝ)*(x-round x)^2))
  nlinarith only [h,hcos,hmult]

lemma char_fraction (Q n : ℕ) [NeZero Q] (hn : 0<n) (hd : n ∣ Q) (h : ZMod (4*Q)) :
    ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h) =
      Complex.exp (((2*Real.pi*((h.valMinAbs:ℝ)/(4*n)):ℝ):ℂ)*Complex.I) := by
  let j := h.valMinAbs
  have hh : (j:ZMod (4*Q))=h := h.coe_valMinAbs
  have hchar (r : ℤ) : ZMod.stdAddChar ((r:ZMod (4*Q))*(j:ZMod (4*Q))) =
      Complex.exp (((2*Real.pi*(j:ℝ)/((4*Q:ℕ):ℝ)*(r:ℝ):ℝ):ℂ)*Complex.I) := by
    rw [←Int.cast_mul,ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  have hc := hchar (Q/n:ℕ)
  rw [hh] at hc
  simp only [Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat] at hc
  rw [hc]
  have eqn : ((Q/n:ℕ):ℝ)*n=Q := by exact_mod_cast Nat.div_mul_cancel hd
  have hn' : (n:ℝ)≠0 := by positivity
  have hQ : (Q:ℝ)≠0 := by exact_mod_cast NeZero.ne Q
  have hw : ((Q/n:ℕ):ℝ)≠0 := by intro h0; rw [h0,zero_mul] at eqn; exact hQ eqn.symm
  have angle : 2*Real.pi*(j:ℝ)/(4*Q)*((Q/n:ℕ):ℝ)=2*Real.pi*((j:ℝ)/(4*n)) := by
    rw [← eqn]
    field_simp
  rw [angle]

lemma mass_card (N Q : ℕ) [NeZero Q] (A : Finset ℕ)
    (ha : ∀ n ∈ A, N≤16*n ∧ n∣Q) (hm : 3*Q≤2*∑ n∈A,Q/n) : 3*N≤32*A.card := by
  have hb : N*(∑ n ∈ A,Q/n) ≤ A.card*(16*Q) := calc
    _ = ∑ n ∈ A,N*(Q/n) := mul_sum _ _ _
    _ ≤ ∑ _n ∈ A,16*Q := by
      apply sum_le_sum
      intro n hn
      calc
        _ ≤ (16*n)*(Q/n) := Nat.mul_le_mul_right _ (ha n hn).1
        _ = 16*Q := by rw [mul_assoc,Nat.mul_div_cancel' (ha n hn).2]
    _ = _ := by simp
  apply (mul_le_mul_iff_of_pos_right (NeZero.pos Q)).mp
  nlinarith only [Nat.mul_le_mul_left N hm,hb]

lemma medium_weight (N : ℕ) (hN : 0<N) (A : Finset ℕ)
    (ha : ∀ n ∈ A, 0<n ∧ N≤16*n ∧ n≤N) (hc : 3*N ≤ 32*A.card)
    (j : ℤ) (hj : 16*j.natAbs ≤ N) :
    Real.exp (-(8/27:ℝ)*∑ n ∈ A, ((j:ℝ)/(4*n)-round ((j:ℝ)/(4*n)))^2) ≤
      Real.exp (-((j.natAbs:ℝ)^2/(1024*N))) := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have habs : |(j:ℝ)|=(j.natAbs:ℝ) := by rw [← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast]
  have hj' : (16:ℝ)*j.natAbs ≤ N := by exact_mod_cast hj
  have hc' : (3:ℝ)*N ≤ 32*A.card := by exact_mod_cast hc
  have term (n) (hn : n∈A) :
      ((j.natAbs:ℝ)/(4*N))^2 ≤ ((j:ℝ)/(4*n)-round ((j:ℝ)/(4*n)))^2 := by
    obtain ⟨hn0,hnl,hnu⟩ := ha n hn
    have hn' : (0:ℝ)<n := by exact_mod_cast hn0
    have hnl' : (N:ℝ)≤16*n := by exact_mod_cast hnl
    have hnu' : (n:ℝ)≤N := by exact_mod_cast hnu
    have hdist : |(j:ℝ)/(4*n)| ≤ 1/4 := by
      rw [abs_div,abs_of_pos (by positivity : 0<(4:ℝ)*n),habs,div_le_iff₀ (by positivity)]
      linarith
    have hr : round ((j:ℝ)/(4*n))=0 := by
      apply round_eq_zero_iff.mpr
      obtain ⟨h1,h2⟩ := abs_le.mp hdist
      exact ⟨by linarith,by linarith⟩
    rw [hr,Int.cast_zero,sub_zero]
    calc
      _ ≤ (|(j:ℝ)/(4*n)|)^2 := by
        rw [abs_div,abs_of_pos (by positivity : 0<(4:ℝ)*n),habs]
        exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (by positivity)
          (by positivity) (by linarith)) 2
      _ = _ := sq_abs _
  have hb := sum_le_sum term
  simp only [sum_const,nsmul_eq_mul] at hb
  apply Real.exp_le_exp.mpr
  suffices hbound : (j.natAbs:ℝ)^2/(1024*N) ≤ (8/27)*((A.card:ℝ)*((j.natAbs:ℝ)/(4*N))^2) by linarith
  field_simp [hN'.ne']
  nlinarith only [mul_nonneg (sq_nonneg (j.natAbs:ℝ)) (sub_nonneg.mpr hc'),
    mul_nonneg (sq_nonneg (j.natAbs:ℝ)) hN'.le]

lemma medium_exp (N k : ℕ) (hN : 0<N) (hk : N^3<k^5) :
    Real.exp (-((k:ℝ)^2/(1024*N))) ≤ ((1024^10*Nat.factorial 10:ℕ):ℝ)/N^2 := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have hh : (N:ℝ)^3 ≤ (k:ℝ)^5 := by exact_mod_cast hk.le
  have hpow : (N:ℝ)^12 ≤ (k:ℝ)^20 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity : (0:ℝ)≤(N:ℝ)^3) hh 4
  let u := (k:ℝ)^2/(1024*N)
  have he := Real.pow_div_factorial_le_exp u (by dsimp [u]; positivity : 0≤u) 10
  change Real.exp (-u) ≤ _
  rw [Real.exp_neg,← one_div,div_le_div_iff₀ (Real.exp_pos _) (by positivity),one_mul]
  calc
    (N:ℝ)^2 ≤ (k:ℝ)^20/N^10 := by rw [le_div_iff₀ (by positivity),← pow_add]; exact hpow
    _ = ((1024^10*Nat.factorial 10:ℕ):ℝ)*(u^10/(Nat.factorial 10:ℝ)) := by
      dsimp [u]; push_cast; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

lemma middle_card (Q N : ℕ) [NeZero Q] (T : Finset (ZMod (4*Q)))
    (h : ∀ j∈T,16*j.valMinAbs.natAbs ≤ N) : T.card ≤ 2*N+1 := by
  have hle : T.card ≤ (Icc (-(N:ℤ)) (N:ℤ)).card := by
    apply card_le_card_of_injOn ZMod.valMinAbs
    · intro j hj
      have hn := h j hj
      have ha := Int.abs_eq_natAbs j.valMinAbs
      apply mem_Icc.mpr
      omega
    · intro a _ b _ h; exact ZMod.valMinAbs_inj.mp h
  rw [Int.card_Icc] at hle
  omega

set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → OMA.R_Erdos294_erdos_294_R1_H1_R1.H2 := by
  classical
  rintro mass ⟨c,hc,far_estimate⟩
  refine ⟨c,hc,?_⟩
  let K : ℕ := 1024^10 * Nat.factorial 10
  filter_upwards [mass c hc,far_estimate,eventually_ge_atTop (8*K+1)] with N hm hf hlarge
  let Q := Nat.lcmUpto ⌊c*(N:ℝ)/((Real.log N)^3*(Real.log (Real.log N))^4)⌋₊
  have hQ : 0<Q := Nat.lcmUpto_pos _
  letI : NeZero Q := ⟨hQ.ne'⟩
  let A := (Icc 1 N).filter fun n => N≤16*n ∧ n ∣ Q
  let V := ∑ n ∈ A,Q/n
  have ha (n) (hn:n∈A) : 0<n ∧ N≤16*n ∧ n≤N ∧ n∣Q := by
    obtain ⟨hi,hl,hd⟩ := mem_filter.mp hn
    obtain ⟨hp,hu⟩ := mem_Icc.mp hi
    exact ⟨hp,hl,hu,hd⟩
  change 3*Q ≤ 2*V ∧ V ≤ 3*Q at hm
  refine ⟨A,ha,hm.1,hm.2,?_⟩
  intro t hmin hmax
  have hN : 0<N := by omega
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have hV : 0<V := by omega
  have hV' : (0:ℝ)<V := by exact_mod_cast hV
  let p : ℝ := (t:ℝ)/V
  have hp : 1/9 ≤ p := by
    apply (le_div_iff₀ hV').mpr
    have h : (V:ℝ)≤9*t := by exact_mod_cast (show V≤9*t by omega)
    linarith
  have hp' : p ≤ 2/3 := by
    apply (div_le_iff₀ hV').mpr
    have h : (3:ℝ)*t ≤ 2*V := by exact_mod_cast (show 3*t≤2*V by omega)
    linarith
  let low := univ.filter fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5≤N^3
  let far := univ.filter fun h : ZMod (4*Q) => N<16*h.valMinAbs.natAbs
  let mid := lowᶜ.filter fun h => 16*h.valMinAbs.natAbs≤N
  let W (h : ZMod (4*Q)) := Real.exp (-(8/27:ℝ)*∑ n∈A,
    ((h.valMinAbs:ℝ)/(4*n)-round ((h.valMinAbs:ℝ)/(4*n)))^2)
  let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t:ZMod (4*Q)))*h) *
    ∏ n∈A,(1-(p:ℂ)+(p:ℂ)*ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h))
  change (∑ h∈far,W h) < 1/2 at hf
  have hF (h) : ‖F h‖≤W h := by
    dsimp only [F,W]
    rw [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul,norm_prod]
    rw [mul_sum,Real.exp_sum]
    apply prod_le_prod (fun _ _ => norm_nonneg _)
    intro n hn
    rw [char_fraction Q n (ha _ hn).1 (ha _ hn).2.2.2]
    exact factor_decay p _ hp hp'
  have hcard := mass_card N Q A (fun n hn => ⟨(ha _ hn).2.1,(ha _ hn).2.2.2⟩) hm.1
  have hmid (h) (hh : h∈mid) : W h ≤ (K:ℝ)/N^2 := by
    obtain ⟨hl,hm'⟩ := mem_filter.mp hh
    have hhi : N^3 < h.valMinAbs.natAbs^5 := by
      simpa [low,ZMod.valMinAbs_natAbs_eq_min] using hl
    exact (medium_weight N hN A (fun n hn => ⟨(ha _ hn).1,(ha _ hn).2.1,(ha _ hn).2.2.1⟩)
      hcard h.valMinAbs hm').trans (medium_exp N _ hN hhi)
  have hcount := middle_card Q N mid (fun _ h => (mem_filter.mp h).2)
  have hmid_total : (∑ h∈mid,W h) < 1/2 := calc
    _ ≤ ∑ _h∈mid,(K:ℝ)/N^2 := sum_le_sum hmid
    _ = (mid.card:ℝ)*((K:ℝ)/N^2) := by simp
    _ ≤ (2*(N:ℝ)+1)*((K:ℝ)/N^2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcount
    _ < 1/2 := by
      have hNK : (8:ℝ)*K+1 ≤ N := by exact_mod_cast hlarge
      have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
      rw [← mul_div_assoc,div_lt_iff₀ (by positivity)]
      have h1 := mul_le_mul_of_nonneg_right (show 2*(N:ℝ)+1≤3*N by linarith) (show (0:ℝ)≤K by positivity)
      have h2 := mul_lt_mul_of_pos_left (show 6*(K:ℝ)<N by linarith [show (0:ℝ)≤K by positivity]) hN'
      calc
        _ ≤ 3*(N:ℝ)*K := h1
        _ = (1/2:ℝ)*(N*(6*(K:ℝ))) := by ring
        _ < (1/2:ℝ)*(N*N) := mul_lt_mul_of_pos_left h2 (by norm_num)
        _ = _ := by ring
  have hrest : lowᶜ.filter (fun h => ¬ 16*h.valMinAbs.natAbs≤N) ⊆ far := by
    intro h hh
    exact mem_filter.mpr ⟨mem_univ _,lt_of_not_ge (mem_filter.mp hh).2⟩
  have he := sum_filter_add_sum_filter_not lowᶜ (fun h => 16*h.valMinAbs.natAbs≤N) W
  have hfar := sum_le_sum_of_subset_of_nonneg (f:=W) hrest (fun h _ _ => (Real.exp_pos _).le)
  change (∑ h∈mid,W h) + _ = _ at he
  have bound : (∑ h∈lowᶜ,W h)<1 := by linarith
  have complete := lt_of_le_of_lt ((norm_sum_le lowᶜ F).trans (sum_le_sum (fun h _ => hF h))) bound
  have hpC : (p:ℂ) = (t:ℂ)/(V:ℂ) := by simp only [p,Complex.ofReal_div, Complex.ofReal_natCast]
  dsimp only [F] at complete
  rw [hpC] at complete
  exact complete

end OMA.R_Erdos294_erdos_294_R1_H1_R1_H2_R1

end

section

open Finset Complex
namespace OMA.EgyptianFourier

private lemma cubic (u : ℝ) (hu : |u| ≤ 1) :
    ‖Complex.exp ((u:ℂ)*I) - (1+(u:ℂ)*I-(u:ℂ)^2/2)‖ ≤ 3*|u|^3 := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((u:ℂ)*I) 3
  have hn : ‖(u:ℂ)*I‖ = |u| := by simp
  rw [hn] at h
  have hpoly : (∑ m ∈ range 3, ((u:ℂ)*I)^m / m.factorial) =
      1+(u:ℂ)*I-(u:ℂ)^2/2 := by
    norm_num [sum_range_succ,mul_pow,Complex.I_sq]
    <;> ring
  rw [hpoly] at h
  have he : Real.exp |u| ≤ 3 := (Real.exp_le_exp.mpr hu).trans
    (by linarith [Real.exp_one_lt_d9])
  nlinarith only [h,mul_le_mul_of_nonneg_left he (pow_nonneg (abs_nonneg u) 3)]

private lemma centered (p x : ℝ) (hp : 0≤p) (hp' : p≤1) (hx : |x|≤1) :
    ‖(1-(p:ℂ))*Complex.exp (((-p*x:ℝ):ℂ)*I) +
      (p:ℂ)*Complex.exp ((((1-p)*x:ℝ):ℂ)*I) -
      ((1-p*(1-p)*x^2/2:ℝ):ℂ)‖ ≤ 3*|x|^3 := by
  let q (s:ℝ) : ℂ := 1+(s:ℂ)*I-(s:ℂ)^2/2
  let E (s:ℝ) : ℂ := Complex.exp ((s:ℂ)*I)-q s
  have hl : |(-p)*x| ≤ |x| := by
    rw [abs_mul,abs_neg,abs_of_nonneg hp]
    exact mul_le_of_le_one_left (abs_nonneg _) hp'
  have hr : |(1-p)*x| ≤ |x| := by
    rw [abs_mul,abs_of_nonneg (by linarith : 0≤1-p)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
  have hE (s:ℝ) (h : |s|≤|x|) : ‖E s‖ ≤ 3*|x|^3 :=
    (cubic _ (h.trans hx)).trans (by gcongr)
  calc
    _ = ‖(1-(p:ℂ))*E (-p*x)+(p:ℂ)*E ((1-p)*x)‖ := by
      congr 1
      dsimp only [E,q]
      push_cast
      ring
    _ ≤ ‖(1-(p:ℂ))*E (-p*x)‖ + ‖(p:ℂ)*E ((1-p)*x)‖ := norm_add_le _ _
    _ = (1-p)*‖E (-p*x)‖ + p*‖E ((1-p)*x)‖ := by
      rw [norm_mul,norm_mul,←Complex.ofReal_one,←Complex.ofReal_sub]
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp,
        abs_of_nonneg (by linarith : 0≤1-p)]
    _ ≤ (1-p)*(3*|x|^3)+p*(3*|x|^3) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hE _ hl) (by linarith))
        (mul_le_mul_of_nonneg_left (hE _ hr) hp)
    _ = _ := by ring

/-- A product of centered Bernoulli factors has nonnegative real part if
each increment is small and their absolute cubes have small total. -/
theorem positive_product (A : Finset ℕ) (p : ℝ) (x : ℕ → ℝ)
    (hp : 0≤p) (hp' : p≤1) (hx : ∀ n ∈ A, |x n|≤1)
    (hsmall : 6*(∑ n ∈ A, |x n|^3) ≤ 1/4) :
    0 ≤ (∏ n ∈ A, ((1-(p:ℂ))*Complex.exp (((-p*x n:ℝ):ℂ)*I) +
      (p:ℂ)*Complex.exp ((((1-p)*x n:ℝ):ℂ)*I))).re := by
  let d (n:ℕ) : ℝ := 1-p*(1-p)*(x n)^2/2
  let z (n:ℕ) : ℂ := (1-(p:ℂ))*Complex.exp (((-p*x n:ℝ):ℂ)*I) +
      (p:ℂ)*Complex.exp ((((1-p)*x n:ℝ):ℂ)*I)
  let e (n:ℕ) : ℂ := (z n-(d n:ℂ))/(d n:ℂ)
  have hd (n) (hn:n∈A) : 1/2 ≤ d n := by
    have hb := abs_le.mp (hx n hn)
    have h1 : (x n)^2 ≤ 1 := by nlinarith [mul_nonneg (show 0≤1-x n by linarith) (show 0≤1+x n by linarith)]
    have h2 : p*(1-p) ≤ 1 := by nlinarith [sq_nonneg p]
    dsimp only [d]
    nlinarith only [mul_le_mul h2 h1 (sq_nonneg _) (by norm_num : (0:ℝ)≤1)]
  have he (n) (hn:n∈A) : ‖e n‖ ≤ 6*|x n|^3 := by
    have hdpos : 0<d n := by linarith [hd n hn]
    dsimp only [e]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hdpos.le,div_le_iff₀ hdpos]
    have h := centered p (x n) hp hp' (hx n hn)
    change ‖z n-(d n:ℂ)‖ ≤ _ at h
    nlinarith only [h,mul_le_mul_of_nonneg_left (hd n hn) (show 0≤6*|x n|^3 by positivity)]
  have herr : (∑ n ∈ A, ‖e n‖) ≤ 1/4 := calc
    _ ≤ ∑ n ∈ A, 6*|x n|^3 := sum_le_sum he
    _ ≤ _ := by rwa [←mul_sum]
  have hn := A.norm_prod_one_add_sub_one_le e
  have hequarter : Real.exp (1/4) < 2 := (Real.exp_lt_two_add_div_two_sub (by norm_num) (by norm_num)).trans (by norm_num)
  have hab := Complex.abs_re_le_norm ((∏ n ∈ A, (1+e n))-1)
  rw [Complex.sub_re,Complex.one_re] at hab
  have hpos : 0 ≤ (∏ n ∈ A, (1+e n)).re := by
    linarith [(abs_le.mp (hab.trans hn)).1, Real.exp_le_exp.mpr herr]
  change 0 ≤ (∏ n ∈ A, z n).re
  have hz (n) (hn:n∈A) : z n = (d n:ℂ)*(1+e n) := by
    have hdpos : 0<d n := by linarith [hd n hn]
    dsimp only [e]
    field_simp [show (d n:ℂ) ≠ 0 by exact_mod_cast hdpos.ne']
    <;> ring
  rw [prod_congr rfl hz,prod_mul_distrib,←Complex.ofReal_prod]
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg (prod_nonneg fun n hn => (show 0≤d n by linarith [hd n hn])) hpos



private lemma frequencies (N k : ℕ) (hN : 1000000^5 ≤ N) (hk : k^5 ≤ N^3) :
    32*k ≤ N ∧ 786432*k^3 ≤ N^2 := by
  have hge : 1≤N := by omega
  constructor
  · apply (Nat.pow_le_pow_iff_left (by decide : (5:ℕ)≠0)).mp
    calc
      (32*k)^5 = 32^5*k^5 := mul_pow _ _ _
      _ ≤ N*N^3 := Nat.mul_le_mul (by omega) hk
      _ = N^4 := by ring
      _ ≤ N^5 := Nat.pow_le_pow_right hge (by decide)
  · apply (Nat.pow_le_pow_iff_left (by decide : (5:ℕ)≠0)).mp
    calc
      (786432*k^3)^5 = 786432^5*(k^5)^3 := by ring
      _ ≤ N*(N^3)^3 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hk 3)
      _ = (N^2)^5 := by ring

private lemma char_int (M : ℕ) [NeZero M] (r j : ℤ) :
    ZMod.stdAddChar ((r:ZMod M)*(j:ZMod M)) =
      Complex.exp (((2*Real.pi*(j:ℝ)/(M:ℝ)*(r:ℝ):ℝ):ℂ)*I) := by
  rw [←Int.cast_mul,ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private lemma centers (A : Finset ℕ) (w : ℕ → ℕ) (t : ℕ) (u : ℝ) (p : ℝ)
    (hp : p*(∑ n ∈ A,(w n:ℝ))=t) :
    Complex.exp (((u*(-(t:ℝ)):ℝ):ℂ)*I) *
      (∏ n ∈ A, (1-(p:ℂ)+(p:ℂ)*Complex.exp (((u*w n:ℝ):ℂ)*I))) =
    ∏ n ∈ A, ((1-(p:ℂ))*Complex.exp (((-p*(u*w n):ℝ):ℂ)*I) +
      (p:ℂ)*Complex.exp ((((1-p)*(u*w n):ℝ):ℂ)*I)) := by
  have he (n:ℕ) : ((1-(p:ℂ))*Complex.exp (((-p*(u*w n):ℝ):ℂ)*I) +
      (p:ℂ)*Complex.exp ((((1-p)*(u*w n):ℝ):ℂ)*I)) =
      Complex.exp (((-p*(u*w n):ℝ):ℂ)*I) *
        (1-(p:ℂ)+(p:ℂ)*Complex.exp (((u*w n:ℝ):ℂ)*I)) := by
    push_cast
    rw [show (1-(p:ℂ))*((u:ℂ)*w n)*I = (-p:ℂ)*((u:ℂ)*w n)*I + (u:ℂ)*w n*I by ring,
      Complex.exp_add]
    ring
  simp_rw [he]
  rw [prod_mul_distrib,←Complex.exp_sum]
  congr 2
  have hx : u*(-(t:ℝ)) = ∑ n ∈ A, -p*(u*w n) := by
    simp_rw [show ∀ n : ℕ, -p*(u*w n)=(-u*p)*(w n) from fun n => by ring,←mul_sum]
    rw [←hp];ring
  rw [hx,Complex.ofReal_sum,Finset.sum_mul]


theorem low (N Q : ℕ) [NeZero Q] (hN : 1000000^5 ≤ N)
    (A : Finset ℕ) (ha : ∀ n ∈ A, 0<n ∧ N≤16*n ∧ n≤N ∧ n∣Q)
    (hmass : 3*Q ≤ 2*(∑ n ∈ A,Q/n)) (t : ℕ) (ht : t≤Q) :
    let V := ∑ n ∈ A,Q/n
    let P : ℂ := (t:ℂ)/(V:ℂ)
    let S := Finset.univ.filter (fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5 ≤ N^3)
    let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t:ZMod (4*Q)))*h) *
      ∏ n ∈ A, (1-P+P*ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h))
    1 ≤ (∑ h ∈ S,F h).re := by
  classical
  let V := ∑ n ∈ A,Q/n
  let p : ℝ := (t:ℝ)/V
  have hQ : 0<Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hV : 0<V := by change 3*Q ≤ 2*V at hmass; omega
  have hV' : (0:ℝ)<V := by exact_mod_cast hV
  have hp : 0≤p := by dsimp [p];positivity
  have hp' : p≤1 := by
    apply (div_le_iff₀ hV').mpr
    rw [one_mul]
    change 3*Q ≤ 2*V at hmass
    exact_mod_cast (show t≤V by omega)
  have hpV : p*(∑ n ∈ A,((Q/n:ℕ):ℝ))=t := by
    rw [←Nat.cast_sum]; exact div_mul_cancel₀ _ hV'.ne'
  let S := Finset.univ.filter (fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5 ≤ N^3)
  let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t:ZMod (4*Q)))*h) *
      ∏ n ∈ A, (1-(p:ℂ)+(p:ℂ)*ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h))
  have hP : (t:ℂ)/(V:ℂ)=(p:ℂ) := by simp [p]
  change 1 ≤ (∑ h ∈ S, ZMod.stdAddChar ((-(t:ZMod (4*Q)))*h) *
    ∏ n ∈ A, (1-(t:ℂ)/(V:ℂ)+(t:ℂ)/(V:ℂ)*ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h))).re
  rw [hP]
  change 1 ≤ (∑ h ∈ S,F h).re
  have hz : (0:ZMod (4*Q))∈S := by simp [S]
  have hzero : F 0=1 := by simp [F]
  have nonneg (h) (hh:h∈S) : 0≤(F h).re := by
    let j := ZMod.valMinAbs h
    let k := j.natAbs
    let u : ℝ := 2*Real.pi*j/((4*Q:ℕ):ℝ)
    let x (n:ℕ) : ℝ := u*(Q/n:ℕ)
    have hk : k^5≤N^3 := by
      have hh' := (Finset.mem_filter.mp hh).2
      simpa only [k,j,ZMod.valMinAbs_natAbs_eq_min] using hh'
    obtain ⟨hlin,hcub⟩ := frequencies N k hN hk
    have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hQp : (0:ℝ)<Q := by exact_mod_cast hQ
    have hjabs : |(j:ℝ)|=(k:ℝ) := by
      dsimp only [k]; rw [←Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    have hx (n : ℕ) (hn:n∈A) : |x n| ≤ 32*(k:ℝ)/N := by
      obtain ⟨hn₀,hn₁,_,hd⟩ := ha n hn
      have hnpos : (0:ℝ)<n := by exact_mod_cast hn₀
      have hdiv : ((Q/n:ℕ):ℝ) = Q/n := by
        apply (eq_div_iff hnpos.ne').mpr
        exact_mod_cast Nat.div_mul_cancel hd
      have heq : x n = Real.pi*j/(2*n) := by
        dsimp only [x,u]; rw [hdiv];push_cast
        field_simp;ring
      rw [heq,abs_div,abs_mul,abs_of_pos Real.pi_pos,hjabs,
        abs_of_pos (by positivity : (0:ℝ)<2*n)]
      apply (div_le_div_iff₀ (by positivity) hNp).mpr
      calc
        _ ≤ (4*(k:ℝ))*(16*n) := mul_le_mul
          (mul_le_mul_of_nonneg_right Real.pi_le_four (by positivity)) (by exact_mod_cast hn₁)
          (by positivity) (by positivity)
        _ = _ := by ring
    have hx₁ (n) (hn:n∈A) : |x n|≤1 := (hx n hn).trans
      ((div_le_one hNp).mpr (by exact_mod_cast hlin))
    have hcard : A.card ≤ N := by
      have hs : A ⊆ Finset.Icc 1 N := fun n hn => Finset.mem_Icc.mpr
        ⟨(ha n hn).1,(ha n hn).2.2.1⟩
      simpa using Finset.card_le_card hs
    have hsum : (∑ n ∈ A, |x n|^3) ≤ (N:ℝ)*(32*k/N)^3 := calc
      _ ≤ ∑ _n ∈ A,(32*(k:ℝ)/N)^3 := sum_le_sum fun n hn => by gcongr;exact hx n hn
      _ = (A.card:ℝ)*(32*k/N)^3 := by simp
      _ ≤ _ := by gcongr
    have hsmall : 6*(∑ n ∈ A,|x n|^3) ≤ 1/4 := by
      apply le_trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
      apply (mul_le_mul_iff_of_pos_right (pow_pos hNp 2)).mp
      calc
        _ = 196608*(k:ℝ)^3 := by field_simp;ring
        _ ≤ _ := by
          have hc : 786432*(k:ℝ)^3 ≤ (N:ℝ)^2 := by exact_mod_cast hcub
          linarith
    have hchar (r:ℤ) : ZMod.stdAddChar ((r:ZMod (4*Q))*h) =
        Complex.exp (((u*(r:ℝ):ℝ):ℂ)*I) := by
      have H := char_int (4*Q) r j
      rw [show (j:ZMod (4*Q)) = h from h.coe_valMinAbs] at H
      exact H
    have hneg := hchar (-(t:ℤ))
    push_cast at hneg
    have hpos (n:ℕ) : ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h) =
        Complex.exp (((u*(Q/n:ℕ):ℝ):ℂ)*I) := by simpa only [Int.cast_natCast] using hchar ((Q/n:ℕ):ℤ)
    dsimp only [F]
    simp_rw [hneg,hpos]
    have hcen := centers A (fun n=>Q/n) t u p hpV
    push_cast at hcen ⊢
    rw [hcen]
    have H := positive_product A p x hp hp' hx₁ hsmall
    dsimp only [x] at H
    push_cast at H
    exact H
  have h := Finset.single_le_sum nonneg hz
  rw [hzero,Complex.one_re] at h
  simpa only [Complex.re_sum] using h

end OMA.EgyptianFourier

open Filter

theorem OMA.erdos294Fourier : OMA.R_Erdos294_erdos_294_R1_H1_R1.H1 := by
  filter_upwards [eventually_ge_atTop (1000000^5 : ℕ)] with N hN
  intro Q _ A ha hmass _ t _ ht
  exact OMA.EgyptianFourier.low N Q hN A ha hmass t ht

end

section

/-! Reciprocal mass bounds on smooth integers in dyadic intervals. -/

open Finset Filter

namespace Erdos294StepH1

private lemma sum_biUnion_le_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ b ∈ s.biUnion t, f b) ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    have hunion :
        (∑ b ∈ t a ∪ s.biUnion t, f b) ≤ (∑ b ∈ t a, f b) + ∑ b ∈ s.biUnion t, f b := by
      have h := sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hinter : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b := sum_nonneg fun b _ => hf b
      linarith
    linarith

private lemma sum_image_le_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ b ∈ s.image g, f b) ≤ ∑ a ∈ s, f (g a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [image_insert, sum_insert ha]
    by_cases hmem : g a ∈ s.image g
    · rw [insert_eq_of_mem hmem]
      linarith [hf (g a)]
    · rw [sum_insert hmem]
      linarith

private lemma exp_two_lt_eight : Real.exp 2 < 8 := by
  have h1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith

private lemma eighteen_lt_exp_three : (18 : ℝ) < Real.exp 3 := by
  have h1 : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
  nlinarith

private lemma four_lt_exp_two : (4 : ℝ) < Real.exp 2 := by
  have h1 : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith

private lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos (1 / 2)
  have hexp : Real.exp (1 / 2) < 2 := by nlinarith
  have hlog := Real.log_lt_log hpos hexp
  rwa [Real.log_exp] at hlog

private lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) four_lt_exp_two.le
  rwa [Real.log_exp] at h

private lemma log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) : (Real.log x) ^ 2 ≤ 4 * x := by
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hexp : Real.log x / 2 + 1 ≤ Real.exp (Real.log x / 2) :=
    Real.add_one_le_exp (Real.log x / 2)
  have hsq : Real.exp (Real.log x / 2) * Real.exp (Real.log x / 2) = x := by
    rw [← Real.exp_add, add_halves, Real.exp_log (by linarith)]
  have hpos : 0 < Real.exp (Real.log x / 2) := Real.exp_pos (Real.log x / 2)
  nlinarith

private lemma interval_eq_Ico {N : ℕ} (hN : 256 ≤ N) :
    ((Icc 1 N).filter fun n => N ≤ 16 * n) = Ico ((N + 15) / 16) (N + 1) := by
  ext n
  simp only [mem_filter, mem_Icc, mem_Ico]
  omega

private lemma sum_Ico_telescope (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Ico a b, (f (k + 1) - f k)) = f b - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [sum_Ico_succ_top hmn, ih]
    ring

private lemma harmonic_bounds {N : ℕ} (hN : 256 ≤ N) :
    (2 : ℝ) ≤ (∑ n ∈ (Icc 1 N).filter (fun n => N ≤ 16 * n), 1 / (n : ℝ)) ∧
      (∑ n ∈ (Icc 1 N).filter (fun n => N ≤ 16 * n), 1 / (n : ℝ)) ≤ 3 := by
  rw [interval_eq_Ico hN]
  set m := (N + 15) / 16
  have hm4 : 16 ≤ m := by omega
  have hmN : m ≤ N + 1 := by omega
  constructor
  · have hstep : ∀ k ∈ Ico m (N + 1),
        Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≤ 1 / (k : ℝ) := by
      intro k hk
      have hk1 : 1 ≤ k := by
        have := (mem_Ico.mp hk).1
        omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
      have hdivpos : 0 < ((k : ℝ) + 1) / (k : ℝ) := by positivity
      have hlog := Real.log_le_sub_one_of_pos hdivpos
      rw [Real.log_div (by positivity) hkpos.ne'] at hlog
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have hrhs : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
        field_simp [hkpos.ne']
        ring
      rw [hcast]
      linarith
    have htel := sum_Ico_telescope (fun k : ℕ => Real.log (k : ℝ)) hmN
    have hsum := sum_le_sum hstep
    rw [htel] at hsum
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hratio : (8 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / (m : ℝ) := by
      rw [le_div_iff₀ hmpos]
      have hnat : 8 * m ≤ N + 1 := by omega
      exact_mod_cast hnat
    have hlog8 : Real.log 8 ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      rw [← Real.log_div (by positivity) hmpos.ne']
      exact Real.log_le_log (by norm_num) hratio
    have h2log8 : (2 : ℝ) ≤ Real.log 8 := by
      have h := Real.log_le_log (Real.exp_pos 2) exp_two_lt_eight.le
      rwa [Real.log_exp] at h
    linarith
  · let g : ℕ → ℝ := fun j => Real.log ((j - 1 : ℕ) : ℝ)
    have hstep : ∀ k ∈ Ico m (N + 1), 1 / (k : ℝ) ≤ g (k + 1) - g k := by
      intro k hk
      have hk2 : 2 ≤ k := by
        have := (mem_Ico.mp hk).1
        omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hk1pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < k - 1 by omega)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hk1pos hkpos)
      rw [Real.log_div hk1pos.ne' hkpos.ne'] at hlog
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have : (k - 1) + 1 = k := by omega
        have h' : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by exact_mod_cast this
        linarith
      have hrhs : ((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1 = -(1 / (k : ℝ)) := by
        rw [hcast]
        field_simp [hkpos.ne']
        ring
      have hg : g (k + 1) - g k = Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ) := by
        dsimp [g]
      rw [hg]
      linarith
    have htel := sum_Ico_telescope g hmN
    have hsum := sum_le_sum hstep
    rw [htel] at hsum
    have hgm : g (N + 1) - g m = Real.log (N : ℝ) - Real.log ((m - 1 : ℕ) : ℝ) := by
      dsimp [g]
    rw [hgm] at hsum
    have hm1pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < m - 1 by omega)
    have hratio : (N : ℝ) / ((m - 1 : ℕ) : ℝ) ≤ 18 := by
      rw [div_le_iff₀ hm1pos]
      have hnat : N ≤ 18 * (m - 1) := by omega
      exact_mod_cast hnat
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlog18 : Real.log (N : ℝ) - Real.log ((m - 1 : ℕ) : ℝ) ≤ Real.log 18 := by
      rw [← Real.log_div hNpos.ne' hm1pos.ne']
      exact Real.log_le_log (div_pos hNpos hm1pos) hratio
    have hlog18_le : Real.log 18 ≤ 3 := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 18) eighteen_lt_exp_three.le
      rwa [Real.log_exp] at h
    linarith

private lemma divisor_mass_le {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) :
    (∑ n ∈ ((Icc 1 N).filter fun n => N ≤ 16 * n).filter (fun n => d ∣ n), 1 / (n : ℝ)) ≤
      16 / (d : ℝ) := by
  set M := ((Icc 1 N).filter fun n => N ≤ 16 * n).filter (fun n => d ∣ n)
  have hcard : M.card ≤ N / d := by
    have hinj : M.card ≤ (Icc 1 (N / d)).card := by
      refine card_le_card_of_injOn (fun n => n / d) ?_ ?_
      · intro n hn
        obtain ⟨hnI, hdn⟩ := mem_filter.mp hn
        obtain ⟨hnIcc, _⟩ := mem_filter.mp hnI
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnIcc
        have hq1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) (by omega)
        exact mem_Icc.mpr ⟨hq1, Nat.div_le_div_right hnN⟩
      · intro a ha b hb hab
        obtain ⟨_, hda⟩ := mem_filter.mp ha
        obtain ⟨_, hdb⟩ := mem_filter.mp hb
        have ha' : d * (a / d) = a := Nat.mul_div_cancel' hda
        have hb' : d * (b / d) = b := Nat.mul_div_cancel' hdb
        dsimp only at hab
        rw [← ha', hab, hb']
    simpa using hinj
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hterm : ∀ n ∈ M, 1 / (n : ℝ) ≤ 16 / (N : ℝ) := by
    intro n hn
    obtain ⟨hnI, _⟩ := mem_filter.mp hn
    obtain ⟨hnIcc, hn16⟩ := mem_filter.mp hnI
    obtain ⟨hn1, _⟩ := mem_Icc.mp hnIcc
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn16' : (N : ℝ) ≤ 16 * (n : ℝ) := by exact_mod_cast hn16
    rw [div_le_div_iff₀ hnpos hNpos]
    linarith
  have hsum : (∑ n ∈ M, 1 / (n : ℝ)) ≤ (M.card : ℝ) * (16 / (N : ℝ)) := by
    calc
      (∑ n ∈ M, 1 / (n : ℝ)) ≤ ∑ _n ∈ M, 16 / (N : ℝ) := sum_le_sum hterm
      _ = (M.card : ℝ) * (16 / (N : ℝ)) := by simp
  have hdiv_le : ((N / d : ℕ) : ℝ) * (d : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N d
  have hcard_le : (M.card : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    have h1 : (M.card : ℝ) ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast hcard
    have h2 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := (le_div_iff₀ hdpos).mpr hdiv_le
    exact h1.trans h2
  calc
    (∑ n ∈ M, 1 / (n : ℝ)) ≤ (M.card : ℝ) * (16 / (N : ℝ)) := hsum
    _ ≤ ((N : ℝ) / (d : ℝ)) * (16 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard_le (by positivity)
    _ = 16 / (d : ℝ) := by
      field_simp [hNpos.ne', hdpos.ne']

private lemma large_squares_sum_le {y : ℕ} (hy : 16384 ≤ y) :
    (∑ m ∈ Icc (Nat.sqrt y + 1) y, 16 / ((m ^ 2 : ℕ) : ℝ)) ≤ 1 / 8 := by
  set z := Nat.sqrt y
  have hz128 : 128 ≤ z := Nat.le_sqrt.mpr (by omega)
  have hz_sq : z * z ≤ y := Nat.sqrt_le y
  have hzy : z + 1 ≤ y + 1 := by nlinarith
  have hIco : Icc (z + 1) y = Ico (z + 1) (y + 1) := by
    ext m
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hIco]
  let h : ℕ → ℝ := fun k => -(1 / ((k - 1 : ℕ) : ℝ))
  have hstep : ∀ m ∈ Ico (z + 1) (y + 1), 16 / ((m ^ 2 : ℕ) : ℝ) ≤ 16 * (h (m + 1) - h m) := by
    intro m hm
    have hm2 : 2 ≤ m := by
      have := (mem_Ico.mp hm).1
      omega
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hm1pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < m - 1 by omega)
    have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : (m - 1) + 1 = m := by omega
      have h' : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by exact_mod_cast this
      linarith
    have hdiff : h (m + 1) - h m = 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) := by
      dsimp [h]
      ring
    rw [hdiff, Nat.cast_pow]
    have hfrac : 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) = 1 / (((m - 1 : ℕ) : ℝ) * (m : ℝ)) := by
      rw [hmcast]
      field_simp [hmpos.ne', (show (m : ℝ) - 1 ≠ 0 by linarith)]
      ring
    rw [hfrac]
    have hle : ((m - 1 : ℕ) : ℝ) * (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rw [hmcast]
      nlinarith
    have hdiv : 1 / ((m : ℝ) ^ 2) ≤ 1 / (((m - 1 : ℕ) : ℝ) * (m : ℝ)) :=
      one_div_le_one_div_of_le (mul_pos hm1pos hmpos) hle
    have h16eq : 16 / ((m : ℝ) ^ 2) = 16 * (1 / ((m : ℝ) ^ 2)) := by ring
    linarith
  have hsum := sum_le_sum hstep
  have hsub_eq : (∑ i ∈ Ico (z + 1) (y + 1), (h (i + 1) - h i)) = h (y + 1) - h (z + 1) :=
    sum_Ico_telescope h hzy
  rw [← mul_sum, hsub_eq] at hsum
  have htel : h (y + 1) - h (z + 1) = 1 / (z : ℝ) - 1 / (y : ℝ) := by
    dsimp [h]
    ring
  rw [htel] at hsum
  have hy_nonneg : 0 ≤ 1 / (y : ℝ) := by positivity
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hz128' : (128 : ℝ) ≤ z := by exact_mod_cast hz128
  have h16z : 16 / (z : ℝ) ≤ 1 / 8 := by
    rw [div_le_iff₀ hzpos]
    linarith
  have h16dist : 16 * (1 / (z : ℝ) - 1 / (y : ℝ)) = 16 / (z : ℝ) - 16 * (1 / (y : ℝ)) := by ring
  linarith

private lemma small_powers_sum_le {y : ℕ} (hy : 16384 ≤ y) :
    (∑ m ∈ Icc 2 (Nat.sqrt y), 16 / ((m ^ (m.log y + 1) : ℕ) : ℝ)) ≤ 1 / 8 := by
  set z := Nat.sqrt y
  have hz128 : 128 ≤ z := Nat.le_sqrt.mpr (by omega)
  have hz_sq : (z : ℝ) ^ 2 ≤ (y : ℝ) := by
    have : z * z ≤ y := Nat.sqrt_le y
    have hcast : (z : ℝ) * (z : ℝ) ≤ (y : ℝ) := by exact_mod_cast this
    nlinarith
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hterm : ∀ m ∈ Icc 2 z, 16 / ((m ^ (m.log y + 1) : ℕ) : ℝ) ≤ 16 / ((z : ℝ) ^ 2) := by
    intro m hm
    have hm1 : 1 < m := by
      have := (mem_Icc.mp hm).1
      omega
    have hyd : y < m ^ (m.log y + 1) := Nat.lt_pow_succ_log_self hm1 y
    have hyd' : (y : ℝ) < ((m ^ (m.log y + 1) : ℕ) : ℝ) := by exact_mod_cast hyd
    exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hzpos 2) (hz_sq.trans hyd'.le)
  have hsum :
      (∑ m ∈ Icc 2 z, 16 / ((m ^ (m.log y + 1) : ℕ) : ℝ)) ≤
        ((Icc 2 z).card : ℝ) * (16 / ((z : ℝ) ^ 2)) := by
    calc
      _ ≤ ∑ _m ∈ Icc 2 z, 16 / ((z : ℝ) ^ 2) := sum_le_sum hterm
      _ = ((Icc 2 z).card : ℝ) * (16 / ((z : ℝ) ^ 2)) := by simp
  have hcard : (Icc 2 z).card ≤ z := by
    rw [Nat.card_Icc]
    omega
  have hcard' : ((Icc 2 z).card : ℝ) ≤ (z : ℝ) := by exact_mod_cast hcard
  have hz128' : (128 : ℝ) ≤ z := by exact_mod_cast hz128
  calc
    (∑ m ∈ Icc 2 z, 16 / ((m ^ (m.log y + 1) : ℕ) : ℝ)) ≤
        ((Icc 2 z).card : ℝ) * (16 / ((z : ℝ) ^ 2)) := hsum
    _ ≤ (z : ℝ) * (16 / ((z : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = 16 / (z : ℝ) := by
      field_simp [hzpos.ne']
    _ ≤ 1 / 8 := by
      rw [div_le_iff₀ hzpos]
      linarith

private lemma dyadic_block_primes_le {y : ℕ} (hy : 2 ≤ y) (k : ℕ) :
    (∑ p ∈ (Ioc (2 ^ k * y) (2 ^ (k + 1) * y)).filter Nat.Prime, 16 / (p : ℝ)) ≤
      64 / Real.log (y : ℝ) := by
  set P := (Ioc (2 ^ k * y) (2 ^ (k + 1) * y)).filter Nat.Prime
  set A : ℕ := 2 ^ k * y
  set B : ℕ := 2 ^ (k + 1) * y
  have hApos_nat : 0 < A := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hApos : (0 : ℝ) < A := by exact_mod_cast hApos_nat
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hy1
  have hterm : ∀ p ∈ P, 16 / (p : ℝ) ≤ 16 * Real.log (p : ℝ) / ((A : ℝ) * Real.log (y : ℝ)) := by
    intro p hp
    simp only [P, mem_filter, mem_Ioc] at hp
    obtain ⟨⟨hAp, _⟩, _⟩ := hp
    have hAp' : (A : ℝ) < (p : ℝ) := by exact_mod_cast hAp
    have hyp : (y : ℝ) ≤ (p : ℝ) := by
      have : y ≤ A := Nat.le_mul_of_pos_left y (Nat.pow_pos (by decide))
      have h' : (y : ℝ) ≤ (A : ℝ) := by exact_mod_cast this
      linarith
    have hppos : (0 : ℝ) < p := lt_trans hApos hAp'
    have hlogp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log (by positivity) hyp
    rw [div_le_div_iff₀ hppos (mul_pos hApos hlogy)]
    nlinarith [mul_le_mul_of_nonneg_left hlogp (by positivity : (0 : ℝ) ≤ 16 * (p : ℝ)),
      mul_le_mul_of_nonneg_right hAp'.le (by positivity : (0 : ℝ) ≤ 16 * Real.log (y : ℝ))]
  have hsum1 :
      (∑ p ∈ P, 16 / (p : ℝ)) ≤
        (16 / ((A : ℝ) * Real.log (y : ℝ))) * ∑ p ∈ P, Real.log (p : ℝ) := by
    calc
      (∑ p ∈ P, 16 / (p : ℝ)) ≤
          ∑ p ∈ P, 16 * Real.log (p : ℝ) / ((A : ℝ) * Real.log (y : ℝ)) := sum_le_sum hterm
      _ = ∑ p ∈ P, (16 / ((A : ℝ) * Real.log (y : ℝ))) * Real.log (p : ℝ) := by
        refine sum_congr rfl fun p _ => ?_
        ring
      _ = (16 / ((A : ℝ) * Real.log (y : ℝ))) * ∑ p ∈ P, Real.log (p : ℝ) := by
        rw [← mul_sum]
  have hsub : P ⊆ (Ioc 0 ⌊(B : ℝ)⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [P, mem_filter, mem_Ioc, Nat.floor_natCast] at hp ⊢
    exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have htheta_sub : (∑ p ∈ P, Real.log (p : ℝ)) ≤ Chebyshev.theta (B : ℝ) := by
    unfold Chebyshev.theta
    exact sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
  have htheta_ub : Chebyshev.theta (B : ℝ) ≤ Real.log 4 * (B : ℝ) :=
    Chebyshev.theta_le_log4_mul_x (by positivity)
  have hBA : (B : ℝ) = 2 * (A : ℝ) := by
    dsimp [A, B]
    rw [pow_succ']
    push_cast
    ring
  have hlogsum : (∑ p ∈ P, Real.log (p : ℝ)) ≤ 4 * (A : ℝ) := by
    have h4 : Real.log 4 * (B : ℝ) ≤ 2 * (B : ℝ) :=
      mul_le_mul_of_nonneg_right log_four_le_two (by positivity)
    linarith
  calc
    (∑ p ∈ P, 16 / (p : ℝ)) ≤
        (16 / ((A : ℝ) * Real.log (y : ℝ))) * ∑ p ∈ P, Real.log (p : ℝ) := hsum1
    _ ≤ (16 / ((A : ℝ) * Real.log (y : ℝ))) * (4 * (A : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogsum (by positivity)
    _ = 64 / Real.log (y : ℝ) := by
      field_simp [hApos.ne', hlogy.ne']
      ring

private lemma large_primes_sum_le {N y : ℕ} (hy : 2 ≤ y) :
    (∑ p ∈ (Ioc y N).filter Nat.Prime, 16 / (p : ℝ)) ≤
      64 * ((Nat.log 2 (N / y) + 1 : ℕ) : ℝ) / Real.log (y : ℝ) := by
  set K := Nat.log 2 (N / y) + 1
  let block : ℕ → Finset ℕ := fun k => (Ioc (2 ^ k * y) (2 ^ (k + 1) * y)).filter Nat.Prime
  have hcover : (Ioc y N).filter Nat.Prime ⊆ (range K).biUnion block := by
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    obtain ⟨⟨hyp, hpN⟩, hprime⟩ := hp
    let q := (p - 1) / y
    have hq1 : 1 ≤ q := Nat.div_pos (by omega) (by omega)
    have hqN : q ≤ N / y := Nat.div_le_div_right (by omega)
    let k := Nat.log 2 q
    have hkK : k < K := by
      have : k ≤ Nat.log 2 (N / y) := Nat.log_mono_right hqN
      omega
    have hpow_le : 2 ^ k ≤ q := Nat.pow_log_le_self 2 (by omega)
    have hlow : 2 ^ k * y < p := by
      have h1 : 2 ^ k * y ≤ q * y := Nat.mul_le_mul_right y hpow_le
      have h2 : q * y ≤ p - 1 := Nat.div_mul_le_self (p - 1) y
      omega
    have hpow_gt : q < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) q
    have hhigh : p ≤ 2 ^ (k + 1) * y := by
      have h1 : q + 1 ≤ 2 ^ (k + 1) := by omega
      have h2 : (q + 1) * y ≤ 2 ^ (k + 1) * y := Nat.mul_le_mul_right y h1
      have hdiv := Nat.div_add_mod (p - 1) y
      have hmod : (p - 1) % y < y := Nat.mod_lt (p - 1) (by omega)
      have hmul : (q + 1) * y = y * ((p - 1) / y) + y := by
        dsimp [q]
        ring
      have h3 : p ≤ (q + 1) * y := by omega
      exact h3.trans h2
    exact mem_biUnion.mpr ⟨k, mem_range.mpr hkK, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hlow, hhigh⟩, hprime⟩⟩
  have h1 :
      (∑ p ∈ (Ioc y N).filter Nat.Prime, 16 / (p : ℝ)) ≤
        ∑ p ∈ (range K).biUnion block, 16 / (p : ℝ) :=
    sum_le_sum_of_subset_of_nonneg hcover fun p _ _ => by positivity
  have h2 :
      (∑ p ∈ (range K).biUnion block, 16 / (p : ℝ)) ≤
        ∑ k ∈ range K, ∑ p ∈ block k, 16 / (p : ℝ) :=
    sum_biUnion_le_sum (range K) block (fun p => 16 / (p : ℝ)) (fun p => by positivity)
  have h3 :
      (∑ k ∈ range K, ∑ p ∈ block k, 16 / (p : ℝ)) ≤
        ∑ _k ∈ range K, 64 / Real.log (y : ℝ) :=
    sum_le_sum fun k _ => dyadic_block_primes_le hy k
  calc
    (∑ p ∈ (Ioc y N).filter Nat.Prime, 16 / (p : ℝ)) ≤
        ∑ _k ∈ range K, 64 / Real.log (y : ℝ) := (h1.trans h2).trans h3
    _ = ((K : ℕ) : ℝ) * (64 / Real.log (y : ℝ)) := by simp
    _ = 64 * ((K : ℕ) : ℝ) / Real.log (y : ℝ) := by ring

private lemma bad_reciprocal_sum_le {N y : ℕ} (hN : 256 ≤ N) (hy : 16384 ≤ y)
    (hKlog : 64 * ((Nat.log 2 (N / y) + 1 : ℕ) : ℝ) / Real.log (y : ℝ) ≤ 1 / 4) :
    (∑ n ∈ ((Icc 1 N).filter fun n => N ≤ 16 * n).filter (fun n => ¬ n ∣ Nat.lcmUpto y),
      1 / (n : ℝ)) ≤ 1 / 2 := by
  set I_N := (Icc 1 N).filter fun n => N ≤ 16 * n
  set Q := Nat.lcmUpto y
  set z := Nat.sqrt y
  let D1 := (Ioc y N).filter Nat.Prime
  let D2 := (Icc (z + 1) y).image fun m => m ^ 2
  let D3 := (Icc 2 z).image fun m => m ^ (m.log y + 1)
  let D := D1 ∪ D2 ∪ D3
  let mult : ℕ → Finset ℕ := fun d => I_N.filter fun n => d ∣ n
  have hcover : I_N.filter (fun n => ¬ n ∣ Q) ⊆ D.biUnion mult := by
    intro n hn
    simp only [mem_filter] at hn
    obtain ⟨hnI, hnotdvd⟩ := hn
    have hn1 : 1 ≤ n := (mem_Icc.mp (mem_filter.mp hnI).1).1
    have hnN : n ≤ N := (mem_Icc.mp (mem_filter.mp hnI).1).2
    have hQ0 : Q ≠ 0 := Nat.lcmUpto_ne_zero y
    have hex : ∃ p : ℕ, p.Prime ∧ Q.factorization p < n.factorization p := by
      by_contra! hall
      exact hnotdvd ((Nat.factorization_prime_le_iff_dvd (by omega) hQ0).mp hall)
    obtain ⟨p, hp, hfac⟩ := hex
    rw [Nat.factorization_lcmUpto y hp] at hfac
    have hexp : p.log y + 1 ≤ n.factorization p := by omega
    have hdvd_pow : p ^ (p.log y + 1) ∣ n :=
      (Nat.pow_dvd_pow p hexp).trans (Nat.ordProj_dvd n p)
    by_cases hpy : y < p
    · have hpdvd : p ∣ n := (dvd_pow_self p (Nat.succ_ne_zero _)).trans hdvd_pow
      have hpN : p ≤ N := (Nat.le_of_dvd (by omega) hpdvd).trans hnN
      have hpD : p ∈ D :=
        mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpy, hpN⟩, hp⟩))
      exact mem_biUnion.mpr ⟨p, hpD, mem_filter.mpr ⟨hnI, hpdvd⟩⟩
    · have hpy' : p ≤ y := le_of_not_gt hpy
      by_cases hpz : z < p
      · have hlog1 : 1 ≤ p.log y := Nat.le_log_of_pow_le hp.one_lt (by simpa using hpy')
        have hp2dvd : p ^ 2 ∣ n :=
          (Nat.pow_dvd_pow p (show 2 ≤ p.log y + 1 by omega)).trans hdvd_pow
        have hp2D2 : p ^ 2 ∈ D2 := mem_image.mpr ⟨p, mem_Icc.mpr ⟨by omega, hpy'⟩, rfl⟩
        have hp2D : p ^ 2 ∈ D := mem_union_left _ (mem_union_right _ hp2D2)
        exact mem_biUnion.mpr ⟨p ^ 2, hp2D, mem_filter.mpr ⟨hnI, hp2dvd⟩⟩
      · have hpz' : p ≤ z := le_of_not_gt hpz
        have hp2 : 2 ≤ p := hp.two_le
        have hpD3 : p ^ (p.log y + 1) ∈ D3 :=
          mem_image.mpr ⟨p, mem_Icc.mpr ⟨hp2, hpz'⟩, rfl⟩
        have hpD : p ^ (p.log y + 1) ∈ D := mem_union_right _ hpD3
        exact mem_biUnion.mpr ⟨p ^ (p.log y + 1), hpD, mem_filter.mpr ⟨hnI, hdvd_pow⟩⟩
  let mass : ℕ → ℝ := fun d => ∑ n ∈ mult d, 1 / (n : ℝ)
  have hmass0 : ∀ d, 0 ≤ mass d := fun d => sum_nonneg fun _ _ => by positivity
  have hsub :
      (∑ n ∈ I_N.filter (fun n => ¬ n ∣ Q), 1 / (n : ℝ)) ≤ ∑ d ∈ D, mass d := by
    calc
      _ ≤ ∑ n ∈ D.biUnion mult, 1 / (n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => by positivity
      _ ≤ ∑ d ∈ D, mass d := sum_biUnion_le_sum D mult _ fun _ => by positivity
  have hunion123 : (∑ d ∈ D, mass d) ≤ (∑ d ∈ D1, mass d) + (∑ d ∈ D2, mass d) + ∑ d ∈ D3, mass d := by
    have h1 : (∑ d ∈ D1 ∪ D2 ∪ D3, mass d) ≤ (∑ d ∈ D1 ∪ D2, mass d) + ∑ d ∈ D3, mass d := by
      have h := sum_union_inter (s₁ := D1 ∪ D2) (s₂ := D3) (f := mass)
      have hi : 0 ≤ ∑ d ∈ (D1 ∪ D2) ∩ D3, mass d := sum_nonneg fun d _ => hmass0 d
      linarith
    have h2 : (∑ d ∈ D1 ∪ D2, mass d) ≤ (∑ d ∈ D1, mass d) + ∑ d ∈ D2, mass d := by
      have h := sum_union_inter (s₁ := D1) (s₂ := D2) (f := mass)
      have hi : 0 ≤ ∑ d ∈ D1 ∩ D2, mass d := sum_nonneg fun d _ => hmass0 d
      linarith
    dsimp [D]
    linarith
  have hN1 : 1 ≤ N := by omega
  have hD1_le : (∑ d ∈ D1, mass d) ≤ 1 / 4 := by
    have hstep : ∀ p ∈ D1, mass p ≤ 16 / (p : ℝ) := by
      intro p hp
      exact divisor_mass_le hN1 (mem_filter.mp hp).2.one_le
    exact (sum_le_sum hstep).trans ((large_primes_sum_le (by omega) ).trans hKlog)
  have hD2_le : (∑ d ∈ D2, mass d) ≤ 1 / 8 := by
    calc
      (∑ d ∈ D2, mass d) ≤ ∑ m ∈ Icc (z + 1) y, mass (m ^ 2) :=
        sum_image_le_sum _ _ mass hmass0
      _ ≤ ∑ m ∈ Icc (z + 1) y, 16 / ((m ^ 2 : ℕ) : ℝ) := by
        refine sum_le_sum fun m hm => divisor_mass_le hN1 ?_
        have : 1 ≤ m := by
          have := (mem_Icc.mp hm).1
          omega
        exact Nat.one_le_pow 2 m this
      _ ≤ 1 / 8 := large_squares_sum_le hy
  have hD3_le : (∑ d ∈ D3, mass d) ≤ 1 / 8 := by
    calc
      (∑ d ∈ D3, mass d) ≤ ∑ m ∈ Icc 2 z, mass (m ^ (m.log y + 1)) :=
        sum_image_le_sum _ _ mass hmass0
      _ ≤ ∑ m ∈ Icc 2 z, 16 / ((m ^ (m.log y + 1) : ℕ) : ℝ) := by
        refine sum_le_sum fun m hm => divisor_mass_le hN1 ?_
        have : 1 ≤ m := by
          have := (mem_Icc.mp hm).1
          omega
        exact Nat.one_le_pow _ m this
      _ ≤ 1 / 8 := small_powers_sum_le hy
  linarith

private lemma asymptotic_params (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      256 ≤ N ∧
        let y := ⌊c * (N : ℝ) / ((Real.log N) ^ 3 * (Real.log (Real.log N)) ^ 4)⌋₊
        16384 ≤ y ∧
          64 * ((Nat.log 2 (N / y) + 1 : ℕ) : ℝ) / Real.log (y : ℝ) ≤ 1 / 4 := by
  let B : ℝ := max (4 * 20000 ^ 2) ((4 ^ 8 * 24 ^ 2 : ℝ) * (2 / c) + 20000 * |Real.log (2 / c)|)
  let N0 : ℕ := ⌈Real.exp B⌉₊ + 256
  filter_upwards [eventually_ge_atTop N0] with N hN
  have hN256 : 256 ≤ N := by omega
  refine ⟨hN256, ?_⟩
  dsimp only
  set L := Real.log (N : ℝ)
  set D := L ^ 3 * (Real.log L) ^ 4
  set X := c * (N : ℝ) / D
  set y := ⌊X⌋₊
  have hB_ge1 : (1600000000 : ℝ) ≤ B := by
    have : (4 * 20000 ^ 2 : ℝ) ≤ B := le_max_left _ _
    linarith
  have hB_ge2 : (4 ^ 8 * 24 ^ 2 : ℝ) * (2 / c) + 20000 * |Real.log (2 / c)| ≤ B :=
    le_max_right _ _
  have hexpB_le : Real.exp B ≤ (N : ℝ) := by
    have h1 : Real.exp B ≤ (⌈Real.exp B⌉₊ : ℝ) := Nat.le_ceil (Real.exp B)
    have h2 : (⌈Real.exp B⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show ⌈Real.exp B⌉₊ ≤ N by omega)
    exact h1.trans h2
  have hBL : B ≤ L := by
    have h := Real.log_le_log (Real.exp_pos B) hexpB_le
    rwa [Real.log_exp] at h
  have hL_big : (1600000000 : ℝ) ≤ L := hB_ge1.trans hBL
  have hlogL_pos : 0 < Real.log L := Real.log_pos (by linarith)
  have hlogL_sq : (Real.log L) ^ 2 ≤ 4 * L := log_sq_le_four_mul (by linarith)
  have hlogL_small : 20000 * Real.log L ≤ L := by
    have hsq : (20000 * Real.log L) ^ 2 ≤ L ^ 2 := by nlinarith
    nlinarith
  have hlogL_le : Real.log L ≤ L := by linarith
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have hD_le_L7 : D ≤ L ^ 7 := by
    have hp4 : (Real.log L) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hlogL_pos.le hlogL_le 4
    have hL3 : 0 ≤ L ^ 3 := by positivity
    calc
      D = L ^ 3 * (Real.log L) ^ 4 := rfl
      _ ≤ L ^ 3 * L ^ 4 := mul_le_mul_of_nonneg_left hp4 hL3
      _ = L ^ 7 := by ring
  have hL8 : L ^ 8 ≤ (4 ^ 8 * 24 ^ 2 : ℝ) * Real.exp (L / 2) := by
    have hpow := Real.pow_div_factorial_le_exp (L / 4) (by linarith) 4
    have hfac : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hfac] at hpow
    have hsq : ((L / 4) ^ 4 / 24) ^ 2 ≤ (Real.exp (L / 4)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hpow 2
    have hexp2 : (Real.exp (L / 4)) ^ 2 = Real.exp (L / 2) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [hexp2] at hsq
    nlinarith
  have hconst_L : (4 ^ 8 * 24 ^ 2 : ℝ) ≤ (c / 2) * L := by
    have h1 : (4 ^ 8 * 24 ^ 2 : ℝ) * (2 / c) ≤ L := by
      have ha : 0 ≤ |Real.log (2 / c)| := abs_nonneg _
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ c / 2 by positivity)
    have h3 : (4 ^ 8 * 24 ^ 2 : ℝ) * (2 / c) * (c / 2) = (4 ^ 8 * 24 ^ 2 : ℝ) := by
      field_simp [hc.ne']
    linarith
  have hL7_exp : L ^ 7 ≤ (c / 2) * Real.exp (L / 2) := by
    have h1 : L ^ 8 ≤ (c / 2) * L * Real.exp (L / 2) := by
      calc
        L ^ 8 ≤ (4 ^ 8 * 24 ^ 2 : ℝ) * Real.exp (L / 2) := hL8
        _ ≤ ((c / 2) * L) * Real.exp (L / 2) :=
          mul_le_mul_of_nonneg_right hconst_L (Real.exp_pos _).le
    have hposexp : 0 < Real.exp (L / 2) := Real.exp_pos (L / 2)
    nlinarith
  have hN_exp : (N : ℝ) = Real.exp (L / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add, add_halves, Real.exp_log (by exact_mod_cast (show 0 < N by omega))]
  have hX_ge_exp : 2 * Real.exp (L / 2) ≤ X := by
    dsimp [X]
    rw [le_div_iff₀ hD_pos, hN_exp]
    have hDL : D ≤ (c / 2) * Real.exp (L / 2) := hD_le_L7.trans hL7_exp
    have hmul := mul_le_mul_of_nonneg_right hDL (show 0 ≤ 2 * Real.exp (L / 2) by positivity)
    linarith
  have hexp_large : 50000 ≤ Real.exp (L / 2) := by
    have h := Real.add_one_le_exp (L / 2)
    linarith
  have hy_ge_exp : Real.exp (L / 2) ≤ (y : ℝ) := by
    have hfl : X - 1 < (y : ℝ) := by
      have := Nat.lt_floor_add_one X
      linarith
    linarith
  have hy16384 : 16384 ≤ y := by
    have : (16384 : ℝ) ≤ (y : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨hy16384, ?_⟩
  have hlogy_ge : L / 2 ≤ Real.log (y : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (L / 2)) hy_ge_exp
    rwa [Real.log_exp] at h
  have hX_half_le_y : X / 2 ≤ (y : ℝ) := by
    have hfl : X - 1 < (y : ℝ) := by
      have := Nat.lt_floor_add_one X
      linarith
    linarith
  have hy_ge_frac : (c / 2) * (N : ℝ) / L ^ 7 ≤ (y : ℝ) := by
    have hXL7 : c * (N : ℝ) / L ^ 7 ≤ X := by
      dsimp [X]
      exact div_le_div_of_nonneg_left (by positivity) hD_pos hD_le_L7
    have heq : (c / 2) * (N : ℝ) / L ^ 7 = (c * (N : ℝ) / L ^ 7) / 2 := by ring
    linarith
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hNy_le : ((N / y : ℕ) : ℝ) ≤ (2 / c) * L ^ 7 := by
    have h1 : ((N / y : ℕ) : ℝ) * (y : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.div_mul_le_self N y
    have h2 : ((N / y : ℕ) : ℝ) ≤ (N : ℝ) / (y : ℝ) := (le_div_iff₀ hypos).mpr h1
    have h3 : (N : ℝ) / (y : ℝ) ≤ (2 / c) * L ^ 7 := by
      rw [div_le_iff₀ hypos]
      have h4 : (c / 2) * (N : ℝ) ≤ (y : ℝ) * L ^ 7 :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < L ^ 7)).mp hy_ge_frac
      have h5 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ 2 / c by positivity)
      have h6 : (2 / c) * ((c / 2) * (N : ℝ)) = (N : ℝ) := by
        field_simp [hc.ne']
      have h7 : (2 / c) * ((y : ℝ) * L ^ 7) = (2 / c) * L ^ 7 * (y : ℝ) := by ring
      linarith
    exact h2.trans h3
  have habs_logc : 20000 * |Real.log (2 / c)| ≤ L := by
    have hpos_t : 0 ≤ (4 ^ 8 * 24 ^ 2 : ℝ) * (2 / c) := by positivity
    linarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := half_lt_log_two
  have hK_le : ((Nat.log 2 (N / y) + 1 : ℕ) : ℝ) ≤ L / 512 := by
    by_cases hq0 : N / y = 0
    · simp [hq0]
      linarith
    · set k := Nat.log 2 (N / y)
      have hpow_nat : 2 ^ k ≤ N / y := Nat.pow_log_le_self 2 hq0
      have hpow_real : (2 : ℝ) ^ k ≤ (2 / c) * L ^ 7 := by
        have h1 : (2 : ℝ) ^ k ≤ ((N / y : ℕ) : ℝ) := by exact_mod_cast hpow_nat
        exact h1.trans hNy_le
      have hlog_pow : (k : ℝ) * Real.log 2 ≤ Real.log (2 / c) + 7 * Real.log L := by
        have h := Real.log_le_log (by positivity) hpow_real
        rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
        linarith
      have hk_half : (k : ℝ) * (1 / 2) ≤ |Real.log (2 / c)| + 7 * Real.log L := by
        have hk0 : (0 : ℝ) ≤ k := by positivity
        have hle1 : (k : ℝ) * (1 / 2) ≤ (k : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hlog2.le hk0
        have hle2 : Real.log (2 / c) ≤ |Real.log (2 / c)| := le_abs_self _
        linarith
      have hcast_k : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast_k]
      linarith
  have hlogy_pos : 0 < Real.log (y : ℝ) := by linarith
  rw [div_le_iff₀ hlogy_pos]
  linarith

end Erdos294StepH1

theorem OMA.erdos294NearFrequencies : OMA.R_Erdos294_erdos_294_R1_H1_R1_H2_R1.H1 := by
  intro c hc
  filter_upwards [Erdos294StepH1.asymptotic_params c hc] with N hN
  obtain ⟨hN256, hy16384, hKlog⟩ := hN
  dsimp only
  set y := ⌊c * (N : ℝ) / ((Real.log N) ^ 3 * (Real.log (Real.log N)) ^ 4)⌋₊
  set Q := Nat.lcmUpto y
  set I_N := (Icc 1 N).filter fun n => N ≤ 16 * n
  set A' := I_N.filter fun n => n ∣ Q
  have hA_eq :
      ((Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q) = A' := by
    ext n
    simp only [A', I_N, mem_filter]
    tauto
  rw [hA_eq]
  have hharm := Erdos294StepH1.harmonic_bounds hN256
  have hbad := Erdos294StepH1.bad_reciprocal_sum_le hN256 hy16384 hKlog
  have hsplit :=
    sum_filter_add_sum_filter_not I_N (fun n => n ∣ Q) (fun n : ℕ => 1 / (n : ℝ))
  have hbad_nonneg :
      0 ≤ ∑ n ∈ I_N.filter (fun n => ¬ n ∣ Q), 1 / (n : ℝ) :=
    sum_nonneg fun _ _ => by positivity
  have hgood_lo : (3 / 2 : ℝ) ≤ ∑ n ∈ A', 1 / (n : ℝ) := by linarith
  have hgood_hi : (∑ n ∈ A', 1 / (n : ℝ)) ≤ 3 := by linarith
  have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast Nat.lcmUpto_pos y
  have hsum_eq : ((∑ n ∈ A', Q / n : ℕ) : ℝ) = (Q : ℝ) * ∑ n ∈ A', 1 / (n : ℝ) := by
    rw [Nat.cast_sum, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hn).1).1).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hdvd : n ∣ Q := (mem_filter.mp hn).2
    have hmul : ((Q / n : ℕ) : ℝ) * (n : ℝ) = (Q : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    field_simp [hnpos.ne']
    linarith
  constructor
  · have hreal : ((3 * Q : ℕ) : ℝ) ≤ ((2 * ∑ n ∈ A', Q / n : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [hsum_eq]
      nlinarith
    exact_mod_cast hreal
  · have hreal : ((∑ n ∈ A', Q / n : ℕ) : ℝ) ≤ ((3 * Q : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [hsum_eq]
      nlinarith
    exact_mod_cast hreal

end

section

/-!
# Proof of `Erdos294.erdos_294.R1.H1.R1.H2.R1.H2`

Proves the far-frequency exponential-sum bound for smooth divisors in `[N/16, N]`
following the minor-arc divisibility method of Liu and Sawhney (arXiv:2404.07113,
Proposition 3.2 and Lemma 4.1). Restricting the nonnegative phase sum to smooth
integers with at most 5 distinct prime factors removes all `log log N` losses from
prime-factor multiplicity, allowing `c = 1` with purely elementary Chebyshev bounds.

Credits for upstream reductions and sibling proofs of `Erdos294.erdos_294`:
- `@steveDOTdigital` (PRs #5730, #6217, #6261, #6598, #6840)
- `@mattdorman` (PR #8765)
- `@vkascheev` (PR #833)
-/

open Finset Filter Real

namespace Erdos294StepH2

/- ## Section 1: Elementary Chebyshev prime-counting bounds -/

section PrimeCounting

private lemma log_le_four_sqrt_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have h1 : Real.log x / 4 + 1 ≤ Real.exp (Real.log x / 4) := Real.add_one_le_exp _
  have h2 : Real.exp (Real.log x / 4) = Real.sqrt (Real.sqrt x) := by
    have hs1 : Real.exp (Real.log x / 2) = Real.sqrt x := by
      rw [← Real.sqrt_sq (Real.exp_pos _).le, sq, ← Real.exp_add, add_halves, Real.exp_log hx]
    rw [← hs1, ← Real.sqrt_sq (Real.exp_pos _).le, sq, ← Real.exp_add]
    congr 2; ring
  linarith

private lemma sqrt_sqrt_le_mul_of_le {a x : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (Real.sqrt (a * x)) = Real.sqrt (Real.sqrt a) * Real.sqrt (Real.sqrt x) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul (Real.sqrt_nonneg a)]

private lemma theta_sub_eq_sum_Ioc {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log b, Chebyshev.theta_eq_sum_primesLE_log a]
  have hsub : Nat.primesLE a ⊆ Nat.primesLE b := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans hab, hp.2⟩
  have hsdiff : Nat.primesLE b \ Nat.primesLE a = (Ioc a b).filter Nat.Prime := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hpb, hp⟩, hna⟩
      refine ⟨⟨?_, hpb⟩, hp⟩
      by_contra hle
      exact hna ⟨le_of_not_gt hle, hp⟩
    · rintro ⟨⟨hap, hpb⟩, hp⟩
      exact ⟨⟨hpb, hp⟩, fun ⟨hpa, _⟩ => by omega⟩
  rw [← hsdiff, Finset.sum_sdiff_eq_sub hsub]

private lemma theta_ge_half {n : ℕ} (hn : 10 ^ 10 ≤ n) :
    (n : ℝ) / 2 ≤ Chebyshev.theta (n : ℝ) := by
  have hge := Chebyshev.theta_ge n
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn_big : (10 ^ 10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hq : (100 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := by
    have h1 : (10000 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.le_sqrt (by norm_num) hn_pos.le]
      nlinarith
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]
    nlinarith
  have hsqn : Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 = Real.sqrt (n : ℝ) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hsq2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
  have hlogn : Real.log (n : ℝ) ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) :=
    log_le_four_sqrt_sqrt hn_pos
  have hlogn1 : Real.log ((n : ℝ) + 1) ≤ 4 * Real.sqrt (Real.sqrt (2 * (n : ℝ))) := by
    have hle : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    exact (Real.log_le_log (by positivity) hle).trans (log_le_four_sqrt_sqrt (by positivity))
  have hss2 : Real.sqrt (Real.sqrt (2 : ℝ)) ≤ 2 := by
    have h1 : Real.sqrt (2 : ℝ) ≤ 4 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hlogn1_le : Real.log ((n : ℝ) + 1) ≤ 8 * Real.sqrt (Real.sqrt (n : ℝ)) := by
    rw [sqrt_sqrt_le_mul_of_le (by norm_num)] at hlogn1
    nlinarith [Real.sqrt_nonneg (Real.sqrt (n : ℝ))]
  set s := Real.sqrt (Real.sqrt (n : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq_eq : Real.sqrt (n : ℝ) = s ^ 2 := hsqn.symm
  have hn_eq : (n : ℝ) = s ^ 4 := by
    calc (n : ℝ) = Real.sqrt (n : ℝ) ^ 2 := hsq2.symm
      _ = (s ^ 2) ^ 2 := by rw [hsq_eq]
      _ = s ^ 4 := by ring
  have hterm1 : 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ 8 * s ^ 3 := by
    rw [hsq_eq]
    nlinarith [sq_nonneg s]
  have hterm2 : 8 * s ^ 3 + 8 * s ≤ 0.1 * s ^ 4 := by
    have hs3 : 100 * s ^ 3 ≤ s ^ 4 := by nlinarith [pow_nonneg hs0 3]
    have hs1 : s ≤ s ^ 3 := by nlinarith [sq_nonneg s]
    nlinarith
  have hlog_tot : Real.log ((n : ℝ) + 1) + 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ 0.1 * (n : ℝ) := by
    calc Real.log ((n : ℝ) + 1) + 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)
        ≤ 8 * s + 8 * s ^ 3 := add_le_add hlogn1_le hterm1
      _ ≤ 0.1 * s ^ 4 := by linarith
      _ = 0.1 * (n : ℝ) := by rw [hn_eq]
  nlinarith

private lemma theta_three_sub_ge {X : ℕ} (hX : 10 ^ 10 ≤ X) :
    (X : ℝ) / 2 ≤ Chebyshev.theta ((3 * X : ℕ) : ℝ) - Chebyshev.theta (X : ℝ) := by
  have hge := Chebyshev.theta_ge (3 * X)
  have hle := Chebyshev.theta_le_log4_mul_x (x := (X : ℝ)) (by positivity)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hX_pos : (0 : ℝ) < X := by positivity
  have hX_big : (10 ^ 10 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  set s := Real.sqrt (Real.sqrt ((3 * X : ℕ) : ℝ))
  have h3X_pos : (0 : ℝ) < ((3 * X : ℕ) : ℝ) := by positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h3X_big : (3 * 10 ^ 10 : ℝ) ≤ ((3 * X : ℕ) : ℝ) := by
    push_cast; linarith
  have hs_ge : (130 : ℝ) ≤ s := by
    have h1 : (16900 : ℝ) ≤ Real.sqrt ((3 * X : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) h3X_pos.le]; nlinarith
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]; nlinarith
  have hsq : Real.sqrt ((3 * X : ℕ) : ℝ) = s ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
  have h3X_eq : ((3 * X : ℕ) : ℝ) = s ^ 4 := by
    calc ((3 * X : ℕ) : ℝ) = Real.sqrt ((3 * X : ℕ) : ℝ) ^ 2 := (Real.sq_sqrt h3X_pos.le).symm
      _ = (s ^ 2) ^ 2 := by rw [hsq]
      _ = s ^ 4 := by ring
  have hlog3X : Real.log ((3 * X : ℕ) : ℝ) ≤ 4 * s := log_le_four_sqrt_sqrt h3X_pos
  have hlog3X1 : Real.log (((3 * X : ℕ) : ℝ) + 1) ≤ 8 * s := by
    have h1 : Real.log (((3 * X : ℕ) : ℝ) + 1) ≤ Real.log (2 * ((3 * X : ℕ) : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (2 * ((3 * X : ℕ) : ℝ)) ≤ 4 * Real.sqrt (Real.sqrt (2 * ((3 * X : ℕ) : ℝ))) :=
      log_le_four_sqrt_sqrt (by positivity)
    rw [sqrt_sqrt_le_mul_of_le (by norm_num)] at h2
    have hss2 : Real.sqrt (Real.sqrt (2 : ℝ)) ≤ 2 := by
      have ha : Real.sqrt (2 : ℝ) ≤ 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      rw [Real.sqrt_le_left (by norm_num)]; linarith
    nlinarith
  have hterm : 2 * Real.sqrt ((3 * X : ℕ) : ℝ) * Real.log ((3 * X : ℕ) : ℝ) ≤ 8 * s ^ 3 := by
    rw [hsq]; nlinarith [sq_nonneg s]
  have hrem : 8 * s ^ 3 + 8 * s ≤ 0.063 * s ^ 4 := by
    have hs3 : 130 * s ^ 3 ≤ s ^ 4 := by nlinarith [pow_nonneg hs0 3]
    have hs1 : 100 * s ≤ s ^ 3 := by nlinarith [sq_nonneg s]
    nlinarith
  have hcast : ((3 * X : ℕ) : ℝ) = 3 * (X : ℝ) := by push_cast; ring
  have herr : Real.log (((3 * X : ℕ) : ℝ) + 1) +
      2 * Real.sqrt ((3 * X : ℕ) : ℝ) * Real.log ((3 * X : ℕ) : ℝ) ≤ 0.189 * (X : ℝ) := by
    linarith [h3X_eq, hcast]
  rw [hlog4] at hle
  rw [hcast] at hge herr
  rw [hcast]
  nlinarith

private lemma five_primes_in_Ioc_three {X : ℕ} (hX : 10 ^ 10 ≤ X) :
    5 ≤ ((Ioc X (3 * X)).filter Nat.Prime).card := by
  have hth := theta_three_sub_ge hX
  rw [theta_sub_eq_sum_Ioc (by omega : X ≤ 3 * X)] at hth
  have hX_pos : (0 : ℝ) < X := by positivity
  have h3X_pos : (0 : ℝ) < ((3 * X : ℕ) : ℝ) := by positivity
  have hsum_le : ∑ p ∈ (Ioc X (3 * X)).filter Nat.Prime, Real.log (p : ℝ) ≤
      (((Ioc X (3 * X)).filter Nat.Prime).card : ℝ) * Real.log ((3 * X : ℕ) : ℝ) := by
    calc ∑ p ∈ (Ioc X (3 * X)).filter Nat.Prime, Real.log (p : ℝ)
        ≤ ∑ _p ∈ (Ioc X (3 * X)).filter Nat.Prime, Real.log ((3 * X : ℕ) : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          have hp' := mem_filter.mp hp
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
          exact Real.log_le_log hp_pos (by exact_mod_cast (mem_Ioc.mp hp'.1).2)
      _ = (((Ioc X (3 * X)).filter Nat.Prime).card : ℝ) * Real.log ((3 * X : ℕ) : ℝ) := by simp
  have hlog_le : Real.log ((3 * X : ℕ) : ℝ) ≤ 4 * Real.sqrt (Real.sqrt ((3 * X : ℕ) : ℝ)) :=
    log_le_four_sqrt_sqrt h3X_pos
  have hlog_pos : 0 < Real.log ((3 * X : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * X by omega))
  set s := Real.sqrt (Real.sqrt ((3 * X : ℕ) : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h3X_big : (3 * 10 ^ 10 : ℝ) ≤ ((3 * X : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : 3 * 10 ^ 10 ≤ 3 * X)
  have hs_ge : (130 : ℝ) ≤ s := by
    have h1 : (16900 : ℝ) ≤ Real.sqrt ((3 * X : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) h3X_pos.le]; nlinarith
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]; nlinarith
  have h3X_eq : ((3 * X : ℕ) : ℝ) = s ^ 4 := by
    have hsq : Real.sqrt ((3 * X : ℕ) : ℝ) = s ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
    calc ((3 * X : ℕ) : ℝ) = Real.sqrt ((3 * X : ℕ) : ℝ) ^ 2 := (Real.sq_sqrt h3X_pos.le).symm
      _ = (s ^ 2) ^ 2 := by rw [hsq]
      _ = s ^ 4 := by ring
  have hcast : ((3 * X : ℕ) : ℝ) = 3 * (X : ℝ) := by push_cast; ring
  have h5log : 5 * Real.log ((3 * X : ℕ) : ℝ) ≤ (X : ℝ) / 2 := by
    have hs3 : 130 ^ 3 * s ≤ s ^ 4 := by
      have ha : 130 ^ 2 ≤ s ^ 2 := by nlinarith
      have hb : 130 ^ 3 ≤ s ^ 3 := by nlinarith
      nlinarith
    linarith [h3X_eq, hcast]
  have hcard_real : (5 : ℝ) ≤ (((Ioc X (3 * X)).filter Nat.Prime).card : ℝ) := by
    nlinarith
  exact_mod_cast hcard_real

private lemma theta_four_sub_ge {P : ℕ} (hP : 10 ^ 10 ≤ P) :
    (P : ℝ) ≤ Chebyshev.theta ((4 * P : ℕ) : ℝ) - Chebyshev.theta (P : ℝ) := by
  have hge := Chebyshev.theta_ge (4 * P)
  have hle := Chebyshev.theta_le_log4_mul_x (x := (P : ℝ)) (by positivity)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have h4P_pos : (0 : ℝ) < ((4 * P : ℕ) : ℝ) := by positivity
  set s := Real.sqrt (Real.sqrt ((4 * P : ℕ) : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h4P_big : (4 * 10 ^ 10 : ℝ) ≤ ((4 * P : ℕ) : ℝ) := by
    push_cast; exact_mod_cast (by omega : 4 * 10 ^ 10 ≤ 4 * P)
  have hs_ge : (140 : ℝ) ≤ s := by
    have h1 : (19600 : ℝ) ≤ Real.sqrt ((4 * P : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) h4P_pos.le]; nlinarith
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]; nlinarith
  have hsq : Real.sqrt ((4 * P : ℕ) : ℝ) = s ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
  have h4P_eq : ((4 * P : ℕ) : ℝ) = s ^ 4 := by
    calc ((4 * P : ℕ) : ℝ) = Real.sqrt ((4 * P : ℕ) : ℝ) ^ 2 := (Real.sq_sqrt h4P_pos.le).symm
      _ = (s ^ 2) ^ 2 := by rw [hsq]
      _ = s ^ 4 := by ring
  have hlog4P : Real.log ((4 * P : ℕ) : ℝ) ≤ 4 * s := log_le_four_sqrt_sqrt h4P_pos
  have hlog4P1 : Real.log (((4 * P : ℕ) : ℝ) + 1) ≤ 8 * s := by
    have h1 : Real.log (((4 * P : ℕ) : ℝ) + 1) ≤ Real.log (2 * ((4 * P : ℕ) : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (2 * ((4 * P : ℕ) : ℝ)) ≤ 4 * Real.sqrt (Real.sqrt (2 * ((4 * P : ℕ) : ℝ))) :=
      log_le_four_sqrt_sqrt (by positivity)
    rw [sqrt_sqrt_le_mul_of_le (by norm_num)] at h2
    have hss2 : Real.sqrt (Real.sqrt (2 : ℝ)) ≤ 2 := by
      have ha : Real.sqrt (2 : ℝ) ≤ 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      rw [Real.sqrt_le_left (by norm_num)]; linarith
    nlinarith
  have hterm : 2 * Real.sqrt ((4 * P : ℕ) : ℝ) * Real.log ((4 * P : ℕ) : ℝ) ≤ 8 * s ^ 3 := by
    rw [hsq]; nlinarith [sq_nonneg s]
  have hrem : 8 * s ^ 3 + 8 * s ≤ 0.06 * s ^ 4 := by
    have hs3 : 140 * s ^ 3 ≤ s ^ 4 := by nlinarith [pow_nonneg hs0 3]
    have hs1 : 100 * s ≤ s ^ 3 := by nlinarith [sq_nonneg s]
    nlinarith
  have hcast : ((4 * P : ℕ) : ℝ) = 4 * (P : ℝ) := by push_cast; ring
  have herr : Real.log (((4 * P : ℕ) : ℝ) + 1) +
      2 * Real.sqrt ((4 * P : ℕ) : ℝ) * Real.log ((4 * P : ℕ) : ℝ) ≤ 0.24 * (P : ℝ) := by
    linarith [h4P_eq, hcast]
  rw [hlog4] at hle
  rw [hcast] at hge herr
  rw [hcast]
  nlinarith

private lemma card_primesLE_ge {U : ℕ} (hU : 10 ^ 10 ≤ U) :
    (U : ℝ) / (2 * Real.log (U : ℝ)) ≤ ((Nat.primesLE U).card : ℝ) := by
  have hth := theta_ge_half hU
  rw [Chebyshev.theta_eq_sum_primesLE_log U] at hth
  have hU_pos : (0 : ℝ) < U := by positivity
  have hlogU_pos : 0 < Real.log (U : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hsum_le : ∑ p ∈ Nat.primesLE U, Real.log (p : ℝ) ≤
      ((Nat.primesLE U).card : ℝ) * Real.log (U : ℝ) := by
    calc ∑ p ∈ Nat.primesLE U, Real.log (p : ℝ)
        ≤ ∑ _p ∈ Nat.primesLE U, Real.log (U : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          have hp' := Nat.mem_primesLE.mp hp
          exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast hp'.1)
      _ = ((Nat.primesLE U).card : ℝ) * Real.log (U : ℝ) := by simp
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log (U : ℝ))]
  linarith

private lemma eight_log_four_le_quarter {P : ℕ} (hP : 10 ^ 10 ≤ P) :
    8 * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 4 := by
  have h4P_pos : (0 : ℝ) < ((4 * P : ℕ) : ℝ) := by positivity
  have hlog := log_le_four_sqrt_sqrt h4P_pos
  set s := Real.sqrt (Real.sqrt ((4 * P : ℕ) : ℝ))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h4P_big : (4 * 10 ^ 10 : ℝ) ≤ ((4 * P : ℕ) : ℝ) := by
    push_cast; exact_mod_cast (by omega : 4 * 10 ^ 10 ≤ 4 * P)
  have hs_ge : (140 : ℝ) ≤ s := by
    have h1 : (19600 : ℝ) ≤ Real.sqrt ((4 * P : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) h4P_pos.le]; nlinarith
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)]; nlinarith
  have h4P_eq : ((4 * P : ℕ) : ℝ) = s ^ 4 := by
    have hsq : Real.sqrt ((4 * P : ℕ) : ℝ) = s ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg _)).symm
    calc ((4 * P : ℕ) : ℝ) = Real.sqrt ((4 * P : ℕ) : ℝ) ^ 2 := (Real.sq_sqrt h4P_pos.le).symm
      _ = (s ^ 2) ^ 2 := by rw [hsq]
      _ = s ^ 4 := by ring
  have hcast : ((4 * P : ℕ) : ℝ) = 4 * (P : ℝ) := by push_cast; ring
  have hs3 : 140 ^ 3 * s ≤ s ^ 4 := by
    have ha : 140 ^ 2 ≤ s ^ 2 := by nlinarith
    have hb : 140 ^ 3 ≤ s ^ 3 := by nlinarith
    nlinarith
  linarith [h4P_eq, hcast]

end PrimeCounting

/- ## Section 2: Arithmetic helpers and minor-arc divisibility core -/

section MinorArcCore

private def qOf (S p : ℕ) : ℕ := p ^ (p.log S)

private lemma qOf_pos {S p : ℕ} (hp : p.Prime) : 0 < qOf S p :=
  Nat.pow_pos hp.pos

private lemma qOf_le_S {S p : ℕ} (hS : S ≠ 0) : qOf S p ≤ S :=
  Nat.pow_log_le_self p hS

private lemma prime_dvd_qOf {S p : ℕ} (hp : p ∈ Nat.primesLE S) : p ∣ qOf S p := by
  have ⟨hpS, hpr⟩ := Nat.mem_primesLE.mp hp
  have hlog : 1 ≤ p.log S := Nat.le_log_of_pow_le hpr.one_lt (by simpa using hpS)
  exact dvd_pow_self p (by omega)

private lemma qOf_dvd_lcmUpto {S p : ℕ} (hp : p ∈ Nat.primesLE S) :
    qOf S p ∣ Nat.lcmUpto S := by
  rw [Nat.lcmUpto_eq_prod_pow_log S]
  exact Finset.dvd_prod_of_mem (fun q => q ^ q.log S) hp

private lemma primeFactors_qOf_subset {S p : ℕ} (hp : p.Prime) :
    (qOf S p).primeFactors ⊆ {p} := by
  intro r hr
  have ⟨hrp, hrdvd, _⟩ := Nat.mem_primeFactors.mp hr
  have hrp' : r ∣ p := hrp.dvd_of_dvd_pow hrdvd
  exact mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hrp hp).mp hrp')

private lemma coprime_qOf_of_ne {S p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) :
    Nat.Coprime (qOf S p₁) (qOf S p₂) :=
  ((Nat.coprime_primes hp₁ hp₂).mpr hne).pow _ _

private lemma coprime_qOf_prime_of_ne {S p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) :
    Nat.Coprime (qOf S p) r :=
  ((Nat.coprime_primes hp hr).mpr hne).pow_left _

private lemma prime_dvd_lcmUpto {S r : ℕ} (hr : r.Prime) (hrS : r ≤ S) :
    r ∣ Nat.lcmUpto S :=
  (prime_dvd_qOf (Nat.mem_primesLE.mpr ⟨hrS, hr⟩)).trans
    (qOf_dvd_lcmUpto (Nat.mem_primesLE.mpr ⟨hrS, hr⟩))

private lemma prod_dvd_of_natCoprime {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ} {m : ℕ}
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime (f a) (f b))
    (hdvd : ∀ a ∈ s, f a ∣ m) :
    (∏ a ∈ s, f a) ∣ m := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcop_a : Nat.Coprime (f a) (∏ b ∈ s, f b) :=
      Nat.Coprime.prod_right fun b hb =>
        hcop a (mem_insert_self a s) b (mem_insert_of_mem hb) (fun h => ha (h ▸ hb))
    have hdvd_s : (∏ b ∈ s, f b) ∣ m :=
      ih (fun x hx y hy hxy => hcop x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy)
        (fun x hx => hdvd x (mem_insert_of_mem hx))
    exact hcop_a.mul_dvd_of_dvd_of_dvd (hdvd a (mem_insert_self a s)) hdvd_s

private lemma four_mul_prod_qOf_dvd {S : ℕ} {D : Finset ℕ} (hDsub : D ⊆ Nat.primesLE S)
    (hDne : D.Nonempty) {x : ℤ}
    (hx : ∀ p ∈ D, ((4 * qOf S p : ℕ) : ℤ) ∣ x) :
    ((4 * ∏ p ∈ D, qOf S p : ℕ) : ℤ) ∣ x := by
  have hnat : 4 * ∏ p ∈ D, qOf S p ∣ x.natAbs := by
    have hx' : ∀ p ∈ D, 4 * qOf S p ∣ x.natAbs := fun p hp => Int.natCast_dvd.mp (hx p hp)
    by_cases h2 : 2 ∈ D
    · have hprod : ∏ p ∈ D, qOf S p = qOf S 2 * ∏ p ∈ D.erase 2, qOf S p :=
        (Finset.mul_prod_erase D (qOf S) h2).symm
      rw [hprod, ← mul_assoc]
      have hcop : Nat.Coprime (4 * qOf S 2) (∏ p ∈ D.erase 2, qOf S p) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have ⟨hne, hpD⟩ := mem_erase.mp hp
        have hpr := Nat.prime_of_mem_primesLE (hDsub hpD)
        have hcop2 : Nat.Coprime 2 (qOf S p) :=
          ((Nat.coprime_primes Nat.prime_two hpr).mpr hne.symm).pow_right _
        have hcop4 : Nat.Coprime 4 (qOf S p) := by
          simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hcop2.pow_left 2
        exact hcop4.mul_left (coprime_qOf_of_ne Nat.prime_two hpr hne.symm)
      have hdvd1 : 4 * qOf S 2 ∣ x.natAbs := hx' 2 h2
      have hdvd2 : ∏ p ∈ D.erase 2, qOf S p ∣ x.natAbs := by
        refine prod_dvd_of_natCoprime ?_ fun p hp =>
          (dvd_mul_left (qOf S p) 4).trans (hx' p (mem_of_mem_erase hp))
        intro a ha b hb hab
        exact coprime_qOf_of_ne (Nat.prime_of_mem_primesLE (hDsub (mem_of_mem_erase ha)))
          (Nat.prime_of_mem_primesLE (hDsub (mem_of_mem_erase hb))) hab
      exact hcop.mul_dvd_of_dvd_of_dvd hdvd1 hdvd2
    · obtain ⟨p₀, hp₀⟩ := hDne
      have hdvd4 : 4 ∣ x.natAbs := (dvd_mul_right 4 (qOf S p₀)).trans (hx' p₀ hp₀)
      have hcop : Nat.Coprime 4 (∏ p ∈ D, qOf S p) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hpr := Nat.prime_of_mem_primesLE (hDsub hp)
        have hne : 2 ≠ p := fun h => h2 (h ▸ hp)
        have hcop2 : Nat.Coprime 2 (qOf S p) :=
          ((Nat.coprime_primes Nat.prime_two hpr).mpr hne).pow_right _
        simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hcop2.pow_left 2
      have hdvdP : ∏ p ∈ D, qOf S p ∣ x.natAbs := by
        refine prod_dvd_of_natCoprime ?_ fun p hp =>
          (dvd_mul_left (qOf S p) 4).trans (hx' p hp)
        intro a ha b hb hab
        exact coprime_qOf_of_ne (Nat.prime_of_mem_primesLE (hDsub ha))
          (Nat.prime_of_mem_primesLE (hDsub hb)) hab
      exact hcop.mul_dvd_of_dvd_of_dvd hdvd4 hdvdP
  exact Int.natCast_dvd.mpr hnat

private lemma card_primeFactors_mul_le (a b : ℕ) :
    (a * b).primeFactors.card ≤ a.primeFactors.card + b.primeFactors.card := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [Nat.primeFactors_mul ha hb]
  exact Finset.card_union_le _ _

private lemma exists_good_p' {U t M_bad p : ℕ} {B : Finset ℕ}
    (hB_pos : ∀ n ∈ B, 0 < n)
    (hB_omega : ∀ n ∈ B, n.primeFactors.card ≤ 5)
    (hB_lt : B.card < t)
    (havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1)) :
    ∃ p' ∈ (Nat.primesLE U).erase p, (B.filter (fun n => p' ∣ n)).card ≤ M_bad := by
  by_contra! hall
  let S' := (Nat.primesLE U).erase p
  have hS'_card : (Nat.primesLE U).card - 1 ≤ S'.card := by
    dsimp [S']
    by_cases hp : p ∈ Nat.primesLE U
    · rw [Finset.card_erase_of_mem hp]
    · rw [Finset.erase_eq_of_notMem hp]; omega
  have hlo : S'.card * (M_bad + 1) ≤ ∑ p' ∈ S', (B.filter (fun n => p' ∣ n)).card := by
    calc S'.card * (M_bad + 1)
        = ∑ _p' ∈ S', (M_bad + 1) := by simp
      _ ≤ ∑ p' ∈ S', (B.filter (fun n => p' ∣ n)).card :=
          sum_le_sum fun p' hp' => Nat.succ_le_of_lt (hall p' hp')
  have hswap : ∑ p' ∈ S', (B.filter (fun n => p' ∣ n)).card =
      ∑ n ∈ B, (S'.filter (fun p' => p' ∣ n)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hhi : ∑ n ∈ B, (S'.filter (fun p' => p' ∣ n)).card ≤ 5 * B.card := by
    calc ∑ n ∈ B, (S'.filter (fun p' => p' ∣ n)).card
        ≤ ∑ n ∈ B, n.primeFactors.card := by
          refine sum_le_sum fun n hn => Finset.card_le_card fun p' hp' => ?_
          have ⟨hp'S, hp'n⟩ := mem_filter.mp hp'
          exact Nat.mem_primeFactors.mpr
            ⟨Nat.prime_of_mem_primesLE (mem_of_mem_erase hp'S), hp'n, (hB_pos n hn).ne'⟩
      _ ≤ ∑ _n ∈ B, 5 := sum_le_sum fun n hn => hB_omega n hn
      _ = 5 * B.card := by simp [mul_comm]
  have h1 : ((Nat.primesLE U).card - 1) * (M_bad + 1) ≤ S'.card * (M_bad + 1) :=
    Nat.mul_le_mul_right _ hS'_card
  omega

private lemma exists_prime_avoiding {X : ℕ} (hX : 10 ^ 10 ≤ X) {avoid : Finset ℕ}
    (hav : avoid.card ≤ 3) :
    ∃ r : ℕ, r.Prime ∧ X < r ∧ r ≤ 3 * X ∧ r ∉ avoid := by
  let Pset := (Ioc X (3 * X)).filter Nat.Prime
  have hcard : 5 ≤ Pset.card := five_primes_in_Ioc_three hX
  have hdiff : (Pset \ avoid).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Pset ⊆ avoid := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  obtain ⟨r, hr⟩ := hdiff
  have ⟨hrP, hrA⟩ := mem_sdiff.mp hr
  have ⟨hrI, hrPr⟩ := mem_filter.mp hrP
  have ⟨hr1, hr2⟩ := mem_Ioc.mp hrI
  exact ⟨r, hrPr, hr1, hr2, hrA⟩

private lemma exists_multiplier_r {N S P K U p p' : ℕ}
    (hS_big : 10 ^ 22 ≤ S)
    (hSN : S ≤ N)
    (hP_pos : 0 < P)
    (hK_def : K = N / (16 * P))
    (hSU_L0 : 10 ^ 11 * S * U ≤ K + 1)
    (hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S)
    (hp : p ∈ Nat.primesLE S)
    (hp' : p' ∈ (Nat.primesLE U).erase p) :
    let d := qOf S p * p'
    ∃ r : ℕ, K + 1 ≤ d * r ∧ 4 * P * (d * r) ≤ N ∧
      r ∣ Nat.lcmUpto S ∧ Nat.Coprime d r ∧ r.primeFactors.card ≤ 2 := by
  intro d
  have hp_pr : p.Prime := Nat.prime_of_mem_primesLE hp
  have hp'_mem : p' ∈ Nat.primesLE U := mem_of_mem_erase hp'
  have hp'_pr : p'.Prime := Nat.prime_of_mem_primesLE hp'_mem
  have hp'_le : p' ≤ U := Nat.le_of_mem_primesLE hp'_mem
  have hd_pos : 0 < d := Nat.mul_pos (qOf_pos hp_pr) hp'_pr.pos
  have hd_le : d ≤ S * U := Nat.mul_le_mul (qOf_le_S (by omega)) hp'_le
  set L₀ := K + 1
  set U₀ := N / (4 * P)
  have h4K_U0 : 4 * K ≤ U₀ := by
    have h1 : 16 * P * K ≤ N := by rw [hK_def]; exact Nat.mul_div_le N (16 * P)
    have h2 : (4 * K) * (4 * P) ≤ N := by nlinarith
    exact (Nat.le_div_iff_mul_le (by positivity)).mpr h2
  have hd_L0 : 10 ^ 11 * d ≤ L₀ := by
    calc 10 ^ 11 * d ≤ 10 ^ 11 * (S * U) := Nat.mul_le_mul_left _ hd_le
      _ = 10 ^ 11 * S * U := by ring
      _ ≤ L₀ := hSU_L0
  have hd_pf : d.primeFactors.card ≤ 2 := by
    calc d.primeFactors.card
        ≤ (qOf S p).primeFactors.card + p'.primeFactors.card := card_primeFactors_mul_le _ _
      _ ≤ ({p} : Finset ℕ).card + 1 := by
          rw [hp'_pr.primeFactors, Finset.card_singleton]
          exact Nat.add_le_add_right (Finset.card_le_card (primeFactors_qOf_subset hp_pr)) 1
      _ = 2 := by simp
  set X := L₀ / d + 1
  have hX_big : 10 ^ 10 ≤ X := by
    have : 10 ^ 11 ≤ L₀ / d := (Nat.le_div_iff_mul_le hd_pos).mpr (by linarith)
    omega
  by_cases hA : 3 * X ≤ S
  · obtain ⟨r₁, hr₁_pr, hr₁_gt, hr₁_le, hr₁_av⟩ :=
      exists_prime_avoiding hX_big (by omega : d.primeFactors.card ≤ 3)
    have hcop : Nat.Coprime d r₁ := by
      rw [Nat.coprime_comm]
      refine hr₁_pr.coprime_iff_not_dvd.mpr fun hdvd => hr₁_av ?_
      exact Nat.mem_primeFactors.mpr ⟨hr₁_pr, hdvd, hd_pos.ne'⟩
    have hlo : L₀ ≤ d * r₁ := by
      have h1 : L₀ < d * X := Nat.lt_mul_div_succ L₀ hd_pos
      have h2 : d * X ≤ d * r₁ := Nat.mul_le_mul_left d hr₁_gt.le
      omega
    have hhi : d * r₁ ≤ U₀ := by
      have h1 : d * r₁ ≤ d * (3 * X) := Nat.mul_le_mul_left d hr₁_le
      have h2 : d * (L₀ / d) ≤ L₀ := Nat.mul_div_le L₀ d
      have h3 : d * (3 * X) = 3 * (d * (L₀ / d)) + 3 * d := by dsimp [X]; ring
      omega
    have hhiN : 4 * P * (d * r₁) ≤ N := by
      have h1 : 4 * P * (d * r₁) ≤ 4 * P * U₀ := Nat.mul_le_mul_left _ hhi
      exact h1.trans (Nat.mul_div_le N (4 * P))
    refine ⟨r₁, hlo, hhiN, prime_dvd_lcmUpto hr₁_pr (hr₁_le.trans hA), hcop, ?_⟩
    rw [hr₁_pr.primeFactors, Finset.card_singleton]; decide
  · have hSX : S < 3 * X := lt_of_not_ge hA
    set Y₁ := S / 10 ^ 12
    have hY₁_big : 10 ^ 10 ≤ Y₁ := (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
    obtain ⟨r₁, hr₁_pr, hr₁_gt, hr₁_le, hr₁_av⟩ :=
      exists_prime_avoiding hY₁_big (by omega : d.primeFactors.card ≤ 3)
    have hr₁_S : r₁ ≤ S := by
      have : 10 ^ 12 * Y₁ ≤ S := Nat.mul_div_le S (10 ^ 12)
      omega
    have hcop₁ : Nat.Coprime d r₁ := by
      rw [Nat.coprime_comm]
      refine hr₁_pr.coprime_iff_not_dvd.mpr fun hdvd => hr₁_av ?_
      exact Nat.mem_primeFactors.mpr ⟨hr₁_pr, hdvd, hd_pos.ne'⟩
    set d₁ := d * r₁
    have hd₁_pos : 0 < d₁ := Nat.mul_pos hd_pos hr₁_pr.pos
    have hd₁_pf : d₁.primeFactors.card ≤ 3 := by
      calc d₁.primeFactors.card
          ≤ d.primeFactors.card + r₁.primeFactors.card := card_primeFactors_mul_le _ _
        _ ≤ 2 + 1 := by rw [hr₁_pr.primeFactors, Finset.card_singleton]; omega
        _ = 3 := rfl
    have hdS_le : d * S ≤ 4 * L₀ := by
      have h1 : S ≤ 4 * (L₀ / d) := by dsimp [X] at hSX; omega
      have h2 : d * S ≤ 4 * (d * (L₀ / d)) := by
        calc d * S ≤ d * (4 * (L₀ / d)) := Nat.mul_le_mul_left d h1
          _ = 4 * (d * (L₀ / d)) := by ring
      have h3 : d * (L₀ / d) ≤ L₀ := Nat.mul_div_le L₀ d
      omega
    have hr₁_ub : 10 ^ 12 * r₁ ≤ 3 * S := by
      have h1 : 10 ^ 12 * Y₁ ≤ S := Nat.mul_div_le S (10 ^ 12)
      omega
    have hd₁_L0 : 10 ^ 12 * d₁ ≤ 12 * L₀ := by
      calc 10 ^ 12 * d₁ = d * (10 ^ 12 * r₁) := by dsimp [d₁]; ring
        _ ≤ d * (3 * S) := Nat.mul_le_mul_left d hr₁_ub
        _ = 3 * (d * S) := by ring
        _ ≤ 3 * (4 * L₀) := Nat.mul_le_mul_left 3 hdS_le
        _ = 12 * L₀ := by ring
    set X₂ := L₀ / d₁ + 1
    have hX₂_big : 10 ^ 10 ≤ X₂ := by
      have h1 : 10 ^ 10 * d₁ ≤ L₀ := by omega
      have h2 : 10 ^ 10 ≤ L₀ / d₁ := (Nat.le_div_iff_mul_le hd₁_pos).mpr (by linarith)
      omega
    have h3X₂_S : 3 * X₂ ≤ S := by
      have hr₁_lb : S < 10 ^ 12 * r₁ := by
        have h1 : S < 10 ^ 12 * (Y₁ + 1) := Nat.lt_mul_div_succ S (by positivity)
        have h2 : 10 ^ 12 * (Y₁ + 1) ≤ 10 ^ 12 * r₁ := Nat.mul_le_mul_left _ hr₁_gt
        omega
      have hL₀_N : L₀ ≤ N := by
        have h1 : 16 * P * K ≤ N := by rw [hK_def]; exact Nat.mul_div_le N (16 * P)
        have h2 : K ≤ N := by nlinarith
        have : 16 * K ≤ N := by nlinarith
        omega
      have hprod_le : S * (L₀ / d₁) ≤ 10 ^ 12 * N := by
        calc S * (L₀ / d₁)
            ≤ (10 ^ 12 * r₁) * (L₀ / d₁) := Nat.mul_le_mul_right _ hr₁_lb.le
          _ ≤ (10 ^ 12 * d₁) * (L₀ / d₁) := by
              refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)
              exact Nat.le_mul_of_pos_left r₁ hd_pos
          _ = 10 ^ 12 * (d₁ * (L₀ / d₁)) := by ring
          _ ≤ 10 ^ 12 * L₀ := Nat.mul_le_mul_left _ (Nat.mul_div_le L₀ d₁)
          _ ≤ 10 ^ 12 * N := Nat.mul_le_mul_left _ hL₀_N
      have hmul_S : (3 * X₂) * S ≤ S * S := by
        have h1 : (3 * X₂) * S = 3 * (S * (L₀ / d₁)) + 3 * S := by dsimp [X₂]; ring
        rw [h1]
        have h2 : 3 * S ≤ 10 ^ 12 * N := by omega
        linarith
      exact Nat.le_of_mul_le_mul_right hmul_S (by omega)
    obtain ⟨r₂, hr₂_pr, hr₂_gt, hr₂_le, hr₂_av⟩ :=
      exists_prime_avoiding hX₂_big hd₁_pf
    have hr₂_S : r₂ ≤ S := hr₂_le.trans h3X₂_S
    have hcop_d₁_r₂ : Nat.Coprime d₁ r₂ := by
      rw [Nat.coprime_comm]
      refine hr₂_pr.coprime_iff_not_dvd.mpr fun hdvd => hr₂_av ?_
      exact Nat.mem_primeFactors.mpr ⟨hr₂_pr, hdvd, hd₁_pos.ne'⟩
    have ⟨hcop_d_r₂, hcop_r₁_r₂⟩ := Nat.coprime_mul_iff_left.mp hcop_d₁_r₂
    have hcop_d_r : Nat.Coprime d (r₁ * r₂) := hcop₁.mul_right hcop_d_r₂
    have hr_dvd : r₁ * r₂ ∣ Nat.lcmUpto S :=
      hcop_r₁_r₂.mul_dvd_of_dvd_of_dvd (prime_dvd_lcmUpto hr₁_pr hr₁_S)
        (prime_dvd_lcmUpto hr₂_pr hr₂_S)
    have hlo : L₀ ≤ d * (r₁ * r₂) := by
      rw [← mul_assoc]
      change L₀ ≤ d₁ * r₂
      have h1 : L₀ < d₁ * X₂ := Nat.lt_mul_div_succ L₀ hd₁_pos
      have h2 : d₁ * X₂ ≤ d₁ * r₂ := Nat.mul_le_mul_left d₁ hr₂_gt.le
      omega
    have hhi : d * (r₁ * r₂) ≤ U₀ := by
      rw [← mul_assoc]
      change d₁ * r₂ ≤ U₀
      have h1 : d₁ * r₂ ≤ d₁ * (3 * X₂) := Nat.mul_le_mul_left d₁ hr₂_le
      have h2 : d₁ * (L₀ / d₁) ≤ L₀ := Nat.mul_div_le L₀ d₁
      have h3 : d₁ * (3 * X₂) = 3 * (d₁ * (L₀ / d₁)) + 3 * d₁ := by dsimp [X₂]; ring
      have h4 : 3 * d₁ + 4 ≤ L₀ := by omega
      omega
    have hhiN : 4 * P * (d * (r₁ * r₂)) ≤ N := by
      have h1 : 4 * P * (d * (r₁ * r₂)) ≤ 4 * P * U₀ := Nat.mul_le_mul_left _ hhi
      exact h1.trans (Nat.mul_div_le N (4 * P))
    have hpf : (r₁ * r₂).primeFactors.card ≤ 2 := by
      calc (r₁ * r₂).primeFactors.card
          ≤ r₁.primeFactors.card + r₂.primeFactors.card := card_primeFactors_mul_le _ _
        _ = 1 + 1 := by rw [hr₁_pr.primeFactors, hr₂_pr.primeFactors]; simp
        _ = 2 := rfl
    exact ⟨r₁ * r₂, hlo, hhiN, hr_dvd, hcop_d_r, hpf⟩

private lemma prod_P_inter_gt_N {N P M_bad : ℕ}
    (hN2 : 2 ≤ N)
    (hP_ge : 4 * Real.log (N : ℝ) ≤ (P : ℝ))
    (hP_big : 10 ^ 10 ≤ P)
    (hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2)
    {P₁ P₂ : Finset ℕ}
    (hP₁_sub : P₁ ⊆ (Ioc P (4 * P)).filter Nat.Prime)
    (_hP₂_sub : P₂ ⊆ (Ioc P (4 * P)).filter Nat.Prime)
    (hP₁_bad : ((Ioc P (4 * P)).filter Nat.Prime \ P₁).card ≤ M_bad + 4)
    (hP₂_bad : ((Ioc P (4 * P)).filter Nat.Prime \ P₂).card ≤ M_bad + 4) :
    N < ∏ p ∈ P₁ ∩ P₂, p := by
  let Pset := (Ioc P (4 * P)).filter Nat.Prime
  have hth : (P : ℝ) ≤ ∑ p ∈ Pset, Real.log (p : ℝ) := by
    rw [← theta_sub_eq_sum_Ioc (by omega : P ≤ 4 * P)]
    exact theta_four_sub_ge hP_big
  have hinter_sub : P₁ ∩ P₂ ⊆ Pset := Finset.inter_subset_left.trans hP₁_sub
  have hsdiff_sub : Pset \ (P₁ ∩ P₂) ⊆ (Pset \ P₁) ∪ (Pset \ P₂) := by
    intro p hp
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union] at hp ⊢
    by_cases h1 : p ∈ P₁
    · exact Or.inr ⟨hp.1, fun h2 => hp.2 ⟨h1, h2⟩⟩
    · exact Or.inl ⟨hp.1, h1⟩
  have hbad_card : (Pset \ (P₁ ∩ P₂)).card ≤ 2 * M_bad + 8 := by
    calc (Pset \ (P₁ ∩ P₂)).card
        ≤ ((Pset \ P₁) ∪ (Pset \ P₂)).card := Finset.card_le_card hsdiff_sub
      _ ≤ (Pset \ P₁).card + (Pset \ P₂).card := Finset.card_union_le _ _
      _ ≤ (M_bad + 4) + (M_bad + 4) := Nat.add_le_add hP₁_bad hP₂_bad
      _ = 2 * M_bad + 8 := by ring
  have hbad_sum : ∑ p ∈ Pset \ (P₁ ∩ P₂), Real.log (p : ℝ) ≤ (P : ℝ) / 2 := by
    calc ∑ p ∈ Pset \ (P₁ ∩ P₂), Real.log (p : ℝ)
        ≤ ∑ _p ∈ Pset \ (P₁ ∩ P₂), Real.log ((4 * P : ℕ) : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          have hpP := (mem_sdiff.mp hp).1
          have hp' := mem_filter.mp hpP
          exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast (mem_Ioc.mp hp'.1).2)
      _ = ((Pset \ (P₁ ∩ P₂)).card : ℝ) * Real.log ((4 * P : ℕ) : ℝ) := by simp
      _ ≤ (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 4 * P by omega)))
          exact_mod_cast hbad_card
      _ ≤ (P : ℝ) / 2 := hM_le
  have hsplit := Finset.sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ)) hinter_sub
  have hgood_log : (P : ℝ) / 2 ≤ ∑ p ∈ P₁ ∩ P₂, Real.log (p : ℝ) := by linarith
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogN_lt : Real.log (N : ℝ) < ∑ p ∈ P₁ ∩ P₂, Real.log (p : ℝ) := by linarith
  have hprod_pos : ∀ p ∈ P₁ ∩ P₂, (p : ℝ) ≠ 0 := fun p hp => by
    have hpP := mem_filter.mp (hinter_sub hp)
    exact_mod_cast hpP.2.ne_zero
  have hexp : (N : ℝ) < ((∏ p ∈ P₁ ∩ P₂, p : ℕ) : ℝ) := by
    rw [← Real.exp_log (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < N)]
    have hlog_prod : Real.log ((∏ p ∈ P₁ ∩ P₂, p : ℕ) : ℝ) = ∑ p ∈ P₁ ∩ P₂, Real.log (p : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod hprod_pos]
    have hprod_gt0 : (0 : ℝ) < ((∏ p ∈ P₁ ∩ P₂, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      exact Finset.prod_pos fun p hp => by
        exact_mod_cast (mem_filter.mp (hinter_sub hp)).2.pos
    rw [← Real.exp_log hprod_gt0, hlog_prod]
    exact Real.exp_lt_exp.mpr hlogN_lt
  exact_mod_cast hexp

private noncomputable def Dof (N S K t : ℕ) (j : ℤ) : Finset ℕ :=
  let Q := Nat.lcmUpto S
  let A' := ((Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q).filter fun n => n.primeFactors.card ≤ 5
  (Nat.primesLE S).filter fun p =>
    (A'.filter fun n => qOf S p ∣ n ∧
      ¬ 2 * (j - 4 * (n : ℤ) * round ((j : ℝ) / (4 * n))).natAbs < K).card < t

private lemma exists_common_multiple_near_h {N S P K U t M_bad : ℕ}
    (hN2 : 2 ≤ N)
    (hS_big : 10 ^ 22 ≤ S)
    (hSN : S ≤ N)
    (hP_ge : 4 * Real.log (N : ℝ) ≤ (P : ℝ))
    (hP_big : 10 ^ 10 ≤ P)
    (h4P_S : 4 * P ≤ S)
    (hK_def : K = N / (16 * P))
    (hU_S : U ≤ S)
    (hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2)
    (havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1))
    (hSU_L0 : 10 ^ 11 * S * U ≤ K + 1)
    (hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S)
    (j : ℤ)
    (hDne : (Dof N S K t j).Nonempty) :
    ∃ x : ℤ, 2 * (j - x).natAbs < K ∧ ((4 * ∏ p ∈ Dof N S K t j, qOf S p : ℕ) : ℤ) ∣ x := by
  let Q := Nat.lcmUpto S
  let A' := ((Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q).filter fun n => n.primeFactors.card ≤ 5
  let jNear := fun n : ℕ => 2 * (j - 4 * (n : ℤ) * round ((j : ℝ) / (4 * n))).natAbs < K
  let D := Dof N S K t j
  let Pset := (Ioc P (4 * P)).filter Nat.Prime
  have hK_lt_N : K < N := by
    rw [hK_def]
    exact Nat.div_lt_self (by omega) (by omega)
  have hfor_p : ∀ p ∈ D,
      ∃ (x : ℤ) (Pp : Finset ℕ),
        2 * (j - x).natAbs < K ∧
        ((4 * qOf S p : ℕ) : ℤ) ∣ x ∧
        Pp ⊆ Pset ∧
        (Pset \ Pp).card ≤ M_bad + 4 ∧
        ∀ r ∈ Pp, (r : ℤ) ∣ x := by
    intro p hpD
    have ⟨hpS, hB_lt⟩ := mem_filter.mp hpD
    have hp_pr : p.Prime := Nat.prime_of_mem_primesLE hpS
    let B := A'.filter fun n => qOf S p ∣ n ∧ ¬ jNear n
    have hB_pos : ∀ n ∈ B, 0 < n := fun n hn => by
      have hn1 := (mem_filter.mp hn).1
      have hn2 := (mem_filter.mp hn1).1
      have hn3 := (mem_Icc.mp (mem_filter.mp hn2).1).1
      omega
    have hB_omega : ∀ n ∈ B, n.primeFactors.card ≤ 5 := fun n hn =>
      (mem_filter.mp (mem_filter.mp hn).1).2
    obtain ⟨p', hp'_er, hp'_bad⟩ := exists_good_p' hB_pos hB_omega hB_lt havg
    have hp'_mem : p' ∈ Nat.primesLE U := mem_of_mem_erase hp'_er
    have hp'_pr : p'.Prime := Nat.prime_of_mem_primesLE hp'_mem
    have hp'_ne : p' ≠ p := ne_of_mem_erase hp'_er
    have hp'_S : p' ≤ S := (Nat.le_of_mem_primesLE hp'_mem).trans hU_S
    obtain ⟨r, hr_lo, hr_hi, hr_dvd, hr_cop, hr_pf⟩ :=
      exists_multiplier_r hS_big hSN (by omega) hK_def hSU_L0 hCaseB_S hpS hp'_er
    set d := qOf S p * p'
    set m := d * r
    have hm_pos : 0 < m := by omega
    have hm_dvd_Q : m ∣ Q := by
      have hd_dvd : d ∣ Q :=
        (coprime_qOf_prime_of_ne hp_pr hp'_pr hp'_ne.symm).mul_dvd_of_dvd_of_dvd
          (qOf_dvd_lcmUpto hpS) (prime_dvd_lcmUpto hp'_pr hp'_S)
      exact hr_cop.mul_dvd_of_dvd_of_dvd hd_dvd hr_dvd
    have hm_pf : m.primeFactors.card ≤ 4 := by
      have hd_pf : d.primeFactors.card ≤ 2 := by
        calc d.primeFactors.card
            ≤ (qOf S p).primeFactors.card + p'.primeFactors.card := card_primeFactors_mul_le _ _
          _ ≤ ({p} : Finset ℕ).card + 1 := by
              rw [hp'_pr.primeFactors, Finset.card_singleton]
              exact Nat.add_le_add_right (Finset.card_le_card (primeFactors_qOf_subset hp_pr)) 1
          _ = 2 := by simp
      calc m.primeFactors.card ≤ d.primeFactors.card + r.primeFactors.card :=
            card_primeFactors_mul_le d r
        _ ≤ 2 + 2 := Nat.add_le_add hd_pf hr_pf
        _ = 4 := rfl
    have hmul_mem_A' : ∀ r' ∈ Pset, ¬ r' ∣ m → m * r' ∈ A' ∧ qOf S p ∣ m * r' := by
      intro r' hr' hndvd
      have ⟨hr'I, hr'_pr⟩ := mem_filter.mp hr'
      have ⟨hr'1, hr'2⟩ := mem_Ioc.mp hr'I
      have hcop_mr' : Nat.Coprime m r' := (hr'_pr.coprime_iff_not_dvd.mpr hndvd).symm
      have hmr'_dvd : m * r' ∣ Q :=
        hcop_mr'.mul_dvd_of_dvd_of_dvd hm_dvd_Q (prime_dvd_lcmUpto hr'_pr (hr'2.trans h4P_S))
      have hmr'_leN : m * r' ≤ N := by
        calc m * r' ≤ m * (4 * P) := Nat.mul_le_mul_left m hr'2
          _ = 4 * P * m := by ring
          _ ≤ N := hr_hi
      have hmr'_ge : N ≤ 16 * (m * r') := by
        have h1 : N < 16 * P * (K + 1) := by
          rw [hK_def]; exact Nat.lt_mul_div_succ N (by positivity)
        have h2 : 16 * P * (K + 1) ≤ 16 * r' * m := by
          have ha : 16 * P ≤ 16 * r' := Nat.mul_le_mul_left 16 hr'1.le
          exact Nat.mul_le_mul ha hr_lo
        nlinarith
      have hmr'_pf : (m * r').primeFactors.card ≤ 5 := by
        calc (m * r').primeFactors.card
            ≤ m.primeFactors.card + r'.primeFactors.card := card_primeFactors_mul_le _ _
          _ ≤ 4 + 1 := by rw [hr'_pr.primeFactors, Finset.card_singleton]; omega
          _ = 5 := rfl
      refine ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hm_pos hr'_pr.pos, hmr'_leN⟩, hmr'_ge, hmr'_dvd⟩,
        hmr'_pf⟩, ?_⟩
      exact (dvd_mul_right (qOf S p) p').trans ((dvd_mul_right d r).trans (dvd_mul_right m r'))
    let Pp := Pset.filter fun r' => ¬ r' ∣ m ∧ jNear (m * r')
    have hPp_sub : Pp ⊆ Pset := Finset.filter_subset _ _
    have hPp_bad : (Pset \ Pp).card ≤ M_bad + 4 := by
      let S_div := Pset.filter fun r' => r' ∣ m
      let S_far := Pset.filter fun r' => ¬ r' ∣ m ∧ ¬ jNear (m * r')
      have hcov : Pset \ Pp ⊆ S_div ∪ S_far := by
        intro r' hr'
        have ⟨hr'P, hr'n⟩ := mem_sdiff.mp hr'
        simp only [Pp, mem_filter] at hr'n
        by_cases hdvd : r' ∣ m
        · exact mem_union_left _ (mem_filter.mpr ⟨hr'P, hdvd⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨hr'P, hdvd, fun hjn => hr'n ⟨hr'P, hdvd, hjn⟩⟩)
      have hdiv_card : S_div.card ≤ 4 := by
        have hsub : S_div ⊆ m.primeFactors := by
          intro r' hr'
          have ⟨hr'P, hr'm⟩ := mem_filter.mp hr'
          exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hr'P).2, hr'm, hm_pos.ne'⟩
        exact (Finset.card_le_card hsub).trans hm_pf
      have hfar_card : S_far.card ≤ M_bad := by
        have hinj : S_far.card ≤ (B.filter (fun n => p' ∣ n)).card := by
          refine Finset.card_le_card_of_injOn (fun r' => m * r') ?_ ?_
          · intro r' hr'
            have ⟨hr'P, hndvd, hnjn⟩ := mem_filter.mp hr'
            obtain ⟨hA', hq⟩ := hmul_mem_A' r' hr'P hndvd
            have hp'_dvd : p' ∣ m * r' :=
              (dvd_mul_left p' (qOf S p)).trans ((dvd_mul_right d r).trans (dvd_mul_right m r'))
            exact mem_filter.mpr ⟨mem_filter.mpr ⟨hA', hq, hnjn⟩, hp'_dvd⟩
          · intro a _ b _ hab
            exact Nat.eq_of_mul_eq_mul_left hm_pos hab
        exact hinj.trans hp'_bad
      calc (Pset \ Pp).card ≤ (S_div ∪ S_far).card := Finset.card_le_card hcov
        _ ≤ S_div.card + S_far.card := Finset.card_union_le _ _
        _ ≤ 4 + M_bad := Nat.add_le_add hdiv_card hfar_card
        _ = M_bad + 4 := by omega
    have hPp_ne : Pp.Nonempty := by
      have hgt := prod_P_inter_gt_N hN2 hP_ge hP_big hM_le hPp_sub hPp_sub hPp_bad hPp_bad
      rw [Finset.inter_self] at hgt
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.prod_empty] at hgt
      omega
    obtain ⟨r₀, hr₀⟩ := hPp_ne
    have hr₀_jn : jNear (m * r₀) := (mem_filter.mp hr₀).2.2
    let x : ℤ := 4 * ((m * r₀ : ℕ) : ℤ) * round ((j : ℝ) / (4 * ((m * r₀ : ℕ) : ℝ)))
    have hx_near : 2 * (j - x).natAbs < K := by
      simpa only [jNear, x, Nat.cast_mul] using hr₀_jn
    have hx_4m : ((4 * m : ℕ) : ℤ) ∣ x := by
      refine ⟨(r₀ : ℤ) * round ((j : ℝ) / (4 * ((m * r₀ : ℕ) : ℝ))), ?_⟩
      dsimp only [x]; push_cast; ring
    have hx_4q : ((4 * qOf S p : ℕ) : ℤ) ∣ x := by
      have hqm : 4 * qOf S p ∣ 4 * m :=
        Nat.mul_dvd_mul_left 4 ((dvd_mul_right (qOf S p) p').trans (dvd_mul_right d r))
      exact (Int.natCast_dvd_natCast.mpr hqm).trans hx_4m
    have hx_div_Pp : ∀ r' ∈ Pp, (r' : ℤ) ∣ x := by
      intro r' hr'
      have hr'_jn : jNear (m * r') := (mem_filter.mp hr').2.2
      let y : ℤ := 4 * ((m * r' : ℕ) : ℤ) * round ((j : ℝ) / (4 * ((m * r' : ℕ) : ℝ)))
      have hy_near : 2 * (j - y).natAbs < K := by
        simpa only [jNear, y, Nat.cast_mul] using hr'_jn
      have hy_4m : ((4 * m : ℕ) : ℤ) ∣ y := by
        refine ⟨(r' : ℤ) * round ((j : ℝ) / (4 * ((m * r' : ℕ) : ℝ))), ?_⟩
        dsimp only [y]; push_cast; ring
      have hy_r' : (r' : ℤ) ∣ y := by
        refine ⟨4 * (m : ℤ) * round ((j : ℝ) / (4 * ((m * r' : ℕ) : ℝ))), ?_⟩
        dsimp only [y]; push_cast; ring
      have hdiff_dvd : 4 * m ∣ (x - y).natAbs :=
        Int.natCast_dvd.mp (dvd_sub hx_4m hy_4m)
      have hdiff_lt : (x - y).natAbs < 4 * m := by
        have htri : (x - y).natAbs ≤ (j - x).natAbs + (j - y).natAbs := by
          have heq : x - y = -(j - x) + (j - y) := by ring
          rw [heq]
          calc (-(j - x) + (j - y)).natAbs ≤ (-(j - x)).natAbs + (j - y).natAbs :=
                Int.natAbs_add_le _ _
            _ = (j - x).natAbs + (j - y).natAbs := by rw [Int.natAbs_neg]
        omega
      have hdiff0 : (x - y).natAbs = 0 := by
        by_contra hne
        have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdiff_dvd
        omega
      have hxy : x = y := sub_eq_zero.mp (Int.natAbs_eq_zero.mp hdiff0)
      rw [hxy]; exact hy_r'
    exact ⟨x, Pp, hx_near, hx_4q, hPp_sub, hPp_bad, hx_div_Pp⟩
  obtain ⟨p₀, hp₀⟩ := hDne
  obtain ⟨x₀, P₀, hx₀_near, _, hP₀_sub, hP₀_bad, hx₀_div⟩ := hfor_p p₀ hp₀
  have halleq : ∀ p ∈ D, ((4 * qOf S p : ℕ) : ℤ) ∣ x₀ := by
    intro p hp
    obtain ⟨x₁, P₁, hx₁_near, hx₁_4q, hP₁_sub, hP₁_bad, hx₁_div⟩ := hfor_p p hp
    have hgt : N < ∏ r ∈ P₀ ∩ P₁, r :=
      prod_P_inter_gt_N hN2 hP_ge hP_big hM_le hP₀_sub hP₁_sub hP₀_bad hP₁_bad
    have hprod_dvd : (∏ r ∈ P₀ ∩ P₁, r) ∣ (x₀ - x₁).natAbs := by
      refine prod_dvd_of_natCoprime ?_ fun r hr => ?_
      · intro a ha b hb hab
        have ha' := (mem_filter.mp (hP₀_sub (mem_inter.mp ha).1)).2
        have hb' := (mem_filter.mp (hP₀_sub (mem_inter.mp hb).1)).2
        exact (Nat.coprime_primes ha' hb').mpr hab
      · have hr0 := hx₀_div r (mem_inter.mp hr).1
        have hr1 := hx₁_div r (mem_inter.mp hr).2
        exact Int.natCast_dvd.mp (dvd_sub hr0 hr1)
    have hdiff_lt : (x₀ - x₁).natAbs < ∏ r ∈ P₀ ∩ P₁, r := by
      have htri : (x₀ - x₁).natAbs ≤ (j - x₀).natAbs + (j - x₁).natAbs := by
        have heq : x₀ - x₁ = -(j - x₀) + (j - x₁) := by ring
        rw [heq]
        calc (-(j - x₀) + (j - x₁)).natAbs ≤ (-(j - x₀)).natAbs + (j - x₁).natAbs :=
              Int.natAbs_add_le _ _
          _ = (j - x₀).natAbs + (j - x₁).natAbs := by rw [Int.natAbs_neg]
      omega
    have hdiff0 : (x₀ - x₁).natAbs = 0 := by
      by_contra hne
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hprod_dvd
      omega
    have hxeq : x₀ = x₁ := sub_eq_zero.mp (Int.natAbs_eq_zero.mp hdiff0)
    rw [hxeq]; exact hx₁_4q
  refine ⟨x₀, hx₀_near, four_mul_prod_qOf_dvd (Finset.filter_subset _ _) ⟨p₀, hp₀⟩ halleq⟩

private lemma D_ne_primesLE {N S P K U t M_bad : ℕ}
    (hN2 : 2 ≤ N)
    (hS_big : 10 ^ 22 ≤ S)
    (hSN : S ≤ N)
    (hP_ge : 4 * Real.log (N : ℝ) ≤ (P : ℝ))
    (hP_big : 10 ^ 10 ≤ P)
    (h4P_S : 4 * P ≤ S)
    (hK_def : K = N / (16 * P))
    (hK_lt_Q : K < Nat.lcmUpto S)
    (hU_S : U ≤ S)
    (hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2)
    (havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1))
    (hSU_L0 : 10 ^ 11 * S * U ≤ K + 1)
    (hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S)
    (h : ZMod (4 * Nat.lcmUpto S))
    (hfar : N < 16 * h.valMinAbs.natAbs) :
    Dof N S K t h.valMinAbs ≠ Nat.primesLE S := by
  intro hEq
  let Q := Nat.lcmUpto S
  have hQ_pos : 0 < Q := Nat.lcmUpto_pos S
  have : NeZero (4 * Q) := ⟨by positivity⟩
  have hDne : (Dof N S K t h.valMinAbs).Nonempty := by
    rw [hEq]
    exact ⟨2, Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩⟩
  obtain ⟨x, hx_near, hx_dvd⟩ :=
    exists_common_multiple_near_h hN2 hS_big hSN hP_ge hP_big h4P_S hK_def hU_S hM_le havg
      hSU_L0 hCaseB_S h.valMinAbs hDne
  rw [hEq] at hx_dvd
  have hprodQ : ∏ p ∈ Nat.primesLE S, qOf S p = Q := (Nat.lcmUpto_eq_prod_pow_log S).symm
  rw [hprodQ] at hx_dvd
  have hx_dvd_nat : 4 * Q ∣ x.natAbs := Int.natCast_dvd.mp hx_dvd
  have hj_le : h.valMinAbs.natAbs ≤ 2 * Q := by
    have := ZMod.natAbs_valMinAbs_le h
    omega
  have hx_lt : x.natAbs < 4 * Q := by
    have htri : x.natAbs ≤ h.valMinAbs.natAbs + (h.valMinAbs - x).natAbs := by
      calc x.natAbs = (h.valMinAbs + -(h.valMinAbs - x)).natAbs := by congr 1; ring
        _ ≤ h.valMinAbs.natAbs + (-(h.valMinAbs - x)).natAbs := Int.natAbs_add_le _ _
        _ = h.valMinAbs.natAbs + (h.valMinAbs - x).natAbs := by rw [Int.natAbs_neg]
    omega
  have hx0 : x = 0 := by
    have h0 : x.natAbs = 0 := by
      by_contra hne
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hx_dvd_nat
      omega
    exact Int.natAbs_eq_zero.mp h0
  rw [hx0, sub_zero] at hx_near
  have hK_le : 16 * K ≤ N := by
    have h1 : 16 * P * K ≤ N := by rw [hK_def]; exact Nat.mul_div_le N (16 * P)
    nlinarith
  omega

private lemma weight_le_inv_pow {N S K t : ℕ}
    (hN2 : 2 ≤ N)
    (hK_pos : 0 < K)
    (ht_ge : 10800 * (N : ℝ) ^ 2 * Real.log (N : ℝ) / (K : ℝ) ^ 2 ≤ (t : ℝ))
    (j : ℤ) :
    let Q := Nat.lcmUpto S
    let A := (Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q
    let s := (Nat.primesLE S \ Dof N S K t j).card
    Real.exp (-(8 / 27 : ℝ) * ∑ n ∈ A,
      let x := (j : ℝ) / (4 * n)
      (x - round x) ^ 2) ≤ ((N : ℝ) ^ (10 * s))⁻¹ := by
  intro Q A s
  let A' := A.filter fun n => n.primeFactors.card ≤ 5
  let jNear := fun n : ℕ => 2 * (j - 4 * (n : ℤ) * round ((j : ℝ) / (4 * n))).natAbs < K
  let D := Dof N S K t j
  let f : ℕ → ℝ := fun n =>
    let x := (j : ℝ) / (4 * n)
    (x - round x) ^ 2
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => sq_nonneg _
  have hsubA : ∑ n ∈ A', f n ≤ ∑ n ∈ A, f n :=
    sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => hf_nonneg _
  have hdouble : ∑ p ∈ Nat.primesLE S, ∑ n ∈ A'.filter (fun n => qOf S p ∣ n), f n ≤
      5 * ∑ n ∈ A', f n := by
    have h1 : ∑ p ∈ Nat.primesLE S, ∑ n ∈ A'.filter (fun n => qOf S p ∣ n), f n =
        ∑ n ∈ A', (((Nat.primesLE S).filter (fun p => qOf S p ∣ n)).card : ℝ) * f n := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [h1, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    refine mul_le_mul_of_nonneg_right ?_ (hf_nonneg n)
    have hn_pos : 0 < n := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hn).1).1).1
    have hn_pf : n.primeFactors.card ≤ 5 := (mem_filter.mp hn).2
    have hsub : (Nat.primesLE S).filter (fun p => qOf S p ∣ n) ⊆ n.primeFactors := by
      intro p hp
      have ⟨hpS, hqn⟩ := mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primesLE hpS, (prime_dvd_qOf hpS).trans hqn, hn_pos.ne'⟩
    exact_mod_cast (Finset.card_le_card hsub).trans hn_pf
  have hterm_far : ∀ n ∈ A', ¬ jNear n → (K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2) ≤ f n := by
    intro n hn hnj
    have hnA := mem_filter.mp (mem_filter.mp hn).1
    have ⟨hn1, hnN⟩ := mem_Icc.mp hnA.1
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hN_pos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hgeK : K ≤ 2 * (j - 4 * (n : ℤ) * round ((j : ℝ) / (4 * n))).natAbs := le_of_not_gt hnj
    have hgeK_real : (K : ℝ) ≤ 2 * |(j : ℝ) - 4 * (n : ℝ) * (round ((j : ℝ) / (4 * n)) : ℝ)| := by
      have hcast : (((j - 4 * (n : ℤ) * round ((j : ℝ) / (4 * n))).natAbs : ℕ) : ℝ) =
          |(j : ℝ) - 4 * (n : ℝ) * (round ((j : ℝ) / (4 * n)) : ℝ)| := by
        rw [← Int.cast_natCast, ← Int.abs_eq_natAbs, Int.cast_abs]
        push_cast; rfl
      rw [← hcast]
      exact_mod_cast hgeK
    have hfrac : (j : ℝ) / (4 * (n : ℝ)) - (round ((j : ℝ) / (4 * (n : ℝ))) : ℝ) =
        ((j : ℝ) - 4 * (n : ℝ) * (round ((j : ℝ) / (4 * (n : ℝ))) : ℝ)) / (4 * (n : ℝ)) := by
      field_simp [hn_pos.ne']
    have habs : (K : ℝ) / (8 * (N : ℝ)) ≤
        |(j : ℝ) / (4 * (n : ℝ)) - (round ((j : ℝ) / (4 * (n : ℝ))) : ℝ)| := by
      rw [hfrac, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * (n : ℝ))]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hnN' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      have h1 : (K : ℝ) * (4 * (n : ℝ)) ≤ (K : ℝ) * (4 * (N : ℝ)) := by nlinarith
      nlinarith
    have hsq := pow_le_pow_left₀ (by positivity) habs 2
    rw [sq_abs] at hsq
    have heq : ((K : ℝ) / (8 * (N : ℝ))) ^ 2 = (K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2) := by ring
    dsimp only [f]
    linarith
  have hbad_lower : (s : ℝ) * ((t : ℝ) * ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2))) ≤
      ∑ p ∈ Nat.primesLE S, ∑ n ∈ A'.filter (fun n => qOf S p ∣ n), f n := by
    calc (s : ℝ) * ((t : ℝ) * ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2)))
        = ∑ _p ∈ Nat.primesLE S \ D, (t : ℝ) * ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2)) := by
          simp only [Finset.sum_const, nsmul_eq_mul, s, D]
      _ ≤ ∑ p ∈ Nat.primesLE S \ D,
            ∑ n ∈ A'.filter (fun n => qOf S p ∣ n ∧ ¬ jNear n), f n := by
          refine sum_le_sum fun p hp => ?_
          have ⟨hpS, hpD⟩ := mem_sdiff.mp hp
          have hcard : t ≤ (A'.filter (fun n => qOf S p ∣ n ∧ ¬ jNear n)).card := by
            by_contra hlt
            exact hpD (mem_filter.mpr ⟨hpS, lt_of_not_ge hlt⟩)
          calc (t : ℝ) * ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2))
              ≤ ((A'.filter (fun n => qOf S p ∣ n ∧ ¬ jNear n)).card : ℝ) *
                  ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2)) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
            _ = ∑ _n ∈ A'.filter (fun n => qOf S p ∣ n ∧ ¬ jNear n),
                  (K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2) := by simp
            _ ≤ ∑ n ∈ A'.filter (fun n => qOf S p ∣ n ∧ ¬ jNear n), f n :=
                sum_le_sum fun n hn => hterm_far n (mem_filter.mp hn).1 (mem_filter.mp hn).2.2
      _ ≤ ∑ p ∈ Nat.primesLE S \ D, ∑ n ∈ A'.filter (fun n => qOf S p ∣ n), f n := by
          refine sum_le_sum fun p _ => sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hf_nonneg _
          intro n hn; have ⟨h1, h2, _⟩ := mem_filter.mp hn; exact mem_filter.mpr ⟨h1, h2⟩
      _ ≤ ∑ p ∈ Nat.primesLE S, ∑ n ∈ A'.filter (fun n => qOf S p ∣ n), f n :=
          sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ =>
            sum_nonneg fun _ _ => hf_nonneg _
  have hK_pos' : (0 : ℝ) < K := by exact_mod_cast hK_pos
  have hN_pos' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht_mul : 10800 * Real.log (N : ℝ) / 64 ≤ (t : ℝ) * ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2)) := by
    have h1 := mul_le_mul_of_nonneg_right ht_ge (by positivity : 0 ≤ (K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2))
    have heq : 10800 * (N : ℝ) ^ 2 * Real.log (N : ℝ) / (K : ℝ) ^ 2 *
        ((K : ℝ) ^ 2 / (64 * (N : ℝ) ^ 2)) = 10800 * Real.log (N : ℝ) / 64 := by
      field_simp [hK_pos'.ne', hN_pos'.ne']
    linarith
  have hexp_le : -(8 / 27 : ℝ) * ∑ n ∈ A, f n ≤ -((10 * s : ℕ) : ℝ) * Real.log (N : ℝ) := by
    have h1 : (s : ℝ) * (10800 * Real.log (N : ℝ) / 64) ≤ 5 * ∑ n ∈ A, f n := by
      have hmul := mul_le_mul_of_nonneg_left ht_mul (Nat.cast_nonneg s)
      linarith
    push_cast
    linarith
  calc Real.exp (-(8 / 27 : ℝ) * ∑ n ∈ A, f n)
      ≤ Real.exp (-((10 * s : ℕ) : ℝ) * Real.log (N : ℝ)) := Real.exp_le_exp.mpr hexp_le
    _ = ((N : ℝ) ^ (10 * s))⁻¹ := by
        rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hN_pos']

private lemma card_far_with_D_le {N S P K U t M_bad : ℕ}
    (hN4 : 4 ≤ N)
    (hS_big : 10 ^ 22 ≤ S)
    (hSN : S ≤ N)
    (hP_ge : 4 * Real.log (N : ℝ) ≤ (P : ℝ))
    (hP_big : 10 ^ 10 ≤ P)
    (h4P_S : 4 * P ≤ S)
    (hK_def : K = N / (16 * P))
    (hU_S : U ≤ S)
    (hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2)
    (havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1))
    (hSU_L0 : 10 ^ 11 * S * U ≤ K + 1)
    (hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S)
    (D : Finset ℕ) (hDsub : D ⊆ Nat.primesLE S) :
    let Q := Nat.lcmUpto S
    letI : NeZero Q := ⟨Nat.lcmUpto_ne_zero S⟩
    let s := (Nat.primesLE S \ D).card
    (univ.filter fun h : ZMod (4 * Q) => N < 16 * h.valMinAbs.natAbs ∧ Dof N S K t h.valMinAbs = D).card ≤
      N ^ (s + 1) := by
  dsimp only
  set Q := Nat.lcmUpto S
  have : NeZero Q := ⟨Nat.lcmUpto_ne_zero S⟩
  set s := (Nat.primesLE S \ D).card
  let H := univ.filter fun h : ZMod (4 * Q) => N < 16 * h.valMinAbs.natAbs ∧ Dof N S K t h.valMinAbs = D
  have hprod_split : (∏ p ∈ D, qOf S p) * (∏ p ∈ Nat.primesLE S \ D, qOf S p) = Q := by
    rw [mul_comm, Finset.prod_sdiff hDsub]
    exact (Nat.lcmUpto_eq_prod_pow_log S).symm
  have hR_le : ∏ p ∈ Nat.primesLE S \ D, qOf S p ≤ N ^ s := by
    calc ∏ p ∈ Nat.primesLE S \ D, qOf S p
        ≤ ∏ _p ∈ Nat.primesLE S \ D, N :=
          Finset.prod_le_prod' fun p _ => (qOf_le_S (by omega)).trans hSN
      _ = N ^ s := by simp [s]
  by_cases hDne : D.Nonempty
  · set M := 4 * ∏ p ∈ D, qOf S p
    set R := ∏ p ∈ Nat.primesLE S \ D, qOf S p
    have hMR : M * R = 4 * Q := by
      dsimp [M, R]; rw [mul_assoc, hprod_split]
    have hR_pos : 0 < R := Finset.prod_pos fun p hp => qOf_pos (Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1)
    let box := Finset.range R ×ˢ Finset.Icc (-(K / 2 : ℤ)) (K / 2 : ℤ)
    let φ : ℕ × ℤ → ZMod (4 * Q) := fun p => ((M * p.1 : ℕ) : ZMod (4 * Q)) + (p.2 : ZMod (4 * Q))
    have hsub_img : H ⊆ box.image φ := by
      intro h hh
      have ⟨_, hD_eq⟩ := (mem_filter.mp hh).2
      have hDne' : (Dof N S K t h.valMinAbs).Nonempty := hD_eq.symm ▸ hDne
      obtain ⟨x, hx_near, hx_dvd⟩ :=
        exists_common_multiple_near_h (by omega) hS_big hSN hP_ge hP_big h4P_S hK_def hU_S hM_le
          havg hSU_L0 hCaseB_S h.valMinAbs hDne'
      rw [hD_eq] at hx_dvd
      obtain ⟨u, hu⟩ := hx_dvd
      set r_int : ℤ := u % (R : ℤ)
      have hr_nonneg : 0 ≤ r_int := Int.emod_nonneg u (by exact_mod_cast hR_pos.ne')
      have hr_lt : r_int < (R : ℤ) := Int.emod_lt_of_pos u (by exact_mod_cast hR_pos)
      set r_nat : ℕ := r_int.toNat
      have hr_nat_lt : r_nat < R := by omega
      have hr_cast : (r_nat : ℤ) = r_int := Int.toNat_of_nonneg hr_nonneg
      set d_int : ℤ := h.valMinAbs - x
      have hd_mem : d_int ∈ Finset.Icc (-(K / 2 : ℤ)) (K / 2 : ℤ) := by
        rw [mem_Icc]
        have h1 : 2 * d_int.natAbs < K := hx_near
        have h2 : |d_int| = (d_int.natAbs : ℤ) := Int.abs_eq_natAbs d_int
        have h3 : -(d_int.natAbs : ℤ) ≤ d_int ∧ d_int ≤ (d_int.natAbs : ℤ) := abs_le.mp (le_of_eq h2)
        omega
      refine mem_image.mpr ⟨(r_nat, d_int), mem_product.mpr ⟨mem_range.mpr hr_nat_lt, hd_mem⟩, ?_⟩
      dsimp only [φ]
      have hx_mod : (x : ZMod (4 * Q)) = ((M * r_nat : ℕ) : ZMod (4 * Q)) := by
        have hdiv_mod : u = (R : ℤ) * (u / (R : ℤ)) + r_int := by
          have := Int.emod_add_mul_ediv u (R : ℤ)
          dsimp [r_int]; linarith
        have hx_eq : x = ((4 * Q : ℕ) : ℤ) * (u / (R : ℤ)) + ((M * r_nat : ℕ) : ℤ) := by
          have hMR' : ((4 * Q : ℕ) : ℤ) = (M : ℤ) * (R : ℤ) := by exact_mod_cast hMR.symm
          have hu' : x = (M : ℤ) * u := hu
          rw [hu', hMR']
          conv_lhs => rw [hdiv_mod, ← hr_cast]
          push_cast; ring
        rw [hx_eq]
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add]
      rw [← hx_mod, ← Int.cast_add, show x + d_int = h.valMinAbs by dsimp [d_int]; ring]
      exact h.coe_valMinAbs
    have hK_le : K + 1 ≤ N := by
      have h1 : 16 * P * K ≤ N := by rw [hK_def]; exact Nat.mul_div_le N (16 * P)
      nlinarith
    have hIcc_card : (Finset.Icc (-(K / 2 : ℤ)) (K / 2 : ℤ)).card ≤ N := by
      rw [Int.card_Icc]
      omega
    calc H.card ≤ (box.image φ).card := Finset.card_le_card hsub_img
      _ ≤ box.card := Finset.card_image_le
      _ = R * (Finset.Icc (-(K / 2 : ℤ)) (K / 2 : ℤ)).card := by simp [box]
      _ ≤ N ^ s * N := Nat.mul_le_mul hR_le hIcc_card
      _ = N ^ (s + 1) := by rw [pow_succ]
  · rw [Finset.not_nonempty_iff_eq_empty] at hDne
    have hH_le : H.card ≤ Fintype.card (ZMod (4 * Q)) := Finset.card_le_univ H
    rw [ZMod.card (4 * Q)] at hH_le
    have hQ_eq : Q = ∏ p ∈ Nat.primesLE S \ D, qOf S p := by
      rw [hDne, Finset.sdiff_empty]; exact Nat.lcmUpto_eq_prod_pow_log S
    calc H.card ≤ 4 * Q := hH_le
      _ = 4 * ∏ p ∈ Nat.primesLE S \ D, qOf S p := by rw [hQ_eq]
      _ ≤ N * N ^ s := Nat.mul_le_mul hN4 hR_le
      _ = N ^ (s + 1) := by rw [pow_succ']

private lemma choose_le_pow_self (n k : ℕ) : n.choose k ≤ n ^ k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp
    | succ m =>
      have h1 : (m + 1).choose (k + 1) * (k + 1) = (m + 1) * m.choose k := by
        have := Nat.add_one_mul_choose_eq m k
        linarith
      have h2 : (m + 1).choose (k + 1) ≤ (m + 1) * m.choose k := by
        calc (m + 1).choose (k + 1) ≤ (m + 1).choose (k + 1) * (k + 1) :=
              Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
          _ = (m + 1) * m.choose k := h1
      calc (m + 1).choose (k + 1) ≤ (m + 1) * m.choose k := h2
        _ ≤ (m + 1) * m ^ k := Nat.mul_le_mul_left _ (ih m)
        _ ≤ (m + 1) * (m + 1) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ m) k)
        _ = (m + 1) ^ (k + 1) := by rw [pow_succ']

private lemma far_sum_lt_half {N S P K U t M_bad : ℕ}
    (hN4 : 4 ≤ N)
    (hS_big : 10 ^ 22 ≤ S)
    (hSN : S ≤ N)
    (hP_ge : 4 * Real.log (N : ℝ) ≤ (P : ℝ))
    (hP_big : 10 ^ 10 ≤ P)
    (h4P_S : 4 * P ≤ S)
    (hK_def : K = N / (16 * P))
    (hK_pos : 0 < K)
    (hK_lt_Q : K < Nat.lcmUpto S)
    (hU_S : U ≤ S)
    (ht_ge : 10800 * (N : ℝ) ^ 2 * Real.log (N : ℝ) / (K : ℝ) ^ 2 ≤ (t : ℝ))
    (hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2)
    (havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1))
    (hSU_L0 : 10 ^ 11 * S * U ≤ K + 1)
    (hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S) :
    let Q := Nat.lcmUpto S
    letI : NeZero Q := ⟨Nat.lcmUpto_ne_zero S⟩
    let A := (Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q
    let far := univ.filter fun h : ZMod (4 * Q) => N < 16 * h.valMinAbs.natAbs
    (∑ h ∈ far, Real.exp (-(8 / 27 : ℝ) * ∑ n ∈ A,
      let x := (h.valMinAbs : ℝ) / (4 * n)
      (x - round x) ^ 2)) < 1 / 2 := by
  dsimp only
  set Q := Nat.lcmUpto S
  have : NeZero Q := ⟨Nat.lcmUpto_ne_zero S⟩
  set A := (Icc 1 N).filter fun n => N ≤ 16 * n ∧ n ∣ Q
  set far := univ.filter fun h : ZMod (4 * Q) => N < 16 * h.valMinAbs.natAbs
  let DofH : ZMod (4 * Q) → Finset ℕ := fun h => Dof N S K t h.valMinAbs
  let W : ZMod (4 * Q) → ℝ := fun h =>
    Real.exp (-(8 / 27 : ℝ) * ∑ n ∈ A,
      let x := (h.valMinAbs : ℝ) / (4 * n)
      (x - round x) ^ 2)
  let PS := Nat.primesLE S
  have hPS_le_N : PS.card ≤ N := by
    have hsub : PS ⊆ Icc 1 S := by
      intro p hp
      have ⟨hpS, hpr⟩ := Nat.mem_primesLE.mp hp
      exact mem_Icc.mpr ⟨hpr.one_le, hpS⟩
    calc PS.card ≤ (Icc 1 S).card := Finset.card_le_card hsub
      _ = S := by simp
      _ ≤ N := hSN
  have hmaps : ∀ h ∈ far, DofH h ∈ PS.powerset.erase PS := by
    intro h hh
    refine mem_erase.mpr ⟨?_, mem_powerset.mpr (Finset.filter_subset _ _)⟩
    exact D_ne_primesLE (by omega) hS_big hSN hP_ge hP_big h4P_S hK_def hK_lt_Q hU_S hM_le havg
      hSU_L0 hCaseB_S h (mem_filter.mp hh).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps W]
  have hfiber_le : ∀ D ∈ PS.powerset.erase PS,
      ∑ h ∈ far.filter (fun h => DofH h = D), W h ≤
        ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ := by
    intro D hD
    have hDsub : D ⊆ PS := mem_powerset.mp (mem_of_mem_erase hD)
    have hcard := card_far_with_D_le hN4 hS_big hSN hP_ge hP_big h4P_S hK_def hU_S hM_le havg
      hSU_L0 hCaseB_S D hDsub
    have hfilt_eq : far.filter (fun h => DofH h = D) =
        univ.filter fun h : ZMod (4 * Q) => N < 16 * h.valMinAbs.natAbs ∧ Dof N S K t h.valMinAbs = D := by
      ext h; simp [far, DofH]
    calc ∑ h ∈ far.filter (fun h => DofH h = D), W h
        ≤ ∑ _h ∈ far.filter (fun h => DofH h = D), ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ := by
          refine sum_le_sum fun h hh => ?_
          have hEq : Dof N S K t h.valMinAbs = D := (mem_filter.mp hh).2
          simpa only [W, A, Q, PS, hEq] using
            weight_le_inv_pow (S := S) (by omega) hK_pos ht_ge h.valMinAbs
      _ = ((far.filter (fun h => DofH h = D)).card : ℝ) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ := by simp
      _ ≤ ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hfilt_eq]
          exact_mod_cast hcard
  have hsum1 : ∑ D ∈ PS.powerset.erase PS, ∑ h ∈ far.filter (fun h => DofH h = D), W h ≤
      ∑ D ∈ PS.powerset.erase PS, ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ :=
    sum_le_sum hfiber_le
  have hmaps_s : ∀ D ∈ PS.powerset.erase PS, (PS \ D).card ∈ Icc 1 PS.card := by
    intro D hD
    have ⟨hne, hsub⟩ := mem_erase.mp hD
    have hsub' : D ⊆ PS := mem_powerset.mp hsub
    have hs_pos : 1 ≤ (PS \ D).card := by
      by_contra h0
      have hemp : PS \ D = ∅ := Finset.card_eq_zero.mp (by omega)
      exact hne (Finset.Subset.antisymm hsub' (Finset.sdiff_eq_empty_iff_subset.mp hemp))
    exact mem_Icc.mpr ⟨hs_pos, Finset.card_le_card Finset.sdiff_subset⟩
  conv_rhs at hsum1 => rw [← Finset.sum_fiberwise_of_maps_to hmaps_s]
  have hN_pos : (0 : ℝ) < N := by positivity
  have hN_ge4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
  have hterm_s : ∀ s ∈ Icc 1 PS.card,
      ∑ D ∈ (PS.powerset.erase PS).filter (fun D => (PS \ D).card = s),
        ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ ≤
        ((N : ℝ) ^ 7)⁻¹ := by
    intro s hs
    have hs1 : 1 ≤ s := (mem_Icc.mp hs).1
    have hcard_D : ((PS.powerset.erase PS).filter (fun D => (PS \ D).card = s)).card ≤ N ^ s := by
      have hinj : ((PS.powerset.erase PS).filter (fun D => (PS \ D).card = s)).card ≤
          (PS.powersetCard s).card := by
        refine Finset.card_le_card_of_injOn (fun D => PS \ D) ?_ ?_
        · intro D hD
          have ⟨h1, h2⟩ := mem_filter.mp hD
          exact mem_powersetCard.mpr ⟨Finset.sdiff_subset, h2⟩
        · intro D₁ hD₁ D₂ hD₂ heq
          dsimp only at heq
          have hsub₁ : D₁ ⊆ PS := mem_powerset.mp (mem_of_mem_erase (mem_filter.mp hD₁).1)
          have hsub₂ : D₂ ⊆ PS := mem_powerset.mp (mem_of_mem_erase (mem_filter.mp hD₂).1)
          rw [← Finset.sdiff_sdiff_eq_self hsub₁, ← Finset.sdiff_sdiff_eq_self hsub₂, heq]
      calc ((PS.powerset.erase PS).filter (fun D => (PS \ D).card = s)).card
          ≤ (PS.powersetCard s).card := hinj
        _ = PS.card.choose s := Finset.card_powersetCard s PS
        _ ≤ PS.card ^ s := choose_le_pow_self PS.card s
        _ ≤ N ^ s := Nat.pow_le_pow_left hPS_le_N s
    have hpow_le : (N : ℝ) ^ s * ((N : ℝ) ^ (s + 1) * ((N : ℝ) ^ (10 * s))⁻¹) ≤ ((N : ℝ) ^ 7)⁻¹ := by
      have h1 : (N : ℝ) ^ s * ((N : ℝ) ^ (s + 1) * ((N : ℝ) ^ (10 * s))⁻¹) =
          ((N : ℝ) ^ (2 * s + 1)) / ((N : ℝ) ^ (10 * s)) := by
        rw [div_eq_mul_inv, ← mul_assoc, ← pow_add]
        congr 2; omega
      rw [h1, ← one_div, div_le_div_iff₀ (pow_pos hN_pos _) (pow_pos hN_pos _), one_mul, ← pow_add]
      exact pow_le_pow_right₀ (by linarith) (by omega : 2 * s + 1 + 7 ≤ 10 * s)
    calc ∑ D ∈ (PS.powerset.erase PS).filter (fun D => (PS \ D).card = s),
            ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹
        = ∑ _D ∈ (PS.powerset.erase PS).filter (fun D => (PS \ D).card = s),
            ((N : ℝ) ^ (s + 1)) * ((N : ℝ) ^ (10 * s))⁻¹ :=
          Finset.sum_congr rfl fun D hD => by rw [(mem_filter.mp hD).2]
      _ = (((PS.powerset.erase PS).filter (fun D => (PS \ D).card = s)).card : ℝ) *
            (((N : ℝ) ^ (s + 1)) * ((N : ℝ) ^ (10 * s))⁻¹) := by simp
      _ ≤ (N : ℝ) ^ s * (((N : ℝ) ^ (s + 1)) * ((N : ℝ) ^ (10 * s))⁻¹) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_D) (by positivity)
      _ ≤ ((N : ℝ) ^ 7)⁻¹ := hpow_le
  have hsum2 : ∑ s ∈ Icc 1 PS.card,
      ∑ D ∈ (PS.powerset.erase PS).filter (fun D => (PS \ D).card = s),
        ((N : ℝ) ^ ((PS \ D).card + 1)) * ((N : ℝ) ^ (10 * (PS \ D).card))⁻¹ ≤
      (N : ℝ) * ((N : ℝ) ^ 7)⁻¹ := by
    calc _ ≤ ∑ _s ∈ Icc 1 PS.card, ((N : ℝ) ^ 7)⁻¹ := sum_le_sum hterm_s
      _ = ((Icc 1 PS.card).card : ℝ) * ((N : ℝ) ^ 7)⁻¹ := by simp
      _ ≤ (N : ℝ) * ((N : ℝ) ^ 7)⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Nat.card_Icc]; exact_mod_cast (show PS.card + 1 - 1 ≤ N by omega)
  have hfinal : (N : ℝ) * ((N : ℝ) ^ 7)⁻¹ < 1 / 2 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ (pow_pos hN_pos 7)]
    have hN6 : (4 : ℝ) ^ 6 ≤ (N : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hN_ge4 6
    have hpow : (N : ℝ) ^ 7 = (N : ℝ) * (N : ℝ) ^ 6 := by ring
    rw [hpow]
    nlinarith
  exact lt_of_le_of_lt (hsum1.trans hsum2) hfinal

end MinorArcCore

/- ## Section 3: Asymptotic parameter verification for `c = 1` -/

section Asymptotics

private lemma pow_seven_le_exp_quarter {L : ℝ} (hL : 10 ^ 16 ≤ L) :
    L ^ 7 ≤ Real.exp (L / 4) := by
  have hpow := Real.pow_div_factorial_le_exp (L / 4) (by linarith) 8
  have hfac : (Nat.factorial 8 : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [hfac] at hpow
  have h1 : L ^ 7 * (4 ^ 8 * 40320 : ℝ) ≤ L ^ 8 := by
    have ha : (4 ^ 8 * 40320 : ℝ) ≤ L := by linarith
    have hb := mul_le_mul_of_nonneg_left ha (pow_nonneg (by linarith : 0 ≤ L) 7)
    linarith [show L ^ 7 * L = L ^ 8 by ring]
  have h2 : L ^ 7 ≤ (L / 4) ^ 8 / 40320 := by
    have heq : (L / 4) ^ 8 / 40320 = L ^ 8 / (4 ^ 8 * 40320) := by ring
    rw [heq, le_div_iff₀ (by norm_num)]
    exact h1
  exact h2.trans hpow

private lemma params_avg_bound {N P K U t M_bad : ℕ} {L LL : ℝ}
    (hN_pos : (0 : ℝ) < N)
    (hL_ge : 10 ^ 16 ≤ L)
    (hLL_ge : 10 ^ 15 ≤ LL)
    (hLL_def : LL = Real.log L)
    (hP_ge : 4 * L ≤ (P : ℝ))
    (hP_le : (P : ℝ) ≤ 5 * L)
    (hP_big : 10 ^ 10 ≤ P)
    (hK_real_lo : (N : ℝ) / (100 * L) ≤ (K : ℝ))
    (hU_hi : (U : ℝ) ≤ L ^ 2 * LL ^ 3)
    (hU_lo : L ^ 2 * LL ^ 3 / 2 ≤ (U : ℝ))
    (hU_big : 10 ^ 10 ≤ U)
    (ht_def : t = ⌈10800 * (N : ℝ) ^ 2 * L / (K : ℝ) ^ 2⌉₊)
    (hM_def : M_bad = ⌊(P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ))⌋₊) :
    5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1) := by
  have hL_pos : 0 < L := by linarith
  have hLL_pos : 0 < LL := by linarith
  have hLL_le_L : LL ≤ L := by rw [hLL_def]; linarith [Real.log_le_sub_one_of_pos hL_pos]
  have ht_ub : (t : ℝ) ≤ 2 * 10 ^ 8 * L ^ 3 := by
    have h1 : (t : ℝ) < 10800 * (N : ℝ) ^ 2 * L / (K : ℝ) ^ 2 + 1 := by
      rw [ht_def]; exact Nat.ceil_lt_add_one (by positivity)
    have hK2 : ((N : ℝ) / (100 * L)) ^ 2 ≤ (K : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hK_real_lo 2
    have h2 : 10800 * (N : ℝ) ^ 2 * L / (K : ℝ) ^ 2 ≤
        10800 * (N : ℝ) ^ 2 * L / ((N : ℝ) / (100 * L)) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hK2
    have heq : 10800 * (N : ℝ) ^ 2 * L / ((N : ℝ) / (100 * L)) ^ 2 = 10800 * 10000 * L ^ 3 := by
      field_simp [hN_pos.ne', hL_pos.ne']; ring
    have hL3 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hlogU_ub : Real.log (U : ℝ) ≤ 5 * LL := by
    have h1 : (U : ℝ) ≤ L ^ 5 := by
      have ha : LL ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hLL_pos.le hLL_le_L 3
      calc (U : ℝ) ≤ L ^ 2 * LL ^ 3 := hU_hi
        _ ≤ L ^ 2 * L ^ 3 := mul_le_mul_of_nonneg_left ha (by positivity)
        _ = L ^ 5 := by ring
    have h2 := Real.log_le_log (by exact_mod_cast (show 0 < U by omega)) h1
    rw [Real.log_pow, ← hLL_def] at h2
    exact h2
  have hpiU_lo : L ^ 2 * LL ^ 2 / 20 ≤ ((Nat.primesLE U).card : ℝ) := by
    have h1 := card_primesLE_ge hU_big
    have hlogU_pos : 0 < Real.log (U : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < U by omega))
    have h2 : L ^ 2 * LL ^ 3 / 2 / (2 * (5 * LL)) ≤ (U : ℝ) / (2 * Real.log (U : ℝ)) :=
      div_le_div₀ (by positivity) hU_lo (by positivity) (by linarith)
    have heq : L ^ 2 * LL ^ 3 / 2 / (2 * (5 * LL)) = L ^ 2 * LL ^ 2 / 20 := by
      field_simp [hLL_pos.ne']; ring
    linarith
  have hpiU_sub : L ^ 2 * LL ^ 2 / 40 ≤ (((Nat.primesLE U).card - 1 : ℕ) : ℝ) := by
    have hLL2 : (1 : ℝ) ≤ LL ^ 2 := one_le_pow₀ (by linarith)
    have hL2 : (10 ^ 20 : ℝ) ≤ L ^ 2 := by nlinarith only [hL_ge]
    have hpi_ge2 : (40 : ℝ) ≤ L ^ 2 * LL ^ 2 / 40 := by nlinarith only [hL2, hLL2]
    have hpi_nat : 1 ≤ (Nat.primesLE U).card := by
      have : (1 : ℝ) ≤ ((Nat.primesLE U).card : ℝ) := by linarith
      exact_mod_cast this
    rw [Nat.cast_sub hpi_nat, Nat.cast_one]
    linarith
  have hlog4P_ub : Real.log ((4 * P : ℕ) : ℝ) ≤ 2 * LL := by
    have h1 : ((4 * P : ℕ) : ℝ) ≤ L ^ 2 := by
      push_cast; nlinarith only [hP_le, hL_ge]
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, ← hLL_def] at h2
    exact h2
  have hlog4P_pos : 0 < Real.log ((4 * P : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 4 * P by omega))
  have hM1_lo : L / (4 * LL) ≤ ((M_bad + 1 : ℕ) : ℝ) := by
    have h1 : (P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ)) < ((M_bad + 1 : ℕ) : ℝ) := by
      rw [hM_def]; push_cast; exact Nat.lt_floor_add_one _
    have h2 : 4 * L / (8 * (2 * LL)) ≤ (P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ)) :=
      div_le_div₀ (by positivity) hP_ge (by positivity) (by linarith)
    have heq : 4 * L / (8 * (2 * LL)) = L / (4 * LL) := by field_simp [hLL_pos.ne']; ring
    linarith
  have hprod_lo : L ^ 3 * LL / 160 ≤
      (((Nat.primesLE U).card - 1 : ℕ) : ℝ) * ((M_bad + 1 : ℕ) : ℝ) := by
    have hmul := mul_le_mul hpiU_sub hM1_lo (by positivity) (by positivity)
    have heq : (L ^ 2 * LL ^ 2 / 40) * (L / (4 * LL)) = L ^ 3 * LL / 160 := by
      field_simp [hLL_pos.ne']; ring
    linarith
  have hreal : ((5 * t : ℕ) : ℝ) ≤ (((Nat.primesLE U).card - 1) * (M_bad + 1) : ℕ) := by
    push_cast
    push_cast at hprod_lo
    have h1 : 10 ^ 9 * L ^ 3 ≤ L ^ 3 * LL / 160 := by
      rw [le_div_iff₀ (by norm_num)]
      have ha : (160 * 10 ^ 9 : ℝ) ≤ LL := by linarith
      nlinarith only [ha, pow_pos hL_pos 3]
    linarith
  exact_mod_cast hreal

private lemma asymptotic_far_params :
    ∀ᶠ N : ℕ in atTop,
      let S := ⌊(1 : ℝ) * (N : ℝ) / ((Real.log (N : ℝ)) ^ 3 * (Real.log (Real.log (N : ℝ))) ^ 4)⌋₊
      let P := ⌈4 * Real.log (N : ℝ)⌉₊
      let K := N / (16 * P)
      let U := ⌊(Real.log (N : ℝ)) ^ 2 * (Real.log (Real.log (N : ℝ))) ^ 3⌋₊
      let t := ⌈10800 * (N : ℝ) ^ 2 * Real.log (N : ℝ) / (K : ℝ) ^ 2⌉₊
      let M_bad := ⌊(P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ))⌋₊
      4 ≤ N ∧ 10 ^ 22 ≤ S ∧ S ≤ N ∧
      4 * Real.log (N : ℝ) ≤ (P : ℝ) ∧ 10 ^ 10 ≤ P ∧ 4 * P ≤ S ∧
      0 < K ∧ K < Nat.lcmUpto S ∧ U ≤ S ∧
      10800 * (N : ℝ) ^ 2 * Real.log (N : ℝ) / (K : ℝ) ^ 2 ≤ (t : ℝ) ∧
      (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2 ∧
      5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1) ∧
      10 ^ 11 * S * U ≤ K + 1 ∧
      4 * 10 ^ 12 * N ≤ S * S := by
  have hL_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL_top : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp hL_top
  filter_upwards [eventually_ge_atTop (10 ^ 10), hL_top.eventually_ge_atTop (10 ^ 16),
    hLL_top.eventually_ge_atTop (10 ^ 15)] with N hN_ge hL_ge hLL_ge
  set L := Real.log (N : ℝ)
  set LL := Real.log L
  set D := L ^ 3 * LL ^ 4
  set S := ⌊(1 : ℝ) * (N : ℝ) / D⌋₊
  set P := ⌈4 * L⌉₊
  set K := N / (16 * P)
  set U := ⌊L ^ 2 * LL ^ 3⌋₊
  set t := ⌈10800 * (N : ℝ) ^ 2 * L / (K : ℝ) ^ 2⌉₊
  set M_bad := ⌊(P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ))⌋₊
  set E := Real.exp (L / 4)
  have hN_pos : (0 : ℝ) < N := by positivity
  have hL_pos : 0 < L := by linarith
  have hLL_pos : 0 < LL := by linarith
  have hD_pos : 0 < D := by positivity
  have hE_pos : 0 < E := Real.exp_pos _
  have hE_ge : (10 ^ 15 : ℝ) ≤ E := by
    have h1 := Real.add_one_le_exp (L / 4)
    dsimp [E]; linarith
  have hE4 : E ^ 4 = (N : ℝ) := by
    dsimp [E]; rw [← Real.exp_nat_mul]
    have heq : (4 : ℕ) * (L / 4) = L := by push_cast; ring
    rw [heq]; exact Real.exp_log hN_pos
  have hLL_le_L : LL ≤ L := by linarith [Real.log_le_sub_one_of_pos hL_pos]
  have hD_le_L7 : D ≤ L ^ 7 := by
    have h1 : LL ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hLL_pos.le hLL_le_L 4
    dsimp [D]; nlinarith only [h1, pow_nonneg hL_pos.le 3]
  have hL7_le_E : L ^ 7 ≤ E := pow_seven_le_exp_quarter hL_ge
  have hD_le_E : D ≤ E := hD_le_L7.trans hL7_le_E
  have hE3_le_ND : E ^ 3 ≤ (N : ℝ) / D := by
    rw [le_div_iff₀ hD_pos, ← hE4]
    have h1 := mul_le_mul_of_nonneg_left hD_le_E (pow_nonneg hE_pos.le 3)
    linarith [show E ^ 3 * E = E ^ 4 by ring]
  have hE3_big : (10 ^ 45 : ℝ) ≤ E ^ 3 := by
    have h1 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10 ^ 15) hE_ge 3
    linarith [show ((10 ^ 15 : ℝ) ^ 3) = (10 ^ 45 : ℝ) by norm_num]
  have hS_eq : S = ⌊(N : ℝ) / D⌋₊ := by dsimp [S]; rw [one_mul]
  have hS_real_lo : (N : ℝ) / D - 1 < (S : ℝ) := by
    rw [hS_eq]; linarith [Nat.lt_floor_add_one ((N : ℝ) / D)]
  have hS_real_hi : (S : ℝ) ≤ (N : ℝ) / D := by
    rw [hS_eq]; exact Nat.floor_le (by positivity)
  have hS_ge_E3half : E ^ 3 / 2 ≤ (S : ℝ) := by linarith
  have hS_big : 10 ^ 22 ≤ S := by
    have : (10 ^ 22 : ℝ) ≤ (S : ℝ) := by linarith
    exact_mod_cast this
  have hSN : S ≤ N := by
    have hD1 : 1 ≤ D := by
      have h1 : 1 ≤ L ^ 3 := one_le_pow₀ (by linarith)
      have h2 : 1 ≤ LL ^ 4 := one_le_pow₀ (by linarith)
      dsimp [D]; nlinarith only [h1, h2]
    exact_mod_cast hS_real_hi.trans (div_le_self hN_pos.le hD1)
  have hP_ge : 4 * L ≤ (P : ℝ) := Nat.le_ceil (4 * L)
  have hP_le : (P : ℝ) ≤ 5 * L := by
    have h1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * L)
    linarith
  have hP_big : 10 ^ 10 ≤ P := by
    have : (10 ^ 10 : ℝ) ≤ (P : ℝ) := by linarith
    exact_mod_cast this
  have hL_le_E : L ≤ E := by
    have h1 : 1 ≤ L ^ 6 := one_le_pow₀ (by linarith)
    nlinarith only [h1, hL_pos, hL7_le_E]
  have hE2_big : (10 ^ 30 : ℝ) ≤ E ^ 2 := by nlinarith only [hE_ge]
  have hE_le_E3 : 10 ^ 30 * E ≤ E ^ 3 := by
    have ha : E ^ 3 = E * E ^ 2 := by ring
    rw [ha]; nlinarith only [hE2_big, hE_pos]
  have h4P_S : 4 * P ≤ S := by
    have h1 : ((4 * P : ℕ) : ℝ) ≤ (S : ℝ) := by push_cast; linarith
    exact_mod_cast h1
  have hK_real_lo : (N : ℝ) / (100 * L) ≤ (K : ℝ) := by
    have h1 : (N : ℝ) / (16 * (P : ℝ)) - 1 < (K : ℝ) := by
      have hnat : N < 16 * P * (K + 1) := Nat.lt_mul_div_succ N (by positivity)
      have hreal : (N : ℝ) < 16 * (P : ℝ) * ((K : ℝ) + 1) := by exact_mod_cast hnat
      rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]
      linarith
    have h2 : (N : ℝ) / (80 * L) ≤ (N : ℝ) / (16 * (P : ℝ)) :=
      div_le_div_of_nonneg_left hN_pos.le (by positivity) (by linarith)
    have h3 : (N : ℝ) / (80 * L) - (N : ℝ) / (100 * L) = (N : ℝ) / (400 * L) := by
      field_simp [hL_pos.ne']; ring
    have h4 : 1 ≤ (N : ℝ) / (400 * L) := by
      rw [one_le_div (by positivity), ← hE4]
      have ha : E ^ 4 = E * E ^ 3 := by ring
      rw [ha]; nlinarith only [hL_le_E, hE3_big, hE_pos]
    linarith
  have hK_pos : 0 < K := by
    have h1 : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le (by positivity) hK_real_lo
    exact_mod_cast h1
  have hK_lt_Q : K < Nat.lcmUpto S := by
    have hQ_pos : (0 : ℝ) < (Nat.lcmUpto S : ℝ) := by exact_mod_cast Nat.lcmUpto_pos S
    have hpsi := Chebyshev.psi_ge S
    rw [Chebyshev.psi_eq_log_lcmUpto S] at hpsi
    have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    have hlogS1 : Real.log ((S : ℝ) + 1) ≤ (S : ℝ) / 10 := by
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((S : ℝ) + 1) / 20 by positivity)
      have h2 : Real.log (((S : ℝ) + 1) / 20) = Real.log ((S : ℝ) + 1) - Real.log 20 :=
        Real.log_div (by positivity) (by norm_num)
      have h3 : Real.log 20 ≤ 20 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20)]
      linarith
    have hL_le_S : L ≤ (S : ℝ) / 4 := by
      have h1 : ((4 * P : ℕ) : ℝ) ≤ (S : ℝ) := by exact_mod_cast h4P_S
      push_cast at h1; linarith
    have hS_pos : (0 : ℝ) < S := by positivity
    have hL_lt_logQ : L < Real.log (Nat.lcmUpto S : ℝ) := by
      nlinarith only [hpsi, hlog2, hlogS1, hL_le_S, hS_pos]
    have hN_lt_Q : (N : ℝ) < (Nat.lcmUpto S : ℝ) := by
      rw [← Real.exp_log hN_pos, ← Real.exp_log hQ_pos]
      exact Real.exp_lt_exp.mpr hL_lt_logQ
    have hN_lt_Q_nat : N < Nat.lcmUpto S := by exact_mod_cast hN_lt_Q
    have hK_le_N : K ≤ N := Nat.div_le_self N (16 * P)
    omega
  have hU_hi : (U : ℝ) ≤ L ^ 2 * LL ^ 3 := Nat.floor_le (by positivity)
  have hU_lo : L ^ 2 * LL ^ 3 / 2 ≤ (U : ℝ) := by
    have h1 := Nat.lt_floor_add_one (L ^ 2 * LL ^ 3)
    have ha : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ (by linarith)
    have hb2 : (1 : ℝ) ≤ LL ^ 2 := one_le_pow₀ (by linarith)
    have hb : (2 : ℝ) ≤ LL ^ 3 := by nlinarith only [hb2, hLL_ge]
    have h2 : 2 ≤ L ^ 2 * LL ^ 3 := by nlinarith only [ha, hb]
    linarith
  have hU_big : 10 ^ 10 ≤ U := by
    have ha : (10 ^ 20 : ℝ) ≤ L ^ 2 := by nlinarith only [hL_ge]
    have hb : (1 : ℝ) ≤ LL ^ 3 := one_le_pow₀ (by linarith)
    have h1 : (10 ^ 10 : ℝ) ≤ (U : ℝ) := by nlinarith only [ha, hb, hU_lo]
    exact_mod_cast h1
  have hU_S : U ≤ S := by
    have ha : LL ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hLL_pos.le hLL_le_L 3
    have hb : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ (by linarith)
    have h1 : L ^ 2 * LL ^ 3 ≤ L ^ 7 := by
      calc L ^ 2 * LL ^ 3 ≤ L ^ 2 * L ^ 3 := mul_le_mul_of_nonneg_left ha (by positivity)
        _ = L ^ 5 := by ring
        _ ≤ L ^ 5 * L ^ 2 := le_mul_of_one_le_right (by positivity) hb
        _ = L ^ 7 := by ring
    have h2 : (U : ℝ) ≤ (S : ℝ) := by linarith
    exact_mod_cast h2
  have ht_ge : 10800 * (N : ℝ) ^ 2 * L / (K : ℝ) ^ 2 ≤ (t : ℝ) := Nat.le_ceil _
  have hM_le : (2 * (M_bad : ℝ) + 8) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 2 := by
    have hlog4P_pos : 0 < Real.log ((4 * P : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < 4 * P by omega))
    have hM_hi : (M_bad : ℝ) ≤ (P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ)) :=
      Nat.floor_le (by positivity)
    have h1 : 2 * (M_bad : ℝ) * Real.log ((4 * P : ℕ) : ℝ) ≤ (P : ℝ) / 4 := by
      have ha := mul_le_mul_of_nonneg_right hM_hi (by positivity : 0 ≤ 2 * Real.log ((4 * P : ℕ) : ℝ))
      have heq : (P : ℝ) / (8 * Real.log ((4 * P : ℕ) : ℝ)) * (2 * Real.log ((4 * P : ℕ) : ℝ)) =
          (P : ℝ) / 4 := by field_simp [hlog4P_pos.ne']; ring
      linarith
    linarith [eight_log_four_le_quarter hP_big]
  have havg : 5 * t ≤ ((Nat.primesLE U).card - 1) * (M_bad + 1) :=
    params_avg_bound hN_pos hL_ge hLL_ge rfl hP_ge hP_le hP_big hK_real_lo hU_hi hU_lo hU_big rfl rfl
  have hSU_L0 : 10 ^ 11 * S * U ≤ K + 1 := by
    have hSU_le : (S : ℝ) * (U : ℝ) ≤ (N : ℝ) / (L * LL) := by
      have hmul := mul_le_mul hS_real_hi hU_hi (by positivity) (by positivity)
      have heq : (N : ℝ) / D * (L ^ 2 * LL ^ 3) = (N : ℝ) / (L * LL) := by
        dsimp [D]; field_simp [hL_pos.ne', hLL_pos.ne']
      linarith
    have h1 : 10 ^ 11 * ((N : ℝ) / (L * LL)) ≤ (N : ℝ) / (100 * L) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 : (10 ^ 11 * 100 : ℝ) ≤ LL := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (N : ℝ) * L)
      linarith [show (N : ℝ) * L * (10 ^ 11 * 100) = 10 ^ 11 * (N : ℝ) * (100 * L) by ring,
        show (N : ℝ) * L * LL = (N : ℝ) * (L * LL) by ring]
    have hreal : ((10 ^ 11 * S * U : ℕ) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast hreal
  have hCaseB_S : 4 * 10 ^ 12 * N ≤ S * S := by
    have hsq : E ^ 6 / 4 ≤ (S : ℝ) * (S : ℝ) := by
      have h1 : (E ^ 3 / 2) ^ 2 ≤ (S : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hS_ge_E3half 2
      have heq : (E ^ 3 / 2) ^ 2 = E ^ 6 / 4 := by ring
      have heq2 : (S : ℝ) ^ 2 = (S : ℝ) * (S : ℝ) := sq _
      linarith
    have hreal : ((4 * 10 ^ 12 * N : ℕ) : ℝ) ≤ ((S * S : ℕ) : ℝ) := by
      push_cast; rw [← hE4]
      have ha : E ^ 6 = E ^ 4 * E ^ 2 := by ring
      have h1 : 16 * 10 ^ 12 * E ^ 4 ≤ E ^ 6 := by
        rw [ha]; nlinarith only [hE2_big, pow_pos hE_pos 4]
      linarith
    exact_mod_cast hreal
  exact ⟨by omega, hS_big, hSN, hP_ge, hP_big, h4P_S, hK_pos, hK_lt_Q, hU_S, ht_ge, hM_le,
    havg, hSU_L0, hCaseB_S⟩

end Asymptotics

end Erdos294StepH2

theorem OMA.erdos294FarFrequencies : OMA.R_Erdos294_erdos_294_R1_H1_R1_H2_R1.H2 := by
  refine ⟨1, zero_lt_one, ?_⟩
  filter_upwards [Erdos294StepH2.asymptotic_far_params] with N hN
  obtain ⟨hN4, hS_big, hSN, hP_ge, hP_big, h4P_S, hK_pos, hK_lt_Q, hU_S, ht_ge, hM_le,
    havg, hSU_L0, hCaseB_S⟩ := hN
  exact Erdos294StepH2.far_sum_lt_half hN4 hS_big hSN hP_ge hP_big h4P_S rfl hK_pos hK_lt_Q
    hU_S ht_ge hM_le havg hSU_L0 hCaseB_S

end

section

/-!
For x = log N, y = log x and z = log y choose L = ceiling(x*y^3*z^5).
Then log L ≤ 2y and log log L ≤ 2z, so the smaller smoothness cutoff
eventually exceeds 20x. Chebyshev's elementary lower bound for the lcm
then puts it above 4N. One further factor z absorbs the separation constant.
-/

open Real Filter Finset

namespace Scale294

lemma log_power (d : ℕ) : ∀ᶠ r : ℝ in atTop, 2*(log r)^d ≤ r := by
  filter_upwards [(Real.isLittleO_pow_log_id_atTop (n := d)).bound (show (0 : ℝ) < 1/2 by norm_num),
    eventually_ge_atTop (1 : ℝ)] with r h hr
  have h' : |(log r)^d| ≤ (1/2 : ℝ)*|r| := h
  rw [abs_of_nonneg (pow_nonneg (log_nonneg hr) _),abs_of_nonneg (by linarith)] at h'
  linarith

lemma lcm_monotone {a b : ℕ} (h : a ≤ b) : Nat.lcmUpto a ∣ Nat.lcmUpto b := by
  unfold Nat.lcmUpto
  apply Finset.lcm_dvd
  intro n hn
  apply Finset.dvd_lcm
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans h⟩

lemma lcm_large {N S : ℕ} (hN : 0 < N) (hx : 8 ≤ Real.log (N : ℝ))
    (hS : 20 * Real.log (N : ℝ) ≤ S) : 4*N ≤ Nat.lcmUpto S := by
  have hpos : 0 < (N : ℝ) := by positivity
  have hs : (128 : ℝ) ≤ S := by linarith
  have hh : Real.log ((S : ℝ)+1) ≤ (S : ℝ)/4 := by
    rw [show (S : ℝ)+1 = 8*(((S : ℝ)+1)/8) by ring,Real.log_mul (by norm_num) (by positivity)]
    have h := Real.log_le_self (show 0 ≤ ((S : ℝ)+1)/8 by positivity)
    linarith [Real.log_le_self (by norm_num : (0 : ℝ) ≤ 8)]
  have ht : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hψ := Chebyshev.psi_ge S
  rw [Chebyshev.psi_eq_log_lcmUpto] at hψ
  have hf : Real.log ((4 : ℝ)*N) ≤ Real.log (Nat.lcmUpto S) := by
    rw [Real.log_mul (by norm_num) hpos.ne']
    nlinarith [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (S : ℝ)),
      Real.log_le_self (by norm_num : (0 : ℝ) ≤ 4)]
  exact_mod_cast (Real.log_le_log_iff (by positivity) (by exact_mod_cast Nat.lcmUpto_pos S)).mp hf

end Scale294

open Scale294

theorem OMA.erdos294Upper : OMA.R_Erdos294_erdos_294_R1.H2 := by
  intro c hc N₀
  refine ⟨6,?_⟩
  have tx := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ty := Real.tendsto_log_atTop.comp tx
  have tz := Real.tendsto_log_atTop.comp ty
  filter_upwards [tz.eventually_ge_atTop 64,tz.eventually_ge_atTop (4096/c),
    tx.eventually_ge_atTop (max 128 (N₀ : ℝ)),ty.eventually_ge_atTop 64,
    tx.eventually (log_power 8),tendsto_natCast_atTop_atTop.eventually (log_power 9),
    eventually_ge_atTop (1 : ℕ)] with N hz64 hcz hx' hy64 hp8 hp9 hN
  let x := log (N : ℝ)
  let y := log x
  let z := log y
  change 64 ≤ z at hz64
  change 4096/c ≤ z at hcz
  change max 128 (N₀ : ℝ) ≤ x at hx'
  change 64 ≤ y at hy64
  change 2*y^8 ≤ x at hp8
  change 2*x^9 ≤ (N : ℝ) at hp9
  have hx : 128 ≤ x := (le_max_left ..).trans hx'
  have hxN : (N₀ : ℝ) ≤ x := (le_max_right ..).trans hx'
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  have hzy : z ≤ y := Real.log_le_self hy0.le
  have hyx : y ≤ x := Real.log_le_self hx0.le
  have hcz' := (div_le_iff₀ hc).mp hcz
  let B := x*y^3*z^5
  let L := ⌈B⌉₊
  have hB : x ≤ B := by
    calc
      x = x*1^3*1^5 := by ring
      _ ≤ x*y^3*z^5 := by gcongr <;> linarith
  have hLlo : B ≤ (L : ℝ) := Nat.le_ceil _
  have hLup : (L : ℝ) ≤ 2*B := by
    have := Nat.ceil_lt_add_one (show 0 ≤ B by linarith)
    change (L : ℝ) < B+1 at this
    linarith
  have hLx : (L : ℝ) ≤ x^2 := calc
    _ ≤ 2*(x*y^3*z^5) := hLup
    _ ≤ 2*(x*y^3*y^5) := by gcongr
    _ = x*(2*y^8) := by ring
    _ ≤ x*x := by gcongr
    _ = _ := by ring
  have hlog : log L ≤ 2*y := calc
    _ ≤ log (x^2) := Real.log_le_log (by linarith) hLx
    _ = _ := by rw [Real.log_pow]; simp [y]
  have hlog0 : y ≤ log L := Real.log_le_log hx0 (by linarith)
  have hloglog0 : z ≤ log (log L) := Real.log_le_log hy0 hlog0
  have hloglog : log (log L) ≤ 2*z := calc
    _ ≤ log (2*y) := Real.log_le_log (by linarith) hlog
    _ = log 2 + z := by rw [Real.log_mul (by norm_num) hy0.ne']
    _ ≤ _ := by linarith [Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2)]
  let DL := (log L)^3*(log (log L))^4
  have hd0 : 0 < DL := mul_pos (pow_pos (by linarith) _) (pow_pos (by linarith) _)
  have hd1 : 1 ≤ DL := by
    change 1 ≤ (log L)^3*(log (log L))^4
    calc
      1 = (1 : ℝ)^3*1^4 := by norm_num
      _ ≤ _ := by gcongr <;> linarith
  have hdhi : DL ≤ 128*y^3*z^4 := calc
    _ ≤ (2*y)^3*(2*z)^4 := by dsimp [DL]; gcongr <;> linarith
    _ = _ := by ring
  let SL := ⌊c*(L:ℝ)/DL⌋₊
  have hbig : 21*x ≤ c*(L:ℝ)/DL := by
    apply (le_div_iff₀ hd0).mpr
    calc
      21*x*DL ≤ 21*x*(128*y^3*z^4) := by gcongr
      _ ≤ (x*y^3*z^4)*(z*c) := by
        have hh : 2688 ≤ z*c := by linarith
        nlinarith only [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ x*y^3*z^4)]
      _ = c*B := by dsimp [B]; ring
      _ ≤ _ := by gcongr
  have hSL : 20*x ≤ (SL : ℝ) := by
    have hh := Nat.lt_floor_add_one (c*(L:ℝ)/DL)
    change _ < (SL : ℝ)+1 at hh
    linarith
  have hctl : (L : ℝ)*(x^3*y^4) ≤ N := calc
    _ ≤ x^2*(x^3*x^4) := by gcongr
    _ = x^9 := by ring
    _ ≤ _ := by linarith [show 0 ≤ x^9 by positivity]
  have hdiv : SL ≤ ⌊c*(N : ℝ)/(x^3*y^4)⌋₊ := by
    apply Nat.floor_le_floor
    calc
      c*(L:ℝ)/DL ≤ c*(L:ℝ) := div_le_self (by positivity) hd1
      _ ≤ _ := by
        apply (le_div_iff₀ (by positivity)).mpr
        calc
          c*(L:ℝ)*(x^3*y^4) = c*((L:ℝ)*(x^3*y^4)) := by ring
          _ ≤ _ := by gcongr
  refine ⟨L,by exact_mod_cast (show (N₀ : ℝ) ≤ L by linarith),
    by exact_mod_cast (show (32 : ℝ) ≤ L by linarith),
    lcm_large hN (by change 8 ≤ x; linarith) hSL,lcm_monotone hdiv,?_⟩
  change 32*(L : ℝ)*|(N:ℝ)/(x*y^3*z^(6 : ℝ))| ≤ N
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,Real.rpow_natCast,abs_of_nonneg (by positivity)]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  have hfin : 32*(L : ℝ) ≤ x*y^3*z^6 := calc
    _ ≤ 32*(2*B) := by gcongr
    _ = 64*B := by ring
    _ ≤ z*B := by gcongr
    _ = _ := by dsimp [B]; ring
  nlinarith only [mul_le_mul_of_nonneg_right hfin (by positivity : 0 ≤ (N : ℝ))]

end

namespace OMA.Erdos305Proof

open Finset Filter Real
open scoped BigOperators

/-- The Liu–Sawhney estimates proved in the Erdős 294 formalization. -/
private theorem moderateFractions : OMA.R_Erdos294_erdos_294_R1.H1 :=
  OMA.R_Erdos294_erdos_294_R1_H1_R1.main OMA.erdos294Fourier
    (OMA.R_Erdos294_erdos_294_R1_H1_R1_H2_R1.main
      OMA.erdos294NearFrequencies OMA.erdos294FarFrequencies)

private theorem sum_dilate (m : ℕ) (hm : 0 < m) (B : Finset ℕ) :
    (∑ d ∈ B.image (m * ·), (1 : ℚ) / d) = (∑ d ∈ B, (1 : ℚ) / d) / m := by
  rw [Finset.sum_div, Finset.sum_image]
  · exact sum_congr rfl fun d _ => by push_cast; ring
  · intro d _ e _ he
    exact Nat.eq_of_mul_eq_mul_left hm he

/-- A fixed finite range of positive integers has representations with a common
bound on the denominators, by successively using disjoint intervals. -/
private theorem smallIntegerFractions (k : ℕ) :
    ∃ M : ℕ, ∀ a ≤ k, ∃ B : Finset ℕ, (∀ d ∈ B, 0 < d ∧ d ≤ M) ∧
      ∑ d ∈ B, (1 : ℚ) / d = (a : ℚ) := by
  obtain ⟨c, hc, N₀, hrep⟩ := moderateFractions
  induction k with
  | zero =>
    refine ⟨0, fun a ha => ⟨∅, by simp, ?_⟩⟩
    have : a = 0 := by omega
    simp [this]
  | succ k ih =>
    obtain ⟨M, hM⟩ := ih
    let L := max N₀ (16 * M + 16)
    have hL : 16 * M + 16 ≤ L := le_max_right _ _
    obtain ⟨F, hF, hsumF⟩ :=
      hrep L (le_max_left _ _) 1 1 (by decide) (one_dvd _) (by decide) (by decide)
    have hfresh : ∀ d ∈ F, M < d ∧ d ≤ L := by
      intro d hd
      obtain ⟨hlo, hhi⟩ := hF d hd
      exact ⟨by omega, hhi⟩
    refine ⟨L, fun a ha => ?_⟩
    by_cases hok : a ≤ k
    · obtain ⟨B, hb, hsumB⟩ := hM a hok
      exact ⟨B, fun d hd => ⟨(hb d hd).1, le_trans (hb d hd).2 (by omega)⟩, hsumB⟩
    · have ha' : a = k + 1 := by omega
      obtain ⟨B, hb, hsumB⟩ := hM k le_rfl
      have hdj : Disjoint B F := disjoint_left.mpr fun d hd hf =>
        (not_lt_of_ge (hb d hd).2) (hfresh d hf).1
      refine ⟨B ∪ F, ?_, ?_⟩
      · intro d hd
        rcases mem_union.mp hd with hB | hF'
        · exact ⟨(hb d hB).1, le_trans (hb d hB).2 (by omega)⟩
        · exact ⟨by have := (hfresh d hF').1; omega, (hfresh d hF').2⟩
      · rw [sum_union hdj, hsumB, hsumF, ha', Nat.cast_add, Nat.cast_one] <;> norm_num

/-- Choose the two normalized fractions with numerators between Q/3 and Q.
Their denominator dilations differ by a factor greater than 16. -/
private theorem selectNumerators {a b Q : ℕ} (ha : 17 < a) (hab : a < b)
    (hQ : 4 * b ≤ Q) :
    ∃ u v s : ℕ, 0 < s ∧ 16 * s < b ∧ v + u * b = a * Q ∧
      Q ≤ 3 * v ∧ v ≤ Q ∧ Q ≤ 3 * (s * u) ∧ s * u ≤ Q := by
  have hb : 0 < b := by omega
  let u := (a - 1) * Q / b + 1
  have hu0 : 0 < u := Nat.succ_pos _
  have hlow : (a - 1) * Q < u * b := by
    simpa [u, Nat.mul_comm] using Nat.lt_mul_div_succ ((a - 1) * Q) hb
  have hupp : u * b ≤ (a - 1) * Q + b := by
    dsimp [u]
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self ((a - 1) * Q) b) b
  have haq : (a - 1) * Q + Q = a * Q := by
    calc
      (a - 1) * Q + Q = ((a - 1) + 1) * Q := by rw [Nat.add_mul, Nat.one_mul]
      _ = a * Q := by rw [show a - 1 + 1 = a by omega]
  have huab : u * b ≤ a * Q := hupp.trans (by omega)
  have huQ : u ≤ Q := by
    by_contra! h
    have gt := Nat.mul_lt_mul_of_pos_right h hb
    have le := Nat.mul_le_mul_right Q hab.le
    rw [Nat.mul_comm b Q] at le
    omega
  let v := a * Q - u * b
  have hv : v + u * b = a * Q := Nat.sub_add_cancel huab
  let s := Q / u
  have hs : 0 < s := Nat.div_pos huQ hu0
  have hsu : s * u ≤ Q := Nat.div_mul_le_self Q u
  have hsuLower : Q ≤ 3 * (s * u) := by
    have hnext : Q < (s + 1) * u := by
      simpa [s, Nat.mul_comm] using Nat.lt_mul_div_succ Q hu0
    rw [Nat.add_mul, Nat.one_mul] at hnext
    have hu_le : u ≤ s * u := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right u (show 1 ≤ s by omega)
    omega
  have hsep : 16 * s < b := by
    by_contra! h
    have hbound : u * b ≤ 16 * (s * u) := by
      simpa only [Nat.mul_assoc, Nat.mul_comm b u] using Nat.mul_le_mul_right u h
    have hlarge : 16 * Q ≤ (a - 1) * Q :=
      Nat.mul_le_mul_right Q (by omega)
    exact (not_lt_of_ge (hbound.trans ((Nat.mul_le_mul_left 16 hsu).trans hlarge))) hlow
  exact ⟨u, v, s, hs, hsep, hv, by omega, by omega, hsuLower, hsu⟩

/-- Splitting the rational into two fractions with a common smooth denominator
allows both blocks to be chosen at the same scale. -/
private theorem representFromTwoBlocks {c : ℝ} {N₀ L a b : ℕ}
    (hrep : ∀ N : ℕ, N₀ ≤ N →
      ∀ d a : ℕ, 0 < d →
      d ∣ Nat.lcmUpto ⌊c * (N : ℝ) / (Real.log N ^ 3 * Real.log (Real.log N) ^ 4)⌋₊ →
      d ≤ 3 * a → a ≤ d →
      ∃ B : Finset ℕ, (∀ x ∈ B, N ≤ 16 * x ∧ x ≤ N) ∧
        ∑ x ∈ B, (1 : ℚ) / x = (a : ℚ) / d)
    (hN : N₀ ≤ L) (hL : 32 ≤ L)
    (ha : 17 < a) (hab : a < b)
    (hQ : 4 * b ≤ Nat.lcmUpto ⌊c * (L : ℝ) / (Real.log L ^ 3 * Real.log (Real.log L) ^ 4)⌋₊) :
    ∃ E : Finset ℕ, (∀ d ∈ E, 0 < d ∧ d ≤ b * L) ∧
      ∑ d ∈ E, (1 : ℚ) / d = (a : ℚ) / b := by
  let Q := Nat.lcmUpto ⌊c * (L : ℝ) / (Real.log L ^ 3 * Real.log (Real.log L) ^ 4)⌋₊
  have hQ0 : 0 < Q := Nat.lcmUpto_pos _
  have hb : 0 < b := by omega
  obtain ⟨u, v, s, hs, hsep, hv, hvLo, hvHi, hsuLo, hsuHi⟩ :=
    selectNumerators ha hab (Q := Q) hQ
  obtain ⟨B, hB, hsumB⟩ := hrep L hN Q v hQ0 dvd_rfl hvLo hvHi
  obtain ⟨D, hD, hsumD⟩ := hrep L hN Q (s * u) hQ0 dvd_rfl hsuLo hsuHi
  let B' := B.image (b * ·)
  let D' := D.image (s * ·)
  have hScaleSep : 16 * (s * L) < b * L := by
    simpa only [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_right hsep (show 0 < L by omega)
  have hdisj : Disjoint B' D' := by
    apply disjoint_left.mpr
    intro z hzB hzD
    obtain ⟨x, hxB, hx⟩ := mem_image.mp hzB
    obtain ⟨y, hyD, hy⟩ := mem_image.mp hzD
    have hlo : b * L ≤ 16 * z := by
      have h := Nat.mul_le_mul_left b (hB x hxB).1
      rwa [Nat.mul_left_comm b 16 x, hx] at h
    have hhi : 16 * z ≤ 16 * (s * L) := by
      rw [← hy]
      exact Nat.mul_le_mul_left 16 (Nat.mul_le_mul_left s (hD y hyD).2)
    omega
  refine ⟨B' ∪ D', ?_, ?_⟩
  · intro z hz
    rcases mem_union.mp hz with hzB | hzD
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hzB
      obtain ⟨hlo, hhi⟩ := hB x hx
      exact ⟨Nat.mul_pos hb (by omega), Nat.mul_le_mul_left b hhi⟩
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp hzD
      obtain ⟨hlo, hhi⟩ := hD y hy
      exact ⟨Nat.mul_pos hs (by omega),
        (Nat.mul_le_mul_left s hhi).trans (Nat.mul_le_mul_right L (by omega))⟩
  · rw [sum_union hdisj]
    change (∑ d ∈ B.image (b * ·), (1 : ℚ) / d) +
      (∑ d ∈ D.image (s * ·), (1 : ℚ) / d) = (a : ℚ) / b
    rw [sum_dilate b hb, sum_dilate s hs, hsumB, hsumD, Nat.cast_mul]
    have hv' : (v : ℚ) + (u : ℚ) * b = (a : ℚ) * Q := by exact_mod_cast hv
    have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ0.ne'
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
    have cancel : ((s : ℚ) * (u : ℚ) / Q) / s = (u : ℚ) / Q := by
      field_simp [hQ', hs']
    rw [cancel]
    field_simp [hQ', hb'] <;> nlinarith only [hv']

theorem bound : type_of% @Erdos305.erdos_305.variants.liu_sawhney := by
  obtain ⟨c, hc, N₀, hrep⟩ := moderateFractions
  obtain ⟨M, hsmall⟩ := smallIntegerFractions 17
  obtain ⟨K, hK⟩ := OMA.erdos294Upper c hc (max N₀ M)
  refine ⟨1, K, one_pos, ?_⟩
  have hlog : Tendsto (fun b : ℕ => Real.log (b : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun b : ℕ => Real.log (Real.log (b : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlogloglog : Tendsto (fun b : ℕ => Real.log (Real.log (Real.log (b : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hloglog
  filter_upwards [hK, eventually_gt_atTop (0 : ℕ),
    hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_gt_atTop (0 : ℝ)),
    hlogloglog.eventually (eventually_gt_atTop (0 : ℝ))] with b hLdata hb hlogb hloglogb hlogloglogb
  obtain ⟨L, hL0, hL32, hQ, _, hscale⟩ := hLdata
  let f : ℝ := Real.log b * Real.log (Real.log b) ^ 3 * Real.log (Real.log (Real.log b)) ^ K
  have hf : 0 < f := mul_pos (mul_pos hlogb (pow_pos hloglogb 3))
    (Real.rpow_pos_of_pos hlogloglogb K)
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hLle : (L : ℝ) ≤ f := by
    change 32 * (L : ℝ) * |(b : ℝ) / f| ≤ (b : ℝ) at hscale
    rw [abs_of_pos (div_pos hbR hf),
      show 32 * (L : ℝ) * ((b : ℝ) / f) = (32 * (L : ℝ) * b) / f by ring,
      div_le_iff₀ hf] at hscale
    have h32 := (mul_le_mul_iff_of_pos_right hbR).mp (by
      simpa only [mul_comm (b : ℝ) f] using hscale : 32 * (L : ℝ) * b ≤ f * b)
    linarith only [h32, (Nat.cast_nonneg L : (0 : ℝ) ≤ (L : ℝ))]
  have hbL : Erdos305.Dmax b ≤ b * L := by
    unfold Erdos305.Dmax
    apply Finset.sup_le
    intro a ha
    have hab := (mem_Ico.mp ha).2
    have hrepBound : ∃ E : Finset ℕ, (∀ d ∈ E, 0 < d ∧ d ≤ b * L) ∧
        ∑ d ∈ E, (1 : ℚ) / d = (a : ℚ) / b := by
      by_cases ha' : a ≤ 17
      · obtain ⟨B, hB, hsum⟩ := hsmall a ha'
        refine ⟨B.image (b * ·), ?_, ?_⟩
        · intro d hd
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hd
          obtain ⟨hx0, hxM⟩ := hB x hx
          exact ⟨Nat.mul_pos hb hx0, Nat.mul_le_mul_left b (hxM.trans ((le_max_right _ _).trans hL0))⟩
        · rw [sum_dilate b hb, hsum]
      · exact representFromTwoBlocks hrep ((le_max_left _ _).trans hL0) hL32 (by omega) hab hQ
    obtain ⟨E, hE, hsum⟩ := hrepBound
    unfold Erdos305.D
    apply Nat.sInf_le
    exact ⟨E, fun h => (hE 0 h).1.false, fun d hd => (hE d hd).2, hsum⟩
  calc
    (Erdos305.Dmax b : ℝ) ≤ (b : ℝ) * L := by exact_mod_cast hbL
    _ ≤ (b : ℝ) * f := mul_le_mul_of_nonneg_left hLle hbR.le
    _ = _ := by dsimp [f]; ring

end OMA.Erdos305Proof

theorem OMA.solution : type_of% @Erdos305.erdos_305.variants.liu_sawhney :=
  OMA.Erdos305Proof.bound
