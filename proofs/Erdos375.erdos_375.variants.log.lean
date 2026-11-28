import FormalConjectures.ErdosProblems.«375»
import Mathlib

-- Credit: @synthrosai (shorter proof by cofactor averaging)

/-! # Distinct prime representatives for a logarithmic block of composite integers

The standalone assembly first appeared in PR 16479 and includes the reductions
from PRs 4808 and 5097 and their component proofs.

This is the Ramachandra–Shorey–Tijdeman theorem. The two reductions and their
component proofs come from the open-math-agents registry. The proof of the
two-logarithm estimate is the contribution in PR 13986, commit 392e25d0.
The new large-obstruction argument by synthrosai applies cofactor averaging
and reuses the rounded-exponent lemma from the small-obstruction case.
The final theorem composes the Hall obstruction, its two size cases, the
linear-form bound, and the choice of analytic parameters. -/

/-! Ramachandra, Shorey and Tijdeman, J. Reine Angew. Math. 273 (1975),
109–124. A minimal obstruction to Hall's theorem has only primes smaller
than the block length (their Lemmas 2–3). Section 2 produces a very small
linear form in two logarithms from such an obstruction. Section 3 bounds
this linear form from below. We separate the scalar choice of the parameter
in the latter bound and absorb all finite endpoints. -/
namespace OMA.R_Erdos375_erdos_375_variants_log_R1

open Finset Filter Real

/-- The two-logarithm configuration from the combinatorial argument of
section 2, with the height scale allowed to be an arbitrarily small power. -/
def H1 : Prop := ∀ b : ℝ, 0 < b → ∀ S₀ : ℝ, ∃ c > (0:ℝ), ∀ᶠ n : ℕ in atTop,
  ∀ k : ℕ, (k:ℝ) < c*(log n/log (log n))^3 →
  ∀ J : Finset (Fin k),
  let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
  P.card < J.card → (∀ p ∈ P, p < k) →
  ∃ (S : ℝ) (u v : ℚ) (m : ℤ), S₀ ≤ S ∧ S ≤ (n:ℝ)^b ∧ 0 < u ∧ 0 < v ∧
    (u.num.natAbs+u.den:ℕ) ≤ (log S)^16 ∧ ((v.num.natAbs+v.den:ℕ):ℝ) ≤ S ∧
    2*log S/log (log S) ≤ |(m:ℝ)| ∧ |(m:ℝ)| ≤ (log S)^16 ∧
    |log (v:ℝ)| ≤ (log S)^(3/4:ℝ) ∧
    0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧ |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ))

/-- The two-logarithm theorem of section 3, with height exponents A=B=16. -/
def H2 : Prop := ∃ D > (0:ℝ), ∀ S : ℝ, 27 < S → ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
  ∀ (u v : ℚ) (m : ℤ), 0 < u → 0 < v →
  ((u.num.natAbs+u.den:ℕ):ℝ) ≤ (log S)^16 → ((v.num.natAbs+v.den:ℕ):ℝ) ≤ S →
  2*log S/log (log S) ≤ |(m:ℝ)| → |(m:ℝ)| ≤ (log S)^16 →
  |log (v:ℝ)| ≤ log S/log (log S)*exp (-(log (log S))^z) →
  0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| →
  exp (-D*log S*(log (log S))^(4-4*z)) ≤ |(m:ℝ)*log (u:ℝ)-log (v:ℝ)|

/-- An elementary choice of the free exponent in the logarithm estimate. -/
def H3 : Prop := ∃ K > (0:ℝ), ∀ᶠ S : ℝ in atTop, ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 ∧
  (log S)^(3/4:ℝ) ≤ log S/log (log S)*exp (-(log (log S))^z) ∧
  (log (log S))^(4-4*z) ≤ K

lemma minimal_family {n k : ℕ}
    (bad : ¬ ∃ p : Fin k → ℕ, Function.Injective p ∧ ∀ i, p i ∈ (n+i.val+1).primeFactors) :
    ∃ J : Finset (Fin k), let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
      P.card < J.card ∧ ∀ p ∈ P, p < k := by
  classical
  let F (i : Fin k) := (n+i.val+1).primeFactors
  have hh : ¬ ∀ s : Finset (Fin k), s.card ≤ (s.biUnion F).card :=
    fun h => bad ((all_card_le_biUnion_card_iff_exists_injective F).mp h)
  push_neg at hh
  let fam := univ.filter fun s : Finset (Fin k) => (s.biUnion F).card < s.card
  have non : fam.Nonempty := by
    obtain ⟨s,hs⟩ := hh
    exact ⟨s,mem_filter.mpr ⟨mem_univ _,hs⟩⟩
  obtain ⟨J,hJ,least⟩ := exists_min_image fam card non
  have defic : (J.biUnion F).card < J.card := (mem_filter.mp hJ).2
  refine ⟨J,defic,?_⟩
  intro p hp
  change p ∈ J.biUnion F at hp
  obtain ⟨i,hi,hpi⟩ := mem_biUnion.mp hp
  by_contra! large
  have unique (j : Fin k) (h : p ∈ F j) : i=j := by
    have di : p ∣ n+i.val+1 := Nat.dvd_of_mem_primeFactors hpi
    have dj : p ∣ n+j.val+1 := Nat.dvd_of_mem_primeFactors h
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with hlt|he|hgt
    · have d : p ∣ j.val-i.val := by convert Nat.dvd_sub dj di using 1 <;> omega
      have := Nat.le_of_dvd (show 0 < (j.val-i.val : ℕ) by omega) d
      omega
    · exact he
    · have d : p ∣ i.val-j.val := by convert Nat.dvd_sub di dj using 1 <;> omega
      have := Nat.le_of_dvd (show 0 < (i.val-j.val : ℕ) by omega) d
      omega
  let J' := J.erase i
  have sub : J'.biUnion F ⊆ (J.biUnion F).erase p := by
    intro q hq
    obtain ⟨j,hj,hq⟩ := mem_biUnion.mp hq
    obtain ⟨ne,jm⟩ := mem_erase.mp hj
    exact mem_erase.mpr ⟨fun e => ne ((unique j (e ▸ hq)).symm),mem_biUnion.mpr ⟨j,jm,hq⟩⟩
  have cl := card_le_card sub
  have pin : p ∈ J.biUnion F := mem_biUnion.mpr ⟨i,hi,hpi⟩
  rw [card_erase_of_mem pin] at cl
  have cj : J'.card = J.card-1 := card_erase_of_mem hi
  have jpos := card_pos.mpr (show J.Nonempty from ⟨i,hi⟩)
  have ppos := card_pos.mpr (show (J.biUnion F).Nonempty from ⟨p,pin⟩)
  have sm : J' ∈ fam := mem_filter.mpr ⟨mem_univ _,by omega⟩
  have := least J' sm
  omega

theorem main : H1 → H2 → H3 → type_of% @Erdos375.erdos_375.variants.log := by
  classical
  intro extract lower adjust
  obtain ⟨D,hd,hl⟩ := lower
  obtain ⟨K,hk,hadj⟩ := adjust
  obtain ⟨S₀,hS⟩ := eventually_atTop.mp (hadj.and (eventually_gt_atTop (27:ℝ)))
  let b := 1/(2*D*K)
  have bp : 0 < b := by dsimp [b]; positivity
  obtain ⟨c,hc,hex⟩ := extract b bp S₀
  let w := fun n : ℕ => (log n/log (log n))^3
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hex.and (eventually_ge_atTop (2:ℕ)))
  let B := 1 + ∑ i ∈ range N, |w i|
  have bge : 1 ≤ B := by dsimp [B]; linarith [sum_nonneg (s := range N) (fun i _ => abs_nonneg (w i))]
  have bpos : 0 < B := by linarith
  refine ⟨min c (1/B),lt_min hc (by positivity),?_⟩
  intro n k height comp
  change (k:ℝ) < min c (1/B)*w n at height
  have wpos : 0 < w n := by
    by_contra! hn
    have := mul_nonpos_of_nonneg_of_nonpos (le_min hc.le (by positivity : (0:ℝ) ≤ 1/B)) hn
    linarith [Nat.cast_nonneg (α := ℝ) k]
  by_cases early : n < N
  · have term := single_le_sum (f := fun i : ℕ => |w i|) (fun i _ => abs_nonneg (w i)) (mem_range.mpr early)
    have wn : w n < B := by dsimp [B]; linarith [le_abs_self (w n)]
    have sml := mul_le_mul_of_nonneg_right (min_le_right c (1/B)) wpos.le
    have kk : (k:ℝ) < 1 := by
      calc
        _ < _ := height
        _ ≤ _ := sml
        _ < 1 := by rw [one_div_mul_eq_div,div_lt_one bpos]; exact wn
    have klt : k < 1 := by exact_mod_cast kk
    have : k=0 := by omega
    subst k
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨huse,hn⟩ := hN n (Nat.le_of_not_gt early)
  have hsize := height.trans_le (mul_le_mul_of_nonneg_right (min_le_left c _) wpos.le)
  suffices h : ∃ p : Fin k → ℕ, Function.Injective p ∧ ∀ i, p i ∈ (n+i.val+1).primeFactors by
    obtain ⟨p,inj,h⟩ := h
    exact ⟨p,inj,fun i => ⟨Nat.prime_of_mem_primeFactors (h i),Nat.dvd_of_mem_primeFactors (h i)⟩⟩
  by_contra bad
  obtain ⟨J,defic,small⟩ := minimal_family bad
  obtain ⟨S,u,v,m,Sge,Su,up,vp,uh,vh,ml,mu,lv,Lp,Lu⟩ := huse k hsize J defic small
  obtain ⟨⟨z,z0,z1,lim,weight⟩,Sbig⟩ := hS S Sge
  have lp := log_pos (show 1 < S by linarith)
  have nn : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have low := hl S Sbig z z0 z1 u v m up vp uh vh ml mu (lv.trans lim) Lp
  have contra : (n:ℝ)^(-(1/2:ℝ)) ≤ exp (-D*log S*(log (log S))^(4-4*z)) := by
    calc
      _ = ((n:ℝ)^b)^(-(D*K)) := by rw [← rpow_mul nn.le]; congr 1; dsimp [b]; field_simp
      _ ≤ S^(-(D*K)) := rpow_le_rpow_of_nonpos (by linarith) Su (neg_nonpos.mpr (mul_nonneg hd.le hk.le))
      _ ≤ _ := by
        rw [rpow_def_of_pos (by linarith : 0 < S),exp_le_exp]
        nlinarith [mul_nonneg (mul_nonneg hd.le lp.le) (sub_nonneg.mpr weight)]
  exact (not_le_of_gt Lu) (contra.trans low)

end OMA.R_Erdos375_erdos_375_variants_log_R1

/-! Ramachandra, Shorey and Tijdeman (1975), section 2. The first application
of their approximation argument either supplies the logarithmic form or
forces a large family. Removing one maximal prime-power factor for each
prime leaves cofactors whose product divides the factorial. At the cubic
scale this forces many elements with exactly one assigned prime. -/
namespace OMA.R_Erdos375_erdos_375_variants_log_R1_H1_R1
open Filter Finset Real

-- The finite factorial bound after assigning each prime to one position
-- where its valuation is maximal. A counts unassigned positions, B the
-- positions with exactly one assigned prime.
def H1 : Prop := ∀ n k : ℕ, ∀ J : Finset (Fin k),
  let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
  P.card < J.card → (∀ p ∈ P, p < k) →
  ∃ (a : ℕ) (B : Finset (Fin k)) (p e u : Fin k → ℕ), B ⊆ J ∧
    J.card ≤ 2*a+B.card ∧ (n+1)^a ≤ k.factorial ∧
    (∏ i ∈ B, u i) ≤ k.factorial ∧ Set.InjOn p B ∧
    ∀ i ∈ B, (p i).Prime ∧ p i < k ∧ 0 < u i ∧ n+i.val+1 = u i*(p i)^(e i)

-- First-stage extraction from a small obstruction (the proof of Lemma 6).
def H2 : Prop := ∀ b : ℝ, 0 < b → ∀ S₀ : ℝ, ∃ δ > (0:ℝ), ∃ c > (0:ℝ),
  ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k:ℝ) < c*(log n/log (log n))^3 →
  ∀ J : Finset (Fin k),
  let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
  P.card < J.card → (∀ p ∈ P, p < k) →
  δ*(log n/log (log n))^2 ≤ J.card ∨ ∃ (S : ℝ) (u v : ℚ) (m : ℤ), S₀ ≤ S ∧ S ≤ (n:ℝ)^b ∧ 0 < u ∧ 0 < v ∧
    ((u.num.natAbs+u.den:ℕ):ℝ) ≤ (log S)^16 ∧ ((v.num.natAbs+v.den:ℕ):ℝ) ≤ S ∧
    2*log S/log (log S) ≤ |(m:ℝ)| ∧ |(m:ℝ)| ≤ (log S)^16 ∧
    |log (v:ℝ)| ≤ (log S)^(3/4:ℝ) ∧
    0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧ |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ))

-- Second-stage extraction (the close cofactors and close exponents on
-- pages 116–118). This statement concerns individual factorizations.
def H3 : Prop := ∀ b : ℝ, 0 < b → ∀ S₀ : ℝ, ∀ δ > (0:ℝ), ∃ c > (0:ℝ),
  ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k:ℝ) < c*(log n/log (log n))^3 →
  ∀ (B : Finset (Fin k)) (p e u : Fin k → ℕ),
    δ*(log n/log (log n))^2 ≤ B.card → (∏ i ∈ B, u i) ≤ k.factorial →
    Set.InjOn p B →
    (∀ i ∈ B, (p i).Prime ∧ p i < k ∧ 0 < u i ∧ n+i.val+1 = u i*(p i)^(e i)) →
    ∃ (S : ℝ) (u v : ℚ) (m : ℤ), S₀ ≤ S ∧ S ≤ (n:ℝ)^b ∧ 0 < u ∧ 0 < v ∧
    ((u.num.natAbs+u.den:ℕ):ℝ) ≤ (log S)^16 ∧ ((v.num.natAbs+v.den:ℕ):ℝ) ≤ S ∧
    2*log S/log (log S) ≤ |(m:ℝ)| ∧ |(m:ℝ)| ≤ (log S)^16 ∧
    |log (v:ℝ)| ≤ (log S)^(3/4:ℝ) ∧
    0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧ |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ))

theorem main : H1 → H2 → H3 → OMA.R_Erdos375_erdos_375_variants_log_R1.H1 := by
  intro extraction small large b hb S₀
  obtain ⟨δ,hδ,c₁,hc₁,hs⟩ := small b hb S₀
  obtain ⟨c₂,hc₂,hl⟩ := large b hb S₀ (δ/2) (by positivity)
  let c := min (min c₁ c₂) (min 1 (δ/12))
  have hc : 0<c := by dsimp [c]; positivity
  have hc1 : c≤c₁ := (min_le_left ..).trans (min_le_left ..)
  have hc2 : c≤c₂ := (min_le_left ..).trans (min_le_right ..)
  have hc3 : c≤1 := (min_le_right ..).trans (min_le_left ..)
  have hcd : c≤δ/12 := (min_le_right ..).trans (min_le_right ..)
  refine ⟨c,hc,?_⟩
  have tlog : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have tll : Tendsto (fun n : ℕ => log (log (n:ℝ))) atTop atTop :=
    tendsto_log_atTop.comp tlog
  filter_upwards [hs,hl,tlog.eventually_ge_atTop 1,tll.eventually_ge_atTop 1,
    eventually_ge_atTop 2] with n hs hl hlog hll hn
  intro k hk J P hJ hP
  let L := log (n:ℝ)
  let l := log L
  let Q := L/l
  change 1≤L at hlog
  change 1≤l at hll
  change (k:ℝ)<c*Q^3 at hk
  have lp : 0<l := by linarith
  have Lp : 0<L := by linarith
  have qp : 0<Q := div_pos Lp lp
  have ql : Q≤L := (div_le_iff₀ lp).mpr (by nlinarith only [mul_nonneg Lp.le (sub_nonneg.mpr hll)])
  have kpos : 0<k := by
    have : J.card ≤ k := (card_le_card (subset_univ J)).trans_eq (by simp)
    omega
  rcases hs k (hk.trans_le (mul_le_mul_of_nonneg_right hc1 (pow_nonneg qp.le _))) J hJ hP with hbig|done
  · obtain ⟨a,B,p,e,u,_,hcard,hpow,hfac,hinj,hsingle⟩ := extraction n k J hJ hP
    change δ*Q^2 ≤ _ at hbig
    have hkc : (k:ℝ) ≤ L^3 := calc
      _ ≤ c*Q^3 := hk.le
      _ ≤ 1*L^3 := mul_le_mul hc3 (pow_le_pow_left₀ qp.le ql 3) (pow_nonneg qp.le _) zero_le_one
      _ = _ := one_mul _
    have hkl : log (k:ℝ) ≤ 3*l := by
      have v := log_le_log (by exact_mod_cast kpos) hkc
      rwa [Real.log_pow] at v
    have hnZ : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
    have kn : (n:ℝ)^a ≤ (k:ℝ)^k := by
      exact_mod_cast (Nat.pow_le_pow_left (Nat.le_succ n) a).trans (hpow.trans k.factorial_le_pow)
    have lg := log_le_log (pow_pos hnZ a) kn
    rw [Real.log_pow,Real.log_pow] at lg
    change (a:ℝ)*L ≤ (k:ℝ)*log k at lg
    have ha : (a:ℝ)*L ≤ 3*c*Q^2*L := calc
      _ ≤ (k:ℝ)*log k := lg
      _ ≤ (c*Q^3)*(3*l) := mul_le_mul hk.le hkl (log_natCast_nonneg _) (by positivity)
      _ = _ := by dsimp [Q]; field_simp <;> ring
    have ha' : (a:ℝ) ≤ 3*c*Q^2 := le_of_mul_le_mul_right ha Lp
    have hB : δ/2*Q^2 ≤ (B.card:ℝ) := by
      have hcard' : (J.card:ℝ) ≤ 2*(a:ℝ)+(B.card:ℝ) := by exact_mod_cast hcard
      nlinarith only [hbig,hcard',ha',mul_le_mul_of_nonneg_right hcd (sq_nonneg Q)]
    exact hl k (hk.trans_le (mul_le_mul_of_nonneg_right hc2 (pow_nonneg qp.le _))) B p e u hB hfac hinj hsingle
  · exact done

end OMA.R_Erdos375_erdos_375_variants_log_R1_H1_R1

section

/-! For each prime, assign a row where its valuation is largest. The powers
at every other row divide its distance to that row. Distinct prime powers
are coprime, so their full product divides the factorial. -/
open Finset

private lemma product_dist {k : ℕ} (j:Fin k) (S:Finset (Fin k)) :
    (∏ i∈S, (if i.val<j.val then j.val-i.val else if j.val < i.val then i.val-j.val else 1)) ∣ k.factorial := by
  classical
  let L := S.filter (fun i => i.val<j.val)
  let R := S.filter (fun i => j.val < i.val)
  have injL : Set.InjOn (fun i:Fin k => j.val-i.val) ↑L := by
    intro i hi i' hi' e
    have h := (mem_filter.mp hi).2
    have h' := (mem_filter.mp hi').2
    apply Fin.ext
    dsimp at e
    omega
  have injR : Set.InjOn (fun i:Fin k => i.val-j.val) ↑R := by
    intro i hi i' hi' e
    have h := (mem_filter.mp hi).2
    have h' := (mem_filter.mp hi').2
    apply Fin.ext
    dsimp at e
    omega
  have lsub : L.image (fun i => j.val-i.val) ⊆ Icc 1 j.val := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have := (mem_filter.mp hi).2
    exact mem_Icc.mpr ⟨by omega,Nat.sub_le ..⟩
  have rsub : R.image (fun i => i.val-j.val) ⊆ Icc 1 (k-j.val) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have := (mem_filter.mp hi).2
    have := i.isLt
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have left := prod_dvd_prod_of_subset _ _ id lsub
  have right := prod_dvd_prod_of_subset _ _ id rsub
  have prodI (n:ℕ) : ∏ i∈Icc 1 n,id i=n.factorial := by
    have e : Icc 1 n=Ico 1 (n+1) := by ext i; simp
    rw [e]; exact prod_Ico_id_eq_factorial n
  rw [prod_image injL,prodI] at left
  rw [prod_image injR,prodI] at right
  have eq : (∏ i∈S, (if i.val<j.val then j.val-i.val else if j.val < i.val then i.val-j.val else 1)) =
       (∏ i∈L, (j.val-i.val))*(∏ i∈R,(i.val-j.val)) := by
    dsimp only [L,R]
    rw [prod_filter,prod_filter,←prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    by_cases h:i.val<j.val <;> simp [h,show i.val<j.val → ¬j.val < i.val from fun a => a.asymm]
  rw [eq]
  exact (Nat.mul_dvd_mul left right).trans (Nat.factorial_mul_factorial_dvd_factorial j.isLt.le)

private lemma off_max {n k p:ℕ} (_hp:p.Prime) (J:Finset (Fin k)) (j:Fin k)
    (maxi:∀ i∈J, (n+i.val+1).factorization p ≤ (n+j.val+1).factorization p) :
    (∏ i∈J, p^(if i=j then 0 else (n+i.val+1).factorization p)) ∣ k.factorial := by
  apply dvd_trans _ (product_dist j J)
  apply prod_dvd_prod_of_dvd
  intro i hi
  by_cases eq:i=j
  · simp [eq]
  rw [if_neg eq]
  have dl := Nat.ordProj_dvd (n+i.val+1) p
  have dr : p^(n+i.val+1).factorization p ∣ n+j.val+1 :=
    (pow_dvd_pow _ (maxi i hi)).trans (Nat.ordProj_dvd _ _)
  by_cases lt:i.val<j.val
  · rw [if_pos lt]
    have h := Nat.dvd_sub dr dl
    rwa [show n+j.val+1-(n+i.val+1)=j.val-i.val by omega] at h
  · have gt : j.val < i.val := by have ne : i.val≠j.val := fun h => eq (Fin.ext h); omega
    rw [if_neg lt,if_pos gt]
    have h := Nat.dvd_sub dl dr
    rwa [show n+i.val+1-(n+j.val+1)=i.val-j.val by omega] at h

theorem OMA.GrimmAssembly.extraction : OMA.R_Erdos375_erdos_375_variants_log_R1_H1_R1.H1 := by
  classical
  intro n k J P deficit small
  have jne : J.Nonempty := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) deficit)
  let w (i:Fin k) := n+i.val+1
  have wp (i:Fin k) : 0<w i := Nat.succ_pos _
  let e (i:Fin k) (p:ℕ) := (w i).factorization p
  have ex (p:ℕ) := J.exists_max_image (fun i => e i p) jne
  choose f fj mx using ex
  let F (i:Fin k) := P.filter (fun p => f p=i)
  let Z := J.filter (fun i => (F i).card=0)
  let B := J.filter (fun i => (F i).card=1)
  have pprime (p:ℕ) (hp:p∈P) : p.Prime := by
    obtain ⟨i,_,h⟩ := mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors h
  have psum : ∑ i∈J,(F i).card = P.card := (card_eq_sum_card_fiberwise (f:=f) (s:=P) (t:=J) (fun p _ => fj p)).symm
  have count : J.card ≤ 2*Z.card+B.card := by
    have point (i:Fin k) : 2≤(F i).card+2*(if (F i).card=0 then 1 else 0)+(if (F i).card=1 then 1 else 0) := by split_ifs <;> omega
    have h := sum_le_sum (s:=J) (fun i _ => point i)
    rw [sum_add_distrib,sum_add_distrib,←mul_sum,psum] at h
    simp only [sum_const,nsmul_eq_mul] at h
    have z : ∑ i∈J,(if (F i).card=0 then 1 else 0) = Z.card := (card_filter ..).symm
    have b : ∑ i∈J,(if (F i).card=1 then 1 else 0) = B.card := (card_filter ..).symm
    rw [z,b] at h
    change J.card*2 ≤ P.card+2*Z.card+B.card at h
    omega
  let v (i:Fin k) (p:ℕ) := if i=f p then 0 else e i p
  let u (i:Fin k) := ∏ p∈P,p^(v i p)
  have u0 (i:Fin k) : 0<u i := prod_pos fun p hp => pow_pos (pprime p hp).pos _
  have all : ∏ i∈J,u i ∣ k.factorial := by
    change (∏ i∈J,∏ p∈P,p^(v i p)) ∣ _
    rw [prod_comm]
    apply prod_dvd_of_isRelPrime
    · intro p hp q hq pq
      apply Nat.coprime_iff_isRelPrime.mp
      apply Nat.Coprime.prod_left
      intro i _
      apply Nat.Coprime.prod_right
      intro j _
      exact (((pprime p hp).coprime_iff_not_dvd.mpr (fun h => pq (((Nat.dvd_prime (pprime q hq)).mp h).resolve_left (pprime p hp).ne_one))).pow_left _).pow_right _
    · intro p hp
      exact off_max (pprime p hp) J (f p) (mx p)
  have bound (T:Finset (Fin k)) (hT:T⊆J) : ∏ i∈T,u i ≤ k.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos k) ((prod_dvd_prod_of_subset _ _ u hT).trans all)
  let remn (i:Fin k) := ∏ p∈P,p^(if i=f p then e i p else 0)
  have split (i:Fin k) (hi:i∈J) : w i = u i*remn i := by
    have sub : (w i).primeFactors⊆P := fun p hp => mem_biUnion.mpr ⟨i,hi,hp⟩
    have prod : ∏ p∈P, p^(e i p) = w i := by
      apply Eq.trans _ (Nat.prod_primeFactors_pow_factorization (wp i).ne').symm
      change ∏ p∈P, p^(e i p) = ∏ p∈(w i).primeFactors,p^(e i p)
      symm
      apply prod_subset sub
      intro p _ hp
      have z : (w i).factorization p=0 := by
        simpa only [←Finsupp.notMem_support_iff,Nat.support_factorization] using hp
      simp [e,z]
    rw [←prod]
    dsimp only [u,remn]
    rw [←prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    by_cases eq:i=f p <;> simp [v,eq]
  have zero (i:Fin k) (hi:i∈Z) : n+1≤u i := by
    obtain ⟨ij,empty⟩ := mem_filter.mp hi
    have no (p:ℕ) (hp:p∈P) : i≠f p := by
      intro eq
      have h : p∈F i := mem_filter.mpr ⟨hp,eq.symm⟩
      rw [card_eq_zero.mp empty] at h
      exact notMem_empty _ h
    have r : remn i=1 := prod_eq_one (fun p hp => by simp [no p hp])
    have e := split i ij
    rw [r,mul_one] at e
    dsimp [w] at e
    omega
  have get (i:Fin k) (hi:i∈B) : ∃ q:ℕ,F i={q} := card_eq_one.mp (mem_filter.mp hi).2
  let p (i:Fin k) := if h:i∈B then (get i h).choose else 0
  have singleton (i:Fin k) (hi:i∈B) : F i={p i} := by simpa [p,hi] using (get i hi).choose_spec
  have member (i:Fin k) (hi:i∈B) : p i∈P ∧ f (p i)=i := by
    have h : p i∈F i := by rw [singleton i hi]; simp
    exact mem_filter.mp h
  refine ⟨Z.card,B,p,fun i => e i (p i),u,filter_subset ..,count,?_,bound B (filter_subset ..),?_,?_⟩
  · calc (n+1)^Z.card = ∏ i∈Z,(n+1) := (prod_const _).symm
         _ ≤ ∏ i∈Z,u i := prod_le_prod' (fun i hi => zero i hi)
         _ ≤ _ := bound Z (filter_subset ..)
  · intro i hi j hj eq
    exact (member i hi).2.symm.trans ((congrArg f eq).trans (member j hj).2)
  · intro i hi
    refine ⟨pprime _ (member i hi).1,small _ (member i hi).1,u0 i,?_⟩
    have r : remn i=(p i)^(e i (p i)) := by
      dsimp [remn]
      rw [prod_eq_single_of_mem (p i) (member i hi).1 (fun q hq ne => ?_),if_pos (member i hi).2.symm]
      have no : i≠f q := by
        intro eq
        have h : q∈F i := mem_filter.mpr ⟨hq,eq.symm⟩
        rw [singleton i hi] at h
        exact ne (mem_singleton.mp h)
      simp [no]
    exact (split i (mem_filter.mp hi).1).trans (congrArg (u i * ·) r)

end

section

/-! The first-stage extraction of Ramachandra, Shorey and Tijdeman, Section 2.
For a small Hall obstruction choose h around d log(n)/(1000 log log n).
A common multiple of its cofactors and the pairwise gcd bounds show that
fewer than h cofactors have log larger than d log(n)/16. The unassigned
rows all have large cofactors, so at least a quarter of log(n)/log log(n)
rows have a unique assigned prime and a small cofactor. -/
namespace OMA.GrimmSmall
open Finset Real Filter
open scoped Topology

-- Assign primes to maximum-valuation rows. All retained cofactors divide
-- a common integer at most k to the power card J; the gcd of any two of
-- them divides a nonzero difference of row indices and hence is at most k.
private def Structural : Prop := ∀ n k : ℕ, ∀ J : Finset (Fin k),
  let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
  P.card<J.card → (∀ p∈P,p<k) →
  ∃ (Z B : Finset (Fin k)) (p e u : Fin k → ℕ),
    Z⊆J ∧ B⊆J ∧ J.card≤2*Z.card+B.card ∧ n+1≤k^J.card ∧
    (∀ i∈J,0<u i) ∧ (∀ i∈Z,n+1≤u i) ∧
    (∀ W⊆J, ∏ i∈W,u i ≤ k^(J.card+W.card^2)) ∧
    ∀ i∈B,(p i).Prime ∧ p i<k ∧ n+i.val+1=u i*(p i)^(e i)

-- Rounding prime exponents down to a common bin and absorbing the
-- residual powers in the small cofactors gives a pair of near logarithms.
private def Rounded : Prop := ∀ b : ℝ, 0<b → ∀ S₀ : ℝ, ∃ d:ℝ, 0<d ∧ d≤1/100 ∧
  ∀ᶠ n : ℕ in atTop, ∀ k:ℕ, (k:ℝ)<(log n/log (log n))^3 →
  ∀ (B:Finset (Fin k)) (p e u:Fin k→ℕ),
    (log n/log (log n))/4≤B.card →
    (∀ i∈B,(p i).Prime ∧ p i<k ∧ 0<u i ∧ log (u i:ℝ)≤d*log n/16 ∧ n+i.val+1=u i*(p i)^(e i)) →
    ∃ (S:ℝ) (x y:ℚ) (m:ℤ), S₀≤S ∧ S≤(n:ℝ)^b ∧ 0<x ∧ 0<y ∧
    ((x.num.natAbs+x.den:ℕ):ℝ)≤(log S)^16 ∧ ((y.num.natAbs+y.den:ℕ):ℝ)≤S ∧
    2*log S/log (log S)≤|(m:ℝ)| ∧ |(m:ℝ)|≤(log S)^16 ∧
    |log (y:ℝ)|≤(log S)^(3/4:ℝ) ∧ 0 < |(m:ℝ)*log (x:ℝ)-log (y:ℝ)| ∧
    |(m:ℝ)*log (x:ℝ)-log (y:ℝ)| < (n:ℝ)^(-(1/2:ℝ))

private theorem main : Structural → Rounded → OMA.R_Erdos375_erdos_375_variants_log_R1_H1_R1.H2 := by
  classical
  intro structural near b hb S₀
  obtain ⟨d,dp,dc,near⟩ := near b hb S₀
  let δ := d^2/100000000
  refine ⟨δ,by dsimp [δ]; positivity,1,one_pos,?_⟩
  have tN : Tendsto (fun n:ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have tL := tendsto_log_atTop.comp tN
  have tl := tendsto_log_atTop.comp tL
  have smalllog := isLittleO_log_id_atTop.bound (show 0<d/2000 by positivity)
  filter_upwards [near,eventually_ge_atTop 2,tL.eventually_ge_atTop 1,tl.eventually_ge_atTop 1,
    tL.eventually smalllog] with n near hn hL hl raw
  intro k hk J P deficit small
  let L := log (n:ℝ)
  let l := log L
  let Q := L/l
  change 1≤L at hL
  change 1≤l at hl
  change ‖l‖≤d/2000*‖L‖ at raw
  rw [Real.norm_of_nonneg (by linarith),Real.norm_of_nonneg (by linarith)] at raw
  have hQ : 2000/d≤Q := by
    apply (le_div_iff₀ (show 0<l by linarith)).mpr
    rw [div_mul_eq_mul_div,div_le_iff₀ dp]
    linarith
  simp only [one_mul] at hk
  change (k:ℝ)<Q^3 at hk
  by_cases big:δ*Q^2≤J.card
  · exact Or.inl big
  right
  obtain ⟨Z,B,p,e,u,zJ,bJ,count,nk,up,zero,products,rows⟩ := structural n k J deficit small
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have kp : 0<k := by
    obtain ⟨i,_⟩ := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) deficit)
    exact Nat.zero_lt_of_lt i.isLt
  have Lp : 0<L := by linarith
  have lp : 0<l := by linarith
  have qp : 0<Q := div_pos Lp lp
  have qrel : Q*l=L := div_mul_cancel₀ _ lp.ne'
  have qL : Q≤L := (div_le_iff₀ lp).mpr (by nlinarith only [mul_nonneg Lp.le (sub_nonneg.mpr hl)])
  have kL := hk.le.trans (pow_le_pow_left₀ qp.le qL 3)
  have lk : log (k:ℝ)≤3*l := by
    have h := log_le_log (by exact_mod_cast kp) kL
    rwa [log_pow] at h
  have jlow : Q≤3*(J.card:ℝ) := by
    have lg := log_le_log np (by exact_mod_cast (Nat.le_succ n).trans nk : (n:ℝ)≤(k:ℝ)^J.card)
    rw [log_pow] at lg
    apply (div_le_iff₀ lp).mpr
    linarith only [lg,mul_le_mul_of_nonneg_left lk (Nat.cast_nonneg J.card (α:=ℝ))]
  let T := d*L/16
  let h := ⌊d*Q/1000⌋₊
  have y2 : 2≤d*Q/1000 := by have ht := (div_le_iff₀ dp).mp hQ; linarith
  have hup : (h:ℝ)≤d*Q/1000 := Nat.floor_le (by linarith)
  have hlo : d*Q/2000≤(h:ℝ) := by
    have h' := Nat.lt_floor_add_one (d*Q/1000)
    change d*Q/1000<(h:ℝ)+1 at h'
    linarith
  let D := J.filter (fun i => T<log (u i:ℝ))
  have few : D.card<h := by
    by_contra! many
    obtain ⟨W,wD,wc⟩ := exists_subset_card_eq many
    have wJ := wD.trans (show D ⊆ J from filter_subset ..)
    have lo : (h:ℝ)*T ≤ ∑ i∈W, log (u i:ℝ) := by
      rw [←wc,←nsmul_eq_mul,←sum_const]
      exact sum_le_sum fun i hi => (mem_filter.mp (wD hi)).2.le
    have lg := log_le_log (prod_pos (s:=W) (fun i hi => show 0<(u i:ℝ) by exact_mod_cast up i (wJ hi)))
      (show (∏ i∈W,(u i:ℝ))≤(k:ℝ)^(J.card+W.card^2) by exact_mod_cast products W wJ)
    rw [log_prod (fun i hi => by exact_mod_cast (up i (wJ hi)).ne'),log_pow,wc] at lg
    push_cast at lg
    have cost := lo.trans (lg.trans (mul_le_mul_of_nonneg_left lk (by positivity)))
    have jless : (J.card:ℝ)<δ*Q^2 := lt_of_not_ge big
    have h2 := pow_le_pow_left₀ (Nat.cast_nonneg h (α:=ℝ)) hup 2
    have upper := mul_le_mul_of_nonneg_right (add_le_add jless.le h2) (show 0≤3*l by positivity)
    have left := mul_le_mul_of_nonneg_right hlo (show 0≤T by dsimp [T]; positivity)
    have bad := left.trans (cost.trans upper)
    dsimp only [T,δ] at bad
    rw [←qrel] at bad
    nlinarith only [bad,mul_pos (mul_pos (sq_pos_of_pos dp) (sq_pos_of_pos qp)) lp]
  have zd : Z⊆D := by
    intro i hi
    have lg := log_le_log np (by exact_mod_cast (Nat.le_succ n).trans (zero i hi) : (n:ℝ)≤u i)
    have tl : T<L := by dsimp [T]; nlinarith only [Lp,mul_le_mul_of_nonneg_right dc Lp.le]
    exact mem_filter.mpr ⟨zJ hi,tl.trans_le lg⟩
  let G := B \ D
  have gc : B.card≤G.card+D.card := by
    have h := card_le_card (s:=B) (t:=G∪D) (by intro i hi; by_cases h:i∈D; exact mem_union_right _ h; exact mem_union_left _ (mem_sdiff.mpr ⟨hi,h⟩))
    exact h.trans (card_union_le ..)
  have he : J.card≤G.card+3*h := by have := card_le_card zd; omega
  have he' : (J.card:ℝ)≤(G.card:ℝ)+3*h := by exact_mod_cast he
  have enough : Q/4≤(G.card:ℝ) := by nlinarith only [jlow,he',hup,mul_le_mul_of_nonneg_right dc qp.le,qp.le]
  refine near k hk G p e u enough ?_
  intro i hi
  obtain ⟨ib,id⟩ := mem_sdiff.mp hi
  have data := rows i ib
  refine ⟨data.1,data.2.1,up i (bJ ib),le_of_not_gt (fun h => id (mem_filter.mpr ⟨bJ ib,h⟩)),data.2.2⟩

private lemma small_prod {α:Type*} [DecidableEq α] {w:α→ℕ} {k:ℕ} (S:Finset α)
    (pos:∀ i∈S, 0<w i) (kp:0<k)
    (cross:∀ i∈S, ∀ j∈S, i≠j → (w i).gcd (w j)≤k) :
    ∏ i∈S,w i ≤ S.lcm w * k^(S.card^2) := by
  classical
  have gcdprod (x:ℕ) (U:Finset α) : x.gcd (∏ i∈U,w i) ∣ ∏ i∈U,x.gcd (w i) := by
    induction U using Finset.induction_on with
    | empty => simp
    | insert i U hi ih =>
      rw [prod_insert hi,prod_insert hi]
      exact (gcd_mul_dvd_mul_gcd x (w i) _).trans (Nat.mul_dvd_mul_left _ ih)
  induction S using Finset.induction_on with
  | empty => simp
  | insert a V hi ih =>
    have vp (i:α) (h:i∈V) := pos i (mem_insert_of_mem h)
    have va := pos a (mem_insert_self ..)
    have ihprod := ih vp (fun i h j h' ne => cross i (mem_insert_of_mem h) j (mem_insert_of_mem h') ne)
    have gd : (w a).gcd (V.lcm w) ∣ ∏ i∈V,(w a).gcd (w i) :=
      (Nat.gcd_dvd_gcd_of_dvd_right _ (V.lcm_dvd_prod w)).trans (gcdprod _ _)
    have pg : 0<∏ i∈V,(w a).gcd (w i) := prod_pos (fun i _ => Nat.gcd_pos_of_pos_left _ va)
    have gb : (w a).gcd (V.lcm w) ≤ k^V.card := (Nat.le_of_dvd pg gd).trans (by
      rw [←prod_const (s:=V) k]
      exact prod_le_prod' fun i h => cross a (mem_insert_self ..) i (mem_insert_of_mem h) (fun e => hi (e ▸ h)))
    rw [prod_insert hi,lcm_insert,card_insert_of_notMem hi]
    calc (w a)*(∏ i∈V,w i) ≤ (w a)*(V.lcm w*k^(V.card^2)) := Nat.mul_le_mul_left _ ihprod
         _ = (w a).lcm (V.lcm w) * ((w a).gcd (V.lcm w) * k^(V.card^2)) := by
            calc _ = ((w a)*(V.lcm w))*k^(V.card^2) := by ring
                 _ = ((w a).gcd (V.lcm w)*(w a).lcm (V.lcm w))*k^(V.card^2) := by rw [Nat.gcd_mul_lcm]
                 _ = _ := by ring
         _ ≤ (w a).lcm (V.lcm w) * (k^V.card*k^(V.card^2)) := by gcongr
         _ ≤ _ := by
            rw [←pow_add]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right kp (by nlinarith))

private theorem structural : Structural := by
  classical
  intro n k J P deficit small
  have jne : J.Nonempty := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) deficit)
  let w (i:Fin k) := n+i.val+1
  have wp (i:Fin k) : 0<w i := Nat.succ_pos _
  let e (i:Fin k) (p:ℕ) := (w i).factorization p
  have ex (p:ℕ) := J.exists_max_image (fun i => e i p) jne
  choose f fj mx using ex
  let F (i:Fin k) := P.filter (fun p => f p=i)
  let Z := J.filter (fun i => (F i).card=0)
  let B := J.filter (fun i => (F i).card=1)
  have pprime (p:ℕ) (hp:p∈P) : p.Prime := by
    obtain ⟨i,_,h⟩ := mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors h
  have psum : ∑ i∈J,(F i).card = P.card := (card_eq_sum_card_fiberwise (f:=f) (s:=P) (t:=J) (fun p _ => fj p)).symm
  have count : J.card ≤ 2*Z.card+B.card := by
    have point (i:Fin k) : 2≤(F i).card+2*(if (F i).card=0 then 1 else 0)+(if (F i).card=1 then 1 else 0) := by split_ifs <;> omega
    have h := sum_le_sum (s:=J) (fun i _ => point i)
    rw [sum_add_distrib,sum_add_distrib,←mul_sum,psum] at h
    simp only [sum_const,nsmul_eq_mul] at h
    have z : ∑ i∈J,(if (F i).card=0 then 1 else 0) = Z.card := (card_filter ..).symm
    have b : ∑ i∈J,(if (F i).card=1 then 1 else 0) = B.card := (card_filter ..).symm
    rw [z,b] at h
    change J.card*2 ≤ P.card+2*Z.card+B.card at h
    omega
  let v (i:Fin k) (p:ℕ) := if i=f p then 0 else e i p
  let u (i:Fin k) := ∏ p∈P,p^(v i p)
  have u0 (i:Fin k) : 0<u i := prod_pos fun p hp => pow_pos (pprime p hp).pos _
  let remn (i:Fin k) := ∏ p∈P,p^(if i=f p then e i p else 0)
  have split (i:Fin k) (hi:i∈J) : w i = u i*remn i := by
    have sub : (w i).primeFactors⊆P := fun p hp => mem_biUnion.mpr ⟨i,hi,hp⟩
    have prod : ∏ p∈P, p^(e i p) = w i := by
      apply Eq.trans _ (Nat.prod_primeFactors_pow_factorization (wp i).ne').symm
      change ∏ p∈P, p^(e i p) = ∏ p∈(w i).primeFactors,p^(e i p)
      symm
      apply prod_subset sub
      intro p _ hp
      have z : (w i).factorization p=0 := by
        simpa only [←Finsupp.notMem_support_iff,Nat.support_factorization] using hp
      simp [e,z]
    rw [←prod]
    dsimp only [u,remn]
    rw [←prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    by_cases eq:i=f p <;> simp [v,eq]
  have zero (i:Fin k) (hi:i∈Z) : n+1≤u i := by
    obtain ⟨ij,empty⟩ := mem_filter.mp hi
    have no (p:ℕ) (hp:p∈P) : i≠f p := by
      intro eq
      have h : p∈F i := mem_filter.mpr ⟨hp,eq.symm⟩
      rw [card_eq_zero.mp empty] at h
      exact notMem_empty _ h
    have r : remn i=1 := prod_eq_one (fun p hp => by simp [no p hp])
    have e := split i ij
    rw [r,mul_one] at e
    dsimp [w] at e
    omega
  have get (i:Fin k) (hi:i∈B) : ∃ q:ℕ,F i={q} := card_eq_one.mp (mem_filter.mp hi).2
  let p (i:Fin k) := if h:i∈B then (get i h).choose else 0
  have singleton (i:Fin k) (hi:i∈B) : F i={p i} := by simpa [p,hi] using (get i hi).choose_spec
  have member (i:Fin k) (hi:i∈B) : p i∈P ∧ f (p i)=i := by
    have h : p i∈F i := by rw [singleton i hi]; simp
    exact mem_filter.mp h
  have kp : 0<k := by obtain ⟨i,_⟩ := jne; exact Nat.zero_lt_of_lt i.isLt
  have vcap (i:Fin k) (ii:i∈J) (p:ℕ) (ph:p∈P) : p^(v i p)≤k := by
    by_cases eq:i=f p
    · simpa [v,eq] using (show 1≤k by omega)
    rw [show v i p=e i p by simp [v,eq]]
    have dw : p^(e i p)∣w i := Nat.ordProj_dvd _ _
    have dm : p^(e i p)∣w (f p) := (pow_dvd_pow _ (mx p i ii)).trans (Nat.ordProj_dvd _ _)
    have ne : i.val≠(f p).val := fun h => eq (Fin.ext h)
    rcases lt_or_gt_of_ne ne with h|h
    · have dif := Nat.dvd_sub dm dw
      have E : w (f p)-w i=(f p).val-i.val := by dsimp [w]; omega
      rw [E] at dif
      exact (Nat.le_of_dvd (by omega) dif).trans ((Nat.sub_le ..).trans (f p).isLt.le)
    · have dif := Nat.dvd_sub dw dm
      have E : w i-w (f p)=i.val-(f p).val := by dsimp [w]; omega
      rw [E] at dif
      exact (Nat.le_of_dvd (by omega) dif).trans ((Nat.sub_le ..).trans i.isLt.le)
  let A := ∏ q∈P,q^(J.sup (fun i => v i q))
  have cap : A≤k^J.card := by
    apply le_trans _ (Nat.pow_le_pow_right kp deficit.le)
    rw [←prod_const (s:=P) k]
    apply prod_le_prod'
    intro q hq
    obtain ⟨i,ii,eq⟩ := exists_mem_eq_sup J jne (fun i => v i q)
    rw [eq]
    exact vcap i ii q hq
  have ud (i:Fin k) (ii:i∈J) : u i∣A := by
    apply prod_dvd_prod_of_dvd
    intro q _
    exact pow_dvd_pow _ (le_sup (s:=J) (f:=fun i => v i q) ii)
  have Ap : 0<A := prod_pos fun q hq => pow_pos (pprime q hq).pos _
  have missing : ∃ i∈J,i∉P.image f := by
    by_contra! cover
    have h := (card_le_card cover).trans card_image_le
    omega
  obtain ⟨i,ij,absent⟩ := missing
  have iz : i∈Z := mem_filter.mpr ⟨ij,card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr (by
    intro q h
    exact absent (mem_image.mpr ⟨q,(mem_filter.mp h).1,(mem_filter.mp h).2⟩)))⟩
  have nk := (zero i iz).trans ((Nat.le_of_dvd Ap (ud i ij)).trans cap)
  have udiv (i:Fin k) (ii:i∈J) : u i ∣ w i := ⟨remn i,split i ii⟩
  have gcdcap (i:Fin k) (ii:i∈J) (j:Fin k) (jj:j∈J) (ij:i≠j) : (u i).gcd (u j)≤k := by
    let g := (u i).gcd (u j)
    have di : g∣w i := (Nat.gcd_dvd_left ..).trans (udiv i ii)
    have dj : g∣w j := (Nat.gcd_dvd_right ..).trans (udiv j jj)
    have ne : i.val≠j.val := fun h => ij (Fin.ext h)
    rcases lt_or_gt_of_ne ne with h|h
    · have dif := Nat.dvd_sub dj di
      have E : w j-w i=j.val-i.val := by dsimp [w]; omega
      rw [E] at dif
      exact (Nat.le_of_dvd (by omega) dif).trans ((Nat.sub_le ..).trans j.isLt.le)
    · have dif := Nat.dvd_sub di dj
      have E : w i-w j=i.val-j.val := by dsimp [w]; omega
      rw [E] at dif
      exact (Nat.le_of_dvd (by omega) dif).trans ((Nat.sub_le ..).trans i.isLt.le)
  refine ⟨Z,B,p,fun i => e i (p i),u,filter_subset ..,filter_subset ..,count,nk,fun i _ => u0 i,zero,?_,?_⟩
  · intro W wJ
    have h := small_prod W (fun i _ => u0 i) kp (fun i hi j hj ne => gcdcap i (wJ hi) j (wJ hj) ne)
    have lc := (Nat.le_of_dvd Ap (show W.lcm u∣A from lcm_dvd (fun j hj => ud j (wJ hj)))).trans cap
    rw [pow_add]
    exact h.trans (Nat.mul_le_mul_right _ lc)


  · intro i hi
    refine ⟨pprime _ (member i hi).1,small _ (member i hi).1,?_⟩
    have r : remn i=(p i)^(e i (p i)) := by
      dsimp [remn]
      rw [prod_eq_single_of_mem (p i) (member i hi).1 (fun q hq ne => ?_),if_pos (member i hi).2.symm]
      have no : i≠f q := by
        intro eq
        have h : q∈F i := mem_filter.mpr ⟨hq,eq.symm⟩
        rw [singleton i hi] at h
        exact ne (mem_singleton.mp h)
      simp [no]
    exact (split i (mem_filter.mp hi).1).trans (congrArg (u i * ·) r)


private lemma height_div {a b:ℕ} (ha:0<a) (hb:0<b) :
    (((a:ℚ)/b).num.natAbs+((a:ℚ)/b).den) ≤ a+b := by
  have bd : ((b:ℤ))≠0 := by exact_mod_cast hb.ne'
  have n := Rat.num_dvd (a:ℤ) bd
  have d := Rat.den_dvd (a:ℤ) (b:ℤ)
  rw [Rat.divInt_eq_div] at n d
  push_cast at n d
  have hn := Int.natAbs_dvd_natAbs.mpr n
  have hd := Int.natAbs_dvd_natAbs.mpr d
  simp only [Int.natAbs_natCast] at hn hd
  exact Nat.add_le_add (Nat.le_of_dvd ha hn) (Nat.le_of_dvd hb hd)

private lemma log_near {x y N K:ℝ} (np:0<N) (kx:0≤K) (hx:N≤x) (hy:N≤y)
    (xa:x≤N+K) (ya:y≤N+K) : |log x-log y| ≤ K/N := by
  have xp := np.trans_le hx
  have yp := np.trans_le hy
  have one (v w:ℝ) (vp:0<v) (wp:0<w) (h:N≤w) (up:v≤N+K) : log v-log w≤K/N := by
    rw [←log_div vp.ne' wp.ne']
    have b := log_le_sub_one_of_pos (div_pos vp wp)
    have h' : v/w ≤ (N+K)/N :=
      div_le_div₀ (by linarith) up np h
    have e : (N+K)/N = 1+K/N := by field_simp
    linarith only [b,h',e]
  exact abs_sub_le_iff.mpr ⟨one x y xp yp hy xa,one y x yp xp hx ya⟩

private lemma logpower (a R:ℝ) (ha:0<a) (hR:0<R) :
    ∀ᶠ x:ℝ in atTop, (log x)^8 ≤ a*x^R := by
  have h := (isLittleO_log_rpow_rpow_atTop 8 hR).bound ha
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with x hx h1
  simpa only [Real.rpow_natCast,Real.rpow_ofNat, Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (log_nonneg h1) _),
    abs_of_nonneg (rpow_nonneg (zero_le_one.trans h1) _)] using hx

private lemma rounded_pair {k:ℕ} (B:Finset (Fin k)) (p e u:Fin k→ℕ) (L l d:ℝ)
    (hL:1≤L) (hl:1≤l) (dp:0<d) (dc:d≤1/100)
    (size:L/l/4≤B.card) (big:100 < l^2) (bigD:100/d ≤ l^2) (slow:l^8≤d*L)
    (co:∀ i∈B,0<u i ∧ 0<p i ∧ log (u i:ℝ)≤d*L/16 ∧ log (p i:ℝ)≤3*l ∧ (e i:ℝ)≤4*L) :
    ∃ i∈B, ∃ j∈B, i≠j ∧ ∃ (m a b:ℕ), 0<a ∧ 0<b ∧
    u i*(p i)^(e i)=a*(p i)^m ∧ u j*(p j)^(e j)=b*(p j)^m ∧
    log (a:ℝ)≤d*L/4 ∧ log (b:ℝ)≤d*L/4 ∧ |log (a:ℝ)-log (b:ℝ)|≤l^6 ∧ (m:ℝ)≤4*L := by
  classical
  have lp : 0<l := by linarith
  have Lp : 0<L := by linarith
  let K := ⌊L/l^3⌋₊
  have scale : 2≤L/l^3 := by
    apply (le_div_iff₀ (pow_pos lp _)).mpr
    have e := pow_le_pow_right₀ hl (by decide : 3≤8)
    nlinarith only [e,slow,mul_le_mul_of_nonneg_right dc Lp.le,Lp.le]
  have kp : 0<K := Nat.floor_pos.mpr (by linarith)
  have kr : 0<(K:ℝ) := by exact_mod_cast kp
  have kup : (K:ℝ)≤L/l^3 := Nat.floor_le (by positivity)
  have klo : L/l^3≤2*(K:ℝ) := by
    have h := Nat.lt_floor_add_one (L/l^3)
    change L/l^3<(K:ℝ)+1 at h
    linarith [show 1≤(K:ℝ) by exact_mod_cast kp]
  let m (i:Fin k) := (e i/K)*K
  let a (i:Fin k) := u i*(p i)^(e i%K)
  have afact (i:Fin k) : u i*(p i)^(e i)=a i*(p i)^(m i) := by
    dsimp [a,m]
    rw [mul_assoc,←pow_add,Nat.mul_comm (e i/K) K,Nat.mod_add_div]
  have apos (i:Fin k) (hi:i∈B) : 0<a i := by dsimp [a]; exact Nat.mul_pos (co i hi).1 (pow_pos (co i hi).2.1 _)
  have alog (i:Fin k) (hi:i∈B) : log (a i:ℝ)≤d*L/4 := by
    obtain ⟨up,pp,ul,pl,_⟩ := co i hi
    dsimp [a]
    rw [Nat.cast_mul,Nat.cast_pow,log_mul (by exact_mod_cast up.ne') (by positivity [pp]),log_pow]
    have er : ((e i%K:ℕ):ℝ)≤L/l^3 := (show ((e i%K:ℕ):ℝ)≤(K:ℝ) by exact_mod_cast (Nat.mod_lt _ kp).le).trans kup
    have mul := mul_le_mul er pl (log_natCast_nonneg _) (by positivity)
    have small : (L/l^3)*(3*l)≤d*L/8 := by
      rw [show L/l^3*(3*l)=3*L/l^2 by field_simp]
      apply (div_le_iff₀ (sq_pos_of_pos lp)).mpr
      have h := (div_le_iff₀ dp).mp bigD
      nlinarith only [mul_le_mul_of_nonneg_left h Lp.le,Lp.le]
    linarith only [ul,mul,small,mul_pos dp Lp]
  have alL (i:Fin k) (hi:i∈B) : log (a i:ℝ)≤L := (alog i hi).trans (by nlinarith only [mul_le_mul_of_nonneg_right dc Lp.le,Lp.le])
  let bins := range (⌊8*l^3⌋₊+1) ×ˢ range (⌊L/l^6⌋₊+1)
  let key (i:Fin k) := (e i/K,⌊log (a i:ℝ)/l^6⌋₊)
  have maps (i:Fin k) (hi:i∈B) : key i∈bins := by
    apply mem_product.mpr
    constructor
    · apply mem_range.mpr
      apply Nat.lt_succ_of_le
      apply (Nat.le_floor_iff (by positivity)).mpr
      have dd := Nat.cast_div_le (α:=ℝ) (m:=e i) (n:=K)
      apply dd.trans
      apply (div_le_iff₀ kr).mpr
      have h := (div_le_iff₀ (pow_pos lp 3)).mp klo
      nlinarith only [h,(co i hi).2.2.2.2]
    · exact mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right (alL i hi) (by positivity))))
  have count : bins.card<B.card := by
    have w1 : 1≤L/l^6 := by
      apply (le_div_iff₀ (pow_pos lp _)).mpr
      have e := pow_le_pow_right₀ hl (by decide : 6≤8)
      nlinarith only [e,slow,mul_le_mul_of_nonneg_right dc Lp.le,Lp.le]
    have r1 : 1≤l^3 := one_le_pow₀ hl
    have a₁ := Nat.floor_le (show 0≤8*l^3 by positivity)
    have a₂ := Nat.floor_le (show 0≤L/l^6 by positivity)
    have bound : (bins.card:ℝ)≤18*L/l^3 := by
      simp only [bins,card_product,card_range,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      have h := mul_le_mul (show (⌊8*l^3⌋₊:ℝ)+1≤9*l^3 by linarith) (show (⌊L/l^6⌋₊:ℝ)+1 ≤ 2*(L/l^6) by linarith) (by positivity) (by positivity)
      exact h.trans_eq (by field_simp; ring)
    have low : 18*L/l^3 < L/l/4 := by
      rw [show L/l/4=(l^2/4)*(L/l^3) by field_simp,mul_div_assoc]
      exact mul_lt_mul_of_pos_right (by linarith) (div_pos Lp (pow_pos lp _))
    exact_mod_cast (bound.trans_lt low).trans_le size
  obtain ⟨i,bi,j,bj,ne,eq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to count maps
  have first : e i/K=e j/K := congrArg Prod.fst eq
  have second : ⌊log (a i:ℝ)/l^6⌋₊=⌊log (a j:ℝ)/l^6⌋₊ := congrArg Prod.snd eq
  have wp : 0<l^6 := pow_pos lp _
  have li := Nat.floor_le (div_nonneg (log_natCast_nonneg (a i)) wp.le)
  have lj := Nat.floor_le (div_nonneg (log_natCast_nonneg (a j)) wp.le)
  have ui := Nat.lt_floor_add_one (log (a i:ℝ)/l^6)
  have uj := Nat.lt_floor_add_one (log (a j:ℝ)/l^6)
  rw [second] at li ui
  have diff : |log (a i:ℝ)/l^6-log (a j:ℝ)/l^6|≤1 := abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩
  rw [←sub_div,abs_div,abs_of_pos wp,div_le_iff₀ wp,one_mul] at diff
  have ms : m i=m j := congrArg (· * K) first
  refine ⟨i,bi,j,bj,ne,m i,a i,a j,apos i bi,apos j bj,afact i,by rw [ms]; exact afact j,alog i bi,alog j bj,diff,?_⟩
  exact (show (m i:ℝ)≤(e i:ℝ) by exact_mod_cast Nat.div_mul_le_self (e i) K).trans (co i bi).2.2.2.2

private lemma forms {n k X Y a b p q e:ℕ} {S:ℝ} (nels:X≠Y)
    (xp:0<X) (yp:0<Y) (pa:0<a) (pb:0<b) (pp:0<p) (pq:0<q)
    (splX:X=a*p^e) (splY:Y=b*q^e) (np:0<n)
    (nx:n≤X) (ny:n≤Y) (xk:X≤n+k) (yk:Y≤n+k)
    (small:(k:ℝ)/n<(n:ℝ)^(-(1/2:ℝ))) (sp:0<S)
    (prime:(p:ℝ)+(q:ℝ)≤(log S)^16)
    (lo:2*log S/log (log S)≤(e:ℝ)) (hi:(e:ℝ)≤(log S)^16)
    (la:log (a:ℝ)≤log S-log 2) (lb:log (b:ℝ)≤log S-log 2)
    (delta:|log (a:ℝ)-log (b:ℝ)|≤(log S)^(3/4:ℝ)) :
    ∃ (u v:ℚ) (m:ℤ), 0<u ∧ 0<v ∧ ((u.num.natAbs+u.den:ℕ):ℝ)≤(log S)^16 ∧
    ((v.num.natAbs+v.den:ℕ):ℝ)≤S ∧ 2*log S/log (log S)≤|(m:ℝ)| ∧ |(m:ℝ)|≤(log S)^16 ∧
    |log (v:ℝ)|≤(log S)^(3/4:ℝ) ∧ 0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧
    |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ)) := by
  let u : ℚ := (p:ℚ)/q
  let v : ℚ := (b:ℚ)/a
  have h₁ := Nat.cast_le (α:=ℝ).mpr (height_div pp pq)
  have h₂ := Nat.cast_le (α:=ℝ).mpr (height_div pb pa)
  push_cast at h₁ h₂
  have ca : (a:ℝ)≤S/2 := (log_le_log_iff (by exact_mod_cast pa) (by positivity)).mp (by rwa [log_div sp.ne' (by norm_num)])
  have cb : (b:ℝ)≤S/2 := (log_le_log_iff (by exact_mod_cast pb) (by positivity)).mp (by rwa [log_div sp.ne' (by norm_num)])
  have lu : log (u:ℝ)=log (p:ℝ)-log (q:ℝ) := by simp [u,log_div,pp.ne',pq.ne']
  have lv : log (v:ℝ)=log (b:ℝ)-log (a:ℝ) := by simp [v,log_div,pa.ne',pb.ne']
  have xl (z c d:ℕ) (hc:0<c) (hd:0<d) (eq:z=c*d^e) :
      log (z:ℝ)=log (c:ℝ)+(e:ℝ)*log (d:ℝ) := by rw [eq,Nat.cast_mul,Nat.cast_pow,log_mul (by positivity) (by positivity),log_pow]
  have hX := xl _ _ _ pa pp splX
  have hY := xl _ _ _ pb pq splY
  have eq : (e:ℝ)*log (u:ℝ)-log (v:ℝ)=log (X:ℝ)-log (Y:ℝ) := by rw [lu,lv,hX,hY]; ring
  have logne : log (X:ℝ)≠log (Y:ℝ) := fun h => nels (by exact_mod_cast (Real.log_injOn_pos (show (0:ℝ)<X by exact_mod_cast xp) (show (0:ℝ)<Y by exact_mod_cast yp) h))
  have close := log_near (x:=(X:ℝ)) (y:=(Y:ℝ)) (by exact_mod_cast np : (0:ℝ)<n) (Nat.cast_nonneg k) (by exact_mod_cast nx) (by exact_mod_cast ny)
    (by exact_mod_cast xk) (by exact_mod_cast yk)
  refine ⟨u,v,e,by dsimp [u]; positivity,by dsimp [v]; positivity,?_,?_,?_,?_,?_,?_,?_⟩
  · push_cast
    exact h₁.trans prime
  · push_cast
    exact h₂.trans (by linarith)
  · simpa using lo
  · simpa using hi
  · rwa [lv,abs_sub_comm]
  · rw [Int.cast_natCast,eq]; exact abs_pos.mpr (sub_ne_zero.mpr logne)
  · rw [Int.cast_natCast,eq]; exact close.trans_lt small

private theorem rounded : Rounded := by
  classical
  intro b hb S₀
  let d := min b (1/100:ℝ)
  have dp : 0<d := lt_min hb (by norm_num)
  have db : d≤b := min_le_left .. 
  have dc : d≤1/100 := min_le_right ..
  refine ⟨d,dp,dc,?_⟩
  have tN : Tendsto (fun n:ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have tL := tendsto_log_atTop.comp tN
  have tl := tendsto_log_atTop.comp tL
  have tD := (tendsto_const_mul_atTop_of_pos dp).mpr tL
  have tS := tendsto_exp_atTop.comp tD
  have tl2 := (tendsto_pow_atTop (by decide : 2≠0)).comp tl
  filter_upwards [eventually_ge_atTop 2,tL.eventually_ge_atTop 8,tl.eventually_ge_atTop 1,
    tl.eventually_ge_atTop (-2*log d),tL.eventually_ge_atTop (2/d^2),
    tD.eventually_ge_atTop 8,tS.eventually_ge_atTop S₀,tl2.eventually_gt_atTop (100+100/d),
    tL.eventually (logpower d 1 dp one_pos),tN.eventually (logpower 1 (1/2) one_pos (by norm_num))]
    with n hn hL hl hdlog hdL hD hS hδl hpow hNpow
  let L := log (n:ℝ)
  let l := log L
  let S := exp (d*L)
  let T := d*L/4
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  change 8≤L at hL
  change 1≤l at hl
  change -2*log d ≤ l at hdlog
  change 2/d^2≤L at hdL
  change 8≤d*L at hD
  change S₀≤S at hS
  change 100+100/d<l^2 at hδl
  change l^8 ≤ d*L^(1:ℝ) at hpow
  rw [rpow_one] at hpow
  change L^8≤1*(n:ℝ)^(1/2:ℝ) at hNpow
  rw [one_mul,←sqrt_eq_rpow] at hNpow
  have Lp : 0<L := by linarith
  have lp : 0<l := by linarith
  have sp : 0<S := exp_pos _
  have ls : log S=d*L := log_exp _
  have llS : l/2≤log (log S) := by rw [ls,log_mul dp.ne' Lp.ne']; change _≤log d+l; linarith
  have Spow : S≤(n:ℝ)^b := by rw [rpow_def_of_pos np]; apply exp_le_exp.mpr; dsimp [L]; nlinarith only [mul_le_mul_of_nonneg_right db Lp.le]
  have sp2 : L≤(d*L)^2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos dp)).mp hdL
    nlinarith only [mul_le_mul_of_nonneg_left h Lp.le,Lp.le]
  have cap16 : 4*L^3 ≤ (d*L)^16 := calc
    _ ≤ L^4 := by nlinarith only [mul_nonneg (show 0≤L-4 by linarith) (pow_nonneg Lp.le 3)]
    _ ≤ ((d*L)^2)^4 := pow_le_pow_left₀ Lp.le sp2 _
    _ = (d*L)^8 := by ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by decide)
  have width : l^6 ≤ (log S)^(3/4:ℝ) := by
    rw [ls]
    calc l^6 = (l^8)^(3/4:ℝ) := by rw [←rpow_natCast_mul lp.le]; norm_num
         _ ≤ _ := rpow_le_rpow (by positivity) hpow (by norm_num)
  have wL : l^4≤L := by
    have h := pow_le_pow_right₀ hl (by decide : 4≤8)
    nlinarith only [h,hpow,mul_le_mul_of_nonneg_right dc Lp.le]
  intro k hk B p e u size row
  let Q := L/l
  change (k:ℝ)<Q^3 at hk
  change Q/4 ≤ (B.card:ℝ) at size
  have qp : 0<Q := div_pos Lp lp
  have qL : Q≤L := (div_le_iff₀ lp).mpr (by nlinarith only [mul_nonneg Lp.le (sub_nonneg.mpr hl)])
  have kl : (k:ℝ)≤L^3 := hk.le.trans (pow_le_pow_left₀ qp.le qL _)
  have root : (k:ℝ)<sqrt n := by
    have h : L^3<L^8 := pow_lt_pow_right₀ (by linarith) (by decide)
    exact kl.trans_lt (h.trans_le hNpow)
  have kn : k≤n := by
    have h := Real.sqrt_le_self_iff.mpr (Or.inr (show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega)))
    exact_mod_cast root.le.trans h
  have ks : (k:ℝ)/n < (n:ℝ)^(-(1/2:ℝ)) := by
    rw [←show sqrt (n:ℝ)/n=(n:ℝ)^(-(1/2:ℝ)) by rw [sqrt_eq_rpow,show (n:ℝ)^(-(1/2:ℝ))=(n:ℝ)^((1/2:ℝ)-1) by norm_num,rpow_sub np,rpow_one]]
    exact div_lt_div_of_pos_right root np
  have bp : B.Nonempty := card_pos.mp (by exact_mod_cast (show 0<Q/4 by positivity).trans_le size)
  obtain ⟨ib,hib⟩ := bp
  have kp : 0<k := (row ib hib).1.pos.trans (row ib hib).2.1
  have logk : log (k:ℝ)≤3*l := by
    have h := log_le_log (by exact_mod_cast kp) kl
    rwa [log_pow] at h
  let X (i:Fin k) := n+i.val+1
  have bounds (i:Fin k) : n≤X i ∧ X i≤n+k := by dsimp [X]; have := i.isLt; omega
  have xl (i:Fin k) (bi:i∈B) : log (X i:ℝ)=log (u i:ℝ)+(e i:ℝ)*log (p i:ℝ) := by
    have hi := row i bi
    dsimp only [X]
    rw [hi.2.2.2.2,Nat.cast_mul,Nat.cast_pow,log_mul (by exact_mod_cast hi.2.2.1.ne') (by positivity [hi.1.pos]),log_pow]
  have Llo (i:Fin k) : L≤log (X i:ℝ) := log_le_log np (by exact_mod_cast (bounds i).1)
  have Lup (i:Fin k) : log (X i:ℝ)≤2*L := by
    have h : (X i:ℝ)≤(n:ℝ)^2 := by exact_mod_cast ((bounds i).2.trans (by nlinarith : n+k≤n^2))
    have h' := log_le_log (by dsimp [X]; positivity) h
    rwa [log_pow] at h'
  have expbd (i:Fin k) (bi:i∈B) : (e i:ℝ)≤4*L := by
    have pp := (row i bi).1
    have lg := log_le_log (by norm_num : (0:ℝ)<2) (by exact_mod_cast pp.two_le : (2:ℝ)≤p i)
    have h := mul_le_mul_of_nonneg_left (show 1/2≤log (p i:ℝ) by linarith [log_two_gt_d9]) (Nat.cast_nonneg (e i))
    linarith only [h,xl i bi, Lup i,log_natCast_nonneg (u i)]
  obtain ⟨i,bi,j,bj,ij,m,a,b',ap,bp',fa,fb,ai,aj,close,mcap⟩ := rounded_pair B p e u L l d (by linarith) hl dp dc size
    (by linarith [show 0<100/d by positivity]) (by linarith) hpow (by
      intro z hz
      have h := row z hz
      exact ⟨h.2.2.1,h.1.pos,h.2.2.2.1,(log_le_log (show (0:ℝ)<p z by exact_mod_cast h.1.pos) (by exact_mod_cast h.2.1.le)).trans logk,expbd z hz⟩)
  have fX : X i=a*(p i)^m := (row i bi).2.2.2.2.trans fa
  have fY : X j=b'*(p j)^m := (row j bj).2.2.2.2.trans fb
  have lX : log (X i:ℝ)=log (a:ℝ)+(m:ℝ)*log (p i:ℝ) := by
    rw [fX,Nat.cast_mul,Nat.cast_pow,log_mul (by exact_mod_cast ap.ne') (by positivity [(row i bi).1.pos]),log_pow]
  have emin : 2*log S/log (log S)≤(m:ℝ) := by
    have plog := (log_le_log (show (0:ℝ)<p i by exact_mod_cast (row i bi).1.pos) (by exact_mod_cast (row i bi).2.1.le)).trans logk
    have h := mul_le_mul_of_nonneg_left plog (Nat.cast_nonneg m (α:=ℝ))
    have main : L ≤ T+(m:ℝ)*(3*l) := by dsimp [T]; linarith only [lX,Llo i,ai,h]
    apply (div_le_iff₀ (by linarith : 0<log (log S))).mpr
    rw [ls]
    have mult := mul_le_mul_of_nonneg_left llS (Nat.cast_nonneg m (α:=ℝ))
    dsimp [T] at main
    rw [ls] at mult
    linarith only [main,mult,mul_le_mul_of_nonneg_right dc Lp.le,Lp.le]
  have ne : X i≠X j := by intro h; apply ij; apply Fin.ext; dsimp [X] at h; omega
  have heights : (p i:ℝ)+(p j:ℝ)≤(log S)^16 := by
    rw [ls]
    have pi : (p i:ℝ) ≤ k := by exact_mod_cast (row i bi).2.1.le
    have pj : (p j:ℝ) ≤ k := by exact_mod_cast (row j bj).2.1.le
    linarith only [pi,pj,kl,cap16,pow_nonneg Lp.le 3]
  have endE : (m:ℝ)≤(log S)^16 := by
    rw [ls]
    have h := pow_le_pow_right₀ (by linarith : 1≤L) (by decide : 1≤3)
    rw [pow_one] at h
    linarith only [mcap,h,cap16]
  have room : T≤log S-log 2 := by rw [ls]; dsimp [T]; linarith [log_two_lt_d9]
  obtain ⟨x,y,m,xx,yy,hx,hy,low,high,lv,nonzero,near⟩ := forms ne (by dsimp [X]; omega) (by dsimp [X]; omega)
    ap bp' (row i bi).1.pos (row j bj).1.pos fX fY
    (by omega : 0<n) (bounds i).1 (bounds j).1 (bounds i).2 (bounds j).2 ks sp heights emin endE (ai.trans room) (aj.trans room) (close.trans width)
  exact ⟨S,x,y,m,hS,Spow,xx,yy,hx,hy,low,high,lv,nonzero,near⟩


end OMA.GrimmSmall

theorem OMA.GrimmAssembly.smallObstruction : OMA.R_Erdos375_erdos_375_variants_log_R1_H1_R1.H2 :=
  OMA.GrimmSmall.main OMA.GrimmSmall.structural OMA.GrimmSmall.rounded

end

section

open Finset Real Filter

/-- In a large family, the factorial product bound leaves enough small cofactors
for the same rounded-exponent argument used for a small Hall obstruction. -/
theorem OMA.GrimmAssembly.largeObstruction :
    OMA.R_Erdos375_erdos_375_variants_log_R1_H1_R1.H3 := by
  classical
  intro b hb S₀ δ hδ
  obtain ⟨d, hd, _, roundRows⟩ := OMA.GrimmSmall.rounded b hb S₀
  let c := min 1 (δ * d / 100)
  have hc : 0 < c := lt_min one_pos (by positivity)
  refine ⟨c, hc, ?_⟩
  have tL : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [roundRows, tL.eventually_ge_atTop 1,
    (tendsto_log_atTop.comp tL).eventually_ge_atTop 1,
    tL.eventually (isLittleO_log_id_atTop.bound hδ)] with n roundRows hL hl growth
  intro k hk B p e u size fac _ rows
  let L := log (n : ℝ)
  let l := log L
  let Q := L / l
  let T := d * L / 16
  change 1 ≤ L at hL
  change 1 ≤ l at hl
  change ‖l‖ ≤ δ * ‖L‖ at growth
  change (k : ℝ) < c * Q^3 at hk
  change δ * Q^2 ≤ (B.card : ℝ) at size
  have Lpos : 0 < L := by linarith
  have lpos : 0 < l := by linarith
  have Qpos : 0 < Q := div_pos Lpos lpos
  have Tpos : 0 < T := by dsimp [T]; positivity
  have scale : 1 ≤ δ * Q := by
    rw [Real.norm_of_nonneg lpos.le, Real.norm_of_nonneg Lpos.le] at growth
    dsimp [Q]
    rwa [← mul_div_assoc, le_div_iff₀ lpos, one_mul]
  have short : (k : ℝ) < Q^3 :=
    hk.trans_le (mul_le_of_le_one_left (by positivity) (min_le_left ..))
  have Qle : Q ≤ L :=
    (div_le_iff₀ lpos).mpr (by nlinarith only [mul_nonneg Lpos.le (sub_nonneg.mpr hl)])
  obtain ⟨i, hi⟩ := card_pos.mp (by exact_mod_cast (mul_pos hδ (sq_pos_of_pos Qpos)).trans_le size)
  have kpos := (rows i hi).1.pos.trans (rows i hi).2.1
  have logk : log (k : ℝ) ≤ 3 * l := by
    have bound := log_le_log (by exact_mod_cast kpos)
      (short.le.trans (pow_le_pow_left₀ Qpos.le Qle 3))
    rwa [log_pow] at bound
  have budget : ∑ i ∈ B, log (u i : ℝ) ≤ 3 * c * Q^2 * L := calc
    _ ≤ (k : ℝ) * log k := by
      have pos : 0 < ∏ i ∈ B, (u i : ℝ) := prod_pos fun i hi => by exact_mod_cast (rows i hi).2.2.1
      have h := log_le_log pos (show (∏ i ∈ B, (u i : ℝ)) ≤ (k : ℝ)^k by
        exact_mod_cast fac.trans k.factorial_le_pow)
      rwa [log_prod (fun i hi => by exact_mod_cast (rows i hi).2.2.1.ne'), log_pow] at h
    _ ≤ (c * Q^3) * (3 * l) := mul_le_mul hk.le logk (log_natCast_nonneg _) (by positivity)
    _ = _ := by dsimp [Q]; field_simp
  let G := B.filter (fun i => log (u i : ℝ) ≤ T)
  let D := B \ G
  have cost : (D.card : ℝ) * T ≤ ∑ i ∈ B, log (u i : ℝ) := calc
    _ = ∑ _i ∈ D, T := by simp
    _ ≤ ∑ i ∈ D, log (u i : ℝ) := by
      apply sum_le_sum
      intro i hi
      obtain ⟨hiB, hiG⟩ := mem_sdiff.mp hi
      exact (lt_of_not_ge fun h => hiG (mem_filter.mpr ⟨hiB, h⟩)).le
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun i _ _ => log_natCast_nonneg _)
  have few : (D.card : ℝ) ≤ δ * Q^2 / 2 := by
    apply le_of_mul_le_mul_right _ Tpos
    refine (cost.trans budget).trans ?_
    have hcδ : c ≤ δ * d / 100 := min_le_right ..
    dsimp [T]
    nlinarith only [mul_le_mul_of_nonneg_right hcδ (mul_nonneg (sq_nonneg Q) Lpos.le),
      mul_nonneg (mul_nonneg hδ.le hd.le) (mul_nonneg (sq_nonneg Q) Lpos.le)]
  have counts : (D.card : ℝ) + G.card = B.card := by
    exact_mod_cast (card_sdiff_add_card_eq_card (show G ⊆ B from filter_subset ..) : D.card + G.card = B.card)
  have enough : Q / 4 ≤ (G.card : ℝ) := by
    nlinarith only [size, few, counts, mul_le_mul_of_nonneg_right scale Qpos.le, Qpos.le]
  apply roundRows k short G p e u enough
  intro i hi
  obtain ⟨hiB, hiT⟩ := mem_filter.mp hi
  obtain ⟨hp, hk, hu, factor⟩ := rows i hiB
  exact ⟨hp, hk, hu, hiT, factor⟩

end

section

/-! With M = log log S >= 64, take z = 1 - log 8 / log M, so M^z = M/8 and
M^(4-4z) = 8^4. The first inequality becomes M exp(3M/4) <= exp(7M/8), i.e. M <= exp(M/8),
which follows from exp x >= x^3/6. -/

open Finset Filter Real

namespace OMA.P2b375

theorem sol : OMA.R_Erdos375_erdos_375_variants_log_R1.H3 := by
  unfold OMA.R_Erdos375_erdos_375_variants_log_R1.H3
  refine ⟨8 ^ 4, by norm_num, ?_⟩
  have hT : Tendsto (fun S : ℝ => log (log S)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hT.eventually (eventually_ge_atTop 64), Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop 0)] with S hM hL
  set L := log S with hLdef
  set M := log L with hMdef
  have hM0 : 0 < M := by linarith
  have hl8 : 0 < log (8:ℝ) := Real.log_pos (by norm_num)
  have hlM : log 8 < log M := Real.log_lt_log (by norm_num) (by linarith)
  have hlM0 : 0 < log M := by linarith
  have hLM : L = exp M := (Real.exp_log hL).symm
  refine ⟨1 - log 8 / log M, ?_, ?_, ?_, ?_⟩
  · have : log 8 / log M ≤ 1 := by rw [div_le_one hlM0]; exact hlM.le
    linarith
  · have : 0 ≤ log 8 / log M := div_nonneg hl8.le hlM0.le
    linarith
  · have hMz : M ^ (1 - log 8 / log M) = M / 8 := by
      rw [Real.rpow_def_of_pos hM0]
      have : log M * (1 - log 8 / log M) = log M - log 8 := by field_simp
      rw [this, Real.exp_sub, Real.exp_log hM0, Real.exp_log (by norm_num)]
    rw [hMz, hLM]
    rw [Real.rpow_def_of_pos (Real.exp_pos M), Real.log_exp]
    -- exp (M * (3/4)) ≤ exp M / M * exp (-(M/8))
    have hcube : M ≤ exp (M / 8) := by
      have h := Real.pow_div_factorial_le_exp (M / 8) (by positivity) 3
      norm_num [Nat.factorial] at h
      have hsq : 3072 ≤ M ^ 2 := by nlinarith
      have h3 : M * 3072 ≤ M * M ^ 2 := mul_le_mul_of_nonneg_left hsq hM0.le
      have h4 : M ≤ (M / 8) ^ 3 / 6 := by nlinarith
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hM0, ← Real.exp_add]
    calc exp (M * (3 / 4)) * M ≤ exp (M * (3 / 4)) * exp (M / 8) :=
          mul_le_mul_of_nonneg_left hcube (Real.exp_pos _).le
      _ = exp (M + -(M / 8)) := by rw [← Real.exp_add]; ring_nf
  · rw [Real.rpow_def_of_pos hM0]
    have : log M * (4 - 4 * (1 - log 8 / log M)) = 4 * log 8 := by field_simp; ring
    rw [this, show (4:ℝ) * log 8 = log (8 ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)]

end OMA.P2b375

theorem OMA.GrimmAssembly.chooseParameter : OMA.R_Erdos375_erdos_375_variants_log_R1.H3 := OMA.P2b375.sol

end

section

/-! Lower bound for linear forms in two rational logarithms (Ramachandra-Shorey-Tijdeman 1975, Section 3).
Handles bounded S and small m by Liouville height bounds, and large m via Siegel's lemma, a bivariate
zero lemma using polynomial resultants, and analytic extrapolation via Lagrange interpolation. -/

namespace OMA.Erdos375LogR1H2

section AnalyticAux

open Complex Finset Metric

lemma peel_one (F : ℂ → ℂ) (hF : Differentiable ℂ F) (a : ℂ) (ha : F a = 0) :
    Differentiable ℂ (dslope F a) ∧ ∀ z, F z = (z - a) * dslope F a z := by
  refine ⟨?_, fun z => ?_⟩
  · exact differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope (s := Set.univ) (f := F) (c := a) Filter.univ_mem).2
        hF.differentiableOn)
  · have h := sub_smul_dslope F a z
    simp only [smul_eq_mul, ha, sub_zero] at h
    exact h.symm

lemma peel_finset (S : Finset ℂ) : ∀ (G : ℂ → ℂ), Differentiable ℂ G →
    (∀ a ∈ S, G a = 0) →
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ z : ℂ, G z = (∏ a ∈ S, (z - a)) * H z := by
  classical
  induction S using Finset.induction_on with
  | empty => intro G hG _; exact ⟨G, hG, fun _ => by simp⟩
  | insert a S haS ih =>
    intro G hG hvan
    obtain ⟨hD, hfac⟩ := peel_one G hG a (hvan a (mem_insert_self a S))
    have hvanD : ∀ b ∈ S, dslope G a b = 0 := by
      intro b hb
      have hne : b - a ≠ 0 := sub_ne_zero.mpr (fun h => haS (h ▸ hb))
      have h0 : (b - a) * dslope G a b = 0 := by
        rw [← hfac b]; exact hvan b (mem_insert_of_mem hb)
      exact (mul_eq_zero.mp h0).resolve_left hne
    obtain ⟨H, hH, hfacH⟩ := ih (dslope G a) hD hvanD
    refine ⟨H, hH, fun z => ?_⟩
    rw [hfac z, hfacH z, prod_insert haS]
    ring

noncomputable def lagrangeInterp (Z : Finset ℤ) (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∑ a ∈ Z, F (a : ℂ) * ∏ b ∈ Z.erase a, (w - (b : ℂ)) / ((a : ℂ) - (b : ℂ))

lemma differentiable_lagrangeInterp (Z : Finset ℤ) (F : ℂ → ℂ) :
    Differentiable ℂ (lagrangeInterp Z F) := by
  unfold lagrangeInterp
  refine Differentiable.fun_sum fun a _ => Differentiable.const_mul ?_ _
  exact Differentiable.fun_finsetProd
    (fun b _ => (differentiable_id.sub_const (b : ℂ)).div_const ((a : ℂ) - (b : ℂ)))

lemma lagrangeInterp_apply_mem (Z : Finset ℤ) (F : ℂ → ℂ) {a : ℤ} (ha : a ∈ Z) :
    lagrangeInterp Z F (a : ℂ) = F (a : ℂ) := by
  unfold lagrangeInterp
  rw [Finset.sum_eq_single a]
  · have hprod : ∏ b ∈ Z.erase a, ((a : ℂ) - (b : ℂ)) / ((a : ℂ) - (b : ℂ)) = 1 := by
      refine Finset.prod_eq_one fun b hb => ?_
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      exact div_self (sub_ne_zero.mpr (fun h => hba (by exact_mod_cast h.symm)))
    rw [hprod, mul_one]
  · intro c hc hca
    have ha' : a ∈ Z.erase c := Finset.mem_erase.mpr ⟨hca.symm, ha⟩
    have hprod : ∏ b ∈ Z.erase c, ((a : ℂ) - (b : ℂ)) / ((c : ℂ) - (b : ℂ)) = 0 :=
      Finset.prod_eq_zero ha' (by simp)
    rw [hprod, mul_zero]
  · intro hna; exact absurd ha hna

lemma norm_lagrangeInterp_le (Z : Finset ℤ) (F : ℂ → ℂ) {ρ W ε : ℝ}
    (hW : 1 ≤ W) (hρW : ρ ≤ W) (hε : 0 ≤ ε)
    (hZ : ∀ a ∈ Z, ‖(a : ℂ)‖ ≤ ρ) (hF : ∀ a ∈ Z, ‖F (a : ℂ)‖ ≤ ε)
    {w : ℂ} (hw : ‖w‖ ≤ W) :
    ‖lagrangeInterp Z F w‖ ≤ (Z.card : ℝ) * ε * (2 * W) ^ Z.card := by
  unfold lagrangeInterp
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (ε * (2 * W) ^ Z.card) fun a ha => ?_).trans_eq (by
    rw [nsmul_eq_mul]; ring)
  rw [norm_mul, norm_prod]
  have h1 : ‖F (a : ℂ)‖ ≤ ε := hF a ha
  have h2 : ∏ b ∈ Z.erase a, ‖(w - (b : ℂ)) / ((a : ℂ) - (b : ℂ))‖ ≤ (2 * W) ^ Z.card := by
    have hsub : ∏ b ∈ Z.erase a, ‖(w - (b : ℂ)) / ((a : ℂ) - (b : ℂ))‖ ≤
        (2 * W) ^ (Z.erase a).card := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun b hb => ?_
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      have hden : (1 : ℝ) ≤ ‖(a : ℂ) - (b : ℂ)‖ := by
        rw [show (a : ℂ) - (b : ℂ) = (((a - b : ℤ) : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hba.symm)
      have hnum : ‖w - (b : ℂ)‖ ≤ 2 * W := by
        have hb' : ‖(b : ℂ)‖ ≤ ρ := hZ b (Finset.mem_erase.mp hb).2
        exact (norm_sub_le _ _).trans (by linarith)
      rw [norm_div]
      exact (div_le_self (norm_nonneg _) hden).trans hnum
    exact hsub.trans (pow_le_pow_right₀ (by linarith) (Finset.card_erase_le))
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hε

lemma extrapolate_with_approx_zeros (Z : Finset ℤ) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    {ρ W M ε : ℝ} (hρ : 0 ≤ ρ) (hW : ρ < W) (hW1 : 1 ≤ W) (hε : 0 ≤ ε)
    (hZ : ∀ a ∈ Z, ‖(a : ℂ)‖ ≤ ρ) (hFε : ∀ a ∈ Z, ‖F (a : ℂ)‖ ≤ ε)
    (hFM : ∀ z : ℂ, ‖z‖ = W → ‖F z‖ ≤ M)
    {w₁ : ℂ} (hw₁ : ‖w₁‖ ≤ ρ) :
    ‖F w₁‖ ≤ ((2 * ρ) / (W - ρ)) ^ Z.card * (M + (Z.card : ℝ) * ε * (2 * W) ^ Z.card) +
      (Z.card : ℝ) * ε * (2 * W) ^ Z.card := by
  classical
  set L := lagrangeInterp Z F
  set G : ℂ → ℂ := fun z => F z - L z
  have hGd : Differentiable ℂ G := hF.sub (differentiable_lagrangeInterp Z F)
  set S : Finset ℂ := Z.image (fun a : ℤ => (a : ℂ)) with hSdef
  have hScard : S.card = Z.card := Finset.card_image_of_injective Z Int.cast_injective
  have hGvan : ∀ z ∈ S, G z = 0 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    simp only [G, L, lagrangeInterp_apply_mem Z F ha, sub_self]
  obtain ⟨H, hHd, hfac⟩ := peel_finset S G hGd hGvan
  set E : ℝ := (Z.card : ℝ) * ε * (2 * W) ^ Z.card
  have hE0 : 0 ≤ E := by positivity
  have hW0 : 0 < W := by linarith
  have hWρ : 0 < W - ρ := by linarith
  have hSa : ∀ z ∈ S, ‖z‖ ≤ ρ := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact hZ a ha
  have hHsphere : ∀ z : ℂ, ‖z‖ = W → ‖H z‖ ≤ (M + E) / (W - ρ) ^ Z.card := by
    intro z hz
    have hP : (W - ρ) ^ Z.card ≤ ‖∏ a ∈ S, (z - a)‖ := by
      rw [norm_prod, ← hScard, ← Finset.prod_const]
      refine Finset.prod_le_prod (fun _ _ => hWρ.le) fun a ha => ?_
      have h1 := norm_sub_norm_le z a
      linarith [hSa a ha]
    have hGz : ‖G z‖ ≤ M + E := by
      have hLz : ‖L z‖ ≤ E :=
        norm_lagrangeInterp_le Z F hW1 hW.le hε hZ hFε (by rw [hz])
      exact (norm_sub_le _ _).trans (add_le_add (hFM z hz) hLz)
    rw [le_div_iff₀ (pow_pos hWρ Z.card)]
    calc ‖H z‖ * (W - ρ) ^ Z.card
        ≤ ‖H z‖ * ‖∏ a ∈ S, (z - a)‖ := mul_le_mul_of_nonneg_left hP (norm_nonneg _)
      _ = ‖G z‖ := by rw [hfac z, norm_mul, mul_comm]
      _ ≤ M + E := hGz
  have hHw₁ : ‖H w₁‖ ≤ (M + E) / (W - ρ) ^ Z.card := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hHd.diffContOnCl
      (fun y hy => hHsphere y (by
        rw [frontier_ball (0 : ℂ) hW0.ne'] at hy
        simpa [mem_sphere_iff_norm] using hy))
      (by rw [closure_ball (0 : ℂ) hW0.ne', mem_closedBall_iff_norm]; simpa using hw₁.trans hW.le)
  have hPw₁ : ‖∏ a ∈ S, (w₁ - a)‖ ≤ (2 * ρ) ^ Z.card := by
    rw [norm_prod, ← hScard, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun a ha => ?_
    exact (norm_sub_le _ _).trans (by linarith [hSa a ha])
  have hGw₁ : ‖G w₁‖ ≤ ((2 * ρ) / (W - ρ)) ^ Z.card * (M + E) := by
    calc ‖G w₁‖ = ‖∏ a ∈ S, (w₁ - a)‖ * ‖H w₁‖ := by rw [hfac w₁, norm_mul]
      _ ≤ (2 * ρ) ^ Z.card * ((M + E) / (W - ρ) ^ Z.card) :=
          mul_le_mul hPw₁ hHw₁ (norm_nonneg _) (pow_nonneg (by linarith) _)
      _ = ((2 * ρ) / (W - ρ)) ^ Z.card * (M + E) := by rw [div_pow]; ring
  have hLw₁ : ‖L w₁‖ ≤ E := norm_lagrangeInterp_le Z F hW1 hW.le hε hZ hFε (hw₁.trans hW.le)
  calc ‖F w₁‖ = ‖G w₁ + L w₁‖ := by simp only [G, sub_add_cancel]
    _ ≤ ‖G w₁‖ + ‖L w₁‖ := norm_add_le _ _
    _ ≤ ((2 * ρ) / (W - ρ)) ^ Z.card * (M + E) + E := add_le_add hGw₁ hLw₁

end AnalyticAux

section RealArith

lemma abs_exp_sub_exp_le (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤ |x - y| * Real.exp (max x y) := by
  wlog hxy : x ≤ y
  · rw [abs_sub_comm (Real.exp x) _, abs_sub_comm x y, max_comm x y]
    exact this y x (le_of_not_ge hxy)
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hxy)),
    abs_of_nonpos (sub_nonpos.mpr hxy), max_eq_right hxy]
  have h1 : -(y - x) + 1 ≤ Real.exp (-(y - x)) := Real.add_one_le_exp (-(y - x))
  have h2 : 1 - Real.exp (-(y - x)) ≤ y - x := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos y).le
  rw [mul_sub, mul_one, ← Real.exp_add, show y + -(y - x) = x by ring] at h3
  linarith

lemma rat_num_natAbs_eq {r : ℚ} (hr : 0 < r) : (r.num.natAbs : ℤ) = r.num :=
  Int.natAbs_of_nonneg (Rat.num_pos.mpr hr).le

lemma rat_num_natAbs_cast_rat {r : ℚ} (hr : 0 < r) : (r.num.natAbs : ℚ) = r.num := by
  rw [← Int.cast_natCast, rat_num_natAbs_eq hr]

lemma rat_num_natAbs_cast_real {r : ℚ} (hr : 0 < r) : (r.num.natAbs : ℝ) = r.num := by
  rw [← Int.cast_natCast, rat_num_natAbs_eq hr]

lemma rat_inv_height {u : ℚ} (hu : 0 < u) :
    (u⁻¹).num.natAbs + (u⁻¹).den = u.num.natAbs + u.den := by
  have swapped := Rat.den_inv_of_ne_zero (inv_ne_zero hu.ne')
  rw [inv_inv] at swapped
  rw [← swapped, Rat.den_inv_of_ne_zero hu.ne', Nat.add_comm]

lemma rat_div_height_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ((p : ℚ) / (q : ℚ)).num.natAbs ≤ p ∧ ((p : ℚ) / (q : ℚ)).den ≤ q := by
  have hd : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have num := Rat.num_dvd (p : ℤ) hd
  have den := Rat.den_dvd (p : ℤ) (q : ℤ)
  rw [Rat.divInt_eq_div] at num den
  push_cast at num den
  exact ⟨Nat.le_of_dvd hp (Int.natAbs_dvd_natAbs.mpr num),
    Nat.le_of_dvd hq (Int.natAbs_dvd_natAbs.mpr den)⟩

lemma abs_log_rat_ge_of_ne_one {r : ℚ} (hr : 0 < r) (hr1 : r ≠ 1) :
    1 / ((r.num.natAbs + r.den : ℕ) : ℝ) ≤ |Real.log (r : ℝ)| := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr1R : (r : ℝ) ≠ 1 := by exact_mod_cast hr1
  have hnum : (r.num : ℝ) = (r.num.natAbs : ℝ) := (rat_num_natAbs_cast_real hr).symm
  have ha0 : (0 : ℝ) < r.num.natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr (Rat.num_pos.mpr hr).ne'
  have hb0 : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hcast : (r : ℝ) = (r.num.natAbs : ℝ) / (r.den : ℝ) := by
    rw [Rat.cast_def, hnum]
  rcases lt_or_gt_of_ne hr1R with hlt | hgt
  · have hlog : Real.log (r : ℝ) ≤ (r : ℝ) - 1 := Real.log_le_sub_one_of_pos hrR
    have hlt' : r.num.natAbs < r.den := by
      have : (r.num.natAbs : ℝ) / r.den < 1 := hcast ▸ hlt
      rw [div_lt_one hb0] at this
      exact_mod_cast this
    have hdiff : (1 : ℝ) ≤ (r.den : ℝ) - r.num.natAbs := by
      have : (1 : ℕ) ≤ r.den - r.num.natAbs := by omega
      have h' : (1 : ℝ) ≤ ((r.den - r.num.natAbs : ℕ) : ℝ) := by exact_mod_cast this
      rwa [Nat.cast_sub hlt'.le] at h'
    have h1 : 1 / ((r.num.natAbs + r.den : ℕ) : ℝ) ≤ 1 / (r.den : ℝ) := by
      apply one_div_le_one_div_of_le hb0
      exact_mod_cast Nat.le_add_left r.den r.num.natAbs
    have h2 : 1 / (r.den : ℝ) ≤ 1 - (r : ℝ) := by
      rw [hcast, one_sub_div hb0.ne']
      exact div_le_div_of_nonneg_right hdiff hb0.le
    have h3 : 1 - (r : ℝ) ≤ -Real.log (r : ℝ) := by linarith
    exact (h1.trans (h2.trans h3)).trans (neg_le_abs _)
  · have hlog : Real.log ((r : ℝ)⁻¹) ≤ (r : ℝ)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hrR)
    rw [Real.log_inv] at hlog
    have hgt' : r.den < r.num.natAbs := by
      have : 1 < (r.num.natAbs : ℝ) / r.den := hcast ▸ hgt
      rw [one_lt_div hb0] at this
      exact_mod_cast this
    have hdiff : (1 : ℝ) ≤ (r.num.natAbs : ℝ) - r.den := by
      have : (1 : ℕ) ≤ r.num.natAbs - r.den := by omega
      have h' : (1 : ℝ) ≤ ((r.num.natAbs - r.den : ℕ) : ℝ) := by exact_mod_cast this
      rwa [Nat.cast_sub hgt'.le] at h'
    have h1 : 1 / ((r.num.natAbs + r.den : ℕ) : ℝ) ≤ 1 / (r.num.natAbs : ℝ) := by
      apply one_div_le_one_div_of_le ha0
      exact_mod_cast Nat.le_add_right r.num.natAbs r.den
    have h2 : 1 / (r.num.natAbs : ℝ) ≤ 1 - (r : ℝ)⁻¹ := by
      rw [hcast, inv_div, one_sub_div ha0.ne']
      exact div_le_div_of_nonneg_right hdiff ha0.le
    have h3 : 1 - (r : ℝ)⁻¹ ≤ Real.log (r : ℝ) := by linarith
    exact (h1.trans (h2.trans h3)).trans (le_abs_self _)

lemma exists_prime_padicValRat_ne_zero {u : ℚ} (hu : 1 < u) :
    ∃ p : ℕ, p.Prime ∧ padicValRat p u ≠ 0 ∧
      ((padicValRat p u).natAbs : ℝ) ≤ Real.log ((u.num.natAbs + u.den : ℕ) : ℝ) / Real.log 2 := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hlt : u.den < u.num.natAbs := by
    have h1 : (1 : ℚ) < u.num / u.den := by rwa [Rat.num_div_den]
    have hd : (0 : ℚ) < u.den := by exact_mod_cast u.pos
    rw [one_lt_div hd] at h1
    have h2 : (u.num.natAbs : ℤ) = u.num := rat_num_natAbs_eq hu0
    have h3 : (u.den : ℤ) < (u.num.natAbs : ℤ) := by rw [h2]; exact_mod_cast h1
    exact_mod_cast h3
  have hge2 : u.num.natAbs ≠ 1 := by have := u.pos; omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hge2
  have : Fact p.Prime := ⟨hp⟩
  have hndvd : ¬ p ∣ u.den := by
    intro h
    exact hp.not_dvd_one (u.reduced ▸ Nat.dvd_gcd hpdvd h)
  have hu_eq : u = (u.num.natAbs : ℚ) / (u.den : ℚ) := by
    have h2 : (u.num.natAbs : ℚ) = u.num := rat_num_natAbs_cast_rat hu0
    rw [h2, Rat.num_div_den]
  have ha0 : (u.num.natAbs : ℚ) ≠ 0 := by exact_mod_cast (by omega : u.num.natAbs ≠ 0)
  have hb0 : (u.den : ℚ) ≠ 0 := by exact_mod_cast u.den_nz
  have hv : padicValRat p u = (padicValNat p u.num.natAbs : ℤ) := by
    calc padicValRat p u
        = padicValRat p ((u.num.natAbs : ℚ) / (u.den : ℚ)) := by conv_lhs => rw [hu_eq]
      _ = padicValRat p (u.num.natAbs : ℚ) - padicValRat p (u.den : ℚ) := padicValRat.div ha0 hb0
      _ = (padicValNat p u.num.natAbs : ℤ) - (padicValNat p u.den : ℤ) := by
          rw [padicValRat.of_nat, padicValRat.of_nat]
      _ = (padicValNat p u.num.natAbs : ℤ) := by
          rw [padicValNat.eq_zero_of_not_dvd hndvd, Nat.cast_zero, sub_zero]
  have hv0 : padicValNat p u.num.natAbs ≠ 0 := by
    have := one_le_padicValNat_of_dvd (by omega : u.num.natAbs ≠ 0) hpdvd
    omega
  refine ⟨p, hp, by rw [hv]; exact_mod_cast hv0, ?_⟩
  rw [hv, Int.natAbs_natCast]
  have hord : p ^ padicValNat p u.num.natAbs ≤ u.num.natAbs :=
    Nat.le_of_dvd (by omega) (pow_padicValNat_dvd)
  have h2pow : (2 : ℝ) ^ padicValNat p u.num.natAbs ≤ ((u.num.natAbs + u.den : ℕ) : ℝ) := by
    have hpow : 2 ^ padicValNat p u.num.natAbs ≤ p ^ padicValNat p u.num.natAbs :=
      Nat.pow_le_pow_left hp.two_le _
    exact_mod_cast hpow.trans (hord.trans (Nat.le_add_right _ _))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by positivity) h2pow
  rw [Real.log_pow] at hlog
  rwa [le_div_iff₀ hl2]

end RealArith

section ZeroLemma

open Polynomial Finset

section DegInner

noncomputable def degInner (f : (ℚ[X])[X]) : ℕ :=
  f.support.sup fun i => (f.coeff i).natDegree

lemma coeff_natDegree_le_degInner (f : (ℚ[X])[X]) (i : ℕ) :
    (f.coeff i).natDegree ≤ degInner f := by
  by_cases hi : i ∈ f.support
  · exact Finset.le_sup (f := fun j => (f.coeff j).natDegree) hi
  · rw [mem_support_iff, not_not] at hi
    simp [hi]

lemma degInner_zero : degInner (0 : (ℚ[X])[X]) = 0 := by
  simp [degInner]

lemma degInner_C (c : ℚ[X]) : degInner (C c) = c.natDegree := by
  by_cases hc : c = 0
  · subst hc; simp [degInner]
  · rw [degInner, support_C hc, Finset.sup_singleton, coeff_C_zero]

lemma degInner_CC (q : ℚ) : degInner (C (C q) : (ℚ[X])[X]) = 0 := by
  rw [degInner_C, natDegree_C]

lemma degInner_X : degInner (X : (ℚ[X])[X]) = 0 := by
  rw [degInner, support_X, Finset.sup_singleton, coeff_X_one, natDegree_one]

lemma degInner_add_le (f g : (ℚ[X])[X]) : degInner (f + g) ≤ max (degInner f) (degInner g) := by
  refine Finset.sup_le fun i _ => ?_
  rw [coeff_add]
  exact (natDegree_add_le _ _).trans (max_le_max (coeff_natDegree_le_degInner f i)
    (coeff_natDegree_le_degInner g i))

lemma degInner_mul_le (f g : (ℚ[X])[X]) : degInner (f * g) ≤ degInner f + degInner g := by
  refine Finset.sup_le fun i _ => ?_
  rw [coeff_mul]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun ij _ => ?_)
  exact natDegree_mul_le.trans
    (Nat.add_le_add (coeff_natDegree_le_degInner f ij.1) (coeff_natDegree_le_degInner g ij.2))

lemma degInner_pow_le (f : (ℚ[X])[X]) (n : ℕ) : degInner (f ^ n) ≤ n * degInner f := by
  induction n with
  | zero => rw [pow_zero, ← C_1, degInner_C, natDegree_one, zero_mul]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (degInner_mul_le _ _).trans (Nat.add_le_add_right ih _)

lemma degInner_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → (ℚ[X])[X]) (B : ℕ)
    (hB : ∀ i ∈ s, degInner (f i) ≤ B) : degInner (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [degInner_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (degInner_add_le _ _).trans (max_le (hB a (Finset.mem_insert_self a s))
      (ih fun i hi => hB i (Finset.mem_insert_of_mem hi)))

lemma exists_max_degInner_index {f : (ℚ[X])[X]} (hf : f ≠ 0) :
    ∃ i₀ ∈ f.support, (f.coeff i₀).natDegree = degInner f ∧
      ∀ i, i₀ < i → f.coeff i = 0 ∨ (f.coeff i).natDegree < degInner f := by
  classical
  let S := f.support.filter fun i => (f.coeff i).natDegree = degInner f
  have hne : f.support.Nonempty := nonempty_support_iff.mpr hf
  obtain ⟨i₁, hi₁, hmax₁⟩ := Finset.exists_mem_eq_sup f.support hne fun i => (f.coeff i).natDegree
  have hSne : S.Nonempty := ⟨i₁, Finset.mem_filter.mpr ⟨hi₁, hmax₁.symm⟩⟩
  let i₀ := S.max' hSne
  have hi₀S : i₀ ∈ S := Finset.max'_mem S hSne
  have hi₀ := Finset.mem_filter.mp hi₀S
  refine ⟨i₀, hi₀.1, hi₀.2, fun i hlt => ?_⟩
  by_cases his : i ∈ f.support
  · right
    have hle : (f.coeff i).natDegree ≤ degInner f := coeff_natDegree_le_degInner f i
    have hne_deg : (f.coeff i).natDegree ≠ degInner f := by
      intro heq
      have hiS : i ∈ S := Finset.mem_filter.mpr ⟨his, heq⟩
      have := Finset.le_max' S i hiS
      omega
    omega
  · left
    exact notMem_support_iff.mp his

lemma degInner_mul_eq {f g : (ℚ[X])[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    degInner (f * g) = degInner f + degInner g := by
  by_cases hsum : degInner f + degInner g = 0
  · have := degInner_mul_le f g
    omega
  have hpos : 0 < degInner f + degInner g := Nat.pos_of_ne_zero hsum
  obtain ⟨i₀, hi₀, hdi₀, hltf⟩ := exists_max_degInner_index hf
  obtain ⟨j₀, hj₀, hdj₀, hltg⟩ := exists_max_degInner_index hg
  have hfi₀ : f.coeff i₀ ≠ 0 := mem_support_iff.mp hi₀
  have hgj₀ : g.coeff j₀ ≠ 0 := mem_support_iff.mp hj₀
  have hmain : (f.coeff i₀ * g.coeff j₀).natDegree = degInner f + degInner g := by
    rw [natDegree_mul hfi₀ hgj₀, hdi₀, hdj₀]
  set A := Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)
  have hij_mem : (i₀, j₀) ∈ A := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
  have hrest : (∑ xy ∈ A.erase (i₀, j₀), f.coeff xy.1 * g.coeff xy.2).natDegree <
      degInner f + degInner g := by
    have hlt : ∀ xy ∈ A.erase (i₀, j₀), (f.coeff xy.1 * g.coeff xy.2).natDegree <
        degInner f + degInner g := by
      intro xy hxy
      have hne : xy ≠ (i₀, j₀) := (Finset.mem_erase.mp hxy).1
      have hcases : i₀ < xy.1 ∨ j₀ < xy.2 := by
        have hsum_xy : xy.1 + xy.2 = i₀ + j₀ :=
          Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_erase.mp hxy).2
        by_contra hcon
        push Not at hcon
        have : xy.1 = i₀ ∧ xy.2 = j₀ := by omega
        exact hne (Prod.ext this.1 this.2)
      rcases hcases with h1 | h2
      · rcases hltf xy.1 h1 with hz | hdeg
        · simp [hz, hpos]
        · by_cases hfb : f.coeff xy.1 = 0
          · simp [hfb, hpos]
          · by_cases hgb : g.coeff xy.2 = 0
            · simp [hgb, hpos]
            · rw [natDegree_mul hfb hgb]
              exact Nat.add_lt_add_of_lt_of_le hdeg (coeff_natDegree_le_degInner g xy.2)
      · rcases hltg xy.2 h2 with hz | hdeg
        · simp [hz, hpos]
        · by_cases hfb : f.coeff xy.1 = 0
          · simp [hfb, hpos]
          · by_cases hgb : g.coeff xy.2 = 0
            · simp [hgb, hpos]
            · rw [natDegree_mul hfb hgb]
              exact Nat.add_lt_add_of_le_of_lt (coeff_natDegree_le_degInner f xy.1) hdeg
    have h_all : ∀ xy ∈ A.erase (i₀, j₀),
        (f.coeff xy.1 * g.coeff xy.2).natDegree ≤ degInner f + degInner g - 1 :=
      fun xy hxy => Nat.le_sub_one_of_lt (hlt xy hxy)
    exact (natDegree_sum_le_of_forall_le (n := degInner f + degInner g - 1) (A.erase (i₀, j₀))
      (fun xy => f.coeff xy.1 * g.coeff xy.2) h_all).trans_lt (Nat.sub_lt hpos Nat.one_pos)
  have hcoeff : (f * g).coeff (i₀ + j₀) =
      f.coeff i₀ * g.coeff j₀ + ∑ xy ∈ A.erase (i₀, j₀), f.coeff xy.1 * g.coeff xy.2 := by
    rw [coeff_mul]
    exact (Finset.add_sum_erase A (fun xy => f.coeff xy.1 * g.coeff xy.2) hij_mem).symm
  have hdeg_coeff : ((f * g).coeff (i₀ + j₀)).natDegree = degInner f + degInner g := by
    rw [hcoeff, natDegree_add_eq_left_of_natDegree_lt (hrest.trans_eq hmain.symm), hmain]
  have hle1 : degInner (f * g) ≤ degInner f + degInner g := degInner_mul_le f g
  have hle2 : degInner f + degInner g ≤ degInner (f * g) := by
    rw [← hdeg_coeff]
    exact coeff_natDegree_le_degInner (f * g) (i₀ + j₀)
  omega

lemma degInner_multiset_prod {s : Multiset ((ℚ[X])[X])} (hs : ∀ f ∈ s, f ≠ 0) :
    degInner s.prod = (s.map degInner).sum := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.prod_zero, ← C_1, degInner_C, natDegree_one]; simp
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ f ∈ s, f ≠ 0 := fun f hf => hs f (Multiset.mem_cons_of_mem hf)
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h => hs' 0 h rfl)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, degInner_mul_eq ha hprod, ih hs']

lemma natDegree_multiset_prod {s : Multiset ((ℚ[X])[X])} (hs : ∀ f ∈ s, f ≠ 0) :
    s.prod.natDegree = (s.map Polynomial.natDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ f ∈ s, f ≠ 0 := fun f hf => hs f (Multiset.mem_cons_of_mem hf)
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h => hs' 0 h rfl)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, natDegree_mul ha hprod, ih hs']

end DegInner

section ShiftAndResultant

noncomputable def scaleInner (lam : ℚ) : ℚ[X] →+* ℚ[X] :=
  eval₂RingHom C (C lam * Polynomial.X)

lemma scaleInner_C (lam q : ℚ) : scaleInner lam (C q) = C q := by
  simp [scaleInner]

lemma scaleInner_eval (lam y : ℚ) (p : ℚ[X]) :
    (scaleInner lam p).eval y = p.eval (lam * y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, scaleInner, coe_eval₂RingHom,
      eval₂_C, eval₂_X, eval_mul, eval_C, eval_pow, eval_mul, eval_C, eval_X,
      eval_mul, eval_C, eval_pow, eval_X]

lemma scaleInner_coeff (lam : ℚ) (p : ℚ[X]) (k : ℕ) :
    (scaleInner lam p).coeff k = lam ^ k * p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq, mul_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, scaleInner, coe_eval₂RingHom,
      eval₂_C, eval₂_X, mul_pow, ← C_pow, ← mul_assoc, mul_comm (C a), ← C_mul,
      coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with hkn
    · subst hkn; ring
    · ring

lemma scaleInner_natDegree (lam : ℚ) (hlam : lam ≠ 0) (p : ℚ[X]) :
    (scaleInner lam p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · subst hp; simp
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [scaleInner_coeff, coeff_eq_zero_of_natDegree_lt hN, mul_zero]
  · refine le_natDegree_of_ne_zero ?_
    rw [scaleInner_coeff]
    exact mul_ne_zero (pow_ne_zero _ hlam) (leadingCoeff_ne_zero.mpr hp)

lemma scaleInner_injective (lam : ℚ) (hlam : lam ≠ 0) :
    Function.Injective (scaleInner lam) := by
  intro p q hpq
  ext k
  have hk := congrArg (fun r : ℚ[X] => r.coeff k) hpq
  rw [scaleInner_coeff, scaleInner_coeff] at hk
  exact mul_left_cancel₀ (pow_ne_zero k hlam) hk

noncomputable def shiftPoly (f : (ℚ[X])[X]) (α lam : ℚ) : (ℚ[X])[X] :=
  (f.map (scaleInner lam)).comp (Polynomial.X + C (C α))

lemma shiftPoly_evalEval (f : (ℚ[X])[X]) (α lam y x : ℚ) :
    (shiftPoly f α lam).evalEval y x = f.evalEval (lam * y) (x + α) := by
  unfold shiftPoly evalEval
  rw [eval_comp, eval_add, eval_X, eval_C, ← C_add, eval_map]
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval₂_add, eval_add, hp, hq]
  | monomial n c =>
    simp only [← C_mul_X_pow_eq_monomial, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
      eval_mul, eval_C, eval_pow, eval_X, scaleInner_eval]

lemma shiftPoly_natDegree (f : (ℚ[X])[X]) (α lam : ℚ) (hlam : lam ≠ 0) :
    (shiftPoly f α lam).natDegree = f.natDegree := by
  unfold shiftPoly
  have h1 : (f.map (scaleInner lam)).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective (scaleInner_injective lam hlam) _
  have hdeg1 : (Polynomial.X + C (C α) : (ℚ[X])[X]).natDegree = 1 := natDegree_X_add_C _
  rw [natDegree_comp, h1, hdeg1, mul_one]

lemma degInner_shiftPoly_le (f : (ℚ[X])[X]) (α lam : ℚ) :
    degInner (shiftPoly f α lam) ≤ degInner f := by
  unfold shiftPoly
  rw [comp_eq_sum_left, sum_def]
  refine degInner_finset_sum_le _ _ _ fun i _ => ?_
  have h1 : degInner (C ((f.map (scaleInner lam)).coeff i)) ≤ degInner f := by
    rw [degInner_C, coeff_map]
    by_cases hlam : lam = 0
    · subst hlam
      have h0 : (scaleInner 0 (f.coeff i)).natDegree = 0 := by
        refine natDegree_eq_zero.mpr ⟨(f.coeff i).coeff 0, ?_⟩
        ext k
        cases k with
        | zero => simp [scaleInner_coeff]
        | succ k => simp [scaleInner_coeff]
      omega
    · rw [scaleInner_natDegree lam hlam]
      exact coeff_natDegree_le_degInner f i
  have h0 : degInner (Polynomial.X + C (C α) : (ℚ[X])[X]) = 0 := by
    have hle : degInner (Polynomial.X + C (C α) : (ℚ[X])[X]) ≤ 0 :=
      (degInner_add_le _ _).trans (max_le degInner_X.le (degInner_CC α).le)
    omega
  have h2 : degInner ((Polynomial.X + C (C α) : (ℚ[X])[X]) ^ i) = 0 := by
    have hle := degInner_pow_le (Polynomial.X + C (C α) : (ℚ[X])[X]) i
    rw [h0, mul_zero] at hle
    omega
  exact (degInner_mul_le _ _).trans (by omega)

lemma shiftPoly_coeff_top (f : (ℚ[X])[X]) (α lam : ℚ) :
    (shiftPoly f α lam).coeff f.natDegree = scaleInner lam (f.coeff f.natDegree) := by
  unfold shiftPoly
  set p := f.map (scaleInner lam)
  have hpdeg : p.natDegree ≤ f.natDegree := natDegree_map_le
  conv_lhs => rw [p.as_sum_range' (f.natDegree + 1) (Nat.lt_succ_of_le hpdeg)]
  simp only [← C_mul_X_pow_eq_monomial]
  rw [Polynomial.sum_comp, finsetSum_coeff]
  rw [Finset.sum_eq_single f.natDegree]
  · rw [mul_comp, C_comp, X_pow_comp, mul_comm, coeff_mul_C]
    have hmon : ((Polynomial.X + C (C α) : (ℚ[X])[X]) ^ f.natDegree).Monic :=
      (monic_X_add_C _).pow _
    have hdeg : ((Polynomial.X + C (C α) : (ℚ[X])[X]) ^ f.natDegree).natDegree = f.natDegree := by
      rw [natDegree_pow, natDegree_X_add_C, mul_one]
    have hlead := hmon.leadingCoeff
    rw [leadingCoeff, hdeg] at hlead
    rw [hlead, one_mul, coeff_map]
  · intro i hi hne
    have hilt : i < f.natDegree := by
      rw [Finset.mem_range] at hi; omega
    have hdeg : (C (p.coeff i) * (Polynomial.X + C (C α)) ^ i).natDegree < f.natDegree := by
      refine natDegree_mul_le.trans_lt ?_
      rw [natDegree_C, zero_add, natDegree_pow, natDegree_X_add_C, mul_one]
      exact hilt
    rw [mul_comp, C_comp, X_pow_comp, coeff_eq_zero_of_natDegree_lt hdeg]
  · intro h; simp at h

lemma coeff_X_add_C_pow_pred {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R] (c : R) :
    ∀ d : ℕ, 1 ≤ d → ((Polynomial.X + C c : R[X]) ^ d).coeff (d - 1) = (d : R) * c := by
  intro d hd
  induction d with
  | zero => omega
  | succ k ih =>
    rcases k with _ | k
    · simp
    · have hk : 1 ≤ k + 1 := by omega
      have ihk := ih hk
      rw [pow_succ, mul_add, coeff_add, mul_comm _ (C c), coeff_C_mul]
      have hx : (((Polynomial.X + C c : R[X]) ^ (k + 1)) * Polynomial.X).coeff (k + 1) =
          ((Polynomial.X + C c : R[X]) ^ (k + 1)).coeff k := by
        rw [coeff_mul_X]
      have hmon : ((Polynomial.X + C c : R[X]) ^ (k + 1)).Monic := (monic_X_add_C c).pow _
      have hdeg : ((Polynomial.X + C c : R[X]) ^ (k + 1)).natDegree = k + 1 := by
        rw [natDegree_pow, natDegree_X_add_C, mul_one]
      have hlead := hmon.leadingCoeff
      rw [leadingCoeff, hdeg] at hlead
      have ihk' : ((Polynomial.X + C c : R[X]) ^ (k + 1)).coeff k = ((k + 1 : ℕ) : R) * c := by
        simp only [Nat.add_sub_cancel] at ihk; exact ihk
      rw [show k + 1 + 1 - 1 = k + 1 by omega]
      rw [hx, ihk', hlead]
      push_cast
      ring

lemma shiftPoly_coeff_sub_one (f : (ℚ[X])[X]) (α lam : ℚ) (hf : 1 ≤ f.natDegree) :
    (shiftPoly f α lam).coeff (f.natDegree - 1) =
      (f.natDegree : ℚ[X]) * C α * scaleInner lam (f.coeff f.natDegree) +
        scaleInner lam (f.coeff (f.natDegree - 1)) := by
  unfold shiftPoly
  set d := f.natDegree
  set p := f.map (scaleInner lam)
  have hpdeg : p.natDegree ≤ d := natDegree_map_le
  conv_lhs => rw [p.as_sum_range' (d + 1) (Nat.lt_succ_of_le hpdeg)]
  simp only [← C_mul_X_pow_eq_monomial]
  rw [Polynomial.sum_comp]
  have hd_mem : d ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  have hd1_mem : d - 1 ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  have hd_ne : d - 1 ≠ d := by omega
  have hsum : ∑ i ∈ Finset.range (d + 1), (C (p.coeff i) * Polynomial.X ^ i).comp (Polynomial.X + C (C α)) =
      C (p.coeff d) * (Polynomial.X + C (C α)) ^ d +
      C (p.coeff (d - 1)) * (Polynomial.X + C (C α)) ^ (d - 1) +
      ∑ i ∈ ((Finset.range (d + 1)).erase d).erase (d - 1),
        (C (p.coeff i) * Polynomial.X ^ i).comp (Polynomial.X + C (C α)) := by
    have h1 := Finset.add_sum_erase (Finset.range (d + 1))
      (fun i => (C (p.coeff i) * Polynomial.X ^ i).comp (Polynomial.X + C (C α))) hd_mem
    have hd1_mem' : d - 1 ∈ (Finset.range (d + 1)).erase d := Finset.mem_erase.mpr ⟨hd_ne, hd1_mem⟩
    have h2 := Finset.add_sum_erase ((Finset.range (d + 1)).erase d)
      (fun i => (C (p.coeff i) * Polynomial.X ^ i).comp (Polynomial.X + C (C α))) hd1_mem'
    rw [← h1, ← h2, mul_comp, C_comp, X_pow_comp, mul_comp, C_comp, X_pow_comp]
    ring
  rw [hsum, coeff_add, coeff_add]
  have hrest : (∑ i ∈ ((Finset.range (d + 1)).erase d).erase (d - 1),
      (C (p.coeff i) * Polynomial.X ^ i).comp (Polynomial.X + C (C α))).coeff (d - 1) = 0 := by
    rw [finsetSum_coeff]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi1 : i ≠ d - 1 := (Finset.mem_erase.mp hi).1
    have hi2 : i ≠ d := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hi3 : i < d + 1 := Finset.mem_range.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2
    have hilt : i < d - 1 := by omega
    rw [mul_comp, C_comp, X_pow_comp]
    refine coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt ?_)
    rw [natDegree_C, zero_add, natDegree_pow, natDegree_X_add_C, mul_one]
    exact hilt
  have hterm_d1 : (C (p.coeff (d - 1)) * (Polynomial.X + C (C α)) ^ (d - 1)).coeff (d - 1) =
      p.coeff (d - 1) := by
    rw [mul_comm, coeff_mul_C]
    have hmon : ((Polynomial.X + C (C α) : (ℚ[X])[X]) ^ (d - 1)).Monic := (monic_X_add_C _).pow _
    have hdeg : ((Polynomial.X + C (C α) : (ℚ[X])[X]) ^ (d - 1)).natDegree = d - 1 := by
      rw [natDegree_pow, natDegree_X_add_C, mul_one]
    have hlead := hmon.leadingCoeff
    rw [leadingCoeff, hdeg] at hlead
    rw [hlead, one_mul]
  have hterm_d : ((Polynomial.X + C (C α) : (ℚ[X])[X]) ^ d).coeff (d - 1) = (d : ℚ[X]) * C α :=
    coeff_X_add_C_pow_pred (C α) d hf
  rw [hrest, add_zero, hterm_d1, mul_comm (C (p.coeff d)), coeff_mul_C, hterm_d]
  simp only [p, coeff_map]

lemma isPrimitive_of_irreducible_of_natDegree_pos {f : (ℚ[X])[X]} (hirr : Irreducible f)
    (hfdeg : 1 ≤ f.natDegree) : f.IsPrimitive := by
  rw [isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  obtain ⟨g, rfl⟩ := hr
  rcases hirr.isUnit_or_isUnit rfl with hu | hu
  · exact isUnit_C.mp hu
  · exfalso
    have hgdeg : g.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    have hr0 : r ≠ 0 := by rintro rfl; simp at hfdeg
    have hg0 : g ≠ 0 := hu.ne_zero
    rw [natDegree_mul (C_ne_zero.mpr hr0) hg0, natDegree_C, hgdeg] at hfdeg
    omega

lemma not_dvd_shiftPoly {f : (ℚ[X])[X]} (hirr : Irreducible f)
    (hfdeg : 1 ≤ f.natDegree) (hfinner : 1 ≤ degInner f)
    {α lam : ℚ} (hlam : 0 < lam) (hne : α ≠ 0 ∨ lam ≠ 1) :
    ¬ f ∣ shiftPoly f α lam := by
  intro ⟨h, hEq⟩
  have hf0 : f ≠ 0 := hirr.ne_zero
  have hs0 : shiftPoly f α lam ≠ 0 := by
    intro hs
    have h1 := shiftPoly_natDegree f α lam hlam.ne'
    rw [hs, natDegree_zero] at h1
    omega
  have hh0 : h ≠ 0 := by rintro rfl; simp at hEq; exact hs0 hEq
  have hdeg : h.natDegree = 0 := by
    have h1 := congrArg Polynomial.natDegree hEq
    rw [shiftPoly_natDegree f α lam hlam.ne', natDegree_mul hf0 hh0] at h1
    omega
  obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp hdeg
  have hc0 : c ≠ 0 := by rintro rfl; simp at hh0
  have hcd0 : c.natDegree = 0 := by
    have h1 := degInner_shiftPoly_le f α lam
    rw [hEq, degInner_mul_eq hf0 (C_ne_zero.mpr hc0), degInner_C] at h1
    omega
  obtain ⟨c₀, rfl⟩ := natDegree_eq_zero.mp hcd0
  have hc₀ : c₀ ≠ 0 := by rintro rfl; simp at hc0
  by_cases hα : α = 0
  · subst hα
    have hlam1 : lam ≠ 1 := hne.resolve_left (fun h => h rfl)
    have hmap : shiftPoly f 0 lam = f.map (scaleInner lam) := by
      simp [shiftPoly]
    rw [hmap] at hEq
    obtain ⟨i₀, hi₀, hdi₀, _⟩ := exists_max_degInner_index hf0
    set k₀ := (f.coeff i₀).natDegree
    have hk₀pos : 1 ≤ k₀ := by omega
    have hfk₀ : (f.coeff i₀).coeff k₀ ≠ 0 := by
      rw [← leadingCoeff, leadingCoeff_ne_zero]
      exact mem_support_iff.mp hi₀
    have hc₀eq : c₀ = lam ^ k₀ := by
      have hi := congrArg (fun p : (ℚ[X])[X] => (p.coeff i₀).coeff k₀) hEq
      rw [coeff_map, scaleInner_coeff, mul_comm f, coeff_C_mul, coeff_C_mul] at hi
      exact mul_right_cancel₀ hfk₀ hi.symm
    have hcoeff0 : ∀ i, (f.coeff i).coeff 0 = 0 := by
      intro i
      have hi := congrArg (fun p : (ℚ[X])[X] => (p.coeff i).coeff 0) hEq
      rw [coeff_map, scaleInner_coeff, pow_zero, one_mul, mul_comm f, coeff_C_mul, coeff_C_mul,
        hc₀eq] at hi
      have hlamk : lam ^ k₀ ≠ 1 := by
        rcases lt_or_gt_of_ne hlam1 with hl | hg
        · exact (pow_lt_one₀ hlam.le hl (by omega)).ne
        · exact (one_lt_pow₀ hg (by omega)).ne'
      have hmul0 : (1 - lam ^ k₀) * (f.coeff i).coeff 0 = 0 := by linarith
      exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hlamk.symm)
    have hdvdX : C Polynomial.X ∣ f := by
      have heqX : f = C Polynomial.X * ∑ i ∈ Finset.range (f.natDegree + 1),
          C (f.coeff i /ₘ Polynomial.X) * Polynomial.X ^ i := by
        conv_lhs => rw [f.as_sum_range_C_mul_X_pow]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hdvd_i : Polynomial.X ∣ f.coeff i := X_dvd_iff.mpr (hcoeff0 i)
        obtain ⟨q, hq⟩ := hdvd_i
        have hq' : f.coeff i /ₘ Polynomial.X = q := by
          rw [hq, mul_divByMonic_cancel_left _ monic_X]
        rw [hq', hq, C_mul]
        ring
      exact ⟨_, heqX⟩
    obtain ⟨g, hg⟩ := hdvdX
    rcases hirr.isUnit_or_isUnit hg with hu | hu
    · have hXunit : IsUnit (Polynomial.X : ℚ[X]) := isUnit_C.mp hu
      have := Polynomial.natDegree_eq_zero_of_isUnit hXunit
      simp at this
    · have hgdeg : g.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
      have hg0 : g ≠ 0 := hu.ne_zero
      have hdegf := congrArg Polynomial.natDegree hg
      rw [natDegree_mul (C_ne_zero.mpr X_ne_zero) hg0, natDegree_C, hgdeg, zero_add] at hdegf
      omega
  · have htop := congrArg (fun p : (ℚ[X])[X] => p.coeff f.natDegree) hEq
    rw [shiftPoly_coeff_top, mul_comm f, coeff_C_mul] at htop
    set d := f.natDegree
    set k := (f.coeff d).natDegree
    set γ := (f.coeff d).coeff k
    have hfd0 : f.coeff d ≠ 0 := leadingCoeff_ne_zero.mpr hf0
    have hγ0 : γ ≠ 0 := leadingCoeff_ne_zero.mpr hfd0
    have hc₀eq : c₀ = lam ^ k := by
      have hk := congrArg (fun p : ℚ[X] => p.coeff k) htop
      rw [scaleInner_coeff, coeff_C_mul] at hk
      exact mul_right_cancel₀ hγ0 hk.symm
    have hsub1 := congrArg (fun p : (ℚ[X])[X] => p.coeff (d - 1)) hEq
    rw [shiftPoly_coeff_sub_one f α lam hfdeg, mul_comm f, coeff_C_mul] at hsub1
    have hk1 := congrArg (fun p : ℚ[X] => p.coeff k) hsub1
    have hnat_mul : (d : ℚ[X]) * C α * scaleInner lam (f.coeff d) =
        C ((d : ℚ) * α) * scaleInner lam (f.coeff d) := by
      rw [← map_natCast C d, ← C_mul]
    rw [coeff_add, hnat_mul, coeff_C_mul, scaleInner_coeff, scaleInner_coeff, coeff_C_mul,
      hc₀eq] at hk1
    have hzero : (d : ℚ) * α * lam ^ k * γ = 0 := by linarith
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hlamk0 : lam ^ k ≠ 0 := pow_ne_zero k hlam.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hd0 hα) hlamk0) hγ0 hzero

lemma resultant_shiftPoly_ne_zero {f : (ℚ[X])[X]} (hirr : Irreducible f)
    (hfdeg : 1 ≤ f.natDegree) (hfinner : 1 ≤ degInner f)
    {α lam : ℚ} (hlam : 0 < lam) (hne : α ≠ 0 ∨ lam ≠ 1) :
    f.resultant (shiftPoly f α lam) ≠ 0 := by
  let K := FractionRing (ℚ[X])
  let φ : ℚ[X] →+* K := algebraMap (ℚ[X]) K
  have hprim : f.IsPrimitive := isPrimitive_of_irreducible_of_natDegree_pos hirr hfdeg
  have hirrK : Irreducible (f.map φ) := hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hndvd : ¬ f.map φ ∣ (shiftPoly f α lam).map φ := by
    rw [← hprim.dvd_iff_fraction_map_dvd_fraction_map K]
    exact not_dvd_shiftPoly hirr hfdeg hfinner hlam hne
  have hcop : IsCoprime (f.map φ) ((shiftPoly f α lam).map φ) :=
    (hirrK.isCoprime_or_dvd _).resolve_right hndvd
  have hresK : (f.map φ).resultant ((shiftPoly f α lam).map φ) ≠ 0 :=
    resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective (IsFractionRing.injective _ _),
    natDegree_map_eq_of_injective (IsFractionRing.injective _ _),
    resultant_map_map] at hresK
  intro h0
  rw [h0, map_zero] at hresK
  exact hresK rfl

lemma natDegree_resultant_le (f g : (ℚ[X])[X]) :
    (f.resultant g).natDegree ≤ f.natDegree * degInner g + g.natDegree * degInner f := by
  unfold resultant
  set m := f.natDegree
  set n := g.natDegree
  set M := f.sylvester g m n
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _
    (fun σ => Equiv.Perm.sign σ • ∏ i : Fin (m + n), M (σ i) i) fun σ _ => ?_
  have hsign : (Equiv.Perm.sign σ • ∏ i : Fin (m + n), M (σ i) i).natDegree =
      (∏ i : Fin (m + n), M (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hsign]
  have hprod : ∏ i : Fin (m + n), M (σ i) i =
      (∏ j₁ : Fin m, M (σ (Fin.castAdd n j₁)) (Fin.castAdd n j₁)) *
      (∏ j₂ : Fin n, M (σ (Fin.natAdd m j₂)) (Fin.natAdd m j₂)) := by
    rw [← finSumFinEquiv.prod_comp (fun i => M (σ i) i), Fintype.prod_sum_type]
    rfl
  rw [hprod]
  refine natDegree_mul_le.trans (Nat.add_le_add ?_ ?_)
  · refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    calc ∑ j₁ : Fin m, (M (σ (Fin.castAdd n j₁)) (Fin.castAdd n j₁)).natDegree
        ≤ ∑ _j₁ : Fin m, degInner g := Finset.sum_le_sum fun j₁ _ => ?_
      _ = m * degInner g := by simp
    simp only [M, sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact coeff_natDegree_le_degInner g _
    · simp
  · refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    calc ∑ j₂ : Fin n, (M (σ (Fin.natAdd m j₂)) (Fin.natAdd m j₂)).natDegree
        ≤ ∑ _j₂ : Fin n, degInner f := Finset.sum_le_sum fun j₂ _ => ?_
      _ = n * degInner f := by simp
    simp only [M, sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact coeff_natDegree_le_degInner f _
    · simp

end ShiftAndResultant

section ZeroLemmaMain

lemma card_eval_root_X_only {f : (ℚ[X])[X]} (hf0 : f ≠ 0) (hfinner : degInner f = 0)
    {m : ℤ} (hm : 0 < m) (R1 S1 : ℕ) :
    ((Finset.range R1 ×ˢ Finset.range S1).filter fun rs : ℕ × ℕ =>
      f.evalEval 1 ((rs.1 : ℚ) + (rs.2 : ℚ) * m) = 0).card ≤
      f.natDegree * (R1 / m.natAbs + 1) := by
  classical
  set f₀ : ℚ[X] := f.map (evalRingHom 1)
  have hf_eq : f = f₀.map C := by
    ext i j
    simp only [f₀, coeff_map, coe_evalRingHom]
    have hdeg0 : (f.coeff i).natDegree = 0 := by
      have := coeff_natDegree_le_degInner f i
      omega
    obtain ⟨q, hq⟩ := natDegree_eq_zero.mp hdeg0
    rw [← hq, eval_C]
  have hf₀_ne : f₀ ≠ 0 := by
    intro h0
    rw [h0, Polynomial.map_zero] at hf_eq
    exact hf0 hf_eq
  have hf₀_deg : f₀.natDegree = f.natDegree := by
    conv_rhs => rw [hf_eq]
    exact (natDegree_map_eq_of_injective C_injective f₀).symm
  have heval : ∀ (rs : ℕ × ℕ),
      f.evalEval 1 ((rs.1 : ℚ) + (rs.2 : ℚ) * m) = 0 ↔
      ((rs.1 : ℚ) + (rs.2 : ℚ) * m) ∈ f₀.roots := by
    intro rs
    rw [mem_roots hf₀_ne, IsRoot.def]
    conv_lhs => rw [hf_eq, evalEval_map_C]
  let G := Finset.range R1 ×ˢ Finset.range S1
  let Z := G.filter fun rs : ℕ × ℕ => f.evalEval 1 ((rs.1 : ℚ) + (rs.2 : ℚ) * m) = 0
  have hsub : Z ⊆ f₀.roots.toFinset.biUnion fun x₀ =>
      G.filter fun rs : ℕ × ℕ => (rs.1 : ℚ) + (rs.2 : ℚ) * m = x₀ := by
    intro rs hrs
    rw [Finset.mem_filter] at hrs
    rw [Finset.mem_biUnion]
    refine ⟨(rs.1 : ℚ) + (rs.2 : ℚ) * m, ?_, Finset.mem_filter.mpr ⟨hrs.1, rfl⟩⟩
    exact Multiset.mem_toFinset.mpr ((heval rs).mp hrs.2)
  have hcard1 : Z.card ≤ ∑ x₀ ∈ f₀.roots.toFinset,
      (G.filter fun rs : ℕ × ℕ => (rs.1 : ℚ) + (rs.2 : ℚ) * m = x₀).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hfiber : ∀ x₀ : ℚ,
      (G.filter fun rs : ℕ × ℕ => (rs.1 : ℚ) + (rs.2 : ℚ) * m = x₀).card ≤ R1 / m.natAbs + 1 := by
    intro x₀
    set F := G.filter fun rs : ℕ × ℕ => (rs.1 : ℚ) + (rs.2 : ℚ) * m = x₀
    by_cases hFe : F.Nonempty
    · obtain ⟨rs₀, hrs₀⟩ := hFe
      let Sset := F.image Prod.snd
      have hS_ne : Sset.Nonempty := ⟨rs₀.2, Finset.mem_image_of_mem _ hrs₀⟩
      let s₀ := Sset.min' hS_ne
      obtain ⟨rs_min, hrs_min, hs_min⟩ := Finset.mem_image.mp (Finset.min'_mem Sset hS_ne)
      have hF_inj : F.card ≤ Sset.card := by
        refine Finset.card_le_card_of_injOn Prod.snd (fun _ h => Finset.mem_image_of_mem _ h) ?_
        intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        have hreq : (a.1 : ℚ) = (b.1 : ℚ) := by
          have : a.2 = b.2 := hab
          rw [this] at ha'
          linarith
        have har : a.1 = b.1 := by exact_mod_cast hreq
        exact Prod.ext har hab
      have hSsub : Sset ⊆ Finset.Icc s₀ (s₀ + R1 / m.natAbs) := by
        intro s hs
        obtain ⟨rs, hrs, rfl⟩ := Finset.mem_image.mp hs
        have hmin_le : s₀ ≤ rs.2 := Finset.min'_le Sset rs.2 hs
        have hmem_rs := Finset.mem_filter.mp hrs
        have hmem_min := Finset.mem_filter.mp hrs_min
        have hr_lt : rs.1 < R1 := Finset.mem_range.mp (Finset.mem_product.mp hmem_rs.1).1
        have hrm_lt : rs_min.1 < R1 := Finset.mem_range.mp (Finset.mem_product.mp hmem_min.1).1
        have heq_q : (rs.1 : ℚ) + (rs.2 : ℚ) * m = (rs_min.1 : ℚ) + (rs_min.2 : ℚ) * m :=
          hmem_rs.2.trans hmem_min.2.symm
        have heq_z : (rs.1 : ℤ) + (rs.2 : ℤ) * m = (rs_min.1 : ℤ) + (rs_min.2 : ℤ) * m := by
          exact_mod_cast heq_q
        have hm_eq : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm.le
        have hs_diff : (rs.2 - s₀) * m.natAbs < R1 := by
          have h1 : ((rs.2 - s₀ : ℕ) : ℤ) * m.natAbs = (rs_min.1 : ℤ) - rs.1 := by
            rw [Nat.cast_sub hmin_le, hm_eq, show (s₀ : ℤ) = rs_min.2 by rw [hs_min]]
            linarith
          have h2 : (((rs.2 - s₀ : ℕ) * m.natAbs : ℕ) : ℤ) < R1 := by
            rw [Nat.cast_mul, h1]; omega
          exact_mod_cast h2
        have hm_pos : 0 < m.natAbs := Int.natAbs_pos.mpr hm.ne'
        have hdiv : rs.2 - s₀ ≤ R1 / m.natAbs := by
          have : rs.2 - s₀ ≤ (R1 - 1) / m.natAbs := by
            rw [Nat.le_div_iff_mul_le hm_pos]
            exact Nat.le_pred_of_lt hs_diff
          exact this.trans (Nat.div_le_div_right (by omega))
        exact Finset.mem_Icc.mpr ⟨hmin_le, by omega⟩
      have hScard : Sset.card ≤ R1 / m.natAbs + 1 := by
        have h1 : Sset.card ≤ (Finset.Icc s₀ (s₀ + R1 / m.natAbs)).card :=
          Finset.card_le_card hSsub
        rw [Nat.card_Icc, add_assoc, Nat.add_sub_cancel_left] at h1
        exact h1
      exact hF_inj.trans hScard
    · rw [Finset.not_nonempty_iff_eq_empty] at hFe
      rw [hFe, Finset.card_empty]
      exact Nat.zero_le _
  have hroots : f₀.roots.toFinset.card ≤ f.natDegree := by
    rw [← hf₀_deg]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' f₀)
  calc Z.card ≤ ∑ _x₀ ∈ f₀.roots.toFinset, (R1 / m.natAbs + 1) :=
        hcard1.trans (Finset.sum_le_sum fun x₀ _ => hfiber x₀)
    _ = f₀.roots.toFinset.card * (R1 / m.natAbs + 1) := by simp
    _ ≤ f.natDegree * (R1 / m.natAbs + 1) := Nat.mul_le_mul_right _ hroots

private lemma card_Z_FM_sq {u v : ℚ} (hu : 0 < u) (hv : 0 < v)
    (hind : ∀ a b : ℤ, u ^ a * v ^ b = 1 → a = 0 ∧ b = 0)
    (hind_nat : ∀ p₁ p₂ : ℕ × ℕ, u ^ p₁.1 * v ^ p₁.2 = u ^ p₂.1 * v ^ p₂.2 → p₁ = p₂)
    {m : ℤ} {R1 S1 : ℕ} (hR1 : 1 ≤ R1) (hS1 : 1 ≤ S1)
    {f : (ℚ[X])[X]} (hirr : Irreducible f) (hfdeg : 1 ≤ f.natDegree) (hfinner : 1 ≤ degInner f)
    {Zf : Finset (ℕ × ℕ)} (hZf_sub : Zf ⊆ Finset.range R1 ×ˢ Finset.range S1)
    (hZf_eval : ∀ rs ∈ Zf, f.evalEval (u ^ rs.1 * v ^ rs.2) ((rs.1 : ℚ) + (rs.2 : ℚ) * m) = 0) :
    Zf.card ^ 2 ≤ 16 * R1 * S1 * f.natDegree * degInner f := by
  classical
  by_cases hsmall : Zf.card ≤ 1
  · have h1 : Zf.card ^ 2 ≤ 1 := by nlinarith
    have hp : 0 < R1 * S1 * f.natDegree * degInner f :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hR1 hS1) hfdeg) hfinner
    have h2 : 1 ≤ 16 * R1 * S1 * f.natDegree * degInner f := by
      calc 1 ≤ R1 * S1 * f.natDegree * degInner f := hp
        _ ≤ 16 * (R1 * S1 * f.natDegree * degInner f) := Nat.le_mul_of_pos_left _ (by norm_num)
        _ = 16 * R1 * S1 * f.natDegree * degInner f := by ring
    exact h1.trans h2
  have hpairs_le : Zf.card * Zf.card - Zf.card ≤ 8 * R1 * S1 * f.natDegree * degInner f := by
    let Δ := Finset.Ioo (-(R1 : ℤ)) (R1 : ℤ) ×ˢ Finset.Ioo (-(S1 : ℤ)) (S1 : ℤ)
    let Δ' := Δ.erase (0, 0)
    let Pairs := Zf.offDiag
    let diff : (ℕ × ℕ) × (ℕ × ℕ) → ℤ × ℤ := fun pp =>
      ((pp.2.1 : ℤ) - pp.1.1, (pp.2.2 : ℤ) - pp.1.2)
    have hsub_pairs : Pairs ⊆ Δ'.biUnion fun δ => Pairs.filter fun pp => diff pp = δ := by
      intro pp hpp
      have hmem := Finset.mem_offDiag.mp hpp
      have hp1G := hZf_sub hmem.1
      have hp2G := hZf_sub hmem.2.1
      have hp1r := Finset.mem_range.mp (Finset.mem_product.mp hp1G).1
      have hp1s := Finset.mem_range.mp (Finset.mem_product.mp hp1G).2
      have hp2r := Finset.mem_range.mp (Finset.mem_product.mp hp2G).1
      have hp2s := Finset.mem_range.mp (Finset.mem_product.mp hp2G).2
      have hne0 : diff pp ≠ (0, 0) := by
        intro hd
        have hr_eq : pp.1.1 = pp.2.1 := by
          have := congrArg Prod.fst hd; dsimp [diff] at this; omega
        have hs_eq : pp.1.2 = pp.2.2 := by
          have := congrArg Prod.snd hd; dsimp [diff] at this; omega
        exact hmem.2.2 (Prod.ext hr_eq hs_eq)
      have hδΔ : diff pp ∈ Δ := by
        dsimp [diff, Δ]
        exact Finset.mem_product.mpr
          ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩⟩
      exact Finset.mem_biUnion.mpr ⟨diff pp, Finset.mem_erase.mpr ⟨hne0, hδΔ⟩,
        Finset.mem_filter.mpr ⟨hpp, rfl⟩⟩
    have hfiber_le : ∀ δ ∈ Δ', (Pairs.filter fun pp => diff pp = δ).card ≤
        2 * f.natDegree * degInner f := by
      intro δ hδ
      have hδ0 : δ ≠ (0, 0) := (Finset.mem_erase.mp hδ).1
      let α := (δ.1 : ℚ) + (δ.2 : ℚ) * m
      let lam := u ^ δ.1 * v ^ δ.2
      have hlam_pos : 0 < lam := mul_pos (zpow_pos hu _) (zpow_pos hv _)
      have hlam_ne1 : lam ≠ 1 := by
        intro h1
        obtain ⟨h1', h2'⟩ := hind δ.1 δ.2 h1
        exact hδ0 (Prod.ext h1' h2')
      let g := shiftPoly f α lam
      let Res := f.resultant g
      have hRes_ne0 : Res ≠ 0 :=
        resultant_shiftPoly_ne_zero hirr hfdeg hfinner hlam_pos (Or.inr hlam_ne1)
      have hRes_deg : Res.natDegree ≤ 2 * f.natDegree * degInner f := by
        calc Res.natDegree
            ≤ f.natDegree * degInner g + g.natDegree * degInner f := natDegree_resultant_le f g
          _ ≤ f.natDegree * degInner f + f.natDegree * degInner f := by
              rw [shiftPoly_natDegree f α lam hlam_pos.ne']
              exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (degInner_shiftPoly_le f α lam)) _
          _ = 2 * f.natDegree * degInner f := by ring
      let φ : (ℕ × ℕ) × (ℕ × ℕ) → ℚ := fun pp => u ^ pp.1.1 * v ^ pp.1.2
      have hinj : Set.InjOn φ (Pairs.filter fun pp => diff pp = δ) := by
        intro pp₁ hpp₁ pp₂ hpp₂ heq
        have hd1 := (Finset.mem_filter.mp hpp₁).2
        have hd2 := (Finset.mem_filter.mp hpp₂).2
        have hp1eq : pp₁.1 = pp₂.1 := hind_nat pp₁.1 pp₂.1 heq
        have hr2 : pp₁.2.1 = pp₂.2.1 := by
          have := congrArg Prod.fst (hd1.trans hd2.symm)
          dsimp [diff] at this; rw [hp1eq] at this; omega
        have hs2 : pp₁.2.2 = pp₂.2.2 := by
          have := congrArg Prod.snd (hd1.trans hd2.symm)
          dsimp [diff] at this; rw [hp1eq] at this; omega
        exact Prod.ext hp1eq (Prod.ext hr2 hs2)
      have hmaps : ∀ pp ∈ Pairs.filter fun pp => diff pp = δ, φ pp ∈ Res.roots.toFinset := by
        intro pp hpp
        have hmem := Finset.mem_filter.mp hpp
        have hpp_mem := Finset.mem_offDiag.mp hmem.1
        have hp1Z := hZf_eval pp.1 hpp_mem.1
        have hp2Z := hZf_eval pp.2 hpp_mem.2.1
        have hdiff := hmem.2
        have hdr : δ.1 = (pp.2.1 : ℤ) - pp.1.1 := by
          have := congrArg Prod.fst hdiff; exact this.symm
        have hds : δ.2 = (pp.2.2 : ℤ) - pp.1.2 := by
          have := congrArg Prod.snd hdiff; exact this.symm
        obtain ⟨a, b, _, _, hab⟩ := exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl
          (Or.inl (Nat.ne_of_gt hfdeg))
        have hev := congrArg (evalEval (φ pp) ((pp.1.1 : ℚ) + (pp.1.2 : ℚ) * m)) hab
        rw [evalEval_add, evalEval_mul, evalEval_mul, evalEval_C, hp1Z, zero_mul, zero_add] at hev
        have hlam_eq : lam * φ pp = u ^ pp.2.1 * v ^ pp.2.2 := by
          dsimp [lam, φ]
          rw [hdr, hds, zpow_sub₀ hu.ne', zpow_sub₀ hv.ne',
            zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast]
          have hu1 : u ^ pp.1.1 ≠ 0 := pow_ne_zero _ hu.ne'
          have hv1 : v ^ pp.1.2 ≠ 0 := pow_ne_zero _ hv.ne'
          field_simp
        have hα_eq : (pp.1.1 : ℚ) + (pp.1.2 : ℚ) * m + α = (pp.2.1 : ℚ) + (pp.2.2 : ℚ) * m := by
          dsimp [α]
          rw [hdr, hds]
          push_cast
          ring
        have hgev : g.evalEval (φ pp) ((pp.1.1 : ℚ) + (pp.1.2 : ℚ) * m) = 0 := by
          rw [shiftPoly_evalEval, hlam_eq, hα_eq, hp2Z]
        rw [hgev, zero_mul] at hev
        exact Multiset.mem_toFinset.mpr ((mem_roots hRes_ne0).mpr hev.symm)
      calc (Pairs.filter fun pp => diff pp = δ).card
          ≤ Res.roots.toFinset.card := Finset.card_le_card_of_injOn φ hmaps hinj
        _ ≤ Res.natDegree := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' Res)
        _ ≤ 2 * f.natDegree * degInner f := hRes_deg
    have hΔ_card : Δ'.card ≤ 4 * R1 * S1 := by
      have h1 : Δ'.card ≤ Δ.card := Finset.card_le_card (Finset.erase_subset _ _)
      have hIooR : (Finset.Ioo (-(R1 : ℤ)) (R1 : ℤ)).card ≤ 2 * R1 := by
        rw [Int.card_Ioo, ← Int.ofNat_le, Int.toNat_of_nonneg (by omega)]
        omega
      have hIooS : (Finset.Ioo (-(S1 : ℤ)) (S1 : ℤ)).card ≤ 2 * S1 := by
        rw [Int.card_Ioo, ← Int.ofNat_le, Int.toNat_of_nonneg (by omega)]
        omega
      have h2 : Δ.card ≤ 4 * R1 * S1 := by
        rw [Finset.card_product]
        calc (Finset.Ioo (-(R1 : ℤ)) (R1 : ℤ)).card * (Finset.Ioo (-(S1 : ℤ)) (S1 : ℤ)).card
            ≤ (2 * R1) * (2 * S1) := Nat.mul_le_mul hIooR hIooS
          _ = 4 * R1 * S1 := by ring
      exact h1.trans h2
    have hPcard : Pairs.card = Zf.card * Zf.card - Zf.card := Finset.offDiag_card Zf
    calc Zf.card * Zf.card - Zf.card
        = Pairs.card := hPcard.symm
      _ ≤ ∑ δ ∈ Δ', (Pairs.filter fun pp => diff pp = δ).card :=
          (Finset.card_le_card hsub_pairs).trans Finset.card_biUnion_le
      _ ≤ ∑ _δ ∈ Δ', (2 * f.natDegree * degInner f) := Finset.sum_le_sum hfiber_le
      _ = Δ'.card * (2 * f.natDegree * degInner f) := by simp
      _ ≤ (4 * R1 * S1) * (2 * f.natDegree * degInner f) := Nat.mul_le_mul_right _ hΔ_card
      _ = 8 * R1 * S1 * f.natDegree * degInner f := by ring
  have hZ2 : 2 ≤ Zf.card := by omega
  have hmul : Zf.card ≤ Zf.card * Zf.card := Nat.le_mul_self _
  have hmul2 : 2 * Zf.card ≤ Zf.card * Zf.card := by nlinarith
  have hsq_le : Zf.card ^ 2 ≤ 2 * (Zf.card * Zf.card - Zf.card) := by
    have h1 : Zf.card ^ 2 = Zf.card * Zf.card := sq _
    have hsub : Zf.card * Zf.card = (Zf.card * Zf.card - Zf.card) + Zf.card :=
      (Nat.sub_add_cancel hmul).symm
    nlinarith
  calc Zf.card ^ 2
      ≤ 2 * (Zf.card * Zf.card - Zf.card) := hsq_le
    _ ≤ 2 * (8 * R1 * S1 * f.natDegree * degInner f) := Nat.mul_le_mul_left 2 hpairs_le
    _ = 16 * R1 * S1 * f.natDegree * degInner f := by ring

theorem zero_lemma {u v : ℚ} (hu : 0 < u) (hv : 0 < v)
    (hind : ∀ a b : ℤ, u ^ a * v ^ b = 1 → a = 0 ∧ b = 0)
    {m : ℤ} (hm : 0 < m) (_huv : u ^ m ≠ v)
    {I J R1 S1 : ℕ} (hI : 1 ≤ I) (hJ : 1 ≤ J) (hR1 : 1 ≤ R1) (hS1 : 1 ≤ S1)
    (hRS : 64 * I * J ≤ R1 * S1) (hSJ : 16 * J ≤ S1) (hSm : 4 * I ≤ S1 * m.natAbs)
    (p : ℕ → ℕ → ℤ) (hp : ∃ i < I, ∃ j < J, p i j ≠ 0) :
    ∃ r < R1, ∃ s < S1,
      ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
        (p i j : ℚ) * ((r : ℚ) + (s : ℚ) * m) ^ i * u ^ (j * r) * v ^ (j * s) ≠ 0 := by
  classical
  set P : (ℚ[X])[X] :=
    ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
      C (C (p i j : ℚ) * Polynomial.X ^ j) * Polynomial.X ^ i
  have hPeval : ∀ (r s : ℕ),
      P.evalEval (u ^ r * v ^ s) ((r : ℚ) + (s : ℚ) * m) =
      ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
        (p i j : ℚ) * ((r : ℚ) + (s : ℚ) * m) ^ i * u ^ (j * r) * v ^ (j * s) := by
    intro r s
    simp only [P, evalEval_finsetSum, evalEval_mul, evalEval_C, eval_mul, eval_C, eval_pow,
      eval_X, evalEval_pow, evalEval_X]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm r j, mul_comm s j]
    ring
  by_contra hvan
  push Not at hvan
  obtain ⟨i₀, hi₀I, j₀, hj₀J, hp₀⟩ := hp
  have hPcoeff : ∀ i j, (P.coeff i).coeff j = if i < I ∧ j < J then (p i j : ℚ) else 0 := by
    have hterm : ∀ k l i j, ((C (C (p k l : ℚ) * Polynomial.X ^ l) * Polynomial.X ^ k).coeff i).coeff j =
        if i = k ∧ j = l then (p k l : ℚ) else 0 := by
      intro k l i j
      rw [coeff_C_mul_X_pow]
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl, coeff_C_mul_X_pow]
        by_cases hjl : j = l
        · subst hjl; simp
        · rw [if_neg hjl, if_neg (fun h => hjl h.2)]
      · rw [if_neg hik, coeff_zero, if_neg (fun h => hik h.1)]
    intro i j
    simp only [P, finsetSum_coeff]
    by_cases hi : i < I
    · rw [Finset.sum_eq_single i]
      · simp only [hi, true_and]
        by_cases hj : j < J
        · rw [Finset.sum_eq_single j]
          · rw [hterm i j i j, if_pos ⟨rfl, rfl⟩, if_pos hj]
          · intro l _ hlj
            have hneq : ¬ (i = i ∧ j = l) := fun h => hlj h.2.symm
            rw [hterm i l i j, if_neg hneq]
          · intro hj'; exact absurd (Finset.mem_range.mpr hj) hj'
        · rw [if_neg hj]
          exact Finset.sum_eq_zero fun l hl => by
            have hl' : l < J := Finset.mem_range.mp hl
            have hneq : ¬ (i = i ∧ j = l) := fun h => hj (h.2 ▸ hl')
            rw [hterm i l i j, if_neg hneq]
      · intro k _ hki
        exact Finset.sum_eq_zero fun l _ => by
          have hneq : ¬ (i = k ∧ j = l) := fun h => hki h.1.symm
          rw [hterm k l i j, if_neg hneq]
      · intro hi'; exact absurd (Finset.mem_range.mpr hi) hi'
    · rw [if_neg (fun h => hi h.1)]
      exact Finset.sum_eq_zero fun k hk => by
        have hk' : k < I := Finset.mem_range.mp hk
        exact Finset.sum_eq_zero fun l _ => by
          have hneq : ¬ (i = k ∧ j = l) := fun h => hi (h.1 ▸ hk')
          rw [hterm k l i j, if_neg hneq]
  have hP0 : P ≠ 0 := by
    intro h0
    have := congrArg (fun q : (ℚ[X])[X] => (q.coeff i₀).coeff j₀) h0
    rw [hPcoeff, if_pos ⟨hi₀I, hj₀J⟩] at this
    simp only [coeff_zero, Int.cast_eq_zero] at this
    exact hp₀ this
  have hP_degX : P.natDegree < I := by
    refine (natDegree_sum_le_of_forall_le (n := I - 1) _
      (fun i => ∑ j ∈ Finset.range J, C (C (p i j : ℚ) * Polynomial.X ^ j) * Polynomial.X ^ i)
      fun i hi => ?_).trans_lt (by omega)
    refine natDegree_sum_le_of_forall_le (n := I - 1) _
      (fun j => C (C (p i j : ℚ) * Polynomial.X ^ j) * Polynomial.X ^ i) fun j _ => ?_
    refine natDegree_mul_le.trans ?_
    rw [natDegree_C, zero_add, natDegree_X_pow]
    have hi_lt : i < I := Finset.mem_range.mp hi
    omega
  have hP_degY : degInner P < J := by
    refine (degInner_finset_sum_le _ _ (J - 1) fun i _ => ?_).trans_lt (by omega)
    refine degInner_finset_sum_le _ _ (J - 1) fun j hj => ?_
    have hj_lt : j < J := Finset.mem_range.mp hj
    have hx_pow : degInner ((Polynomial.X : (ℚ[X])[X]) ^ i) ≤ 0 := by
      have h1 := degInner_pow_le (Polynomial.X : (ℚ[X])[X]) i
      rw [degInner_X, mul_zero] at h1
      exact h1
    have hc_le : degInner (C (C (p i j : ℚ) * Polynomial.X ^ j)) ≤ j := by
      rw [degInner_C]
      exact natDegree_mul_le.trans (by rw [natDegree_C, zero_add, natDegree_X_pow])
    exact (degInner_mul_le _ _).trans (by omega)
  have hind_nat : ∀ p₁ p₂ : ℕ × ℕ,
      u ^ p₁.1 * v ^ p₁.2 = u ^ p₂.1 * v ^ p₂.2 → p₁ = p₂ := by
    intro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ h
    have hq : u ^ ((r₁ : ℤ) - r₂) * v ^ ((s₁ : ℤ) - s₂) = 1 := by
      rw [zpow_sub₀ hu.ne', zpow_sub₀ hv.ne', zpow_natCast, zpow_natCast,
        zpow_natCast, zpow_natCast]
      have hne : u ^ r₂ * v ^ s₂ ≠ 0 := mul_ne_zero (pow_ne_zero _ hu.ne') (pow_ne_zero _ hv.ne')
      rw [div_mul_div_comm, h, div_self hne]
    obtain ⟨hr, hs⟩ := hind _ _ hq
    exact Prod.ext (by omega) (by omega)
  let factorsP := UniqueFactorizationMonoid.factors P
  let F : Finset ((ℚ[X])[X]) := factorsP.toFinset
  have hfac_ne0 : ∀ f ∈ factorsP, f ≠ 0 := fun f hf =>
    (UniqueFactorizationMonoid.irreducible_of_factor f hf).ne_zero
  obtain ⟨u₀, hu₀⟩ := UniqueFactorizationMonoid.factors_prod hP0
  have hu₀_degX : (u₀ : (ℚ[X])[X]).natDegree = 0 := natDegree_eq_zero_of_isUnit u₀.isUnit
  obtain ⟨c₀, hc₀⟩ := natDegree_eq_zero.mp hu₀_degX
  have hc₀_unit : IsUnit c₀ := isUnit_C.mp (hc₀ ▸ u₀.isUnit)
  have hc₀_deg : c₀.natDegree = 0 := natDegree_eq_zero_of_isUnit hc₀_unit
  obtain ⟨q₀, hq₀⟩ := natDegree_eq_zero.mp hc₀_deg
  have hq₀_ne : q₀ ≠ 0 := by
    rintro rfl
    have : (u₀ : (ℚ[X])[X]) = 0 := by rw [← hc₀, ← hq₀, C_0, C_0]
    exact u₀.ne_zero this
  have hsum_toFinset : ∀ (s : Multiset ((ℚ[X])[X])) (g : (ℚ[X])[X] → ℕ),
      ∑ x ∈ s.toFinset, g x ≤ (s.map g).sum := by
    intro s g
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      by_cases ha : a ∈ s
      · rw [Multiset.toFinset_cons, Finset.insert_eq_of_mem (Multiset.mem_toFinset.mpr ha),
          Multiset.map_cons, Multiset.sum_cons]
        omega
      · rw [Multiset.toFinset_cons,
          Finset.sum_insert (fun h => ha (Multiset.mem_toFinset.mp h)),
          Multiset.map_cons, Multiset.sum_cons]
        omega
  have hF_degX_sum : ∑ f ∈ F, f.natDegree < I := by
    have h1 := hsum_toFinset factorsP Polynomial.natDegree
    have h2 : (factorsP.map Polynomial.natDegree).sum = factorsP.prod.natDegree :=
      (natDegree_multiset_prod hfac_ne0).symm
    have h3 : factorsP.prod.natDegree = P.natDegree := by
      have hp0 : factorsP.prod ≠ 0 := Multiset.prod_ne_zero (fun h => hfac_ne0 0 h rfl)
      rw [← hu₀, natDegree_mul hp0 u₀.ne_zero, hu₀_degX, add_zero]
    exact (h1.trans_eq (h2.trans h3)).trans_lt hP_degX
  have hF_degY_sum : ∑ f ∈ F, degInner f < J := by
    have h1 := hsum_toFinset factorsP degInner
    have h2 : (factorsP.map degInner).sum = degInner factorsP.prod :=
      (degInner_multiset_prod hfac_ne0).symm
    have h3 : degInner factorsP.prod = degInner P := by
      have hp0 : factorsP.prod ≠ 0 := Multiset.prod_ne_zero (fun h => hfac_ne0 0 h rfl)
      have hu₀_degY : degInner (u₀ : (ℚ[X])[X]) = 0 := by rw [← hc₀, ← hq₀, degInner_CC]
      rw [← hu₀, degInner_mul_eq hp0 u₀.ne_zero, hu₀_degY, add_zero]
    exact (h1.trans_eq (h2.trans h3)).trans_lt hP_degY
  let G : Finset (ℕ × ℕ) := Finset.range R1 ×ˢ Finset.range S1
  let Z : (ℚ[X])[X] → Finset (ℕ × ℕ) := fun f =>
    G.filter fun rs => f.evalEval (u ^ rs.1 * v ^ rs.2) ((rs.1 : ℚ) + (rs.2 : ℚ) * m) = 0
  have hG_sub : G ⊆ F.biUnion Z := by
    intro rs hrs
    have hrs' := Finset.mem_product.mp hrs
    have hvan_rs : P.evalEval (u ^ rs.1 * v ^ rs.2) ((rs.1 : ℚ) + (rs.2 : ℚ) * m) = 0 := by
      rw [hPeval]
      exact hvan rs.1 (Finset.mem_range.mp hrs'.1) rs.2 (Finset.mem_range.mp hrs'.2)
    rw [← hu₀, evalEval_mul] at hvan_rs
    have hu₀_eval : (u₀ : (ℚ[X])[X]).evalEval (u ^ rs.1 * v ^ rs.2) ((rs.1 : ℚ) + (rs.2 : ℚ) * m) = q₀ := by
      rw [← hc₀, ← hq₀, evalEval_CC]
    rw [hu₀_eval] at hvan_rs
    have hprod0 : factorsP.prod.evalEval (u ^ rs.1 * v ^ rs.2) ((rs.1 : ℚ) + (rs.2 : ℚ) * m) = 0 :=
      (mul_eq_zero.mp hvan_rs).resolve_right hq₀_ne
    rw [evalEval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod0
    obtain ⟨f, hfF, hfev⟩ := hprod0
    exact Finset.mem_biUnion.mpr ⟨f, Multiset.mem_toFinset.mpr hfF, Finset.mem_filter.mpr ⟨hrs, hfev⟩⟩
  have hG_card : G.card ≤ ∑ f ∈ F, (Z f).card :=
    (Finset.card_le_card hG_sub).trans Finset.card_biUnion_le
  let FX := F.filter fun f => degInner f = 0
  let FYM := F.filter fun f => ¬ degInner f = 0
  let FY := FYM.filter fun f => f.natDegree = 0
  let FM := FYM.filter fun f => ¬ f.natDegree = 0
  have hF_part : ∑ f ∈ F, (Z f).card =
      (∑ f ∈ FX, (Z f).card) + ((∑ f ∈ FY, (Z f).card) + (∑ f ∈ FM, (Z f).card)) := by
    rw [← Finset.sum_filter_add_sum_filter_not F (fun f => degInner f = 0) (fun f => (Z f).card),
      ← Finset.sum_filter_add_sum_filter_not FYM (fun f => f.natDegree = 0) (fun f => (Z f).card)]
  have hFX_le : ∑ f ∈ FX, (Z f).card ≤ I * (R1 / m.natAbs) + I := by
    have hterm : ∀ f ∈ FX, (Z f).card ≤ f.natDegree * (R1 / m.natAbs + 1) := by
      intro f hf
      have hfF : f ∈ F := (Finset.mem_filter.mp hf).1
      have hfi : degInner f = 0 := (Finset.mem_filter.mp hf).2
      have hf0 : f ≠ 0 := hfac_ne0 f (Multiset.mem_toFinset.mp hfF)
      have heqZ : Z f = G.filter fun rs : ℕ × ℕ => f.evalEval 1 ((rs.1 : ℚ) + (rs.2 : ℚ) * m) = 0 := by
        ext rs
        simp only [Z, Finset.mem_filter, and_congr_right_iff]
        intro _
        have hf_eq : f = (f.map (evalRingHom 1)).map C := by
          ext i j
          simp only [coeff_map, coe_evalRingHom]
          have hdeg0 : (f.coeff i).natDegree = 0 := by
            have := coeff_natDegree_le_degInner f i
            omega
          obtain ⟨q, hq⟩ := natDegree_eq_zero.mp hdeg0
          rw [← hq, eval_C]
        conv_lhs => rw [hf_eq, evalEval_map_C]
        conv_rhs => rw [hf_eq, evalEval_map_C]
      rw [heqZ]
      exact card_eval_root_X_only hf0 hfi hm R1 S1
    calc ∑ f ∈ FX, (Z f).card
        ≤ ∑ f ∈ FX, f.natDegree * (R1 / m.natAbs + 1) := Finset.sum_le_sum hterm
      _ = (∑ f ∈ FX, f.natDegree) * (R1 / m.natAbs + 1) := by rw [Finset.sum_mul]
      _ ≤ I * (R1 / m.natAbs + 1) :=
          Nat.mul_le_mul_right _ ((Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hF_degX_sum.le)
      _ = I * (R1 / m.natAbs) + I := by ring
  have hFX_64 : 64 * ∑ f ∈ FX, (Z f).card ≤ 17 * (R1 * S1) := by
    have hm_pos : 0 < m.natAbs := Int.natAbs_pos.mpr hm.ne'
    have h4 : 4 * (I * (R1 / m.natAbs)) ≤ R1 * S1 := by
      refine Nat.le_of_mul_le_mul_right ?_ hm_pos
      calc 4 * (I * (R1 / m.natAbs)) * m.natAbs
          = (4 * I) * ((R1 / m.natAbs) * m.natAbs) := by ring
        _ ≤ (S1 * m.natAbs) * R1 := Nat.mul_le_mul hSm (Nat.div_mul_le_self R1 m.natAbs)
        _ = R1 * S1 * m.natAbs := by ring
    have hI64 : 64 * I ≤ R1 * S1 := by
      calc 64 * I = 64 * I * 1 := by ring
        _ ≤ 64 * I * J := Nat.mul_le_mul_left _ hJ
        _ ≤ R1 * S1 := hRS
    omega
  have hFY_le : ∑ f ∈ FY, (Z f).card ≤ J := by
    have hterm : ∀ f ∈ FY, (Z f).card ≤ degInner f := by
      intro f hf
      have hf1 := Finset.mem_filter.mp hf
      have hfF : f ∈ F := (Finset.mem_filter.mp hf1.1).1
      have hfd0 : f.natDegree = 0 := hf1.2
      have hf0 : f ≠ 0 := hfac_ne0 f (Multiset.mem_toFinset.mp hfF)
      obtain ⟨q, hfq⟩ := natDegree_eq_zero.mp hfd0
      have hq0 : q ≠ 0 := by rintro rfl; simp at hfq; exact hf0 hfq.symm
      have hqdeg : q.natDegree = degInner f := by rw [← hfq, degInner_C]
      have hinj : Set.InjOn (fun rs : ℕ × ℕ => u ^ rs.1 * v ^ rs.2) (Z f) :=
        fun p₁ _ p₂ _ h => hind_nat p₁ p₂ h
      have hmaps : ∀ rs ∈ Z f, u ^ rs.1 * v ^ rs.2 ∈ q.roots.toFinset := by
        intro rs hrs
        have hev := (Finset.mem_filter.mp hrs).2
        rw [← hfq, evalEval_C] at hev
        exact Multiset.mem_toFinset.mpr ((mem_roots hq0).mpr hev)
      calc (Z f).card ≤ q.roots.toFinset.card := Finset.card_le_card_of_injOn _ hmaps hinj
        _ ≤ q.natDegree := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' q)
        _ = degInner f := hqdeg
    exact (Finset.sum_le_sum hterm).trans
      ((Finset.sum_le_sum_of_subset ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))).trans hF_degY_sum.le)
  have hFY_64 : 64 * ∑ f ∈ FY, (Z f).card ≤ 4 * (R1 * S1) := by
    have h1 : J ≤ 16 * J := by omega
    have h2 : 16 * J ≤ S1 := hSJ
    have h3 : S1 ≤ R1 * S1 := Nat.le_mul_of_pos_left S1 hR1
    omega
  have hFM_sq : ∀ f ∈ FM, (Z f).card ^ 2 ≤ 16 * R1 * S1 * f.natDegree * degInner f := by
    intro f hf
    have hf1 := Finset.mem_filter.mp hf
    have hf2 := Finset.mem_filter.mp hf1.1
    have hfF : f ∈ F := hf2.1
    have hirr : Irreducible f := UniqueFactorizationMonoid.irreducible_of_factor f (Multiset.mem_toFinset.mp hfF)
    have hfdeg : 1 ≤ f.natDegree := Nat.pos_of_ne_zero hf1.2
    have hfinner : 1 ≤ degInner f := Nat.pos_of_ne_zero hf2.2
    exact card_Z_FM_sq hu hv hind hind_nat hR1 hS1 hirr hfdeg hfinner
      (Finset.filter_subset _ G) (fun rs hrs => (Finset.mem_filter.mp hrs).2)
  set fmSum := ∑ f ∈ FM, (Z f).card
  have hFM_cs : 2 * fmSum ≤ R1 * S1 := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul FM
      (r := fun f => ((Z f).card : ℤ))
      (f := fun f => (4 * R1 * f.natDegree : ℤ))
      (g := fun f => (4 * S1 * degInner f : ℤ))
      (fun _ _ => Int.mul_nonneg (Int.mul_nonneg (by norm_num) (Int.natCast_nonneg _)) (Int.natCast_nonneg _))
      (fun _ _ => Int.mul_nonneg (Int.mul_nonneg (by norm_num) (Int.natCast_nonneg _)) (Int.natCast_nonneg _))
      (fun f hf => by
        have h := hFM_sq f hf
        have hz : ((Z f).card : ℤ) ^ 2 ≤ (16 * R1 * S1 * f.natDegree * degInner f : ℤ) := by
          exact_mod_cast h
        linarith)
    have hsumX : (∑ f ∈ FM, (4 * R1 * f.natDegree : ℤ)) ≤ (4 * R1 * I : ℤ) := by
      rw [← Finset.mul_sum]
      have hle : ∑ f ∈ FM, f.natDegree ≤ I :=
        ((Finset.sum_le_sum_of_subset ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))).trans hF_degX_sum.le)
      have hlez : (∑ f ∈ FM, (f.natDegree : ℤ)) ≤ (I : ℤ) := by exact_mod_cast hle
      exact Int.mul_le_mul_of_nonneg_left hlez (by positivity)
    have hsumY : (∑ f ∈ FM, (4 * S1 * degInner f : ℤ)) ≤ (4 * S1 * J : ℤ) := by
      rw [← Finset.mul_sum]
      have hle : ∑ f ∈ FM, degInner f ≤ J :=
        ((Finset.sum_le_sum_of_subset ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))).trans hF_degY_sum.le)
      have hlez : (∑ f ∈ FM, (degInner f : ℤ)) ≤ (J : ℤ) := by exact_mod_cast hle
      exact Int.mul_le_mul_of_nonneg_left hlez (by positivity)
    have h64_nat : 64 * (I * J) ≤ R1 * S1 := by
      rw [← mul_assoc]; exact hRS
    have h64 : (64 : ℤ) * (I * J : ℤ) ≤ (R1 * S1 : ℤ) := by exact_mod_cast h64_nat
    have hprod_nonneg2 : 0 ≤ ∑ f ∈ FM, (4 * S1 * degInner f : ℤ) :=
      Finset.sum_nonneg fun _ _ => Int.mul_nonneg (Int.mul_nonneg (by norm_num) (Int.natCast_nonneg _))
        (Int.natCast_nonneg _)
    have hbound : (2 * (fmSum : ℤ)) ^ 2 ≤ (R1 * S1 : ℤ) ^ 2 := by
      have hnonneg1 : (0 : ℤ) ≤ (4 * R1 * I : ℤ) := by positivity
      have hfm : (fmSum : ℤ) = ∑ f ∈ FM, ((Z f).card : ℤ) := by
        dsimp [fmSum]; push_cast; rfl
      rw [hfm]
      calc (2 * (∑ f ∈ FM, ((Z f).card : ℤ))) ^ 2
          = 4 * (∑ f ∈ FM, ((Z f).card : ℤ)) ^ 2 := by ring
        _ ≤ 4 * ((∑ f ∈ FM, (4 * R1 * f.natDegree : ℤ)) * (∑ f ∈ FM, (4 * S1 * degInner f : ℤ))) :=
            Int.mul_le_mul_of_nonneg_left hcs (by norm_num)
        _ ≤ 4 * ((4 * R1 * I : ℤ) * (4 * S1 * J : ℤ)) :=
            Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul hsumX hsumY hprod_nonneg2 hnonneg1) (by norm_num)
        _ = (R1 * S1 : ℤ) * ((64 : ℤ) * (I * J : ℤ)) := by ring
        _ ≤ (R1 * S1 : ℤ) * (R1 * S1 : ℤ) :=
            Int.mul_le_mul_of_nonneg_left h64 (Int.natCast_nonneg _)
        _ = (R1 * S1 : ℤ) ^ 2 := by ring
    have hbound_nat : (2 * fmSum) ^ 2 ≤ (R1 * S1) ^ 2 := by exact_mod_cast hbound
    by_contra hcon
    push Not at hcon
    have hRS_pos' : 0 < R1 * S1 := Nat.mul_pos hR1 hS1
    have hlt2 : (R1 * S1) ^ 2 < (2 * fmSum) ^ 2 := by
      calc (R1 * S1) ^ 2 = (R1 * S1) * (R1 * S1) := sq _
        _ < (2 * fmSum) * (R1 * S1) := Nat.mul_lt_mul_of_pos_right hcon hRS_pos'
        _ ≤ (2 * fmSum) * (2 * fmSum) := Nat.mul_le_mul_left _ hcon.le
        _ = (2 * fmSum) ^ 2 := (sq _).symm
    exact lt_irrefl _ (hlt2.trans_le hbound_nat)
  have hFM_64 : 64 * fmSum ≤ 32 * (R1 * S1) := by omega
  have hG_eq : G.card = R1 * S1 := by simp [G]
  have hRS_pos : 0 < R1 * S1 := Nat.mul_pos hR1 hS1
  have htot : 64 * G.card ≤ 53 * (R1 * S1) := by
    calc 64 * G.card
        ≤ 64 * ∑ f ∈ F, (Z f).card := Nat.mul_le_mul_left 64 hG_card
      _ = 64 * ∑ f ∈ FX, (Z f).card + 64 * ∑ f ∈ FY, (Z f).card + 64 * fmSum := by
          rw [hF_part]; dsimp [fmSum]; ring
      _ ≤ 17 * (R1 * S1) + 4 * (R1 * S1) + 32 * (R1 * S1) :=
          Nat.add_le_add (Nat.add_le_add hFX_64 hFY_64) hFM_64
      _ = 53 * (R1 * S1) := by ring
  rw [hG_eq] at htot
  nlinarith

end ZeroLemmaMain

end ZeroLemma

section SiegelAndMain

open Real Finset Complex
open scoped Matrix.Norms.Elementwise

lemma exp_M_bounds {M L : ℝ} (hM : 100 ≤ M) (hL : L = Real.exp M) :
    M + 1 ≤ L ∧ 10 ^ 5 * M ^ 4 ≤ L ∧ 24 * M ≤ Real.exp (4 * M) ∧ 2 ≤ L := by
  have hM0 : 0 ≤ M := by linarith
  have h1 : M + 1 ≤ L := by rw [hL]; linarith [Real.add_one_le_exp M]
  have h2 : 10 ^ 5 * M ^ 4 ≤ L := by
    have hpow := Real.pow_div_factorial_le_exp (x := M) hM0 10
    rw [← hL] at hpow
    have hfac : (Nat.factorial 10 : ℝ) = 3628800 := by norm_num [Nat.factorial]
    rw [hfac] at hpow
    have hM6 : (100 : ℝ) ^ 6 ≤ M ^ 6 := pow_le_pow_left₀ (by norm_num) hM 6
    have hc : (10 : ℝ) ^ 5 * 3628800 ≤ M ^ 6 := by linarith
    have hmul : (10 : ℝ) ^ 5 * M ^ 4 * 3628800 ≤ M ^ 10 := by
      calc (10 : ℝ) ^ 5 * M ^ 4 * 3628800
          = ((10 : ℝ) ^ 5 * 3628800) * M ^ 4 := by ring
        _ ≤ M ^ 6 * M ^ 4 := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = M ^ 10 := by ring
    linarith
  have h3 : 24 * M ≤ Real.exp (4 * M) := by
    have hpow2 := Real.pow_div_factorial_le_exp (x := 4 * M) (show 0 ≤ 4 * M by linarith) 2
    have hfac2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [hfac2] at hpow2
    have hsq : 24 * M ≤ (4 * M) ^ 2 / 2 := by nlinarith
    exact hsq.trans hpow2
  have h4 : 2 ≤ L := by linarith
  exact ⟨h1, h2, h3, h4⟩

lemma liouville_pow_div_lower {u v : ℚ} {m : ℤ} (hu : 0 < u) (hv : 0 < v) (hm : 0 < m)
    {U V : ℝ} (hHu : ((u.num.natAbs + u.den : ℕ) : ℝ) ≤ U)
    (hHv : ((v.num.natAbs + v.den : ℕ) : ℝ) ≤ V)
    (hpos : 0 < |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)|) :
    1 / (2 * V * U ^ m.natAbs) ≤ |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| := by
  set r : ℚ := u ^ m.natAbs / v
  have hr : 0 < r := div_pos (pow_pos hu _) hv
  have hm_eq : (m.natAbs : ℝ) = (m : ℝ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hm.le]
  have hlog : Real.log (r : ℝ) = (m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ) := by
    have hr_cast : (r : ℝ) = (u : ℝ) ^ m.natAbs / (v : ℝ) := by
      dsimp [r]; push_cast; rfl
    rw [hr_cast, Real.log_div (pow_ne_zero _ (by exact_mod_cast hu.ne')) (by exact_mod_cast hv.ne'),
      Real.log_pow, hm_eq]
  have hr1 : r ≠ 1 := by
    intro h1
    rw [h1, Rat.cast_one, Real.log_one] at hlog
    rw [← hlog, abs_zero] at hpos
    exact lt_irrefl 0 hpos
  have hu_num : (u.num.natAbs : ℚ) = u.num := rat_num_natAbs_cast_rat hu
  have hv_num : (v.num.natAbs : ℚ) = v.num := rat_num_natAbs_cast_rat hv
  have hr_eq : r = ((u.num.natAbs ^ m.natAbs * v.den : ℕ) : ℚ) /
      ((u.den ^ m.natAbs * v.num.natAbs : ℕ) : ℚ) := by
    dsimp [r]
    conv_lhs => rw [← Rat.num_div_den u, ← Rat.num_div_den v, ← hu_num, ← hv_num]
    push_cast
    rw [div_pow]
    have h1 : (u.den : ℚ) ≠ 0 := by exact_mod_cast u.den_nz
    have h2 : (v.num.natAbs : ℚ) ≠ 0 := by
      exact_mod_cast (Int.natAbs_pos.mpr (Rat.num_pos.mpr hv).ne').ne'
    have h3 : (v.den : ℚ) ≠ 0 := by exact_mod_cast v.den_nz
    field_simp
  have hupos : 0 < u.num.natAbs := Int.natAbs_pos.mpr (Rat.num_pos.mpr hu).ne'
  have hvpos : 0 < v.num.natAbs := Int.natAbs_pos.mpr (Rat.num_pos.mpr hv).ne'
  have hp_pos : 0 < u.num.natAbs ^ m.natAbs * v.den := Nat.mul_pos (pow_pos hupos _) v.pos
  have hq_pos : 0 < u.den ^ m.natAbs * v.num.natAbs := Nat.mul_pos (pow_pos u.pos _) hvpos
  obtain ⟨hnum_le, hden_le⟩ := rat_div_height_le hp_pos hq_pos
  rw [← hr_eq] at hnum_le hden_le
  have hU0 : 0 ≤ U := le_trans (Nat.cast_nonneg _) hHu
  have hV0 : 0 ≤ V := le_trans (Nat.cast_nonneg _) hHv
  have huA : (u.num.natAbs : ℝ) ≤ U := by
    have : (u.num.natAbs : ℝ) ≤ ((u.num.natAbs + u.den : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    exact this.trans hHu
  have huB : (u.den : ℝ) ≤ U := by
    have : (u.den : ℝ) ≤ ((u.num.natAbs + u.den : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left _ _
    exact this.trans hHu
  have hvA : (v.num.natAbs : ℝ) ≤ V := by
    have : (v.num.natAbs : ℝ) ≤ ((v.num.natAbs + v.den : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    exact this.trans hHv
  have hvB : (v.den : ℝ) ≤ V := by
    have : (v.den : ℝ) ≤ ((v.num.natAbs + v.den : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left _ _
    exact this.trans hHv
  have hht_pos : (0 : ℝ) < ((r.num.natAbs + r.den : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_pos_right r.num.natAbs r.pos
  have hht_le : ((r.num.natAbs + r.den : ℕ) : ℝ) ≤ 2 * V * U ^ m.natAbs := by
    have h1 : (r.num.natAbs : ℝ) ≤ U ^ m.natAbs * V := by
      have : (r.num.natAbs : ℝ) ≤ ((u.num.natAbs ^ m.natAbs * v.den : ℕ) : ℝ) := by
        exact_mod_cast hnum_le
      push_cast at this
      exact this.trans (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) huA _) hvB
        (Nat.cast_nonneg _) (pow_nonneg hU0 _))
    have h2 : (r.den : ℝ) ≤ U ^ m.natAbs * V := by
      have : (r.den : ℝ) ≤ ((u.den ^ m.natAbs * v.num.natAbs : ℕ) : ℝ) := by
        exact_mod_cast hden_le
      push_cast at this
      exact this.trans (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) huB _) hvA
        (Nat.cast_nonneg _) (pow_nonneg hU0 _))
    push_cast
    linarith
  have hlog_ge := abs_log_rat_ge_of_ne_one hr hr1
  rw [hlog] at hlog_ge
  exact (one_div_le_one_div_of_le hht_pos hht_le).trans hlog_ge

lemma small_S_case {D S z : ℝ} {u v : ℚ} {m : ℤ}
    (hD : Real.log (2 * Real.exp (Real.exp 100) *
      ((Real.exp 100) ^ 16) ^ Nat.ceil ((Real.exp 100) ^ 16)) / 3 + 1 ≤ D)
    (hDpos : 0 < D)
    (hS27 : 27 < S) (hS_le : S ≤ Real.exp (Real.exp 100))
    (_hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hu : 0 < u) (hv : 0 < v) (hm : 0 < m)
    (hHu : ((u.num.natAbs + u.den : ℕ) : ℝ) ≤ (Real.log S) ^ 16)
    (hHv : ((v.num.natAbs + v.den : ℕ) : ℝ) ≤ S)
    (hmu : |(m : ℝ)| ≤ (Real.log S) ^ 16)
    (hpos : 0 < |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)|) :
    Real.exp (-D * Real.log S * (Real.log (Real.log S)) ^ (4 - 4 * z)) ≤
      |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| := by
  set L0 := Real.exp 100
  set S0 := Real.exp L0
  set B0 := 2 * S0 * (L0 ^ 16) ^ Nat.ceil (L0 ^ 16)
  have hB0_pos : 0 < B0 := by positivity
  have hexp3 : Real.exp 3 < 27 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    calc (Real.exp 1) ^ 3 < 3 ^ 3 := pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
      _ = 27 := by norm_num
  have hS3 : Real.exp 3 < S := hexp3.trans hS27
  have hL3 : 3 < Real.log S := by
    have h := Real.log_lt_log (Real.exp_pos 3) hS3
    rwa [Real.log_exp] at h
  have hMe : Real.exp 1 < Real.log S := Real.exp_one_lt_three.trans hL3
  have hM1 : 1 < Real.log (Real.log S) := by
    have h := Real.log_lt_log (Real.exp_pos 1) hMe
    rwa [Real.log_exp] at h
  have hMz : 1 ≤ (Real.log (Real.log S)) ^ (4 - 4 * z) :=
    Real.one_le_rpow hM1.le (by linarith)
  have h3le : 3 ≤ Real.log S * (Real.log (Real.log S)) ^ (4 - 4 * z) := by
    nlinarith
  have hD3 : Real.log B0 ≤ 3 * D := by linarith
  have hexp_le : Real.exp (-D * Real.log S * (Real.log (Real.log S)) ^ (4 - 4 * z)) ≤
      1 / B0 := by
    have h1 : Real.log B0 ≤ D * Real.log S * (Real.log (Real.log S)) ^ (4 - 4 * z) := by
      have := mul_le_mul_of_nonneg_left h3le hDpos.le
      linarith
    have h2 : Real.exp (-D * Real.log S * (Real.log (Real.log S)) ^ (4 - 4 * z)) ≤
        Real.exp (-Real.log B0) := Real.exp_le_exp.mpr (by linarith)
    rwa [Real.exp_neg, Real.exp_log hB0_pos, ← one_div] at h2
  have hL_le : Real.log S ≤ L0 := by
    have h := Real.log_le_log (by linarith) hS_le
    rwa [Real.log_exp] at h
  have hL16 : (Real.log S) ^ 16 ≤ L0 ^ 16 :=
    pow_le_pow_left₀ (by linarith) hL_le 16
  have hm_le_ceil : m.natAbs ≤ Nat.ceil (L0 ^ 16) := by
    have hmR : (m.natAbs : ℝ) ≤ L0 ^ 16 := by
      have : (m.natAbs : ℝ) = |(m : ℝ)| := by
        rw [abs_of_pos (by exact_mod_cast hm), ← Int.cast_natCast, Int.natAbs_of_nonneg hm.le]
      rw [this]
      exact hmu.trans hL16
    exact_mod_cast hmR.trans (Nat.le_ceil _)
  have hpow_le : (L0 ^ 16) ^ m.natAbs ≤ (L0 ^ 16) ^ Nat.ceil (L0 ^ 16) :=
    pow_le_pow_right₀ (by have : 1 ≤ L0 := Real.one_le_exp (by norm_num); exact one_le_pow₀ this)
      hm_le_ceil
  have hliou := liouville_pow_div_lower hu hv hm (hHu.trans hL16) (hHv.trans hS_le) hpos
  have hB0_ge : 1 / B0 ≤ 1 / (2 * S0 * (L0 ^ 16) ^ m.natAbs) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
  exact hexp_le.trans (hB0_ge.trans hliou)

lemma neg_DLM_le_neg_L {D L M z : ℝ} (hL : 0 < L) (hD : 1 ≤ D) (hM1 : 1 ≤ M)
    (hz1 : z ≤ 1) : -D * L * M ^ (4 - 4 * z) ≤ -L := by
  have hMz4 : 1 ≤ M ^ (4 - 4 * z) := Real.one_le_rpow hM1 (by linarith)
  have h1 : L ≤ D * L := le_mul_of_one_le_left hL.le hD
  have h2 : D * L ≤ D * L * M ^ (4 - 4 * z) :=
    le_mul_of_one_le_right (mul_nonneg (by linarith) hL.le) hMz4
  linarith

lemma case_one_small_m {D S z : ℝ} {u v : ℚ} {m : ℤ}
    (hM100 : 100 ≤ Real.log (Real.log S)) (hSpos : 0 < S) (hLpos_in : 0 < Real.log S)
    (_hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hD : 10 ^ 15 ≤ D) (hu : 0 < u) (hv : 0 < v) (hm : 0 < m)
    (hHu : ((u.num.natAbs + u.den : ℕ) : ℝ) ≤ (Real.log S) ^ 16)
    (hHv : ((v.num.natAbs + v.den : ℕ) : ℝ) ≤ S)
    (hm_le : (m : ℝ) ≤ 10 ^ 7 * Real.log S * (Real.log (Real.log S)) ^ (3 - 4 * z))
    (hpos : 0 < |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)|) :
    Real.exp (-D * Real.log S * (Real.log (Real.log S)) ^ (4 - 4 * z)) ≤
      |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| := by
  set L := Real.log S
  set M := Real.log L
  have hMpos : 0 < M := by linarith
  have hLpos : 0 < L := hLpos_in
  have hL_eq : L = Real.exp M := (Real.exp_log hLpos).symm
  obtain ⟨hML, _, _, h2L⟩ := exp_M_bounds hM100 hL_eq
  have hS_eq : S = Real.exp L := (Real.exp_log hSpos).symm
  have hMz4 : 1 ≤ M ^ (4 - 4 * z) := Real.one_le_rpow (by linarith) (by linarith)
  have hMpow : M * M ^ (3 - 4 * z) = M ^ (4 - 4 * z) := by
    rw [show M * M ^ (3 - 4 * z) = M ^ (1 : ℝ) * M ^ (3 - 4 * z) by rw [Real.rpow_one],
      ← Real.rpow_add hMpos]
    ring_nf
  have hm_eq : (m.natAbs : ℝ) = (m : ℝ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hm.le]
  have hliou := liouville_pow_div_lower hu hv hm hHu hHv hpos
  have hden_le : 2 * S * (L ^ 16) ^ m.natAbs ≤ Real.exp (D * L * M ^ (4 - 4 * z)) := by
    have h2 : (2 : ℝ) ≤ Real.exp M := by linarith [hL_eq]
    have h16 : (L ^ 16) ^ m.natAbs = Real.exp (16 * M * (m : ℝ)) := by
      rw [hL_eq, ← Real.exp_nat_mul, ← Real.exp_nat_mul, hm_eq]
      ring_nf
    calc 2 * S * (L ^ 16) ^ m.natAbs
        ≤ Real.exp M * Real.exp L * Real.exp (16 * M * (m : ℝ)) := by
          rw [hS_eq, h16]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le)
            (Real.exp_pos _).le
      _ = Real.exp (M + L + 16 * M * (m : ℝ)) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (D * L * M ^ (4 - 4 * z)) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : M + L ≤ 2 * L * M ^ (4 - 4 * z) := by
            calc M + L ≤ 2 * L := by linarith
              _ = 2 * L * 1 := (mul_one _).symm
              _ ≤ 2 * L * M ^ (4 - 4 * z) := mul_le_mul_of_nonneg_left hMz4 (by positivity)
          have h2' : 16 * M * (m : ℝ) ≤ 16 * 10 ^ 7 * L * M ^ (4 - 4 * z) := by
            calc 16 * M * (m : ℝ)
                ≤ 16 * M * (10 ^ 7 * L * M ^ (3 - 4 * z)) :=
                  mul_le_mul_of_nonneg_left hm_le (by positivity)
              _ = 16 * 10 ^ 7 * L * (M * M ^ (3 - 4 * z)) := by ring
              _ = 16 * 10 ^ 7 * L * M ^ (4 - 4 * z) := by rw [hMpow]
          have h3 : (16 * 10 ^ 7 + 2) * L * M ^ (4 - 4 * z) ≤ D * L * M ^ (4 - 4 * z) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hLpos.le)
              (by positivity)
          linarith
  have hexp_le : Real.exp (-D * L * M ^ (4 - 4 * z)) ≤ 1 / (2 * S * (L ^ 16) ^ m.natAbs) := by
    rw [show -D * L * M ^ (4 - 4 * z) = -(D * L * M ^ (4 - 4 * z)) by ring, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hden_le
  exact hexp_le.trans hliou

lemma wlog_pos_uv {D S z : ℝ} {u v : ℚ} {m : ℤ}
    (hM100 : 100 ≤ Real.log (Real.log S)) (hSpos : 0 < S) (hLpos_in : 0 < Real.log S)
    (_hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hD : 10 ^ 15 ≤ D) (hu : 0 < u) (hv : 0 < v) (hm : 0 < m)
    (hHu : ((u.num.natAbs + u.den : ℕ) : ℝ) ≤ (Real.log S) ^ 16)
    (hHv : ((v.num.natAbs + v.den : ℕ) : ℝ) ≤ S)
    (hpos : 0 < |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)|)
    (hcontra : |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| <
      Real.exp (-D * Real.log S * (Real.log (Real.log S)) ^ (4 - 4 * z))) :
    (1 < u ∧ 1 < v) ∨ (1 < u⁻¹ ∧ 1 < v⁻¹) := by
  set L := Real.log S
  set M := Real.log L
  have hLpos : 0 < L := hLpos_in
  have hL_eq : L = Real.exp M := (Real.exp_log hLpos).symm
  obtain ⟨_, hM4L, _, _⟩ := exp_M_bounds hM100 hL_eq
  have hS_eq : S = Real.exp L := (Real.exp_log hSpos).symm
  have hexp_L : Real.exp (-D * L * M ^ (4 - 4 * z)) ≤ Real.exp (-L) :=
    Real.exp_le_exp.mpr (neg_DLM_le_neg_L hLpos (by linarith) (by linarith) hz1)
  have h1S : Real.exp (-L) = 1 / S := by rw [Real.exp_neg, ← one_div, ← hS_eq]
  have h16M : Real.exp (-L) ≤ Real.exp (-16 * M) := by
    refine Real.exp_le_exp.mpr ?_
    have hM1 : 1 ≤ M := by linarith
    have hM4 : M ≤ M ^ 4 := by
      calc M = M * 1 := (mul_one _).symm
        _ ≤ M * M ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hM1) (by linarith)
        _ = M ^ 4 := by ring
    have hle : 16 * M ≤ 10 ^ 5 * M ^ 4 := by
      calc 16 * M ≤ 10 ^ 5 * M := by linarith
        _ ≤ 10 ^ 5 * M ^ 4 := mul_le_mul_of_nonneg_left hM4 (by norm_num)
    linarith
  have hL16_inv : 1 / L ^ 16 = Real.exp (-16 * M) := by
    rw [hL_eq, ← Real.exp_nat_mul, one_div, ← Real.exp_neg]; ring_nf
  have hnot_u1 : u ≠ 1 := by
    intro hu1
    have hvu : v ≠ 1 := by
      intro hv1
      rw [hu1, hv1, Rat.cast_one, Real.log_one, mul_zero, sub_zero, abs_zero] at hpos
      exact lt_irrefl 0 hpos
    have hlogv := abs_log_rat_ge_of_ne_one hv hvu
    have h1v : 1 / S ≤ 1 / ((v.num.natAbs + v.den : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by exact_mod_cast Nat.add_pos_right v.num.natAbs v.pos) hHv
    rw [hu1, Rat.cast_one, Real.log_one, mul_zero, zero_sub, abs_neg] at hcontra
    exact lt_irrefl _ ((h1v.trans hlogv).trans_lt (hcontra.trans_le (hexp_L.trans_eq h1S)))
  have hnot_v1 : v ≠ 1 := by
    intro hv1
    have hlogu := abs_log_rat_ge_of_ne_one hu hnot_u1
    have h1u : 1 / L ^ 16 ≤ 1 / ((u.num.natAbs + u.den : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by exact_mod_cast Nat.add_pos_right u.num.natAbs u.pos) hHu
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ m)
    rw [hv1, Rat.cast_one, Real.log_one, sub_zero, abs_mul,
      abs_of_pos (by exact_mod_cast hm)] at hcontra
    have hmul : 1 / L ^ 16 ≤ (m : ℝ) * |Real.log (u : ℝ)| := by
      calc 1 / L ^ 16 ≤ |Real.log (u : ℝ)| := h1u.trans hlogu
        _ = 1 * |Real.log (u : ℝ)| := (one_mul _).symm
        _ ≤ (m : ℝ) * |Real.log (u : ℝ)| := mul_le_mul_of_nonneg_right hm1 (abs_nonneg _)
    have h_inv_le : Real.exp (-L) ≤ 1 / L ^ 16 := h16M.trans_eq hL16_inv.symm
    exact lt_irrefl _ (hmul.trans_lt (hcontra.trans_le (hexp_L.trans h_inv_le)))
  have hlogv_ge : 1 / S ≤ |Real.log (v : ℝ)| :=
    (one_div_le_one_div_of_le (by exact_mod_cast Nat.add_pos_right v.num.natAbs v.pos) hHv).trans
      (abs_log_rat_ge_of_ne_one hv hnot_v1)
  have hu_cases : u < 1 ∨ 1 < u := lt_or_gt_of_ne hnot_u1
  have hv_cases : v < 1 ∨ 1 < v := lt_or_gt_of_ne hnot_v1
  have hu_posR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hv_posR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hm_posR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rcases hu_cases with hu_lt | hu_gt <;> rcases hv_cases with hv_lt | hv_gt
  · right
    exact ⟨(one_lt_inv₀ hu).mpr hu_lt, (one_lt_inv₀ hv).mpr hv_lt⟩
  · exfalso
    have hlu : Real.log (u : ℝ) < 0 := Real.log_neg hu_posR (by exact_mod_cast hu_lt)
    have hlv : 0 < Real.log (v : ℝ) := Real.log_pos (by exact_mod_cast hv_gt)
    have hsum : |Real.log (v : ℝ)| ≤ |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| := by
      have hneg : (m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ) < 0 := by nlinarith
      rw [abs_of_pos hlv, abs_of_neg hneg]
      nlinarith
    exact lt_irrefl _ ((hlogv_ge.trans hsum).trans_lt (hcontra.trans_le (hexp_L.trans_eq h1S)))
  · exfalso
    have hlu : 0 < Real.log (u : ℝ) := Real.log_pos (by exact_mod_cast hu_gt)
    have hlv : Real.log (v : ℝ) < 0 := Real.log_neg hv_posR (by exact_mod_cast hv_lt)
    have hsum : |Real.log (v : ℝ)| ≤ |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| := by
      have hpos' : 0 < (m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ) := by nlinarith
      rw [abs_of_neg hlv, abs_of_pos hpos']
      nlinarith
    exact lt_irrefl _ ((hlogv_ge.trans hsum).trans_lt (hcontra.trans_le (hexp_L.trans_eq h1S)))
  · left
    exact ⟨hu_gt, hv_gt⟩

lemma log_u_le_of_pos {D S z : ℝ} {u v : ℚ} {m : ℤ}
    (hM100 : 100 ≤ Real.log (Real.log S)) (hLpos_in : 0 < Real.log S)
    (_hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hD : 10 ^ 15 ≤ D) (hu : 1 < u) (hm : 0 < m)
    (hml : 2 * Real.log S / Real.log (Real.log S) ≤ |(m : ℝ)|)
    (hlv : |Real.log (v : ℝ)| ≤ Real.log S / Real.log (Real.log S) *
      Real.exp (-(Real.log (Real.log S)) ^ z))
    (hcontra : |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| <
      Real.exp (-D * Real.log S * (Real.log (Real.log S)) ^ (4 - 4 * z))) :
    Real.log (u : ℝ) ≤ Real.exp (-(Real.log (Real.log S)) ^ z) ∧
      (m : ℝ) * Real.log (u : ℝ) ≤ 2 * (Real.log S / Real.log (Real.log S)) *
        Real.exp (-(Real.log (Real.log S)) ^ z) := by
  set L := Real.log S
  set M := Real.log L
  have hMpos : 0 < M := by linarith
  have hLpos : 0 < L := hLpos_in
  have hL_eq : L = Real.exp M := (Real.exp_log hLpos).symm
  obtain ⟨hML, _, _, _⟩ := exp_M_bounds hM100 hL_eq
  have hM1 : 1 ≤ M := by linarith
  have hMz_le : M ^ z ≤ M := by
    simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM1 hz1
  have h1LM : 1 ≤ L / M := (one_le_div hMpos).mpr (by linarith)
  have hexp_dom : Real.exp (-D * L * M ^ (4 - 4 * z)) ≤ (L / M) * Real.exp (-M ^ z) := by
    have h1 : Real.exp (-D * L * M ^ (4 - 4 * z)) ≤ Real.exp (-L) :=
      Real.exp_le_exp.mpr (neg_DLM_le_neg_L hLpos (by linarith) hM1 hz1)
    have h2 : Real.exp (-L) ≤ Real.exp (-M ^ z) :=
      Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (-M ^ z) ≤ (L / M) * Real.exp (-M ^ z) :=
      le_mul_of_one_le_left (Real.exp_pos _).le h1LM
    exact h1.trans (h2.trans h3)
  have hmul_le : (m : ℝ) * Real.log (u : ℝ) ≤ 2 * (L / M) * Real.exp (-M ^ z) := by
    have htri : (m : ℝ) * Real.log (u : ℝ) ≤
        |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| + |Real.log (v : ℝ)| := by
      linarith [le_abs_self ((m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)),
        le_abs_self (Real.log (v : ℝ))]
    linarith
  have hm_ge : 2 * L / M ≤ (m : ℝ) := by
    rwa [abs_of_pos (by exact_mod_cast hm)] at hml
  have hlu_pos : 0 < Real.log (u : ℝ) := Real.log_pos (by exact_mod_cast hu)
  have hdiv : Real.log (u : ℝ) ≤ Real.exp (-M ^ z) := by
    have h2LM_pos : 0 < 2 * L / M := by positivity
    have h1 : (2 * L / M) * Real.log (u : ℝ) ≤ (2 * L / M) * Real.exp (-M ^ z) := by
      calc (2 * L / M) * Real.log (u : ℝ)
          ≤ (m : ℝ) * Real.log (u : ℝ) := mul_le_mul_of_nonneg_right hm_ge hlu_pos.le
        _ ≤ 2 * (L / M) * Real.exp (-M ^ z) := hmul_le
        _ = (2 * L / M) * Real.exp (-M ^ z) := by ring
    exact le_of_mul_le_mul_left h1 h2LM_pos
  exact ⟨hdiv, hmul_le⟩

lemma mult_indep_of_contra {D S z : ℝ} {u v : ℚ} {m : ℤ}
    (hM100 : 100 ≤ Real.log (Real.log S)) (hLpos_in : 0 < Real.log S)
    (_hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hD : 10 ^ 15 ≤ D) (hu : 1 < u) (hv : 1 < v) (_hm : 0 < m)
    (hHu : ((u.num.natAbs + u.den : ℕ) : ℝ) ≤ (Real.log S) ^ 16)
    (hpos : 0 < |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)|)
    (hcontra : |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| <
      Real.exp (-D * Real.log S * (Real.log (Real.log S)) ^ (4 - 4 * z))) :
    ∀ a b : ℤ, u ^ a * v ^ b = 1 → a = 0 ∧ b = 0 := by
  intro a b hab
  by_contra hne
  set L := Real.log S
  set M := Real.log L
  have hMpos : 0 < M := by linarith
  have hLpos : 0 < L := hLpos_in
  have hL_eq : L = Real.exp M := (Real.exp_log hLpos).symm
  obtain ⟨hML, hM4L, h24M, _⟩ := exp_M_bounds hM100 hL_eq
  have hlu_pos : 0 < Real.log (u : ℝ) := Real.log_pos (by exact_mod_cast hu)
  have hlv_pos : 0 < Real.log (v : ℝ) := Real.log_pos (by exact_mod_cast hv)
  have hu0 : u ≠ 0 := (lt_trans zero_lt_one hu).ne'
  have hv0 : v ≠ 0 := (lt_trans zero_lt_one hv).ne'
  have huR0 : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hu)
  have hvR0 : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hv)
  have hlog_rel : (a : ℝ) * Real.log (u : ℝ) + (b : ℝ) * Real.log (v : ℝ) = 0 := by
    have h1 : ((u ^ a * v ^ b : ℚ) : ℝ) = 1 := by exact_mod_cast hab
    have h2 : (u : ℝ) ^ a * (v : ℝ) ^ b = 1 := by
      push_cast at h1; exact h1
    have h3 := congrArg Real.log h2
    rw [Real.log_mul (zpow_ne_zero _ huR0.ne') (zpow_ne_zero _ hvR0.ne'),
      Real.log_zpow, Real.log_zpow, Real.log_one] at h3
    exact h3
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, Int.cast_zero, zero_mul, zero_add] at hlog_rel
    have hb0 : b ≠ 0 := fun hb => hne ⟨ha, hb⟩
    have := (mul_eq_zero.mp hlog_rel).resolve_right hlv_pos.ne'
    exact hb0 (by exact_mod_cast this)
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb, Int.cast_zero, zero_mul, add_zero] at hlog_rel
    have := (mul_eq_zero.mp hlog_rel).resolve_right hlu_pos.ne'
    exact ha0 (by exact_mod_cast this)
  let g : ℕ := Nat.gcd a.natAbs b.natAbs
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left b.natAbs (Int.natAbs_pos.mpr ha0)
  let a' : ℤ := a / (g : ℤ)
  let b' : ℤ := b / (g : ℤ)
  have hdvd_a : (g : ℤ) ∣ a := Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
  have hdvd_b : (g : ℤ) ∣ b := Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  have ha_eq : a' * (g : ℤ) = a := Int.ediv_mul_cancel hdvd_a
  have hb_eq : b' * (g : ℤ) = b := Int.ediv_mul_cancel hdvd_b
  have ha'_abs : a'.natAbs = a.natAbs / g := by
    have h1 : a'.natAbs * g = a.natAbs := by
      calc a'.natAbs * g = (a' * (g : ℤ)).natAbs := by rw [Int.natAbs_mul, Int.natAbs_natCast]
        _ = a.natAbs := by rw [ha_eq]
    exact Nat.eq_div_of_mul_eq_left hg_pos.ne' h1
  have hb'_abs : b'.natAbs = b.natAbs / g := by
    have h1 : b'.natAbs * g = b.natAbs := by
      calc b'.natAbs * g = (b' * (g : ℤ)).natAbs := by rw [Int.natAbs_mul, Int.natAbs_natCast]
        _ = b.natAbs := by rw [hb_eq]
    exact Nat.eq_div_of_mul_eq_left hg_pos.ne' h1
  have hcop : Nat.Coprime b'.natAbs a'.natAbs := by
    rw [ha'_abs, hb'_abs]
    exact (Nat.coprime_div_gcd_div_gcd hg_pos).symm
  obtain ⟨p, hp, hvp_ne, hvp_le⟩ := exists_prime_padicValRat_ne_zero hu
  have : Fact p.Prime := ⟨hp⟩
  have hpadic : a * padicValRat p u + b * padicValRat p v = 0 := by
    have h1 := congrArg (padicValRat p) hab
    rw [padicValRat.mul (zpow_ne_zero _ hu0) (zpow_ne_zero _ hv0),
      padicValRat.zpow, padicValRat.zpow, padicValRat.one] at h1
    exact h1
  have hpadic' : a' * padicValRat p u = (-b') * padicValRat p v := by
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg_pos.ne'
    have h1 : (g : ℤ) * (a' * padicValRat p u + b' * padicValRat p v) = 0 := by
      calc (g : ℤ) * (a' * padicValRat p u + b' * padicValRat p v)
          = (a' * g) * padicValRat p u + (b' * g) * padicValRat p v := by ring
        _ = a * padicValRat p u + b * padicValRat p v := by rw [ha_eq, hb_eq]
        _ = 0 := hpadic
    have h2 := (mul_eq_zero.mp h1).resolve_left hg0
    linarith
  have hdvd_vp : b'.natAbs ∣ (padicValRat p u).natAbs := by
    have hnat : a'.natAbs * (padicValRat p u).natAbs = b'.natAbs * (padicValRat p v).natAbs := by
      have := congrArg Int.natAbs hpadic'
      simpa [Int.natAbs_mul, Int.natAbs_neg] using this
    exact hcop.dvd_of_dvd_mul_left ⟨(padicValRat p v).natAbs, hnat⟩
  have hvp_abs_pos : 0 < (padicValRat p u).natAbs := Int.natAbs_pos.mpr hvp_ne
  have hb'_le_vp : (b'.natAbs : ℝ) ≤ (padicValRat p u).natAbs := by
    exact_mod_cast Nat.le_of_dvd hvp_abs_pos hdvd_vp
  have hb'_lt : (b'.natAbs : ℝ) ≤ 24 * M := by
    have hlogH : Real.log ((u.num.natAbs + u.den : ℕ) : ℝ) ≤ 16 * M := by
      have h1 := Real.log_le_log (by exact_mod_cast Nat.add_pos_right u.num.natAbs u.pos) hHu
      rw [Real.log_pow, show Real.log L = M from rfl,
        show ((16 : ℕ) : ℝ) * M = 16 * M by norm_num] at h1
      exact h1
    have hl2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    calc (b'.natAbs : ℝ) ≤ ((padicValRat p u).natAbs : ℝ) := hb'_le_vp
      _ ≤ Real.log ((u.num.natAbs + u.den : ℕ) : ℝ) / Real.log 2 := hvp_le
      _ ≤ (16 * M) / Real.log 2 := div_le_div_of_nonneg_right hlogH (by linarith)
      _ ≤ (16 * M) / 0.69 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hl2.le
      _ = (16 / 0.69) * M := by ring
      _ ≤ 24 * M := mul_le_mul_of_nonneg_right (by norm_num) hMpos.le
  have hb'_ne : b' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hb_eq
    exact hb0 hb_eq.symm
  have hlog'_rel : (a' : ℝ) * Real.log (u : ℝ) + (b' : ℝ) * Real.log (v : ℝ) = 0 := by
    have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg_pos.ne'
    have h1 : (g : ℝ) * ((a' : ℝ) * Real.log (u : ℝ) + (b' : ℝ) * Real.log (v : ℝ)) = 0 := by
      calc (g : ℝ) * ((a' : ℝ) * Real.log (u : ℝ) + (b' : ℝ) * Real.log (v : ℝ))
          = ((a' * (g : ℤ) : ℤ) : ℝ) * Real.log (u : ℝ) +
            ((b' * (g : ℤ) : ℤ) : ℝ) * Real.log (v : ℝ) := by push_cast; ring
        _ = (a : ℝ) * Real.log (u : ℝ) + (b : ℝ) * Real.log (v : ℝ) := by rw [ha_eq, hb_eq]
        _ = 0 := hlog_rel
    exact (mul_eq_zero.mp h1).resolve_left hgR
  have hlam_eq : (b' : ℝ) * ((m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)) =
      ((m * b' + a' : ℤ) : ℝ) * Real.log (u : ℝ) := by
    push_cast
    linarith
  have hmb_ne : m * b' + a' ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, zero_mul] at hlam_eq
    rcases mul_eq_zero.mp hlam_eq with h1 | h2
    · exact hb'_ne (by exact_mod_cast h1)
    · rw [h2, abs_zero] at hpos; exact lt_irrefl 0 hpos
  have hmb_ge : (1 : ℝ) ≤ |((m * b' + a' : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hmb_ne
  have hlogu_ge : 1 / L ^ 16 ≤ Real.log (u : ℝ) := by
    have h1 := abs_log_rat_ge_of_ne_one (lt_trans zero_lt_one hu) (ne_of_gt hu)
    rw [abs_of_pos hlu_pos] at h1
    exact (one_div_le_one_div_of_le
      (by exact_mod_cast Nat.add_pos_right u.num.natAbs u.pos) hHu).trans h1
  have hb'_absR : |(b' : ℝ)| = (b'.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hlam_low : 1 / (24 * M * L ^ 16) ≤ |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| := by
    have hbpos : (0 : ℝ) < |(b' : ℝ)| := abs_pos.mpr (by exact_mod_cast hb'_ne)
    have hmul_ge : (1 : ℝ) / L ^ 16 ≤ |(b' : ℝ)| * |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| := by
      rw [← abs_mul, hlam_eq, abs_mul, abs_of_pos hlu_pos]
      calc 1 / L ^ 16 = 1 * (1 / L ^ 16) := (one_mul _).symm
        _ ≤ |((m * b' + a' : ℤ) : ℝ)| * Real.log (u : ℝ) :=
            mul_le_mul hmb_ge hlogu_ge (by positivity) (by positivity)
    calc 1 / (24 * M * L ^ 16)
        = (1 / L ^ 16) / (24 * M) := by ring
      _ ≤ (1 / L ^ 16) / |(b' : ℝ)| := by
          refine div_le_div_of_nonneg_left (by positivity) hbpos ?_
          rw [hb'_absR]; exact hb'_lt
      _ ≤ |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| := by
          rwa [div_le_iff₀' hbpos]
  have h20M : Real.exp (-L) ≤ 1 / (24 * M * L ^ 16) := by
    rw [Real.exp_neg, ← one_div]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h24L : 24 * M * L ^ 16 ≤ Real.exp (20 * M) := by
      calc 24 * M * L ^ 16 ≤ Real.exp (4 * M) * (Real.exp M) ^ 16 := by
            rw [← hL_eq]; exact mul_le_mul_of_nonneg_right h24M (by positivity)
        _ = Real.exp (20 * M) := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    have h20L : 20 * M ≤ L := by
      have hM1 : 1 ≤ M := by linarith
      have hM4 : M ≤ M ^ 4 := by
        calc M = M * 1 := (mul_one _).symm
          _ ≤ M * M ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hM1) hMpos.le
          _ = M ^ 4 := by ring
      have hle : 20 * M ≤ 10 ^ 5 * M ^ 4 := by
        calc 20 * M ≤ 10 ^ 5 * M := by linarith
          _ ≤ 10 ^ 5 * M ^ 4 := mul_le_mul_of_nonneg_left hM4 (by norm_num)
      exact hle.trans hM4L
    exact h24L.trans (Real.exp_le_exp.mpr h20L)
  have hexp_L : Real.exp (-D * L * M ^ (4 - 4 * z)) ≤ Real.exp (-L) :=
    Real.exp_le_exp.mpr (neg_DLM_le_neg_L hLpos (by linarith) (by linarith) hz1)
  linarith

lemma abs_F_sub_Q_le {I J R1 S1 : ℕ} {p : ℕ → ℕ → ℤ} {u v : ℚ} {m : ℤ}
    (hu : 1 < u) (hv : 1 < v) (hm : 0 < m)
    {L ρ Pmax : ℝ} (hPmax : ∀ i < I, ∀ j < J, |(p i j : ℝ)| ≤ Pmax)
    (hPmax0 : 0 ≤ Pmax)
    (hρ : ∀ r < R1, ∀ s < S1, (r : ℝ) + (s : ℝ) * m ≤ ρ) (hρ0 : 1 ≤ ρ)
    (hlu0 : 0 ≤ Real.log (u : ℝ)) (hmlu0 : 0 ≤ (m : ℝ) * Real.log (u : ℝ))
    (hlv0 : 0 ≤ Real.log (v : ℝ))
    (hmlu_le : (m : ℝ) * Real.log (u : ℝ) ≤ 2 * L) (hlv_le : Real.log (v : ℝ) ≤ L)
    (hlu_le : Real.log (u : ℝ) ≤ 1)
    {r s : ℕ} (hr : r < R1) (hs : s < S1) :
    ‖(∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, (p i j : ℂ) *
        (((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ) ^ i *
        Complex.exp ((j : ℂ) * (Real.log (u : ℝ) : ℂ) * (((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ))) -
      (((∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, (p i j : ℚ) *
        ((r : ℚ) + (s : ℚ) * m) ^ i * u ^ (j * r) * v ^ (j * s) : ℚ) : ℝ) : ℂ)‖ ≤
      (I : ℝ) * (J : ℝ) * Pmax * ρ ^ I * ((J : ℝ) * (S1 : ℝ)) *
        |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| *
        Real.exp ((J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L) := by
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hu)
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hv)
  have hQcast : (((∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, (p i j : ℚ) *
      ((r : ℚ) + (s : ℚ) * m) ^ i * u ^ (j * r) * v ^ (j * s) : ℚ) : ℝ) : ℂ) =
      ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J, (p i j : ℂ) *
        (((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ) ^ i *
        ((Real.exp ((j : ℝ) * (r : ℝ) * Real.log (u : ℝ) +
          (j : ℝ) * (s : ℝ) * Real.log (v : ℝ)) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hpow_uv : (((u : ℝ) ^ (j * r) * (v : ℝ) ^ (j * s) : ℝ) : ℂ) =
        ((Real.exp ((j : ℝ) * (r : ℝ) * Real.log (u : ℝ) +
          (j : ℝ) * (s : ℝ) * Real.log (v : ℝ)) : ℝ) : ℂ) := by
      congr 1
      rw [Real.exp_add, show (j : ℝ) * (r : ℝ) * Real.log (u : ℝ) =
        ((j * r : ℕ) : ℝ) * Real.log (u : ℝ) by push_cast; ring,
        show (j : ℝ) * (s : ℝ) * Real.log (v : ℝ) =
          ((j * s : ℕ) : ℝ) * Real.log (v : ℝ) by push_cast; ring,
        Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log huR, Real.exp_log hvR]
    push_cast at hpow_uv ⊢
    rw [mul_assoc, hpow_uv]
  rw [hQcast, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hL0 : 0 ≤ L := by
    have := hlv0.trans hlv_le; exact this
  set E := (J : ℝ) * Pmax * ρ ^ I * ((J : ℝ) * (S1 : ℝ)) *
    |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| *
    Real.exp ((J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L)
  have hE0 : 0 ≤ E := by positivity
  refine (Finset.sum_le_card_nsmul _ _ E fun i hi => ?_).trans_eq (by
    rw [Finset.card_range, nsmul_eq_mul]; simp only [E]; ring)
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  set Ej := Pmax * ρ ^ I * ((J : ℝ) * (S1 : ℝ)) *
    |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| *
    Real.exp ((J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L)
  refine (Finset.sum_le_card_nsmul _ _ Ej fun j hj => ?_).trans_eq (by
    rw [Finset.card_range, nsmul_eq_mul]; simp only [E, Ej]; ring)
  have hiI : i < I := Finset.mem_range.mp hi
  have hjJ : j < J := Finset.mem_range.mp hj
  have hterm_eq : (p i j : ℂ) * (((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ) ^ i *
      Complex.exp ((j : ℂ) * (Real.log (u : ℝ) : ℂ) * (((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ)) -
      (p i j : ℂ) * (((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ) ^ i *
      ((Real.exp ((j : ℝ) * (r : ℝ) * Real.log (u : ℝ) +
        (j : ℝ) * (s : ℝ) * Real.log (v : ℝ)) : ℝ) : ℂ) =
      (p i j : ℂ) * (((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ) ^ i *
      ((Real.exp ((j : ℝ) * Real.log (u : ℝ) * ((r : ℝ) + (s : ℝ) * m)) -
        Real.exp ((j : ℝ) * (r : ℝ) * Real.log (u : ℝ) +
          (j : ℝ) * (s : ℝ) * Real.log (v : ℝ)) : ℝ) : ℂ) := by
    have hexpC : Complex.exp ((j : ℂ) * (Real.log (u : ℝ) : ℂ) * (((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ)) =
        ((Real.exp ((j : ℝ) * Real.log (u : ℝ) * ((r : ℝ) + (s : ℝ) * m)) : ℝ) : ℂ) := by
      rw [show (j : ℂ) * (Real.log (u : ℝ) : ℂ) * (((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ) =
        (((j : ℝ) * Real.log (u : ℝ) * ((r : ℝ) + (s : ℝ) * m) : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_exp]
    rw [hexpC]
    push_cast
    ring
  rw [hterm_eq, norm_mul, norm_mul, norm_pow]
  have hp_bd : ‖(p i j : ℂ)‖ ≤ Pmax := by
    rw [show (p i j : ℂ) = (((p i j : ℝ) : ℂ)) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
    exact hPmax i hiI j hjJ
  have hw_nn : (0 : ℝ) ≤ (r : ℝ) + (s : ℝ) * m := by positivity
  have hw_bd : ‖(((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ)‖ ^ i ≤ ρ ^ I := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw_nn]
    exact (pow_le_pow_left₀ hw_nn (hρ r hr s hs) i).trans (pow_le_pow_right₀ hρ0 hiI.le)
  have hexp_diff : ‖((Real.exp ((j : ℝ) * Real.log (u : ℝ) * ((r : ℝ) + (s : ℝ) * m)) -
      Real.exp ((j : ℝ) * (r : ℝ) * Real.log (u : ℝ) +
        (j : ℝ) * (s : ℝ) * Real.log (v : ℝ)) : ℝ) : ℂ)‖ ≤
      ((J : ℝ) * (S1 : ℝ)) * |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| *
        Real.exp ((J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hdiff := abs_exp_sub_exp_le
      ((j : ℝ) * Real.log (u : ℝ) * ((r : ℝ) + (s : ℝ) * m))
      ((j : ℝ) * (r : ℝ) * Real.log (u : ℝ) + (j : ℝ) * (s : ℝ) * Real.log (v : ℝ))
    have hxy : |(j : ℝ) * Real.log (u : ℝ) * ((r : ℝ) + (s : ℝ) * m) -
        ((j : ℝ) * (r : ℝ) * Real.log (u : ℝ) + (j : ℝ) * (s : ℝ) * Real.log (v : ℝ))| ≤
        (J : ℝ) * (S1 : ℝ) * |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| := by
      have heq : (j : ℝ) * Real.log (u : ℝ) * ((r : ℝ) + (s : ℝ) * m) -
          ((j : ℝ) * (r : ℝ) * Real.log (u : ℝ) + (j : ℝ) * (s : ℝ) * Real.log (v : ℝ)) =
          ((j : ℝ) * (s : ℝ)) * ((m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)) := by ring
      rw [heq, abs_mul, abs_of_nonneg (by positivity)]
      have hj_le : (j : ℝ) ≤ J := by exact_mod_cast hjJ.le
      have hs_le : (s : ℝ) ≤ S1 := by exact_mod_cast hs.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul hj_le hs_le (by positivity) (by positivity))
        (abs_nonneg _)
    have hmax : max ((j : ℝ) * Real.log (u : ℝ) * ((r : ℝ) + (s : ℝ) * m))
        ((j : ℝ) * (r : ℝ) * Real.log (u : ℝ) + (j : ℝ) * (s : ℝ) * Real.log (v : ℝ)) ≤
        (J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L := by
      have hj_le : (j : ℝ) ≤ J := by exact_mod_cast hjJ.le
      have hr_le : (r : ℝ) ≤ R1 := by exact_mod_cast hr.le
      have hs_le : (s : ℝ) ≤ S1 := by exact_mod_cast hs.le
      refine max_le ?_ ?_
      · calc (j : ℝ) * Real.log (u : ℝ) * ((r : ℝ) + (s : ℝ) * m)
            = (j : ℝ) * (r : ℝ) * Real.log (u : ℝ) + (j : ℝ) * (s : ℝ) * ((m : ℝ) * Real.log (u : ℝ)) := by ring
          _ ≤ (J : ℝ) * (R1 : ℝ) * 1 + (J : ℝ) * (S1 : ℝ) * (2 * L) := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul (mul_le_mul hj_le hr_le (by positivity) (by positivity))
                  hlu_le hlu0 (by positivity)
              · exact mul_le_mul (mul_le_mul hj_le hs_le (by positivity) (by positivity))
                  hmlu_le hmlu0 (by positivity)
          _ = (J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L := by ring
      · calc (j : ℝ) * (r : ℝ) * Real.log (u : ℝ) + (j : ℝ) * (s : ℝ) * Real.log (v : ℝ)
            ≤ (J : ℝ) * (R1 : ℝ) * 1 + (J : ℝ) * (S1 : ℝ) * L := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul (mul_le_mul hj_le hr_le (by positivity) (by positivity))
                  hlu_le hlu0 (by positivity)
              · exact mul_le_mul (mul_le_mul hj_le hs_le (by positivity) (by positivity))
                  hlv_le hlv0 (by positivity)
          _ ≤ (J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L := by
              have : 0 ≤ (J : ℝ) * (S1 : ℝ) * L := by positivity
              linarith
    exact hdiff.trans (mul_le_mul hxy (Real.exp_le_exp.mpr hmax) (Real.exp_pos _).le (by positivity))
  calc ‖(p i j : ℂ)‖ * ‖(((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ)‖ ^ i *
      ‖((Real.exp ((j : ℝ) * Real.log (u : ℝ) * ((r : ℝ) + (s : ℝ) * m)) -
        Real.exp ((j : ℝ) * (r : ℝ) * Real.log (u : ℝ) +
          (j : ℝ) * (s : ℝ) * Real.log (v : ℝ)) : ℝ) : ℂ)‖
      ≤ (Pmax * ρ ^ I) * (((J : ℝ) * (S1 : ℝ)) * |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| *
          Real.exp ((J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L)) := by
        exact mul_le_mul (mul_le_mul hp_bd hw_bd (pow_nonneg (norm_nonneg _) _) hPmax0)
          hexp_diff (norm_nonneg _) (by positivity)
    _ = Ej := by simp only [Ej]; ring

set_option maxHeartbeats 800000 in
lemma analytic_extrap_contra {D S z : ℝ} {u v : ℚ} {m : ℤ}
    (hM100 : 100 ≤ Real.log (Real.log S)) (hLpos_in : 0 < Real.log S)
    (hz1 : z ≤ 1) (hD : 10 ^ 15 ≤ D) (hu : 1 < u) (hv : 1 < v) (hm : 0 < m)
    (hm_leR : (m : ℝ) ≤ (Real.log S) ^ 16)
    (hlv : |Real.log (v : ℝ)| ≤ Real.log S / Real.log (Real.log S) *
      Real.exp (-(Real.log (Real.log S)) ^ z))
    (hlog_u : Real.log (u : ℝ) ≤ Real.exp (-(Real.log (Real.log S)) ^ z))
    (hmlog_u : (m : ℝ) * Real.log (u : ℝ) ≤ 2 * (Real.log S / Real.log (Real.log S)) *
      Real.exp (-(Real.log (Real.log S)) ^ z))
    (hcontra : |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| <
      Real.exp (-D * Real.log S * (Real.log (Real.log S)) ^ (4 - 4 * z)))
    {I J R0 S0 R1 S1 r1 s1 : ℕ}
    (hR0_le_R1 : R0 ≤ R1) (hS0_le_S1 : S0 ≤ S1)
    (hr1 : r1 < R1) (hs1 : s1 < S1) (hR1_1 : 1 ≤ R1)
    (hR0_lt_m : R0 < m.natAbs)
    (hJ_hi : (J : ℝ) ≤ 1001 * (Real.log (Real.log S)) ^ (1 - z))
    (hI_hi : (I : ℝ) ≤ (3 * 10 ^ 10 + 1) * Real.log S * (Real.log (Real.log S)) ^ (2 - 3 * z))
    (hN0_lo : 9.98 * 10 ^ 12 * Real.log S * (Real.log (Real.log S)) ^ (3 - 4 * z) ≤
      ((R0 * S0 : ℕ) : ℝ))
    (hN0_hi : ((R0 * S0 : ℕ) : ℝ) ≤
      10 ^ 13 * Real.log S * (Real.log (Real.log S)) ^ (3 - 4 * z))
    (hR1_hi : (R1 : ℝ) ≤ 1.6 * 10 ^ 7 * Real.log S * (Real.log (Real.log S)) ^ (1 - 2 * z))
    (hS1_hi : (S1 : ℝ) ≤ 2 * 10 ^ 8 * (Real.log (Real.log S)) ^ (2 - 2 * z))
    (hR1_L2 : (R1 : ℝ) ≤ (Real.log S) ^ 2)
    (hS1_L : (S1 : ℝ) ≤ Real.log S)
    (p : ℕ → ℕ → ℤ)
    (hp_bd : ∀ i < I, ∀ j < J, |(p i j : ℝ)| ≤
      Real.exp (6.1 * 10 ^ 11 * (Real.log S * (Real.log (Real.log S)) ^ (3 - 3 * z))))
    (hQ_zero : ∀ r < R0, ∀ s < S0,
      (∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
        (p i j : ℚ) * ((r : ℚ) + (s : ℚ) * m) ^ i * u ^ (j * r) * v ^ (j * s)) = 0)
    (hQ_low : Real.exp (-4.7 * 10 ^ 11 * (Real.log S * (Real.log (Real.log S)) ^ (3 - 3 * z))) ≤
      |((∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
        (p i j : ℚ) * ((r1 : ℚ) + (s1 : ℚ) * m) ^ i * u ^ (j * r1) * v ^ (j * s1) : ℚ) : ℝ)|) :
    False := by
  classical
  set L := Real.log S
  set M := Real.log L
  set Λ := |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)|
  have hMpos : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hLpos : 0 < L := hLpos_in
  have hL_eq : L = Real.exp M := (Real.exp_log hLpos).symm
  obtain ⟨_, _, _, h2L⟩ := exp_M_bounds hM100 hL_eq
  have hlu_pos : 0 < Real.log (u : ℝ) := Real.log_pos (by exact_mod_cast hu)
  have hlv_pos : 0 < Real.log (v : ℝ) := Real.log_pos (by exact_mod_cast hv)
  have hM_z_hi : M ^ z ≤ M := by
    simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM1 hz1
  have hM_33z_lo : 1 ≤ M ^ (3 - 3 * z) := Real.one_le_rpow hM1 (by linarith)
  have hM_33z_44z : M ^ (3 - 3 * z) ≤ M ^ (4 - 4 * z) :=
    Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have hM_prod_34_z : M ^ (3 - 4 * z) * M ^ z = M ^ (3 - 3 * z) := by
    rw [← Real.rpow_add hMpos]; ring_nf
  have hM_prod_34_1 : M ^ (3 - 4 * z) * M = M ^ (4 - 4 * z) := by
    conv_rhs => rw [show (4 - 4 * z : ℝ) = (3 - 4 * z) + 1 by ring, Real.rpow_add hMpos, Real.rpow_one]
  have hM_prod_23_1_33 : M ^ (2 - 3 * z) * M = M ^ (3 - 3 * z) := by
    conv_rhs => rw [show (3 - 3 * z : ℝ) = (2 - 3 * z) + 1 by ring, Real.rpow_add hMpos, Real.rpow_one]
  have hM_prod_12_1_1 : M ^ (1 - 2 * z) * M ^ (1 - z) * M = M ^ (3 - 3 * z) := by
    rw [← Real.rpow_add hMpos,
      show M ^ (1 - 2 * z + (1 - z)) * M = M ^ (1 - 2 * z + (1 - z)) * M ^ (1 : ℝ) by
        rw [Real.rpow_one],
      ← Real.rpow_add hMpos]
    ring_nf
  have hM_prod_1_22 : M ^ (1 - z) * M ^ (2 - 2 * z) = M ^ (3 - 3 * z) := by
    rw [← Real.rpow_add hMpos]; ring_nf
  set B1 : ℝ := L * M ^ (3 - 3 * z)
  set B2 : ℝ := L * M ^ (4 - 4 * z)
  have hB1_ge : 1 ≤ B1 := one_le_mul_of_one_le_of_one_le (by linarith) hM_33z_lo
  have hB1_le_B2 : B1 ≤ B2 := mul_le_mul_of_nonneg_left hM_33z_44z hLpos.le
  set N0 : ℕ := R0 * S0
  set ρ : ℝ := (R1 : ℝ) + (S1 : ℝ) * (m : ℝ)
  have hρ_ge : 1 ≤ ρ := by
    have : (1 : ℝ) ≤ (R1 : ℝ) := by exact_mod_cast hR1_1
    have : 0 ≤ (S1 : ℝ) * (m : ℝ) := by positivity
    linarith
  have hρ_le : ρ ≤ L ^ 18 := by
    have hL17 : (R1 : ℝ) ≤ L ^ 17 := by
      calc (R1 : ℝ) ≤ L ^ 2 := hR1_L2
        _ = L ^ 2 * 1 := (mul_one _).symm
        _ ≤ L ^ 2 * L ^ 15 := mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith)) (by positivity)
        _ = L ^ 17 := by ring
    have hS1m : (S1 : ℝ) * (m : ℝ) ≤ L ^ 17 := by
      calc (S1 : ℝ) * (m : ℝ) ≤ L * L ^ 16 := mul_le_mul hS1_L hm_leR (by exact_mod_cast hm.le) hLpos.le
        _ = L ^ 17 := by ring
    calc ρ = (R1 : ℝ) + (S1 : ℝ) * (m : ℝ) := rfl
      _ ≤ L ^ 17 + L ^ 17 := add_le_add hL17 hS1m
      _ = 2 * L ^ 17 := by ring
      _ ≤ L * L ^ 17 := mul_le_mul_of_nonneg_right h2L (by positivity)
      _ = L ^ 18 := by ring
  have hρ_exp : ρ ≤ Real.exp (18 * M) := by
    calc ρ ≤ L ^ 18 := hρ_le
      _ = Real.exp (18 * M) := by rw [hL_eq, ← Real.exp_nat_mul]; ring_nf
  set α : ℝ := M * Real.exp (M ^ z)
  set W : ℝ := α * ρ
  have hα_ge : 100 ≤ α := by
    calc (100 : ℝ) ≤ M := hM100
      _ = M * 1 := (mul_one _).symm
      _ ≤ M * Real.exp (M ^ z) := mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) hMpos.le
  have hρ_lt_W : ρ < W := by
    calc ρ = 1 * ρ := (one_mul _).symm
      _ < α * ρ := mul_lt_mul_of_pos_right (by linarith) (by linarith)
  have hW_ge1 : 1 ≤ W := by linarith
  have hW_exp : W ≤ Real.exp (20 * M) := by
    have hMz_exp : Real.exp (M ^ z) ≤ Real.exp M := Real.exp_le_exp.mpr hM_z_hi
    have hM_exp : M ≤ Real.exp M := by rw [← hL_eq]; linarith
    calc W = M * Real.exp (M ^ z) * ρ := rfl
      _ ≤ Real.exp M * Real.exp M * Real.exp (18 * M) :=
          mul_le_mul (mul_le_mul hM_exp hMz_exp (Real.exp_pos _).le (Real.exp_pos _).le)
            hρ_exp (by positivity) (by positivity)
      _ = Real.exp (20 * M) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h2W_exp : 2 * W ≤ Real.exp (21 * M) := by
    have h2 : (2 : ℝ) ≤ Real.exp M := by linarith [hL_eq]
    calc 2 * W ≤ Real.exp M * Real.exp (20 * M) := mul_le_mul h2 hW_exp (by positivity) (by positivity)
      _ = Real.exp (21 * M) := by rw [← Real.exp_add]; ring_nf
  let Q : ℕ → ℕ → ℚ := fun r s =>
    ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
      (p i j : ℚ) * ((r : ℚ) + (s : ℚ) * m) ^ i * u ^ (j * r) * v ^ (j * s)
  let F : ℂ → ℂ := fun w => ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
    (p i j : ℂ) * w ^ i * Complex.exp ((j : ℂ) * (Real.log (u : ℝ) : ℂ) * w)
  have hFd : Differentiable ℂ F := by
    refine Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ => ?_
    refine ((differentiable_pow i).const_mul _).mul ?_
    exact (differentiable_id.const_mul _).cexp
  have hMW : ∀ w : ℂ, ‖w‖ = W → ‖F w‖ ≤ Real.exp (1.7 * 10 ^ 12 * B1) := by
    intro w hw
    have hlog_u_le1 : Real.log (u : ℝ) ≤ 1 :=
      hlog_u.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
    have hJWu : (J : ℝ) * W * Real.log (u : ℝ) ≤ 4.2 * 10 ^ 11 * B1 := by
      have hterm1 : M * Real.exp (M ^ z) * (R1 : ℝ) * Real.log (u : ℝ) ≤ M * (R1 : ℝ) := by
        have hmul : Real.exp (M ^ z) * Real.log (u : ℝ) ≤ 1 := by
          calc Real.exp (M ^ z) * Real.log (u : ℝ)
              ≤ Real.exp (M ^ z) * Real.exp (-(M ^ z)) :=
                mul_le_mul_of_nonneg_left hlog_u (Real.exp_pos _).le
            _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        calc M * Real.exp (M ^ z) * (R1 : ℝ) * Real.log (u : ℝ)
            = M * (R1 : ℝ) * (Real.exp (M ^ z) * Real.log (u : ℝ)) := by ring
          _ ≤ M * (R1 : ℝ) * 1 := mul_le_mul_of_nonneg_left hmul (by positivity)
          _ = M * (R1 : ℝ) := mul_one _
      have hterm2 : M * Real.exp (M ^ z) * (S1 : ℝ) * ((m : ℝ) * Real.log (u : ℝ)) ≤
          2 * L * (S1 : ℝ) := by
        have hmul : M * Real.exp (M ^ z) * ((m : ℝ) * Real.log (u : ℝ)) ≤ 2 * L := by
          calc M * Real.exp (M ^ z) * ((m : ℝ) * Real.log (u : ℝ))
              ≤ M * Real.exp (M ^ z) * (2 * (L / M) * Real.exp (-(M ^ z))) :=
                mul_le_mul_of_nonneg_left hmlog_u (by positivity)
            _ = (2 * L) * (M / M) * (Real.exp (M ^ z) * Real.exp (-(M ^ z))) := by ring
            _ = 2 * L := by
                rw [div_self hMpos.ne', mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        calc M * Real.exp (M ^ z) * (S1 : ℝ) * ((m : ℝ) * Real.log (u : ℝ))
            = (S1 : ℝ) * (M * Real.exp (M ^ z) * ((m : ℝ) * Real.log (u : ℝ))) := by ring
          _ ≤ (S1 : ℝ) * (2 * L) := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg _)
          _ = 2 * L * (S1 : ℝ) := by ring
      have hWu : W * Real.log (u : ℝ) ≤ M * (R1 : ℝ) + 2 * L * (S1 : ℝ) := by
        calc W * Real.log (u : ℝ)
            = M * Real.exp (M ^ z) * (R1 : ℝ) * Real.log (u : ℝ) +
              M * Real.exp (M ^ z) * (S1 : ℝ) * ((m : ℝ) * Real.log (u : ℝ)) := by
              dsimp [W, α, ρ]; ring
          _ ≤ M * (R1 : ℝ) + 2 * L * (S1 : ℝ) := add_le_add hterm1 hterm2
      have hJMR1 : (J : ℝ) * (M * (R1 : ℝ)) ≤ 1001 * (1.6 * 10 ^ 7) * B1 := by
        calc (J : ℝ) * (M * (R1 : ℝ))
            ≤ (1001 * M ^ (1 - z)) * (M * (1.6 * 10 ^ 7 * L * M ^ (1 - 2 * z))) :=
              mul_le_mul hJ_hi (mul_le_mul_of_nonneg_left hR1_hi hMpos.le) (by positivity) (by positivity)
          _ = 1001 * (1.6 * 10 ^ 7) * (L * (M ^ (1 - 2 * z) * M ^ (1 - z) * M)) := by ring
          _ = 1001 * (1.6 * 10 ^ 7) * B1 := by rw [hM_prod_12_1_1]
      have hJLS1 : (J : ℝ) * (2 * L * (S1 : ℝ)) ≤ 2 * 1001 * (2 * 10 ^ 8) * B1 := by
        calc (J : ℝ) * (2 * L * (S1 : ℝ))
            ≤ (1001 * M ^ (1 - z)) * (2 * L * (2 * 10 ^ 8 * M ^ (2 - 2 * z))) :=
              mul_le_mul hJ_hi (mul_le_mul_of_nonneg_left hS1_hi (by positivity))
                (by positivity) (by positivity)
          _ = 2 * 1001 * (2 * 10 ^ 8) * (L * (M ^ (1 - z) * M ^ (2 - 2 * z))) := by ring
          _ = 2 * 1001 * (2 * 10 ^ 8) * B1 := by rw [hM_prod_1_22]
      have hc : 1001 * (1.6 * 10 ^ 7 : ℝ) + 2 * 1001 * (2 * 10 ^ 8) ≤ 4.2 * 10 ^ 11 := by norm_num
      calc (J : ℝ) * W * Real.log (u : ℝ)
          = (J : ℝ) * (W * Real.log (u : ℝ)) := by ring
        _ ≤ (J : ℝ) * (M * (R1 : ℝ) + 2 * L * (S1 : ℝ)) :=
            mul_le_mul_of_nonneg_left hWu (Nat.cast_nonneg _)
        _ = (J : ℝ) * (M * (R1 : ℝ)) + (J : ℝ) * (2 * L * (S1 : ℝ)) := by ring
        _ ≤ (1001 * (1.6 * 10 ^ 7) + 2 * 1001 * (2 * 10 ^ 8)) * B1 := by linarith
        _ ≤ 4.2 * 10 ^ 11 * B1 := mul_le_mul_of_nonneg_right hc (by linarith)
    have hterm_bd : ∀ i ∈ Finset.range I, ∀ j ∈ Finset.range J,
        ‖(p i j : ℂ) * w ^ i * Complex.exp ((j : ℂ) * (Real.log (u : ℝ) : ℂ) * w)‖ ≤
          Real.exp (1.65 * 10 ^ 12 * B1) := by
      intro i hi j hj
      have hiI : i < I := Finset.mem_range.mp hi
      have hjJ : j < J := Finset.mem_range.mp hj
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
      have hp_term : ‖(p i j : ℂ)‖ ≤ Real.exp (6.1 * 10 ^ 11 * B1) := by
        rw [show (p i j : ℂ) = (((p i j : ℝ) : ℂ)) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
        exact hp_bd i hiI j hjJ
      have hw_term : ‖w‖ ^ i ≤ Real.exp (20 * M * I) := by
        rw [hw]
        calc W ^ i ≤ (Real.exp (20 * M)) ^ i := pow_le_pow_left₀ (by linarith) hW_exp i
          _ = Real.exp ((i : ℝ) * (20 * M)) := (Real.exp_nat_mul _ _).symm
          _ ≤ Real.exp ((I : ℝ) * (20 * M)) :=
              Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hiI.le) (by positivity))
          _ = Real.exp (20 * M * I) := by ring_nf
      have hexp_term : Real.exp ((j : ℂ) * (Real.log (u : ℝ) : ℂ) * w).re ≤
          Real.exp (4.2 * 10 ^ 11 * B1) := by
        refine Real.exp_le_exp.mpr ?_
        have hre : ((j : ℂ) * (Real.log (u : ℝ) : ℂ) * w).re = (j : ℝ) * Real.log (u : ℝ) * w.re := by
          simp [Complex.mul_re]
        rw [hre]
        have hwre : w.re ≤ W := hw ▸ Complex.re_le_norm w
        calc (j : ℝ) * Real.log (u : ℝ) * w.re
            ≤ (j : ℝ) * Real.log (u : ℝ) * W := mul_le_mul_of_nonneg_left hwre (by positivity)
          _ ≤ (J : ℝ) * Real.log (u : ℝ) * W :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hjJ.le) hlu_pos.le)
                (by linarith)
          _ = (J : ℝ) * W * Real.log (u : ℝ) := by ring
          _ ≤ 4.2 * 10 ^ 11 * B1 := hJWu
      have h20MI : 20 * M * (I : ℝ) ≤ 6.1 * 10 ^ 11 * B1 := by
        calc 20 * M * (I : ℝ) ≤ 20 * M * ((3 * 10 ^ 10 + 1) * L * M ^ (2 - 3 * z)) :=
              mul_le_mul_of_nonneg_left hI_hi (by positivity)
          _ = 20 * (3 * 10 ^ 10 + 1) * (L * (M ^ (2 - 3 * z) * M)) := by ring
          _ = 20 * (3 * 10 ^ 10 + 1) * B1 := by rw [hM_prod_23_1_33]
          _ ≤ 6.1 * 10 ^ 11 * B1 := by
              have : 20 * (3 * 10 ^ 10 + 1 : ℝ) ≤ 6.1 * 10 ^ 11 := by norm_num
              exact mul_le_mul_of_nonneg_right this (by linarith)
      calc ‖(p i j : ℂ)‖ * ‖w‖ ^ i * Real.exp ((j : ℂ) * (Real.log (u : ℝ) : ℂ) * w).re
          ≤ Real.exp (6.1 * 10 ^ 11 * B1) * Real.exp (20 * M * I) * Real.exp (4.2 * 10 ^ 11 * B1) :=
            mul_le_mul (mul_le_mul hp_term hw_term (by positivity) (by positivity))
              hexp_term (Real.exp_pos _).le (by positivity)
        _ = Real.exp (6.1 * 10 ^ 11 * B1 + 20 * M * I + 4.2 * 10 ^ 11 * B1) := by
            rw [← Real.exp_add, ← Real.exp_add]
        _ ≤ Real.exp (1.65 * 10 ^ 12 * B1) := Real.exp_le_exp.mpr (by linarith)
    have hIJ_exp2 : (I : ℝ) * (J : ℝ) ≤ Real.exp (0.05 * 10 ^ 12 * B1) := by
      have hIexp : (I : ℝ) ≤ Real.exp (I : ℝ) := by linarith [Real.add_one_le_exp (I : ℝ)]
      have hJexp : (J : ℝ) ≤ Real.exp (J : ℝ) := by linarith [Real.add_one_le_exp (J : ℝ)]
      have hsum_le : (I : ℝ) + (J : ℝ) ≤ 0.05 * 10 ^ 12 * B1 := by
        have hI_bd : (I : ℝ) ≤ (3 * 10 ^ 10 + 1) * B1 := by
          have hMle : M ^ (2 - 3 * z) ≤ M ^ (3 - 3 * z) :=
            Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
          calc (I : ℝ) ≤ (3 * 10 ^ 10 + 1) * L * M ^ (2 - 3 * z) := hI_hi
            _ ≤ (3 * 10 ^ 10 + 1) * L * M ^ (3 - 3 * z) :=
                mul_le_mul_of_nonneg_left hMle (by positivity)
            _ = (3 * 10 ^ 10 + 1) * B1 := by dsimp [B1]; ring
        have hJ_bd : (J : ℝ) ≤ 1001 * B1 := by
          have hMle : M ^ (1 - z) ≤ L * M ^ (3 - 3 * z) :=
            (Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)).trans
              (le_mul_of_one_le_left (by positivity) (by linarith))
          calc (J : ℝ) ≤ 1001 * M ^ (1 - z) := hJ_hi
            _ ≤ 1001 * (L * M ^ (3 - 3 * z)) := mul_le_mul_of_nonneg_left hMle (by norm_num)
            _ = 1001 * B1 := by dsimp [B1]
        linarith
      exact (mul_le_mul hIexp hJexp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans
        ((Real.exp_add _ _).symm.le.trans (Real.exp_le_exp.mpr hsum_le))
    have hsum_bd : ‖F w‖ ≤ (I : ℝ) * (J : ℝ) * Real.exp (1.65 * 10 ^ 12 * B1) := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ ((J : ℝ) * Real.exp (1.65 * 10 ^ 12 * B1)) fun i hi => ?_).trans_eq
        (by rw [Finset.card_range, nsmul_eq_mul]; ring)
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ (Real.exp (1.65 * 10 ^ 12 * B1)) fun j hj =>
        hterm_bd i hi j hj).trans_eq (by rw [Finset.card_range, nsmul_eq_mul])
    calc ‖F w‖ ≤ Real.exp (0.05 * 10 ^ 12 * B1) * Real.exp (1.65 * 10 ^ 12 * B1) :=
          hsum_bd.trans (mul_le_mul_of_nonneg_right hIJ_exp2 (Real.exp_pos _).le)
      _ = Real.exp (1.7 * 10 ^ 12 * B1) := by rw [← Real.exp_add]; ring_nf
  have hFsubQ_le : ∀ r < R1, ∀ s < S1,
      ‖F (((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ) - ((Q r s : ℚ) : ℂ)‖ ≤
        Λ * Real.exp (2 * 10 ^ 12 * B1) := by
    intro r hr s hs
    have hρ_rs : ∀ r' < R1, ∀ s' < S1, (r' : ℝ) + (s' : ℝ) * m ≤ ρ := by
      intro r' hr' s' hs'
      dsimp [ρ]; gcongr
    have hlu_le1 : Real.log (u : ℝ) ≤ 1 :=
      hlog_u.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
    have hmlu_2L : (m : ℝ) * Real.log (u : ℝ) ≤ 2 * L := by
      have h1 : Real.exp (-(M ^ z)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      have h2 : 2 * (L / M) * Real.exp (-(M ^ z)) ≤ 2 * L := by
        calc 2 * (L / M) * Real.exp (-(M ^ z))
            ≤ 2 * (L / 1) * 1 := mul_le_mul (mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_left hLpos.le (by norm_num) hM1) (by norm_num))
              h1 (Real.exp_pos _).le (by positivity)
          _ = 2 * L := by ring
      exact hmlog_u.trans h2
    have hlv_L : Real.log (v : ℝ) ≤ L := by
      have h1 : |Real.log (v : ℝ)| ≤ L := by
        have h2 : L / M * Real.exp (-(M ^ z)) ≤ L := by
          calc L / M * Real.exp (-(M ^ z)) ≤ (L / 1) * 1 :=
                mul_le_mul (div_le_div_of_nonneg_left hLpos.le (by norm_num) hM1)
                  (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))) (Real.exp_pos _).le (by positivity)
            _ = L := by ring
        exact hlv.trans h2
      exact (le_abs_self _).trans h1
    have hdiff := abs_F_sub_Q_le (I := I) (J := J) (R1 := R1) (S1 := S1) (p := p)
      hu hv hm (Pmax := Real.exp (6.1 * 10 ^ 11 * B1)) hp_bd (Real.exp_pos _).le hρ_rs hρ_ge
      hlu_pos.le (by positivity) hlv_pos.le hmlu_2L hlv_L hlu_le1 hr hs
    have hpref : (I : ℝ) * (J : ℝ) * Real.exp (6.1 * 10 ^ 11 * B1) * ρ ^ I * ((J : ℝ) * (S1 : ℝ)) *
        Real.exp ((J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L) ≤ Real.exp (2 * 10 ^ 12 * B1) := by
      have hρI : ρ ^ I ≤ Real.exp (6.1 * 10 ^ 11 * B1) := by
        calc ρ ^ I ≤ (Real.exp (18 * M)) ^ I := pow_le_pow_left₀ (by linarith) hρ_exp I
          _ = Real.exp ((I : ℝ) * (18 * M)) := (Real.exp_nat_mul _ _).symm
          _ ≤ Real.exp (6.1 * 10 ^ 11 * B1) := Real.exp_le_exp.mpr (by
              calc (I : ℝ) * (18 * M) ≤ ((3 * 10 ^ 10 + 1) * L * M ^ (2 - 3 * z)) * (18 * M) :=
                    mul_le_mul_of_nonneg_right hI_hi (by positivity)
                _ = 18 * (3 * 10 ^ 10 + 1) * (L * (M ^ (2 - 3 * z) * M)) := by ring
                _ = 18 * (3 * 10 ^ 10 + 1) * B1 := by rw [hM_prod_23_1_33]
                _ ≤ 6.1 * 10 ^ 11 * B1 := by
                    have : 18 * (3 * 10 ^ 10 + 1 : ℝ) ≤ 6.1 * 10 ^ 11 := by norm_num
                    exact mul_le_mul_of_nonneg_right this (by linarith))
      have hJR1_2JS1L : (J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L ≤ 4.3 * 10 ^ 11 * B1 := by
        have h1 : (J : ℝ) * (R1 : ℝ) ≤ 1001 * (1.6 * 10 ^ 7) * B1 := by
          have : M ^ (1 - z) * M ^ (1 - 2 * z) ≤ M ^ (3 - 3 * z) :=
            (Real.rpow_add hMpos _ _).symm.le.trans (Real.rpow_le_rpow_of_exponent_le hM1 (by linarith))
          calc (J : ℝ) * (R1 : ℝ) ≤ (1001 * M ^ (1 - z)) * (1.6 * 10 ^ 7 * L * M ^ (1 - 2 * z)) :=
                mul_le_mul hJ_hi hR1_hi (Nat.cast_nonneg _) (by positivity)
            _ = 1001 * (1.6 * 10 ^ 7) * (L * (M ^ (1 - z) * M ^ (1 - 2 * z))) := by ring
            _ ≤ 1001 * (1.6 * 10 ^ 7) * B1 := mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left this hLpos.le) (by positivity)
        have h2 : 2 * (J : ℝ) * (S1 : ℝ) * L ≤ 2 * 1001 * (2 * 10 ^ 8) * B1 := by
          calc 2 * (J : ℝ) * (S1 : ℝ) * L
              ≤ 2 * (1001 * M ^ (1 - z)) * (2 * 10 ^ 8 * M ^ (2 - 2 * z)) * L := by
                gcongr
            _ = 2 * 1001 * (2 * 10 ^ 8) * (L * (M ^ (1 - z) * M ^ (2 - 2 * z))) := by ring
            _ = 2 * 1001 * (2 * 10 ^ 8) * B1 := by rw [hM_prod_1_22]
        have hc : 1001 * (1.6 * 10 ^ 7 : ℝ) + 2 * 1001 * (2 * 10 ^ 8) ≤ 4.3 * 10 ^ 11 := by norm_num
        linarith [mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ B1)]
      have hIJJS : (I : ℝ) * (J : ℝ) * ((J : ℝ) * (S1 : ℝ)) ≤ Real.exp (0.1 * 10 ^ 12 * B1) := by
        have h1 : (I : ℝ) ≤ Real.exp (I : ℝ) := by linarith [Real.add_one_le_exp (I : ℝ)]
        have h2 : (J : ℝ) ≤ Real.exp (J : ℝ) := by linarith [Real.add_one_le_exp (J : ℝ)]
        have h3 : (S1 : ℝ) ≤ Real.exp (S1 : ℝ) := by linarith [Real.add_one_le_exp (S1 : ℝ)]
        have hI_bd : (I : ℝ) ≤ (3 * 10 ^ 10 + 1) * B1 := by
          have hMle : M ^ (2 - 3 * z) ≤ M ^ (3 - 3 * z) :=
            Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
          calc (I : ℝ) ≤ (3 * 10 ^ 10 + 1) * L * M ^ (2 - 3 * z) := hI_hi
            _ ≤ (3 * 10 ^ 10 + 1) * L * M ^ (3 - 3 * z) :=
                mul_le_mul_of_nonneg_left hMle (by positivity)
            _ = (3 * 10 ^ 10 + 1) * B1 := by dsimp [B1]; ring
        have hJ_bd : (J : ℝ) ≤ 1001 * B1 := by
          have hMle : M ^ (1 - z) ≤ B1 :=
            (Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)).trans
              (le_mul_of_one_le_left (by positivity) (by linarith))
          exact hJ_hi.trans (mul_le_mul_of_nonneg_left hMle (by norm_num))
        have hS1_bd : (S1 : ℝ) ≤ 2 * 10 ^ 8 * B1 := by
          have hMle : M ^ (2 - 2 * z) ≤ B1 :=
            (Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)).trans
              (le_mul_of_one_le_left (by positivity) (by linarith))
          exact hS1_hi.trans (mul_le_mul_of_nonneg_left hMle (by norm_num))
        have hsum : (I : ℝ) + (J : ℝ) + (J : ℝ) + (S1 : ℝ) ≤ 0.1 * 10 ^ 12 * B1 := by linarith
        calc (I : ℝ) * (J : ℝ) * ((J : ℝ) * (S1 : ℝ))
            ≤ Real.exp (I : ℝ) * Real.exp (J : ℝ) * (Real.exp (J : ℝ) * Real.exp (S1 : ℝ)) := by
              exact mul_le_mul (mul_le_mul h1 h2 (Nat.cast_nonneg _) (Real.exp_pos _).le)
                (mul_le_mul h2 h3 (Nat.cast_nonneg _) (Real.exp_pos _).le)
                (by positivity) (by positivity)
          _ = Real.exp ((I : ℝ) + (J : ℝ) + (J : ℝ) + (S1 : ℝ)) := by
              rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
          _ ≤ Real.exp (0.1 * 10 ^ 12 * B1) := Real.exp_le_exp.mpr hsum
      calc (I : ℝ) * (J : ℝ) * Real.exp (6.1 * 10 ^ 11 * B1) * ρ ^ I * ((J : ℝ) * (S1 : ℝ)) *
            Real.exp ((J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L)
          = ((I : ℝ) * (J : ℝ) * ((J : ℝ) * (S1 : ℝ))) * Real.exp (6.1 * 10 ^ 11 * B1) * ρ ^ I *
              Real.exp ((J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L) := by ring
        _ ≤ Real.exp (0.1 * 10 ^ 12 * B1) * Real.exp (6.1 * 10 ^ 11 * B1) *
              Real.exp (6.1 * 10 ^ 11 * B1) * Real.exp (4.3 * 10 ^ 11 * B1) := by
            gcongr
        _ = Real.exp ((0.1 + 0.61 + 0.61 + 0.43) * 10 ^ 12 * B1) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp (2 * 10 ^ 12 * B1) := Real.exp_le_exp.mpr (by linarith)
    rw [show ((Q r s : ℚ) : ℂ) = (((Q r s : ℚ) : ℝ) : ℂ) by push_cast; rfl]
    calc ‖F (((r : ℝ) + (s : ℝ) * m : ℝ) : ℂ) - (((Q r s : ℚ) : ℝ) : ℂ)‖
        ≤ (I : ℝ) * (J : ℝ) * Real.exp (6.1 * 10 ^ 11 * B1) * ρ ^ I * ((J : ℝ) * (S1 : ℝ)) * Λ *
            Real.exp ((J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L) := hdiff
      _ = ((I : ℝ) * (J : ℝ) * Real.exp (6.1 * 10 ^ 11 * B1) * ρ ^ I * ((J : ℝ) * (S1 : ℝ)) *
            Real.exp ((J : ℝ) * (R1 : ℝ) + 2 * (J : ℝ) * (S1 : ℝ) * L)) * Λ := by ring
      _ ≤ Real.exp (2 * 10 ^ 12 * B1) * Λ := mul_le_mul_of_nonneg_right hpref (abs_nonneg _)
      _ = Λ * Real.exp (2 * 10 ^ 12 * B1) := by ring
  let Z0 : Finset ℤ := (Finset.range R0 ×ˢ Finset.range S0).image fun rs : ℕ × ℕ => (rs.1 : ℤ) + (rs.2 : ℤ) * m
  have hZ0_inj : Set.InjOn (fun rs : ℕ × ℕ => (rs.1 : ℤ) + (rs.2 : ℤ) * m)
      ((Finset.range R0 ×ˢ Finset.range S0 : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro ⟨r₁, s₁⟩ h1 ⟨r₂, s₂⟩ h2 heq
    have h1' := Finset.mem_coe.mp h1
    have h2' := Finset.mem_coe.mp h2
    have hr₁ : r₁ < R0 := Finset.mem_range.mp (Finset.mem_product.mp h1').1
    have hr₂ : r₂ < R0 := Finset.mem_range.mp (Finset.mem_product.mp h2').1
    have hs_eq : s₁ = s₂ := by
      by_contra hne
      have hdiff : ((s₂ : ℤ) - (s₁ : ℤ)) ≠ 0 := by omega
      have h1_abs : (m : ℤ) ≤ |((s₂ : ℤ) - (s₁ : ℤ)) * m| := by
        rw [abs_mul, abs_of_pos hm]
        exact le_mul_of_one_le_left hm.le (Int.one_le_abs hdiff)
      have h2_abs : ((s₂ : ℤ) - (s₁ : ℤ)) * m = (r₁ : ℤ) - (r₂ : ℤ) := by linarith
      rw [h2_abs] at h1_abs
      have hR0_m : (R0 : ℤ) < m := by
        rw [← Int.natAbs_of_nonneg hm.le]
        exact_mod_cast hR0_lt_m
      have : |(r₁ : ℤ) - (r₂ : ℤ)| < (R0 : ℤ) := by rw [abs_lt]; constructor <;> omega
      omega
    subst hs_eq
    have hr_eq : r₁ = r₂ := by
      have : (r₁ : ℤ) = (r₂ : ℤ) := by linarith
      exact_mod_cast this
    exact Prod.ext hr_eq rfl
  have hZ0_card : Z0.card = N0 := by
    rw [Finset.card_image_of_injOn hZ0_inj, Finset.card_product, Finset.card_range, Finset.card_range]
  have hZ0_bd : ∀ a ∈ Z0, ‖(a : ℂ)‖ ≤ ρ := by
    intro a ha
    obtain ⟨rs, hrs, rfl⟩ := Finset.mem_image.mp ha
    have hr : rs.1 < R1 := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_product.mp hrs).1) hR0_le_R1
    have hs : rs.2 < S1 := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_product.mp hrs).2) hS0_le_S1
    rw [show (((rs.1 : ℤ) + (rs.2 : ℤ) * m : ℤ) : ℂ) = (((rs.1 : ℝ) + (rs.2 : ℝ) * m : ℝ) : ℂ) by
      push_cast; rfl, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    dsimp [ρ]; gcongr
  set ε : ℝ := Λ * Real.exp (2 * 10 ^ 12 * B1)
  have hε0 : 0 ≤ ε := by positivity
  have hF_Z0 : ∀ a ∈ Z0, ‖F (a : ℂ)‖ ≤ ε := by
    intro a ha
    obtain ⟨rs, hrs, rfl⟩ := Finset.mem_image.mp ha
    have hr0 : rs.1 < R0 := Finset.mem_range.mp (Finset.mem_product.mp hrs).1
    have hs0 : rs.2 < S0 := Finset.mem_range.mp (Finset.mem_product.mp hrs).2
    have hr1' : rs.1 < R1 := lt_of_lt_of_le hr0 hR0_le_R1
    have hs1' : rs.2 < S1 := lt_of_lt_of_le hs0 hS0_le_S1
    have h0 := hQ_zero rs.1 hr0 rs.2 hs0
    have hd := hFsubQ_le rs.1 hr1' rs.2 hs1'
    dsimp [Q] at hd
    rw [h0, Rat.cast_zero, sub_zero] at hd
    simpa [show (((rs.1 : ℤ) + (rs.2 : ℤ) * m : ℤ) : ℂ) = (((rs.1 : ℝ) + (rs.2 : ℝ) * m : ℝ) : ℂ) by
      push_cast; rfl] using hd
  set w1 : ℂ := (((r1 : ℝ) + (s1 : ℝ) * m : ℝ) : ℂ)
  have hw1_bd : ‖w1‖ ≤ ρ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    dsimp [ρ]; gcongr
  have hextrap := extrapolate_with_approx_zeros Z0 F hFd (by linarith) hρ_lt_W hW_ge1 hε0
    hZ0_bd hF_Z0 hMW hw1_bd
  have hsupp_base : (2 * ρ) / (W - ρ) ≤ Real.exp (-(M ^ z)) := by
    have hWρ_pos : 0 < W - ρ := by linarith
    rw [div_le_iff₀ hWρ_pos, Real.exp_neg]
    have h2e : 2 * Real.exp (M ^ z) + 1 ≤ α := by
      have hexp1 : 1 ≤ Real.exp (M ^ z) := Real.one_le_exp (by positivity)
      calc 2 * Real.exp (M ^ z) + 1 ≤ 2 * Real.exp (M ^ z) + Real.exp (M ^ z) := by linarith
        _ = 3 * Real.exp (M ^ z) := by ring
        _ ≤ M * Real.exp (M ^ z) := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    calc 2 * ρ = (2 * Real.exp (M ^ z)) * (Real.exp (M ^ z))⁻¹ * ρ := by
          field_simp [(Real.exp_pos (M ^ z)).ne']
      _ ≤ (α - 1) * (Real.exp (M ^ z))⁻¹ * ρ := by gcongr; linarith
      _ = (Real.exp (M ^ z))⁻¹ * (W - ρ) := by dsimp [W]; ring
  have hsupp : ((2 * ρ) / (W - ρ)) ^ Z0.card ≤ Real.exp (-9.98 * 10 ^ 12 * B1) := by
    have hpos_base : 0 ≤ (2 * ρ) / (W - ρ) := div_nonneg (by linarith) (by linarith)
    calc ((2 * ρ) / (W - ρ)) ^ Z0.card
        ≤ (Real.exp (-(M ^ z))) ^ Z0.card := pow_le_pow_left₀ hpos_base hsupp_base _
      _ = Real.exp ((Z0.card : ℝ) * (-(M ^ z))) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-9.98 * 10 ^ 12 * B1) := by
          refine Real.exp_le_exp.mpr ?_
          rw [hZ0_card]
          calc (N0 : ℝ) * (-(M ^ z)) = -((N0 : ℝ) * M ^ z) := by ring
            _ ≤ -((9.98 * 10 ^ 12 * L * M ^ (3 - 4 * z)) * M ^ z) := by gcongr
            _ = -9.98 * 10 ^ 12 * (L * (M ^ (3 - 4 * z) * M ^ z)) := by ring
            _ = -9.98 * 10 ^ 12 * B1 := by rw [hM_prod_34_z]
  have hsupp_le1 : ((2 * ρ) / (W - ρ)) ^ Z0.card ≤ 1 :=
    hsupp.trans (Real.exp_le_one_iff.mpr (by linarith))
  have h4_le_exp2 : (4 : ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_one_gt_two
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h.le 2
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hQ_quarter : Real.exp (-5 * 10 ^ 11 * B1) ≤ (1 / 4 : ℝ) * |(Q r1 s1 : ℝ)| := by
    have hexp_4 : Real.exp (-5 * 10 ^ 11 * B1) ≤ (1 / 4 : ℝ) * Real.exp (-4.7 * 10 ^ 11 * B1) := by
      calc Real.exp (-5 * 10 ^ 11 * B1)
          ≤ Real.exp (-4.7 * 10 ^ 11 * B1 - 2) := Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp (-4.7 * 10 ^ 11 * B1) * (Real.exp 2)⁻¹ := by
            rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg]
        _ ≤ Real.exp (-4.7 * 10 ^ 11 * B1) * (4 : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by norm_num) h4_le_exp2) (Real.exp_pos _).le
        _ = (1 / 4 : ℝ) * Real.exp (-4.7 * 10 ^ 11 * B1) := by ring
    exact hexp_4.trans (mul_le_mul_of_nonneg_left hQ_low (by norm_num))
  have hterm1 : ((2 * ρ) / (W - ρ)) ^ Z0.card * Real.exp (1.7 * 10 ^ 12 * B1) <
      (1 / 4 : ℝ) * |(Q r1 s1 : ℝ)| := by
    have h1 : ((2 * ρ) / (W - ρ)) ^ Z0.card * Real.exp (1.7 * 10 ^ 12 * B1) ≤
        Real.exp (-9.98 * 10 ^ 12 * B1) * Real.exp (1.7 * 10 ^ 12 * B1) :=
      mul_le_mul_of_nonneg_right hsupp (Real.exp_pos _).le
    rw [← Real.exp_add] at h1
    have h2 : Real.exp (-9.98 * 10 ^ 12 * B1 + 1.7 * 10 ^ 12 * B1) < Real.exp (-5 * 10 ^ 11 * B1) :=
      Real.exp_lt_exp.mpr (by linarith)
    exact (h1.trans_lt h2).trans_le hQ_quarter
  have hN0W : (Z0.card : ℝ) * (2 * W) ^ Z0.card ≤ Real.exp (2.2 * 10 ^ 14 * B2) := by
    rw [hZ0_card]
    have hN0_exp : (N0 : ℝ) ≤ Real.exp (0.1 * 10 ^ 14 * B2) := by
      have hM34_44 : M ^ (3 - 4 * z) ≤ M ^ (4 - 4 * z) :=
        Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      have h1 : (N0 : ℝ) ≤ 0.1 * 10 ^ 14 * B2 := by
        calc (N0 : ℝ) ≤ 10 ^ 13 * L * M ^ (3 - 4 * z) := hN0_hi
          _ ≤ 10 ^ 13 * L * M ^ (4 - 4 * z) :=
              mul_le_mul_of_nonneg_left hM34_44 (by positivity)
          _ = 0.1 * 10 ^ 14 * B2 := by dsimp [B2]; ring
      linarith [Real.add_one_le_exp (0.1 * 10 ^ 14 * B2)]
    have h2W_pow : (2 * W) ^ N0 ≤ Real.exp (2.1 * 10 ^ 14 * B2) := by
      calc (2 * W) ^ N0 ≤ (Real.exp (21 * M)) ^ N0 := pow_le_pow_left₀ (by linarith) h2W_exp N0
        _ = Real.exp ((N0 : ℝ) * (21 * M)) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (2.1 * 10 ^ 14 * B2) := by
            refine Real.exp_le_exp.mpr ?_
            calc (N0 : ℝ) * (21 * M) ≤ (10 ^ 13 * L * M ^ (3 - 4 * z)) * (21 * M) :=
                  mul_le_mul_of_nonneg_right hN0_hi (by positivity)
              _ = 2.1 * 10 ^ 14 * (L * (M ^ (3 - 4 * z) * M)) := by ring
              _ = 2.1 * 10 ^ 14 * B2 := by rw [hM_prod_34_1]
    calc (N0 : ℝ) * (2 * W) ^ N0
        ≤ Real.exp (0.1 * 10 ^ 14 * B2) * Real.exp (2.1 * 10 ^ 14 * B2) :=
          mul_le_mul hN0_exp h2W_pow (by positivity) (by positivity)
      _ = Real.exp (2.2 * 10 ^ 14 * B2) := by rw [← Real.exp_add]; ring_nf
  have hΛ_lt : Λ < Real.exp (-D * B2) := by
    rw [show -D * B2 = -D * L * M ^ (4 - 4 * z) by dsimp [B2]; ring]
    exact hcontra
  have hterm2 : 2 * ((Z0.card : ℝ) * ε * (2 * W) ^ Z0.card) < (1 / 4 : ℝ) * |(Q r1 s1 : ℝ)| := by
    have h2le : (2 : ℝ) ≤ Real.exp (1 * B2) := by
      have : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
      have hB2 : 1 ≤ B2 := hB1_ge.trans hB1_le_B2
      exact this.trans (Real.exp_le_exp.mpr (by linarith))
    have hε_lt : ε < Real.exp ((-D + 2 * 10 ^ 12) * B2) := by
      have hB12 : 2 * 10 ^ 12 * B1 ≤ 2 * 10 ^ 12 * B2 :=
        mul_le_mul_of_nonneg_left hB1_le_B2 (by positivity)
      calc ε = Λ * Real.exp (2 * 10 ^ 12 * B1) := rfl
        _ < Real.exp (-D * B2) * Real.exp (2 * 10 ^ 12 * B1) :=
            mul_lt_mul_of_pos_right hΛ_lt (Real.exp_pos _)
        _ ≤ Real.exp (-D * B2) * Real.exp (2 * 10 ^ 12 * B2) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hB12) (Real.exp_pos _).le
        _ = Real.exp ((-D + 2 * 10 ^ 12) * B2) := by rw [← Real.exp_add]; ring_nf
    have hZ0W0 : 0 ≤ (Z0.card : ℝ) * (2 * W) ^ Z0.card :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
    have hlt_exp : 2 * ((Z0.card : ℝ) * ε * (2 * W) ^ Z0.card) < Real.exp (-5 * 10 ^ 11 * B1) := by
      calc 2 * ((Z0.card : ℝ) * ε * (2 * W) ^ Z0.card)
          = 2 * ((Z0.card : ℝ) * (2 * W) ^ Z0.card) * ε := by ring
        _ ≤ Real.exp (1 * B2) * Real.exp (2.2 * 10 ^ 14 * B2) * ε :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul h2le hN0W hZ0W0 (Real.exp_pos _).le) hε0
        _ < Real.exp (1 * B2) * Real.exp (2.2 * 10 ^ 14 * B2) * Real.exp ((-D + 2 * 10 ^ 12) * B2) :=
            mul_lt_mul_of_pos_left hε_lt (mul_pos (Real.exp_pos _) (Real.exp_pos _))
        _ = Real.exp ((1 + 2.2 * 10 ^ 14 + (-D + 2 * 10 ^ 12)) * B2) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-5 * 10 ^ 11 * B1) := by
            refine Real.exp_le_exp.mpr ?_
            have h1 : 1 + 2.2 * 10 ^ 14 + (-D + 2 * 10 ^ 12) ≤ -5 * 10 ^ 11 := by linarith
            calc (1 + 2.2 * 10 ^ 14 + (-D + 2 * 10 ^ 12)) * B2
                ≤ (-5 * 10 ^ 11) * B2 := mul_le_mul_of_nonneg_right h1 (by linarith)
              _ ≤ (-5 * 10 ^ 11) * B1 := mul_le_mul_of_nonpos_left hB1_le_B2 (by norm_num)
    exact hlt_exp.trans_le hQ_quarter
  have hterm3 : ‖F w1 - ((Q r1 s1 : ℚ) : ℂ)‖ < (1 / 4 : ℝ) * |(Q r1 s1 : ℝ)| := by
    have hd := hFsubQ_le r1 hr1 s1 hs1
    have h1 : Λ * Real.exp (2 * 10 ^ 12 * B1) < Real.exp (-5 * 10 ^ 11 * B1) := by
      calc Λ * Real.exp (2 * 10 ^ 12 * B1)
          < Real.exp (-D * B2) * Real.exp (2 * 10 ^ 12 * B1) :=
            mul_lt_mul_of_pos_right hΛ_lt (Real.exp_pos _)
        _ ≤ Real.exp (-D * B1) * Real.exp (2 * 10 ^ 12 * B1) := by
            refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
            exact mul_le_mul_of_nonpos_left hB1_le_B2 (by linarith)
        _ = Real.exp ((-D + 2 * 10 ^ 12) * B1) := by rw [← Real.exp_add]; ring_nf
        _ < Real.exp (-5 * 10 ^ 11 * B1) :=
            Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right (by linarith) (by linarith))
    exact (hd.trans_lt h1).trans_le hQ_quarter
  have hF_bd : ‖F w1‖ < (1 / 2 : ℝ) * |(Q r1 s1 : ℝ)| := by
    have hE0 : 0 ≤ (Z0.card : ℝ) * ε * (2 * W) ^ Z0.card :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hε0) (pow_nonneg (by linarith) _)
    calc ‖F w1‖ ≤ ((2 * ρ) / (W - ρ)) ^ Z0.card *
            (Real.exp (1.7 * 10 ^ 12 * B1) + (Z0.card : ℝ) * ε * (2 * W) ^ Z0.card) +
            (Z0.card : ℝ) * ε * (2 * W) ^ Z0.card := hextrap
      _ ≤ ((2 * ρ) / (W - ρ)) ^ Z0.card * Real.exp (1.7 * 10 ^ 12 * B1) +
            1 * ((Z0.card : ℝ) * ε * (2 * W) ^ Z0.card) +
            (Z0.card : ℝ) * ε * (2 * W) ^ Z0.card := by
          rw [mul_add]
          exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hsupp_le1 hE0)) le_rfl
      _ = ((2 * ρ) / (W - ρ)) ^ Z0.card * Real.exp (1.7 * 10 ^ 12 * B1) +
            2 * ((Z0.card : ℝ) * ε * (2 * W) ^ Z0.card) := by ring
      _ < (1 / 4 : ℝ) * |(Q r1 s1 : ℝ)| + (1 / 4 : ℝ) * |(Q r1 s1 : ℝ)| := add_lt_add hterm1 hterm2
      _ = (1 / 2 : ℝ) * |(Q r1 s1 : ℝ)| := by ring
  have hQ_norm : |(Q r1 s1 : ℝ)| = ‖((Q r1 s1 : ℚ) : ℂ)‖ := by
    rw [show ((Q r1 s1 : ℚ) : ℂ) = (((Q r1 s1 : ℝ) : ℂ)) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
  have htri : |(Q r1 s1 : ℝ)| ≤ ‖F w1‖ + ‖F w1 - ((Q r1 s1 : ℚ) : ℂ)‖ := by
    rw [hQ_norm]
    calc ‖((Q r1 s1 : ℚ) : ℂ)‖ = ‖F w1 - (F w1 - ((Q r1 s1 : ℚ) : ℂ))‖ := by ring_nf
      _ ≤ ‖F w1‖ + ‖F w1 - ((Q r1 s1 : ℚ) : ℂ)‖ := norm_sub_le _ _
  linarith [abs_nonneg (Q r1 s1 : ℝ)]

set_option maxHeartbeats 800000 in
lemma case_two_large_m {D S z : ℝ} {u v : ℚ} {m : ℤ}
    (hM100 : 100 ≤ Real.log (Real.log S)) (hSpos : 0 < S) (hLpos_in : 0 < Real.log S)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hD : 10 ^ 15 ≤ D) (hu : 1 < u) (hv : 1 < v) (hm : 0 < m)
    (hHu : ((u.num.natAbs + u.den : ℕ) : ℝ) ≤ (Real.log S) ^ 16)
    (hHv : ((v.num.natAbs + v.den : ℕ) : ℝ) ≤ S)
    (hmu : |(m : ℝ)| ≤ (Real.log S) ^ 16)
    (hlv : |Real.log (v : ℝ)| ≤ Real.log S / Real.log (Real.log S) *
      Real.exp (-(Real.log (Real.log S)) ^ z))
    (hlog_u : Real.log (u : ℝ) ≤ Real.exp (-(Real.log (Real.log S)) ^ z))
    (hmlog_u : (m : ℝ) * Real.log (u : ℝ) ≤ 2 * (Real.log S / Real.log (Real.log S)) *
      Real.exp (-(Real.log (Real.log S)) ^ z))
    (hind : ∀ a b : ℤ, u ^ a * v ^ b = 1 → a = 0 ∧ b = 0)
    (hm_gt : 10 ^ 7 * Real.log S * (Real.log (Real.log S)) ^ (3 - 4 * z) < (m : ℝ))
    (hpos : 0 < |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)|)
    (hcontra : |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)| <
      Real.exp (-D * Real.log S * (Real.log (Real.log S)) ^ (4 - 4 * z))) :
    False := by
  classical
  set L := Real.log S
  set M := Real.log L
  set Λ := |(m : ℝ) * Real.log (u : ℝ) - Real.log (v : ℝ)|
  have hMpos : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hLpos : 0 < L := hLpos_in
  have hL_eq : L = Real.exp M := (Real.exp_log hLpos).symm
  obtain ⟨hML, hM4L, _, h2L⟩ := exp_M_bounds hM100 hL_eq
  have hS_eq : S = Real.exp L := (Real.exp_log hSpos).symm
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hv0 : 0 < v := lt_trans zero_lt_one hv
  have huR0 : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu0
  have hvR0 : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv0
  have hlu_pos : 0 < Real.log (u : ℝ) := Real.log_pos (by exact_mod_cast hu)
  have hlv_pos : 0 < Real.log (v : ℝ) := Real.log_pos (by exact_mod_cast hv)
  have hm_eqR : (m.natAbs : ℝ) = (m : ℝ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hm.le]
  have hm_leR : (m : ℝ) ≤ L ^ 16 := by
    rwa [abs_of_pos (by exact_mod_cast hm)] at hmu
  -- Power relations for M
  have hM_1z : 1 ≤ M ^ (1 - z) := Real.one_le_rpow hM1 (by linarith)
  have hM_1z_le : M ^ (1 - z) ≤ M := by
    simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM1 (by linarith : 1 - z ≤ 1)
  have hM_22z : 1 ≤ M ^ (2 - 2 * z) := Real.one_le_rpow hM1 (by linarith)
  have hM_22z_le : M ^ (2 - 2 * z) ≤ M ^ 2 := by
    simpa [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hM1 (by linarith : 2 - 2 * z ≤ 2)
  have hM_1z_22z : M ^ (1 - z) ≤ M ^ (2 - 2 * z) :=
    Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have hM_12z_lo : M⁻¹ ≤ M ^ (1 - 2 * z) := by
    rw [← Real.rpow_neg_one M]
    exact Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have hM_12z_hi : M ^ (1 - 2 * z) ≤ M := by
    simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM1 (by linarith : 1 - 2 * z ≤ 1)
  have hM_12z_34z : M ^ (1 - 2 * z) ≤ M ^ (3 - 4 * z) :=
    Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have hM_23z_lo : M⁻¹ ≤ M ^ (2 - 3 * z) := by
    rw [← Real.rpow_neg_one M]
    exact Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have hM_23z_hi : M ^ (2 - 3 * z) ≤ M ^ 2 := by
    simpa [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hM1 (by linarith : 2 - 3 * z ≤ 2)
  have hM_z_lo : 1 ≤ M ^ z := Real.one_le_rpow hM1 hz0
  have hM_z_hi : M ^ z ≤ M := by
    simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM1 hz1
  have hM_33z_lo : 1 ≤ M ^ (3 - 3 * z) := Real.one_le_rpow hM1 (by linarith)
  have hM_33z_44z : M ^ (3 - 3 * z) ≤ M ^ (4 - 4 * z) :=
    Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have hM_23z_56z : M ^ (2 - 3 * z) ≤ M ^ (5 - 6 * z) :=
    Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have hM_prod_23_1 : M ^ (2 - 3 * z) * M ^ (1 - z) = M ^ (3 - 4 * z) := by
    rw [← Real.rpow_add hMpos]; ring_nf
  have hM_prod_12_22 : M ^ (1 - 2 * z) * M ^ (2 - 2 * z) = M ^ (3 - 4 * z) := by
    rw [← Real.rpow_add hMpos]; ring_nf
  have hM_prod_1_22 : M ^ (1 - z) * M ^ (2 - 2 * z) = M ^ (3 - 3 * z) := by
    rw [← Real.rpow_add hMpos]; ring_nf
  have hM_prod_34_z : M ^ (3 - 4 * z) * M ^ z = M ^ (3 - 3 * z) := by
    rw [← Real.rpow_add hMpos]; ring_nf
  have hM_prod_34_1 : M ^ (3 - 4 * z) * M = M ^ (4 - 4 * z) := by
    conv_rhs => rw [show (4 - 4 * z : ℝ) = (3 - 4 * z) + 1 by ring, Real.rpow_add hMpos, Real.rpow_one]
  have hM_prod_23_1_33 : M ^ (2 - 3 * z) * M = M ^ (3 - 3 * z) := by
    conv_rhs => rw [show (3 - 3 * z : ℝ) = (2 - 3 * z) + 1 by ring, Real.rpow_add hMpos, Real.rpow_one]
  have hM_prod_12_1_1 : M ^ (1 - 2 * z) * M ^ (1 - z) * M = M ^ (3 - 3 * z) := by
    rw [← Real.rpow_add hMpos,
      show M ^ (1 - 2 * z + (1 - z)) * M = M ^ (1 - 2 * z + (1 - z)) * M ^ (1 : ℝ) by
        rw [Real.rpow_one],
      ← Real.rpow_add hMpos]
    ring_nf
  set B1 : ℝ := L * M ^ (3 - 3 * z)
  set B2 : ℝ := L * M ^ (4 - 4 * z)
  have hB1_ge : 1 ≤ B1 := one_le_mul_of_one_le_of_one_le (by linarith) hM_33z_lo
  have hB1_le_B2 : B1 ≤ B2 := mul_le_mul_of_nonneg_left hM_33z_44z hLpos.le
  -- Parameter definitions
  let J : ℕ := Nat.ceil (1000 * M ^ (1 - z))
  let I : ℕ := Nat.ceil (3 * 10 ^ 10 * L * M ^ (2 - 3 * z))
  let R0 : ℕ := Nat.floor (10 ^ 6 * L * M ^ (1 - 2 * z))
  let S0 : ℕ := Nat.floor (10 ^ 7 * M ^ (2 - 2 * z))
  let R1 : ℕ := 16 * R0
  let S1 : ℕ := 20 * S0
  let N0 : ℕ := R0 * S0
  have hJ_lo : 1000 * M ^ (1 - z) ≤ (J : ℝ) := Nat.le_ceil _
  have hJ_hi : (J : ℝ) ≤ 1001 * M ^ (1 - z) := by
    have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ 1000 * M ^ (1 - z))
    linarith
  have hJ1 : 1 ≤ J := by
    have : (1 : ℝ) ≤ (J : ℝ) := by linarith
    exact_mod_cast this
  have hLM23_ge : 1 ≤ L * M ^ (2 - 3 * z) := by
    have h1 : 10 ^ 5 * M ^ 3 ≤ L * M⁻¹ := by
      have : (10 ^ 5 * M ^ 4) * M⁻¹ ≤ L * M⁻¹ := mul_le_mul_of_nonneg_right hM4L (by positivity)
      calc 10 ^ 5 * M ^ 3 = (10 ^ 5 * M ^ 4) * M⁻¹ := by field_simp
        _ ≤ L * M⁻¹ := this
    have h2 : L * M⁻¹ ≤ L * M ^ (2 - 3 * z) := mul_le_mul_of_nonneg_left hM_23z_lo hLpos.le
    have hM3 : 1 ≤ M ^ 3 := one_le_pow₀ hM1
    have h3 : (1 : ℝ) ≤ 10 ^ 5 * M ^ 3 := by linarith
    linarith
  have hI_lo : 3 * 10 ^ 10 * L * M ^ (2 - 3 * z) ≤ (I : ℝ) := Nat.le_ceil _
  have hI_hi : (I : ℝ) ≤ (3 * 10 ^ 10 + 1) * L * M ^ (2 - 3 * z) := by
    have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ 3 * 10 ^ 10 * L * M ^ (2 - 3 * z))
    linarith
  have hI1 : 1 ≤ I := by
    have : (1 : ℝ) ≤ (I : ℝ) := by linarith
    exact_mod_cast this
  have hLM12_ge : 1 ≤ L * M ^ (1 - 2 * z) := by
    have h1 : 10 ^ 5 * M ^ 3 ≤ L * M⁻¹ := by
      have : (10 ^ 5 * M ^ 4) * M⁻¹ ≤ L * M⁻¹ := mul_le_mul_of_nonneg_right hM4L (by positivity)
      calc 10 ^ 5 * M ^ 3 = (10 ^ 5 * M ^ 4) * M⁻¹ := by field_simp
        _ ≤ L * M⁻¹ := this
    have h2 : L * M⁻¹ ≤ L * M ^ (1 - 2 * z) := mul_le_mul_of_nonneg_left hM_12z_lo hLpos.le
    have hM3 : 1 ≤ M ^ 3 := one_le_pow₀ hM1
    have h3 : (1 : ℝ) ≤ 10 ^ 5 * M ^ 3 := by linarith
    linarith
  have hR0_hi : (R0 : ℝ) ≤ 10 ^ 6 * L * M ^ (1 - 2 * z) :=
    Nat.floor_le (by positivity)
  have hR0_lo : 999 * 10 ^ 3 * L * M ^ (1 - 2 * z) ≤ (R0 : ℝ) := by
    have hlt := Nat.lt_floor_add_one (10 ^ 6 * L * M ^ (1 - 2 * z))
    linarith
  have hR0_1 : 1 ≤ R0 := by
    have : (1 : ℝ) ≤ (R0 : ℝ) := by linarith
    exact_mod_cast this
  have hS0_hi : (S0 : ℝ) ≤ 10 ^ 7 * M ^ (2 - 2 * z) :=
    Nat.floor_le (by positivity)
  have hS0_lo : 999 * 10 ^ 4 * M ^ (2 - 2 * z) ≤ (S0 : ℝ) := by
    have hlt := Nat.lt_floor_add_one (10 ^ 7 * M ^ (2 - 2 * z))
    linarith
  have hS0_1 : 1 ≤ S0 := by
    have : (1 : ℝ) ≤ (S0 : ℝ) := by linarith
    exact_mod_cast this
  have hR1_1 : 1 ≤ R1 := by omega
  have hS1_1 : 1 ≤ S1 := by omega
  have hN0_lo : 9.98 * 10 ^ 12 * L * M ^ (3 - 4 * z) ≤ (N0 : ℝ) := by
    have hmul : (999 * 10 ^ 3 * L * M ^ (1 - 2 * z)) * (999 * 10 ^ 4 * M ^ (2 - 2 * z)) ≤
        (R0 : ℝ) * (S0 : ℝ) := mul_le_mul hR0_lo hS0_lo (by positivity) (by positivity)
    have hconst : (9.98 : ℝ) * 10 ^ 12 ≤ 999 * 10 ^ 3 * (999 * 10 ^ 4) := by norm_num
    have hN0_eq : (N0 : ℝ) = (R0 : ℝ) * (S0 : ℝ) := by dsimp [N0]; push_cast; rfl
    rw [hN0_eq]
    calc 9.98 * 10 ^ 12 * L * M ^ (3 - 4 * z)
        = (9.98 * 10 ^ 12) * L * (M ^ (1 - 2 * z) * M ^ (2 - 2 * z)) := by
          rw [hM_prod_12_22]
      _ ≤ (999 * 10 ^ 3 * (999 * 10 ^ 4)) * L * (M ^ (1 - 2 * z) * M ^ (2 - 2 * z)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hLpos.le) (by positivity)
      _ = (999 * 10 ^ 3 * L * M ^ (1 - 2 * z)) * (999 * 10 ^ 4 * M ^ (2 - 2 * z)) := by ring
      _ ≤ (R0 : ℝ) * (S0 : ℝ) := hmul
  have hN0_hi : (N0 : ℝ) ≤ 10 ^ 13 * L * M ^ (3 - 4 * z) := by
    have hN0_eq : (N0 : ℝ) = (R0 : ℝ) * (S0 : ℝ) := by dsimp [N0]; push_cast; rfl
    rw [hN0_eq]
    calc (R0 : ℝ) * (S0 : ℝ)
        ≤ (10 ^ 6 * L * M ^ (1 - 2 * z)) * (10 ^ 7 * M ^ (2 - 2 * z)) :=
          mul_le_mul hR0_hi hS0_hi (Nat.cast_nonneg _) (by positivity)
      _ = 10 ^ 13 * L * M ^ (3 - 4 * z) := by rw [← hM_prod_12_22]; ring
  have h2N0_lt_IJ : 2 * R0 * S0 < I * J := by
    have hIJ_lo : 3 * 10 ^ 13 * L * M ^ (3 - 4 * z) ≤ (I : ℝ) * (J : ℝ) := by
      calc 3 * 10 ^ 13 * L * M ^ (3 - 4 * z)
          = (3 * 10 ^ 10 * L * M ^ (2 - 3 * z)) * (1000 * M ^ (1 - z)) := by
            rw [← hM_prod_23_1]; ring
        _ ≤ (I : ℝ) * (J : ℝ) := mul_le_mul hI_lo hJ_lo (by positivity) (by positivity)
    have hltR : ((2 * R0 * S0 : ℕ) : ℝ) < ((I * J : ℕ) : ℝ) := by
      calc ((2 * R0 * S0 : ℕ) : ℝ) = 2 * (N0 : ℝ) := by dsimp [N0]; push_cast; ring
        _ ≤ 2 * (10 ^ 13 * L * M ^ (3 - 4 * z)) := by linarith
        _ < 3 * 10 ^ 13 * L * M ^ (3 - 4 * z) := by
          have hpos3 : 0 < L * M ^ (3 - 4 * z) := by positivity
          linarith
        _ ≤ ((I * J : ℕ) : ℝ) := by push_cast; exact hIJ_lo
    exact_mod_cast hltR
  have hRS_zero : 64 * I * J ≤ R1 * S1 := by
    have hIJ_hi : (I : ℝ) * (J : ℝ) ≤ (3 * 10 ^ 10 + 1) * 1001 * L * M ^ (3 - 4 * z) := by
      calc (I : ℝ) * (J : ℝ)
          ≤ ((3 * 10 ^ 10 + 1) * L * M ^ (2 - 3 * z)) * (1001 * M ^ (1 - z)) :=
            mul_le_mul hI_hi hJ_hi (Nat.cast_nonneg _) (by positivity)
        _ = (3 * 10 ^ 10 + 1) * 1001 * L * M ^ (3 - 4 * z) := by
            rw [← hM_prod_23_1]; ring
    have hR1S1_lo : (320 : ℝ) * (9.98 * 10 ^ 12 * L * M ^ (3 - 4 * z)) ≤ (R1 : ℝ) * (S1 : ℝ) := by
      have : (R1 : ℝ) * (S1 : ℝ) = 320 * (N0 : ℝ) := by dsimp [R1, S1, N0]; push_cast; ring
      linarith
    have hleR : ((64 * I * J : ℕ) : ℝ) ≤ ((R1 * S1 : ℕ) : ℝ) := by
      push_cast
      have h1 : 64 * ((3 * 10 ^ 10 + 1) * 1001 : ℝ) ≤ 320 * (9.98 * 10 ^ 12) := by norm_num
      have h2 : 64 * ((I : ℝ) * (J : ℝ)) ≤ 64 * ((3 * 10 ^ 10 + 1) * 1001 * L * M ^ (3 - 4 * z)) :=
        mul_le_mul_of_nonneg_left hIJ_hi (by norm_num)
      have h3 : 64 * ((3 * 10 ^ 10 + 1) * 1001 : ℝ) * (L * M ^ (3 - 4 * z)) ≤
          320 * (9.98 * 10 ^ 12) * (L * M ^ (3 - 4 * z)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      linarith
    exact_mod_cast hleR
  have hSJ_zero : 16 * J ≤ S1 := by
    have h1 : ((16 * J : ℕ) : ℝ) ≤ 16 * 1001 * M ^ (2 - 2 * z) := by
      push_cast
      calc 16 * (J : ℝ) ≤ 16 * (1001 * M ^ (1 - z)) := mul_le_mul_of_nonneg_left hJ_hi (by norm_num)
        _ ≤ 16 * (1001 * M ^ (2 - 2 * z)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM_1z_22z (by norm_num)) (by norm_num)
        _ = 16 * 1001 * M ^ (2 - 2 * z) := by ring
    have h2 : 20 * 999 * 10 ^ 4 * M ^ (2 - 2 * z) ≤ ((S1 : ℕ) : ℝ) := by
      dsimp [S1]; push_cast; linarith
    have h3 : (16 * 1001 : ℝ) ≤ 20 * 999 * 10 ^ 4 := by norm_num
    have h4 : ((16 * J : ℕ) : ℝ) ≤ ((S1 : ℕ) : ℝ) := by
      have : 16 * 1001 * M ^ (2 - 2 * z) ≤ 20 * 999 * 10 ^ 4 * M ^ (2 - 2 * z) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      linarith
    exact_mod_cast h4
  have hSm_zero : 4 * I ≤ S1 * m.natAbs := by
    have h1 : ((4 * I : ℕ) : ℝ) ≤ 4 * (3 * 10 ^ 10 + 1) * L * M ^ (5 - 6 * z) := by
      have hle : 4 * (I : ℝ) ≤ 4 * ((3 * 10 ^ 10 + 1) * L * M ^ (2 - 3 * z)) :=
        mul_le_mul_of_nonneg_left hI_hi (by norm_num)
      have hle2 : L * M ^ (2 - 3 * z) ≤ L * M ^ (5 - 6 * z) :=
        mul_le_mul_of_nonneg_left hM_23z_56z hLpos.le
      calc ((4 * I : ℕ) : ℝ) = 4 * (I : ℝ) := by push_cast; rfl
        _ ≤ 4 * ((3 * 10 ^ 10 + 1) * L * M ^ (2 - 3 * z)) := hle
        _ = 4 * (3 * 10 ^ 10 + 1) * (L * M ^ (2 - 3 * z)) := by ring
        _ ≤ 4 * (3 * 10 ^ 10 + 1) * (L * M ^ (5 - 6 * z)) :=
            mul_le_mul_of_nonneg_left hle2 (by positivity)
        _ = 4 * (3 * 10 ^ 10 + 1) * L * M ^ (5 - 6 * z) := by ring
    have h2 : (20 * 999 * 10 ^ 4 * 10 ^ 7) * L * M ^ (5 - 6 * z) ≤ ((S1 * m.natAbs : ℕ) : ℝ) := by
      have hS1_lo : 20 * 999 * 10 ^ 4 * M ^ (2 - 2 * z) ≤ (S1 : ℝ) := by
        dsimp [S1]; push_cast; linarith
      have hm_lo : 10 ^ 7 * L * M ^ (3 - 4 * z) ≤ (m.natAbs : ℝ) := by rw [hm_eqR]; exact hm_gt.le
      have hprod : (20 * 999 * 10 ^ 4 * M ^ (2 - 2 * z)) * (10 ^ 7 * L * M ^ (3 - 4 * z)) ≤
          (S1 : ℝ) * (m.natAbs : ℝ) := mul_le_mul hS1_lo hm_lo (by positivity) (by positivity)
      have hM56 : M ^ (2 - 2 * z) * M ^ (3 - 4 * z) = M ^ (5 - 6 * z) := by
        rw [← Real.rpow_add hMpos]; ring_nf
      push_cast
      calc (20 * 999 * 10 ^ 4 * 10 ^ 7) * L * M ^ (5 - 6 * z)
          = (20 * 999 * 10 ^ 4 * M ^ (2 - 2 * z)) * (10 ^ 7 * L * M ^ (3 - 4 * z)) := by
            rw [← hM56]; ring
        _ ≤ (S1 : ℝ) * (m.natAbs : ℝ) := hprod
    have h3 : 4 * (3 * 10 ^ 10 + 1 : ℝ) ≤ 20 * 999 * 10 ^ 4 * 10 ^ 7 := by norm_num
    have h4 : ((4 * I : ℕ) : ℝ) ≤ ((S1 * m.natAbs : ℕ) : ℝ) := by
      have : 4 * (3 * 10 ^ 10 + 1) * L * M ^ (5 - 6 * z) ≤
          (20 * 999 * 10 ^ 4 * 10 ^ 7) * L * M ^ (5 - 6 * z) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hLpos.le) (by positivity)
      linarith
    exact_mod_cast h4
  have hR0_lt_m : R0 < m.natAbs := by
    have h1 : (R0 : ℝ) ≤ 10 ^ 6 * L * M ^ (3 - 4 * z) := by
      exact hR0_hi.trans (mul_le_mul_of_nonneg_left hM_12z_34z (by positivity))
    have h2 : (R0 : ℝ) < (m.natAbs : ℝ) := by
      rw [hm_eqR]
      have : 10 ^ 6 * L * M ^ (3 - 4 * z) ≤ 10 ^ 7 * L * M ^ (3 - 4 * z) := by
        have : 0 ≤ L * M ^ (3 - 4 * z) := by positivity
        linarith
      exact (h1.trans this).trans_lt hm_gt
    exact_mod_cast h2
  -- Bounds on R1, S1, rho, W
  have hR1_hi : (R1 : ℝ) ≤ 1.6 * 10 ^ 7 * L * M ^ (1 - 2 * z) := by
    dsimp [R1]; push_cast; linarith
  have hS1_hi : (S1 : ℝ) ≤ 2 * 10 ^ 8 * M ^ (2 - 2 * z) := by
    dsimp [S1]; push_cast; linarith
  have hR1_L2 : (R1 : ℝ) ≤ L ^ 2 := by
    have h1 : 1.6 * 10 ^ 7 * M ^ (1 - 2 * z) ≤ 10 ^ 5 * M ^ 4 := by
      have hle : 1.6 * 10 ^ 7 * M ^ (1 - 2 * z) ≤ 1.6 * 10 ^ 7 * M :=
        mul_le_mul_of_nonneg_left hM_12z_hi (by norm_num)
      have hM3 : (10 : ℝ) ^ 3 ≤ M ^ 3 := by
        calc (10 : ℝ) ^ 3 ≤ 100 ^ 3 := by norm_num
          _ ≤ M ^ 3 := pow_le_pow_left₀ (by norm_num) hM100 3
      have hle2 : 1.6 * 10 ^ 7 * M ≤ 10 ^ 5 * M ^ 4 := by
        calc 1.6 * 10 ^ 7 * M ≤ (10 ^ 5 * M ^ 3) * M :=
              mul_le_mul_of_nonneg_right (by linarith) hMpos.le
          _ = 10 ^ 5 * M ^ 4 := by ring
      exact hle.trans hle2
    calc (R1 : ℝ) ≤ 1.6 * 10 ^ 7 * L * M ^ (1 - 2 * z) := hR1_hi
      _ = L * (1.6 * 10 ^ 7 * M ^ (1 - 2 * z)) := by ring
      _ ≤ L * (10 ^ 5 * M ^ 4) := mul_le_mul_of_nonneg_left h1 hLpos.le
      _ ≤ L * L := mul_le_mul_of_nonneg_left hM4L hLpos.le
      _ = L ^ 2 := by ring
  have hS1_L : (S1 : ℝ) ≤ L := by
    have h1 : 2 * 10 ^ 8 * M ^ (2 - 2 * z) ≤ 10 ^ 5 * M ^ 4 := by
      have hle : 2 * 10 ^ 8 * M ^ (2 - 2 * z) ≤ 2 * 10 ^ 8 * M ^ 2 :=
        mul_le_mul_of_nonneg_left hM_22z_le (by norm_num)
      have hM2 : (10 : ℝ) ^ 4 ≤ M ^ 2 := by
        calc (10 : ℝ) ^ 4 = 100 ^ 2 := by norm_num
          _ ≤ M ^ 2 := pow_le_pow_left₀ (by norm_num) hM100 2
      have hle2 : 2 * 10 ^ 8 * M ^ 2 ≤ 10 ^ 5 * M ^ 4 := by
        calc 2 * 10 ^ 8 * M ^ 2 ≤ (10 ^ 5 * M ^ 2) * M ^ 2 :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = 10 ^ 5 * M ^ 4 := by ring
      exact hle.trans hle2
    exact hS1_hi.trans (h1.trans hM4L)
  set ρ : ℝ := (R1 : ℝ) + (S1 : ℝ) * (m : ℝ)
  have hρ_ge : 1 ≤ ρ := by
    have : (1 : ℝ) ≤ (R1 : ℝ) := by exact_mod_cast hR1_1
    have : 0 ≤ (S1 : ℝ) * (m : ℝ) := by positivity
    linarith
  have hρ_le : ρ ≤ L ^ 18 := by
    have hL17 : (R1 : ℝ) ≤ L ^ 17 := by
      calc (R1 : ℝ) ≤ L ^ 2 := hR1_L2
        _ = L ^ 2 * 1 := (mul_one _).symm
        _ ≤ L ^ 2 * L ^ 15 := mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith)) (by positivity)
        _ = L ^ 17 := by ring
    have hS1m : (S1 : ℝ) * (m : ℝ) ≤ L ^ 17 := by
      calc (S1 : ℝ) * (m : ℝ) ≤ L * L ^ 16 := mul_le_mul hS1_L hm_leR (by exact_mod_cast hm.le) hLpos.le
        _ = L ^ 17 := by ring
    calc ρ = (R1 : ℝ) + (S1 : ℝ) * (m : ℝ) := rfl
      _ ≤ L ^ 17 + L ^ 17 := add_le_add hL17 hS1m
      _ = 2 * L ^ 17 := by ring
      _ ≤ L * L ^ 17 := mul_le_mul_of_nonneg_right h2L (by positivity)
      _ = L ^ 18 := by ring
  have hρ_exp : ρ ≤ Real.exp (18 * M) := by
    calc ρ ≤ L ^ 18 := hρ_le
      _ = Real.exp (18 * M) := by rw [hL_eq, ← Real.exp_nat_mul]; ring_nf
  set α : ℝ := M * Real.exp (M ^ z)
  set W : ℝ := α * ρ
  have hα_ge : 100 ≤ α := by
    calc (100 : ℝ) ≤ M := hM100
      _ = M * 1 := (mul_one _).symm
      _ ≤ M * Real.exp (M ^ z) := mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) hMpos.le
  have hρ_lt_W : ρ < W := by
    calc ρ = 1 * ρ := (one_mul _).symm
      _ < α * ρ := mul_lt_mul_of_pos_right (by linarith) (by linarith)
  have hW_ge1 : 1 ≤ W := by linarith
  have hW_exp : W ≤ Real.exp (20 * M) := by
    have hMz_exp : Real.exp (M ^ z) ≤ Real.exp M := Real.exp_le_exp.mpr hM_z_hi
    have hM_exp : M ≤ Real.exp M := by rw [← hL_eq]; linarith
    calc W = M * Real.exp (M ^ z) * ρ := rfl
      _ ≤ Real.exp M * Real.exp M * Real.exp (18 * M) :=
          mul_le_mul (mul_le_mul hM_exp hMz_exp (Real.exp_pos _).le (Real.exp_pos _).le)
            hρ_exp (by positivity) (by positivity)
      _ = Real.exp (20 * M) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h2W_exp : 2 * W ≤ Real.exp (21 * M) := by
    have h2 : (2 : ℝ) ≤ Real.exp M := by linarith [hL_eq]
    calc 2 * W ≤ Real.exp M * Real.exp (20 * M) := mul_le_mul h2 hW_exp (by positivity) (by positivity)
      _ = Real.exp (21 * M) := by rw [← Real.exp_add]; ring_nf
  -- Siegel's Lemma matrix
  set uA := u.num.natAbs
  set uB := u.den
  set vA := v.num.natAbs
  set vB := v.den
  have huA_cast : (uA : ℚ) = u.num := rat_num_natAbs_cast_rat hu0
  have hvA_cast : (vA : ℚ) = v.num := rat_num_natAbs_cast_rat hv0
  have hu_eq : u = (uA : ℚ) / (uB : ℚ) := by rw [huA_cast, Rat.num_div_den]
  have hv_eq : v = (vA : ℚ) / (vB : ℚ) := by rw [hvA_cast, Rat.num_div_den]
  have huA_le : (uA : ℝ) ≤ Real.exp (16 * M) := by
    have h1 : (uA : ℝ) ≤ L ^ 16 := (Nat.cast_le (α := ℝ).mpr (Nat.le_add_right uA uB)).trans hHu
    rwa [hL_eq, ← Real.exp_nat_mul, show (16 : ℕ) * M = 16 * M by ring] at h1
  have huB_le : (uB : ℝ) ≤ Real.exp (16 * M) := by
    have h1 : (uB : ℝ) ≤ L ^ 16 := (Nat.cast_le (α := ℝ).mpr (Nat.le_add_left uB uA)).trans hHu
    rwa [hL_eq, ← Real.exp_nat_mul, show (16 : ℕ) * M = 16 * M by ring] at h1
  have hvA_le : (vA : ℝ) ≤ Real.exp L := by
    have h1 : (vA : ℝ) ≤ S := (Nat.cast_le (α := ℝ).mpr (Nat.le_add_right vA vB)).trans hHv
    rwa [← hS_eq]
  have hvB_le : (vB : ℝ) ≤ Real.exp L := by
    have h1 : (vB : ℝ) ≤ S := (Nat.cast_le (α := ℝ).mpr (Nat.le_add_left vB vA)).trans hHv
    rwa [← hS_eq]
  let A : Matrix (Fin R0 × Fin S0) (Fin I × Fin J) ℤ := fun rs ij =>
    ((rs.1.1 : ℤ) + (rs.2.1 : ℤ) * m) ^ ij.1.1 *
      (uA : ℤ) ^ (ij.2.1 * rs.1.1) * (uB : ℤ) ^ (J * R0 - ij.2.1 * rs.1.1) *
      (vA : ℤ) ^ (ij.2.1 * rs.2.1) * (vB : ℤ) ^ (J * S0 - ij.2.1 * rs.2.1)
  have hcard_lt : Fintype.card (Fin R0 × Fin S0) < Fintype.card (Fin I × Fin J) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    calc R0 * S0 ≤ 2 * (R0 * S0) := Nat.le_mul_of_pos_left _ (by norm_num)
      _ = 2 * R0 * S0 := by ring
      _ < I * J := h2N0_lt_IJ
  have hcard_pos : 0 < Fintype.card (Fin R0 × Fin S0) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos hR0_1 hS0_1
  obtain ⟨t, ht_ne, ht_mul, ht_norm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A hcard_lt hcard_pos
  have hA_norm : ‖A‖ ≤ Real.exp (18 * M * I + 16 * M * J * R0 + L * J * S0) := by
    rw [Matrix.norm_le_iff (Real.exp_pos _).le]
    intro rs ij
    rw [Int.norm_eq_abs]
    have hrs_pos : (0 : ℝ) ≤ (rs.1.1 : ℝ) + (rs.2.1 : ℝ) * m := by positivity
    have hrs_le : (rs.1.1 : ℝ) + (rs.2.1 : ℝ) * m ≤ Real.exp (18 * M) := by
      have hr1 : rs.1.1 < R1 := lt_of_lt_of_le rs.1.2 (by dsimp [R1]; omega)
      have hs1 : rs.2.1 < S1 := lt_of_lt_of_le rs.2.2 (by dsimp [S1]; omega)
      have hle : (rs.1.1 : ℝ) + (rs.2.1 : ℝ) * m ≤ ρ := by
        dsimp [ρ]
        gcongr
      exact hle.trans hρ_exp
    have hpow_i : ((rs.1.1 : ℝ) + (rs.2.1 : ℝ) * m) ^ ij.1.1 ≤ Real.exp (18 * M * I) := by
      calc ((rs.1.1 : ℝ) + (rs.2.1 : ℝ) * m) ^ ij.1.1
          ≤ (Real.exp (18 * M)) ^ ij.1.1 := pow_le_pow_left₀ hrs_pos hrs_le _
        _ = Real.exp ((ij.1.1 : ℝ) * (18 * M)) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp ((I : ℝ) * (18 * M)) := by
            refine Real.exp_le_exp.mpr ?_
            have hij : (ij.1.1 : ℝ) ≤ I := by exact_mod_cast ij.1.2.le
            exact mul_le_mul_of_nonneg_right hij (by positivity)
        _ = Real.exp (18 * M * I) := by ring_nf
    have hjr_le : ij.2.1 * rs.1.1 ≤ J * R0 := Nat.mul_le_mul ij.2.2.le rs.1.2.le
    have hjs_le : ij.2.1 * rs.2.1 ≤ J * S0 := Nat.mul_le_mul ij.2.2.le rs.2.2.le
    have hpow_u : (uA : ℝ) ^ (ij.2.1 * rs.1.1) * (uB : ℝ) ^ (J * R0 - ij.2.1 * rs.1.1) ≤
        Real.exp (16 * M * J * R0) := by
      calc (uA : ℝ) ^ (ij.2.1 * rs.1.1) * (uB : ℝ) ^ (J * R0 - ij.2.1 * rs.1.1)
          ≤ (Real.exp (16 * M)) ^ (ij.2.1 * rs.1.1) *
            (Real.exp (16 * M)) ^ (J * R0 - ij.2.1 * rs.1.1) :=
            mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) huA_le _)
              (pow_le_pow_left₀ (Nat.cast_nonneg _) huB_le _) (by positivity) (by positivity)
        _ = (Real.exp (16 * M)) ^ (ij.2.1 * rs.1.1 + (J * R0 - ij.2.1 * rs.1.1)) := (pow_add _ _ _).symm
        _ = (Real.exp (16 * M)) ^ (J * R0) := by rw [Nat.add_sub_of_le hjr_le]
        _ = Real.exp (16 * M * J * R0) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hpow_v : (vA : ℝ) ^ (ij.2.1 * rs.2.1) * (vB : ℝ) ^ (J * S0 - ij.2.1 * rs.2.1) ≤
        Real.exp (L * J * S0) := by
      calc (vA : ℝ) ^ (ij.2.1 * rs.2.1) * (vB : ℝ) ^ (J * S0 - ij.2.1 * rs.2.1)
          ≤ (Real.exp L) ^ (ij.2.1 * rs.2.1) * (Real.exp L) ^ (J * S0 - ij.2.1 * rs.2.1) :=
            mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hvA_le _)
              (pow_le_pow_left₀ (Nat.cast_nonneg _) hvB_le _) (by positivity) (by positivity)
        _ = (Real.exp L) ^ (ij.2.1 * rs.2.1 + (J * S0 - ij.2.1 * rs.2.1)) := (pow_add _ _ _).symm
        _ = (Real.exp L) ^ (J * S0) := by rw [Nat.add_sub_of_le hjs_le]
        _ = Real.exp (L * J * S0) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hA_nonneg : 0 ≤ A rs ij := by
      dsimp [A]
      positivity
    rw [abs_of_nonneg (by exact_mod_cast hA_nonneg)]
    calc ((A rs ij : ℤ) : ℝ)
        = ((rs.1.1 : ℝ) + (rs.2.1 : ℝ) * m) ^ ij.1.1 *
            ((uA : ℝ) ^ (ij.2.1 * rs.1.1) * (uB : ℝ) ^ (J * R0 - ij.2.1 * rs.1.1)) *
            ((vA : ℝ) ^ (ij.2.1 * rs.2.1) * (vB : ℝ) ^ (J * S0 - ij.2.1 * rs.2.1)) := by
          dsimp [A]; push_cast; ring
      _ ≤ Real.exp (18 * M * I) * Real.exp (16 * M * J * R0) * Real.exp (L * J * S0) :=
          mul_le_mul (mul_le_mul hpow_i hpow_u (by positivity) (by positivity))
            hpow_v (by positivity) (by positivity)
      _ = Real.exp (18 * M * I + 16 * M * J * R0 + L * J * S0) := by
          rw [← Real.exp_add, ← Real.exp_add]
  have hmaxA : max 1 ‖A‖ ≤ Real.exp (18 * M * I + 16 * M * J * R0 + L * J * S0) :=
    max_le (Real.one_le_exp (by positivity)) hA_norm
  have ht_norm_le : ‖t‖ ≤ Real.exp (6.1 * 10 ^ 11 * B1) := by
    have he_le : (Fintype.card (Fin R0 × Fin S0) : ℝ) /
        ((Fintype.card (Fin I × Fin J) : ℝ) - Fintype.card (Fin R0 × Fin S0)) ≤ 1 := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      push_cast
      have h2 : 2 * ((R0 : ℝ) * (S0 : ℝ)) < (I : ℝ) * (J : ℝ) := by
        have := (Nat.cast_lt (α := ℝ)).mpr h2N0_lt_IJ
        push_cast at this
        linarith
      have hRS0_nn : 0 ≤ (R0 : ℝ) * (S0 : ℝ) :=
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hdiff_pos : 0 < (I : ℝ) * (J : ℝ) - (R0 : ℝ) * (S0 : ℝ) := by linarith
      rw [div_le_one hdiff_pos]
      linarith
    have hbase_ge1 : 1 ≤ (Fintype.card (Fin I × Fin J) : ℝ) * max 1 ‖A‖ := by
      have hcard1 : (1 : ℝ) ≤ Fintype.card (Fin I × Fin J) := by
        simp only [Fintype.card_prod, Fintype.card_fin]
        exact_mod_cast Nat.mul_pos hI1 hJ1
      exact one_le_mul_of_one_le_of_one_le hcard1 (le_max_left _ _)
    have hrpow : ((Fintype.card (Fin I × Fin J) : ℝ) * max 1 ‖A‖) ^
        ((Fintype.card (Fin R0 × Fin S0) : ℝ) /
          ((Fintype.card (Fin I × Fin J) : ℝ) - Fintype.card (Fin R0 × Fin S0))) ≤
        (Fintype.card (Fin I × Fin J) : ℝ) * max 1 ‖A‖ := by
      simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase_ge1 he_le
    have hJI : J ≤ I := by
      have hJR : (J : ℝ) ≤ 1001 * M :=
        hJ_hi.trans (mul_le_mul_of_nonneg_left hM_1z_le (by norm_num))
      have hIR : 3 * 10 ^ 10 * 10 ^ 5 * M ^ 3 ≤ (I : ℝ) := by
        have hM23 : 10 ^ 5 * M ^ 3 ≤ L * M ^ (2 - 3 * z) := by
          have h1 : 10 ^ 5 * M ^ 3 ≤ L * M⁻¹ := by
            have := mul_le_mul_of_nonneg_right hM4L (by positivity : 0 ≤ M⁻¹)
            calc 10 ^ 5 * M ^ 3 = (10 ^ 5 * M ^ 4) * M⁻¹ := by field_simp
              _ ≤ L * M⁻¹ := this
          exact h1.trans (mul_le_mul_of_nonneg_left hM_23z_lo hLpos.le)
        calc 3 * 10 ^ 10 * 10 ^ 5 * M ^ 3 = 3 * 10 ^ 10 * (10 ^ 5 * M ^ 3) := by ring
          _ ≤ 3 * 10 ^ 10 * (L * M ^ (2 - 3 * z)) :=
              mul_le_mul_of_nonneg_left hM23 (by positivity)
          _ = 3 * 10 ^ 10 * L * M ^ (2 - 3 * z) := by ring
          _ ≤ (I : ℝ) := hI_lo
      have hJI_R : (J : ℝ) ≤ (I : ℝ) := by
        have hM3 : M ≤ M ^ 3 := by
          calc M = 1 * M := (one_mul _).symm
            _ ≤ M ^ 2 * M := mul_le_mul_of_nonneg_right (one_le_pow₀ hM1) hMpos.le
            _ = M ^ 3 := by ring
        have hM3' : 1001 * M ≤ 1001 * M ^ 3 := mul_le_mul_of_nonneg_left hM3 (by norm_num)
        linarith
      exact_mod_cast hJI_R
    have hIJ_exp : (Fintype.card (Fin I × Fin J) : ℝ) ≤ Real.exp (M * I) := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      have hIexp : (I : ℝ) ≤ Real.exp I := by linarith [Real.add_one_le_exp (I : ℝ)]
      have hJexp : (J : ℝ) ≤ Real.exp J := by linarith [Real.add_one_le_exp (J : ℝ)]
      have hIJ_le : (I : ℝ) + (J : ℝ) ≤ M * (I : ℝ) := by
        have hJI_R : (J : ℝ) ≤ (I : ℝ) := by exact_mod_cast hJI
        calc (I : ℝ) + (J : ℝ) ≤ 2 * (I : ℝ) := by linarith
          _ ≤ M * (I : ℝ) := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      push_cast
      exact (mul_le_mul hIexp hJexp (Nat.cast_nonneg _) (Real.exp_pos _).le).trans
        ((Real.exp_add _ _).symm.le.trans (Real.exp_le_exp.mpr hIJ_le))
    have hexp_sum : M * I + (18 * M * I + 16 * M * J * R0 + L * J * S0) ≤ 6.1 * 10 ^ 11 * B1 := by
      have h19 : 19 * M * (I : ℝ) ≤ 19 * (3 * 10 ^ 10 + 1) * B1 := by
        calc 19 * M * (I : ℝ) ≤ 19 * M * ((3 * 10 ^ 10 + 1) * L * M ^ (2 - 3 * z)) :=
              mul_le_mul_of_nonneg_left hI_hi (by positivity)
          _ = 19 * (3 * 10 ^ 10 + 1) * (L * (M ^ (2 - 3 * z) * M)) := by ring
          _ = 19 * (3 * 10 ^ 10 + 1) * B1 := by rw [hM_prod_23_1_33]
      have h16 : 16 * M * (J : ℝ) * (R0 : ℝ) ≤ 16 * 1001 * 10 ^ 6 * B1 := by
        calc 16 * M * (J : ℝ) * (R0 : ℝ)
            ≤ 16 * M * (1001 * M ^ (1 - z)) * (10 ^ 6 * L * M ^ (1 - 2 * z)) := by
              exact mul_le_mul (mul_le_mul_of_nonneg_left hJ_hi (by positivity)) hR0_hi
                (Nat.cast_nonneg _) (by positivity)
          _ = 16 * 1001 * 10 ^ 6 * (L * (M ^ (1 - 2 * z) * M ^ (1 - z) * M)) := by ring
          _ = 16 * 1001 * 10 ^ 6 * B1 := by rw [hM_prod_12_1_1]
      have hJS0 : L * (J : ℝ) * (S0 : ℝ) ≤ 1001 * 10 ^ 7 * B1 := by
        calc L * (J : ℝ) * (S0 : ℝ)
            ≤ L * (1001 * M ^ (1 - z)) * (10 ^ 7 * M ^ (2 - 2 * z)) := by
              exact mul_le_mul (mul_le_mul_of_nonneg_left hJ_hi hLpos.le) hS0_hi
                (Nat.cast_nonneg _) (by positivity)
          _ = 1001 * 10 ^ 7 * (L * (M ^ (1 - z) * M ^ (2 - 2 * z))) := by ring
          _ = 1001 * 10 ^ 7 * B1 := by rw [hM_prod_1_22]
      have hc : 19 * (3 * 10 ^ 10 + 1 : ℝ) + 16 * 1001 * 10 ^ 6 + 1001 * 10 ^ 7 ≤ 6.1 * 10 ^ 11 := by
        norm_num
      have hB0 : 0 ≤ B1 := by linarith
      linarith [mul_le_mul_of_nonneg_right hc hB0]
    calc ‖t‖ ≤ ((Fintype.card (Fin I × Fin J) : ℝ) * max 1 ‖A‖) ^
            ((Fintype.card (Fin R0 × Fin S0) : ℝ) /
              ((Fintype.card (Fin I × Fin J) : ℝ) - Fintype.card (Fin R0 × Fin S0))) := ht_norm
      _ ≤ (Fintype.card (Fin I × Fin J) : ℝ) * max 1 ‖A‖ := hrpow
      _ ≤ Real.exp (M * I) * Real.exp (18 * M * I + 16 * M * J * R0 + L * J * S0) :=
          mul_le_mul hIJ_exp hmaxA (by positivity) (by positivity)
      _ = Real.exp (M * I + (18 * M * I + 16 * M * J * R0 + L * J * S0)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (6.1 * 10 ^ 11 * B1) := Real.exp_le_exp.mpr hexp_sum
  -- Define p : ℕ → ℕ → ℤ and Q
  let p : ℕ → ℕ → ℤ := fun i j => if hi : i < I then if hj : j < J then t (⟨i, hi⟩, ⟨j, hj⟩) else 0 else 0
  have hp_ne : ∃ i < I, ∃ j < J, p i j ≠ 0 := by
    obtain ⟨ij, hij⟩ := Function.ne_iff.mp ht_ne
    refine ⟨ij.1.1, ij.1.2, ij.2.1, ij.2.2, ?_⟩
    simpa [p, ij.1.2, ij.2.2] using hij
  have hp_bd : ∀ i < I, ∀ j < J, |(p i j : ℝ)| ≤ Real.exp (6.1 * 10 ^ 11 * B1) := by
    intro i hi j hj
    have h1 : p i j = t (⟨i, hi⟩, ⟨j, hj⟩) := by simp [p, hi, hj]
    rw [h1, ← Int.norm_eq_abs]
    exact (norm_le_pi_norm t (⟨i, hi⟩, ⟨j, hj⟩)).trans ht_norm_le
  let Q : ℕ → ℕ → ℚ := fun r s =>
    ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
      (p i j : ℚ) * ((r : ℚ) + (s : ℚ) * m) ^ i * u ^ (j * r) * v ^ (j * s)
  have hQ_zero : ∀ r < R0, ∀ s < S0, Q r s = 0 := by
    intro r hr s hs
    have huB0 : (uB : ℚ) ≠ 0 := by exact_mod_cast u.den_nz
    have hvB0 : (vB : ℚ) ≠ 0 := by exact_mod_cast v.den_nz
    have hden_ne0 : (uB : ℚ) ^ (J * R0) * (vB : ℚ) ^ (J * S0) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ huB0) (pow_ne_zero _ hvB0)
    have hmul0 : (uB : ℚ) ^ (J * R0) * (vB : ℚ) ^ (J * S0) * Q r s = 0 := by
      have hclear : (uB : ℚ) ^ (J * R0) * (vB : ℚ) ^ (J * S0) * Q r s =
          ((A.mulVec t (⟨r, hr⟩, ⟨s, hs⟩) : ℤ) : ℚ) := by
        rw [Matrix.mulVec_apply_eq_sum]
        dsimp [Q]
        rw [Finset.mul_sum]
        have hsumI : ∑ i ∈ Finset.range I,
            (uB : ℚ) ^ (J * R0) * (vB : ℚ) ^ (J * S0) *
              ∑ j ∈ Finset.range J, (p i j : ℚ) * ((r : ℚ) + (s : ℚ) * m) ^ i * u ^ (j * r) * v ^ (j * s) =
            ∑ i : Fin I, ∑ j : Fin J,
              (uB : ℚ) ^ (J * R0) * (vB : ℚ) ^ (J * S0) *
                ((p i.1 j.1 : ℚ) * ((r : ℚ) + (s : ℚ) * m) ^ i.1 * u ^ (j.1 * r) * v ^ (j.1 * s)) := by
          rw [← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
        rw [hsumI]
        push_cast
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have hp_eq : p i.1 j.1 = t (i, j) := by simp [p, i.2, j.2]
        have hjr : j.1 * r ≤ J * R0 := Nat.mul_le_mul j.2.le hr.le
        have hjs : j.1 * s ≤ J * S0 := Nat.mul_le_mul j.2.le hs.le
        have hpow_u : (uB : ℚ) ^ (J * R0) * u ^ (j.1 * r) =
            (uA : ℚ) ^ (j.1 * r) * (uB : ℚ) ^ (J * R0 - j.1 * r) := by
          rw [hu_eq, div_pow]
          calc (uB : ℚ) ^ (J * R0) * ((uA : ℚ) ^ (j.1 * r) / (uB : ℚ) ^ (j.1 * r))
              = ((uB : ℚ) ^ (j.1 * r) * (uB : ℚ) ^ (J * R0 - j.1 * r)) *
                  ((uA : ℚ) ^ (j.1 * r) / (uB : ℚ) ^ (j.1 * r)) := by
                rw [← pow_add, Nat.add_sub_of_le hjr]
            _ = (uA : ℚ) ^ (j.1 * r) * (uB : ℚ) ^ (J * R0 - j.1 * r) := by
                field_simp [huB0]
        have hpow_v : (vB : ℚ) ^ (J * S0) * v ^ (j.1 * s) =
            (vA : ℚ) ^ (j.1 * s) * (vB : ℚ) ^ (J * S0 - j.1 * s) := by
          rw [hv_eq, div_pow]
          calc (vB : ℚ) ^ (J * S0) * ((vA : ℚ) ^ (j.1 * s) / (vB : ℚ) ^ (j.1 * s))
              = ((vB : ℚ) ^ (j.1 * s) * (vB : ℚ) ^ (J * S0 - j.1 * s)) *
                  ((vA : ℚ) ^ (j.1 * s) / (vB : ℚ) ^ (j.1 * s)) := by
                rw [← pow_add, Nat.add_sub_of_le hjs]
            _ = (vA : ℚ) ^ (j.1 * s) * (vB : ℚ) ^ (J * S0 - j.1 * s) := by
                field_simp [hvB0]
        rw [hp_eq]
        dsimp [A]
        push_cast
        calc (uB : ℚ) ^ (J * R0) * (vB : ℚ) ^ (J * S0) *
              ((t (i, j) : ℚ) * ((r : ℚ) + (s : ℚ) * m) ^ i.1 * u ^ (j.1 * r) * v ^ (j.1 * s))
            = (t (i, j) : ℚ) * ((r : ℚ) + (s : ℚ) * m) ^ i.1 *
                ((uB : ℚ) ^ (J * R0) * u ^ (j.1 * r)) * ((vB : ℚ) ^ (J * S0) * v ^ (j.1 * s)) := by
              ring
          _ = (t (i, j) : ℚ) * ((r : ℚ) + (s : ℚ) * m) ^ i.1 *
                ((uA : ℚ) ^ (j.1 * r) * (uB : ℚ) ^ (J * R0 - j.1 * r)) *
                ((vA : ℚ) ^ (j.1 * s) * (vB : ℚ) ^ (J * S0 - j.1 * s)) := by
              rw [hpow_u, hpow_v]
          _ = (((r : ℚ) + (s : ℚ) * m) ^ i.1 * (uA : ℚ) ^ (j.1 * r) *
                (uB : ℚ) ^ (J * R0 - j.1 * r) * (vA : ℚ) ^ (j.1 * s) *
                (vB : ℚ) ^ (J * S0 - j.1 * s)) * (t (i, j) : ℚ) := by ring
      rw [hclear, ht_mul]
      simp
    exact (mul_eq_zero.mp hmul0).resolve_left hden_ne0
  -- Zero lemma
  have huv_ne : u ^ m ≠ v := by
    intro heq
    have heqR : (u : ℝ) ^ m = (v : ℝ) := by exact_mod_cast heq
    have hlog := congrArg Real.log heqR
    rw [Real.log_zpow] at hlog
    have hΛ0 : Λ = 0 := by
      dsimp [Λ]
      rw [hlog, sub_self, abs_zero]
    linarith
  obtain ⟨r1, hr1, s1, hs1, hQ_ne⟩ :=
    zero_lemma hu0 hv0 hind hm huv_ne hI1 hJ1 hR1_1 hS1_1 hRS_zero hSJ_zero hSm_zero p hp_ne
  -- Liouville lower bound on |Q r1 s1|
  have hQ_low : Real.exp (-4.7 * 10 ^ 11 * B1) ≤ |(Q r1 s1 : ℝ)| := by
    let Qint : ℤ := ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range J,
      p i j * ((r1 : ℤ) + (s1 : ℤ) * m) ^ i * (uA : ℤ) ^ (j * r1) *
        (uB : ℤ) ^ (J * R1 - j * r1) * (vA : ℤ) ^ (j * s1) * (vB : ℤ) ^ (J * S1 - j * s1)
    have hQint_eq : (Qint : ℚ) = (uB : ℚ) ^ (J * R1) * (vB : ℚ) ^ (J * S1) * Q r1 s1 := by
      dsimp [Qint, Q]
      rw [Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_le : j ≤ J := (Finset.mem_range.mp hj).le
      have hjr : j * r1 ≤ J * R1 := Nat.mul_le_mul hj_le hr1.le
      have hjs : j * s1 ≤ J * S1 := Nat.mul_le_mul hj_le hs1.le
      have huB0 : (uB : ℚ) ≠ 0 := by exact_mod_cast u.den_nz
      have hvB0 : (vB : ℚ) ≠ 0 := by exact_mod_cast v.den_nz
      have hpow_u : (uB : ℚ) ^ (J * R1) * u ^ (j * r1) =
          (uA : ℚ) ^ (j * r1) * (uB : ℚ) ^ (J * R1 - j * r1) := by
        rw [hu_eq, div_pow]
        calc (uB : ℚ) ^ (J * R1) * ((uA : ℚ) ^ (j * r1) / (uB : ℚ) ^ (j * r1))
            = ((uB : ℚ) ^ (j * r1) * (uB : ℚ) ^ (J * R1 - j * r1)) *
                ((uA : ℚ) ^ (j * r1) / (uB : ℚ) ^ (j * r1)) := by
              rw [← pow_add, Nat.add_sub_of_le hjr]
          _ = (uA : ℚ) ^ (j * r1) * (uB : ℚ) ^ (J * R1 - j * r1) := by field_simp [huB0]
      have hpow_v : (vB : ℚ) ^ (J * S1) * v ^ (j * s1) =
          (vA : ℚ) ^ (j * s1) * (vB : ℚ) ^ (J * S1 - j * s1) := by
        rw [hv_eq, div_pow]
        calc (vB : ℚ) ^ (J * S1) * ((vA : ℚ) ^ (j * s1) / (vB : ℚ) ^ (j * s1))
            = ((vB : ℚ) ^ (j * s1) * (vB : ℚ) ^ (J * S1 - j * s1)) *
                ((vA : ℚ) ^ (j * s1) / (vB : ℚ) ^ (j * s1)) := by
              rw [← pow_add, Nat.add_sub_of_le hjs]
          _ = (vA : ℚ) ^ (j * s1) * (vB : ℚ) ^ (J * S1 - j * s1) := by field_simp [hvB0]
      calc (p i j : ℚ) * ((r1 : ℚ) + (s1 : ℚ) * m) ^ i * (uA : ℚ) ^ (j * r1) *
            (uB : ℚ) ^ (J * R1 - j * r1) * (vA : ℚ) ^ (j * s1) * (vB : ℚ) ^ (J * S1 - j * s1)
          = (p i j : ℚ) * ((r1 : ℚ) + (s1 : ℚ) * m) ^ i *
              ((uA : ℚ) ^ (j * r1) * (uB : ℚ) ^ (J * R1 - j * r1)) *
              ((vA : ℚ) ^ (j * s1) * (vB : ℚ) ^ (J * S1 - j * s1)) := by ring
        _ = (p i j : ℚ) * ((r1 : ℚ) + (s1 : ℚ) * m) ^ i *
              ((uB : ℚ) ^ (J * R1) * u ^ (j * r1)) * ((vB : ℚ) ^ (J * S1) * v ^ (j * s1)) := by
            rw [← hpow_u, ← hpow_v]
        _ = (uB : ℚ) ^ (J * R1) * (vB : ℚ) ^ (J * S1) *
              ((p i j : ℚ) * ((r1 : ℚ) + (s1 : ℚ) * m) ^ i * u ^ (j * r1) * v ^ (j * s1)) := by
            ring
    have hQint_ne : Qint ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero] at hQint_eq
      have huB0 : (uB : ℚ) ≠ 0 := by exact_mod_cast u.den_nz
      have hvB0 : (vB : ℚ) ≠ 0 := by exact_mod_cast v.den_nz
      have hden0 : (uB : ℚ) ^ (J * R1) * (vB : ℚ) ^ (J * S1) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ huB0) (pow_ne_zero _ hvB0)
      exact hQ_ne ((mul_eq_zero.mp hQint_eq.symm).resolve_left hden0)
    have hQint_ge1 : (1 : ℝ) ≤ |(Qint : ℝ)| := by exact_mod_cast Int.one_le_abs hQint_ne
    have hQint_R : (Qint : ℝ) = (uB : ℝ) ^ (J * R1) * (vB : ℝ) ^ (J * S1) * (Q r1 s1 : ℝ) := by
      have := congrArg (Rat.cast : ℚ → ℝ) hQint_eq
      push_cast at this
      exact this
    have hden_pos : 0 < (uB : ℝ) ^ (J * R1) * (vB : ℝ) ^ (J * S1) := by
      have : (0 : ℝ) < uB := by exact_mod_cast u.pos
      have : (0 : ℝ) < vB := by exact_mod_cast v.pos
      positivity
    have hden_le : (uB : ℝ) ^ (J * R1) * (vB : ℝ) ^ (J * S1) ≤ Real.exp (4.7 * 10 ^ 11 * B1) := by
      have huB_pow : (uB : ℝ) ^ (J * R1) ≤ Real.exp (16 * M * J * R1) := by
        calc (uB : ℝ) ^ (J * R1) ≤ (Real.exp (16 * M)) ^ (J * R1) :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) huB_le _
          _ = Real.exp (16 * M * J * R1) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      have hvB_pow : (vB : ℝ) ^ (J * S1) ≤ Real.exp (L * J * S1) := by
        calc (vB : ℝ) ^ (J * S1) ≤ (Real.exp L) ^ (J * S1) :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) hvB_le _
          _ = Real.exp (L * J * S1) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      have hexp_den : 16 * M * J * R1 + L * J * S1 ≤ 4.7 * 10 ^ 11 * B1 := by
        have h1 : 16 * M * (J : ℝ) * (R1 : ℝ) ≤ 16 * 1001 * (1.6 * 10 ^ 7) * B1 := by
          calc 16 * M * (J : ℝ) * (R1 : ℝ)
              ≤ 16 * M * (1001 * M ^ (1 - z)) * (1.6 * 10 ^ 7 * L * M ^ (1 - 2 * z)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hJ_hi (by positivity)) hR1_hi
                  (Nat.cast_nonneg _) (by positivity)
            _ = 16 * 1001 * (1.6 * 10 ^ 7) * (L * (M ^ (1 - 2 * z) * M ^ (1 - z) * M)) := by ring
            _ = 16 * 1001 * (1.6 * 10 ^ 7) * B1 := by rw [hM_prod_12_1_1]
        have h2 : L * (J : ℝ) * (S1 : ℝ) ≤ 1001 * (2 * 10 ^ 8) * B1 := by
          calc L * (J : ℝ) * (S1 : ℝ)
              ≤ L * (1001 * M ^ (1 - z)) * (2 * 10 ^ 8 * M ^ (2 - 2 * z)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hJ_hi hLpos.le) hS1_hi
                  (Nat.cast_nonneg _) (by positivity)
            _ = 1001 * (2 * 10 ^ 8) * (L * (M ^ (1 - z) * M ^ (2 - 2 * z))) := by ring
            _ = 1001 * (2 * 10 ^ 8) * B1 := by rw [hM_prod_1_22]
        have hc : 16 * 1001 * (1.6 * 10 ^ 7 : ℝ) + 1001 * (2 * 10 ^ 8) ≤ 4.7 * 10 ^ 11 := by norm_num
        linarith [mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ B1)]
      calc (uB : ℝ) ^ (J * R1) * (vB : ℝ) ^ (J * S1)
          ≤ Real.exp (16 * M * J * R1) * Real.exp (L * J * S1) :=
            mul_le_mul huB_pow hvB_pow (by positivity) (by positivity)
        _ = Real.exp (16 * M * J * R1 + L * J * S1) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (4.7 * 10 ^ 11 * B1) := Real.exp_le_exp.mpr hexp_den
    rw [hQint_R, abs_mul, abs_of_pos hden_pos] at hQint_ge1
    calc Real.exp (-4.7 * 10 ^ 11 * B1)
        = (Real.exp (4.7 * 10 ^ 11 * B1))⁻¹ := by
          rw [show -4.7 * 10 ^ 11 * B1 = -(4.7 * 10 ^ 11 * B1) by ring, Real.exp_neg]
      _ ≤ ((uB : ℝ) ^ (J * R1) * (vB : ℝ) ^ (J * S1))⁻¹ := inv_anti₀ hden_pos hden_le
      _ ≤ |(Q r1 s1 : ℝ)| := by
          rw [inv_le_iff_one_le_mul₀' hden_pos]
          exact hQint_ge1
  exact analytic_extrap_contra hM100 hLpos_in hz1 hD hu hv hm hm_leR hlv hlog_u hmlog_u
    hcontra (by dsimp [R1]; omega) (by dsimp [S1]; omega) hr1 hs1 hR1_1 hR0_lt_m hJ_hi hI_hi
    hN0_lo hN0_hi hR1_hi hS1_hi hR1_L2 hS1_L p hp_bd hQ_zero hQ_low

theorem sol : OMA.R_Erdos375_erdos_375_variants_log_R1.H2 := by
  unfold OMA.R_Erdos375_erdos_375_variants_log_R1.H2
  set L0 := Real.exp 100
  set S0 := Real.exp L0
  set B0 := 2 * S0 * (L0 ^ 16) ^ Nat.ceil (L0 ^ 16)
  set D : ℝ := max (10 ^ 15) (Real.log B0 / 3 + 1)
  have hD_pos : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hD_15 : 10 ^ 15 ≤ D := le_max_left _ _
  have hD_B0 : Real.log B0 / 3 + 1 ≤ D := le_max_right _ _
  refine ⟨D, hD_pos, ?_⟩
  intro S hS27 z hz0 hz1 u v m hu hv hHu hHv hml hmu hlv hpos
  have hexp3 : Real.exp 3 < 27 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    calc (Real.exp 1) ^ 3 < 3 ^ 3 :=
          pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
      _ = 27 := by norm_num
  have hL3 : 3 < Real.log S := by
    have h := Real.log_lt_log (Real.exp_pos 3) (hexp3.trans hS27)
    rwa [Real.log_exp] at h
  have hM1 : 1 < Real.log (Real.log S) := by
    have h := Real.log_lt_log (Real.exp_pos 1) (Real.exp_one_lt_three.trans hL3)
    rwa [Real.log_exp] at h
  have hm_ne0 : m ≠ 0 := by
    intro hm0
    rw [hm0, Int.cast_zero, abs_zero] at hml
    have hpos_rhs : 0 < 2 * Real.log S / Real.log (Real.log S) := by positivity
    linarith
  let m1 : ℤ := if 0 < m then m else -m
  let u1 : ℚ := if 0 < m then u else u⁻¹
  have hm1_pos : 0 < m1 := by dsimp [m1]; split_ifs <;> omega
  have hu1_pos : 0 < u1 := by dsimp [u1]; split_ifs; exact hu; exact inv_pos.mpr hu
  have hm1_abs : |(m1 : ℝ)| = |(m : ℝ)| := by
    dsimp [m1]; split_ifs <;> simp [abs_neg]
  have hu1_ht : u1.num.natAbs + u1.den = u.num.natAbs + u.den := by
    dsimp [u1]; split_ifs
    · rfl
    · exact rat_inv_height hu
  have hHu1 : ((u1.num.natAbs + u1.den : ℕ) : ℝ) ≤ (Real.log S) ^ 16 := by
    rw [hu1_ht]; exact hHu
  have hm1_lin : (m1 : ℝ) * Real.log (u1 : ℝ) = (m : ℝ) * Real.log (u : ℝ) := by
    dsimp [m1, u1]; split_ifs
    · rfl
    · push_cast; rw [Real.log_inv]; ring
  rw [← hm1_lin] at hpos ⊢
  rw [← hm1_abs] at hml hmu
  by_cases hS_le : S ≤ S0
  · exact small_S_case hD_B0 hD_pos hS27 hS_le hz0 hz1 hu1_pos hv hm1_pos hHu1 hHv hmu hpos
  · push Not at hS_le
    have hSpos : 0 < S := lt_trans (Real.exp_pos L0) hS_le
    have hL_gt : L0 < Real.log S := by
      have h := Real.log_lt_log (Real.exp_pos L0) hS_le
      rwa [Real.log_exp] at h
    have hLpos : 0 < Real.log S := lt_trans (Real.exp_pos 100) hL_gt
    have hM100 : 100 ≤ Real.log (Real.log S) := by
      have h := Real.log_lt_log (Real.exp_pos 100) hL_gt
      rw [Real.log_exp] at h
      exact h.le
    by_cases hm_small : (m1 : ℝ) ≤ 10 ^ 7 * Real.log S * (Real.log (Real.log S)) ^ (3 - 4 * z)
    · exact case_one_small_m hM100 hSpos hLpos hz0 hz1 hD_15 hu1_pos hv hm1_pos hHu1 hHv hm_small hpos
    · push Not at hm_small
      by_contra hcontra
      push Not at hcontra
      have hcases := wlog_pos_uv hM100 hSpos hLpos hz0 hz1 hD_15 hu1_pos hv hm1_pos hHu1 hHv hpos hcontra
      let u2 : ℚ := if 1 < u1 ∧ 1 < v then u1 else u1⁻¹
      let v2 : ℚ := if 1 < u1 ∧ 1 < v then v else v⁻¹
      have huv2 : 1 < u2 ∧ 1 < v2 := by
        dsimp [u2, v2]
        split_ifs with h
        · exact h
        · exact hcases.resolve_left h
      have hu2_ht : ((u2.num.natAbs + u2.den : ℕ) : ℝ) ≤ (Real.log S) ^ 16 := by
        dsimp [u2]; split_ifs
        · exact hHu1
        · rw [rat_inv_height hu1_pos]; exact hHu1
      have hv2_ht : ((v2.num.natAbs + v2.den : ℕ) : ℝ) ≤ S := by
        dsimp [v2]; split_ifs
        · exact hHv
        · rw [rat_inv_height hv]; exact hHv
      have hlv2 : |Real.log (v2 : ℝ)| ≤ Real.log S / Real.log (Real.log S) *
          Real.exp (-(Real.log (Real.log S)) ^ z) := by
        dsimp [v2]; split_ifs
        · exact hlv
        · simpa [Rat.cast_inv, Real.log_inv, abs_neg] using hlv
      have hform2 : |(m1 : ℝ) * Real.log (u2 : ℝ) - Real.log (v2 : ℝ)| =
          |(m1 : ℝ) * Real.log (u1 : ℝ) - Real.log (v : ℝ)| := by
        dsimp [u2, v2]; split_ifs
        · rfl
        · push_cast; rw [Real.log_inv, Real.log_inv, show (m1 : ℝ) * -Real.log (u1 : ℝ) - -Real.log (v : ℝ) =
            -((m1 : ℝ) * Real.log (u1 : ℝ) - Real.log (v : ℝ)) by ring, abs_neg]
      rw [← hform2] at hpos hcontra
      obtain ⟨hlog_u2, hmlog_u2⟩ := log_u_le_of_pos hM100 hLpos hz0 hz1 hD_15 huv2.1 hm1_pos hml hlv2 hcontra
      have hind2 := mult_indep_of_contra hM100 hLpos hz0 hz1 hD_15 huv2.1 huv2.2 hm1_pos hu2_ht hpos hcontra
      exact case_two_large_m hM100 hSpos hLpos hz0 hz1 hD_15 huv2.1 huv2.2 hm1_pos hu2_ht hv2_ht hmu
        hlv2 hlog_u2 hmlog_u2 hind2 hm_small hpos hcontra

end SiegelAndMain

end OMA.Erdos375LogR1H2

theorem OMA.GrimmAssembly.linearForm : OMA.R_Erdos375_erdos_375_variants_log_R1.H2 := OMA.Erdos375LogR1H2.sol

end

theorem OMA.solution : type_of% @Erdos375.erdos_375.variants.log := by
  exact OMA.R_Erdos375_erdos_375_variants_log_R1.main
    (OMA.R_Erdos375_erdos_375_variants_log_R1_H1_R1.main OMA.GrimmAssembly.extraction
      OMA.GrimmAssembly.smallObstruction OMA.GrimmAssembly.largeObstruction)
    OMA.GrimmAssembly.linearForm OMA.GrimmAssembly.chooseParameter
