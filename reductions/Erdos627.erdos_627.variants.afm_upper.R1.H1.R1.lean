import OMAReductions.R_Erdos627_erdos_627_variants_afm_upper_R1

/-!
The remaining hypothesis is the uniform off-diagonal estimate in
Gupta, Ndiaye, Norin and Wei, "Optimizing the CGMS upper bound on Ramsey numbers",
arXiv:2407.19026v2, Theorem 1 and its displayed corollary. This is precisely
equation (11) of Araujo, Filipe and Miyazaki, arXiv:2512.16062.

Using the classical binomial bound together with the improved bound controls
all aspect ratios at once: the smaller of s and ε t is at most √(ε s t).
The Pascal induction here follows our proof of the classical bound in #1984.
-/

namespace OMA.R_Erdos627_erdos_627_variants_afm_upper_R1_H1_R1

open SimpleGraph Filter Real Combinatorics.Diagonal
open scoped BigOperators

/-- The uniform off-diagonal Ramsey bound with saving (0.14/e)s and error o(t). -/
def H1 : Prop := ∀ ε > (0 : ℝ), ∀ᶠ t : ℕ in atTop, ∀ s : ℕ, 0 < s → s ≤ t →
  (classicalRamsey s t : ℝ) ≤
    Real.exp (-(0.14 / Real.exp 1) * s + ε * t) * ((s+t).choose s : ℝ)

/-- The finite Ramsey bracket for the actual clique and independence numbers of
a graph, with the sharp Pascal bound at shifted indices. -/
def H2 : Prop := ∀ {n : ℕ} (G : SimpleGraph (Fin n)),
  n < classicalRamsey (G.cliqueNum+1) (G.indepNum+1) ∧
  classicalRamsey (G.cliqueNum+1) (G.indepNum+1) ≤
    (G.cliqueNum+G.indepNum).choose G.cliqueNum

theorem entropy_choose {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    Real.log ((s+t).choose s : ℝ) ≤
      ((s:ℝ)+t) * Real.binEntropy ((s:ℝ)/(s+t)) := by
  let x := (s:ℝ)/(s+t)
  let y := (t:ℝ)/(s+t)
  have hpos : 0 < (s:ℝ)+t := by positivity
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hxy : x+y = 1 := by dsimp [x,y]; field_simp
  have hsx : ((s:ℝ)+t)*x = s := by dsimp [x]; field_simp
  have hty : ((s:ℝ)+t)*y = t := by dsimp [y]; field_simp
  have hc : (0:ℝ) < (s+t).choose s := by exact_mod_cast (Nat.choose_pos (show s ≤ s+t by omega))
  have term : x^s*y^t*((s+t).choose s:ℝ) ≤ (x+y)^(s+t) := by
    rw [add_pow]
    have h := Finset.single_le_sum
      (f := fun i : ℕ => x^i * y^(s+t-i) * ((s+t).choose i : ℝ))
      (fun _ _ => by positivity) (Finset.mem_range.mpr (show s < s+t+1 by omega))
    simpa using h
  have hlog := Real.log_le_log (by positivity) term
  rw [hxy, one_pow, Real.log_one, Real.log_mul (by positivity) hc.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  change _ ≤ ((s:ℝ)+t) * Real.binEntropy x
  rw [Real.binEntropy, show 1-x=y by linarith, Real.log_inv, Real.log_inv, mul_add,
    ← mul_assoc, ← mul_assoc, hsx, hty]
  linarith

theorem entropy_crude {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    (a+b)*Real.binEntropy (a/(a+b)) ≤ 4*Real.sqrt (a*b) := by
  let w := Real.sqrt (a*b)
  have hw : 0<w := Real.sqrt_pos.2 (mul_pos ha hb)
  have hw2 : w^2=a*b := Real.sq_sqrt (mul_pos ha hb).le
  have term (u v : ℝ) (hu : 0<u) (hv : 0<v) (huv : w^2=u*v) :
      u*Real.log ((u+v)/u) ≤ 2*w := by
    have hcmp : (u+v)/u ≤ (1+w/u)^2 := by
      field_simp; nlinarith [mul_nonneg hu.le hw.le]
    have hlog := Real.log_le_log (by positivity) hcmp
    rw [Real.log_pow] at hlog
    have hl := Real.log_le_sub_one_of_pos (show 0<1+w/u by positivity)
    calc u * Real.log ((u+v)/u) ≤ u*(2*(w/u)) := by gcongr; linarith
         _ = _ := by field_simp
  have hsum : 0<a+b := by positivity
  have hy : 1-a/(a+b)=b/(a+b) := by field_simp; ring
  rw [Real.binEntropy, hy, inv_div, inv_div, mul_add, ← mul_assoc, ← mul_assoc,
    mul_div_cancel₀ _ hsum.ne', mul_div_cancel₀ _ hsum.ne']
  have h1 := term a b ha hb hw2
  have h2 := term b a hb ha (by rw [mul_comm]; exact hw2)
  rw [add_comm b a] at h2
  linarith

theorem interpolate {L E s t c η : ℝ} (hL : 0≤L) (hs : 0<s) (ht : 0<t)
    (hc : c≤1) (hη : 0<η) (hrough : E≤4*Real.sqrt (s*t))
    (hbin : L≤E) (himproved : L≤E-c*s+η^2*t) :
    L^2 ≤ (E-c*s)^2 + 8*η*(s*t) := by
  let B := Real.sqrt (s*t)
  have hB : 0<B := Real.sqrt_pos.2 (mul_pos hs ht)
  have hBs : B^2=s*t := Real.sq_sqrt (mul_pos hs ht).le
  have hdiff : L-(E-c*s) ≤ η*B := by
    by_cases h : s ≤ η*B
    · nlinarith [mul_nonneg (sub_nonneg.mpr hc) hs.le]
    · have hh : η^2*t ≤ η*B := by
        suffices η*t ≤ B by nlinarith [mul_le_mul_of_nonneg_left this hη.le]
        have hmul := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge h)) ht.le
        apply le_of_mul_le_mul_right (a := B) _ hB
        nlinarith
      linarith
  have hsq := sq_nonneg (L-(E-c*s))
  have h1 := mul_le_mul_of_nonneg_left hdiff hL
  have h2 := mul_le_mul_of_nonneg_right (hbin.trans hrough) (mul_pos hη hB).le
  change L*(η*B) ≤ (4*B)*(η*B) at h2
  rw [← hBs]
  nlinarith

theorem graph_pos {n : ℕ} (hn : 0<n) (G : SimpleGraph (Fin n)) :
    0<G.cliqueNum ∧ 0<G.indepNum := by
  let v : Fin n := ⟨0,hn⟩
  have hc (H : SimpleGraph (Fin n)) : 0<H.cliqueNum := by
    have h : H.IsClique (({v} : Finset (Fin n)) : Set _) := by simp
    have hl := h.card_le_cliqueNum
    simp only [Finset.card_singleton] at hl
    omega
  exact ⟨hc G, by simpa using hc Gᶜ⟩

theorem shift_choose (s t : ℕ) :
    ((s+1)+(t+1)).choose (s+1) ≤ (s+t+2)^2 * (s+t).choose s := by
  let N := s+t
  have h1 : (N+1).choose (s+1) ≤ (N+1)*N.choose s := by
    rw [Nat.add_one_mul_choose_eq]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have h2 : (N+2).choose (s+1) ≤ (N+1).choose (s+1)*(N+2) := by
    rw [Nat.choose_mul_succ_eq]
    exact Nat.le_mul_of_pos_right _ (by dsimp [N]; omega)
  rw [show s+1+(t+1) = N+2 by dsimp [N]; omega]
  calc (N+2).choose (s+1) ≤ _ := h2
       _ ≤ ((N+1)*N.choose s)*(N+2) := by gcongr
       _ ≤ ((N+2)*N.choose s)*(N+2) := by gcongr; omega
       _ = _ := by dsimp [N]; ring

theorem shift_saving {c : ℝ} (hc : 0≤c)
    (raw : ∀ ε> (0:ℝ), ∀ᶠ t:ℕ in atTop, ∀ s:ℕ, 0<s → s≤t → 0 < classicalRamsey s t →
      Real.log (classicalRamsey s t) ≤ Real.log ((s+t).choose s : ℝ)-c*s+ε*t)
    (ε : ℝ) (hε : 0<ε) : ∀ᶠ t:ℕ in atTop, ∀ s:ℕ, s≤t → 0 < classicalRamsey (s+1) (t+1) →
      Real.log (classicalRamsey (s+1) (t+1)) ≤ Real.log ((s+t).choose s : ℝ)-c*s+ε*t := by
  obtain ⟨T,hT⟩ := eventually_atTop.1 (raw (ε/4) (by positivity))
  have hlog := Real.isLittleO_log_id_atTop.natCast_atTop.bound (show 0<ε/8 by positivity)
  obtain ⟨K,hK⟩ := exists_nat_ge (8*Real.log 4/ε)
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop K, eventually_ge_atTop 1, hlog]
    with t htT htK ht1 htlog
  intro s hst hRpos
  have ht : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have htone : (1:ℝ)≤t := by exact_mod_cast ht1
  have hlogt : Real.log t ≤ (ε/8)*t := by
    simpa [Real.norm_eq_abs, abs_of_nonneg ht.le, abs_of_nonneg (Real.log_nonneg htone)] using htlog
  have hC : 8*Real.log 4 ≤ (t:ℝ)*ε := by
    apply (div_le_iff₀ hε).mp
    exact hK.trans (by exact_mod_cast htK)
  have hraw := hT (t+1) (by omega) (s+1) (by omega) (by omega) hRpos
  have hshift : ((((s+1)+(t+1)).choose (s+1)):ℝ) ≤
      ((4:ℝ)*t)^2 * ((s+t).choose s:ℝ) := by
    have h : (((s+1)+(t+1)).choose (s+1):ℝ) ≤
        ((s:ℝ)+t+2)^2*((s+t).choose s : ℝ) := by exact_mod_cast shift_choose s t
    refine h.trans ?_
    gcongr
    have : (s:ℝ) ≤ t := by exact_mod_cast hst
    linarith
  have hbin : (0:ℝ) < (s+t).choose s := by exact_mod_cast (Nat.choose_pos (show s ≤ s+t by omega))
  have hbin' : (0:ℝ) < ((s+1)+(t+1)).choose (s+1) := by
    exact_mod_cast (Nat.choose_pos (show s+1 ≤ s+1+(t+1) by omega))
  have hlogs := Real.log_le_log hbin' hshift
  rw [Real.log_mul (by positivity) hbin.ne', Real.log_pow,
    Real.log_mul (by norm_num) ht.ne'] at hlogs
  norm_num at hlogs
  push_cast at hraw
  nlinarith [mul_nonneg hε.le (sub_nonneg.mpr htone)]

theorem scale_square {s t c L δ : ℝ} (hs : 0<s) (ht : 0<t)
    (bound : L^2 ≤ ((s+t)*Real.binEntropy (s/(s+t))-c*s)^2 +
      8*(δ*(Real.log 2)^2/8)*(s*t)) :
    (L/Real.log 2)^2 ≤
      (((Real.binEntropy (s/(s+t))-c*(s/(s+t))) /
       (Real.log 2 * Real.sqrt ((s/(s+t))*(1-s/(s+t)))))^2+δ)*(s*t) := by
  have hS : 0<s+t := by positivity
  have hB : 0<Real.sqrt (s*t) := Real.sqrt_pos.2 (mul_pos hs ht)
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : Real.sqrt ((s/(s+t))*(1-s/(s+t))) = Real.sqrt (s*t)/(s+t) := by
    rw [show s/(s+t)*(1-s/(s+t))=s*t/(s+t)^2 by field_simp; ring,
      Real.sqrt_div (mul_pos hs ht).le, Real.sqrt_sq hS.le]
  rw [hsqrt]
  calc (L/Real.log 2)^2 = L^2/(Real.log 2)^2 := div_pow _ _ _
       _ ≤ (((s+t)*Real.binEntropy (s/(s+t))-c*s)^2 +
           8*(δ*(Real.log 2)^2/8)*(s*t))/(Real.log 2)^2 := by gcongr
       _ = _ := by
         conv_rhs => arg 2; rw [← Real.sq_sqrt (mul_pos hs ht).le]
         field_simp
         rw [Real.sq_sqrt (mul_pos hs ht).le]
         ring

theorem transfer (graph_bounds : H2) (raw : ∀ ε> (0:ℝ), ∀ᶠ t:ℕ in atTop, ∀ s:ℕ, 0<s → s≤t → 0 < classicalRamsey s t →
      Real.log (classicalRamsey s t) ≤ Real.log ((s+t).choose s : ℝ)-(0.14/Real.exp 1)*s+ε*t) :
    ∀ δ>(0:ℝ), ∀ᶠ k:ℕ in atTop, ∀ H : SimpleGraph (Fin k),
    let a : ℝ := H.cliqueNum
    let b : ℝ := H.indepNum
    let x := min a b / (a+b)
    (Real.logb 2 k)^2 ≤ (((Real.binEntropy x - (0.14/Real.exp 1)*x) /
      (Real.log 2 * Real.sqrt (x*(1-x))))^2+δ)*(a*b) := by
  intro δ hδ
  let c : ℝ := 0.14/Real.exp 1
  let η : ℝ := δ*(Real.log 2)^2/8
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hη : 0<η := by dsimp [η]; positivity
  have hc : 0≤c := by dsimp [c]; positivity
  have hc' : c≤1 := by
    dsimp [c]
    apply (div_le_iff₀ (Real.exp_pos 1)).mpr
    linarith [Real.add_one_le_exp 1]
  obtain ⟨T,hT⟩ := eventually_atTop.1 (shift_saving hc raw (η^2) (by positivity))
  filter_upwards [eventually_ge_atTop (2^(T+T)), eventually_ge_atTop 1] with k hk hk1
  intro H
  dsimp only
  have sorted (G : SimpleGraph (Fin k)) (hst : G.cliqueNum ≤ G.indepNum) :
      let a : ℝ := G.cliqueNum
      let b : ℝ := G.indepNum
      let x := a/(a+b)
      (Real.logb 2 k)^2 ≤ (((Real.binEntropy x-c*x)/
        (Real.log 2*Real.sqrt (x*(1-x))))^2+δ)*(a*b) := by
    let s := G.cliqueNum
    let t := G.indepNum
    obtain ⟨hR, hbin⟩ := graph_bounds G
    have hkn : k < (s+t).choose s := lt_of_lt_of_le hR hbin
    have hlarge : T≤t := by
      by_contra! ht
      have h1 := Nat.choose_le_two_pow (s+t) s
      have h2 : 2^(s+t) ≤ (2:ℕ)^(T+T) := by
        apply Nat.pow_le_pow_right (by omega)
        change s ≤ t at hst
        omega
      omega
    obtain ⟨hsp, htp⟩ := graph_pos (show 0<k by omega) G
    have hsr : (0:ℝ)<s := by exact_mod_cast hsp
    have htr : (0:ℝ)<t := by exact_mod_cast htp
    have hkr : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
    have hlogR := Real.log_le_log hkr (show (k:ℝ) ≤ classicalRamsey (s+1) (t+1) by exact_mod_cast hR.le)
    have hcbin := Real.log_le_log hkr (show (k:ℝ) ≤ (s+t).choose s by exact_mod_cast hkn.le)
    have he := entropy_choose (s:=s) (t:=t) hsp htp
    have hlo := hT t hlarge s hst (Nat.zero_lt_of_lt hR)
    have hinter := interpolate (s:= (s:ℝ)) (t:= (t:ℝ)) (c:=c) (η:=η)
      (Real.log_nonneg (show (1:ℝ) ≤ k by exact_mod_cast hk1)) hsr htr hc' hη
      (entropy_crude hsr htr) (hcbin.trans he) (by linarith)
    exact scale_square hsr htr hinter
  rcases le_total H.cliqueNum H.indepNum with h|h
  · simpa only [min_eq_left (show (H.cliqueNum:ℝ) ≤ H.indepNum by exact_mod_cast h)]
      using sorted H h
  · have e := sorted Hᶜ (by simpa only [cliqueNum_compl,indepNum_compl] using h)
    simpa only [cliqueNum_compl,indepNum_compl,
      min_eq_right (show (H.indepNum:ℝ) ≤ H.cliqueNum by exact_mod_cast h),
      add_comm (H.indepNum:ℝ) H.cliqueNum, mul_comm (H.indepNum:ℝ) H.cliqueNum] using e

theorem main : H1 → H2 → OMA.R_Erdos627_erdos_627_variants_afm_upper_R1.H1 := by
  intro ramsey finiteBound
  apply transfer finiteBound
  intro ε hε
  filter_upwards [ramsey ε hε] with t ht
  intro s hs hst hpos
  have h := Real.log_le_log (Nat.cast_pos.mpr hpos : (0:ℝ)<classicalRamsey s t) (ht s hs hst)
  have hp : (0:ℝ) < (s+t).choose s := by
    exact_mod_cast (Nat.choose_pos (show s ≤ s+t by omega))
  rw [Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp] at h
  linarith

end OMA.R_Erdos627_erdos_627_variants_afm_upper_R1_H1_R1
